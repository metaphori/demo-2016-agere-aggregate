import it.unibo.scafi.simulation.gui.BasicSpatialIncarnation._
import it.unibo.scafi.simulation.gui.model.AggregateProgram
import Builtins._

import scala.concurrent.duration.Duration

/**
  * @author Roberto Casadei
  *
  */

trait SensorDefinitions { self: AggregateProgram =>
  def sense1 = sense[Boolean]("sens1")
  def sense2 = sense[Boolean]("sens2")
  def sense3 = sense[Boolean]("sens3")
  def nbrRange = nbrvar[Double]("nbrRange") * 100
}

trait BlockT { self: AggregateProgram =>
  def T[V](initial: V, floor: V, decay: V => V)
          (implicit ev: Numeric[V]): V = {
    rep(initial) { v =>
      ev.min(initial, ev.max(floor, decay(v)))
    }
  }

  def T[V](initial: V, decay: V => V)
          (implicit ev: Numeric[V]): V = {
    T(initial, ev.zero, decay)
  }

  def T[V](initial: V)
          (implicit ev: Numeric[V]): V = {
    T(initial, (t: V) => ev.minus(t, ev.one))
  }

  def timer[V](length: V)
              (implicit ev: Numeric[V]) =
    T[V](length)

  def limitedMemory[V, T](value: V, expValue: V, timeout: T)
                         (implicit ev: Numeric[T]) = {
    val t = timer[T](timeout)
    (if (ev.gt(t, ev.zero)) value else expValue, t)
  }

  def timer(dur: Duration): Long = {
    val ct = System.nanoTime() // Current time
    val et = ct + dur.toNanos // Time-to-expire (bootstrap)

    rep((et, dur.toNanos)) { case (expTime, remaining) =>
      if (remaining <= 0) (et, 0)
      else (expTime, expTime - ct)
    }._2 // Selects the component expressing remaining time
  }

  def recentlyTrue(dur: Duration, cond: => Boolean): Boolean =
    rep(false){ happened =>
      branch(cond){ true } { branch(!happened){ false }{ timer(dur)>0 } }
    }

}

trait BlockS { self: AggregateProgram with SensorDefinitions with BlockG =>
  def S(grain: Double,
        metric: => Double): Boolean =
    breakUsingUids(randomUid, grain, metric)

  def minId(): ID = {
    rep(Int.MaxValue) { mmid => math.min(mid(), minHood(nbr {
      mmid
    }))
    }
  }

  def S2(grain: Double): Boolean =
    branch(distanceTo(mid() == minId()) < grain) {
      mid() == minId()
    } {
      S2(grain)
    }

  /**
    * Generates a field of random unique identifiers.
    *
    * @return a tuple where the first element is a random number,
    *         end the second element is the device identifier to
    *         ensure uniqueness of the field elements.
    */
  def randomUid: (Double, ID) = rep((Math.random()), mid()) { v =>
    (v._1, mid())
  }

  /**
    * Breaks simmetry using UIDs. UIDs are used to break symmetry
    * by a competition between devices for leadership.
    */
  def breakUsingUids(uid: (Double, ID),
                     grain: Double,
                     metric: => Double): Boolean =
  // Initially, each device is a candidate leader, competing for leadership.
    uid == rep(uid) { lead: (Double, ID) =>
      // Distance from current device (uid) to the current leader (lead).
      val dist = G[Double](uid == lead, 0, (_: Double) + metric, metric)

      // Initially, current device is candidate, so the distance ('dist')
      // will be 0; the same will be for other devices.
      // To solve the conflict, devices abdicate in favor of devices with
      // lowest UID, according to 'distanceCompetition'.
      distanceCompetition(dist, lead, uid, grain, metric)
    }

  /**
    * Candidate leader devices surrender leadership to the lowest nearby UID.
    *
    * @return
    */
  def distanceCompetition(d: Double,
                          lead: (Double, ID),
                          uid: (Double, ID),
                          grain: Double,
                          metric: => Double) = {
    val inf: (Double, ID) = (Double.PositiveInfinity, uid._2)
    mux(d > grain) {
      // If the current device has a distance to the current candidate leader
      //   which is > grain, then the device candidate itself for another region.
      // Remember: 'grain' represents, in the algorithm,
      //   the mean distance between two leaders.
      uid
    } {
      mux(d >= (0.5 * grain)) {
        // If the current device is at an intermediate distance to the
        //   candidate leader, then it abdicates (by returning 'inf').
        inf
      } {
        // Otherwise, elect the leader with lowest UID.
        // Note: it works because Tuple2 has an OrderingFoldable where
        //   the min(t1,t2) is defined according the 1st element, or
        //   according to the 2nd elem in case of breakeven on the first one.
        //   (minHood uses min to select the candidate leader tuple)
        minHood { mux(nbr { d } + metric >= 0.5 * grain){
          nbr { inf }
        }{
          nbr { lead }
        } }
      }
    }
  }
}

trait BlockG { self: AggregateProgram with SensorDefinitions =>

  def G[V: OrderingFoldable](source: Boolean, field: V, acc: V => V, metric: => Double): V =
    rep((Double.MaxValue, field)) { case (dist, value) =>
      mux(source) {
        (0.0, field)
      } {
        minHoodPlus {
          (nbr{ dist } + metric, acc( nbr{ value }))
        }
      }
    }._2

  def G2[V: OrderingFoldable](source: Boolean)(field: V)(acc: V => V)(metric: => Double = nbrRange): V =
    rep((Double.MaxValue, field)) { case (d,v) =>
      mux(source) { (0.0, field) } {
        minHoodPlus { (nbr{d} + metric, acc(nbr{v})) }
      }
    }._2

  def distanceTo(source: Boolean): Double =
    G2(source)(0.0)(_ + nbrRange)()

  def broadcast[V: OrderingFoldable](source: Boolean, field: V): V =
    G2(source)(field)(v=>v)()

  def distanceBetween(source: Boolean, target: Boolean): Double =
    broadcast(source, distanceTo(target))
}

trait BlockC { self: AggregateProgram with SensorDefinitions =>

  def findParent[V:OrderingFoldable](potential: V): ID = {
    mux(implicitly[OrderingFoldable[V]].compare(minHood { nbr(potential) }, potential) < 0) {
      minHood { nbr { (potential, mid()) } }._2
    } {
      Int.MaxValue
    }
  }

  def C[V: OrderingFoldable](potential: V, acc: (V, V) => V, local: V, Null: V): V = {
    rep(local) { v =>
      acc(local, foldhood(Null)(acc) {
        mux(nbr(findParent(potential)) == mid()) {
          nbr(v)
        } {
          nbr(Null)
        }
      })
    }
  }
}

trait BlocksWithGC { self: BlockC with BlockG =>

  def summarize(sink: Boolean, acc:(Double,Double)=>Double, local:Double, Null:Double): Double =
    broadcast(sink, C(distanceTo(sink), acc, local, Null))

  def average(sink: Boolean, value: Double): Double =
    summarize(sink, (a,b)=>{a+b}, value, 0.0) / summarize(sink, (a,b)=>a+b, 1, 0.0)
}