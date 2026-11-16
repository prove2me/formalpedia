-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_Pi
-- name    : liuyao_ca_fd889115_k1_Analysis_Pi
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T17:57:44.298516+00:00
-- url     : https://prove2.me/theorems/c24d129e-6518-490b-a382-aa4f8f80ee1f
-- title:
--   Computable analysis · Pi · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/Pi.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_Basic
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_AlgebraicFunctions
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_PowerSeries

set_option autoImplicit true

namespace ComputableAnalysis

/-- The Leibniz alternating series, computing `pi / 4`. -/
def leibnizSeries : RealCompute where
  compute := fun n =>
    let state : Rat × Rat := (List.range n).foldl
      (fun state (i : Nat) =>
        let term1 : Rat := 1 / (4 * i + 3)
        let term2 : Rat := 1 / (4 * i + 5)
        let lo := state.1 - term1
        let hi := lo + term2
        (hi, lo))
      (1, 0)
    { lo := state.2, hi := state.1 }

/-- Pi from the Leibniz alternating series. -/
def piLeibniz : RealCompute :=
  (4 : Nat) * leibnizSeries

/-- The kth positive magnitude in Nilakantha's rational pi series.

The first used term is `nilakanthaTerm 1 = 1 / 6`; the value at zero is
harmless but is not part of the series. -/
def nilakanthaTerm (k : Nat) : Rat :=
  4 / ((2 * (k : Rat)) * (2 * (k : Rat) + 1) * (2 * (k : Rat) + 2))

/-- Finite partial sums of Nilakantha's alternating rational pi series.

Each summand is rational and the alternating sign is attached to the
zero-based recursion index. -/
def nilakanthaPartial : Nat -> Rat
  | 0 => 3
  | n + 1 =>
      nilakanthaPartial n + (-1 : Rat) ^ n * nilakanthaTerm (n + 1)

/-- Pi from Nilakantha's accelerated rational alternating series.

Even partial sums are lower bounds and the next odd partial sum is an upper
bound.  Validity and agreement with the geometric pi computation are proved
from a finite termwise transformation to the verified Leibniz series. -/
def piNilakantha : RealCompute where
  compute := fun n =>
    { lo := nilakanthaPartial (2 * n),
      hi := nilakanthaPartial (2 * n + 1) }

/-- Pi from Machin's formula. -/
def piMachin : RealCompute :=
  (4 : Nat) * ((4 : Nat) * arctan (1 / 5) - arctan (1 / 239))

structure PiCirclePoint where
  x : Rat
  y : Rat
deriving Repr, DecidableEq

private theorem rat_square_nonneg (x : Rat) : 0 <= x * x := by
  by_cases hx : 0 <= x
  · exact Rat.mul_nonneg hx hx
  · have hneg : 0 <= -x := by grind
    have hsq : 0 <= (-x) * (-x) := Rat.mul_nonneg hneg hneg
    grind [Rat.mul_neg, Rat.neg_mul, Rat.neg_neg]

private theorem square_sum_sqrtDomain (dx dy : Rat) :
    sqrtDomain (dx * dx + dy * dy) := by
  change ¬dx * dx + dy * dy < 0
  have hx : 0 <= dx * dx := rat_square_nonneg dx
  have hy : 0 <= dy * dy := rat_square_nonneg dy
  grind

/-- Total length of a polygonal path through rational points. -/
def rationalPointPathLength (points : List PiCirclePoint) (n : Nat) : QInterval :=
  let segmentLength := fun (p q : PiCirclePoint) =>
    let dx := q.x - p.x
    let dy := q.y - p.y
    let normSq := dx * dx + dy * dy
    sqrtPartialRaw.compute normSq (square_sum_sqrtDomain dx dy) n
  let rec totalLength : List PiCirclePoint -> QInterval
    | [] => { lo := 0, hi := 0 }
    | [_] => { lo := 0, hi := 0 }
    | p :: q :: rest =>
        let length := segmentLength p q
        let tail := totalLength (q :: rest)
        { lo := length.lo + tail.lo,
          hi := length.hi + tail.hi }
  totalLength points

/-- State for the update-loop presentation of area exhaustion.  The interval
`[lo, hi]` stores the current lower and upper quarter-sector area bounds, while
`intervals` stores the rational parameter intervals still being refined. -/
structure AreaBoundsLoopState where
  lo : Rat
  hi : Rat
  intervals : List (Rat × Rat)
deriving Repr, DecidableEq

/-- The area added to the inscribed chord fan when adjacent parameters
`p < q < r` replace the old interval `[p,r]` by two intervals. -/
def circleAreaIncrement (p q r : Rat) : Rat :=
  (2 * (r - p) * (q - p) * (r - q)) /
    ((1 + p * p) * (1 + q * q) * (1 + r * r))

/-- The area removed from the outer tangent fan when adjacent parameters
`p < q < r` replace the old interval `[p,r]` by two intervals. -/
def circleAreaDecrement (p q r : Rat) : Rat :=
  ((r - p) * (q - p) * (r - q)) /
    ((1 + p * r) * (1 + p * q) * (1 + q * r))

namespace AreaBoundsLoopState

def refineAux : Rat -> Rat -> List (Rat × Rat) -> AreaBoundsLoopState
  | lo, hi, [] => { lo := lo, hi := hi, intervals := [] }
  | lo, hi, (p, r) :: rest =>
      let q := (p + r) / 2
      let next := refineAux
        (lo + circleAreaIncrement p q r)
        (hi - circleAreaDecrement p q r)
        rest
      { next with intervals := (p, q) :: (q, r) :: next.intervals }

end AreaBoundsLoopState

/-- Refine every current rational parameter interval once, updating the lower
and upper area bounds by the explicit increment and decrement formulas. -/
def refineAreaBounds (state : AreaBoundsLoopState) : AreaBoundsLoopState :=
  AreaBoundsLoopState.refineAux state.lo state.hi state.intervals

/-- Iterate the area-bound refinement loop. -/
def iterateAreaBounds : Nat -> AreaBoundsLoopState -> AreaBoundsLoopState
  | 0, state => state
  | n + 1, state => iterateAreaBounds n (refineAreaBounds state)

def piCircleAreaInitial : AreaBoundsLoopState :=
  { lo := 1 / 2, hi := 1, intervals := [(0, 1)] }

def piCircleAreaState (n : Nat) : AreaBoundsLoopState :=
  iterateAreaBounds n piCircleAreaInitial

def piCircleAreaCompute (n : Nat) : QInterval :=
  let state := piCircleAreaState n
  { lo := 4 * state.lo, hi := 4 * state.hi }

/-- Pi as the area of the unit disk, presented as the rational update loop:
start with the quarter-square bounds and refine each rational parameter
interval by one midpoint insertion. -/
def piCircleArea : RealCompute where
  compute := piCircleAreaCompute

theorem piCircleArea_compute_eq (n : Nat) :
    piCircleArea.compute n = piCircleAreaCompute n := rfl

theorem piCircleArea_compute_zero :
    piCircleArea.compute 0 = { lo := 2, hi := 4 } := by
  decide +kernel

/-- Polygon-boundary presentation of the same intended area exhaustion.

This is retained as proof scaffolding for finite geometric comparisons.  It is
not the public pi computation; `piCircleArea` is the increment/decrement loop
above. -/
def piCircleAreaPolygon : RealCompute where
  compute := fun n =>
    let stage : Nat := 2 ^ n
    let parameter := fun (k : Nat) => (k : Rat) / (stage : Rat)
    let point := fun t =>
      let d := 1 + t * t
      let x := (1 - t * t) / d
      let y := (2 * t) / d
      ({ x := x, y := y } : PiCirclePoint)
    let samplePoint := fun k => point (parameter k)
    let rec innerBoundaryFrom (k count : Nat) : List PiCirclePoint :=
      match count with
      | 0 => []
      | count + 1 =>
          samplePoint k :: innerBoundaryFrom (k + 1) count
    let innerBoundary := innerBoundaryFrom 0 (stage + 1)
    let tangentIntersection := fun (p q : PiCirclePoint) =>
      let det := p.x * q.y - p.y * q.x
      let x := (q.y - p.y) / det
      let y := (p.x - q.x) / det
      ({ x := x, y := y } : PiCirclePoint)
    let outerTangentPoint := fun k =>
      tangentIntersection (samplePoint k) (samplePoint (k + 1))
    let rec outerBoundaryFrom (k count : Nat) : List PiCirclePoint :=
      match count with
      | 0 => []
      | count + 1 =>
          outerTangentPoint k ::
            samplePoint (k + 1) ::
              outerBoundaryFrom (k + 1) count
    let outerBoundary := samplePoint 0 :: outerBoundaryFrom 0 stage
    let origin : PiCirclePoint := { x := 0, y := 0 }
    let cross := fun (p q : PiCirclePoint) => p.x * q.y - p.y * q.x
    let rec twiceSignedAreaAux
        (first prev : PiCirclePoint) : List PiCirclePoint -> Rat
      | [] => cross prev first
      | vertex :: rest =>
          cross prev vertex + twiceSignedAreaAux first vertex rest
    let twiceSignedArea := fun vertices =>
      match vertices with
      | [] => 0
      | first :: rest => twiceSignedAreaAux first first rest
    let polygonArea := fun vertices => qabs (twiceSignedArea vertices / 2)
    let innerQuarter := polygonArea (origin :: innerBoundary)
    let outerQuarter := polygonArea (origin :: outerBoundary)
    { lo := 4 * innerQuarter,
      hi := 4 * outerQuarter }

/-- Pi as half the circumference of the unit circle. -/
def piCircumference : RealCompute where
  compute := fun n =>
    let stage : Nat := 2 ^ n
    let parameter := fun (k : Nat) => (k : Rat) / (stage : Rat)
    let point := fun t =>
      let d := 1 + t * t
      let x := (1 - t * t) / d
      let y := (2 * t) / d
      ({ x := x, y := y } : PiCirclePoint)
    let samplePoint := fun k => point (parameter k)
    let rec innerBoundaryFrom (k count : Nat) : List PiCirclePoint :=
      match count with
      | 0 => []
      | count + 1 =>
          samplePoint k :: innerBoundaryFrom (k + 1) count
    let innerBoundary := innerBoundaryFrom 0 (stage + 1)
    let tangentIntersection := fun (p q : PiCirclePoint) =>
      let det := p.x * q.y - p.y * q.x
      let x := (q.y - p.y) / det
      let y := (p.x - q.x) / det
      ({ x := x, y := y } : PiCirclePoint)
    let outerTangentPoint := fun k =>
      tangentIntersection (samplePoint k) (samplePoint (k + 1))
    let rec outerBoundaryFrom (k count : Nat) : List PiCirclePoint :=
      match count with
      | 0 => []
      | count + 1 =>
          outerTangentPoint k ::
            samplePoint (k + 1) ::
              outerBoundaryFrom (k + 1) count
    let outerBoundary := samplePoint 0 :: outerBoundaryFrom 0 stage
    let innerQuarter := rationalPointPathLength innerBoundary stage
    let outerQuarter := rationalPointPathLength outerBoundary stage
    { lo := (4 * innerQuarter.lo) / 2,
      hi := (4 * outerQuarter.hi) / 2 }

namespace PiExamples

#eval! (piLeibniz.compute 10).display
#eval! (piMachin.compute 10).display
#eval! (piCircleArea.compute 10).display
#eval! (piCircumference.compute 10).display

-- These are useful from the command line, but too large for the live infoview:
-- #eval! (piLeibniz.compute 100).display
-- #eval! (piMachin.compute 100).display

end PiExamples

end ComputableAnalysis


