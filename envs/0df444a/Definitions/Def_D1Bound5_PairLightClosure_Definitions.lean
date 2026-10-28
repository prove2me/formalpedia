-- Prove2me | Definitions.Def_D1Bound5_PairLightClosure_Definitions
-- name    : D1Bound5_PairLightClosure_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:54:12.628966+00:00
-- url     : https://prove2.me/theorems/6a742873-4046-40c7-95de-7867e3d772bb
-- title:
--   Pair Light Closure
-- statement:
--   A prefix always looks up destinations in the complete original list. The named objects in this bundle include `pairLightMul`, `pairLightAdd`, `pairLightNeg`, `pairLightMutate`, `PairLightRootWitness`, `PairLightRootWitness.leftRoot`, `PairLightRootWitness.rightRoot`, `PairLightRootWitness.vertex` and 4 further declarations.
-- source:
--   D1Bound5/PairLightClosure.lean, lines 8-10, SHA-256 ef69d3a60e5b156fbd56cb019ebd0325abef2ca7d10021397aca371566944128; D1Bound5/PairLightClosure.lean, lines 12-13, SHA-256 ef69d3a60e5b156fbd56cb019ebd0325abef2ca7d10021397aca371566944128; D1Bound5/PairLightClosure.lean, lines 15-15, SHA-256 ef69d3a60e5b156fbd56cb019ebd0325abef2ca7d10021397aca371566944128; D1Bound5/PairLightClosure.lean, lines 17-23, SHA-256 ef69d3a60e5b156fbd56cb019ebd0325abef2ca7d10021397aca371566944128; D1Bound5/PairLightClosure.lean, lines 25-28, SHA-256 ef69d3a60e5b156fbd56cb019ebd0325abef2ca7d10021397aca371566944128; D1Bound5/PairLightClosure.lean, lines 30-35, SHA-256 ef69d3a60e5b156fbd56cb019ebd0325abef2ca7d10021397aca371566944128; D1Bound5/PairLightClosure.lean, lines 37-48, SHA-256 ef69d3a60e5b156fbd56cb019ebd0325abef2ca7d10021397aca371566944128; D1Bound5/PairLightClosure.lean, lines 50-57, SHA-256 ef69d3a60e5b156fbd56cb019ebd0325abef2ca7d10021397aca371566944128; D1Bound5/PairLightClosure.lean, lines 59-68, SHA-256 ef69d3a60e5b156fbd56cb019ebd0325abef2ca7d10021397aca371566944128. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions

section
namespace D1Bound5

/- Exact coordinate-only version of the indexed closure checker. Mathematical
soundness is established in PairLightClosureBridge, not assumed here. -/

def pairLightMul (tau nu : Int) (x y : PairLightCoordinate) : PairLightCoordinate :=
  (x.1 * y.1 + (-nu) * x.2 * y.2,
    x.1 * y.2 + x.2 * y.1 + tau * x.2 * y.2)

def pairLightAdd (x y : PairLightCoordinate) : PairLightCoordinate :=
  (x.1 + y.1, x.2 + y.2)

def pairLightNeg (x : PairLightCoordinate) : PairLightCoordinate := (-x.1, -x.2)

def pairLightMutate (tau nu : Int) (a b z r0 r s : PairLightCoordinate) :
    PairLightCoordinate :=
  pairLightAdd
    (pairLightAdd (pairLightAdd a b)
      (pairLightMul tau nu
        (pairLightAdd (pairLightMul tau nu (pairLightMul tau nu (2, 0) a) b) (1, 0)) z))
    (pairLightMul tau nu (pairLightMul tau nu (pairLightMul tau nu (2, 0) r0) r) s)

structure PairLightRootWitness where
  vertex : PairLightCoordinate
  leftRoot : PairLightCoordinate
  rightRoot : PairLightCoordinate

def pairLightIndexedCandidateCoveredBool (tau nu bound : Int)
    (vertices : List PairLightCoordinate) (w : PairLightCoordinate)
    (destination : Option Nat) : Bool :=
  match destination with
  | none => decide (bound < pairLightNorm tau nu w)
  | some i => decide (vertices[i]? = some w)

def pairLightIndexedRootWitnessCheckedBool (tau nu : Int)
    (a b r0 : PairLightCoordinate) (bound : Int) (vertices : List PairLightCoordinate)
    (w : PairLightRootWitness) (destinations : Option Nat × Option Nat) : Bool :=
  decide (pairLightMul tau nu w.leftRoot w.leftRoot =
      pairLightProductPlusOne tau nu a w.vertex ∧
    pairLightMul tau nu w.rightRoot w.rightRoot =
      pairLightProductPlusOne tau nu b w.vertex) &&
    (pairLightIndexedCandidateCoveredBool tau nu bound vertices
        (pairLightMutate tau nu a b w.vertex r0 w.leftRoot w.rightRoot) destinations.1 &&
      pairLightIndexedCandidateCoveredBool tau nu bound vertices
        (pairLightMutate tau nu a b w.vertex r0 w.leftRoot (pairLightNeg w.rightRoot))
        destinations.2)

def pairLightIndexedWitnessesCheckedBool (tau nu : Int)
    (a b r0 : PairLightCoordinate) (bound : Int) (vertices : List PairLightCoordinate) :
    List PairLightRootWitness → List (Option Nat × Option Nat) → Bool
  | [], [] => true
  | w :: ws, d :: ds =>
      pairLightIndexedRootWitnessCheckedBool tau nu a b r0 bound vertices w d &&
        pairLightIndexedWitnessesCheckedBool tau nu a b r0 bound vertices ws ds
  | _, _ => false

/-- A prefix always looks up destinations in the complete original list. -/
def pairLightIndexedWitnessesPrefixBool (tau nu : Int)
    (a b r0 : PairLightCoordinate) (bound : Int) (vertices : List PairLightCoordinate) :
    Nat → List PairLightRootWitness → List (Option Nat × Option Nat) → Bool
  | 0, _, _ => true
  | _ + 1, [], [] => true
  | n + 1, w :: ws, d :: ds =>
      pairLightIndexedRootWitnessCheckedBool tau nu a b r0 bound vertices w d &&
        pairLightIndexedWitnessesPrefixBool tau nu a b r0 bound vertices n ws ds
  | _ + 1, _, _ => false





end D1Bound5
end


