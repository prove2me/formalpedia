-- Prove2me | Definitions.Def_N25_CanonicalNormalizedPoints
-- name    : N25_CanonicalNormalizedPoints
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:03:41.69163+00:00
-- url     : https://prove2.me/theorems/208f99b4-4452-4854-87c0-4fb48e7bbc40
-- title:
--   First-nonzero-coordinate representatives of canonical points
-- statement:
--   The file defines the four normalized projective charts $$[1:y:z:w], [0:1:z:w], [0:0:1:w], [0:0:0:1],$$ evaluates the canonical quadric and cubic on them, and defines the subtype of normalized vectors satisfying both equations. It also records the pivot index of the first coordinate equal to one. This is the finite, quotient-free carrier used for explicit point counts and the comparison with scheme points.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_NormalizedPointPredicates
import Definitions.Def_N25_CanonicalUnitPlane
/-! Normalized projective points of the literal canonical intersection. -/
namespace N25.Endgame

def normalizedCoordinates25 {K : Type*} [Field K] :
    MazurProof.RationalPointsN25QuotientWeil.NormalizedProjective4 K →
      Fin 4 → K
  | .xChart y z w => ![1, y, z, w]
  | .yChart z w => ![0, 1, z, w]
  | .zChart w => ![0, 0, 1, w]
  | .wChart => ![0, 0, 0, 1]

def IsCanonicalNormalized25 {K : Type*} [Field K]
    (P : MazurProof.RationalPointsN25QuotientWeil.NormalizedProjective4 K) : Prop :=
  let c := normalizedCoordinates25 P
  N25.canonicalQuadric (c 0) (c 1) (c 2) (c 3) = 0 ∧
    N25.canonicalCubic (c 0) (c 1) (c 2) (c 3) = 0

abbrev CanonicalPoint25 (K : Type*) [Field K] :=
  {P : MazurProof.RationalPointsN25QuotientWeil.NormalizedProjective4 K //
    IsCanonicalNormalized25 P}

/-- The first coordinate equal to one in a normalized representative. -/
def normalizedPivot25 {K : Type*} :
    MazurProof.RationalPointsN25QuotientWeil.NormalizedProjective4 K → Fin 4
  | .xChart _ _ _ => 0
  | .yChart _ _ => 1
  | .zChart _ => 2
  | .wChart => 3

end N25.Endgame


