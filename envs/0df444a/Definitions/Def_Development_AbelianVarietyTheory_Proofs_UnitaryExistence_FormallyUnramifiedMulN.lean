-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FormallyUnramifiedMulN
-- name    : Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FormallyUnramifiedMulN
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:35:06.856727+00:00
-- url     : https://prove2.me/theorems/bae82b7d-e2a5-41d5-bc5e-67deb7523144
-- title:
--   Formally Unramified Mul N
-- statement:
--   Definitions and structural lemmas for Formally Unramified Mul N, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/FormallyUnramifiedMulN.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.MulUnramified
def affineComb {A R : Type} [CommRing A] [CommRing R] (a b c : A →+* R)
    (h : ∀ s t, (a s - c s) * (b t - c t) = 0) : A →+* R where
  toFun s := a s + b s - c s
  map_one' := by simp
  map_zero' := by simp
  map_add' s t := by simp only [map_add]; ring
  map_mul' s t := by
    simp only [map_mul]
    linear_combination - h s t - h t s
variable {S : Scheme.{0}}
end GlobalTheory.MulUnramified
namespace GlobalTheory
end GlobalTheory


