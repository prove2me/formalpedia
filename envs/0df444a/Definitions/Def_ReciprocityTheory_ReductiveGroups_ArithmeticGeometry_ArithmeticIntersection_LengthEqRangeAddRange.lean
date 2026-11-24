-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthEqRangeAddRange
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthEqRangeAddRange
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:30:44.751779+00:00
-- url     : https://prove2.me/theorems/fffee772-3fb9-4ad0-a92f-b5480871b625
-- title:
--   Length Eq Range Add Range
-- statement:
--   Definitions and structural lemmas for Length Eq Range Add Range, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/LengthEqRangeAddRange.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LocalLengthAdditivityTorsionFree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.AI
open Module
def kerSmulMap {A : Type*} [CommRing A] {M N : Type*} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (f : M →ₗ[A] N) (x : A) :
    LinearMap.ker (LinearMap.lsmul A M x) →ₗ[A] LinearMap.ker (LinearMap.lsmul A N x) :=
  f.restrict (fun m hm => by
    rw [LinearMap.mem_ker, LinearMap.lsmul_apply] at hm ⊢
    rw [← map_smul, hm, map_zero])
def cokerSmulMap {A : Type*} [CommRing A] {M N : Type*} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (f : M →ₗ[A] N) (x : A) :
    (M ⧸ LinearMap.range (LinearMap.lsmul A M x)) →ₗ[A]
      (N ⧸ LinearMap.range (LinearMap.lsmul A N x)) :=
  Submodule.mapQ _ _ f (by
    rintro _ ⟨m, rfl⟩
    exact ⟨f m, by simp⟩)
end ReciprocityTheory.ChartRestriction.G.AI


