-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_HeightOneIffDimOne
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_HeightOneIffDimOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:30:23.755066+00:00
-- url     : https://prove2.me/theorems/4a7f07d9-82b4-4eaf-a4d3-88013a6747b7
-- title:
--   Height One Iff Dim One
-- statement:
--   Definitions and structural lemmas for Height One Iff Dim One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/HeightOneIffDimOne.lean

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
universe u v
section general
variable {R S : Type*} [CommRing R] [CommRing S]
end general
section quot
variable {A : Type u} [CommRing A]
noncomputable def quotQuotComapEquiv (a : A) (P : PrimeSpectrum (A ⧸ Ideal.span {a})) :
    (A ⧸ Ideal.span {a}) ⧸ P.asIdeal ≃+*
      A ⧸ (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {a})) P).asIdeal :=
  have hle : Ideal.span {a} ≤
      (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {a})) P).asIdeal := by
    intro x hx
    show Ideal.Quotient.mk _ x ∈ P.asIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact P.asIdeal.zero_mem
  have hP : P.asIdeal = (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {a})) P).asIdeal.map
      (Ideal.Quotient.mk (Ideal.span {a})) :=
    (Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective _).symm
  (Ideal.quotEquivOfEq hP).trans (DoubleQuot.quotQuotEquivQuotOfLE hle)
end quot
variable {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
end ReciprocityTheory.ChartRestriction.G.AI


