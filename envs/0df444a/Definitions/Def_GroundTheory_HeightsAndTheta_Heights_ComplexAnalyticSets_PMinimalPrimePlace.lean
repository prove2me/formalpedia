-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMinimalPrimePlace
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMinimalPrimePlace
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T07:10:40.865113+00:00
-- url     : https://prove2.me/theorems/3af2fd29-e88b-4a22-b091-cd7772727329
-- title:
--   PMinimal Prime Place
-- statement:
--   Definitions and structural lemmas for PMinimal Prime Place, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PMinimalPrimePlace.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StMinimalPrimePlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_CurveNormalisationFiniteLemmas
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartLocalOrder
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial ComplexSets
noncomputable section
namespace MinimalPrimePlace
variable {A B : Type*} [CommRing A] [CommRing B]
theorem le_comap_nonZeroDivisors [IsDomain B] (π : A →+* B) (hker : RingHom.ker π ∈ minimalPrimes A) :
    nonZeroDivisors A ≤ (nonZeroDivisors B).comap π := fun _u hu ↦
  mem_nonZeroDivisors_of_ne_zero fun h ↦
    Set.disjoint_left.1 (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hker) (RingHom.mem_ker.2 h) hu
abbrev fracMap [IsDomain B] (π : A →+* B) (hker : RingHom.ker π ∈ minimalPrimes A) :
    FractionRing A →+* FractionRing B :=
  IsLocalization.map (S := FractionRing A) (FractionRing B) π (le_comap_nonZeroDivisors π hker)
theorem fracMap_aeval [IsDomain B] (π : A →+* B) (hker : RingHom.ker π ∈ minimalPrimes A) (x : FractionRing A)
    (G : Polynomial A) :
    fracMap π hker (Polynomial.aeval x G) = Polynomial.aeval (fracMap π hker x) (G.map π) := by
  rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.eval₂_map, Polynomial.hom_eval₂,
    IsLocalization.map_comp]
theorem isIntegral_fracMap [IsDomain B] (π : A →+* B) (hker : RingHom.ker π ∈ minimalPrimes A) {x : FractionRing A}
    (hx : IsIntegral A x) : IsIntegral B (fracMap π hker x) := by
  obtain ⟨G, hG, hGx⟩ := hx
  refine ⟨G.map π, hG.map π, ?_⟩
  have h := fracMap_aeval π hker x G
  rw [Polynomial.aeval_def, Polynomial.aeval_def, hGx, map_zero] at h
  exact h.symm
def normMap [IsDomain B] (π : A →+* B) (hker : RingHom.ker π ∈ minimalPrimes A) :
    integralClosure A (FractionRing A) →+* integralClosure B (FractionRing B) :=
  ((fracMap π hker).comp (integralClosure A (FractionRing A)).val.toRingHom).codRestrict
    (integralClosure B (FractionRing B)) fun x ↦ isIntegral_fracMap π hker x.2
end MinimalPrimePlace
end
end GroundTheory.Heights₂.Heights


