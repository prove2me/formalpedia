-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_IntegrablePair
-- name    : Development_AutomorphicSpectrum_Proofs_MembershipProofs_IntegrablePair
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:22:47.956139+00:00
-- url     : https://prove2.me/theorems/73045ab8-820b-473d-8c46-1bc0cc1bafcc
-- title:
--   Integrable Pair
-- statement:
--   Definitions and structural lemmas for Integrable Pair, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/IntegrablePair.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_GoodChar
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_GoodCharIsLocallyConstant
import Theorems.Thm_GlobalTheory_CompanionTheory_FinHeis_Implements_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix
namespace GlobalTheory.CompanionTheory.SchrSys
section Pair
variable {R : Type} [TopologicalSpace R] {κ : Type}
theorem integrable_pair (μ : @Measure (κ → R) (borel _)) (hμ : @IsFiniteMeasureOnCompacts _ (borel _) _ μ)
    (φ φ' : SB (κ → R)) :
    @Integrable ℂ _ _ _ (borel _) (fun x => (starRingEnd ℂ) ((φ : (κ → R) → ℂ) x) * (φ' : (κ → R) → ℂ) x) μ := by
  letI : MeasurableSpace (κ → R) := borel _
  haveI : BorelSpace (κ → R) := ⟨rfl⟩
  have h1 : Continuous (φ : (κ → R) → ℂ) := φ.2.1.continuous
  have h2 : Continuous (φ' : (κ → R) → ℂ) := φ'.2.1.continuous
  have h3 : HasCompactSupport (φ' : (κ → R) → ℂ) := φ'.2.2
  exact Continuous.integrable_of_hasCompactSupport ((Complex.continuous_conj.comp h1).mul h2)
    (HasCompactSupport.mul_left (f := fun x => (starRingEnd ℂ) ((φ : (κ → R) → ℂ) x)) h3)
def pairForm (μ : @Measure (κ → R) (borel _)) (hμ : @IsFiniteMeasureOnCompacts _ (borel _) _ μ) :
    SB (κ → R) →ₗ⋆[ℂ] SB (κ → R) →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun φ φ' => pair μ φ φ')
    (by
      intro f f' g
      simp only [pair, Submodule.coe_add, Pi.add_apply, map_add, add_mul]
      exact integral_add (integrable_pair μ hμ f g) (integrable_pair μ hμ f' g))
    (by
      intro a f g
      simp only [pair, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc]
      exact integral_const_mul _ _)
    (by
      intro f g g'
      simp only [pair, Submodule.coe_add, Pi.add_apply, mul_add]
      exact integral_add (integrable_pair μ hμ f g) (integrable_pair μ hμ f g'))
    (by
      intro a f g
      simp only [pair, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_left_comm _ a]
      exact integral_const_mul _ _)
end Pair
end GlobalTheory.CompanionTheory.SchrSys


