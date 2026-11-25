-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
-- name    : Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T13:44:20.843127+00:00
-- url     : https://prove2.me/theorems/96ca6bf8-9a51-4fd8-9ea4-fdf2e3ecee2c
-- title:
--   Is Discrete Valuation Ring Integral Closure Padic Int
-- statement:
--   Definitions and structural lemmas for Is Discrete Valuation Ring Integral Closure Padic Int, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsDiscreteValuationRingIntegralClosurePadicInt.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PrimeEqBotOrMaximalIdealOfIsFieldAway
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRatA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_FiniteAlgebraLocalCompletion_cl_dvr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory
open IsLocalRing TensorProduct
section Nakayama
end Nakayama
section Core
end Core
section Integers
variable (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [Algebra ℚ_[p] K] [Algebra ℤ_[p] K]
  [IsScalarTower ℤ_[p] ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
instance finite_integralClosure_padicInt : Module.Finite ℤ_[p] (integralClosure ℤ_[p] K) :=
  IsIntegralClosure.finite ℤ_[p] ℚ_[p] K _
instance isDiscreteValuationRing_integralClosure_padicInt :
    IsDiscreteValuationRing (integralClosure ℤ_[p] K) :=
  ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_dvr ℤ_[p] ℚ_[p] K
instance isFractionRing_integralClosure_padicInt : IsFractionRing (integralClosure ℤ_[p] K) K :=
  integralClosure.isFractionRing_of_finite_extension ℚ_[p] K
variable {p K}
variable {L : Type*} [Field L] [Algebra ℚ_[p] L] [Algebra ℤ_[p] L]
  [IsScalarTower ℤ_[p] ℚ_[p] L] [FiniteDimensional ℚ_[p] L]
end Integers
section Affine
variable {p : ℕ} [Fact p.Prime]
end Affine
section Scheme
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {p : ℕ} [Fact p.Prime]
end Scheme
example (p : ℕ) [Fact p.Prime] : ∃ m : Ideal (Polynomial ℤ), m.IsMaximal ∧
    (p : Polynomial ℤ) ∈ m ∧ Polynomial.X ∈ m := by
  let φ : Polynomial ℤ →+* ZMod p := Polynomial.eval₂RingHom (Int.castRingHom _) 0
  refine ⟨RingHom.ker φ, RingHom.ker_isMaximal_of_surjective φ fun x => ?_, ?_, ?_⟩
  · obtain ⟨n, rfl⟩ := ZMod.intCast_surjective x
    exact ⟨n, map_intCast φ n⟩
  · simp [RingHom.mem_ker]
  · simp [RingHom.mem_ker, φ]
end GlobalTheory


