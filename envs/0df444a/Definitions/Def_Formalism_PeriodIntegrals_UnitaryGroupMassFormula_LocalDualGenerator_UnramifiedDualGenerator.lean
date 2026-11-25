-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_UnramifiedDualGenerator
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_UnramifiedDualGenerator
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T16:18:17.172342+00:00
-- url     : https://prove2.me/theorems/7f96e387-5bd1-427d-9170-54817ce62ab0
-- title:
--   Unramified Dual Generator
-- statement:
--   Definitions and structural lemmas for Unramified Dual Generator, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalDualGenerator/UnramifiedDualGenerator.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_FpDualUnram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_IsClosedO
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MemOfClosed
import Theorems.Thm_PI_LocDualGen_FpU_Phi_coe
import Theorems.Thm_PI_LocDualGen_FpU_span
import Theorems.Thm_UpperTheory_Reformulated_B_Qi13_linIndep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel IsLocalRing
namespace PI.LocDualGen.FpU
section Main
variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (l : ℕ) [Fact l.Prime] [Algebra ℚ_[l] K]
variable [CharP 𝓀[K] l]
attribute [local instance] algRes
theorem linIndep (hcont : Continuous (algebraMap ℚ_[l] K)) :
    LinearIndependent ℚ_[l] (fun i => (blift K l i : K)) :=
  by apply _root_.UpperTheory.Reformulated.B.Qi13.linIndep <;> assumption
theorem exists_pow_mul_mem (huni : Irreducible ((l : ℕ) : 𝒪[K])) (x : K) :
    ∃ n : ℕ, (l : K) ^ n * x ∈ 𝒪[K] := by
  by_cases hx : x ∈ 𝒪[K]
  · exact ⟨0, by simpa using hx⟩
  have hx1 : 1 < valuation K x := by
    rw [Valuation.mem_integer_iff, not_le] at hx
    exact hx
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, map_zero] at hx1
    exact absurd hx1 (not_lt.mpr zero_le)
  have hinv : x⁻¹ ∈ 𝒪[K] := by
    rw [Valuation.mem_integer_iff, map_inv₀]
    exact inv_le_one_of_one_le₀ hx1.le
  have hr0 : (⟨x⁻¹, hinv⟩ : 𝒪[K]) ≠ 0 := by
    intro h
    have := congrArg Subtype.val h
    exact inv_ne_zero hx0 this
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr0 huni
  refine ⟨n, ?_⟩
  have hu' : x⁻¹ = ((u : 𝒪[K]) : K) * (l : K) ^ n := by
    have := congrArg Subtype.val hu
    simpa using this
  have huu : ((u : 𝒪[K]) : K) * (((u⁻¹ : (𝒪[K])ˣ) : 𝒪[K]) : K) = 1 := by
    rw [← Subring.coe_mul, Units.mul_inv]
    rfl
  have hxe : x = (((u : 𝒪[K]) : K) * (l : K) ^ n)⁻¹ := by rw [← hu', inv_inv]
  have hl0 : ((l : K)) ^ n ≠ 0 := by
    intro h
    rw [h, mul_zero] at hu'
    exact inv_ne_zero hx0 hu'
  have hv : (l : K) ^ n * x = (((u⁻¹ : (𝒪[K])ˣ) : 𝒪[K]) : K) := by
    rw [hxe, mul_inv, ← mul_assoc, mul_comm ((l : K) ^ n), mul_assoc, mul_inv_cancel₀ hl0, mul_one]
    exact inv_eq_of_mul_eq_one_right huu
  rw [hv]
  exact (u⁻¹ : (𝒪[K])ˣ).1.2
theorem spanTop (hcont : Continuous (algebraMap ℚ_[l] K)) (huni : Irreducible ((l : ℕ) : 𝒪[K])) :
    ⊤ ≤ Submodule.span ℚ_[l] (Set.range fun i => (blift K l i : K)) := by
  intro x _
  obtain ⟨n, hn⟩ := exists_pow_mul_mem K l huni x
  obtain ⟨c, hc⟩ := span K l hcont huni ⟨_, hn⟩
  have hc' := congrArg Subtype.val hc
  rw [Phi_coe] at hc'
  change (l : K) ^ n * x = _ at hc'
  have hl0 : (l : K) ^ n ≠ 0 := pow_ne_zero _ (by
    rw [← map_natCast (algebraMap ℚ_[l] K)]
    exact (map_ne_zero _).mpr (by exact_mod_cast (Fact.out : l.Prime).ne_zero))
  have hx : x = ∑ i, (((l : ℚ_[l]) ^ n)⁻¹ * (c i : ℚ_[l])) • (blift K l i : K) := by
    have e : x = ((l : K) ^ n)⁻¹ * ((l : K) ^ n * x) := by field_simp
    rw [e, hc', Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Algebra.smul_def, map_mul, map_inv₀, map_pow, map_natCast]
    ring
  rw [hx]
  exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
def B (hcont : Continuous (algebraMap ℚ_[l] K)) (huni : Irreducible ((l : ℕ) : 𝒪[K])) :
    Module.Basis (Fin (fdim K l)) ℚ_[l] K :=
  Module.Basis.mk (linIndep K l hcont) (spanTop K l hcont huni)
def coef (hcont : Continuous (algebraMap ℚ_[l] K)) (huni : Irreducible ((l : ℕ) : 𝒪[K]))
    (y : 𝒪[K]) : Fin (fdim K l) → ℤ_[l] :=
  (span K l hcont huni y).choose
end Main
end PI.LocDualGen.FpU


