-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_NormIteratedFDerivCexpCompLe
-- name    : Development_AutomorphicSpectrum_Proofs_MembershipProofs_NormIteratedFDerivCexpCompLe
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:15:43.827061+00:00
-- url     : https://prove2.me/theorems/dbca3c69-3bf1-4231-834f-adef1a1bff74
-- title:
--   Norm Iterated FDeriv Cexp Comp Le
-- statement:
--   Definitions and structural lemmas for Norm Iterated FDeriv Cexp Comp Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/NormIteratedFDerivCexpCompLe.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_ExistsHarrisTaylorObjectOfLevelLift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain MeasureTheory Matrix Complex GlobalTheory.CompanionTheory.OM GlobalTheory.WeilM
open scoped ContDiff Nat
namespace GlobalTheory.CompanionTheory.OM
namespace GaussSch
theorem one_add_pow_mul_exp_le {c r : ℝ} (hc : 0 < c) (hr : 0 ≤ r) (N : ℕ) :
    (1 + r) ^ N * Real.exp (-c * r ^ 2) ≤ Real.exp (N ^ 2 / (4 * c)) := by
  have h1 : (1 + r) ^ N ≤ Real.exp r ^ N :=
    pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp r]) N
  calc (1 + r) ^ N * Real.exp (-c * r ^ 2) ≤ Real.exp r ^ N * Real.exp (-c * r ^ 2) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = Real.exp (N * r + -c * r ^ 2) := by rw [← Real.exp_nat_mul, ← Real.exp_add]
    _ ≤ Real.exp (N ^ 2 / (4 * c)) := by
        apply Real.exp_le_exp.2
        rw [le_div_iff₀ (by positivity)]
        nlinarith [sq_nonneg ((N : ℝ) - 2 * c * r)]
theorem norm_iteratedFDeriv_cexp (i : ℕ) (y : ℂ) :
    ‖iteratedFDeriv ℝ i cexp y‖ = Real.exp y.re := by
  rw [← ((Complex.contDiff_exp : ContDiff ℂ (i : WithTop ℕ∞) cexp).contDiffAt (x := y)).restrictScalars_iteratedFDeriv (𝕜 := ℝ),
    Function.comp_apply, ContinuousMultilinearMap.norm_restrictScalars,
    norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate, Complex.iter_deriv_exp,
    Complex.norm_exp]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
theorem norm_iteratedFDeriv_cexp_comp_le {q : E → ℂ} (hq : q.HasTemperateGrowth) (n : ℕ) :
    ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ x : E, ‖iteratedFDeriv ℝ n (cexp ∘ q) x‖ ≤
      C * (1 + ‖x‖) ^ k * Real.exp (q x).re := by
  obtain ⟨m, K, hK, hbd⟩ := hq.norm_iteratedFDeriv_le_uniform n
  refine ⟨n ! * (max K 1) ^ n, m * n, by positivity, fun x ↦ ?_⟩
  have h1x : (1 : ℝ) ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
  have hD1 : 1 ≤ max K 1 * (1 + ‖x‖) ^ m :=
    one_le_mul_of_one_le_of_one_le (le_max_right _ _) (one_le_pow₀ h1x)
  have hD : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i q x‖ ≤ (max K 1 * (1 + ‖x‖) ^ m) ^ i := by
    intro i hi hin
    calc ‖iteratedFDeriv ℝ i q x‖ ≤ K * (1 + ‖x‖) ^ m := hbd i hin x
      _ ≤ max K 1 * (1 + ‖x‖) ^ m := by gcongr; exact le_max_left _ _
      _ = (max K 1 * (1 + ‖x‖) ^ m) ^ 1 := (pow_one _).symm
      _ ≤ (max K 1 * (1 + ‖x‖) ^ m) ^ i := pow_le_pow_right₀ hD1 hi
  have hC : ∀ i, i ≤ n → ‖iteratedFDeriv ℝ i cexp (q x)‖ ≤ Real.exp (q x).re :=
    fun i _ => (norm_iteratedFDeriv_cexp i (q x)).le
  calc ‖iteratedFDeriv ℝ n (cexp ∘ q) x‖
      ≤ n ! * Real.exp (q x).re * (max K 1 * (1 + ‖x‖) ^ m) ^ n :=
        norm_iteratedFDeriv_comp_le (N := n) Complex.contDiff_exp (hq.1.of_le (mod_cast le_top))
          le_rfl x hC hD
    _ = n ! * (max K 1) ^ n * (1 + ‖x‖) ^ (m * n) * Real.exp (q x).re := by
        rw [mul_pow, ← pow_mul]; ring
def cexpSchwartz {q : E → ℂ} (hq : q.HasTemperateGrowth) {c : ℝ} (hc : 0 < c)
    (hre : ∀ x, (q x).re ≤ -c * ‖x‖ ^ 2) : SchwartzMap E ℂ where
  toFun := cexp ∘ q
  smooth' := Complex.contDiff_exp.comp hq.1
  decay' k n := by
    obtain ⟨C, j, hC, hb⟩ := norm_iteratedFDeriv_cexp_comp_le hq n
    refine ⟨C * Real.exp ((k + j : ℕ) ^ 2 / (4 * c)), fun x ↦ ?_⟩
    have hk : ‖x‖ ^ k ≤ (1 + ‖x‖) ^ k := pow_le_pow_left₀ (norm_nonneg x) (by linarith) k
    have he : Real.exp (q x).re ≤ Real.exp (-c * ‖x‖ ^ 2) := Real.exp_le_exp.2 (hre x)
    calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (cexp ∘ q) x‖
        ≤ (1 + ‖x‖) ^ k * (C * (1 + ‖x‖) ^ j * Real.exp (-c * ‖x‖ ^ 2)) :=
          mul_le_mul hk ((hb x).trans (by gcongr)) (norm_nonneg _) (by positivity)
      _ = C * ((1 + ‖x‖) ^ (k + j) * Real.exp (-c * ‖x‖ ^ 2)) := by rw [pow_add]; ring
      _ ≤ C * Real.exp ((k + j : ℕ) ^ 2 / (4 * c)) :=
          mul_le_mul_of_nonneg_left (one_add_pow_mul_exp_le hc (norm_nonneg x) _) hC
variable {κ : Type} [Fintype κ]
end GaussSch
end GlobalTheory.CompanionTheory.OM
end


