-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianSchwartz
-- name    : GroundTheory_GlobalFields_TateThesis_GaussianSchwartz
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:13:33.446802+00:00
-- url     : https://prove2.me/theorems/de840b1a-6876-4077-9365-3d528ad4917c
-- title:
--   Gaussian Schwartz
-- statement:
--   Definitions and structural lemmas for Gaussian Schwartz, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/GaussianSchwartz.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Real Function
open scoped ContDiff Nat SchwartzMap
namespace GroundTheory.Global
noncomputable section
theorem one_add_pow_mul_exp_neg_pi_mul_sq_le {r : ℝ} (hr : 0 ≤ r) (N : ℕ) :
    (1 + r) ^ N * Real.exp (-π * r ^ 2) ≤ Real.exp (N ^ 2 / (4 * π)) := by
  have h1 : (1 + r) ^ N ≤ Real.exp (N * r) := by
    calc (1 + r) ^ N ≤ Real.exp r ^ N :=
          pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp r]) N
      _ = Real.exp (N * r) := by rw [← Real.exp_nat_mul]
  calc (1 + r) ^ N * Real.exp (-π * r ^ 2) ≤ Real.exp (N * r) * Real.exp (-π * r ^ 2) := by
        gcongr
    _ = Real.exp (N * r - π * r ^ 2) := by rw [← Real.exp_add]; ring_nf
    _ ≤ Real.exp (N ^ 2 / (4 * π)) := by
      apply Real.exp_le_exp.2
      rw [le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg ((N : ℝ) - 2 * π * r), Real.pi_pos]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
def gaussianFun (x : E) : ℂ := ((Real.exp (-π * ‖x‖ ^ 2) : ℝ) : ℂ)
theorem contDiff_gaussianFun : ContDiff ℝ ∞ (gaussianFun (E := E)) :=
  Complex.ofRealCLM.contDiff.comp
    (Real.contDiff_exp.comp (contDiff_const.mul (contDiff_norm_sq ℝ)))
theorem norm_iteratedFDeriv_exp (i : ℕ) (y : ℝ) :
    ‖iteratedFDeriv ℝ i Real.exp y‖ = Real.exp y := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate, Real.iter_deriv_exp,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos y)]
theorem norm_iteratedFDeriv_gaussian_le (n : ℕ) :
    ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ x : E, ‖iteratedFDeriv ℝ n (gaussianFun (E := E)) x‖ ≤
      C * (1 + ‖x‖) ^ k * Real.exp (-π * ‖x‖ ^ 2) := by
  set q : E → ℝ := fun x ↦ -π * ‖x‖ ^ 2 with hq_def
  have hq : q.HasTemperateGrowth := (HasTemperateGrowth.const (-π)).mul (hasTemperateGrowth_norm_sq E)
  have hqs : ContDiff ℝ ∞ q := contDiff_const.mul (contDiff_norm_sq ℝ)
  obtain ⟨k, C, hC, hb⟩ := hq.norm_iteratedFDeriv_le_uniform n
  refine ⟨n ! * max C 1 ^ n, k * n, by positivity, fun x ↦ ?_⟩
  have hx1 : 1 ≤ (1 + ‖x‖) ^ k := one_le_pow₀ (by linarith [norm_nonneg x])
  set D := max C 1 * (1 + ‖x‖) ^ k
  have hD1 : 1 ≤ D := one_le_mul_of_one_le_of_one_le (le_max_right _ _) hx1
  have hcomp : ‖iteratedFDeriv ℝ n (Real.exp ∘ q) x‖ ≤ n ! * Real.exp (q x) * D ^ n := by
    refine norm_iteratedFDeriv_comp_le Real.contDiff_exp hqs (by exact_mod_cast le_top) x
      (fun i _ ↦ (norm_iteratedFDeriv_exp i (q x)).le) fun i hi1 hin ↦ ?_
    calc ‖iteratedFDeriv ℝ i q x‖ ≤ C * (1 + ‖x‖) ^ k := hb i hin x
      _ ≤ D := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ D ^ i := le_self_pow₀ hD1 (by omega)
  have hG : gaussianFun (E := E) = (Complex.ofRealLI : ℝ →ₗᵢ[ℝ] ℂ) ∘ (Real.exp ∘ q) := rfl
  rw [hG, LinearIsometry.norm_iteratedFDeriv_comp_left _
    (Real.contDiff_exp.comp hqs).contDiffAt (by exact_mod_cast le_top)]
  refine hcomp.trans (le_of_eq ?_)
  simp only [D, mul_pow, ← pow_mul, hq_def]
  ring
def gaussianSchwartz (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] : 𝓢(E, ℂ) where
  toFun := gaussianFun
  smooth' := contDiff_gaussianFun
  decay' k n := by
    obtain ⟨C, j, hC, hb⟩ := norm_iteratedFDeriv_gaussian_le (E := E) n
    refine ⟨C * Real.exp ((k + j : ℕ) ^ 2 / (4 * π)), fun x ↦ ?_⟩
    have hk : ‖x‖ ^ k ≤ (1 + ‖x‖) ^ k := pow_le_pow_left₀ (norm_nonneg x) (by linarith) k
    calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n gaussianFun x‖
        ≤ (1 + ‖x‖) ^ k * (C * (1 + ‖x‖) ^ j * Real.exp (-π * ‖x‖ ^ 2)) :=
          mul_le_mul hk (hb x) (norm_nonneg _) (by positivity)
      _ = C * ((1 + ‖x‖) ^ (k + j) * Real.exp (-π * ‖x‖ ^ 2)) := by rw [pow_add]; ring
      _ ≤ C * Real.exp ((k + j : ℕ) ^ 2 / (4 * π)) :=
          mul_le_mul_of_nonneg_left (one_add_pow_mul_exp_neg_pi_mul_sq_le (norm_nonneg x) _) hC
end
end GroundTheory.Global


