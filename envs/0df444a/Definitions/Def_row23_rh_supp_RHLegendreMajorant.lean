-- Prove2me | Definitions.Def_row23_rh_supp_RHLegendreMajorant
-- name    : row23_rh_supp_RHLegendreMajorant
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:00:48.474625+00:00
-- url     : https://prove2.me/theorems/697c3ea6-a792-41e1-b5b0-6c46859ef4d9
-- title:
--   Row 23 RH support: RHLegendreMajorant
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLegendreIntegration
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace DusartLegendreSmoothing
open Polynomial Complex MeasureTheory intervalIntegral
lemma iterated_weight_continuous (m k : ℕ) : Continuous (iteratedDeriv k (weight m)) := by
  have he : iteratedDeriv k (weight m)=fun t : ℝ => (derivative^[k] (densityPolynomial m)).eval t := by
    funext t
    exact iteratedDeriv_weight m k t
  rw [he]
  exact (derivative^[k] (densityPolynomial m)).continuous
 theorem weighted_norm_after_ibp (m : ℕ) (δ B : ℝ) (F : ℕ → ℝ → ℂ)
    (hc : ∀ k ≤ m, ContinuousOn (F k) (Set.uIcc (0:ℝ) 1))
    (hd : ∀ k < m, ∀ t ∈ Set.uIcc (0:ℝ) 1, HasDerivAt (F k) (F (k+1) t) t)
    (hpoint : ∀ t ∈ Set.uIcc (0:ℝ) 1, ‖F 0 t‖≤B*(1+δ*t)^(m+1)) :
    ‖∫ t : ℝ in 0..1, (weight m t:ℂ)*F m t‖ ≤ B*derivativeMass m δ := by
  rw [weighted_integration_by_parts m F hc hd,norm_mul,norm_pow]
  simp only [norm_neg,norm_one,one_pow,one_mul]
  let g : ℝ → ℝ := fun t => B*(|iteratedDeriv m (weight m) t| * (1+δ*t)^(m+1))
  have hw := iterated_weight_continuous m m
  have hg : IntervalIntegrable g volume 0 1 := by
    apply Continuous.intervalIntegrable
    dsimp [g]
    fun_prop
  have hb : ∀ t ∈ Set.Ioc (0:ℝ) 1,
      ‖((iteratedDeriv m (weight m) t:ℝ):ℂ)*F 0 t‖ ≤ g t := by
    intro t ht
    have ht' : t ∈ Set.uIcc (0:ℝ) 1 := by
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ)≤1)]
      exact ⟨ht.1.le,ht.2⟩
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    calc
      _ ≤ |iteratedDeriv m (weight m) t| * (B*(1+δ*t)^(m+1)) :=
        mul_le_mul_of_nonneg_left (hpoint t ht') (abs_nonneg _)
      _ = _ := by dsimp [g]; ring
  have h := intervalIntegral.norm_integral_le_of_norm_le (by norm_num : (0:ℝ)≤1)
    (Filter.Eventually.of_forall hb) hg
  simpa only [g,intervalIntegral.integral_const_mul,derivativeMass] using h
end DusartLegendreSmoothing
#print axioms DusartLegendreSmoothing.weighted_norm_after_ibp


