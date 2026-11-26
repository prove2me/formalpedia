-- Prove2me | Definitions.Def_Section5Verified_Section5HermiteFoundations
-- name    : Section5Verified_Section5HermiteFoundations
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-26T19:20:56.044193+00:00
-- url     : https://prove2.me/theorems/4f582df5-995e-5f71-9220-9bb562897e6a
-- title:
--   Section5HermiteFoundations — verified interface
-- statement:
--   Finite register types, encodings, and structural interfaces used by the Section 5 supporting constructions. The included identities are required to make these definitions importable with their verified semantics.
-- source:
--   Supporting formalization for https://arxiv.org/html/2609.40331v3, Section 5; original source Solutions.Section5HermiteFoundations; mechanically extracted with exact Lean declaration spans.

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_splitReg
import Mathlib
section
set_option autoImplicit false

namespace Aux_w_53_hermite

open MeasureTheory Filter Polynomial QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement
open scoped Real Topology Nat ENNReal

/-! ### Part 1: 1D Gaussian Density, Orthonormal Hermite Functions, and `sgn` Coefficients -/

noncomputable def phi (x : ℝ) : ℝ := ProbabilityTheory.gaussianPDFReal 0 1 x

lemma phi_def (x : ℝ) : phi x = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2 / 2)) := by
  simp [phi, ProbabilityTheory.gaussianPDFReal, sub_zero, NNReal.coe_one, mul_one, neg_div]





lemma phi_pos (x : ℝ) : 0 < phi x :=
  ProbabilityTheory.gaussianPDFReal_pos 0 1 x one_ne_zero

lemma continuous_phi : Continuous phi := by
  have : phi = fun x => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2 / 2)) :=
    funext phi_def
  rw [this]
  fun_prop





noncomputable def Hpoly (j : ℕ) (x : ℝ) : ℝ :=
  Polynomial.aeval x (Polynomial.hermite j)









noncomputable def h1D (j : ℕ) (x : ℝ) : ℝ :=
  (Real.sqrt (j.factorial : ℝ))⁻¹ * Hpoly j x



lemma continuous_h1D (j : ℕ) : Continuous (h1D j) := by
  have : h1D j = fun x =>
      (Real.sqrt (j.factorial : ℝ))⁻¹ * ((Polynomial.hermite j).map (algebraMap ℤ ℝ)).eval x := by
    ext x; simp [h1D, Hpoly, Polynomial.aeval_def, Polynomial.eval_map]
  rw [this]
  fun_prop

lemma h1D_zero_fn (x : ℝ) : h1D 0 x = 1 := by
  simp [h1D, Hpoly]





noncomputable def h1D_deriv (j : ℕ) (x : ℝ) : ℝ :=
  if j = 0 then 0 else Real.sqrt (j : ℝ) * h1D (j - 1) x









lemma integrable_pow_mul_phi (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k * phi x) volume := by
  have heven : ∀ m : ℕ, Integrable (fun x : ℝ => x ^ (2 * m) * phi x) volume := by
    intro m
    have h := (integrable_rpow_mul_exp_neg_mul_sq (b := (1 / 2 : ℝ)) (by norm_num)
      (s := (2 * m : ℕ)) (by linarith [show (0 : ℝ) ≤ (2 * m : ℕ) by positivity])).const_mul
      (Real.sqrt (2 * Real.pi))⁻¹
    refine h.congr (ae_of_all _ fun x => ?_)
    simp only [Real.rpow_natCast, phi_def]
    ring
  have hdom : Integrable (fun x : ℝ => (1 + x ^ (2 * k)) * phi x) volume := by
    have h0 := heven 0
    have hk := heven k
    simp only [mul_zero, pow_zero, one_mul] at h0
    have hadd := h0.add hk
    refine hadd.congr (ae_of_all _ fun x => ?_)
    simp [add_mul]
  refine hdom.mono' ((continuous_pow k).mul continuous_phi).aestronglyMeasurable
    (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (phi_pos x), abs_pow]
  have hx : |x| ^ k ≤ 1 + x ^ (2 * k) := by
    by_cases h1 : |x| ≤ 1
    · have : |x| ^ k ≤ 1 := pow_le_one₀ (abs_nonneg x) h1
      have hx2 : 0 ≤ x ^ (2 * k) := by rw [mul_comm, pow_mul]; exact sq_nonneg _
      linarith
    · have h1' : 1 < |x| := lt_of_not_ge h1
      have hpow : |x| ^ k ≤ |x| ^ (2 * k) := pow_le_pow_right₀ h1'.le (by omega)
      have hsq : |x| ^ (2 * k) = x ^ (2 * k) := by rw [pow_mul, sq_abs, ← pow_mul]
      linarith
  exact mul_le_mul_of_nonneg_right hx (phi_pos x).le

lemma integrable_poly_mul_phi (P : Polynomial ℝ) :
    Integrable (fun x : ℝ => P.eval x * phi x) volume := by
  have hsum : (fun x : ℝ => P.eval x * phi x) =
      fun x => ∑ i ∈ P.support, (P.coeff i) * (x ^ i * phi x) := by
    ext x
    rw [Polynomial.eval_eq_sum, Polynomial.sum_def, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hsum]
  exact integrable_finsetSum _ fun i _ => (integrable_pow_mul_phi i).const_mul _

lemma integrable_h1D_mul_h1D_mul_phi (j k : ℕ) :
    Integrable (fun x : ℝ => h1D j x * h1D k x * phi x) volume := by
  let P : Polynomial ℝ :=
    Polynomial.C ((Real.sqrt (j.factorial : ℝ))⁻¹ * (Real.sqrt (k.factorial : ℝ))⁻¹) *
      ((Polynomial.hermite j).map (algebraMap ℤ ℝ) * (Polynomial.hermite k).map (algebraMap ℤ ℝ))
  have hfn : (fun x : ℝ => h1D j x * h1D k x * phi x) = fun x => P.eval x * phi x := by
    ext x
    simp only [P, h1D, Hpoly, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.aeval_def, Polynomial.eval_map]
    ring
  rw [hfn]
  exact integrable_poly_mul_phi P































/-! ### Part 2: Multivariate Hermite Orthonormality & Orthogonal-Projection Invariance -/

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

noncomputable def γ (n : ℕ) : Measure (E n) := ProbabilityTheory.stdGaussian (E n)

instance isProbabilityMeasure_γ (n : ℕ) : IsProbabilityMeasure (γ n) := by
  unfold γ
  infer_instance

noncomputable def Hnd {n : ℕ} (α : Fin n → ℕ) (g : E n) : ℝ :=
  ∏ i : Fin n, h1D (α i) (g i)





















end Aux_w_53_hermite


end


