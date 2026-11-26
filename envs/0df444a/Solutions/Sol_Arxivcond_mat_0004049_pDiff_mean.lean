-- Prove2me | solution 1 for Arxivcond_mat_0004049.pDiff_mean
-- status  : ACCEPTED   (prove)
-- author  : @domodus
-- created : 2026-11-26T13:58:39.761409+00:00
-- url     : https://prove2.me/submissions/08b4f4fa-9ccc-499f-a72a-0f4d24c8bfa1

import Mathlib
import Definitions.Def_Arxivcond_mat_0004049_Basic

open MeasureTheory Filter Topology

namespace Arxivcond_mat_0004049

/-- `D^{-3/2} = (D √D)⁻¹` for `D > 0`. -/
private lemma rpow_neg_three_halves {D : ℝ} (hD : 0 < D) :
    D ^ (-(3 : ℝ) / 2) = (D * Real.sqrt D)⁻¹ := by
  rw [show (-(3 : ℝ) / 2) = -(1 + 1 / 2) by norm_num, Real.rpow_neg hD.le, Real.rpow_add hD,
    Real.rpow_one, ← Real.sqrt_eq_rpow]

/-- `φ P_diff(φ) = Q (1 + t) / (2 D √D)` with `t = φ/φ̄ - 1`, `D = Q + t²`. -/
private lemma mul_pDiff_eq (Q phibar φ : ℝ) (hQ : 0 < Q) (hphibar : 0 < phibar) :
    φ * pDiff Q phibar φ =
      Q * (1 + (φ / phibar - 1)) / (2 * ((Q + (φ / phibar - 1) ^ 2) *
        Real.sqrt (Q + (φ / phibar - 1) ^ 2))) := by
  have hD : 0 < Q + (φ / phibar - 1) ^ 2 := by positivity
  rw [pDiff, rpow_neg_three_halves hD]
  field_simp
  ring

/-- Antiderivative of `φ P_diff(φ)`: `F(φ) = φ̄ (t - Q) / (2 √(Q + t²))`, `t = φ/φ̄ - 1`. -/
private noncomputable def antideriv (Q phibar φ : ℝ) : ℝ :=
  phibar * ((φ / phibar - 1) - Q) / (2 * Real.sqrt (Q + (φ / phibar - 1) ^ 2))

private lemma hasDerivAt_antideriv (Q phibar φ : ℝ) (hQ : 0 < Q) (hphibar : 0 < phibar) :
    HasDerivAt (antideriv Q phibar) (φ * pDiff Q phibar φ) φ := by
  set t := φ / phibar - 1 with ht
  have hD : 0 < Q + t ^ 2 := by positivity
  have hs : 0 < Real.sqrt (Q + t ^ 2) := Real.sqrt_pos.2 hD
  have hss : Real.sqrt (Q + t ^ 2) ^ 2 = Q + t ^ 2 := Real.sq_sqrt hD.le
  have ht' : HasDerivAt (fun x : ℝ => x / phibar - 1) (1 / phibar) φ := by
    simpa using ((hasDerivAt_id φ).div_const phibar).sub_const 1
  have hnum : HasDerivAt (fun x : ℝ => phibar * ((x / phibar - 1) - Q)) (phibar * (1 / phibar)) φ :=
    (ht'.sub_const Q).const_mul phibar
  have hsq : HasDerivAt (fun x : ℝ => Q + (x / phibar - 1) ^ 2) (2 * t * (1 / phibar)) φ := by
    have := (ht'.pow 2).const_add Q
    simpa [ht, mul_comm, mul_assoc, mul_left_comm] using this
  have hden : HasDerivAt (fun x : ℝ => 2 * Real.sqrt (Q + (x / phibar - 1) ^ 2))
      (2 * ((2 * t * (1 / phibar)) / (2 * Real.sqrt (Q + t ^ 2)))) φ :=
    (hsq.sqrt hD.ne').const_mul 2
  have := hnum.div hden (by positivity)
  have hfun : antideriv Q phibar = fun x : ℝ =>
      phibar * ((x / phibar - 1) - Q) / (2 * Real.sqrt (Q + (x / phibar - 1) ^ 2)) := rfl
  rw [hfun]
  refine this.congr_deriv ?_
  rw [mul_pDiff_eq Q phibar φ hQ hphibar, ← ht]
  field_simp
  rw [hss]
  ring

/-- `F(φ) = ± φ̄ k(φ⁻¹)` where `k u = (1/φ̄ - (1+Q) u) / (2 √(Q u² + (1/φ̄ - u)²))`. -/
private lemma antideriv_eq (Q phibar φ : ℝ) (hQ : 0 < Q) (hphibar : 0 < phibar) (hφ : φ ≠ 0) :
    antideriv Q phibar φ = SignType.sign φ * phibar *
      ((1 / phibar - (1 + Q) * φ⁻¹) /
        (2 * Real.sqrt (Q * φ⁻¹ ^ 2 + (1 / phibar - φ⁻¹) ^ 2))) := by
  have hE : Q + (φ / phibar - 1) ^ 2 = φ ^ 2 * (Q * φ⁻¹ ^ 2 + (1 / phibar - φ⁻¹) ^ 2) := by
    field_simp
  have hpos : 0 < Q * φ⁻¹ ^ 2 + (1 / phibar - φ⁻¹) ^ 2 := by positivity
  rw [antideriv, hE, Real.sqrt_mul (sq_nonneg φ), Real.sqrt_sq_eq_abs]
  have hsq := Real.sqrt_pos.2 hpos
  rcases lt_or_gt_of_ne hφ with h | h
  · rw [abs_of_neg h, sign_neg h]
    simp only [SignType.coe_neg_one]
    field_simp
    ring
  · rw [abs_of_pos h, sign_pos h]
    simp only [SignType.coe_one]
    field_simp
    ring

private lemma tendsto_antideriv (Q phibar : ℝ) (hQ : 0 < Q) (hphibar : 0 < phibar) :
    Tendsto (antideriv Q phibar) atTop (𝓝 (phibar / 2)) ∧
      Tendsto (antideriv Q phibar) atBot (𝓝 (-(phibar / 2))) := by
  set k : ℝ → ℝ := fun u =>
    (1 / phibar - (1 + Q) * u) / (2 * Real.sqrt (Q * u ^ 2 + (1 / phibar - u) ^ 2)) with hk
  have hk0 : k 0 = 1 / 2 := by
    simp only [hk]
    rw [show Q * (0 : ℝ) ^ 2 + (1 / phibar - 0) ^ 2 = (1 / phibar) ^ 2 by ring,
      Real.sqrt_sq (by positivity)]
    field_simp
    simp
  have hkc : ContinuousAt k 0 := by
    refine ContinuousAt.div (by fun_prop) (by fun_prop) ?_
    simp; positivity
  constructor
  · have hlim : Tendsto (fun φ : ℝ => (1 : ℝ) * phibar * k φ⁻¹) atTop (𝓝 (1 * phibar * k 0)) :=
      (hkc.tendsto.comp tendsto_inv_atTop_zero).const_mul _
    rw [hk0] at hlim
    refine (hlim.congr' ?_).trans (by norm_num [div_eq_mul_inv])
    filter_upwards [eventually_gt_atTop 0] with φ hφ
    rw [antideriv_eq Q phibar φ hQ hphibar hφ.ne', sign_pos hφ]
    simp [hk]
  · have hlim : Tendsto (fun φ : ℝ => (-1 : ℝ) * phibar * k φ⁻¹) atBot (𝓝 (-1 * phibar * k 0)) :=
      (hkc.tendsto.comp tendsto_inv_atBot_zero).const_mul _
    rw [hk0] at hlim
    refine (hlim.congr' ?_).trans (by norm_num [div_eq_mul_inv])
    filter_upwards [eventually_lt_atBot 0] with φ hφ
    rw [antideriv_eq Q phibar φ hQ hphibar hφ.ne, sign_neg hφ]
    simp [hk]

/-- Pointwise domination `|φ P_diff(φ)| ≤ K (1 + t²)⁻¹`, `t = φ/φ̄ - 1`. -/
private lemma norm_mul_pDiff_le (Q phibar φ : ℝ) (hQ : 0 < Q) (hphibar : 0 < phibar) :
    ‖φ * pDiff Q phibar φ‖ ≤
      Q * (1 / Real.sqrt Q + 1) / (2 * min Q 1) * (1 + (φ / phibar - 1) ^ 2)⁻¹ := by
  set t := φ / phibar - 1
  set m := min Q 1
  have hm : 0 < m := lt_min hQ one_pos
  have hD : 0 < Q + t ^ 2 := by positivity
  set s := Real.sqrt (Q + t ^ 2)
  have hs : 0 < s := Real.sqrt_pos.2 hD
  have hss : s ^ 2 = Q + t ^ 2 := Real.sq_sqrt hD.le
  have hsQ : Real.sqrt Q ≤ s := Real.sqrt_le_sqrt (by nlinarith)
  have hsQ0 : 0 < Real.sqrt Q := Real.sqrt_pos.2 hQ
  have hst : |1 + t| ≤ 1 + s := by
    have : |t| ≤ s := Real.abs_le_sqrt (by nlinarith)
    exact (abs_add_le 1 t).trans (by simpa using this)
  have hDm : m * (1 + t ^ 2) ≤ Q + t ^ 2 := by
    have h1 : m ≤ Q := min_le_left _ _
    have h2 : m ≤ 1 := min_le_right _ _
    nlinarith [sq_nonneg t]
  rw [mul_pDiff_eq Q phibar φ hQ hphibar, Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hQ,
    abs_of_pos (by positivity : (0 : ℝ) < 2 * ((Q + t ^ 2) * s))]
  calc Q * |1 + t| / (2 * ((Q + t ^ 2) * s))
      ≤ Q * (1 + s) / (2 * ((Q + t ^ 2) * s)) := by gcongr
    _ = Q * (1 / s + 1) / (2 * (Q + t ^ 2)) := by field_simp
    _ ≤ Q * (1 / Real.sqrt Q + 1) / (2 * (m * (1 + t ^ 2))) := by gcongr
    _ = Q * (1 / Real.sqrt Q + 1) / (2 * m) * (1 + t ^ 2)⁻¹ := by field_simp

private theorem pDiff_mean_aux (Q phibar : ℝ) (hQ : 0 < Q) (hphibar : 0 < phibar) :
    Integrable (fun φ : ℝ => φ * pDiff Q phibar φ) ∧
      ∫ φ : ℝ, φ * pDiff Q phibar φ = phibar := by
  have hint : Integrable (fun φ : ℝ => φ * pDiff Q phibar φ) := by
    have hg : Integrable (fun φ : ℝ => (1 + (φ / phibar - 1) ^ 2)⁻¹) :=
      (integrable_inv_one_add_sq.comp_sub_right 1).comp_div hphibar.ne'
    refine (hg.const_mul (Q * (1 / Real.sqrt Q + 1) / (2 * min Q 1))).mono' ?_
      (Eventually.of_forall fun φ => norm_mul_pDiff_le Q phibar φ hQ hphibar)
    exact (by unfold pDiff; fun_prop : Measurable _).aestronglyMeasurable
  refine ⟨hint, ?_⟩
  obtain ⟨htop, hbot⟩ := tendsto_antideriv Q phibar hQ hphibar
  rw [integral_of_hasDerivAt_of_tendsto (fun φ => hasDerivAt_antideriv Q phibar φ hQ hphibar)
    hint hbot htop]
  ring

end Arxivcond_mat_0004049

open Arxivcond_mat_0004049 in
theorem solution (Q phibar : ℝ) (hQ : 0 < Q) (hphibar : 0 < phibar) :
    Integrable (fun φ : ℝ => φ * pDiff Q phibar φ) ∧
      ∫ φ : ℝ, φ * pDiff Q phibar φ = phibar :=
  pDiff_mean_aux Q phibar hQ hphibar
