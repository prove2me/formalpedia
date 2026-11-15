-- Prove2me | Definitions.Def_RPLib_S3_EllW2PN4
-- name    : RPLib_S3_EllW2PN4
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T13:47:17.905666+00:00
-- url     : https://prove2.me/theorems/f478d95f-d890-45f4-b955-80237fffc2c4
-- title:
--   The Eichler-Selberg trace formula in weight two: the main term of the NHS zero mode
-- statement:
--   The main term of the NHS zero mode.
--
--   * `rpow_sub_bound`: `|R^(-s) - K^(-s)| R⁻¹ ≤ 4 s K^(-s) K^(-1/4) R^(-3/4)` for `0 < K ≤ R`, `s ≥ 0`.
--   * `g34 σ = (1 + σ²)^(-3/4)`, `K34 = ∫ g34`; `integrable_g34`.
--   * `aR_rpow34`, `integral_aR_rpow34`: `∫ aR^(-3/4) = (4c²y²)^(-3/4) · 2|c|y · K34`.
--   * `Rp_rpow34_le`, `integrable_Rp34`, `integral_Rp34_le`.
--   * `integral_VN_eq`: `∫ VN = y² n^s ∫ Q⁻² (Rp^(-s) - (c²y²)^(-s))` (`∫ Q⁻² = 0`).
--   * `norm_integral_VN_le_main`, **`norm_integral_VN_le_final`**:
--     `|∫_t VN| ≤ 16 K34 s n^s (c²y²)^(-s) / (|c| y) · (2y²/(u²+y²))^(3/4)`.
--   * `M34_eq`, `integrable_M34`, **`integral_M34`**: `∫_u (2y²/(u²+y²))^(3/4) = 2^(3/4) y K34`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224

import Mathlib
import Definitions.Def_RPLib_S3_EllW2PN3

/-!
# S3-ES-Wt2 (O6, file PN4): the main term of the NHS zero mode

* `rpow_sub_bound`: `|R^(-s) - K^(-s)| R⁻¹ ≤ 4 s K^(-s) K^(-1/4) R^(-3/4)` for `0 < K ≤ R`, `s ≥ 0`.
* `g34 σ = (1 + σ²)^(-3/4)`, `K34 = ∫ g34`; `integrable_g34`.
* `aR_rpow34`, `integral_aR_rpow34`: `∫ aR^(-3/4) = (4c²y²)^(-3/4) · 2|c|y · K34`.
* `Rp_rpow34_le`, `integrable_Rp34`, `integral_Rp34_le`.
* `integral_VN_eq`: `∫ VN = y² n^s ∫ Q⁻² (Rp^(-s) - (c²y²)^(-s))` (`∫ Q⁻² = 0`).
* `norm_integral_VN_le_main`, **`norm_integral_VN_le_final`**:
  `|∫_t VN| ≤ 16 K34 s n^s (c²y²)^(-s) / (|c| y) · (2y²/(u²+y²))^(3/4)`.
* `M34_eq`, `integrable_M34`, **`integral_M34`**: `∫_u (2y²/(u²+y²))^(3/4) = 2^(3/4) y K34`.
-/

open MeasureTheory Set Filter Real

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EllW2

/-- The key real inequality (with `x = R/K ≥ 1`: `1 - x^(-s) ≤ s log x ≤ 4 s x^(1/4)`). -/
lemma rpow_sub_bound {K R s : ℝ} (hK : 0 < K) (hKR : K ≤ R) (hs : 0 ≤ s) :
    |R ^ (-s) - K ^ (-s)| * R⁻¹ ≤ 4 * s * K ^ (-s) * (K ^ (-(1 / 4 : ℝ)) * R ^ (-(3 / 4 : ℝ))) := by
  obtain ⟨x, hx1, rfl⟩ : ∃ x, 1 ≤ x ∧ R = K * x :=
    ⟨R / K, (one_le_div hK).2 hKR, by
      have hK0 : K ≠ 0 := hK.ne'
      first
      | field_simp
      | (field_simp; ring)⟩
  have hx0 : 0 < x := lt_of_lt_of_le one_pos hx1
  have hxs : x ^ (-s) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith)
  have hlog : 1 - x ^ (-s) ≤ s * Real.log x := by
    have h := Real.add_one_le_exp (Real.log x * (-s))
    rw [← Real.rpow_def_of_pos hx0] at h
    linarith
  have hlog2 : Real.log x ≤ 4 * x ^ (1 / 4 : ℝ) := by
    calc Real.log x ≤ x ^ (1 / 4 : ℝ) / (1 / 4) :=
          Real.log_le_rpow_div hx0.le (by norm_num)
      _ = 4 * x ^ (1 / 4 : ℝ) := by ring
  have hmain : 1 - x ^ (-s) ≤ 4 * s * x ^ (1 / 4 : ℝ) := by
    have := mul_le_mul_of_nonneg_left hlog2 hs
    linarith
  have e1 : K ^ (-(1 / 4 : ℝ)) * K ^ (-(3 / 4 : ℝ)) = K⁻¹ := by
    rw [← Real.rpow_add hK, show -(1 / 4 : ℝ) + -(3 / 4) = -1 by norm_num, Real.rpow_neg_one]
  have e2 : x ^ (-(3 / 4 : ℝ)) = x ^ (1 / 4 : ℝ) * x⁻¹ := by
    rw [show -(3 / 4 : ℝ) = 1 / 4 - 1 by norm_num, Real.rpow_sub_one hx0.ne', div_eq_mul_inv]
  have hKs := Real.rpow_nonneg hK.le (-s)
  have hxs1 : 0 ≤ 1 - x ^ (-s) := by linarith
  rw [Real.mul_rpow hK.le hx0.le, Real.mul_rpow hK.le hx0.le, mul_inv,
    show K ^ (-s) * x ^ (-s) - K ^ (-s) = -(K ^ (-s) * (1 - x ^ (-s))) by ring, abs_neg,
    abs_of_nonneg (mul_nonneg hKs hxs1), ← mul_assoc (K ^ (-(1 / 4 : ℝ))), e1, e2]
  have hKi : 0 ≤ K⁻¹ * x⁻¹ := mul_nonneg (inv_nonneg.2 hK.le) (inv_nonneg.2 hx0.le)
  calc K ^ (-s) * (1 - x ^ (-s)) * (K⁻¹ * x⁻¹)
      ≤ K ^ (-s) * (4 * s * x ^ (1 / 4 : ℝ)) * (K⁻¹ * x⁻¹) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmain hKs) hKi
    _ = 4 * s * K ^ (-s) * (K⁻¹ * (x ^ (1 / 4 : ℝ) * x⁻¹)) := by ring

/-! ## The `(1 + σ²)^(-3/4)` profile -/

/-- `g34 σ = (1 + σ²)^(-3/4)`. -/
def g34 (σ : ℝ) : ℝ := (1 + σ ^ 2) ^ (-(3 / 4 : ℝ))

/-- `K34 = ∫ (1 + σ²)^(-3/4) dσ`. -/
def K34 : ℝ := ∫ σ, g34 σ

lemma integrable_g34 : Integrable g34 := by
  have h := integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) (r := 3 / 2)
    (by norm_num [Module.finrank_self])
  refine h.congr (Eventually.of_forall fun x => ?_)
  simp only [g34, Real.norm_eq_abs, sq_abs]
  norm_num

lemma g34_nonneg (σ : ℝ) : 0 ≤ g34 σ := Real.rpow_nonneg (by positivity) _

lemma K34_nonneg : 0 ≤ K34 := integral_nonneg g34_nonneg

variable {c n u y : ℝ}

lemma aR_eq_g34 (hc : c ≠ 0) (hy : 0 < y) (w t : ℝ) :
    aR c y w t = 4 * (c ^ 2 * y ^ 2) * (1 + ((t - w) / (2 * |c| * y)) ^ 2) := by
  have hb : 2 * |c| * y ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero (abs_ne_zero.2 hc)) hy.ne'
  have hb2 : (2 * |c| * y) ^ 2 = 4 * (c ^ 2 * y ^ 2) := by rw [mul_pow, mul_pow, sq_abs]; ring
  rw [aR_eq, ← hb2]
  first
  | (field_simp; ring)
  | field_simp
  | (rw [div_pow]; field_simp; ring)

lemma aR_rpow34 (hc : c ≠ 0) (hy : 0 < y) (w t : ℝ) :
    aR c y w t ^ (-(3 / 4 : ℝ)) =
      (4 * (c ^ 2 * y ^ 2)) ^ (-(3 / 4 : ℝ)) * g34 ((t - w) / (2 * |c| * y)) := by
  rw [aR_eq_g34 hc hy, Real.mul_rpow (by positivity) (by positivity), g34]

lemma integrable_aR34 (hc : c ≠ 0) (hy : 0 < y) (w : ℝ) :
    Integrable fun t => aR c y w t ^ (-(3 / 4 : ℝ)) := by
  have hb : 2 * |c| * y ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero (abs_ne_zero.2 hc)) hy.ne'
  refine (((integrable_g34.comp_div hb).comp_sub_right w).const_mul
    ((4 * (c ^ 2 * y ^ 2)) ^ (-(3 / 4 : ℝ)))).congr (Eventually.of_forall fun t => ?_)
  show (4 * (c ^ 2 * y ^ 2)) ^ (-(3 / 4 : ℝ)) * g34 ((t - w) / (2 * |c| * y)) =
    aR c y w t ^ (-(3 / 4 : ℝ))
  rw [aR_rpow34 hc hy]

lemma integral_aR_rpow34 (hc : c ≠ 0) (hy : 0 < y) (w : ℝ) :
    ∫ t, aR c y w t ^ (-(3 / 4 : ℝ)) =
      (4 * (c ^ 2 * y ^ 2)) ^ (-(3 / 4 : ℝ)) * (2 * |c| * y * K34) := by
  have hb : 0 < 2 * |c| * y := mul_pos (mul_pos two_pos (abs_pos.2 hc)) hy
  simp_rw [aR_rpow34 hc hy w]
  rw [integral_const_mul]
  congr 1
  have h1 : ∫ t, g34 ((t - w) / (2 * |c| * y)) = ∫ t, g34 (t / (2 * |c| * y)) :=
    integral_sub_right_eq_self (fun t => g34 (t / (2 * |c| * y))) w
  rw [h1, Measure.integral_comp_div g34 (2 * |c| * y), abs_of_pos hb, smul_eq_mul]
  rfl

/-! ## The `Rp^(-3/4)` integral -/

lemma Rp_rpow34_le (hc : c ≠ 0) (hy : y ≠ 0) (hn : 0 ≤ n) (t : ℝ) :
    Rp c n u y t ^ (-(3 / 4 : ℝ)) ≤ (2 * y ^ 2 / (u ^ 2 + y ^ 2)) ^ (3 / 4 : ℝ) *
      (aR c y (wR c n u) t ^ (-(3 / 4 : ℝ)) + aR c y (-wR c n u) t ^ (-(3 / 4 : ℝ))) := by
  have hR := Rp_pos (u := u) hc hy hn t
  have ha := aR_pos hc hy (wR c n u) t
  have hb := aR_pos hc hy (-wR c n u) t
  have hM : 0 ≤ 2 * y ^ 2 / (u ^ 2 + y ^ 2) := by positivity
  have e : ∀ x : ℝ, 0 < x → x ^ (-(3 / 4 : ℝ)) = x⁻¹ ^ (3 / 4 : ℝ) := fun x hx => by
    rw [Real.rpow_neg hx.le, Real.inv_rpow hx.le]
  calc Rp c n u y t ^ (-(3 / 4 : ℝ)) = (Rp c n u y t)⁻¹ ^ (3 / 4 : ℝ) := e _ hR
    _ ≤ (2 * y ^ 2 / (u ^ 2 + y ^ 2) *
          ((aR c y (wR c n u) t)⁻¹ + (aR c y (-wR c n u) t)⁻¹)) ^ (3 / 4 : ℝ) :=
        Real.rpow_le_rpow (inv_nonneg.2 hR.le) (inv_Rp_le hc hy hn t) (by norm_num)
    _ = (2 * y ^ 2 / (u ^ 2 + y ^ 2)) ^ (3 / 4 : ℝ) *
          ((aR c y (wR c n u) t)⁻¹ + (aR c y (-wR c n u) t)⁻¹) ^ (3 / 4 : ℝ) :=
        Real.mul_rpow hM (add_nonneg (inv_nonneg.2 ha.le) (inv_nonneg.2 hb.le))
    _ ≤ (2 * y ^ 2 / (u ^ 2 + y ^ 2)) ^ (3 / 4 : ℝ) *
          ((aR c y (wR c n u) t)⁻¹ ^ (3 / 4 : ℝ) + (aR c y (-wR c n u) t)⁻¹ ^ (3 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left (Real.rpow_add_le_add_rpow (inv_nonneg.2 ha.le)
          (inv_nonneg.2 hb.le) (by norm_num) (by norm_num)) (Real.rpow_nonneg hM _)
    _ = _ := by rw [e _ ha, e _ hb]

lemma integrable_Rp34 (hc : c ≠ 0) (hy : 0 < y) (hn : 0 ≤ n) :
    Integrable fun t => Rp c n u y t ^ (-(3 / 4 : ℝ)) := by
  refine (((integrable_aR34 hc hy (wR c n u)).add (integrable_aR34 hc hy (-wR c n u))).const_mul
    ((2 * y ^ 2 / (u ^ 2 + y ^ 2)) ^ (3 / 4 : ℝ))).mono' ?_ (Eventually.of_forall fun t => ?_)
  · exact ((continuous_Rp hc hy.ne' hn).rpow_const fun t =>
      Or.inl (Rp_pos hc hy.ne' hn t).ne').aestronglyMeasurable
  · rw [Real.norm_of_nonneg (Real.rpow_nonneg (Rp_pos hc hy.ne' hn t).le _)]
    exact Rp_rpow34_le hc hy.ne' hn t

lemma integral_Rp34_le (hc : c ≠ 0) (hy : 0 < y) (hn : 0 ≤ n) :
    ∫ t, Rp c n u y t ^ (-(3 / 4 : ℝ)) ≤ (2 * y ^ 2 / (u ^ 2 + y ^ 2)) ^ (3 / 4 : ℝ) *
      (2 * ((4 * (c ^ 2 * y ^ 2)) ^ (-(3 / 4 : ℝ)) * (2 * |c| * y * K34))) := by
  have h1 := integrable_aR34 hc hy (wR c n u)
  have h2 := integrable_aR34 hc hy (-wR c n u)
  calc ∫ t, Rp c n u y t ^ (-(3 / 4 : ℝ)) ≤ ∫ t, (2 * y ^ 2 / (u ^ 2 + y ^ 2)) ^ (3 / 4 : ℝ) *
        (aR c y (wR c n u) t ^ (-(3 / 4 : ℝ)) + aR c y (-wR c n u) t ^ (-(3 / 4 : ℝ))) :=
        integral_mono (integrable_Rp34 hc hy hn) ((h1.add h2).const_mul _)
          fun t => Rp_rpow34_le hc hy.ne' hn t
    _ = _ := by
        rw [integral_const_mul, integral_add h1 h2, integral_aR_rpow34 hc hy,
          integral_aR_rpow34 hc hy]
        ring

/-! ## The main term -/

/-- `∫ VN = y² n^s ∫ Q⁻² (Rp^(-s) - (c²y²)^(-s))`, since `∫ Q⁻² = 0`. -/
lemma integral_VN_eq {s : ℝ} (hs : 0 ≤ s) (hc : c ≠ 0) (hy : 0 < y) (hn : 0 < n) :
    ∫ t, VN s c n u y t = ((y ^ 2 * n ^ s : ℝ) : ℂ) *
      ∫ t, (Qp c n u y t ^ 2)⁻¹ * (((Rp c n u y t ^ (-s) - (c ^ 2 * y ^ 2) ^ (-s) : ℝ)) : ℂ) := by
  have hC : ((y ^ 2 * n ^ s : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (mul_pos (pow_pos hy 2) (Real.rpow_pos_of_pos hn s)).ne'
  have hI1 : Integrable fun t => (Qp c n u y t ^ 2)⁻¹ * ((Rp c n u y t ^ (-s) : ℝ) : ℂ) := by
    refine ((integrable_VN (u := u) hs hc hy hn.le).const_mul
      (((y ^ 2 * n ^ s : ℝ) : ℂ))⁻¹).congr (Eventually.of_forall fun t => ?_)
    simp only [VN]
    rw [← mul_assoc, inv_mul_cancel₀ hC, one_mul]
  have hI2 := integrable_inv_Qp_sq (u := u) hc hy hn.le
  have h0 := integral_inv_Qp_sq (u := u) hc hy hn
  have hV : ∫ t, VN s c n u y t = ((y ^ 2 * n ^ s : ℝ) : ℂ) *
      ∫ t, (Qp c n u y t ^ 2)⁻¹ * ((Rp c n u y t ^ (-s) : ℝ) : ℂ) :=
    integral_const_mul _ _
  rw [hV]
  congr 1
  simp only [Complex.ofReal_sub, mul_sub]
  rw [integral_sub hI1 (hI2.mul_const _), integral_mul_const, h0, zero_mul, sub_zero]

lemma norm_integral_VN_le_main {s : ℝ} (hs : 0 ≤ s) (hc : c ≠ 0) (hy : 0 < y) (hn : 0 < n) :
    ‖∫ t, VN s c n u y t‖ ≤ 4 * s * n ^ s * (c ^ 2 * y ^ 2) ^ (-s) *
      (c ^ 2 * y ^ 2) ^ (-(1 / 4 : ℝ)) * ∫ t, Rp c n u y t ^ (-(3 / 4 : ℝ)) := by
  have hA : 0 ≤ y ^ 2 * n ^ s := mul_nonneg (sq_nonneg y) (Real.rpow_nonneg hn.le s)
  have hK : 0 < c ^ 2 * y ^ 2 := mul_pos ((pow_pos (abs_pos.2 hc) 2).trans_eq (sq_abs c))
    (pow_pos hy 2)
  have hKu : ∀ t, c ^ 2 * y ^ 2 ≤ Rp c n u y t := fun t =>
    le_trans (by nlinarith [mul_nonneg (sq_nonneg c) (sq_nonneg u)]) (le_Rp hc hy.ne' hn.le t)
  have hbound : ∀ t, ‖(Qp c n u y t ^ 2)⁻¹ *
      (((Rp c n u y t ^ (-s) - (c ^ 2 * y ^ 2) ^ (-s) : ℝ)) : ℂ)‖ ≤
      (y ^ 2)⁻¹ * (4 * s * (c ^ 2 * y ^ 2) ^ (-s) *
        ((c ^ 2 * y ^ 2) ^ (-(1 / 4 : ℝ)) * Rp c n u y t ^ (-(3 / 4 : ℝ)))) := fun t => by
    rw [norm_mul, norm_inv_Qp_sq hy.ne', Complex.norm_real, Real.norm_eq_abs, VS, neg_zero,
      zero_sub, Real.rpow_neg_one, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 (sq_nonneg y))
    rw [mul_comm (Rp c n u y t)⁻¹]
    exact rpow_sub_bound hK (hKu t) hs
  have hint : Integrable fun t => (y ^ 2)⁻¹ * (4 * s * (c ^ 2 * y ^ 2) ^ (-s) *
      ((c ^ 2 * y ^ 2) ^ (-(1 / 4 : ℝ)) * Rp c n u y t ^ (-(3 / 4 : ℝ)))) :=
    (((integrable_Rp34 (u := u) hc hy hn.le).const_mul _).const_mul _).const_mul _
  have hy2 : y ^ 2 ≠ 0 := pow_ne_zero 2 hy.ne'
  rw [integral_VN_eq hs hc hy hn, norm_mul, Complex.norm_real, Real.norm_of_nonneg hA]
  calc y ^ 2 * n ^ s * ‖∫ t, (Qp c n u y t ^ 2)⁻¹ *
        (((Rp c n u y t ^ (-s) - (c ^ 2 * y ^ 2) ^ (-s) : ℝ)) : ℂ)‖
      ≤ y ^ 2 * n ^ s * ∫ t, (y ^ 2)⁻¹ * (4 * s * (c ^ 2 * y ^ 2) ^ (-s) *
        ((c ^ 2 * y ^ 2) ^ (-(1 / 4 : ℝ)) * Rp c n u y t ^ (-(3 / 4 : ℝ)))) :=
        mul_le_mul_of_nonneg_left (norm_integral_le_of_norm_le hint
          (Eventually.of_forall hbound)) hA
    _ = _ := by
        rw [integral_const_mul, integral_const_mul, integral_const_mul,
          show ∀ a b d : ℝ, a * b * (a⁻¹ * d) = (a * a⁻¹) * (b * d) from fun a b d => by ring,
          mul_inv_cancel₀ hy2, one_mul]
        ring

lemma K14_mul_K34_le (hc : c ≠ 0) (hy : 0 < y) :
    (c ^ 2 * y ^ 2) ^ (-(1 / 4 : ℝ)) * (4 * (c ^ 2 * y ^ 2)) ^ (-(3 / 4 : ℝ)) * (|c| * y) ≤
      1 / (|c| * y) := by
  have hcy : 0 < |c| * y := mul_pos (abs_pos.2 hc) hy
  have hKe : c ^ 2 * y ^ 2 = (|c| * y) ^ 2 := by rw [mul_pow, sq_abs]
  have hK : 0 < c ^ 2 * y ^ 2 := by rw [hKe]; positivity
  have e1 : (c ^ 2 * y ^ 2) ^ (-(1 / 4 : ℝ)) * (c ^ 2 * y ^ 2) ^ (-(3 / 4 : ℝ)) =
      (c ^ 2 * y ^ 2)⁻¹ := by
    rw [← Real.rpow_add hK, show -(1 / 4 : ℝ) + -(3 / 4) = -1 by norm_num, Real.rpow_neg_one]
  have h4 : (4 : ℝ) ^ (-(3 / 4 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have h40 : 0 ≤ (4 : ℝ) ^ (-(3 / 4 : ℝ)) := Real.rpow_nonneg (by norm_num) _
  have e2 : (c ^ 2 * y ^ 2)⁻¹ * (|c| * y) = 1 / (|c| * y) := by
    rw [hKe]; field_simp
  rw [Real.mul_rpow (by norm_num) hK.le,
    show ∀ a b d e : ℝ, a * (b * d) * e = b * ((a * d) * e) from fun a b d e => by ring, e1, e2]
  calc (4 : ℝ) ^ (-(3 / 4 : ℝ)) * (1 / (|c| * y)) ≤ 1 * (1 / (|c| * y)) :=
        mul_le_mul_of_nonneg_right h4 (by positivity)
    _ = 1 / (|c| * y) := one_mul _

/-- **Main term, final form.** -/
theorem norm_integral_VN_le_final {s : ℝ} (hs : 0 ≤ s) (hc : c ≠ 0) (hy : 0 < y) (hn : 0 < n) :
    ‖∫ t, VN s c n u y t‖ ≤ 16 * K34 * s * n ^ s * (c ^ 2 * y ^ 2) ^ (-s) / (|c| * y) *
      (2 * y ^ 2 / (u ^ 2 + y ^ 2)) ^ (3 / 4 : ℝ) := by
  have hP : 0 ≤ 4 * s * n ^ s * (c ^ 2 * y ^ 2) ^ (-s) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hs) (Real.rpow_nonneg hn.le s))
      (Real.rpow_nonneg (by positivity) _)
  have hK14 : 0 ≤ (c ^ 2 * y ^ 2) ^ (-(1 / 4 : ℝ)) := Real.rpow_nonneg (by positivity) _
  have hM : 0 ≤ (2 * y ^ 2 / (u ^ 2 + y ^ 2)) ^ (3 / 4 : ℝ) := Real.rpow_nonneg (by positivity) _
  have hQ : 0 ≤ 4 * s * n ^ s * (c ^ 2 * y ^ 2) ^ (-s) *
      (2 * y ^ 2 / (u ^ 2 + y ^ 2)) ^ (3 / 4 : ℝ) * (4 * K34) :=
    mul_nonneg (mul_nonneg hP hM) (mul_nonneg (by norm_num) K34_nonneg)
  calc ‖∫ t, VN s c n u y t‖
      ≤ 4 * s * n ^ s * (c ^ 2 * y ^ 2) ^ (-s) * (c ^ 2 * y ^ 2) ^ (-(1 / 4 : ℝ)) *
          ∫ t, Rp c n u y t ^ (-(3 / 4 : ℝ)) := norm_integral_VN_le_main hs hc hy hn
    _ ≤ 4 * s * n ^ s * (c ^ 2 * y ^ 2) ^ (-s) * (c ^ 2 * y ^ 2) ^ (-(1 / 4 : ℝ)) *
          ((2 * y ^ 2 / (u ^ 2 + y ^ 2)) ^ (3 / 4 : ℝ) *
            (2 * ((4 * (c ^ 2 * y ^ 2)) ^ (-(3 / 4 : ℝ)) * (2 * |c| * y * K34)))) :=
        mul_le_mul_of_nonneg_left (integral_Rp34_le hc hy hn.le) (mul_nonneg hP hK14)
    _ = 4 * s * n ^ s * (c ^ 2 * y ^ 2) ^ (-s) * (2 * y ^ 2 / (u ^ 2 + y ^ 2)) ^ (3 / 4 : ℝ) *
          (4 * K34) * ((c ^ 2 * y ^ 2) ^ (-(1 / 4 : ℝ)) *
            (4 * (c ^ 2 * y ^ 2)) ^ (-(3 / 4 : ℝ)) * (|c| * y)) := by ring
    _ ≤ 4 * s * n ^ s * (c ^ 2 * y ^ 2) ^ (-s) * (2 * y ^ 2 / (u ^ 2 + y ^ 2)) ^ (3 / 4 : ℝ) *
          (4 * K34) * (1 / (|c| * y)) := mul_le_mul_of_nonneg_left (K14_mul_K34_le hc hy) hQ
    _ = _ := by ring

/-! ## The `u`-integral of the weight -/

lemma M34_eq (hy : 0 < y) (u : ℝ) :
    (2 * y ^ 2 / (u ^ 2 + y ^ 2)) ^ (3 / 4 : ℝ) = 2 ^ (3 / 4 : ℝ) * g34 (u / y) := by
  have hy0 : y ≠ 0 := hy.ne'
  have h1 : 2 * y ^ 2 / (u ^ 2 + y ^ 2) = 2 * (1 + (u / y) ^ 2)⁻¹ := by
    first
    | (field_simp; ring)
    | field_simp
    | (rw [div_pow]; field_simp; ring)
  rw [h1, Real.mul_rpow (by norm_num) (by positivity), Real.inv_rpow (by positivity), g34,
    Real.rpow_neg (by positivity)]

lemma integrable_M34 (hy : 0 < y) :
    Integrable fun u : ℝ => (2 * y ^ 2 / (u ^ 2 + y ^ 2)) ^ (3 / 4 : ℝ) :=
  ((integrable_g34.comp_div hy.ne').const_mul (2 ^ (3 / 4 : ℝ))).congr
    (Eventually.of_forall fun u => (M34_eq hy u).symm)

theorem integral_M34 (hy : 0 < y) :
    ∫ u : ℝ, (2 * y ^ 2 / (u ^ 2 + y ^ 2)) ^ (3 / 4 : ℝ) = 2 ^ (3 / 4 : ℝ) * (y * K34) := by
  simp_rw [M34_eq hy]
  rw [integral_const_mul, Measure.integral_comp_div g34 y, abs_of_pos hy, smul_eq_mul]
  rfl

end RamanujanPetersson.EllW2


