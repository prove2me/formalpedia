-- Prove2me | Definitions.Def_RPLib_S3_EllW2PN2
-- name    : RPLib_S3_EllW2PN2
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T13:43:23.185193+00:00
-- url     : https://prove2.me/theorems/8b49f005-6583-46a2-8b80-a2f7c70db765
-- title:
--   The Eichler-Selberg trace formula in weight two: the `Q`-profile of the NHS zero modes
-- statement:
--   The `Q`-profile of the NHS zero modes.
--
--   At a real trace `t`, `Q = P + i t y` with `P = c (u² + y²) - (t² - 4n)/(4c)` (`Pq`, `Qp`).
--   * `normSq_Qp`: `|Q|² = y² Rp`; `Qp_ne_zero`.
--   * `hasDerivAt_Qp` (`Q' = -t/(2c) + i y`), `norm_dQp_le`: `|Q'| ≤ 2/(|c|y) |Q|`.
--   * `Qp_factor`: `4c Q = -(t - α)(t - β)`, `α, β = ±√(4c²u²+4n) + 2icy` (same imaginary part).
--   * **`integral_inv_Qp_sq`**: `∫_t Q⁻² = 0` (`n > 0`), via `integral_inv_sq_mul_sq` (file PN1).
--   * `hasDerivAt_invQ`, `norm_dinvQ_le`: `|∂_t Q⁻²| ≤ 4/(|c|y) |Q⁻²|`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224

import Mathlib
import Definitions.Def_RPLib_S3_EllW2P
import Definitions.Def_RPLib_S3_EllW2PN1

/-!
# S3-ES-Wt2 (O6, file PN2): the `Q`-profile of the NHS zero modes

At a real trace `t`, `Q = P + i t y` with `P = c (u² + y²) - (t² - 4n)/(4c)` (`Pq`, `Qp`).
* `normSq_Qp`: `|Q|² = y² Rp`; `Qp_ne_zero`.
* `hasDerivAt_Qp` (`Q' = -t/(2c) + i y`), `norm_dQp_le`: `|Q'| ≤ 2/(|c|y) |Q|`.
* `Qp_factor`: `4c Q = -(t - α)(t - β)`, `α, β = ±√(4c²u²+4n) + 2icy` (same imaginary part).
* **`integral_inv_Qp_sq`**: `∫_t Q⁻² = 0` (`n > 0`), via `integral_inv_sq_mul_sq` (file PN1).
* `hasDerivAt_invQ`, `norm_dinvQ_le`: `|∂_t Q⁻²| ≤ 4/(|c|y) |Q⁻²|`.
-/

open MeasureTheory Set Filter Real

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EllW2

/-- `P` at a real trace `t` (shifted coordinates). -/
def Pq (c n u y t : ℝ) : ℝ := c * (u ^ 2 + y ^ 2) - (t ^ 2 - 4 * n) / (4 * c)

/-- `Q = P + i t y`. -/
def Qp (c n u y t : ℝ) : ℂ := (Pq c n u y t : ℂ) + ((t * y : ℝ) : ℂ) * Complex.I

/-- `∂_t Q`. -/
def dQp (c y t : ℝ) : ℂ := ((-(t / (2 * c)) : ℝ) : ℂ) + (y : ℂ) * Complex.I

/-- The roots of `Q` in `t`. -/
def αq (c n u y : ℝ) : ℂ := ((wR c n u : ℝ) : ℂ) + ((2 * c * y : ℝ) : ℂ) * Complex.I

def βq (c n u y : ℝ) : ℂ := ((-wR c n u : ℝ) : ℂ) + ((2 * c * y : ℝ) : ℂ) * Complex.I

/-- `∂_t Q⁻² = -2 Q' / Q³`. -/
def dinvQ (c n u y t : ℝ) : ℂ := -2 * dQp c y t / Qp c n u y t ^ 3

variable {c n u y : ℝ}

lemma Rp_eq_Pq (t : ℝ) : Rp c n u y t = (Pq c n u y t / y) ^ 2 + t ^ 2 := by
  first
  | rfl
  | (unfold Rp RcN Pq; ring)

lemma normSq_Qp (hy : y ≠ 0) (t : ℝ) : Complex.normSq (Qp c n u y t) = y ^ 2 * Rp c n u y t := by
  rw [Rp_eq_Pq, Qp, Complex.normSq_add_mul_I]
  first
  | (field_simp; ring)
  | field_simp

lemma sq_norm_Qp (hy : y ≠ 0) (t : ℝ) : ‖Qp c n u y t‖ ^ 2 = y ^ 2 * Rp c n u y t := by
  rw [Complex.sq_norm, normSq_Qp hy]

lemma Qp_ne_zero (hc : c ≠ 0) (hy : y ≠ 0) (hn : 0 ≤ n) (t : ℝ) : Qp c n u y t ≠ 0 := by
  intro h
  have h1 := normSq_Qp (c := c) (n := n) (u := u) hy t
  rw [h, map_zero] at h1
  have h2 := Rp_pos (u := u) hc hy hn t
  have h3 : 0 < y ^ 2 * Rp c n u y t := by positivity
  linarith

lemma hasDerivAt_Pq (hc : c ≠ 0) (t : ℝ) : HasDerivAt (Pq c n u y) (-(t / (2 * c))) t := by
  have h := ((((hasDerivAt_id t).pow 2).sub_const (4 * n)).div_const (4 * c)).const_sub
    (c * (u ^ 2 + y ^ 2))
  refine h.congr_deriv ?_
  first
  | (simp only [id]; field_simp; ring)
  | (norm_num; field_simp; ring)
  | (simp; field_simp; ring)
  | (simp; field_simp)

lemma hasDerivAt_Qp (hc : c ≠ 0) (t : ℝ) : HasDerivAt (Qp c n u y) (dQp c y t) t := by
  have h1 := (hasDerivAt_Pq (n := n) (u := u) (y := y) hc t).ofReal_comp
  have h2 := (((hasDerivAt_id t).mul_const y).ofReal_comp).mul_const Complex.I
  refine (h1.add h2).congr_deriv ?_
  unfold dQp
  push_cast
  ring

lemma continuous_Qp (hc : c ≠ 0) : Continuous (Qp c n u y) :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_Qp hc t).continuousAt

lemma sq_norm_dQp (t : ℝ) : ‖dQp c y t‖ ^ 2 = (t / (2 * c)) ^ 2 + y ^ 2 := by
  rw [Complex.sq_norm, dQp, Complex.normSq_add_mul_I]
  ring

lemma norm_dQp_le (hc : c ≠ 0) (hy : 0 < y) (hn : 0 ≤ n) (t : ℝ) :
    ‖dQp c y t‖ ≤ 2 / (|c| * y) * ‖Qp c n u y t‖ := by
  have hcy : 0 < |c| * y := mul_pos (abs_pos.2 hc) hy
  rw [div_mul_eq_mul_div, le_div_iff₀ hcy]
  have hR1 : t ^ 2 ≤ Rp c n u y t := by
    rw [Rp_eq_Pq]; nlinarith [sq_nonneg (Pq c n u y t / y)]
  have hR2 := le_Rp (u := u) hc hy.ne' hn t
  have hy2 : 0 ≤ y ^ 2 := sq_nonneg y
  have h3 : y ^ 2 * (c ^ 2 * y ^ 2) ≤ y ^ 2 * Rp c n u y t := by
    have := mul_le_mul_of_nonneg_left hR2 hy2
    nlinarith [mul_nonneg (mul_nonneg hy2 (sq_nonneg c)) (sq_nonneg u)]
  have h4 := mul_le_mul_of_nonneg_left hR1 hy2
  have key : (‖dQp c y t‖ * (|c| * y)) ^ 2 ≤ (2 * ‖Qp c n u y t‖) ^ 2 := by
    rw [mul_pow, mul_pow, sq_norm_dQp, mul_pow, sq_norm_Qp hy.ne', sq_abs]
    have e : ((t / (2 * c)) ^ 2 + y ^ 2) * (c ^ 2 * y ^ 2) =
        y ^ 2 * t ^ 2 / 4 + y ^ 2 * (c ^ 2 * y ^ 2) := by
      field_simp
      ring
    rw [e]
    nlinarith [h3, h4]
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 key

lemma Qp_factor (hc : c ≠ 0) (hn : 0 ≤ n) (t : ℝ) :
    (4 * c : ℂ) * Qp c n u y t = -(((t : ℂ) - αq c n u y) * ((t : ℂ) - βq c n u y)) := by
  have hw : ((wR c n u : ℝ) : ℂ) ^ 2 = 4 * (c : ℂ) ^ 2 * (u : ℂ) ^ 2 + 4 * (n : ℂ) := by
    exact_mod_cast wR_sq (c := c) (u := u) hn
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc
  have hP : (4 * c : ℂ) * (Pq c n u y t : ℂ) =
      4 * (c : ℂ) ^ 2 * ((u : ℂ) ^ 2 + (y : ℂ) ^ 2) - ((t : ℂ) ^ 2 - 4 * n) := by
    unfold Pq
    push_cast
    first
    | (field_simp; ring)
    | field_simp
  unfold Qp αq βq
  rw [mul_add, hP]
  push_cast
  linear_combination (-1 : ℂ) * hw + (4 * (c : ℂ) ^ 2 * (y : ℂ) ^ 2) * Complex.I_sq

lemma αq_im : (αq c n u y).im = 2 * c * y := by simp [αq]

lemma βq_im : (βq c n u y).im = 2 * c * y := by simp [βq]

lemma wR_pos (hn : 0 < n) : 0 < wR c n u := Real.sqrt_pos.2 (by positivity)

lemma αq_ne_βq (hn : 0 < n) : αq c n u y ≠ βq c n u y := by
  intro h
  have h1 := congrArg Complex.re h
  simp only [αq, βq, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_im, mul_zero, mul_one, sub_zero, add_zero] at h1
  linarith [wR_pos (c := c) (u := u) hn]

lemma inv_Qp_sq (hc : c ≠ 0) (hy : y ≠ 0) (hn : 0 ≤ n) (t : ℝ) :
    (Qp c n u y t ^ 2)⁻¹ =
      (16 * (c : ℂ) ^ 2) * (((t : ℂ) - αq c n u y) ^ 2 * ((t : ℂ) - βq c n u y) ^ 2)⁻¹ := by
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc
  have hc4 : (4 * c : ℂ) ≠ 0 := mul_ne_zero (by norm_num) hc'
  have h0 : 2 * c * y ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero hc) hy
  have hX := sub_ne_zero_of_im (γ := αq c n u y) (by rw [αq_im]; exact h0) t
  have hY := sub_ne_zero_of_im (γ := βq c n u y) (by rw [βq_im]; exact h0) t
  have h : Qp c n u y t = -(((t : ℂ) - αq c n u y) * ((t : ℂ) - βq c n u y)) / (4 * c) := by
    rw [eq_div_iff hc4, mul_comm]
    exact Qp_factor hc hn t
  rw [h]
  first
  | (field_simp; ring)
  | (rw [neg_div, neg_sq, div_pow, inv_div, mul_pow, mul_pow, div_eq_mul_inv]; ring)

lemma norm_inv_Qp_sq (hy : y ≠ 0) (t : ℝ) :
    ‖(Qp c n u y t ^ 2)⁻¹‖ = (y ^ 2)⁻¹ * VS 0 c n u y t := by
  rw [norm_inv, norm_pow, sq_norm_Qp hy, VS, neg_zero, zero_sub, Real.rpow_neg_one, mul_inv]

lemma integrable_inv_Qp_sq (hc : c ≠ 0) (hy : 0 < y) (hn : 0 ≤ n) :
    Integrable fun t => (Qp c n u y t ^ 2)⁻¹ := by
  have hcont : Continuous fun t => (Qp c n u y t ^ 2)⁻¹ :=
    ((continuous_Qp hc).pow 2).inv₀ fun t => pow_ne_zero 2 (Qp_ne_zero hc hy.ne' hn t)
  exact ((integrable_VS (u := u) (s := 0) le_rfl hc hy hn).const_mul (y ^ 2)⁻¹).mono'
    hcont.aestronglyMeasurable (Eventually.of_forall fun t => (norm_inv_Qp_sq hy.ne' t).le)

/-- **`∫_ℝ Q⁻² dt = 0`**: both roots of `Q` lie on one side of the real axis. -/
theorem integral_inv_Qp_sq (hc : c ≠ 0) (hy : 0 < y) (hn : 0 < n) :
    ∫ t, (Qp c n u y t ^ 2)⁻¹ = 0 := by
  have hn' := hn.le
  have him : (αq c n u y).im = (βq c n u y).im := by rw [αq_im, βq_im]
  have h0 : (αq c n u y).im ≠ 0 := by
    rw [αq_im]; exact mul_ne_zero (mul_ne_zero two_ne_zero hc) hy.ne'
  have h16 : (16 * (c : ℂ) ^ 2) ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero 2 (Complex.ofReal_ne_zero.2 hc))
  have hint : Integrable fun t : ℝ =>
      (((t : ℂ) - αq c n u y) ^ 2 * ((t : ℂ) - βq c n u y) ^ 2)⁻¹ := by
    have := (integrable_inv_Qp_sq (u := u) hc hy hn').const_mul (16 * (c : ℂ) ^ 2)⁻¹
    refine this.congr (Eventually.of_forall fun t => ?_)
    show (16 * (c : ℂ) ^ 2)⁻¹ * (Qp c n u y t ^ 2)⁻¹ = _
    rw [inv_Qp_sq hc hy.ne' hn' t, ← mul_assoc, inv_mul_cancel₀ h16, one_mul]
  rw [integral_congr_ae (Eventually.of_forall fun t => inv_Qp_sq (u := u) hc hy.ne' hn' t),
    integral_const_mul, integral_inv_sq_mul_sq (αq_ne_βq hn) him h0 hint, mul_zero]

lemma hasDerivAt_invQ (hc : c ≠ 0) (hy : y ≠ 0) (hn : 0 ≤ n) (t : ℝ) :
    HasDerivAt (fun t => (Qp c n u y t ^ 2)⁻¹) (dinvQ c n u y t) t := by
  have hQ := Qp_ne_zero (u := u) hc hy hn t
  refine (((hasDerivAt_Qp hc t).pow 2).inv (pow_ne_zero 2 hQ)).congr_deriv ?_
  unfold dinvQ
  first
  | (simp only [Pi.pow_apply]; field_simp; ring)
  | (beta_reduce; field_simp; ring)
  | (field_simp; simp only [Pi.pow_apply]; ring)
  | (field_simp; ring)
  | (norm_num; field_simp; ring)
  | (simp only [Nat.reduceSub, pow_one, Nat.cast_ofNat]; field_simp; ring)

lemma norm_dinvQ_le (hc : c ≠ 0) (hy : 0 < y) (hn : 0 ≤ n) (t : ℝ) :
    ‖dinvQ c n u y t‖ ≤ 4 / (|c| * y) * ‖(Qp c n u y t ^ 2)⁻¹‖ := by
  have hQ := norm_pos_iff.2 (Qp_ne_zero (u := u) hc hy.ne' hn t)
  have hd := norm_dQp_le (u := u) hc hy hn t
  have hcy : 0 < |c| * y := mul_pos (abs_pos.2 hc) hy
  have e : ‖dinvQ c n u y t‖ = 2 * ‖dQp c y t‖ / ‖Qp c n u y t‖ ^ 3 := by
    unfold dinvQ
    rw [norm_div, norm_mul, norm_pow]
    congr 2
    simp
  rw [e, norm_inv, norm_pow]
  calc 2 * ‖dQp c y t‖ / ‖Qp c n u y t‖ ^ 3
      ≤ 2 * (2 / (|c| * y) * ‖Qp c n u y t‖) / ‖Qp c n u y t‖ ^ 3 := by gcongr
    _ = 4 / (|c| * y) * (‖Qp c n u y t‖ ^ 2)⁻¹ := by
        field_simp
        ring

end RamanujanPetersson.EllW2


