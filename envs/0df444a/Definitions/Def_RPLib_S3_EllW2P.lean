-- Prove2me | Definitions.Def_RPLib_S3_EllW2P
-- name    : RPLib_S3_EllW2P
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T13:39:37.677797+00:00
-- url     : https://prove2.me/theorems/b8b5cf7b-19f8-4be4-833b-5ee08921c3ca
-- title:
--   The Eichler-Selberg trace formula in weight two: the real-trace profile of the `R^(-s-1)` zero modes
-- statement:
--   The real-trace profile of the `R^(-s-1)` zero modes.
--
--   For `c ≠ 0`, `y > 0`, `n ≥ 0` and a REAL trace `t`, `Rp c n u y t = RcN c t (t² - 4n) u y`.
--   * `Rp_mul`: `16 c² y² Rp = a(t) b(t)`, `a = (t - w)² + 4c²y²`, `b = (t + w)² + 4c²y²`, `w = √(4c²u² + 4n)`.
--   * `le_Rp`: `c² (u² + y²) ≤ Rp`; `inv_Rp_le`: `Rp⁻¹ ≤ 2y²/(u²+y²) (a⁻¹ + b⁻¹)`.
--   * `hasDerivAt_Rp`, `abs_dRp_le`: `|∂_t Rp| ≤ Rp / (|c| y)`.
--   * `VS s = Rp^(-s-1)`: `hasDerivAt_VS`, `abs_dVS_le` (`≤ (1+s)/(|c|y) VS`), `integrable_VS`,
--     `integral_VS_le` (`∫_t VS ≤ (c²y²)^(-s) 2π y / (|c| (u²+y²))`), `integrable_dVS`, `integral_abs_dVS_le`;
--     complex forms `ΦS`, `ΦS'` for the Abel summation file AS, `summable_ΦS`.
--   * generic: `integral_inv_sq_add` (`∫ ((t-w)² + Y²)⁻¹ = π / Y`), `summable_int_of_deriv`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224

import Mathlib
import Definitions.Def_RPLib_S3_EllW2W
import Definitions.Def_RPLib_S3_EllW2AS

/-!
# S3-ES-Wt2 (O6, file P): the real-trace profile of the `R^(-s-1)` zero modes

For `c ≠ 0`, `y > 0`, `n ≥ 0` and a REAL trace `t`, `Rp c n u y t = RcN c t (t² - 4n) u y`.
* `Rp_mul`: `16 c² y² Rp = a(t) b(t)`, `a = (t - w)² + 4c²y²`, `b = (t + w)² + 4c²y²`, `w = √(4c²u² + 4n)`.
* `le_Rp`: `c² (u² + y²) ≤ Rp`; `inv_Rp_le`: `Rp⁻¹ ≤ 2y²/(u²+y²) (a⁻¹ + b⁻¹)`.
* `hasDerivAt_Rp`, `abs_dRp_le`: `|∂_t Rp| ≤ Rp / (|c| y)`.
* `VS s = Rp^(-s-1)`: `hasDerivAt_VS`, `abs_dVS_le` (`≤ (1+s)/(|c|y) VS`), `integrable_VS`,
  `integral_VS_le` (`∫_t VS ≤ (c²y²)^(-s) 2π y / (|c| (u²+y²))`), `integrable_dVS`, `integral_abs_dVS_le`;
  complex forms `ΦS`, `ΦS'` for the Abel summation file AS, `summable_ΦS`.
* generic: `integral_inv_sq_add` (`∫ ((t-w)² + Y²)⁻¹ = π / Y`), `summable_int_of_deriv`.
-/

open MeasureTheory Set Filter Real

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EllW2

/-! ## Generic facts -/

lemma inv_sq_add_eq (w : ℝ) {Y : ℝ} (hY : 0 < Y) :
    (fun t : ℝ => ((t - w) ^ 2 + Y ^ 2)⁻¹) = fun t => (Y ^ 2)⁻¹ * (1 + ((t - w) / Y) ^ 2)⁻¹ := by
  have hY0 : Y ≠ 0 := hY.ne'
  ext t
  rw [← mul_inv]
  congr 1
  first | (field_simp; ring) | field_simp

lemma integrable_inv_sq_add (w : ℝ) {Y : ℝ} (hY : 0 < Y) :
    Integrable fun t : ℝ => ((t - w) ^ 2 + Y ^ 2)⁻¹ := by
  rw [inv_sq_add_eq w hY]
  exact ((integrable_inv_one_add_sq.comp_div hY.ne').comp_sub_right w).const_mul _

lemma integral_inv_sq_add (w : ℝ) {Y : ℝ} (hY : 0 < Y) :
    ∫ t : ℝ, ((t - w) ^ 2 + Y ^ 2)⁻¹ = π / Y := by
  have h2 : ∫ t : ℝ, (1 + ((t - w) / Y) ^ 2)⁻¹ = ∫ t : ℝ, (1 + (t / Y) ^ 2)⁻¹ :=
    integral_sub_right_eq_self (fun x : ℝ => (1 + (x / Y) ^ 2)⁻¹) w
  have h3 : ∫ t : ℝ, (1 + (t / Y) ^ 2)⁻¹ = |Y| • ∫ t : ℝ, (1 + t ^ 2)⁻¹ :=
    Measure.integral_comp_div (fun x : ℝ => (1 + x ^ 2)⁻¹) Y
  rw [inv_sq_add_eq w hY, integral_const_mul, h2, h3, integral_univ_inv_one_add_sq, abs_of_pos hY,
    smul_eq_mul]
  have hY0 : Y ≠ 0 := hY.ne'
  first | (field_simp; ring) | field_simp

lemma integrable_inv_sq_add_sq {y : ℝ} (hy : 0 < y) : Integrable fun u : ℝ => (u ^ 2 + y ^ 2)⁻¹ := by
  simpa using integrable_inv_sq_add 0 hy

lemma integral_inv_sq_add_sq {y : ℝ} (hy : 0 < y) : ∫ u : ℝ, (u ^ 2 + y ^ 2)⁻¹ = π / y := by
  simpa using integral_inv_sq_add 0 hy

/-- An integrable `C¹` profile with integrable derivative is summable over `ℤ`. -/
lemma summable_int_of_deriv {Φ Φ' : ℝ → ℂ} (hd : ∀ x, HasDerivAt Φ (Φ' x) x) (hΦ' : Integrable Φ')
    (hΦ : Integrable Φ) : Summable fun t : ℤ => Φ t := by
  refine Summable.of_norm_bounded ((hasSum_unit_norm hΦ).summable.add (hasSum_unit_norm hΦ').summable)
    fun t => ?_
  set D := ∫ u in (t : ℝ)..(t : ℝ) + 1, ‖Φ' u‖ with hD
  have hx : ∀ x ∈ Icc (t : ℝ) (t + 1), ‖Φ t‖ ≤ ‖Φ x‖ + D := fun x hx => by
    have h := norm_sub_le_intervalIntegral hd hΦ' hx.1 hx.2
    calc ‖Φ t‖ = ‖Φ x - (Φ x - Φ t)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖Φ x‖ + ‖Φ x - Φ t‖ := norm_sub_le _ _
      _ ≤ ‖Φ x‖ + D := by gcongr
  have hm := intervalIntegral.integral_mono_on (f := fun _ => ‖Φ t‖) (g := fun x => ‖Φ x‖ + D)
    (show (t : ℝ) ≤ t + 1 by linarith) intervalIntegrable_const
    ((hΦ.norm.intervalIntegrable).add intervalIntegrable_const) hx
  rw [intervalIntegral.integral_const, intervalIntegral.integral_add (hΦ.norm.intervalIntegrable)
    intervalIntegrable_const, intervalIntegral.integral_const] at hm
  simpa using hm

/-! ## The profile `Rp` -/

/-- `RcN` at a real trace `t` (`D = t² - 4n`). -/
def Rp (c n u y t : ℝ) : ℝ := RcN c t (t ^ 2 - 4 * n) u y

/-- `w = √(4c²u² + 4n)`. -/
def wR (c n u : ℝ) : ℝ := √(4 * c ^ 2 * u ^ 2 + 4 * n)

/-- The quadratic factors `(t - w)² + 4c²y²`. -/
def aR (c y w t : ℝ) : ℝ := (t - w) ^ 2 + 4 * c ^ 2 * y ^ 2

variable {c n u y : ℝ}

lemma wR_sq (hn : 0 ≤ n) : wR c n u ^ 2 = 4 * c ^ 2 * u ^ 2 + 4 * n :=
  Real.sq_sqrt (by positivity)

lemma Rp_poly (hc : c ≠ 0) (hy : y ≠ 0) (t : ℝ) :
    16 * c ^ 2 * y ^ 2 * Rp c n u y t =
      (4 * c ^ 2 * (u ^ 2 + y ^ 2) - t ^ 2 + 4 * n) ^ 2 + 16 * c ^ 2 * y ^ 2 * t ^ 2 := by
  unfold Rp RcN
  field_simp
  ring

lemma Rp_mul (hc : c ≠ 0) (hy : y ≠ 0) (hn : 0 ≤ n) (t : ℝ) :
    16 * c ^ 2 * y ^ 2 * Rp c n u y t = aR c y (wR c n u) t * aR c y (-wR c n u) t := by
  rw [Rp_poly hc hy t]
  unfold aR
  linear_combination (-(4 * c ^ 2 * u ^ 2 + 4 * n + wR c n u ^ 2 - 2 * t ^ 2 + 8 * c ^ 2 * y ^ 2)) *
    wR_sq (c := c) (u := u) hn

lemma aR_pos (hc : c ≠ 0) (hy : y ≠ 0) (w t : ℝ) : 0 < aR c y w t := by
  unfold aR; positivity

lemma aR_eq (c y w t : ℝ) : aR c y w t = (t - w) ^ 2 + (2 * |c| * y) ^ 2 := by
  unfold aR; rw [mul_pow, mul_pow, sq_abs]; ring

lemma integrable_inv_aR (hc : c ≠ 0) (hy : 0 < y) (w : ℝ) :
    Integrable fun t => (aR c y w t)⁻¹ := by
  have e : (fun t => (aR c y w t)⁻¹) = fun t => ((t - w) ^ 2 + (2 * |c| * y) ^ 2)⁻¹ := by
    ext t; rw [aR_eq]
  rw [e]
  exact integrable_inv_sq_add w (by positivity)

lemma integral_inv_aR (hc : c ≠ 0) (hy : 0 < y) (w : ℝ) :
    ∫ t, (aR c y w t)⁻¹ = π / (2 * |c| * y) := by
  have e : (fun t => (aR c y w t)⁻¹) = fun t => ((t - w) ^ 2 + (2 * |c| * y) ^ 2)⁻¹ := by
    ext t; rw [aR_eq]
  rw [e]
  exact integral_inv_sq_add w (by positivity)

lemma le_Rp (hc : c ≠ 0) (hy : y ≠ 0) (hn : 0 ≤ n) (t : ℝ) :
    c ^ 2 * (u ^ 2 + y ^ 2) ≤ Rp c n u y t := by
  have hR := Rp_mul (u := u) hc hy hn t
  have hw := wR_sq (c := c) (u := u) hn
  set w := wR c n u
  set a := aR c y w t with ha
  set b := aR c y (-w) t with hb
  have hY : 0 < 4 * c ^ 2 * y ^ 2 := by positivity
  have haY : 4 * c ^ 2 * y ^ 2 ≤ a := by rw [ha]; unfold aR; nlinarith [sq_nonneg (t - w)]
  have hbY : 4 * c ^ 2 * y ^ 2 ≤ b := by rw [hb]; unfold aR; nlinarith [sq_nonneg (t - -w)]
  have hab : 8 * c ^ 2 * (u ^ 2 + y ^ 2) ≤ a + b := by
    rw [ha, hb]; unfold aR; nlinarith [sq_nonneg t, hw]
  have key : 16 * c ^ 2 * y ^ 2 * (c ^ 2 * (u ^ 2 + y ^ 2)) ≤ 16 * c ^ 2 * y ^ 2 * Rp c n u y t := by
    rw [hR]
    nlinarith [mul_nonneg (sub_nonneg.2 haY) (sub_nonneg.2 hbY), mul_le_mul_of_nonneg_left hab hY.le,
      mul_nonneg hY.le (by linarith : (0 : ℝ) ≤ a + b - 2 * (4 * c ^ 2 * y ^ 2))]
  exact le_of_mul_le_mul_left key (by positivity)

lemma Rp_pos (hc : c ≠ 0) (hy : y ≠ 0) (hn : 0 ≤ n) (t : ℝ) : 0 < Rp c n u y t :=
  lt_of_lt_of_le (by positivity) (le_Rp hc hy hn t)

lemma inv_Rp_le (hc : c ≠ 0) (hy : y ≠ 0) (hn : 0 ≤ n) (t : ℝ) :
    (Rp c n u y t)⁻¹ ≤
      2 * y ^ 2 / (u ^ 2 + y ^ 2) * ((aR c y (wR c n u) t)⁻¹ + (aR c y (-wR c n u) t)⁻¹) := by
  have hR := Rp_mul (u := u) hc hy hn t
  have hw := wR_sq (c := c) (u := u) hn
  have hRp := Rp_pos (u := u) hc hy hn t
  have ha := aR_pos hc hy (wR c n u) t
  have hb := aR_pos hc hy (-wR c n u) t
  have hab : 8 * c ^ 2 * (u ^ 2 + y ^ 2) ≤ aR c y (wR c n u) t + aR c y (-wR c n u) t := by
    unfold aR; nlinarith [sq_nonneg t, hw]
  set a := aR c y (wR c n u) t
  set b := aR c y (-wR c n u) t
  have huy : 0 < u ^ 2 + y ^ 2 := by positivity
  have hu0 : u ^ 2 + y ^ 2 ≠ 0 := huy.ne'
  have ha0 : a ≠ 0 := ha.ne'
  have hb0 : b ≠ 0 := hb.ne'
  have hR0 : Rp c n u y t ≠ 0 := hRp.ne'
  calc (Rp c n u y t)⁻¹ = 16 * c ^ 2 * y ^ 2 / (a * b) := by
        rw [← hR]; first | (field_simp; ring) | field_simp
    _ = 2 * y ^ 2 / (u ^ 2 + y ^ 2) * (8 * c ^ 2 * (u ^ 2 + y ^ 2) / (a * b)) := by
        first | (field_simp; ring) | field_simp
    _ ≤ 2 * y ^ 2 / (u ^ 2 + y ^ 2) * ((a + b) / (a * b)) := by gcongr
    _ = _ := by rw [inv_add_inv ha0 hb0]

/-! ## Derivative in the trace -/

lemma hasDerivAt_aR (c y w t : ℝ) : HasDerivAt (aR c y w) (2 * (t - w)) t := by
  have h : HasDerivAt (fun x : ℝ => (x - w) ^ 2 + 4 * c ^ 2 * y ^ 2) (2 * (t - w)) t := by
    have := ((hasDerivAt_id' t).sub_const w).pow 2
    simpa using this.add_const (4 * c ^ 2 * y ^ 2)
  exact h

lemma Rp_eq (hc : c ≠ 0) (hy : y ≠ 0) (hn : 0 ≤ n) :
    Rp c n u y = fun t => aR c y (wR c n u) t * aR c y (-wR c n u) t / (16 * c ^ 2 * y ^ 2) := by
  ext t
  rw [← Rp_mul hc hy hn t]
  first | (field_simp; ring) | field_simp

/-- `∂_t Rp`. -/
def dRp (c n u y t : ℝ) : ℝ :=
  (2 * (t - wR c n u) * aR c y (-wR c n u) t + aR c y (wR c n u) t * (2 * (t - -wR c n u))) /
    (16 * c ^ 2 * y ^ 2)

lemma hasDerivAt_Rp (hc : c ≠ 0) (hy : y ≠ 0) (hn : 0 ≤ n) (t : ℝ) :
    HasDerivAt (Rp c n u y) (dRp c n u y t) t := by
  rw [Rp_eq hc hy hn]
  exact ((hasDerivAt_aR c y _ t).mul (hasDerivAt_aR c y _ t)).div_const _

lemma continuous_Rp (hc : c ≠ 0) (hy : y ≠ 0) (hn : 0 ≤ n) : Continuous (Rp c n u y) :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_Rp hc hy hn t).continuousAt

lemma abs_dRp_le (hc : c ≠ 0) (hy : 0 < y) (hn : 0 ≤ n) (t : ℝ) :
    |dRp c n u y t| ≤ Rp c n u y t / (|c| * y) := by
  unfold dRp
  have hR := Rp_mul (u := u) hc hy.ne' hn t
  set w := wR c n u
  have ha := aR_pos hc hy.ne' w t
  have hb := aR_pos hc hy.ne' (-w) t
  have hcy : 0 < |c| * y := mul_pos (abs_pos.2 hc) hy
  have k1 : 4 * (|c| * y) * |t - w| ≤ aR c y w t := by
    unfold aR
    nlinarith [sq_nonneg (|t - w| - 2 * (|c| * y)), sq_abs (t - w), sq_abs c]
  have k2 : 4 * (|c| * y) * |t - -w| ≤ aR c y (-w) t := by
    unfold aR
    nlinarith [sq_nonneg (|t - -w| - 2 * (|c| * y)), sq_abs (t - -w), sq_abs c]
  have hK : 0 < 16 * c ^ 2 * y ^ 2 := by positivity
  rw [le_div_iff₀ hcy, abs_div, abs_of_pos hK, div_mul_eq_mul_div, div_le_iff₀ hK]
  have hnum : |2 * (t - w) * aR c y (-w) t + aR c y w t * (2 * (t - -w))| ≤
      2 * |t - w| * aR c y (-w) t + aR c y w t * (2 * |t - -w|) := by
    refine (abs_add_le _ _).trans (le_of_eq ?_)
    simp only [abs_mul, abs_of_pos ha, abs_of_pos hb, abs_two]
  have e : Rp c n u y t * (16 * c ^ 2 * y ^ 2) = aR c y w t * aR c y (-w) t := by
    rw [mul_comm]; exact hR
  rw [e]
  nlinarith [mul_le_mul_of_nonneg_right k1 hb.le, mul_le_mul_of_nonneg_left k2 ha.le,
    mul_le_mul_of_nonneg_right hnum hcy.le]

/-! ## The `R^(-s-1)` profile -/

/-- `VS s = Rp^(-s-1)`. -/
def VS (s c n u y t : ℝ) : ℝ := Rp c n u y t ^ (-s - 1)

/-- `∂_t VS`. -/
def dVS (s c n u y t : ℝ) : ℝ := dRp c n u y t * (-s - 1) * Rp c n u y t ^ (-s - 1 - 1)

lemma VS_nonneg (s : ℝ) (hc : c ≠ 0) (hy : y ≠ 0) (hn : 0 ≤ n) (t : ℝ) : 0 ≤ VS s c n u y t :=
  Real.rpow_nonneg (Rp_pos hc hy hn t).le _

lemma hasDerivAt_VS (s : ℝ) (hc : c ≠ 0) (hy : y ≠ 0) (hn : 0 ≤ n) (t : ℝ) :
    HasDerivAt (VS s c n u y) (dVS s c n u y t) t :=
  (hasDerivAt_Rp hc hy hn t).rpow_const (Or.inl (Rp_pos hc hy hn t).ne')

lemma continuous_VS (s : ℝ) (hc : c ≠ 0) (hy : y ≠ 0) (hn : 0 ≤ n) : Continuous (VS s c n u y) :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_VS s hc hy hn t).continuousAt

lemma continuous_dVS (s : ℝ) (hc : c ≠ 0) (hy : y ≠ 0) (hn : 0 ≤ n) : Continuous (dVS s c n u y) := by
  have h1 : Continuous (dRp c n u y) := by unfold dRp aR; fun_prop
  have h2 : Continuous fun t => Rp c n u y t ^ (-s - 1 - 1) :=
    (continuous_Rp hc hy hn).rpow_const fun t => Or.inl (Rp_pos hc hy hn t).ne'
  exact (h1.mul continuous_const).mul h2

lemma abs_dVS_le {s : ℝ} (hs : 0 ≤ s) (hc : c ≠ 0) (hy : 0 < y) (hn : 0 ≤ n) (t : ℝ) :
    |dVS s c n u y t| ≤ (1 + s) / (|c| * y) * VS s c n u y t := by
  have hR := Rp_pos (u := u) hc hy.ne' hn t
  have hd := abs_dRp_le (u := u) hc hy hn t
  have hcy : 0 < |c| * y := mul_pos (abs_pos.2 hc) hy
  have hc0 : |c| ≠ 0 := abs_ne_zero.2 hc
  have hy0 : y ≠ 0 := hy.ne'
  have hR0 : Rp c n u y t ≠ 0 := hR.ne'
  unfold dVS VS
  rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg hR.le _), abs_of_nonpos (by linarith : -s - 1 ≤ 0),
    Real.rpow_sub_one hR0, neg_sub, sub_neg_eq_add]
  have hp : 0 ≤ Rp c n u y t ^ (-s - 1) / Rp c n u y t := div_nonneg (Real.rpow_nonneg hR.le _) hR.le
  calc |dRp c n u y t| * (1 + s) * (Rp c n u y t ^ (-s - 1) / Rp c n u y t)
      ≤ Rp c n u y t / (|c| * y) * (1 + s) * (Rp c n u y t ^ (-s - 1) / Rp c n u y t) := by
        gcongr
    _ = (1 + s) / (|c| * y) * Rp c n u y t ^ (-s - 1) := by
        first | (field_simp; ring) | field_simp

lemma VS_le {s : ℝ} (hs : 0 ≤ s) (hc : c ≠ 0) (hy : y ≠ 0) (hn : 0 ≤ n) (t : ℝ) :
    VS s c n u y t ≤ (c ^ 2 * y ^ 2) ^ (-s) * (2 * y ^ 2 / (u ^ 2 + y ^ 2) *
      ((aR c y (wR c n u) t)⁻¹ + (aR c y (-wR c n u) t)⁻¹)) := by
  have hR := Rp_pos (u := u) hc hy hn t
  have h1 : c ^ 2 * y ^ 2 ≤ Rp c n u y t :=
    le_trans (by nlinarith [mul_nonneg (sq_nonneg c) (sq_nonneg u)]) (le_Rp hc hy hn t)
  unfold VS
  rw [Real.rpow_sub_one hR.ne', div_eq_mul_inv]
  exact mul_le_mul (Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by linarith)) (inv_Rp_le hc hy hn t)
    (inv_nonneg.2 hR.le) (Real.rpow_nonneg (by positivity) _)

/-- Pointwise bound (used for finitely many exceptional traces). -/
lemma VS_le_pt {s : ℝ} (hs : 0 ≤ s) (hc : c ≠ 0) (hy : y ≠ 0) (hn : 0 ≤ n) (t : ℝ) :
    VS s c n u y t ≤ (c ^ 2 * (u ^ 2 + y ^ 2)) ^ (-s - 1) :=
  Real.rpow_le_rpow_of_nonpos (by positivity) (le_Rp hc hy hn t) (by linarith)

lemma integrable_VSbnd (s : ℝ) (hc : c ≠ 0) (hy : 0 < y) (n : ℝ) :
    Integrable fun t => (c ^ 2 * y ^ 2) ^ (-s) * (2 * y ^ 2 / (u ^ 2 + y ^ 2) *
      ((aR c y (wR c n u) t)⁻¹ + (aR c y (-wR c n u) t)⁻¹)) :=
  (((integrable_inv_aR hc hy _).add (integrable_inv_aR hc hy _)).const_mul _).const_mul _

lemma integrable_VS {s : ℝ} (hs : 0 ≤ s) (hc : c ≠ 0) (hy : 0 < y) (hn : 0 ≤ n) :
    Integrable (VS s c n u y) := by
  refine (integrable_VSbnd (u := u) s hc hy n).mono' (continuous_VS s hc hy.ne' hn).aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  rw [Real.norm_of_nonneg (VS_nonneg s hc hy.ne' hn t)]
  exact VS_le hs hc hy.ne' hn t

lemma integral_VS_le {s : ℝ} (hs : 0 ≤ s) (hc : c ≠ 0) (hy : 0 < y) (hn : 0 ≤ n) :
    ∫ t, VS s c n u y t ≤ (c ^ 2 * y ^ 2) ^ (-s) * (2 * π * y / (|c| * (u ^ 2 + y ^ 2))) := by
  have hc0 : |c| ≠ 0 := abs_ne_zero.2 hc
  have hy0 : y ≠ 0 := hy.ne'
  have hu0 : u ^ 2 + y ^ 2 ≠ 0 := by positivity
  calc ∫ t, VS s c n u y t
      ≤ ∫ t, (c ^ 2 * y ^ 2) ^ (-s) * (2 * y ^ 2 / (u ^ 2 + y ^ 2) *
          ((aR c y (wR c n u) t)⁻¹ + (aR c y (-wR c n u) t)⁻¹)) :=
        integral_mono_of_nonneg (Eventually.of_forall fun t => VS_nonneg s hc hy.ne' hn t)
          (integrable_VSbnd (u := u) s hc hy n) (Eventually.of_forall fun t => VS_le hs hc hy.ne' hn t)
    _ = (c ^ 2 * y ^ 2) ^ (-s) * (2 * π * y / (|c| * (u ^ 2 + y ^ 2))) := by
        rw [integral_const_mul, integral_const_mul,
          integral_add (integrable_inv_aR hc hy _) (integrable_inv_aR hc hy _),
          integral_inv_aR hc hy, integral_inv_aR hc hy]
        first | (field_simp; ring) | field_simp

lemma integrable_dVS {s : ℝ} (hs : 0 ≤ s) (hc : c ≠ 0) (hy : 0 < y) (hn : 0 ≤ n) :
    Integrable (dVS s c n u y) :=
  ((integrable_VS hs hc hy hn).const_mul ((1 + s) / (|c| * y))).mono'
    (continuous_dVS s hc hy.ne' hn).aestronglyMeasurable
    (Eventually.of_forall fun t => by rw [Real.norm_eq_abs]; exact abs_dVS_le hs hc hy hn t)

lemma integral_abs_dVS_le {s : ℝ} (hs : 0 ≤ s) (hc : c ≠ 0) (hy : 0 < y) (hn : 0 ≤ n) :
    ∫ t, |dVS s c n u y t| ≤ (1 + s) / (|c| * y) * ∫ t, VS s c n u y t := by
  rw [← integral_const_mul]
  exact integral_mono_of_nonneg (Eventually.of_forall fun t => abs_nonneg _)
    ((integrable_VS hs hc hy hn).const_mul _) (Eventually.of_forall fun t => abs_dVS_le hs hc hy hn t)

/-! ## Complex forms for the Abel summation (file AS) -/

/-- `t ↦ (VS t : ℂ)`. -/
def ΦS (s c n u y : ℝ) (t : ℝ) : ℂ := (VS s c n u y t : ℂ)

/-- `t ↦ (dVS t : ℂ)`. -/
def ΦS' (s c n u y : ℝ) (t : ℝ) : ℂ := (dVS s c n u y t : ℂ)

lemma hasDerivAt_ΦS (s : ℝ) (hc : c ≠ 0) (hy : y ≠ 0) (hn : 0 ≤ n) (t : ℝ) :
    HasDerivAt (ΦS s c n u y) (ΦS' s c n u y t) t :=
  (hasDerivAt_VS s hc hy hn t).ofReal_comp

lemma integrable_ΦS {s : ℝ} (hs : 0 ≤ s) (hc : c ≠ 0) (hy : 0 < y) (hn : 0 ≤ n) :
    Integrable (ΦS s c n u y) :=
  (integrable_VS hs hc hy hn).ofReal

lemma integrable_ΦS' {s : ℝ} (hs : 0 ≤ s) (hc : c ≠ 0) (hy : 0 < y) (hn : 0 ≤ n) :
    Integrable (ΦS' s c n u y) :=
  (integrable_dVS hs hc hy hn).ofReal

lemma summable_ΦS {s : ℝ} (hs : 0 ≤ s) (hc : c ≠ 0) (hy : 0 < y) (hn : 0 ≤ n) :
    Summable fun t : ℤ => ΦS s c n u y t :=
  summable_int_of_deriv (hasDerivAt_ΦS s hc hy.ne' hn) (integrable_ΦS' hs hc hy hn) (integrable_ΦS hs hc hy hn)

lemma integral_ΦS (s c n u y : ℝ) : ∫ t, ΦS s c n u y t = ((∫ t, VS s c n u y t : ℝ) : ℂ) :=
  integral_ofReal

lemma integral_norm_ΦS' (s c n u y : ℝ) : ∫ t, ‖ΦS' s c n u y t‖ = ∫ t, |dVS s c n u y t| := by
  congr 1; ext t; rw [ΦS', Complex.norm_real, Real.norm_eq_abs]

/-- The `u`-integral of the `t`-bound: `∫_u (c²y²)^(-s) 2πy/(|c|(u²+y²)) du = (c²y²)^(-s) 2π²/|c|`. -/
lemma integrable_ubnd (s : ℝ) (c : ℝ) (hy : 0 < y) :
    Integrable fun u : ℝ => (c ^ 2 * y ^ 2) ^ (-s) * (2 * π * y / (|c| * (u ^ 2 + y ^ 2))) := by
  have e : (fun u : ℝ => (c ^ 2 * y ^ 2) ^ (-s) * (2 * π * y / (|c| * (u ^ 2 + y ^ 2)))) =
      fun u => (c ^ 2 * y ^ 2) ^ (-s) * (2 * π * y / |c|) * (u ^ 2 + y ^ 2)⁻¹ := by
    ext u; rw [← div_div]; ring
  rw [e]
  exact (integrable_inv_sq_add_sq hy).const_mul _

lemma integral_ubnd (s : ℝ) (hc : c ≠ 0) (hy : 0 < y) :
    ∫ u : ℝ, (c ^ 2 * y ^ 2) ^ (-s) * (2 * π * y / (|c| * (u ^ 2 + y ^ 2))) =
      (c ^ 2 * y ^ 2) ^ (-s) * (2 * π ^ 2 / |c|) := by
  have hc0 : |c| ≠ 0 := abs_ne_zero.2 hc
  have hy0 : y ≠ 0 := hy.ne'
  have e : (fun u : ℝ => (c ^ 2 * y ^ 2) ^ (-s) * (2 * π * y / (|c| * (u ^ 2 + y ^ 2)))) =
      fun u => (c ^ 2 * y ^ 2) ^ (-s) * (2 * π * y / |c|) * (u ^ 2 + y ^ 2)⁻¹ := by
    ext u; rw [← div_div]; ring
  rw [e, integral_const_mul, integral_inv_sq_add_sq hy]
  first | (field_simp; ring) | field_simp

end RamanujanPetersson.EllW2


