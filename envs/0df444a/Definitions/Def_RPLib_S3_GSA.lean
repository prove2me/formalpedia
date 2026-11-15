-- Prove2me | Definitions.Def_RPLib_S3_GSA
-- name    : RPLib_S3_GSA
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T12:26:23.810446+00:00
-- url     : https://prove2.me/theorems/75591929-72da-4f3b-8882-ea79ba654abf
-- title:
--   The Eichler-Selberg trace formula in weight two: the one-variable series `G_s` and its Fourier coefficients
-- statement:
--   The one-variable series `G_s` and its Fourier coefficients.
--
--   For `s ∈ [0, 1]`, `y > 0`:
--     `fS s y u = (u + y i)⁻² (u² + y²)^(-s)`, `gS s y ξ = 𝓕 (fS s y) ξ`,
--     `Gs s ζ = Σ_{n ∈ ℤ} fS s (Im ζ) (Re ζ + n) = Σ_n (ζ + n)⁻² |ζ + n|^(-2s)`.
--   With `Bnd y = π (1 + y⁻²)² / y`:
--   * `hasSum_Gs`: `Gs s ζ = Σ_n gS s (Im ζ) n · e(n Re ζ)` (Poisson);
--   * `norm_gS_le`: `‖gS s y ξ‖ ≤ Bnd y / (1 + ξ²)`;  `norm_gS_zero_le`: `‖gS s y 0‖ ≤ 2 s Bnd y`;
--   * `tendsto_gS`, `tendsto_Gs`: continuity at `s = 0+`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224; F. Diamond and J. Shurman, A First Course in Modular Forms, GTM 228, Springer 2005, Chapter 5

import Mathlib
import Definitions.Def_RPLib_S3_HypParEA

/-!
# S3-ES-Wt2, part GS_A: the one-variable series `G_s` and its Fourier coefficients

For `s ∈ [0, 1]`, `y > 0`:
  `fS s y u = (u + y i)⁻² (u² + y²)^(-s)`, `gS s y ξ = 𝓕 (fS s y) ξ`,
  `Gs s ζ = Σ_{n ∈ ℤ} fS s (Im ζ) (Re ζ + n) = Σ_n (ζ + n)⁻² |ζ + n|^(-2s)`.
With `Bnd y = π (1 + y⁻²)² / y`:
* `hasSum_Gs`: `Gs s ζ = Σ_n gS s (Im ζ) n · e(n Re ζ)` (Poisson);
* `norm_gS_le`: `‖gS s y ξ‖ ≤ Bnd y / (1 + ξ²)`;  `norm_gS_zero_le`: `‖gS s y 0‖ ≤ 2 s Bnd y`;
* `tendsto_gS`, `tendsto_Gs`: continuity at `s = 0+`.
-/

open Complex MeasureTheory Filter Topology Asymptotics
open scoped Real FourierTransform

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.GSA

def tq (y u : ℝ) : ℝ := u ^ 2 + y ^ 2
def Ainv (y u : ℝ) : ℂ := ((u : ℂ) + (y : ℂ) * I)⁻¹
def bS (s y u : ℝ) : ℝ := tq y u ^ (-s)
def bS1 (s y u : ℝ) : ℝ := -2 * s * u * bS s y u * (tq y u)⁻¹
def bS2 (s y u : ℝ) : ℝ :=
  -2 * s * (bS s y u * (tq y u)⁻¹ + u * bS1 s y u * (tq y u)⁻¹
    - 2 * u ^ 2 * bS s y u * ((tq y u)⁻¹) ^ 2)
def fS (s y u : ℝ) : ℂ := Ainv y u ^ 2 * (bS s y u : ℂ)
def fS1 (s y u : ℝ) : ℂ := -2 * Ainv y u ^ 3 * (bS s y u : ℂ) + Ainv y u ^ 2 * (bS1 s y u : ℂ)
def fS2 (s y u : ℝ) : ℂ :=
  6 * Ainv y u ^ 4 * (bS s y u : ℂ) - 4 * Ainv y u ^ 3 * (bS1 s y u : ℂ)
    + Ainv y u ^ 2 * (bS2 s y u : ℂ)
/-- Fourier coefficients of `G_s` at height `y`. -/
def gS (s y ξ : ℝ) : ℂ := 𝓕 (fS s y) ξ
/-- `Gs s ζ = Σ_n (ζ + n)⁻² |ζ + n|^(-2s)`. -/
def Gs (s : ℝ) (ζ : ℂ) : ℂ := ∑' n : ℤ, fS s ζ.im (ζ.re + n)
def rho (y : ℝ) : ℝ := 1 + (y ^ 2)⁻¹
def Bnd (y : ℝ) : ℝ := π * rho y ^ 2 / y

/-! ### Elementary facts -/

lemma tq_pos {y : ℝ} (hy : 0 < y) (u : ℝ) : 0 < tq y u := by unfold tq; positivity

lemma normSq_wv (y u : ℝ) : normSq ((u : ℂ) + (y : ℂ) * I) = tq y u := by
  simp only [normSq_apply, add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, add_im, mul_im, tq]
  ring

lemma wv_ne_zero {y : ℝ} (hy : 0 < y) (u : ℝ) : (u : ℂ) + (y : ℂ) * I ≠ 0 := by
  intro h
  have h1 := normSq_wv y u
  rw [h, map_zero] at h1
  have := tq_pos hy u
  linarith

lemma norm_Ainv_sq {y : ℝ} (hy : 0 < y) (u : ℝ) : ‖Ainv y u‖ ^ 2 = (tq y u)⁻¹ := by
  rw [Ainv, norm_inv, inv_pow, Complex.sq_norm, normSq_wv]

lemma abs_mul_norm_Ainv_le {y : ℝ} (hy : 0 < y) (u : ℝ) : |u| * ‖Ainv y u‖ ≤ 1 := by
  have hw : 0 < ‖(u : ℂ) + (y : ℂ) * I‖ := norm_pos_iff.2 (wv_ne_zero hy u)
  have h1 : |u| ≤ ‖(u : ℂ) + (y : ℂ) * I‖ := by
    have := Complex.abs_re_le_norm ((u : ℂ) + (y : ℂ) * I)
    simpa using this
  rw [Ainv, norm_inv, ← div_eq_mul_inv, div_le_one hw]
  exact h1

lemma norm_Ainv_le {y : ℝ} (hy : 0 < y) (u : ℝ) : ‖Ainv y u‖ ≤ y⁻¹ := by
  have h1 : y ≤ ‖(u : ℂ) + (y : ℂ) * I‖ := by
    have := Complex.abs_im_le_norm ((u : ℂ) + (y : ℂ) * I)
    have h2 : |((u : ℂ) + (y : ℂ) * I).im| = y := by simp [abs_of_pos hy]
    linarith
  rw [Ainv, norm_inv]
  exact inv_anti₀ hy h1

lemma tq_inv_le {y : ℝ} (hy : 0 < y) (u : ℝ) : (tq y u)⁻¹ ≤ (y ^ 2)⁻¹ :=
  inv_anti₀ (by positivity) (by unfold tq; nlinarith [sq_nonneg u])

lemma bS_pos (s : ℝ) {y : ℝ} (hy : 0 < y) (u : ℝ) : 0 < bS s y u :=
  Real.rpow_pos_of_pos (tq_pos hy u) _

lemma one_le_rho (y : ℝ) : 1 ≤ rho y := by
  unfold rho; have : 0 ≤ (y ^ 2)⁻¹ := by positivity
  linarith

lemma bS_le_rho {s y : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hy : 0 < y) (u : ℝ) :
    bS s y u ≤ rho y := by
  unfold bS rho
  have hy2 : 0 ≤ (y ^ 2)⁻¹ := by positivity
  rcases le_or_gt 1 (tq y u) with h | h
  · have := Real.rpow_le_one_of_one_le_of_nonpos h (by linarith : -s ≤ 0)
    linarith
  · have ht := tq_pos hy u
    have h1 : tq y u ^ (-s) ≤ tq y u ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge ht h.le (by linarith)
    rw [Real.rpow_neg_one] at h1
    have h2 := tq_inv_le hy u
    linarith

/-! ### The dominating function `(u² + y²)⁻¹` -/

lemma tq_inv_eq {y : ℝ} (hy : 0 < y) (u : ℝ) :
    (tq y u)⁻¹ = (y ^ 2)⁻¹ * (1 + (u / y) ^ 2)⁻¹ := by
  have hy2 : (y : ℝ) ^ 2 ≠ 0 := by positivity
  unfold tq
  rw [← mul_inv]
  congr 1
  first | (field_simp; ring) | field_simp

lemma integrable_tq_inv {y : ℝ} (hy : 0 < y) : Integrable (fun u : ℝ => (tq y u)⁻¹) := by
  simp_rw [tq_inv_eq hy]
  exact (integrable_inv_one_add_sq.comp_div hy.ne').const_mul _

lemma integral_tq_inv {y : ℝ} (hy : 0 < y) : ∫ u : ℝ, (tq y u)⁻¹ = π / y := by
  simp_rw [tq_inv_eq hy]
  have h := Measure.integral_comp_div (fun v : ℝ => (1 + v ^ 2)⁻¹) y
  rw [integral_const_mul, h, integral_univ_inv_one_add_sq, abs_of_pos hy, smul_eq_mul]
  field_simp

lemma integral_const_mul_tq_inv {y : ℝ} (hy : 0 < y) (C : ℝ) :
    ∫ u : ℝ, C * (tq y u)⁻¹ = C * (π / y) := by
  rw [integral_const_mul, integral_tq_inv hy]

/-! ### Derivatives -/

lemma hasDerivAt_Ainv {y : ℝ} (hy : 0 < y) (u : ℝ) :
    HasDerivAt (Ainv y) (-(Ainv y u ^ 2)) u := by
  have h := (((hasDerivAt_id' ((u : ℂ))).add_const ((y : ℂ) * I)).inv
    (wv_ne_zero hy u)).comp_ofReal
  refine h.congr_deriv ?_
  simp only [Ainv]
  rw [inv_pow]
  ring

lemma hasDerivAt_tq_inv {y : ℝ} (hy : 0 < y) (u : ℝ) :
    HasDerivAt (fun u => (tq y u)⁻¹) (-(2 * u) * ((tq y u)⁻¹) ^ 2) u := by
  have h := ((hasDerivAt_pow 2 u).add_const (y ^ 2)).inv (tq_pos hy u).ne'
  refine h.congr_deriv ?_
  simp only [tq]
  rw [inv_pow]
  ring

lemma hasDerivAt_bS (s : ℝ) {y : ℝ} (hy : 0 < y) (u : ℝ) :
    HasDerivAt (fun u => bS s y u) (bS1 s y u) u := by
  have h := ((hasDerivAt_pow 2 u).add_const (y ^ 2)).rpow_const (p := -s)
    (Or.inl (tq_pos hy u).ne')
  refine h.congr_deriv ?_
  have ht : (u ^ 2 + y ^ 2 : ℝ) ≠ 0 := (tq_pos hy u).ne'
  simp only [bS1, bS, tq]
  rw [Real.rpow_sub_one ht]
  simp only [Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl, pow_one]
  ring

lemma hasDerivAt_bS1 (s : ℝ) {y : ℝ} (hy : 0 < y) (u : ℝ) :
    HasDerivAt (fun u => bS1 s y u) (bS2 s y u) u := by
  have h := ((((hasDerivAt_id u).const_mul (-2 * s)).mul (hasDerivAt_bS s hy u)).mul
    (hasDerivAt_tq_inv hy u))
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun v => ?_)
  · simp only [bS2, Pi.mul_apply, id] <;> ring
  · simp only [bS1, Pi.mul_apply, id] <;> ring

lemma hasDerivAt_fS (s : ℝ) {y : ℝ} (hy : 0 < y) (u : ℝ) :
    HasDerivAt (fS s y) (fS1 s y u) u := by
  have h := ((hasDerivAt_Ainv hy u).pow 2).mul (hasDerivAt_bS s hy u).ofReal_comp
  refine h.congr_deriv ?_
  simp only [fS1, Pi.mul_apply, Pi.pow_apply, Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl, pow_one]
  ring

lemma hasDerivAt_fS1 (s : ℝ) {y : ℝ} (hy : 0 < y) (u : ℝ) :
    HasDerivAt (fS1 s y) (fS2 s y u) u := by
  have h := ((((hasDerivAt_Ainv hy u).pow 3).const_mul (-2 : ℂ)).mul
    (hasDerivAt_bS s hy u).ofReal_comp).add
    (((hasDerivAt_Ainv hy u).pow 2).mul (hasDerivAt_bS1 s hy u).ofReal_comp)
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun v => ?_)
  · simp only [fS2, Pi.mul_apply, Pi.pow_apply, Pi.add_apply, Nat.cast_ofNat,
      show (3 : ℕ) - 1 = 2 from rfl, show (2 : ℕ) - 1 = 1 from rfl, pow_one]
    ring
  · simp only [fS1, Pi.mul_apply, Pi.pow_apply, Pi.add_apply] <;> ring

lemma continuous_fS (s : ℝ) {y : ℝ} (hy : 0 < y) : Continuous (fS s y) :=
  continuous_iff_continuousAt.2 fun u => (hasDerivAt_fS s hy u).continuousAt

lemma continuous_fS1 (s : ℝ) {y : ℝ} (hy : 0 < y) : Continuous (fS1 s y) :=
  continuous_iff_continuousAt.2 fun u => (hasDerivAt_fS1 s hy u).continuousAt

/-! ### Pointwise bounds -/

lemma abs_bS1 {s y : ℝ} (hs0 : 0 ≤ s) (hy : 0 < y) (u : ℝ) :
    |bS1 s y u| = 2 * s * |u| * bS s y u * (tq y u)⁻¹ := by
  rw [bS1, abs_mul, abs_mul, abs_mul, abs_mul, abs_neg, abs_two, abs_of_nonneg hs0,
    abs_of_pos (bS_pos s hy u), abs_of_pos (inv_pos.2 (tq_pos hy u))]

lemma norm_fS_le {s y : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hy : 0 < y) (u : ℝ) :
    ‖fS s y u‖ ≤ rho y * (tq y u)⁻¹ := by
  rw [fS, norm_mul, norm_pow, norm_Ainv_sq hy, Complex.norm_real,
    Real.norm_of_nonneg (bS_pos s hy u).le, mul_comm]
  exact mul_le_mul_of_nonneg_right (bS_le_rho hs0 hs1 hy u) (inv_pos.2 (tq_pos hy u)).le

lemma norm_fS1_le {s y : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hy : 0 < y) (u : ℝ) :
    ‖fS1 s y u‖ ≤ 4 * rho y * y⁻¹ * (tq y u)⁻¹ := by
  set a := ‖Ainv y u‖ with ha
  have ha0 : 0 ≤ a := norm_nonneg _
  have haq : a ^ 2 = (tq y u)⁻¹ := norm_Ainv_sq hy u
  have hau : |u| * a ≤ 1 := abs_mul_norm_Ainv_le hy u
  have hay : a ≤ y⁻¹ := norm_Ainv_le hy u
  have hb0 := (bS_pos s hy u).le
  have hbr := bS_le_rho hs0 hs1 hy u
  have hq0 : 0 ≤ (tq y u)⁻¹ := (inv_pos.2 (tq_pos hy u)).le
  have h1 : ‖fS1 s y u‖ ≤ 2 * a ^ 3 * bS s y u + a ^ 2 * |bS1 s y u| := by
    refine (norm_add_le _ _).trans (le_of_eq ?_)
    rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg hb0, Real.norm_eq_abs, norm_neg, Complex.norm_ofNat]
  rw [abs_bS1 hs0 hy u, ← haq] at h1
  rw [← haq]
  have hy0 : 0 ≤ y⁻¹ := (inv_pos.2 hy).le
  -- 2 a³ b + a² (2 s |u| b a²) = a² b (2 a + 2 s (|u| a) a) ≤ a² ρ (4 y⁻¹)
  have h2 : 2 * a ^ 3 * bS s y u + a ^ 2 * (2 * s * |u| * bS s y u * a ^ 2)
      = a ^ 2 * bS s y u * (2 * a + 2 * s * (|u| * a) * a) := by ring
  have h3 : 2 * a + 2 * s * (|u| * a) * a ≤ 4 * y⁻¹ := by
    have : s * (|u| * a) ≤ 1 := by nlinarith [mul_nonneg (abs_nonneg u) ha0]
    nlinarith
  have h4 : a ^ 2 * bS s y u ≤ a ^ 2 * rho y := mul_le_mul_of_nonneg_left hbr (by positivity)
  have h5 : 0 ≤ 2 * a + 2 * s * (|u| * a) * a := by
    have := mul_nonneg (abs_nonneg u) ha0; positivity
  calc ‖fS1 s y u‖ ≤ a ^ 2 * bS s y u * (2 * a + 2 * s * (|u| * a) * a) := h1.trans (le_of_eq h2)
    _ ≤ a ^ 2 * rho y * (4 * y⁻¹) :=
        mul_le_mul h4 h3 h5 (mul_nonneg (sq_nonneg a) (zero_le_one.trans (one_le_rho y)))
    _ = 4 * rho y * y⁻¹ * a ^ 2 := by ring

lemma key_bound {a u b s r : ℝ} (ha0 : 0 ≤ a) (hau : |u| * a ≤ 1)
    (hb0 : 0 ≤ b) (hbr : b ≤ r) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    6 * a ^ 4 * b + 4 * a ^ 3 * (2 * s * |u| * b * a ^ 2)
      + a ^ 2 * (2 * s * (b * a ^ 2 + |u| * (2 * s * |u| * b * a ^ 2) * a ^ 2
        + 2 * u ^ 2 * b * (a ^ 2) ^ 2)) ≤ 24 * r * (a ^ 2) ^ 2 := by
  have hp0 : 0 ≤ |u| * a := mul_nonneg (abs_nonneg u) ha0
  have heq : 6 * a ^ 4 * b + 4 * a ^ 3 * (2 * s * |u| * b * a ^ 2)
      + a ^ 2 * (2 * s * (b * a ^ 2 + |u| * (2 * s * |u| * b * a ^ 2) * a ^ 2
        + 2 * u ^ 2 * b * (a ^ 2) ^ 2)) = b * (a ^ 2) ^ 2 *
          (6 + 8 * s * (|u| * a) + 2 * s * (1 + 2 * s * (|u| * a) ^ 2 + 2 * (|u| * a) ^ 2)) := by
    rw [← sq_abs u]; ring
  rw [heq]
  set p := |u| * a with hp
  have h1 : s * p ≤ 1 := by nlinarith [mul_nonneg (sub_nonneg.2 hs1) hp0]
  have h2 : p ^ 2 ≤ 1 := by nlinarith
  have h3 : s * p ^ 2 ≤ 1 := by nlinarith [mul_nonneg (sub_nonneg.2 hs1) (sq_nonneg p)]
  have h4 : s * (s * p ^ 2) ≤ 1 := by nlinarith [mul_nonneg hs0 (sq_nonneg p)]
  have hX : 6 + 8 * s * p + 2 * s * (1 + 2 * s * p ^ 2 + 2 * p ^ 2) ≤ 24 := by nlinarith
  have ha4 : 0 ≤ (a ^ 2) ^ 2 := by positivity
  calc b * (a ^ 2) ^ 2 * (6 + 8 * s * p + 2 * s * (1 + 2 * s * p ^ 2 + 2 * p ^ 2))
      ≤ b * (a ^ 2) ^ 2 * 24 := mul_le_mul_of_nonneg_left hX (by positivity)
    _ ≤ 24 * r * (a ^ 2) ^ 2 := by nlinarith [mul_le_mul_of_nonneg_right hbr ha4]

lemma norm_fS2_le {s y : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hy : 0 < y) (u : ℝ) :
    ‖fS2 s y u‖ ≤ 24 * rho y * (y ^ 2)⁻¹ * (tq y u)⁻¹ := by
  set a := ‖Ainv y u‖ with ha
  have ha0 : 0 ≤ a := norm_nonneg _
  have haq : a ^ 2 = (tq y u)⁻¹ := norm_Ainv_sq hy u
  have hau : |u| * a ≤ 1 := abs_mul_norm_Ainv_le hy u
  have hb0 := (bS_pos s hy u).le
  have hbr := bS_le_rho hs0 hs1 hy u
  have hq0 : 0 ≤ (tq y u)⁻¹ := (inv_pos.2 (tq_pos hy u)).le
  have h1 : ‖fS2 s y u‖ ≤ 6 * a ^ 4 * bS s y u + 4 * a ^ 3 * |bS1 s y u|
      + a ^ 2 * |bS2 s y u| := by
    refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (le_of_eq ?_)) (le_of_eq ?_))
    · rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_real,
        Complex.norm_real, Real.norm_of_nonneg hb0, Real.norm_eq_abs, Complex.norm_ofNat,
        Complex.norm_ofNat]
    · rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  have hb2 : |bS2 s y u| ≤ 2 * s * (bS s y u * (tq y u)⁻¹ + |u| * |bS1 s y u| * (tq y u)⁻¹
      + 2 * u ^ 2 * bS s y u * ((tq y u)⁻¹) ^ 2) := by
    rw [bS2, abs_mul, abs_mul, abs_neg, abs_two, abs_of_nonneg hs0]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine (abs_sub _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
    · rw [abs_of_nonneg (mul_nonneg hb0 hq0)]
    · rw [abs_mul, abs_mul, abs_of_nonneg hq0]
    · rw [abs_of_nonneg (by positivity)]
  rw [abs_bS1 hs0 hy u] at h1 hb2
  rw [← haq] at h1 hb2
  have h2 : a ^ 2 * |bS2 s y u| ≤ a ^ 2 * (2 * s * (bS s y u * a ^ 2
      + |u| * (2 * s * |u| * bS s y u * a ^ 2) * a ^ 2 + 2 * u ^ 2 * bS s y u * (a ^ 2) ^ 2)) :=
    mul_le_mul_of_nonneg_left hb2 (by positivity)
  have h3 := key_bound ha0 hau hb0 hbr hs0 hs1
  have h4 : 24 * rho y * (a ^ 2) ^ 2 ≤ 24 * rho y * (y ^ 2)⁻¹ * a ^ 2 := by
    rw [haq]
    have := tq_inv_le hy u
    have hr := one_le_rho y
    have : 0 ≤ 24 * rho y * (tq y u)⁻¹ :=
      mul_nonneg (mul_nonneg (by norm_num) (zero_le_one.trans hr)) hq0
    nlinarith
  rw [← haq]
  linarith

/-! ### Integrability -/

lemma integrable_fS {s y : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hy : 0 < y) :
    Integrable (fS s y) :=
  Integrable.mono' ((integrable_tq_inv hy).const_mul (rho y))
    (continuous_fS s hy).aestronglyMeasurable (Eventually.of_forall (norm_fS_le hs0 hs1 hy))

lemma integrable_fS1 {s y : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hy : 0 < y) :
    Integrable (fS1 s y) :=
  Integrable.mono' ((integrable_tq_inv hy).const_mul (4 * rho y * y⁻¹))
    (continuous_fS1 s hy).aestronglyMeasurable (Eventually.of_forall (norm_fS1_le hs0 hs1 hy))

lemma continuous_fS2 (s : ℝ) {y : ℝ} (hy : 0 < y) : Continuous (fS2 s y) := by
  have hA : Continuous (Ainv y) :=
    continuous_iff_continuousAt.2 fun u => (hasDerivAt_Ainv hy u).continuousAt
  have hb : Continuous (fun u => bS s y u) :=
    continuous_iff_continuousAt.2 fun u => (hasDerivAt_bS s hy u).continuousAt
  have hb1 : Continuous (fun u => bS1 s y u) :=
    continuous_iff_continuousAt.2 fun u => (hasDerivAt_bS1 s hy u).continuousAt
  have hq : Continuous (fun u => (tq y u)⁻¹) :=
    continuous_iff_continuousAt.2 fun u => (hasDerivAt_tq_inv hy u).continuousAt
  have hb2 : Continuous (fun u => bS2 s y u) := by
    unfold bS2; fun_prop
  unfold fS2
  fun_prop

lemma integrable_fS2 {s y : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hy : 0 < y) :
    Integrable (fS2 s y) :=
  Integrable.mono' ((integrable_tq_inv hy).const_mul (24 * rho y * (y ^ 2)⁻¹))
    (continuous_fS2 s hy).aestronglyMeasurable (Eventually.of_forall (norm_fS2_le hs0 hs1 hy))

/-! ### Fourier coefficients -/

lemma norm_fourier_le (f : ℝ → ℂ) (ξ : ℝ) : ‖𝓕 f ξ‖ ≤ ∫ u, ‖f u‖ := by
  rw [Real.fourier_real_eq]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  simp_rw [Circle.norm_smul]

lemma fourier_fS2 {s y : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hy : 0 < y) (ξ : ℝ) :
    𝓕 (fS2 s y) ξ = (2 * π * I * ξ) * ((2 * π * I * ξ) * gS s y ξ) := by
  have hd0 : deriv (fS s y) = fS1 s y := funext fun u => (hasDerivAt_fS s hy u).deriv
  have hd1 : deriv (fS1 s y) = fS2 s y := funext fun u => (hasDerivAt_fS1 s hy u).deriv
  have h1 := Real.fourier_deriv (integrable_fS hs0 hs1 hy)
    (fun u => (hasDerivAt_fS s hy u).differentiableAt) (by rw [hd0]; exact integrable_fS1 hs0 hs1 hy)
  have h2 := Real.fourier_deriv (integrable_fS1 hs0 hs1 hy)
    (fun u => (hasDerivAt_fS1 s hy u).differentiableAt) (by rw [hd1]; exact integrable_fS2 hs0 hs1 hy)
  rw [hd0] at h1
  rw [hd1] at h2
  rw [h2]
  simp only [h1, smul_eq_mul, gS]

lemma norm_gS_le_rho {s y : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hy : 0 < y) (ξ : ℝ) :
    ‖gS s y ξ‖ ≤ rho y * (π / y) := by
  refine (norm_fourier_le _ ξ).trans ?_
  rw [← integral_const_mul_tq_inv hy]
  exact integral_mono (integrable_fS hs0 hs1 hy).norm ((integrable_tq_inv hy).const_mul _)
    (norm_fS_le hs0 hs1 hy)

theorem norm_gS_le {s y : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hy : 0 < y) (ξ : ℝ) :
    ‖gS s y ξ‖ ≤ Bnd y / (1 + ξ ^ 2) := by
  have hA := norm_gS_le_rho hs0 hs1 hy ξ
  have hB : ‖𝓕 (fS2 s y) ξ‖ ≤ 24 * rho y * (y ^ 2)⁻¹ * (π / y) := by
    refine (norm_fourier_le _ ξ).trans ?_
    rw [← integral_const_mul_tq_inv hy]
    exact integral_mono (integrable_fS2 hs0 hs1 hy).norm ((integrable_tq_inv hy).const_mul _)
      (norm_fS2_le hs0 hs1 hy)
  have hn : ‖(2 * π * I * ξ : ℂ)‖ = 2 * π * |ξ| := by
    simp [abs_of_pos Real.pi_pos]
  rw [fourier_fS2 hs0 hs1 hy ξ, norm_mul, hn, norm_mul, hn] at hB
  have hpi : 3 < π := Real.pi_gt_three
  have hg0 : 0 ≤ ‖gS s y ξ‖ := norm_nonneg _
  have hr := one_le_rho y
  have hy2 : 0 ≤ (y ^ 2)⁻¹ := by positivity
  have hpy : 0 ≤ π / y := by positivity
  -- ξ² ‖g‖ ≤ ρ y⁻² π / y
  have hC : ξ ^ 2 * ‖gS s y ξ‖ ≤ rho y * (y ^ 2)⁻¹ * (π / y) := by
    have e : 2 * π * |ξ| * (2 * π * |ξ| * ‖gS s y ξ‖) = 4 * π ^ 2 * (ξ ^ 2 * ‖gS s y ξ‖) := by
      rw [← sq_abs ξ]; ring
    rw [e] at hB
    have h36 : 36 ≤ 4 * π ^ 2 := by nlinarith
    have hK : 0 ≤ rho y * (y ^ 2)⁻¹ * (π / y) := by positivity
    have hX : 0 ≤ ξ ^ 2 * ‖gS s y ξ‖ := by positivity
    nlinarith
  rw [le_div_iff₀ (by positivity)]
  have e : Bnd y = rho y * (π / y) + rho y * (y ^ 2)⁻¹ * (π / y) := by unfold Bnd rho; ring
  rw [e]
  nlinarith

/-! ### The zero mode -/

lemma gS_zero_eq (s y : ℝ) : gS s y 0 = ∫ u, fS s y u := by
  simp [gS, Real.fourier_real_eq]

lemma hasDerivAt_F (s : ℝ) {y : ℝ} (hy : 0 < y) (u : ℝ) :
    HasDerivAt (fun u => -Ainv y u * (bS s y u : ℂ))
      (fS s y u - Ainv y u * (bS1 s y u : ℂ)) u := by
  have h := (hasDerivAt_Ainv hy u).neg.mul (hasDerivAt_bS s hy u).ofReal_comp
  refine h.congr_deriv ?_
  simp only [fS, Pi.neg_apply]; ring

lemma norm_Ainv_bS1_le {s y : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hy : 0 < y) (u : ℝ) :
    ‖Ainv y u * (bS1 s y u : ℂ)‖ ≤ 2 * s * rho y * (tq y u)⁻¹ := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_bS1 hs0 hy u]
  have hau := abs_mul_norm_Ainv_le hy u
  have hb0 := (bS_pos s hy u).le
  have hbr := bS_le_rho hs0 hs1 hy u
  have hq0 : 0 ≤ (tq y u)⁻¹ := (inv_pos.2 (tq_pos hy u)).le
  have e : ‖Ainv y u‖ * (2 * s * |u| * bS s y u * (tq y u)⁻¹)
      = (2 * s * (tq y u)⁻¹) * ((|u| * ‖Ainv y u‖) * bS s y u) := by ring
  rw [e]
  have h1 : (|u| * ‖Ainv y u‖) * bS s y u ≤ rho y := by
    have := mul_le_mul hau hbr hb0 zero_le_one
    linarith
  have := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 2 * s * (tq y u)⁻¹)
  linarith

lemma tendsto_norm_wv_atTop (y : ℝ) :
    Tendsto (fun u : ℝ => ‖(u : ℂ) + (y : ℂ) * I‖) atTop atTop := by
  refine tendsto_atTop_mono (fun u => (le_abs_self u).trans ?_) tendsto_id
  have := Complex.abs_re_le_norm ((u : ℂ) + (y : ℂ) * I)
  simpa using this

lemma tendsto_norm_wv_atBot (y : ℝ) :
    Tendsto (fun u : ℝ => ‖(u : ℂ) + (y : ℂ) * I‖) atBot atTop := by
  refine tendsto_atTop_mono (fun u => (neg_le_abs u).trans ?_) tendsto_neg_atBot_atTop
  have := Complex.abs_re_le_norm ((u : ℂ) + (y : ℂ) * I)
  simpa using this

lemma tendsto_F {s y : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hy : 0 < y) {l : Filter ℝ}
    (hl : Tendsto (fun u : ℝ => ‖(u : ℂ) + (y : ℂ) * I‖) l atTop) :
    Tendsto (fun u => -Ainv y u * (bS s y u : ℂ)) l (𝓝 0) := by
  have hA : Tendsto (fun u => ‖Ainv y u‖) l (𝓝 0) := by
    simp only [Ainv, norm_inv]; exact tendsto_inv_atTop_zero.comp hl
  refine squeeze_zero_norm (fun u => ?_) (by simpa using hA.const_mul (rho y))
  rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg (bS_pos s hy u).le, mul_comm]
  exact mul_le_mul_of_nonneg_right (bS_le_rho hs0 hs1 hy u) (norm_nonneg _)

theorem norm_gS_zero_le {s y : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hy : 0 < y) :
    ‖gS s y 0‖ ≤ 2 * s * Bnd y := by
  have hI2 : Integrable (fun u => Ainv y u * (bS1 s y u : ℂ)) := by
    refine Integrable.mono' ((integrable_tq_inv hy).const_mul (2 * s * rho y)) ?_
      (Eventually.of_forall (norm_Ainv_bS1_le hs0 hs1 hy))
    have hA : Continuous (Ainv y) :=
      continuous_iff_continuousAt.2 fun u => (hasDerivAt_Ainv hy u).continuousAt
    have hb1 : Continuous (fun u => bS1 s y u) :=
      continuous_iff_continuousAt.2 fun u => (hasDerivAt_bS1 s hy u).continuousAt
    exact (hA.mul (continuous_ofReal.comp hb1)).aestronglyMeasurable
  have hI : Integrable (fun u => fS s y u - Ainv y u * (bS1 s y u : ℂ)) :=
    (integrable_fS hs0 hs1 hy).sub hI2
  have h0 := integral_of_hasDerivAt_of_tendsto (hasDerivAt_F s hy) hI
    (tendsto_F hs0 hs1 hy (tendsto_norm_wv_atBot y)) (tendsto_F hs0 hs1 hy (tendsto_norm_wv_atTop y))
  rw [sub_self, integral_sub (integrable_fS hs0 hs1 hy) hI2, sub_eq_zero] at h0
  rw [gS_zero_eq, h0]
  refine (norm_integral_le_integral_norm _).trans ?_
  have h1 : ∫ u, ‖Ainv y u * (bS1 s y u : ℂ)‖ ≤ 2 * s * rho y * (π / y) := by
    rw [← integral_const_mul_tq_inv hy]
    exact integral_mono hI2.norm ((integrable_tq_inv hy).const_mul _) (norm_Ainv_bS1_le hs0 hs1 hy)
  refine h1.trans ?_
  have hr := one_le_rho y
  have hpy : 0 ≤ π / y := by positivity
  have e : Bnd y = rho y ^ 2 * (π / y) := by unfold Bnd; ring
  rw [e]
  have : rho y ≤ rho y ^ 2 := by nlinarith
  have := mul_le_mul_of_nonneg_right this hpy
  nlinarith

/-! ### Poisson summation -/

lemma isBigO_inv_one_add_sq :
    (fun ξ : ℝ => (1 + ξ ^ 2)⁻¹) =O[cocompact ℝ] (fun ξ : ℝ => |ξ| ^ (-2 : ℝ)) := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [(isCompact_singleton (x := (0 : ℝ))).compl_mem_cocompact] with ξ hξ
  have hξ0 : ξ ≠ 0 := hξ
  have hp : 0 < ξ ^ 2 := by positivity
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg ξ) _),
    one_mul, Real.rpow_neg (abs_nonneg ξ), Real.rpow_two, sq_abs]
  exact inv_anti₀ hp (by linarith)

lemma summable_inv_one_add_sq : Summable (fun n : ℤ => (1 + (n : ℝ) ^ 2)⁻¹) :=
  summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
    (isBigO_inv_one_add_sq.comp_tendsto Int.tendsto_coe_cofinite)

lemma isBigO_fS {s y : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hy : 0 < y) :
    (fS s y) =O[cocompact ℝ] (fun ξ : ℝ => |ξ| ^ (-2 : ℝ)) := by
  refine (isBigO_of_le _ fun u => ?_).trans
    (isBigO_inv_one_add_sq.const_mul_left (rho y * (min 1 (y ^ 2))⁻¹))
  have hm : 0 < min 1 (y ^ 2) := lt_min one_pos (by positivity)
  have h1 := norm_fS_le hs0 hs1 hy u
  have h2 := RamanujanPetersson.HypEA.inv_sq_le hy.ne' u
  have hr := one_le_rho y
  rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (zero_le_one.trans hr) (inv_nonneg.2 hm.le))
    (by positivity))]
  calc ‖fS s y u‖ ≤ rho y * (tq y u)⁻¹ := h1
    _ ≤ rho y * ((min 1 (y ^ 2))⁻¹ * (1 + u ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := by ring

lemma isBigO_gS {s y : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hy : 0 < y) :
    (𝓕 (fS s y)) =O[cocompact ℝ] (fun ξ : ℝ => |ξ| ^ (-2 : ℝ)) := by
  refine (isBigO_of_le _ fun ξ => ?_).trans (isBigO_inv_one_add_sq.const_mul_left (Bnd y))
  have hB : 0 ≤ Bnd y := by unfold Bnd; have := one_le_rho y; positivity
  rw [Real.norm_of_nonneg (by positivity), ← div_eq_mul_inv]
  exact norm_gS_le hs0 hs1 hy ξ

lemma summable_norm_gS {s y : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hy : 0 < y) :
    Summable (fun n : ℤ => ‖gS s y n‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun n => (norm_gS_le hs0 hs1 hy n).trans (le_of_eq (div_eq_mul_inv _ _)))
    (summable_inv_one_add_sq.mul_left (Bnd y))

lemma norm_fourier_coe (n : ℤ) (x : ℝ) : ‖fourier n (x : UnitAddCircle)‖ = 1 :=
  Circle.norm_coe _

/-- **Fourier expansion of `G_s`** (Poisson summation). -/
theorem hasSum_Gs {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {ζ : ℂ} (hζ : 0 < ζ.im) :
    HasSum (fun n : ℤ => gS s ζ.im n * fourier n (ζ.re : UnitAddCircle)) (Gs s ζ) := by
  have hsum : Summable (fun n : ℤ => gS s ζ.im n * fourier n (ζ.re : UnitAddCircle)) :=
    Summable.of_norm_bounded (summable_norm_gS hs0 hs1 hζ)
      (fun n => by rw [norm_mul, norm_fourier_coe, mul_one])
  have hP := Real.tsum_eq_tsum_fourier_of_rpow_decay (continuous_fS s hζ) one_lt_two
    (isBigO_fS hs0 hs1 hζ) (isBigO_gS hs0 hs1 hζ) ζ.re
  rw [Gs, hP]
  exact hsum.hasSum

lemma fS_shift (s : ℝ) (ζ : ℂ) (n : ℤ) :
    fS s ζ.im (ζ.re + n) = ((ζ + n) ^ 2)⁻¹ * ((normSq (ζ + n) ^ (-s) : ℝ) : ℂ) := by
  have h1 : ((ζ.re + n : ℝ) : ℂ) + (ζ.im : ℂ) * I = ζ + n := by
    apply Complex.ext <;> simp
  have h2 : tq ζ.im (ζ.re + n) = normSq (ζ + n) := by rw [← normSq_wv, h1]
  rw [fS, Ainv, bS, h2, h1, inv_pow]

theorem norm_Gs_le {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {ζ : ℂ} (hζ : 0 < ζ.im) :
    ‖Gs s ζ‖ ≤ Bnd ζ.im * ∑' n : ℤ, (1 + (n : ℝ) ^ 2)⁻¹ := by
  rw [← (hasSum_Gs hs0 hs1 hζ).tsum_eq, ← tsum_mul_left]
  refine tsum_of_norm_bounded ((summable_inv_one_add_sq.mul_left (Bnd ζ.im)).hasSum) fun n => ?_
  rw [norm_mul, norm_fourier_coe, mul_one, ← div_eq_mul_inv]
  exact norm_gS_le hs0 hs1 hζ n

/-! ### Continuity at `s = 0+` -/

lemma tendsto_fS {y : ℝ} (hy : 0 < y) (u : ℝ) :
    Tendsto (fun s => fS s y u) (𝓝 0) (𝓝 (fS 0 y u)) := by
  have hb : Tendsto (fun s => bS s y u) (𝓝 0) (𝓝 (bS 0 y u)) := by
    unfold bS
    exact ((Real.continuousAt_const_rpow (tq_pos hy u).ne').comp
      continuous_neg.continuousAt).tendsto
  exact (hb.ofReal).const_mul _

theorem tendsto_gS {y : ℝ} (hy : 0 < y) (ξ : ℝ) :
    Tendsto (fun s => gS s y ξ) (𝓝[>] 0) (𝓝 (gS 0 y ξ)) := by
  simp only [gS, Real.fourier_real_eq]
  refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (fun u => rho y * (tq y u)⁻¹) (Eventually.of_forall fun s => ?_) ?_
    ((integrable_tq_inv hy).const_mul _) (Eventually.of_forall fun u => ?_)
  · exact ((Real.continuous_fourierChar.comp (by fun_prop : Continuous fun u : ℝ => -(u * ξ))).smul
      (continuous_fS s hy)).aestronglyMeasurable
  · filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with s hs
    exact Eventually.of_forall fun u => by
      rw [Circle.norm_smul]; exact norm_fS_le hs.1.le hs.2.le hy u
  · exact ((tendsto_fS hy u).mono_left nhdsWithin_le_nhds).const_smul _

theorem tendsto_Gs {ζ : ℂ} (hζ : 0 < ζ.im) :
    Tendsto (fun s => Gs s ζ) (𝓝[>] 0) (𝓝 (Gs 0 ζ)) := by
  have h0 := (hasSum_Gs le_rfl zero_le_one hζ).tsum_eq
  rw [← h0]
  have hev : (fun s => ∑' n : ℤ, gS s ζ.im n * fourier n (ζ.re : UnitAddCircle))
      =ᶠ[𝓝[>] 0] fun s => Gs s ζ := by
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with s hs
    exact (hasSum_Gs hs.1.le hs.2.le hζ).tsum_eq
  refine Tendsto.congr' hev ?_
  refine tendsto_tsum_of_dominated_convergence
    (summable_inv_one_add_sq.mul_left (Bnd ζ.im))
    (fun n => (tendsto_gS hζ n).mul_const _) ?_
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with s hs n
  rw [norm_mul, norm_fourier_coe, mul_one, ← div_eq_mul_inv]
  exact norm_gS_le hs.1.le hs.2.le hζ n

end RamanujanPetersson.GSA


