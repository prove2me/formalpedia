-- Prove2me | Definitions.Def_RPLib_S3_KernelSDA
-- name    : RPLib_S3_KernelSDA
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T12:26:14.644201+00:00
-- url     : https://prove2.me/theorems/c38ae2b2-0acf-463e-b3ae-e9e15532a668
-- title:
--   The Eichler-Selberg trace formula in weight two: elementary analytic lemmas for the `Γ(M)` Hecke-trick kernel
-- statement:
--   Elementary analytic lemmas for the `Γ(M)` Hecke-trick kernel.
--
--   * `normSq_mul_sub_one_ge`: `2 Im X Im Y ≤ |X Y - 1|²`;
--   * `abs_rpow_sub_one_le`: `|t^s - 1| ≤ |t - 1|` for `t > 0`, `s ∈ [0,1]`;
--   * `norm_Ferr_le`: the MAIN/ERROR bound `‖(A-1)⁻²(η/|A-1|²)^s - A⁻²(η/|A|²)^s‖ ≤ Kerr t / |A|³`;
--   * `sum1D_le`: shifted one-dimensional lattice sums `Σ_a ((t+a)² + h²)^(-3/4)`, uniform in `t`;
--   * `sum2D_le`: two-dimensional sums `Σ_{(c,d)} (|c z + d|²)^(-5/4)`, uniform in `Re z`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224; F. Diamond and J. Shurman, A First Course in Modular Forms, GTM 228, Springer 2005, Chapter 5

import Mathlib

/-!
# S3-ES-Wt2, part KS_D (A): elementary analytic lemmas for the `Γ(M)` Hecke-trick kernel

* `normSq_mul_sub_one_ge`: `2 Im X Im Y ≤ |X Y - 1|²`;
* `abs_rpow_sub_one_le`: `|t^s - 1| ≤ |t - 1|` for `t > 0`, `s ∈ [0,1]`;
* `norm_Ferr_le`: the MAIN/ERROR bound `‖(A-1)⁻²(η/|A-1|²)^s - A⁻²(η/|A|²)^s‖ ≤ Kerr t / |A|³`;
* `sum1D_le`: shifted one-dimensional lattice sums `Σ_a ((t+a)² + h²)^(-3/4)`, uniform in `t`;
* `sum2D_le`: two-dimensional sums `Σ_{(c,d)} (|c z + d|²)^(-5/4)`, uniform in `Re z`.
-/

open Complex Filter Topology

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.KernelSD

/-! ### Pointwise lemmas -/

lemma normSq_mul_sub_one_eq (X Y : ℂ) :
    Complex.normSq (X * Y - 1) = (X.re * Y.re - 1) ^ 2 + (X.im * Y.im) ^ 2 + (X.re * Y.im) ^ 2 +
      (Y.re * X.im) ^ 2 + 2 * (X.im * Y.im) := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.one_re, Complex.one_im]
  ring

lemma normSq_mul_sub_one_ge (X Y : ℂ) : 2 * (X.im * Y.im) ≤ Complex.normSq (X * Y - 1) := by
  rw [normSq_mul_sub_one_eq]
  nlinarith [sq_nonneg (X.re * Y.re - 1), sq_nonneg (X.im * Y.im), sq_nonneg (X.re * Y.im),
    sq_nonneg (Y.re * X.im)]

lemma abs_rpow_sub_one_le {t s : ℝ} (ht : 0 < t) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    |t ^ s - 1| ≤ |t - 1| := by
  rcases le_total 1 t with h | h
  · have h1 : 1 ≤ t ^ s := Real.one_le_rpow h hs0
    have h2 : t ^ s ≤ 1 + s * (t - 1) := by
      have := rpow_one_add_le_one_add_mul_self (s := t - 1) (by linarith) hs0 hs1
      simpa using this
    have h3 : s * (t - 1) ≤ t - 1 := by nlinarith
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith
  · have h1 : t ^ s ≤ 1 := Real.rpow_le_one ht.le h hs0
    have h2 : t ^ (1 : ℝ) ≤ t ^ s := Real.rpow_le_rpow_of_exponent_ge ht h hs1
    rw [Real.rpow_one] at h2
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    linarith

lemma abs_rpow_sub_rpow_le {X Y s : ℝ} (hX : 0 < X) (hY : 0 < Y) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    |X ^ s - Y ^ s| ≤ Y ^ s * |X / Y - 1| := by
  have hYs : 0 < Y ^ s := Real.rpow_pos_of_pos hY s
  have e : X ^ s - Y ^ s = Y ^ s * ((X / Y) ^ s - 1) := by
    rw [Real.div_rpow hX.le hY.le]; field_simp
  rw [e, abs_mul, abs_of_pos hYs]
  exact mul_le_mul_of_nonneg_left (abs_rpow_sub_one_le (div_pos hX hY) hs0 hs1) hYs.le

/-- `y^s ≤ max 1 y` for `y > 0`, `s ∈ [0,1]`. -/
lemma rpow_le_max_one {y s : ℝ} (hy : 0 < y) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : y ^ s ≤ max 1 y := by
  rcases le_total y 1 with h | h
  · exact (Real.rpow_le_one hy.le h hs0).trans (le_max_left _ _)
  · calc y ^ s ≤ y ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h hs1
      _ = y := Real.rpow_one y
      _ ≤ max 1 y := le_max_right _ _

/-- The constant of the ERROR bound. -/
def Kerr (t : ℝ) : ℝ := 4 + 4 * max 1 t⁻¹ + 64 * ((2 * t)⁻¹ + max 1 t⁻¹ / t ^ 2)

/-- `F_s(A) - MAIN_s(A)` (without the `c²` factor). -/
def Ferr (s η : ℝ) (A : ℂ) : ℂ :=
  ((A - 1) ^ 2)⁻¹ * (((η / ‖A - 1‖ ^ 2) ^ s : ℝ) : ℂ) - (A ^ 2)⁻¹ * (((η / ‖A‖ ^ 2) ^ s : ℝ) : ℂ)

lemma norm_Ferr_le {A : ℂ} {η t s : ℝ} (ht : 0 < t) (htη : t ≤ η) (hA : η ≤ ‖A‖)
    (hA1 : 2 * η ≤ ‖A - 1‖ ^ 2) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ‖Ferr s η A‖ ≤ Kerr t * (‖A‖ ^ 3)⁻¹ := by
  set a := ‖A‖ with ha_def
  set b := ‖A - 1‖ with hb_def
  have hη : 0 < η := ht.trans_le htη
  have ha : 0 < a := hη.trans_le hA
  have hb2 : 0 < b ^ 2 := by linarith
  have hb0 : 0 ≤ b := norm_nonneg _
  have hb : 0 < b := by
    rcases hb0.lt_or_eq with h | h
    · exact h
    · rw [← h] at hb2; norm_num at hb2
  have hA0 : A ≠ 0 := norm_pos_iff.mp ha
  have hA10 : A - 1 ≠ 0 := norm_pos_iff.mp hb
  have hab : |a - b| ≤ 1 := by
    have := abs_norm_sub_norm_le A (A - 1)
    simpa using this
  set X := η / b ^ 2 with hX_def
  set Y := η / a ^ 2 with hY_def
  have hX : 0 < X := by positivity
  have hY : 0 < Y := by positivity
  have hX1 : X ≤ 1 := by rw [hX_def, div_le_one hb2]; linarith
  have hXs : X ^ s ≤ 1 := Real.rpow_le_one hX.le hX1 hs0
  have hXs0 : 0 ≤ X ^ s := Real.rpow_nonneg hX.le s
  have hYs0 : 0 ≤ Y ^ s := Real.rpow_nonneg hY.le s
  set K0 := max 1 t⁻¹ with hK0
  have hK01 : 1 ≤ K0 := le_max_left _ _
  have hYle : Y ≤ t⁻¹ := by
    rw [hY_def, div_le_iff₀ (by positivity)]
    have : η * t ≤ a ^ 2 * (t * t⁻¹) := by
      rw [mul_inv_cancel₀ ht.ne', mul_one]; nlinarith
    nlinarith [mul_inv_cancel₀ ht.ne']
  have hYs : Y ^ s ≤ K0 := (rpow_le_max_one hY hs0 hs1).trans (max_le_max le_rfl hYle)
  have hKerr0 : 0 ≤ 64 * ((2 * t)⁻¹ + K0 / t ^ 2) := by positivity
  rcases le_or_gt 4 a with h4 | h4
  · -- large `|A|`
    have hb34 : 3 / 4 * a ≤ b := by
      have := (abs_le.mp hab).2; linarith
    have hnum : ‖2 * A - 1‖ ≤ 9 / 4 * a := by
      calc ‖2 * A - 1‖ ≤ ‖2 * A‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 * a + 1 := by simp [ha_def]
        _ ≤ 9 / 4 * a := by linarith
    have hdiff : ((A - 1) ^ 2)⁻¹ - (A ^ 2)⁻¹ = (2 * A - 1) / ((A - 1) ^ 2 * A ^ 2) := by
      field_simp; ring
    have hT1 : ‖((A - 1) ^ 2)⁻¹ - (A ^ 2)⁻¹‖ ≤ 4 * (a ^ 3)⁻¹ := by
      rw [hdiff, norm_div, norm_mul, norm_pow, norm_pow, ← ha_def, ← hb_def,
        div_le_iff₀ (by positivity)]
      have hb2' : (3 / 4 * a) ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ (by positivity) hb34 2
      calc ‖2 * A - 1‖ ≤ 9 / 4 * a := hnum
        _ = 4 * (a ^ 3)⁻¹ * ((3 / 4 * a) ^ 2 * a ^ 2) := by field_simp; ring
        _ ≤ 4 * (a ^ 3)⁻¹ * (b ^ 2 * a ^ 2) := by gcongr
    have hratio : |X / Y - 1| ≤ 4 * a⁻¹ := by
      have e : X / Y - 1 = (a ^ 2 - b ^ 2) / b ^ 2 := by
        rw [hX_def, hY_def]; field_simp
      rw [e, abs_div, abs_of_pos hb2, div_le_iff₀ hb2]
      have h1 : |a ^ 2 - b ^ 2| ≤ 2 * a + 1 := by
        have : a ^ 2 - b ^ 2 = (a - b) * (a + b) := by ring
        rw [this, abs_mul, abs_of_pos (by linarith : 0 < a + b)]
        have := (abs_le.mp hab)
        nlinarith [abs_nonneg (a - b)]
      have hb2' : (3 / 4 * a) ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ (by positivity) hb34 2
      calc |a ^ 2 - b ^ 2| ≤ 2 * a + 1 := h1
        _ ≤ 9 / 4 * a := by linarith
        _ = 4 * a⁻¹ * (3 / 4 * a) ^ 2 := by field_simp; ring
        _ ≤ 4 * a⁻¹ * b ^ 2 := by gcongr
    have hT2 : |X ^ s - Y ^ s| ≤ K0 * (4 * a⁻¹) :=
      (abs_rpow_sub_rpow_le hX hY hs0 hs1).trans
        (mul_le_mul hYs hratio (abs_nonneg _) (by linarith))
    have hsplit : Ferr s η A = (((A - 1) ^ 2)⁻¹ - (A ^ 2)⁻¹) * ((X ^ s : ℝ) : ℂ) +
        (A ^ 2)⁻¹ * (((X ^ s - Y ^ s : ℝ)) : ℂ) := by
      rw [Ferr, ← hb_def, ← ha_def, ← hX_def, ← hY_def]; push_cast; ring
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg hXs0, norm_inv, norm_pow, ← ha_def]
    have e3 : (a ^ 2)⁻¹ * (K0 * (4 * a⁻¹)) = 4 * K0 * (a ^ 3)⁻¹ := by
      field_simp
    calc ‖((A - 1) ^ 2)⁻¹ - (A ^ 2)⁻¹‖ * X ^ s + (a ^ 2)⁻¹ * |X ^ s - Y ^ s|
        ≤ 4 * (a ^ 3)⁻¹ * 1 + (a ^ 2)⁻¹ * (K0 * (4 * a⁻¹)) := by
          gcongr
      _ = (4 + 4 * K0) * (a ^ 3)⁻¹ := by rw [e3]; ring
      _ ≤ Kerr t * (a ^ 3)⁻¹ := by
          gcongr; rw [Kerr, ← hK0]; linarith
  · -- small `|A|`
    have h1 : ‖((A - 1) ^ 2)⁻¹ * ((X ^ s : ℝ) : ℂ)‖ ≤ (2 * t)⁻¹ := by
      rw [norm_mul, norm_inv, norm_pow, ← hb_def, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hXs0]
      calc (b ^ 2)⁻¹ * X ^ s ≤ (2 * t)⁻¹ * 1 := by
            gcongr
            · linarith
        _ = (2 * t)⁻¹ := mul_one _
    have h2 : ‖(A ^ 2)⁻¹ * ((Y ^ s : ℝ) : ℂ)‖ ≤ K0 / t ^ 2 := by
      rw [norm_mul, norm_inv, norm_pow, ← ha_def, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hYs0, div_eq_inv_mul]
      have : t ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ ht.le (htη.trans hA) 2
      calc (a ^ 2)⁻¹ * Y ^ s ≤ (t ^ 2)⁻¹ * K0 := by gcongr
        _ = (t ^ 2)⁻¹ * K0 := rfl
    have hF : Ferr s η A = ((A - 1) ^ 2)⁻¹ * ((X ^ s : ℝ) : ℂ) - (A ^ 2)⁻¹ * ((Y ^ s : ℝ) : ℂ) := rfl
    have h64 : 1 ≤ 64 * (a ^ 3)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
      have : a ^ 3 ≤ 4 ^ 3 := pow_le_pow_left₀ ha.le h4.le 3
      linarith
    rw [hF]
    calc ‖((A - 1) ^ 2)⁻¹ * ((X ^ s : ℝ) : ℂ) - (A ^ 2)⁻¹ * ((Y ^ s : ℝ) : ℂ)‖
        ≤ (2 * t)⁻¹ + K0 / t ^ 2 := (norm_sub_le _ _).trans (add_le_add h1 h2)
      _ ≤ ((2 * t)⁻¹ + K0 / t ^ 2) * (64 * (a ^ 3)⁻¹) := by
          have : 0 ≤ (2 * t)⁻¹ + K0 / t ^ 2 := by positivity
          nlinarith
      _ ≤ Kerr t * (a ^ 3)⁻¹ := by
          rw [Kerr, ← hK0]
          have : 0 ≤ (a ^ 3)⁻¹ := by positivity
          nlinarith

/-! ### Shifted lattice sums -/

/-- `Σ_a (max 1 |a|)^(-3/2)` (written with squares). -/
def S1 : ℝ := ∑' a : ℤ, ((max 1 |(a : ℝ)|) ^ 2) ^ (-(3 / 4 : ℝ))

lemma summable_S1 : Summable (fun a : ℤ => ((max 1 |(a : ℝ)|) ^ 2) ^ (-(3 / 4 : ℝ))) := by
  refine Summable.of_norm_bounded_eventually (Real.summable_abs_int_rpow (b := 3 / 2) (by norm_num)) ?_
  filter_upwards [Filter.eventually_cofinite_ne 0] with a ha
  have h1 : (1 : ℝ) ≤ |(a : ℝ)| := by exact_mod_cast Int.one_le_abs ha
  rw [max_eq_right h1, Real.norm_eq_abs, abs_of_nonneg (by positivity), ← Real.rpow_natCast,
    ← Real.rpow_mul (abs_nonneg _)]
  norm_num

lemma lower1D {t' h : ℝ} (ht : |t'| ≤ 1 / 2) (hh : 0 < h) (a : ℤ) :
    (min h (1 / 2)) ^ 2 * (max 1 |(a : ℝ)|) ^ 2 ≤ (t' + a) ^ 2 + h ^ 2 := by
  set m := min h (1 / 2)
  have hm0 : 0 < m := lt_min hh (by norm_num)
  have hmh : m ≤ h := min_le_left _ _
  have hm2 : m ≤ 1 / 2 := min_le_right _ _
  by_cases ha : a = 0
  · subst ha
    simp only [Int.cast_zero, abs_zero, max_eq_left (zero_le_one' ℝ), one_pow, mul_one, add_zero]
    nlinarith [sq_nonneg t']
  · have h1 : (1 : ℝ) ≤ |(a : ℝ)| := by exact_mod_cast Int.one_le_abs ha
    rw [max_eq_right h1]
    have h2 : |(a : ℝ)| / 2 ≤ |t' + a| := by
      have := abs_sub_abs_le_abs_sub (a : ℝ) (-t')
      rw [abs_neg, sub_neg_eq_add, add_comm] at this
      linarith
    have h3 : m * |(a : ℝ)| ≤ |t' + a| := by nlinarith
    have h4 : (m * |(a : ℝ)|) ^ 2 ≤ |t' + a| ^ 2 := pow_le_pow_left₀ (by positivity) h3 2
    rw [sq_abs, mul_pow, sq_abs] at h4
    rw [sq_abs]
    nlinarith [sq_nonneg h]

/-- **1D shifted lattice sum**, uniform in the shift `t`. -/
theorem sum1D (t h : ℝ) (hh : 0 < h) :
    Summable (fun a : ℤ => ((t + a) ^ 2 + h ^ 2) ^ (-(3 / 4 : ℝ))) ∧
      ∑' a : ℤ, ((t + a) ^ 2 + h ^ 2) ^ (-(3 / 4 : ℝ)) ≤
        ((min h (1 / 2)) ^ 2) ^ (-(3 / 4 : ℝ)) * S1 := by
  set n0 : ℤ := round t
  have ht' : |t - (n0 : ℝ)| ≤ 1 / 2 := abs_sub_round t
  set f : ℤ → ℝ := fun a => ((t + a) ^ 2 + h ^ 2) ^ (-(3 / 4 : ℝ))
  set e : ℤ ≃ ℤ := Equiv.addRight n0
  have hfe : ∀ a, f (e.symm a) = (((t - n0) + a) ^ 2 + h ^ 2) ^ (-(3 / 4 : ℝ)) := by
    intro a; simp only [f, e, Equiv.addRight_symm, Equiv.coe_addRight]
    congr 1; push_cast; ring
  set m := min h (1 / 2)
  have hm0 : 0 < m := lt_min hh (by norm_num)
  have hpt : ∀ a : ℤ, (((t - n0) + a) ^ 2 + h ^ 2) ^ (-(3 / 4 : ℝ)) ≤
      (m ^ 2) ^ (-(3 / 4 : ℝ)) * ((max 1 |(a : ℝ)|) ^ 2) ^ (-(3 / 4 : ℝ)) := by
    intro a
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) (lower1D ht' hh a) (by norm_num)
  have hs : Summable (fun a : ℤ => (((t - n0) + a) ^ 2 + h ^ 2) ^ (-(3 / 4 : ℝ))) :=
    (summable_S1.mul_left _).of_nonneg_of_le (fun _ => by positivity) hpt
  have hs' : Summable (f ∘ e.symm) := hs.congr fun a => (hfe a).symm
  have hsf : Summable f := (e.symm.summable_iff).mp hs'
  refine ⟨hsf, ?_⟩
  rw [← e.symm.tsum_eq f]
  calc ∑' a, f (e.symm a) = ∑' a : ℤ, (((t - n0) + a) ^ 2 + h ^ 2) ^ (-(3 / 4 : ℝ)) := tsum_congr hfe
    _ ≤ ∑' a : ℤ, (m ^ 2) ^ (-(3 / 4 : ℝ)) * ((max 1 |(a : ℝ)|) ^ 2) ^ (-(3 / 4 : ℝ)) :=
        hs.tsum_le_tsum hpt (summable_S1.mul_left _)
    _ = (m ^ 2) ^ (-(3 / 4 : ℝ)) * S1 := by rw [tsum_mul_left, S1]

/-- `Σ_{(c,d)} (max |c| |d|)^(-5/2)` (written with squares). -/
def S2 : ℝ := ∑' p : ℤ × ℤ, ((max |(p.1 : ℝ)| |(p.2 : ℝ)|) ^ 2) ^ (-(5 / 4 : ℝ))

lemma summable_S2 : Summable (fun p : ℤ × ℤ => ((max |(p.1 : ℝ)| |(p.2 : ℝ)|) ^ 2) ^ (-(5 / 4 : ℝ))) := by
  have h := (EisensteinSeries.summable_one_div_norm_rpow (k := 5 / 2) (by norm_num)).comp_injective
    (finTwoArrowEquiv ℤ).symm.injective
  refine h.congr fun p => ?_
  simp only [Function.comp_apply, EisensteinSeries.norm_eq_max_natAbs, finTwoArrowEquiv_symm_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (le_max_of_le_left (abs_nonneg _))]
  push_cast
  norm_num

lemma lower2D {z : ℂ} {y0 : ℝ} (hy0 : 0 < y0) (hx : |z.re| ≤ 1 / 2) (hy : y0 ≤ z.im) (c d : ℤ) :
    min (1 / 4) (y0 ^ 2) * (max |(c : ℝ)| |(d : ℝ)|) ^ 2 ≤ ‖(c : ℂ) * z + d‖ ^ 2 := by
  have hn : ‖(c : ℂ) * z + d‖ ^ 2 = ((c : ℝ) * z.re + d) ^ 2 + ((c : ℝ) * z.im) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp; ring
  rw [hn]
  have hk1 : min (1 / 4) (y0 ^ 2) ≤ 1 / 4 := min_le_left _ _
  have hk2 : min (1 / 4) (y0 ^ 2) ≤ y0 ^ 2 := min_le_right _ _
  have hk0 : 0 ≤ min (1 / 4) (y0 ^ 2) := le_min (by norm_num) (by positivity)
  rcases le_total |(d : ℝ)| |(c : ℝ)| with h | h
  · rw [max_eq_left h, sq_abs]
    have : y0 ^ 2 ≤ z.im ^ 2 := pow_le_pow_left₀ hy0.le hy 2
    nlinarith [sq_nonneg ((c : ℝ) * z.re + d), sq_nonneg (c : ℝ)]
  · rw [max_eq_right h]
    have h2 : |(d : ℝ)| / 2 ≤ |(c : ℝ) * z.re + d| := by
      have e1 : |(c : ℝ) * z.re| ≤ |(d : ℝ)| / 2 := by
        rw [abs_mul]; nlinarith [abs_nonneg (c : ℝ), abs_nonneg z.re]
      have := abs_sub_abs_le_abs_sub (d : ℝ) (-((c : ℝ) * z.re))
      rw [abs_neg, sub_neg_eq_add, show (d : ℝ) + (c : ℝ) * z.re = (c : ℝ) * z.re + d by ring] at this
      linarith
    have h3 : (|(d : ℝ)| / 2) ^ 2 ≤ |(c : ℝ) * z.re + d| ^ 2 :=
      pow_le_pow_left₀ (by positivity) h2 2
    rw [sq_abs] at h3
    have : ((|(d : ℝ)| / 2) ^ 2) = |(d : ℝ)| ^ 2 / 4 := by ring
    nlinarith [sq_nonneg ((c : ℝ) * z.im), sq_nonneg |(d : ℝ)|]

/-- The shear `(c, d) ↦ (c, d + n c)`. -/
def shear (n : ℤ) : ℤ × ℤ ≃ ℤ × ℤ where
  toFun p := (p.1, p.2 + n * p.1)
  invFun p := (p.1, p.2 - n * p.1)
  left_inv p := by simp
  right_inv p := by simp

/-- **2D lattice sum**, uniform in `Re z`. -/
theorem sum2D {z : ℂ} {y0 : ℝ} (hy0 : 0 < y0) (hy : y0 ≤ z.im) :
    Summable (fun p : ℤ × ℤ => (‖(p.1 : ℂ) * z + p.2‖ ^ 2) ^ (-(5 / 4 : ℝ))) ∧
      ∑' p : ℤ × ℤ, (‖(p.1 : ℂ) * z + p.2‖ ^ 2) ^ (-(5 / 4 : ℝ)) ≤
        (min (1 / 4) (y0 ^ 2)) ^ (-(5 / 4 : ℝ)) * S2 := by
  set n0 : ℤ := round z.re
  set z' : ℂ := z - n0
  have hx' : |z'.re| ≤ 1 / 2 := by simpa [z'] using abs_sub_round z.re
  have hy' : y0 ≤ z'.im := by simpa [z'] using hy
  set f : ℤ × ℤ → ℝ := fun p => (‖(p.1 : ℂ) * z + p.2‖ ^ 2) ^ (-(5 / 4 : ℝ))
  have hfe : ∀ p, f (shear (-n0) p) = (‖(p.1 : ℂ) * z' + p.2‖ ^ 2) ^ (-(5 / 4 : ℝ)) := by
    intro p; simp only [f, shear, Equiv.coe_fn_mk, z']
    congr 3; push_cast; ring
  set κ := min (1 / 4) (y0 ^ 2)
  have hκ : 0 < κ := lt_min (by norm_num) (by positivity)
  have hpt : ∀ p : ℤ × ℤ, (‖(p.1 : ℂ) * z' + p.2‖ ^ 2) ^ (-(5 / 4 : ℝ)) ≤
      κ ^ (-(5 / 4 : ℝ)) * ((max |(p.1 : ℝ)| |(p.2 : ℝ)|) ^ 2) ^ (-(5 / 4 : ℝ)) := by
    intro p
    by_cases hp : max |(p.1 : ℝ)| |(p.2 : ℝ)| = 0
    · have h1 : (p.1 : ℝ) = 0 := abs_eq_zero.mp (le_antisymm (hp ▸ le_max_left _ _) (abs_nonneg _))
      have h2 : (p.2 : ℝ) = 0 := abs_eq_zero.mp (le_antisymm (hp ▸ le_max_right _ _) (abs_nonneg _))
      have h1' : (p.1 : ℂ) = 0 := by exact_mod_cast h1
      have h2' : (p.2 : ℂ) = 0 := by exact_mod_cast h2
      rw [h1', h2', hp]; simp [Real.zero_rpow (by norm_num : (-(5 / 4 : ℝ)) ≠ 0)]
    · have hpos : 0 < max |(p.1 : ℝ)| |(p.2 : ℝ)| :=
        lt_of_le_of_ne (le_max_of_le_left (abs_nonneg _)) (Ne.symm hp)
      rw [← Real.mul_rpow hκ.le (by positivity)]
      exact Real.rpow_le_rpow_of_nonpos (by positivity) (lower2D hy0 hx' hy' p.1 p.2) (by norm_num)
  have hs : Summable (fun p : ℤ × ℤ => (‖(p.1 : ℂ) * z' + p.2‖ ^ 2) ^ (-(5 / 4 : ℝ))) :=
    (summable_S2.mul_left _).of_nonneg_of_le (fun _ => by positivity) hpt
  have hsf : Summable f := ((shear (-n0)).summable_iff).mp (hs.congr fun p => (hfe p).symm)
  refine ⟨hsf, ?_⟩
  rw [← (shear (-n0)).tsum_eq f]
  calc ∑' p, f (shear (-n0) p) = ∑' p : ℤ × ℤ, (‖(p.1 : ℂ) * z' + p.2‖ ^ 2) ^ (-(5 / 4 : ℝ)) :=
        tsum_congr hfe
    _ ≤ ∑' p : ℤ × ℤ, κ ^ (-(5 / 4 : ℝ)) * ((max |(p.1 : ℝ)| |(p.2 : ℝ)|) ^ 2) ^ (-(5 / 4 : ℝ)) :=
        hs.tsum_le_tsum hpt (summable_S2.mul_left _)
    _ = κ ^ (-(5 / 4 : ℝ)) * S2 := by rw [tsum_mul_left, S2]

end RamanujanPetersson.KernelSD


