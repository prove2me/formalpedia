-- Prove2me | Definitions.Def_RPLib_S3_EllW2LC1
-- name    : RPLib_S3_EllW2LC1
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T12:30:44.670537+00:00
-- url     : https://prove2.me/theorems/222c026b-3a2e-4143-b1e8-f6cd3de31293
-- title:
--   The Eichler-Selberg trace formula in weight two: lattice-point count for `eCnt`
-- statement:
--   Lattice-point count for `eCnt`.
--
--   For `z ∈ ℍ` and `y0 > 0`:
--   * `eCnt_ne_top`: `E_{y0}(z) < ∞`;
--   * `abs_y0_eCnt_sub_pi_le` (`im z ≥ 1/2`): `|y0 · E_{y0}(z) − π| ≤ 6 √(y0 · im z) + 2 y0`;
--   * `abs_y0_eCnt_sub_pi_le'` (also `y0 ≤ 1`): `|y0 · E_{y0}(z) − π| ≤ 6 √y0 (1 + √(im z))`.
--   Row `c` fixed: the `d` with `(c x + d)² ≤ R − (c y)²` (`R = y / y0`) form an integer interval of
--   `2 r ± 1` points; the column sum of `2 √(R − (c y)²)` is compared with `∫ = π R / y`
--   (the function is even and antitone on `[0, ∞)`).
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224; H. Iwaniec, Spectral Methods of Automorphic Forms, 2nd ed., Graduate Studies in Mathematics 53, AMS 2002, Chapter 2

import Mathlib
import Definitions.Def_RPLib_S3_EllW2RU2

/-!
# S3-ES-Wt2 (LC1): lattice-point count for `eCnt`

For `z ∈ ℍ` and `y0 > 0`:
* `eCnt_ne_top`: `E_{y0}(z) < ∞`;
* `abs_y0_eCnt_sub_pi_le` (`im z ≥ 1/2`): `|y0 · E_{y0}(z) − π| ≤ 6 √(y0 · im z) + 2 y0`;
* `abs_y0_eCnt_sub_pi_le'` (also `y0 ≤ 1`): `|y0 · E_{y0}(z) − π| ≤ 6 √y0 (1 + √(im z))`.
Row `c` fixed: the `d` with `(c x + d)² ≤ R − (c y)²` (`R = y / y0`) form an integer interval of
`2 r ± 1` points; the column sum of `2 √(R − (c y)²)` is compared with `∫ = π R / y`
(the function is even and antitone on `[0, ∞)`).
-/

set_option autoImplicit false

open MeasureTheory UpperHalfPlane
open scoped ENNReal Real

noncomputable section

namespace RamanujanPetersson.EllW2

variable {y0 : ℝ}

lemma normSq_lc (c d : ℤ) (z : ℍ) :
    Complex.normSq ((c : ℂ) * (z : ℂ) + d) = (c * z.re + d) ^ 2 + (c * z.im) ^ 2 := by
  rw [Complex.normSq_apply]
  simp only [Complex.add_re, Complex.mul_re, Complex.intCast_re, Complex.intCast_im,
    UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, Complex.add_im, Complex.mul_im]
  ring

lemma card_Icc_ceil_floor (u v : ℝ) (h : u ≤ v) :
    v - u - 1 ≤ ((Finset.Icc ⌈u⌉ ⌊v⌋).card : ℝ) ∧
      ((Finset.Icc ⌈u⌉ ⌊v⌋).card : ℝ) ≤ v - u + 1 := by
  have hm : (((Finset.Icc ⌈u⌉ ⌊v⌋).card : ℕ) : ℤ) = max (⌊v⌋ + 1 - ⌈u⌉) 0 := by
    rw [Int.card_Icc, Int.toNat_eq_max]
  have hm' : ((Finset.Icc ⌈u⌉ ⌊v⌋).card : ℝ) = ((max (⌊v⌋ + 1 - ⌈u⌉) 0 : ℤ) : ℝ) := by
    rw [← hm, Int.cast_natCast]
  rw [hm', Int.cast_max]
  push_cast
  have h1 := Int.floor_le v
  have h2 := Int.lt_floor_add_one v
  have h3 := Int.le_ceil u
  have h4 := Int.ceil_lt_add_one u
  constructor
  · exact le_max_of_le_left (by linarith)
  · exact max_le (by linarith) (by linarith)

/-- `R = im z / y0`. -/
def lcR (y0 : ℝ) (z : ℍ) : ℝ := z.im / y0

/-- Half-length of row `c`: `√(R − (c y)²)`. -/
def lcr (y0 : ℝ) (z : ℍ) (c : ℤ) : ℝ := √(lcR y0 z - (c * z.im) ^ 2)

/-- The integers `d` of row `c`. -/
def lcF (y0 : ℝ) (z : ℍ) (c : ℤ) : Finset ℤ :=
  Finset.Icc ⌈-(c * z.re) - lcr y0 z c⌉ ⌊-(c * z.re) + lcr y0 z c⌋

/-- Column range `|c| ≤ K = ⌊√R / y⌋`. -/
def lcK (y0 : ℝ) (z : ℍ) : ℕ := ⌊√(lcR y0 z) / z.im⌋₊

/-- Indicator of `y0 |c z + d|² ≤ im z` (zero pair included). -/
def lcInd (y0 : ℝ) (z : ℍ) (c d : ℤ) : ℝ≥0∞ :=
  if y0 * Complex.normSq ((c : ℂ) * (z : ℂ) + d) ≤ z.im then 1 else 0

lemma lc_iff (hy0 : 0 < y0) (z : ℍ) (c d : ℤ) :
    y0 * Complex.normSq ((c : ℂ) * (z : ℂ) + d) ≤ z.im ↔
      (c * z.re + d) ^ 2 ≤ lcR y0 z - (c * z.im) ^ 2 := by
  rw [normSq_lc, lcR]
  constructor
  · intro h
    have : (c * z.re + d) ^ 2 + (c * z.im) ^ 2 ≤ z.im / y0 := by
      rw [le_div_iff₀' hy0]; exact h
    linarith
  · intro h
    have : (c * z.re + d) ^ 2 + (c * z.im) ^ 2 ≤ z.im / y0 := by linarith
    rwa [le_div_iff₀' hy0] at this

lemma mem_lcF_iff (hy0 : 0 < y0) (z : ℍ) {c : ℤ} (hc : (c * z.im) ^ 2 ≤ lcR y0 z) (d : ℤ) :
    d ∈ lcF y0 z c ↔ y0 * Complex.normSq ((c : ℂ) * (z : ℂ) + d) ≤ z.im := by
  rw [lc_iff hy0, Real.sq_le (sub_nonneg.2 hc)]
  unfold lcF lcr
  rw [Finset.mem_Icc, Int.ceil_le, Int.le_floor]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

lemma tsum_lcInd_row (hy0 : 0 < y0) (z : ℍ) {c : ℤ} (hc : (c * z.im) ^ 2 ≤ lcR y0 z) :
    ∑' d : ℤ, lcInd y0 z c d = (lcF y0 z c).card := by
  rw [tsum_eq_sum (s := lcF y0 z c)]
  · rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
    refine Finset.sum_congr rfl fun d hd => ?_
    unfold lcInd
    exact if_pos ((mem_lcF_iff hy0 z hc d).1 hd)
  · intro d hd
    unfold lcInd
    exact if_neg fun h => hd ((mem_lcF_iff hy0 z hc d).2 h)

lemma lcInd_eq_zero (hy0 : 0 < y0) (z : ℍ) {c : ℤ} (hc : lcR y0 z < (c * z.im) ^ 2) (d : ℤ) :
    lcInd y0 z c d = 0 := by
  unfold lcInd
  refine if_neg ?_
  rw [lc_iff hy0]
  intro h
  nlinarith [sq_nonneg ((c : ℝ) * z.re + d)]

lemma sq_le_of_mem_lcK (hy0 : 0 < y0) (z : ℍ) {c : ℤ}
    (hc : c ∈ Finset.Icc (-(lcK y0 z : ℤ)) (lcK y0 z)) : (c * z.im) ^ 2 ≤ lcR y0 z := by
  rw [Finset.mem_Icc] at hc
  have hy := z.im_pos
  have hR : 0 ≤ lcR y0 z := div_nonneg hy.le hy0.le
  have hρ0 : 0 ≤ √(lcR y0 z) / z.im := div_nonneg (Real.sqrt_nonneg _) hy.le
  have hK : (lcK y0 z : ℝ) ≤ √(lcR y0 z) / z.im := Nat.floor_le hρ0
  have h1 : -(lcK y0 z : ℝ) ≤ c := by exact_mod_cast hc.1
  have h2 : (c : ℝ) ≤ lcK y0 z := by exact_mod_cast hc.2
  have h3 : (c : ℝ) ^ 2 ≤ (√(lcR y0 z) / z.im) ^ 2 := sq_le_sq' (by linarith) (by linarith)
  have h4 : √(lcR y0 z) / z.im * z.im = √(lcR y0 z) := by
    rw [show √(lcR y0 z) / z.im * z.im = √(lcR y0 z) * (z.im / z.im) by ring,
      div_self hy.ne', mul_one]
  calc ((c : ℝ) * z.im) ^ 2 = (c : ℝ) ^ 2 * z.im ^ 2 := by ring
    _ ≤ (√(lcR y0 z) / z.im) ^ 2 * z.im ^ 2 := by gcongr
    _ = (√(lcR y0 z) / z.im * z.im) ^ 2 := by ring
    _ = lcR y0 z := by rw [h4, Real.sq_sqrt hR]

lemma lt_sq_of_not_mem_lcK (hy0 : 0 < y0) (z : ℍ) {c : ℤ}
    (hc : c ∉ Finset.Icc (-(lcK y0 z : ℤ)) (lcK y0 z)) : lcR y0 z < (c * z.im) ^ 2 := by
  rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hc
  have hy := z.im_pos
  have hK : √(lcR y0 z) / z.im < (lcK y0 z : ℝ) + 1 := Nat.lt_floor_add_one _
  have habs : (lcK y0 z : ℝ) + 1 ≤ |(c : ℝ)| := by
    rcases hc with h | h
    · have h' : (c : ℝ) ≤ -(lcK y0 z : ℝ) - 1 := by
        have : c ≤ -(lcK y0 z : ℤ) - 1 := by omega
        exact_mod_cast this
      rw [abs_of_neg (by linarith)]; linarith
    · have h' : (lcK y0 z : ℝ) + 1 ≤ c := by
        have : (lcK y0 z : ℤ) + 1 ≤ c := by omega
        exact_mod_cast this
      rw [abs_of_pos (by linarith)]; linarith
  have h4 : √(lcR y0 z) / z.im * z.im = √(lcR y0 z) := by
    rw [show √(lcR y0 z) / z.im * z.im = √(lcR y0 z) * (z.im / z.im) by ring,
      div_self hy.ne', mul_one]
  have h5 : √(lcR y0 z) < |(c : ℝ)| * z.im := by
    rw [← h4]; exact mul_lt_mul_of_pos_right (by linarith) hy
  calc lcR y0 z < (|(c : ℝ)| * z.im) ^ 2 := Real.lt_sq_of_sqrt_lt h5
    _ = ((c : ℝ) * z.im) ^ 2 := by rw [mul_pow, sq_abs, mul_pow]

/-- **`E_{y0}(z) + 1 = Σ_{|c| ≤ K} #(row c)`.** -/
theorem eCnt_add_one (hy0 : 0 < y0) (z : ℍ) :
    eCnt y0 z + 1 =
      ((∑ c ∈ Finset.Icc (-(lcK y0 z : ℤ)) (lcK y0 z), (lcF y0 z c).card : ℕ) : ℝ≥0∞) := by
  have h0 : ∑' q : ℤ × ℤ, lcInd y0 z q.1 q.2 = eCnt y0 z + 1 := by
    rw [ENNReal.tsum_eq_add_tsum_ite (0 : ℤ × ℤ), add_comm]
    congr 1
    · unfold eCnt
      refine tsum_congr fun q => ?_
      by_cases hq : q = 0
      · subst hq; simp
      · simp [hq, lcInd]
    · simp [lcInd, z.im_pos.le]
  rw [← h0, ENNReal.tsum_prod, tsum_eq_sum (s := Finset.Icc (-(lcK y0 z : ℤ)) (lcK y0 z))]
  · rw [Nat.cast_sum]
    exact Finset.sum_congr rfl fun c hc => tsum_lcInd_row hy0 z (sq_le_of_mem_lcK hy0 z hc)
  · intro c hc
    exact ENNReal.tsum_eq_zero.2 fun d => lcInd_eq_zero hy0 z (lt_sq_of_not_mem_lcK hy0 z hc) d

theorem eCnt_ne_top (hy0 : 0 < y0) (z : ℍ) : eCnt y0 z ≠ ⊤ := by
  have h := eCnt_add_one hy0 z
  intro ht
  rw [ht, top_add] at h
  exact ENNReal.natCast_ne_top _ h.symm

theorem eCnt_toReal_add_one (hy0 : 0 < y0) (z : ℍ) :
    (eCnt y0 z).toReal + 1 =
      ∑ c ∈ Finset.Icc (-(lcK y0 z : ℤ)) (lcK y0 z), ((lcF y0 z c).card : ℝ) := by
  have h := congrArg ENNReal.toReal (eCnt_add_one hy0 z)
  rw [ENNReal.toReal_add (eCnt_ne_top hy0 z) ENNReal.one_ne_top, ENNReal.toReal_one,
    ENNReal.toReal_natCast, Nat.cast_sum] at h
  exact h

/-- `g(t) = √(R − (t y)²)`. -/
def colG (R y t : ℝ) : ℝ := √(R - (t * y) ^ 2)

lemma colG_neg (R y t : ℝ) : colG R y (-t) = colG R y t := by
  unfold colG; rw [neg_mul, neg_sq]

lemma continuous_colG (R y : ℝ) : Continuous (colG R y) := by
  unfold colG
  exact Real.continuous_sqrt.comp (continuous_const.sub ((continuous_id.mul continuous_const).pow 2))

lemma antitoneOn_colG (R : ℝ) {y : ℝ} (hy : 0 ≤ y) : AntitoneOn (colG R y) (Set.Ici 0) := by
  intro s hs t _ hst
  unfold colG
  apply Real.sqrt_le_sqrt
  have h0 : 0 ≤ s * y := mul_nonneg (Set.mem_Ici.mp hs) hy
  have : (s * y) ^ 2 ≤ (t * y) ^ 2 := pow_le_pow_left₀ h0 (mul_le_mul_of_nonneg_right hst hy) 2
  linarith

lemma integral_colG_sym {R y : ℝ} (hR : 0 < R) (hy : 0 < y) :
    ∫ t in (-(√R / y))..(√R / y), colG R y t = π * R / (2 * y) := by
  set ρ := √R / y with hρ
  have hsR : 0 < √R := Real.sqrt_pos.2 hR
  have hρ0 : 0 < ρ := div_pos hsR hy
  have hfun : ∀ t, colG R y t = √R * √(1 - (ρ⁻¹ * t) ^ 2) := by
    intro t
    have h1 : (ρ⁻¹ * t) ^ 2 = (t * y) ^ 2 / R := by
      rw [hρ, inv_div, div_mul_eq_mul_div, div_pow, Real.sq_sqrt hR.le]; ring
    have h2 : R * (1 - (t * y) ^ 2 / R) = R - (t * y) ^ 2 := by
      rw [show R * (1 - (t * y) ^ 2 / R) = R - (t * y) ^ 2 * (R / R) by ring,
        div_self hR.ne', mul_one]
    unfold colG
    rw [h1, ← Real.sqrt_mul hR.le, h2]
  simp only [hfun]
  rw [intervalIntegral.integral_const_mul]
  have hcm : (∫ t in (-ρ)..ρ, √(1 - (ρ⁻¹ * t) ^ 2)) =
      ρ⁻¹⁻¹ • ∫ v in ρ⁻¹ * -ρ..ρ⁻¹ * ρ, √(1 - v ^ 2) :=
    intervalIntegral.integral_comp_mul_left (f := fun v => √(1 - v ^ 2)) (inv_ne_zero hρ0.ne')
  rw [hcm, inv_inv, mul_neg, inv_mul_cancel₀ hρ0.ne', integral_sqrt_one_sub_sq, smul_eq_mul, hρ,
    show √R * (√R / y * (π / 2)) = (√R * √R) * π / (2 * y) by ring, Real.mul_self_sqrt hR.le]
  ring

lemma integral_colG_half {R y T : ℝ} (hR : 0 < R) (hy : 0 < y) (hT : √R / y ≤ T) :
    ∫ t in (0 : ℝ)..T, colG R y t = π * R / (4 * y) := by
  have hsym := integral_colG_sym hR hy
  set ρ := √R / y with hρ
  have hc := continuous_colG R y
  have hii : ∀ a b : ℝ, IntervalIntegrable (colG R y) volume a b :=
    fun a b => hc.intervalIntegrable a b
  have hneg : ∫ t in (-ρ)..0, colG R y t = ∫ t in (0 : ℝ)..ρ, colG R y t := by
    have := intervalIntegral.integral_comp_neg (a := 0) (b := ρ) (f := colG R y)
    simp only [colG_neg, neg_zero] at this
    exact this.symm
  rw [← intervalIntegral.integral_add_adjacent_intervals (hii (-ρ) 0) (hii 0 ρ), hneg] at hsym
  have hρy : ρ * y = √R := by
    rw [hρ, show √R / y * y = √R * (y / y) by ring, div_self hy.ne', mul_one]
  have hEq : Set.EqOn (colG R y) (fun _ => (0 : ℝ)) (Set.uIcc ρ T) := by
    intro t ht
    rw [Set.uIcc_of_le hT] at ht
    show colG R y t = 0
    unfold colG
    rw [Real.sqrt_eq_zero']
    have h1 : √R ≤ t * y := by
      have := mul_le_mul_of_nonneg_right ht.1 hy.le
      rwa [hρy] at this
    have h2 : 0 ≤ √R := Real.sqrt_nonneg R
    nlinarith [Real.sq_sqrt hR.le, mul_nonneg (sub_nonneg.2 h1) (add_nonneg (h2.trans h1) h2)]
  have hzero : ∫ t in ρ..T, colG R y t = 0 := by
    rw [intervalIntegral.integral_congr hEq, intervalIntegral.integral_zero]
  rw [← intervalIntegral.integral_add_adjacent_intervals (hii 0 ρ) (hii ρ T), hzero, add_zero]
  have h4 : π * R / (2 * y) = 2 * (π * R / (4 * y)) := by ring
  linarith

/-- **Column sum vs integral**: `|Σ_{|c| ≤ K} g(c) − π R / (2 y)| ≤ √R` when `K + 1 > √R / y`. -/
lemma sum_colG_bounds {R y : ℝ} (hR : 0 < R) (hy : 0 < y) (K : ℕ) (hK : √R / y < K + 1) :
    2 * (π * R / (4 * y)) - √R ≤ ∑ c ∈ Finset.Icc (-(K : ℤ)) K, colG R y c ∧
      ∑ c ∈ Finset.Icc (-(K : ℤ)) K, colG R y c ≤ 2 * (π * R / (4 * y)) + √R := by
  have hev : Function.Even (fun c : ℤ => colG R y c) := fun c => by
    show colG R y ((-c : ℤ) : ℝ) = colG R y (c : ℝ)
    rw [Int.cast_neg]; exact colG_neg R y c
  rw [Finset.sum_Icc_of_even_eq_range hev K]
  simp only [Int.cast_natCast, Int.cast_zero, two_nsmul]
  have hanti : AntitoneOn (colG R y) (Set.Icc 0 (0 + ((K + 1 : ℕ) : ℝ))) :=
    (antitoneOn_colG R hy.le).mono fun t ht => Set.mem_Ici.2 ht.1
  have hI := integral_colG_half (T := 0 + ((K + 1 : ℕ) : ℝ)) hR hy (by push_cast; linarith)
  have h1 := hanti.integral_le_sum
  have h2 := hanti.sum_le_integral
  rw [hI] at h1 h2
  simp only [zero_add] at h1 h2
  have h3 : ∑ i ∈ Finset.range (K + 1 + 1), colG R y (i : ℝ) =
      ∑ i ∈ Finset.range (K + 1), colG R y ((i + 1 : ℕ) : ℝ) + colG R y ((0 : ℕ) : ℝ) :=
    Finset.sum_range_succ' (fun i : ℕ => colG R y (i : ℝ)) (K + 1)
  have h4 : ∑ i ∈ Finset.range (K + 1 + 1), colG R y (i : ℝ) =
      ∑ i ∈ Finset.range (K + 1), colG R y (i : ℝ) + colG R y ((K + 1 : ℕ) : ℝ) :=
    Finset.sum_range_succ (fun i : ℕ => colG R y (i : ℝ)) (K + 1)
  have h5 : 0 ≤ colG R y ((K + 1 : ℕ) : ℝ) := Real.sqrt_nonneg _
  have h0 : colG R y 0 = √R := by simp [colG]
  have h0' : colG R y ((0 : ℕ) : ℝ) = √R := by simp [colG]
  constructor <;> linarith

/-- **Lattice count**: `|y0 · E_{y0}(z) − π| ≤ 6 √(y0 · im z) + 2 y0` for `im z ≥ 1/2`. -/
theorem abs_y0_eCnt_sub_pi_le (hy0 : 0 < y0) (z : ℍ) (hz : 1 / 2 ≤ z.im) :
    |y0 * (eCnt y0 z).toReal - π| ≤ 6 * √(y0 * z.im) + 2 * y0 := by
  have hy := z.im_pos
  have hR : 0 < lcR y0 z := div_pos hy hy0
  have hK : √(lcR y0 z) / z.im < (lcK y0 z : ℝ) + 1 := Nat.lt_floor_add_one _
  have hK' : (lcK y0 z : ℝ) ≤ √(lcR y0 z) / z.im :=
    Nat.floor_le (div_nonneg (Real.sqrt_nonneg _) hy.le)
  have hS := sum_colG_bounds hR hy (lcK y0 z) hK
  have hE := eCnt_toReal_add_one hy0 z
  have hr : ∀ c : ℤ, lcr y0 z c = colG (lcR y0 z) z.im c := fun c => rfl
  have hrow : ∀ c ∈ Finset.Icc (-(lcK y0 z : ℤ)) (lcK y0 z),
      2 * colG (lcR y0 z) z.im c - 1 ≤ ((lcF y0 z c).card : ℝ) ∧
        ((lcF y0 z c).card : ℝ) ≤ 2 * colG (lcR y0 z) z.im c + 1 := by
    intro c _
    have h0 : 0 ≤ lcr y0 z c := Real.sqrt_nonneg _
    have := card_Icc_ceil_floor (-(c * z.re) - lcr y0 z c) (-(c * z.re) + lcr y0 z c)
      (by linarith)
    have hF : lcF y0 z c =
        Finset.Icc ⌈-(c * z.re) - lcr y0 z c⌉ ⌊-(c * z.re) + lcr y0 z c⌋ := rfl
    rw [hF]
    constructor <;> linarith [this.1, this.2, hr c]
  have hcard : (Finset.Icc (-(lcK y0 z : ℤ)) (lcK y0 z)).card = 2 * lcK y0 z + 1 := by
    rw [Int.card_Icc]; omega
  have hlo := Finset.sum_le_sum fun c hc => (hrow c hc).1
  have hhi := Finset.sum_le_sum fun c hc => (hrow c hc).2
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, hcard, nsmul_eq_mul,
    mul_one] at hlo
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, hcard, nsmul_eq_mul,
    mul_one] at hhi
  push_cast at hlo hhi
  have h2 : √(lcR y0 z) / z.im ≤ 2 * √(lcR y0 z) := by
    rw [div_le_iff₀ hy]; nlinarith [Real.sqrt_nonneg (lcR y0 z)]
  have hb : |(eCnt y0 z).toReal - 4 * (π * lcR y0 z / (4 * z.im))| ≤ 6 * √(lcR y0 z) + 2 := by
    rw [abs_le]; constructor <;> linarith [hS.1, hS.2]
  have h4I : y0 * (4 * (π * lcR y0 z / (4 * z.im))) = π := by
    have : y0 * (4 * (π * lcR y0 z / (4 * z.im))) = π * (y0 / y0) * (z.im / z.im) := by
      unfold lcR; ring
    rw [this, div_self hy0.ne', div_self hy.ne', mul_one, mul_one]
  have hy0R : y0 * √(lcR y0 z) = √(y0 * z.im) := by
    have e : y0 * z.im = y0 ^ 2 * lcR y0 z := by
      have : y0 ^ 2 * lcR y0 z = y0 * z.im * (y0 / y0) := by unfold lcR; ring
      rw [this, div_self hy0.ne', mul_one]
    rw [e, Real.sqrt_mul (sq_nonneg y0), Real.sqrt_sq hy0.le]
  calc |y0 * (eCnt y0 z).toReal - π|
      = |y0 * ((eCnt y0 z).toReal - 4 * (π * lcR y0 z / (4 * z.im)))| := by rw [mul_sub, h4I]
    _ = y0 * |(eCnt y0 z).toReal - 4 * (π * lcR y0 z / (4 * z.im))| := by
        rw [abs_mul, abs_of_pos hy0]
    _ ≤ y0 * (6 * √(lcR y0 z) + 2) := mul_le_mul_of_nonneg_left hb hy0.le
    _ = 6 * (y0 * √(lcR y0 z)) + 2 * y0 := by ring
    _ = 6 * √(y0 * z.im) + 2 * y0 := by rw [hy0R]

/-- **Lattice count, `y0 ≤ 1`**: `|y0 · E_{y0}(z) − π| ≤ 6 √y0 (1 + √(im z))`. -/
theorem abs_y0_eCnt_sub_pi_le' (hy0 : 0 < y0) (hy01 : y0 ≤ 1) (z : ℍ) (hz : 1 / 2 ≤ z.im) :
    |y0 * (eCnt y0 z).toReal - π| ≤ 6 * √y0 * (1 + √z.im) := by
  refine (abs_y0_eCnt_sub_pi_le hy0 z hz).trans ?_
  rw [Real.sqrt_mul hy0.le]
  have hs := Real.sqrt_nonneg y0
  have hs1 : √y0 ≤ 1 := by
    rw [show (1 : ℝ) = √1 from Real.sqrt_one.symm]; exact Real.sqrt_le_sqrt hy01
  have h1 : y0 ≤ √y0 := by
    nlinarith [Real.mul_self_sqrt hy0.le, mul_nonneg (sub_nonneg.2 hs1) hs]
  nlinarith [Real.sqrt_nonneg z.im]

end RamanujanPetersson.EllW2


