-- Prove2me | Definitions.Def_RPLib_S3_HypParD
-- name    : RPLib_S3_HypParD
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-13T21:01:16.21697+00:00
-- url     : https://prove2.me/theorems/1297ae7d-48f4-42f4-b76c-689c32c6d886
-- title:
--   The Eichler-Selberg trace formula, hyperbolic part D: the cusp estimate
-- statement:
--   For $g$ of determinant $n > 0$ with lower-left entry $c \ne 0$ and $z = x + iy$, $|x| \le 1/2$, $y^2 \ge 4n$: lower bounds for $|C_g|^2$ and the resulting decay of $u_g$ that makes the $c \ne 0$ part of the top-edge integral vanish as $Y \to \infty$.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer: the Eichler-Selberg trace formula on $S_k(\Gamma_1(M))$ for $k \ge 3$, proved by Zagier's kernel method). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976 (with the Correction in later printings)

import Mathlib
import Definitions.Def_RPLib_S3_HypParA

/-!
# S3-HypParTerms, part D: the cusp estimate for the `c ≠ 0` terms

For `g = [[a,b],[c,d]]` of determinant `n > 0` with `c ≠ 0`, and `z = x + i y` with `|x| ≤ 1/2`, `y² ≥ 4n`:

* `normSq_Cf_ge`: `|C|² ≥ y² (B + 2n)` where `B = c² y² + (a - c x)² + (c x + d)²`
  (exact identity `c² (|C|² - y² (B + 2n)) = (n - (a - c x)(c x + d))²`);
* `norm_uf_sq_le`: `‖u_g(z)‖² ≤ 2 / (y² B³)` (`u_g = uf g m z (conj z)`, `m ≥ 2`);
* `norm_uf_le_maj`: `‖u_g(z)‖ ≤ 144 n³ / y · maj g`, with the majorant
  `maj g = f(c) f(a) f(q)`, `f(j) = (1 + j²)^(-3/4)`, `q = d / s`, `s = |c / gcd(a, c)|`;
* `summable_maj`: `Σ_{det g = n, c ≠ 0} maj g < ∞` (the map `g ↦ (c, a, q)` is injective because the admissible
  `d` for fixed `(a, c)` form one residue class mod `s`), a product of three `p`-series with `p = 3/2`.

So the `c ≠ 0` part of the top-edge term is `O(1/Y)` uniformly, with no integral comparison needed.
Also `norm_uf_sq_le_of_large`: `‖u_g‖² ≤ 2 y^(2m) / |C|^(2m+2)` once `|C|² ≥ 8 n y²` (any `g`, for O4b).
-/

open Complex
open scoped ComplexConjugate

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.HypPar

open RamanujanPetersson.Kernel

/-! ## The `p`-series majorant -/

section Majorant

/-- `f(j) = (1 + j²)^(-3/4)`. -/
def fw (j : ℤ) : ℝ := (1 + (j : ℝ) ^ 2) ^ (-(3 / 4 : ℝ))

lemma fw_nonneg (j : ℤ) : 0 ≤ fw j := by unfold fw; positivity

lemma fw_pow_four (j : ℤ) : fw j ^ 4 = ((1 + (j : ℝ) ^ 2) ^ 3)⁻¹ := by
  unfold fw
  have h0 : (0 : ℝ) ≤ 1 + (j : ℝ) ^ 2 := by positivity
  rw [← Real.rpow_natCast ((1 + (j : ℝ) ^ 2) ^ (-(3 / 4 : ℝ))) 4, ← Real.rpow_mul h0,
    ← Real.rpow_natCast (1 + (j : ℝ) ^ 2) 3, ← Real.rpow_neg h0]
  congr 1; push_cast; ring

lemma summable_fw : Summable fw := by
  have h2 := Real.summable_abs_int_rpow (b := 3 / 2) (by norm_num)
  have hite : Summable fun j : ℤ => if j = 0 then (1 : ℝ) else 0 :=
    summable_of_ne_finset_zero (s := {0}) (by intro j hj; simp at hj; simp [hj])
  refine (h2.add hite).of_nonneg_of_le (fun j => fw_nonneg j) (fun j => ?_)
  by_cases hj : j = 0
  · subst hj; simp [fw]
  · simp only [hj, if_false, add_zero]
    unfold fw
    have hj1 : (0 : ℝ) < |(j : ℝ)| := by positivity
    calc (1 + (j : ℝ) ^ 2) ^ (-(3 / 4 : ℝ)) ≤ ((j : ℝ) ^ 2) ^ (-(3 / 4 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)
      _ = |(j : ℝ)| ^ (-(3 / 2 : ℝ)) := by
          rw [← sq_abs, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
          congr 1; push_cast; ring

lemma summable_fw3 : Summable fun p : ℤ × ℤ × ℤ => fw p.1 * (fw p.2.1 * fw p.2.2) :=
  summable_fw.mul_of_nonneg (summable_fw.mul_of_nonneg summable_fw fw_nonneg fw_nonneg)
    fw_nonneg (fun _ => mul_nonneg (fw_nonneg _) (fw_nonneg _))

end Majorant

/-! ## The spacing `s = |c / gcd(a, c)|` and the injectivity of `g ↦ (c, a, d / s)` -/

section Spacing

/-- The spacing of the admissible `d` for fixed `(a, c)`: `s(g) = |c / gcd(a, c)|`. -/
def sg (g : Matrix (Fin 2) (Fin 2) ℤ) : ℤ := |g 1 0 / (Int.gcd (g 0 0) (g 1 0) : ℤ)|

/-- `q(g) = d / s(g)` (Euclidean division). -/
def qg (g : Matrix (Fin 2) (Fin 2) ℤ) : ℤ := g 1 1 / sg g

/-- The majorant `f(c) f(a) f(q)`. -/
def maj (g : Matrix (Fin 2) (Fin 2) ℤ) : ℝ := fw (g 1 0) * (fw (g 0 0) * fw (qg g))

lemma maj_nonneg (g : Matrix (Fin 2) (Fin 2) ℤ) : 0 ≤ maj g :=
  mul_nonneg (fw_nonneg _) (mul_nonneg (fw_nonneg _) (fw_nonneg _))

/-- Determinant `n`, lower-left entry nonzero. -/
def cSet (n : ℤ) : Set (Matrix (Fin 2) (Fin 2) ℤ) := {g | g.det = n ∧ g 1 0 ≠ 0}

lemma gcd_pos_c {g : Matrix (Fin 2) (Fin 2) ℤ} (hc : g 1 0 ≠ 0) : 0 < Int.gcd (g 0 0) (g 1 0) :=
  Int.gcd_pos_of_ne_zero_right _ hc

lemma abs_c_eq (g : Matrix (Fin 2) (Fin 2) ℤ) :
    |g 1 0| = (Int.gcd (g 0 0) (g 1 0) : ℤ) * sg g := by
  have h := Int.mul_ediv_cancel' (Int.gcd_dvd_right (g 0 0) (g 1 0))
  unfold sg
  calc |g 1 0| = |(Int.gcd (g 0 0) (g 1 0) : ℤ) * (g 1 0 / (Int.gcd (g 0 0) (g 1 0) : ℤ))| := by rw [h]
    _ = _ := by rw [abs_mul, Nat.abs_cast]

lemma sg_pos {g : Matrix (Fin 2) (Fin 2) ℤ} (hc : g 1 0 ≠ 0) : 0 < sg g := by
  have h1 := abs_c_eq g
  have h2 : 0 ≤ sg g := abs_nonneg _
  rcases h2.lt_or_eq with h | h
  · exact h
  · rw [← h, mul_zero, abs_eq_zero] at h1; exact absurd h1 hc

lemma sg_le {g : Matrix (Fin 2) (Fin 2) ℤ} (hc : g 1 0 ≠ 0) : sg g ≤ |g 1 0| := by
  have h1 := abs_c_eq g
  have hG : (1 : ℤ) ≤ (Int.gcd (g 0 0) (g 1 0) : ℤ) := by
    have := gcd_pos_c hc; omega
  nlinarith [mul_nonneg (sub_nonneg.2 hG) (sg_pos hc).le]

lemma gcd_dvd_det (g : Matrix (Fin 2) (Fin 2) ℤ) : (Int.gcd (g 0 0) (g 1 0) : ℤ) ∣ g.det := by
  rw [Matrix.det_fin_two]
  exact dvd_sub (dvd_mul_of_dvd_left (Int.gcd_dvd_left _ _) _) (dvd_mul_of_dvd_right (Int.gcd_dvd_right _ _) _)

lemma abs_c_le {g : Matrix (Fin 2) (Fin 2) ℤ} (hn : 0 < g.det) : |g 1 0| ≤ g.det * sg g := by
  have hG := Int.le_of_dvd hn (gcd_dvd_det g)
  rw [abs_c_eq]
  exact mul_le_mul_of_nonneg_right hG (abs_nonneg _)

lemma sg_dvd {g : Matrix (Fin 2) (Fin 2) ℤ} (hc : g 1 0 ≠ 0) {e : ℤ} (h : g 1 0 ∣ g 0 0 * e) : sg g ∣ e := by
  have H : 0 < Int.gcd (g 0 0) (g 1 0) := gcd_pos_c hc
  have hG0 : (Int.gcd (g 0 0) (g 1 0) : ℤ) ≠ 0 := by exact_mod_cast H.ne'
  have ha := Int.mul_ediv_cancel' (Int.gcd_dvd_left (g 0 0) (g 1 0))
  have hc' := Int.mul_ediv_cancel' (Int.gcd_dvd_right (g 0 0) (g 1 0))
  have h' : (Int.gcd (g 0 0) (g 1 0) : ℤ) * (g 1 0 / (Int.gcd (g 0 0) (g 1 0) : ℤ)) ∣
      (Int.gcd (g 0 0) (g 1 0) : ℤ) * (g 0 0 / (Int.gcd (g 0 0) (g 1 0) : ℤ) * e) := by
    rw [← mul_assoc, ha, hc']; exact h
  have h2 := (mul_dvd_mul_iff_left hG0).1 h'
  have hcop : Int.gcd (g 1 0 / (Int.gcd (g 0 0) (g 1 0) : ℤ)) (g 0 0 / (Int.gcd (g 0 0) (g 1 0) : ℤ)) = 1 := by
    rw [Int.gcd_comm]; exact Int.gcd_div_gcd_div_gcd H
  unfold sg
  exact (abs_dvd _ _).2 (Int.dvd_of_dvd_mul_right_of_gcd_one h2 hcop)

lemma inj_key {n : ℤ} {g g' : Matrix (Fin 2) (Fin 2) ℤ} (hg : g.det = n) (hg' : g'.det = n) (hc : g 1 0 ≠ 0)
    (h1 : g 1 0 = g' 1 0) (h2 : g 0 0 = g' 0 0) (h3 : qg g = qg g') : g = g' := by
  have hs : sg g' = sg g := by unfold sg; rw [h1, h2]
  rw [Matrix.det_fin_two] at hg hg'
  rw [← h1, ← h2] at hg'
  have hdet : g 0 0 * (g 1 1 - g' 1 1) = g 1 0 * (g 0 1 - g' 0 1) := by linear_combination hg - hg'
  have hdvd : sg g ∣ g 1 1 - g' 1 1 := sg_dvd hc ⟨_, hdet⟩
  have hmod : g 1 1 % sg g = g' 1 1 % sg g :=
    Int.emod_eq_emod_iff_emod_sub_eq_zero.2 (Int.emod_eq_zero_of_dvd hdvd)
  have hq : g 1 1 / sg g = g' 1 1 / sg g := by
    have := h3; unfold qg at this; rw [hs] at this; exact this
  have hd : g 1 1 = g' 1 1 := by
    calc g 1 1 = sg g * (g 1 1 / sg g) + g 1 1 % sg g := (Int.mul_ediv_add_emod _ _).symm
      _ = sg g * (g' 1 1 / sg g) + g' 1 1 % sg g := by rw [hq, hmod]
      _ = g' 1 1 := Int.mul_ediv_add_emod _ _
  have hb : g 0 1 = g' 0 1 := by
    rw [hd, sub_self, mul_zero] at hdet
    have := (mul_eq_zero.1 hdet.symm).resolve_left hc
    linarith
  rw [Matrix.eta_fin_two g, Matrix.eta_fin_two g', h1, h2, hb, hd]

/-- **Summability of the majorant** over `{det g = n, c ≠ 0}`. -/
theorem summable_maj (n : ℤ) : Summable fun g : cSet n => maj g.1 := by
  have hinj : Function.Injective (fun g : cSet n => ((g.1 1 0, g.1 0 0, qg g.1) : ℤ × ℤ × ℤ)) := by
    intro x y hxy
    obtain ⟨g, hgd, hgc⟩ := x
    obtain ⟨g', hgd', _⟩ := y
    simp only [Prod.mk.injEq] at hxy
    obtain ⟨h1, h2, h3⟩ := hxy
    exact Subtype.ext (inj_key hgd hgd' hgc h1 h2 h3)
  refine (summable_fw3.comp_injective hinj).congr (fun g => ?_)
  simp only [Function.comp_apply, maj]

end Spacing

/-! ## The pointwise bound -/

section Bound

/-- `B = c² y² + (a - c x)² + (c x + d)²`. -/
def Bf (g : Matrix (Fin 2) (Fin 2) ℤ) (z : ℂ) : ℝ :=
  (g 1 0 : ℝ) ^ 2 * z.im ^ 2 + ((g 0 0 : ℝ) - g 1 0 * z.re) ^ 2 + ((g 1 0 : ℝ) * z.re + g 1 1) ^ 2

lemma normSq_Cf_ge {g : Matrix (Fin 2) (Fin 2) ℤ} (hc : g 1 0 ≠ 0) (z : ℂ) :
    z.im ^ 2 * (Bf g z + 2 * (g.det : ℝ)) ≤ normSq (Cf g z (conj z)) := by
  have hc' : (0 : ℝ) < (g 1 0 : ℝ) ^ 2 := by
    have : (g 1 0 : ℝ) ≠ 0 := by exact_mod_cast hc
    positivity
  have key : (g 1 0 : ℝ) ^ 2 * (normSq (Cf g z (conj z)) - z.im ^ 2 * (Bf g z + 2 * (g.det : ℝ))) =
      ((g.det : ℝ) - ((g 0 0 : ℝ) - g 1 0 * z.re) * ((g 1 0 : ℝ) * z.re + g 1 1)) ^ 2 := by
    rw [normSq_Cf_conj, Matrix.det_fin_two]; simp only [Bf, Pf]; push_cast; ring
  have h0 : 0 ≤ normSq (Cf g z (conj z)) - z.im ^ 2 * (Bf g z + 2 * (g.det : ℝ)) :=
    le_of_mul_le_mul_left (by rw [mul_zero, key]; exact sq_nonneg _) hc'
  linarith

lemma normSq_uf_conj (g : Matrix (Fin 2) (Fin 2) ℤ) (m : ℕ) (z : ℂ) :
    ‖uf g m z (conj z)‖ ^ 2 =
      (z.im ^ 2) ^ m / (normSq (Cf g z (conj z)) ^ m * normSq (qf g (conj z))) := by
  rw [Complex.sq_norm, uf, Yf_conj, map_div₀, map_mul, map_pow, map_pow, Complex.normSq_ofReal]
  ring

/-- For any `g` of positive determinant: `‖u_g‖² ≤ 2 y^(2m) / |C|^(2m+2)` once `|C|² ≥ 8 n y²`. -/
lemma norm_uf_sq_le_of_large {g : Matrix (Fin 2) (Fin 2) ℤ} (m : ℕ) {z : ℂ} (hy : 0 < z.im)
    (hdet : 0 < g.det) (hL : 8 * (g.det : ℝ) * z.im ^ 2 ≤ normSq (Cf g z (conj z))) :
    ‖uf g m z (conj z)‖ ^ 2 ≤ 2 * (z.im ^ 2) ^ m / normSq (Cf g z (conj z)) ^ (m + 1) := by
  rw [normSq_uf_conj]
  have hC : 0 < normSq (Cf g z (conj z)) := normSq_pos.2 (Cf_conj_ne_zero hdet hy)
  have hdetR : (0 : ℝ) < g.det := by exact_mod_cast hdet
  have hq : normSq (Cf g z (conj z)) / 2 ≤ normSq (qf g (conj z)) := by
    rw [normSq_qf_conj_eq]; nlinarith [sq_nonneg z.im]
  have hq0 : 0 < normSq (qf g (conj z)) := lt_of_lt_of_le (by positivity) hq
  rw [div_le_div_iff₀ (mul_pos (pow_pos hC m) hq0) (pow_pos hC (m + 1))]
  have h1 : normSq (Cf g z (conj z)) ^ (m + 1) ≤
      2 * (normSq (Cf g z (conj z)) ^ m * normSq (qf g (conj z))) := by
    rw [pow_succ]
    have := mul_le_mul_of_nonneg_left hq (pow_pos hC m).le
    nlinarith
  have h2 := mul_le_mul_of_nonneg_left h1 (pow_nonneg (sq_nonneg z.im) m)
  nlinarith

lemma one_le_c_sq {g : Matrix (Fin 2) (Fin 2) ℤ} (hc : g 1 0 ≠ 0) : (1 : ℝ) ≤ (g 1 0 : ℝ) ^ 2 := by
  have h' : (1 : ℝ) ≤ |(g 1 0 : ℝ)| := by exact_mod_cast Int.one_le_abs hc
  nlinarith [sq_abs (g 1 0 : ℝ), abs_nonneg (g 1 0 : ℝ)]

lemma norm_uf_sq_le {g : Matrix (Fin 2) (Fin 2) ℤ} {n : ℤ} (hdet : g.det = n) (hn : 0 < n)
    (hc : g 1 0 ≠ 0) {m : ℕ} (hm : 2 ≤ m) {z : ℂ} (hy : 0 < z.im) (hyn : 4 * (n : ℝ) ≤ z.im ^ 2) :
    ‖uf g m z (conj z)‖ ^ 2 ≤ 2 / (z.im ^ 2 * Bf g z ^ 3) := by
  have hc1 := one_le_c_sq hc
  have hy2 : 0 < z.im ^ 2 := by positivity
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show (1 : ℤ) ≤ n by omega)
  have hB1 : z.im ^ 2 ≤ Bf g z := by
    have := mul_le_mul_of_nonneg_right hc1 hy2.le
    unfold Bf
    nlinarith [sq_nonneg ((g 0 0 : ℝ) - g 1 0 * z.re), sq_nonneg ((g 1 0 : ℝ) * z.re + g 1 1)]
  have hB0 : 0 < Bf g z := lt_of_lt_of_le hy2 hB1
  have hBone : 1 ≤ Bf g z := by linarith
  have hC : z.im ^ 2 * Bf g z ≤ normSq (Cf g z (conj z)) := by
    have := normSq_Cf_ge hc z
    rw [hdet] at this
    have h2 : 0 ≤ z.im ^ 2 * (2 * (n : ℝ)) := by positivity
    nlinarith
  have hq : z.im ^ 2 * Bf g z / 2 ≤ normSq (qf g (conj z)) := by
    have := normSq_Cf_ge hc z
    rw [normSq_qf_conj_eq, hdet]
    rw [hdet] at this
    nlinarith [mul_nonneg hy2.le (sub_nonneg.2 (hyn.trans hB1))]
  have hyB : 0 < z.im ^ 2 * Bf g z := mul_pos hy2 hB0
  rw [normSq_uf_conj]
  calc (z.im ^ 2) ^ m / (normSq (Cf g z (conj z)) ^ m * normSq (qf g (conj z)))
      ≤ (z.im ^ 2) ^ m / ((z.im ^ 2 * Bf g z) ^ m * (z.im ^ 2 * Bf g z / 2)) := by
        apply div_le_div_of_nonneg_left (by positivity) (mul_pos (pow_pos hyB m) (by linarith))
        exact mul_le_mul (pow_le_pow_left₀ hyB.le hC m) hq (by linarith) (pow_nonneg hyB.le m |>.trans
          (pow_le_pow_left₀ hyB.le hC m))
    _ = 2 / (z.im ^ 2 * Bf g z ^ (m + 1)) := by
        rw [div_eq_div_iff (mul_pos (pow_pos hyB m) (by linarith)).ne' (mul_pos hy2 (pow_pos hB0 _)).ne']
        ring
    _ ≤ 2 / (z.im ^ 2 * Bf g z ^ 3) := by
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hBone (by omega)) hy2.le

lemma Bf_ge {g : Matrix (Fin 2) (Fin 2) ℤ} {z : ℂ} (hx : |z.re| ≤ 1 / 2) (hy : 1 ≤ z.im) :
    ((g 1 0 : ℝ) ^ 2 + (g 0 0 : ℝ) ^ 2 + (g 1 1 : ℝ) ^ 2) / 2 ≤ Bf g z := by
  have hx2 : z.re ^ 2 ≤ 1 / 4 := by nlinarith [abs_nonneg z.re, sq_abs z.re]
  have hy2 : 1 ≤ z.im ^ 2 := by nlinarith
  have h1 : (g 1 0 : ℝ) ^ 2 * z.re ^ 2 ≤ (g 1 0 : ℝ) ^ 2 * (1 / 4) :=
    mul_le_mul_of_nonneg_left hx2 (sq_nonneg _)
  have h2 : (g 1 0 : ℝ) ^ 2 * 1 ≤ (g 1 0 : ℝ) ^ 2 * z.im ^ 2 :=
    mul_le_mul_of_nonneg_left hy2 (sq_nonneg _)
  unfold Bf
  nlinarith [sq_nonneg ((g 0 0 : ℝ) - 2 * g 1 0 * z.re), sq_nonneg ((g 1 1 : ℝ) + 2 * g 1 0 * z.re)]

/-- The arithmetic core: `(1+c²)(1+q²)(1+a²) ≤ 36 n⁴ (c² + a² + d²)²` when `d = s q + r`, `0 ≤ r < s`,
`s ≤ |c| ≤ n s`. -/
lemma arith_key {c a d s q r n : ℝ} (hs : 0 < s) (hr0 : 0 ≤ r) (hrs : r < s) (hd : d = s * q + r)
    (hsc : s ^ 2 ≤ c ^ 2) (hcn : c ^ 2 ≤ n ^ 2 * s ^ 2) (hc1 : 1 ≤ c ^ 2) (_hn1 : 1 ≤ n) :
    (1 + c ^ 2) * (1 + q ^ 2) * (1 + a ^ 2) ≤ 36 * n ^ 4 * (c ^ 2 + a ^ 2 + d ^ 2) ^ 2 := by
  have hq : 0 ≤ 1 + q ^ 2 := by positivity
  have e1 : s ^ 2 * (1 + q ^ 2) ≤ 3 * (s ^ 2 + d ^ 2) := by
    subst hd; nlinarith [sq_nonneg (s * q + 3 / 2 * r), mul_le_mul hrs.le hrs.le hr0 hs.le, sq_nonneg s]
  have e2 : c ^ 2 * (1 + q ^ 2) ≤ 3 * n ^ 2 * (c ^ 2 + d ^ 2) := by
    have h1 := mul_le_mul_of_nonneg_right hcn hq
    have h3 := mul_le_mul_of_nonneg_left e1 (sq_nonneg n)
    have h4 := mul_le_mul_of_nonneg_left hsc (sq_nonneg n)
    nlinarith
  have e3 : (1 + c ^ 2) * (1 + q ^ 2) ≤ 6 * n ^ 2 * (c ^ 2 + d ^ 2) := by
    have h1 := mul_le_mul_of_nonneg_right hc1 hq
    nlinarith
  have hn2 : 1 ≤ 6 * n ^ 2 := by nlinarith
  have e4 : (1 + c ^ 2) * (1 + q ^ 2) + a ^ 2 ≤ 6 * n ^ 2 * (c ^ 2 + a ^ 2 + d ^ 2) := by
    have h1 := mul_le_mul_of_nonneg_right hn2 (sq_nonneg a)
    nlinarith
  have hU : 1 ≤ (1 + c ^ 2) * (1 + q ^ 2) := by
    nlinarith [sq_nonneg c, sq_nonneg q, mul_nonneg (sq_nonneg c) (sq_nonneg q)]
  have e5 : ((1 + c ^ 2) * (1 + q ^ 2) + (1 + a ^ 2)) / 2 ≤ (1 + c ^ 2) * (1 + q ^ 2) + a ^ 2 := by
    nlinarith [sq_nonneg a]
  have e6 : (1 + c ^ 2) * (1 + q ^ 2) * (1 + a ^ 2) ≤
      (((1 + c ^ 2) * (1 + q ^ 2) + (1 + a ^ 2)) / 2) ^ 2 := by
    nlinarith [sq_nonneg ((1 + c ^ 2) * (1 + q ^ 2) - (1 + a ^ 2))]
  have hR : 0 ≤ ((1 + c ^ 2) * (1 + q ^ 2) + (1 + a ^ 2)) / 2 := by positivity
  calc (1 + c ^ 2) * (1 + q ^ 2) * (1 + a ^ 2) ≤ (((1 + c ^ 2) * (1 + q ^ 2) + (1 + a ^ 2)) / 2) ^ 2 := e6
    _ ≤ (6 * n ^ 2 * (c ^ 2 + a ^ 2 + d ^ 2)) ^ 2 := pow_le_pow_left₀ hR (e5.trans e4) 2
    _ = 36 * n ^ 4 * (c ^ 2 + a ^ 2 + d ^ 2) ^ 2 := by ring

lemma maj_pow_four (g : Matrix (Fin 2) (Fin 2) ℤ) :
    maj g ^ 4 = (((1 + (g 1 0 : ℝ) ^ 2) * (1 + (qg g : ℝ) ^ 2) * (1 + (g 0 0 : ℝ) ^ 2)) ^ 3)⁻¹ := by
  unfold maj
  simp only [mul_pow, fw_pow_four, mul_inv]
  ring

/-- **Cusp estimate.** For `det g = n > 0`, `c ≠ 0`, `m ≥ 2`, `|x| ≤ 1/2`, `y² ≥ 4n`:
`‖u_g(z)‖ ≤ 144 n³ / y · maj g`. -/
theorem norm_uf_le_maj {g : Matrix (Fin 2) (Fin 2) ℤ} {n : ℤ} (hdet : g.det = n) (hn : 0 < n)
    (hc : g 1 0 ≠ 0) {m : ℕ} (hm : 2 ≤ m) {z : ℂ} (hx : |z.re| ≤ 1 / 2) (hy : 0 < z.im)
    (hyn : 4 * (n : ℝ) ≤ z.im ^ 2) :
    ‖uf g m z (conj z)‖ ≤ 144 * (n : ℝ) ^ 3 / z.im * maj g := by
  have h2 := norm_uf_sq_le hdet hn hc hm hy hyn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show (1 : ℤ) ≤ n by omega)
  have hy1 : 1 ≤ z.im := by nlinarith
  have hBR := Bf_ge (g := g) hx hy1
  -- the arithmetic data
  have spos := sg_pos hc
  have hdetpos : 0 < g.det := by rw [hdet]; exact hn
  have hsR : (0 : ℝ) < sg g := by exact_mod_cast spos
  have hr0 : (0 : ℝ) ≤ ((g 1 1 % sg g : ℤ) : ℝ) := by exact_mod_cast Int.emod_nonneg _ spos.ne'
  have hrs : ((g 1 1 % sg g : ℤ) : ℝ) < sg g := by exact_mod_cast Int.emod_lt_of_pos _ spos
  have hd : (g 1 1 : ℝ) = (sg g : ℝ) * (qg g : ℝ) + ((g 1 1 % sg g : ℤ) : ℝ) := by
    have h := Int.mul_ediv_add_emod (g 1 1) (sg g)
    unfold qg; exact_mod_cast h.symm
  have hsle : (sg g : ℝ) ≤ |(g 1 0 : ℝ)| := by exact_mod_cast sg_le hc
  have hsc : (sg g : ℝ) ^ 2 ≤ (g 1 0 : ℝ) ^ 2 := by
    rw [← sq_abs (g 1 0 : ℝ)]; exact pow_le_pow_left₀ hsR.le hsle 2
  have hcle : |(g 1 0 : ℝ)| ≤ (n : ℝ) * sg g := by
    have := abs_c_le hdetpos; rw [hdet] at this; exact_mod_cast this
  have hcn : (g 1 0 : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 * (sg g : ℝ) ^ 2 := by
    rw [← sq_abs (g 1 0 : ℝ), ← mul_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hcle 2
  have hW := arith_key (a := (g 0 0 : ℝ)) hsR hr0 hrs hd hsc hcn (one_le_c_sq hc) hnR
  set W := (1 + (g 1 0 : ℝ) ^ 2) * (1 + (qg g : ℝ) ^ 2) * (1 + (g 0 0 : ℝ) ^ 2) with hWdef
  set B := Bf g z with hBdef
  have hW0 : 0 < W := by positivity
  have hRnn : 0 ≤ (g 1 0 : ℝ) ^ 2 + (g 0 0 : ℝ) ^ 2 + (g 1 1 : ℝ) ^ 2 := by positivity
  have hB0 : 0 < B := by
    have := one_le_c_sq hc
    nlinarith [sq_nonneg (g 0 0 : ℝ), sq_nonneg (g 1 1 : ℝ)]
  have hWB : W ≤ 144 * (n : ℝ) ^ 4 * B ^ 2 := by
    have h1 : ((g 1 0 : ℝ) ^ 2 + (g 0 0 : ℝ) ^ 2 + (g 1 1 : ℝ) ^ 2) ^ 2 ≤ (2 * B) ^ 2 :=
      pow_le_pow_left₀ hRnn (by linarith) 2
    have h3 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 36 * (n : ℝ) ^ 4)
    linarith
  have hK : 4 * W ^ 3 ≤ (144 * (n : ℝ) ^ 3) ^ 4 * B ^ 6 := by
    have h1 : W ^ 3 ≤ (144 * (n : ℝ) ^ 4 * B ^ 2) ^ 3 := pow_le_pow_left₀ hW0.le hWB 3
    have h4 : 0 ≤ (n : ℝ) ^ 12 * B ^ 6 := by positivity
    have h5 : 4 * (144 * (n : ℝ) ^ 4 * B ^ 2) ^ 3 ≤ (144 * (n : ℝ) ^ 3) ^ 4 * B ^ 6 := by linarith
    linarith
  have hu4 : ‖uf g m z (conj z)‖ ^ 4 ≤ 4 / (z.im ^ 4 * B ^ 6) := by
    calc ‖uf g m z (conj z)‖ ^ 4 = (‖uf g m z (conj z)‖ ^ 2) ^ 2 := by ring
      _ ≤ (2 / (z.im ^ 2 * B ^ 3)) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) h2 2
      _ = 4 / (z.im ^ 4 * B ^ 6) := by rw [div_pow]; ring
  have hfin : 0 ≤ 144 * (n : ℝ) ^ 3 / z.im * maj g :=
    mul_nonneg (div_nonneg (by positivity) hy.le) (maj_nonneg g)
  apply le_of_pow_le_pow_left₀ (n := 4) (by norm_num) hfin
  calc ‖uf g m z (conj z)‖ ^ 4 ≤ 4 / (z.im ^ 4 * B ^ 6) := hu4
    _ ≤ (144 * (n : ℝ) ^ 3) ^ 4 / (z.im ^ 4 * W ^ 3) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have := mul_le_mul_of_nonneg_left hK (by positivity : (0 : ℝ) ≤ z.im ^ 4)
        linarith
    _ = (144 * (n : ℝ) ^ 3 / z.im * maj g) ^ 4 := by
        rw [show (144 * (n : ℝ) ^ 3 / z.im * maj g) ^ 4 = (144 * (n : ℝ) ^ 3) ^ 4 / z.im ^ 4 * maj g ^ 4 by ring,
          maj_pow_four, ← hWdef]
        ring

/-- The same bound for `V_g = u_g / m`. -/
theorem norm_VG_le_maj {g : Matrix (Fin 2) (Fin 2) ℤ} {n : ℤ} (hdet : g.det = n) (hn : 0 < n)
    (hc : g 1 0 ≠ 0) {m : ℕ} (hm : 2 ≤ m) {z : ℂ} (hx : |z.re| ≤ 1 / 2) (hy : 0 < z.im)
    (hyn : 4 * (n : ℝ) ≤ z.im ^ 2) :
    ‖VG g m z‖ ≤ 144 * (n : ℝ) ^ 3 / z.im * maj g := by
  have h := norm_uf_le_maj hdet hn hc hm hx hy hyn
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  unfold VG
  rw [norm_div, Complex.norm_natCast]
  calc ‖uf g m z (conj z)‖ / (m : ℝ) ≤ ‖uf g m z (conj z)‖ := div_le_self (norm_nonneg _) hm1
    _ ≤ _ := h

end Bound

end RamanujanPetersson.HypPar


