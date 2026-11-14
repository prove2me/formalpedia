-- Prove2me | Definitions.Def_RPLib_S3_EllipticTermA
-- name    : RPLib_S3_EllipticTermA
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-13T20:53:37.76064+00:00
-- url     : https://prove2.me/theorems/afae4534-8750-4f95-87c3-fecd1b7b7476
-- title:
--   The Eichler-Selberg trace formula, elliptic term part A: the elliptic orbital integral
-- statement:
--   The radial integral $\int_0^1 r(1-r^2)^m (A - B r^2)^{-(m+2)}\, dr = \frac{A^{-(m+1)}}{2(m+1)(A - B)}$ and the form of $\overline{Q(g; z, -\bar z)^{-k}}\, y^{k}$ in Cayley coordinates centred at the fixed point of an elliptic matrix $g$.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer: the Eichler-Selberg trace formula on $S_k(\Gamma_1(M))$ for $k \ge 3$, proved by Zagier's kernel method). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976 (with the Correction in later printings)

import Mathlib
import Definitions.Def_RPLib_S3_KernelA
import Definitions.Def_RPLib_S3_Bergman

/-!
# S3-EllCentralTerms, part A: the elliptic orbital integral 

* Part 1: the radial integral `∫_0^1 r (1-r²)^m (A - B r²)^{-(m+2)} dr = A^{-(m+1)} / (2 (m+1) (A - B))`
  (FTC with the antiderivative `((1-r²)/(A - B r²))^(m+1)`) and its disc form.
* Part 2: `phiG k g z = conj (Q(g; z, -conj z)^k)⁻¹ y^k` in Cayley coordinates centred at a fixed point of `g`.
-/

open MeasureTheory Metric Set Filter Complex UpperHalfPlane
open scoped Real ComplexConjugate NNReal Manifold

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EllTerm

open RamanujanPetersson.Bergman RamanujanPetersson.Kernel

/-! ## Part 1: radial integral -/

/-- Antiderivative `((1 - r²)/(A - B r²))^(m+1)`. -/
def radF (A B : ℂ) (m : ℕ) (r : ℝ) : ℂ := ((1 - (r : ℂ) ^ 2) / (A - B * (r : ℂ) ^ 2)) ^ (m + 1)

/-- The radial integrand `(1 - r²)^m / (A - B r²)^(m+2)`. -/
def radH (A B : ℂ) (m : ℕ) (r : ℝ) : ℂ := (1 - (r : ℂ) ^ 2) ^ m / (A - B * (r : ℂ) ^ 2) ^ (m + 2)

lemma hasDerivAt_radF {A B : ℂ} (m : ℕ) {r : ℝ} (hr : A - B * (r : ℂ) ^ 2 ≠ 0) :
    HasDerivAt (radF A B m) (-2 * ((m : ℂ) + 1) * (A - B) * ((r : ℂ) * radH A B m r)) r := by
  have hx : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 r := by
    simpa using (hasDerivAt_id r).ofReal_comp
  have hx2 : HasDerivAt (fun x : ℝ => (x : ℂ) ^ 2) (2 * (r : ℂ)) r := by
    simpa using (hasDerivAt_pow 2 (r : ℂ)).comp_ofReal
  have hN : HasDerivAt (fun x : ℝ => 1 - (x : ℂ) ^ 2) (-(2 * (r : ℂ))) r := by
    simpa using hx2.const_sub 1
  have hD : HasDerivAt (fun x : ℝ => A - B * (x : ℂ) ^ 2) (-(B * (2 * (r : ℂ)))) r := by
    simpa using (hx2.const_mul B).const_sub A
  have hq := (hasDerivAt_pow (m + 1) ((1 - (r : ℂ) ^ 2) / (A - B * (r : ℂ) ^ 2))).comp r (hN.div hD hr)
  have e : radF A B m = (fun x : ℂ => x ^ (m + 1)) ∘ (fun x : ℝ => (1 - (x : ℂ) ^ 2) / (A - B * (x : ℂ) ^ 2)) :=
    rfl
  rw [e]
  refine hq.congr_deriv ?_
  simp only [radH, Nat.add_sub_cancel]
  obtain ⟨D, hDdef⟩ : ∃ D : ℂ, D = A - B * (r : ℂ) ^ 2 := ⟨_, rfl⟩
  rw [← hDdef] at hr ⊢
  rw [div_pow]
  push_cast
  field_simp
  subst hDdef
  ring

lemma continuousOn_radH {A B : ℂ} (m : ℕ) (hAB : ∀ r : ℝ, 0 ≤ r → r ≤ 1 → A - B * (r : ℂ) ^ 2 ≠ 0) :
    ContinuousOn (fun r : ℝ => (r : ℂ) * radH A B m r) (Icc 0 1) := by
  refine ContinuousOn.mul (by fun_prop) ?_
  refine ContinuousOn.div (by fun_prop) (by fun_prop) fun r hr => pow_ne_zero _ (hAB r hr.1 hr.2)

/-- `∫_0^1 r (1-r²)^m (A - B r²)^{-(m+2)} dr = A^{-(m+1)} / (2 (m+1) (A - B))`. -/
theorem integral_radH (m : ℕ) {A B : ℂ} (hAB : ∀ r : ℝ, 0 ≤ r → r ≤ 1 → A - B * (r : ℂ) ^ 2 ≠ 0)
    (hne : A ≠ B) :
    ∫ r in (0 : ℝ)..1, (r : ℂ) * radH A B m r = (A ^ (m + 1))⁻¹ / (2 * ((m : ℂ) + 1) * (A - B)) := by
  have hA : A ≠ 0 := by simpa using hAB 0 le_rfl zero_le_one
  have hderiv : ∀ x ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (radF A B m) (-2 * ((m : ℂ) + 1) * (A - B) * ((x : ℂ) * radH A B m x)) x := by
    intro x hx
    rw [uIcc_of_le zero_le_one] at hx
    exact hasDerivAt_radF m (hAB x hx.1 hx.2)
  have hint : IntervalIntegrable (fun x : ℝ => -2 * ((m : ℂ) + 1) * (A - B) * ((x : ℂ) * radH A B m x))
      volume 0 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le zero_le_one]
    exact (continuousOn_radH m hAB).const_smul (-2 * ((m : ℂ) + 1) * (A - B)) |>.congr fun x _ => rfl
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [intervalIntegral.integral_const_mul] at h
  have h1 : radF A B m 1 = 0 := by simp [radF]
  have h0 : radF A B m 0 = (A ^ (m + 1))⁻¹ := by simp [radF, inv_pow]
  rw [h1, h0, zero_sub] at h
  have hc : -2 * ((m : ℂ) + 1) * (A - B) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (by norm_num) ?_) (sub_ne_zero.2 hne)
    exact_mod_cast Nat.succ_ne_zero m
  have hc2 : 2 * ((m : ℂ) + 1) * (A - B) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (by norm_num) ?_) (sub_ne_zero.2 hne)
    exact_mod_cast Nat.succ_ne_zero m
  rw [eq_div_iff hc2]
  linear_combination -h

/-- Volume of the unit disc, from `Bergman.integral_ball_weight` at `s = 0`. -/
lemma volume_real_ball : (volume : Measure ℂ).real (ball (0 : ℂ) 1) = π := by
  have h := integral_ball_weight (s := 0) (by norm_num)
  simp only [Real.rpow_zero, integral_const, smul_eq_mul, mul_one, zero_add, div_one] at h
  rw [measureReal_def] at h ⊢
  simpa using h

/-- Disc form: `∫_{|ζ|<1} (1-|ζ|²)^m / (A - B |ζ|²)^(m+2) = π A^{-(m+1)} / ((m+1)(A - B))`. -/
theorem integral_ball_radH (m : ℕ) {A B : ℂ}
    (hAB : ∀ r : ℝ, 0 ≤ r → r ≤ 1 → A - B * (r : ℂ) ^ 2 ≠ 0) (hne : A ≠ B) :
    ∫ ζ in ball (0 : ℂ) 1, radH A B m ‖ζ‖ = π * ((A ^ (m + 1))⁻¹ / (((m : ℂ) + 1) * (A - B))) := by
  have e1 : ∫ ζ in ball (0 : ℂ) 1, radH A B m ‖ζ‖ = ∫ ζ : ℂ, (Iio (1 : ℝ)).indicator (radH A B m) ‖ζ‖ := by
    rw [← integral_indicator measurableSet_ball]
    congr 1
    funext ζ
    by_cases h : ‖ζ‖ < 1
    · rw [indicator_of_mem (mem_ball_zero_iff.2 h), indicator_of_mem (show ‖ζ‖ ∈ Iio (1 : ℝ) from h)]
    · rw [indicator_of_notMem (fun h' => h (mem_ball_zero_iff.1 h')),
        indicator_of_notMem (show ‖ζ‖ ∉ Iio (1 : ℝ) from h)]
  rw [e1, integral_fun_norm_addHaar (volume : Measure ℂ) ((Iio (1 : ℝ)).indicator (radH A B m)),
    Complex.finrank_real_complex, volume_real_ball]
  have e2 : ∫ y in Ioi (0 : ℝ), y ^ (2 - 1) • (Iio (1 : ℝ)).indicator (radH A B m) y =
      ∫ y in (0 : ℝ)..1, (y : ℂ) * radH A B m y := by
    have e3 : ∀ y : ℝ, y ^ (2 - 1) • (Iio (1 : ℝ)).indicator (radH A B m) y =
        (Iio (1 : ℝ)).indicator (fun y => (y : ℂ) * radH A B m y) y := by
      intro y
      by_cases h : y < 1
      · rw [indicator_of_mem (show y ∈ Iio (1 : ℝ) from h), indicator_of_mem (show y ∈ Iio (1 : ℝ) from h)]
        simp [Complex.real_smul]
      · rw [indicator_of_notMem (show y ∉ Iio (1 : ℝ) from h),
          indicator_of_notMem (show y ∉ Iio (1 : ℝ) from h), smul_zero]
    simp_rw [e3]
    rw [setIntegral_indicator measurableSet_Iio, Ioi_inter_Iio, intervalIntegral.integral_of_le zero_le_one,
      integral_Ioc_eq_integral_Ioo]
  rw [e2, integral_radH m hAB hne]
  simp only [nsmul_eq_mul, Complex.real_smul]
  push_cast
  have hc : ((m : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  have hd : A - B ≠ 0 := sub_ne_zero.2 hne
  field_simp

/-! ## Part 2: the integrand in Cayley coordinates at a fixed point -/

/-- The per-matrix diagonal integrand `conj (Q(g; z, -conj z)^k)⁻¹ * y^k`. -/
def phiG (k : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (z : ℍ) : ℂ :=
  conj ((Q g (z : ℂ) (-conj (z : ℂ)) ^ k)⁻¹) * ((z.im : ℂ) ^ k)

lemma Q_neg_conj (g : Matrix (Fin 2) (Fin 2) ℤ) (z : ℂ) :
    Q g z (-conj z) = (g 0 0 : ℂ) * z + g 0 1 - conj z * ((g 1 0 : ℂ) * z + g 1 1) := by
  simp only [Q]; ring

/-- Pure algebra: with `z = α w + (1-α) conj w` and `w` a fixed point of `[[a,b],[c,d]]`,
`a z + b - conj z (c z + d) = (w - conj w)(α ᾱ λ - (1-α)(1-ᾱ) λ̄)`, `λ = c w + d`. -/
lemma Q_fix_alg (a b c d w W α A : ℂ) (hw : a * w + b = (c * w + d) * w)
    (hW : a * W + b = (c * W + d) * W) :
    a * (α * w + (1 - α) * W) + b - (A * W + (1 - A) * w) * (c * (α * w + (1 - α) * W) + d)
      = (w - W) * (α * A * (c * w + d) - (1 - α) * (1 - A) * (c * W + d)) := by
  linear_combination α * hw + (1 - α) * hW

lemma cay_eq_comb (w ζ : ℂ) (hA : 1 - ζ ≠ 0) :
    cay w ζ = (1 - ζ)⁻¹ * w + (1 - (1 - ζ)⁻¹) * conj w := by
  simp only [cay]; field_simp; ring

lemma conj_cay_eq_comb (w ζ : ℂ) (hA : 1 - ζ ≠ 0) :
    conj (cay w ζ) = conj ((1 - ζ)⁻¹) * conj w + (1 - conj ((1 - ζ)⁻¹)) * w := by
  have hA' : 1 - conj ζ ≠ 0 := by
    intro h; apply hA; simpa using congrArg conj h
  simp only [cay, map_add, map_div₀, map_sub, map_one, conj_conj, map_inv₀]
  field_simp
  ring

/-- `Q(g; z, -conj z)` at `z = cay w ζ`, `w` a fixed point of `g`:
`Q * |1-ζ|² = (w - conj w)(λ - λ̄ |ζ|²)` with `λ = c w + d`. -/
theorem Q_cay (g : Matrix (Fin 2) (Fin 2) ℤ) {w : ℂ}
    (hfix : (g 0 0 : ℂ) * w + g 0 1 = ((g 1 0 : ℂ) * w + g 1 1) * w) {ζ : ℂ} (hA : 1 - ζ ≠ 0) :
    Q g (cay w ζ) (-conj (cay w ζ)) * ((‖1 - ζ‖ ^ 2 : ℝ) : ℂ) =
      (w - conj w) * (((g 1 0 : ℂ) * w + g 1 1) - ((g 1 0 : ℂ) * conj w + g 1 1) * ((‖ζ‖ ^ 2 : ℝ) : ℂ)) := by
  have hW : (g 0 0 : ℂ) * conj w + g 0 1 = ((g 1 0 : ℂ) * conj w + g 1 1) * conj w := by
    have := congrArg conj hfix
    simpa [map_add, map_mul, map_intCast] using this
  rw [Q_neg_conj, conj_cay_eq_comb w ζ hA, cay_eq_comb w ζ hA,
    Q_fix_alg _ _ _ _ w (conj w) _ _ hfix hW]
  have hn1 : ((‖1 - ζ‖ ^ 2 : ℝ) : ℂ) = (1 - ζ) * conj (1 - ζ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hn2 : ((‖ζ‖ ^ 2 : ℝ) : ℂ) = ζ * conj ζ := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hA' : conj (1 - ζ) ≠ 0 := (map_ne_zero _).2 hA
  rw [hn1, hn2]
  simp only [map_inv₀, map_sub, map_one] at *
  field_simp
  ring

/-! ## Part 3: the orbital integral at a fixed point -/

/-- `λ = c w + d`. -/
abbrev lamOf (g : Matrix (Fin 2) (Fin 2) ℤ) (w : ℂ) : ℂ := (g 1 0 : ℂ) * w + g 1 1

lemma conj_lamOf (g : Matrix (Fin 2) (Fin 2) ℤ) (w : ℂ) :
    (g 1 0 : ℂ) * conj w + g 1 1 = conj (lamOf g w) := by
  simp [lamOf, map_add, map_mul, map_intCast]

/-- The orbital integral value `4 (-2i)^{-(m+2)} π conj λ^{-(m+1)} / ((m+1)(conj λ - λ))`. -/
def orbI (m : ℕ) (lam : ℂ) : ℂ :=
  4 * ((-2 * Complex.I) ^ (m + 2))⁻¹ * (π * ((conj lam ^ (m + 1))⁻¹ / (((m : ℂ) + 1) * (conj lam - lam))))

lemma lam_hAB (g : Matrix (Fin 2) (Fin 2) ℤ) {w : ℂ} (hw : 0 < w.im) (hc : g 1 0 ≠ 0) :
    ∀ r : ℝ, 0 ≤ r → r ≤ 1 → conj (lamOf g w) - lamOf g w * (r : ℂ) ^ 2 ≠ 0 := by
  intro r _ _ h
  have him : (conj (lamOf g w) - lamOf g w * (r : ℂ) ^ 2).im = -((g 1 0 : ℝ) * w.im * (1 + r ^ 2)) := by
    simp [lamOf, Complex.mul_im, Complex.mul_re, pow_two]
    ring
  rw [h, Complex.zero_im] at him
  have hc' : (g 1 0 : ℝ) ≠ 0 := by exact_mod_cast hc
  have : (g 1 0 : ℝ) * w.im * (1 + r ^ 2) ≠ 0 := by positivity
  exact this (by linarith)

lemma lam_ne (g : Matrix (Fin 2) (Fin 2) ℤ) {w : ℂ} (hw : 0 < w.im) (hc : g 1 0 ≠ 0) :
    conj (lamOf g w) ≠ lamOf g w := by
  intro h
  apply lam_hAB g hw hc 1 zero_le_one le_rfl
  rw [h]; simp

lemma phiG_eq_div (k : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (z : ℍ) :
    phiG k g z = ((z.im : ℂ) / conj (Q g (z : ℂ) (-conj (z : ℂ)))) ^ k := by
  rw [phiG, map_inv₀, map_pow, div_pow]; ring

/-- Pure algebra behind `phiG_disc`. -/
lemma disc_alg (m : ℕ) {v N R : ℝ} (hv : 0 < v) (hN : 0 < N) (hR : R < 1) {L L' : ℂ}
    (hD : L' - L * (R : ℂ) ≠ 0) :
    ((4 * v ^ 2 / N ^ 2 : ℝ) : ℂ) * ((((v * (1 - R) / N) ^ 2 : ℝ) : ℂ)⁻¹ *
      ((((v * (1 - R) / N : ℝ) : ℂ) / ((-2 * Complex.I * v) * (L' - L * R) / N)) ^ (m + 2)))
    = 4 * ((-2 * Complex.I) ^ (m + 2))⁻¹ * ((1 - (R : ℂ)) ^ m / (L' - L * R) ^ (m + 2)) := by
  have hv' : (v : ℂ) ≠ 0 := by exact_mod_cast hv.ne'
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have h1R : (1 : ℂ) - R ≠ 0 := by
    have : (1 : ℝ) - R ≠ 0 := (sub_pos.2 hR).ne'
    exact_mod_cast this
  have hP : (-2 * Complex.I) ≠ 0 := by simp [Complex.I_ne_zero]
  have e : ((v * (1 - R) / N : ℝ) : ℂ) / ((-2 * Complex.I * v) * (L' - L * R) / N)
      = (1 - R) / ((-2 * Complex.I) * (L' - L * R)) := by
    push_cast
    field_simp
  rw [e, ← mul_assoc]
  have h1 : ((4 * v ^ 2 / N ^ 2 : ℝ) : ℂ) * ((((v * (1 - R) / N) ^ 2 : ℝ) : ℂ))⁻¹ = 4 / (1 - (R : ℂ)) ^ 2 := by
    push_cast
    field_simp
  rw [h1, div_pow, mul_pow, pow_add (1 - (R : ℂ)) m 2]
  have hP2 : (-2 * Complex.I) ^ (m + 2) ≠ 0 := pow_ne_zero _ hP
  have hD2 : (L' - L * (R : ℂ)) ^ (m + 2) ≠ 0 := pow_ne_zero _ hD
  generalize (-2 * Complex.I) ^ (m + 2) = P at hP2 ⊢
  generalize (L' - L * (R : ℂ)) ^ (m + 2) = D at hD2 ⊢
  generalize (1 - (R : ℂ)) ^ m = Y
  field_simp

/-- The integrand on the disc, pointwise. -/
theorem phiG_disc (g : Matrix (Fin 2) (Fin 2) ℤ) {w : ℂ} (hw : 0 < w.im)
    (hfix : (g 0 0 : ℂ) * w + g 0 1 = lamOf g w * w) (hc : g 1 0 ≠ 0) (m : ℕ)
    {ζ : ℂ} (hζ : ζ ∈ ball (0 : ℂ) 1) :
    ‖(w - conj w) / (1 - ζ) ^ 2‖ ^ 2 • (((cay w ζ).im ^ 2)⁻¹ • phiG (m + 2) g (ofComplex (cay w ζ)))
      = 4 * ((-2 * Complex.I) ^ (m + 2))⁻¹ * radH (conj (lamOf g w)) (lamOf g w) m ‖ζ‖ := by
  have hA := one_sub_ne_zero_of_mem_ball hζ
  have hz : 0 < (cay w ζ).im := cay_im_pos hw hζ
  have h1 : ‖ζ‖ < 1 := mem_ball_zero_iff.mp hζ
  have hR : ‖ζ‖ ^ 2 < 1 := by nlinarith [norm_nonneg ζ]
  have hN0 : 0 < ‖1 - ζ‖ := norm_pos_iff.mpr hA
  have hD : conj (lamOf g w) - lamOf g w * (‖ζ‖ : ℂ) ^ 2 ≠ 0 :=
    lam_hAB g hw hc ‖ζ‖ (norm_nonneg _) h1.le
  have hQ := Q_cay g hfix hA
  rw [conj_lamOf] at hQ
  have hQv : Q g (cay w ζ) (-conj (cay w ζ)) =
      (w - conj w) * (lamOf g w - conj (lamOf g w) * ((‖ζ‖ ^ 2 : ℝ) : ℂ)) / ((‖1 - ζ‖ ^ 2 : ℝ) : ℂ) := by
    rw [eq_div_iff (by exact_mod_cast (pow_pos hN0 2).ne')]
    exact hQ
  have e : conj w - w = -2 * Complex.I * (w.im : ℂ) := by
    rw [← neg_sub, Complex.sub_conj]; push_cast; ring
  have hcQ : conj (Q g (cay w ζ) (-conj (cay w ζ))) =
      (-2 * Complex.I * (w.im : ℂ)) * (conj (lamOf g w) - lamOf g w * ((‖ζ‖ ^ 2 : ℝ) : ℂ)) /
        ((‖1 - ζ‖ ^ 2 : ℝ) : ℂ) := by
    rw [hQv]
    simp only [map_div₀, map_mul, map_sub, conj_conj, Complex.conj_ofReal]
    rw [e]
  have e1 : ((ofComplex (cay w ζ) : ℍ) : ℂ) = cay w ζ := by
    rw [ofComplex_apply_of_im_pos hz]
  have e2 : (ofComplex (cay w ζ)).im = (cay w ζ).im := by
    rw [ofComplex_apply_of_im_pos hz]; rfl
  have hD' : conj (lamOf g w) - lamOf g w * ((‖ζ‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by push_cast; exact hD
  have key := disc_alg m hw (pow_pos hN0 2) hR hD'
  rw [phiG_eq_div, e1, e2, hcQ, im_cay w ζ hA, norm_cayDeriv_sq hw, Complex.real_smul, Complex.real_smul,
    radH]
  push_cast at key ⊢
  linear_combination key

/-- **Orbital integral** of `phiG` at a matrix with a fixed point `w ∈ ℍ` and `c ≠ 0`. -/
theorem integral_phiG (g : Matrix (Fin 2) (Fin 2) ℤ) {w : ℂ} (hw : 0 < w.im)
    (hfix : (g 0 0 : ℂ) * w + g 0 1 = lamOf g w * w) (hc : g 1 0 ≠ 0) (m : ℕ) :
    ∫ z : ℍ, phiG (m + 2) g z = orbI m (lamOf g w) := by
  rw [integral_eq_setIntegral, setIntegral_upper_eq_ball hw,
    setIntegral_congr_fun measurableSet_ball (fun ζ hζ => phiG_disc g hw hfix hc m hζ),
    integral_const_mul, integral_ball_radH m (lam_hAB g hw hc) (lam_ne g hw hc)]
  rfl

theorem integrable_phiG (g : Matrix (Fin 2) (Fin 2) ℤ) {w : ℂ} (hw : 0 < w.im)
    (hfix : (g 0 0 : ℂ) * w + g 0 1 = lamOf g w * w) (hc : g 1 0 ≠ 0) (m : ℕ) :
    Integrable (phiG (m + 2) g) := by
  have hAB := lam_hAB g hw hc
  rw [integrable_iff_integrableOn, integrableOn_upper_iff_ball hw]
  refine IntegrableOn.congr_fun ?_ (fun ζ hζ => (phiG_disc g hw hfix hc m hζ).symm) measurableSet_ball
  refine Integrable.const_mul ?_ _
  refine (ContinuousOn.integrableOn_compact (isCompact_closedBall 0 1) ?_).mono_set ball_subset_closedBall
  simp only [radH]
  refine ContinuousOn.div (by fun_prop) (by fun_prop) fun ζ hζ => pow_ne_zero _ ?_
  exact hAB ‖ζ‖ (norm_nonneg _) (mem_closedBall_zero_iff.1 hζ)

/-! ## Part 4: the fixed point of an elliptic integer matrix -/

/-- `s = √(4n - t²)`. -/
def ellS (t n : ℤ) : ℝ := Real.sqrt (4 * n - t ^ 2)

/-- `ρ = (t + i s)/2`, the root of `X² - tX + n` in the upper half plane. -/
def ellRho (t n : ℤ) : ℂ := ((t : ℂ) + Complex.I * (ellS t n : ℂ)) / 2

lemma ellS_sq {t n : ℤ} (h : t ^ 2 ≤ 4 * n) : (ellS t n : ℂ) ^ 2 = 4 * n - t ^ 2 := by
  have h' : (0 : ℝ) ≤ 4 * n - t ^ 2 := by
    have : ((t ^ 2 : ℤ) : ℝ) ≤ ((4 * n : ℤ) : ℝ) := by exact_mod_cast h
    push_cast at this; linarith
  have : ellS t n ^ 2 = 4 * n - t ^ 2 := Real.sq_sqrt h'
  exact_mod_cast this

lemma ellS_pos {t n : ℤ} (h : t ^ 2 < 4 * n) : 0 < ellS t n := by
  apply Real.sqrt_pos.2
  have : ((t ^ 2 : ℤ) : ℝ) < ((4 * n : ℤ) : ℝ) := by exact_mod_cast h
  push_cast at this; linarith

lemma ellRho_root {t n : ℤ} (h : t ^ 2 ≤ 4 * n) : ellRho t n ^ 2 - t * ellRho t n + n = 0 := by
  simp only [ellRho]
  linear_combination (-1 / 4 : ℂ) * ellS_sq h + ((ellS t n : ℂ) ^ 2 / 4) * I_sq

lemma conj_ellRho_root {t n : ℤ} (h : t ^ 2 ≤ 4 * n) :
    conj (ellRho t n) ^ 2 - t * conj (ellRho t n) + n = 0 := by
  have := congrArg conj (ellRho_root h)
  simpa [map_add, map_sub, map_mul, map_pow, map_intCast] using this

lemma ellRho_im (t n : ℤ) : (ellRho t n).im = ellS t n / 2 := by
  simp [ellRho]

/-- `λ₀ = ρ` if `c > 0`, `conj ρ` if `c < 0`. -/
def sgnRho (g : Matrix (Fin 2) (Fin 2) ℤ) : ℂ :=
  if 0 < g 1 0 then ellRho (g 0 0 + g 1 1) g.det else conj (ellRho (g 0 0 + g 1 1) g.det)

/-- The fixed point `(λ₀ - d)/c` of an elliptic `g`. -/
def fixPt (g : Matrix (Fin 2) (Fin 2) ℤ) : ℂ := (sgnRho g - g 1 1) / g 1 0

lemma lamOf_fixPt (g : Matrix (Fin 2) (Fin 2) ℤ) (hc : g 1 0 ≠ 0) : lamOf g (fixPt g) = sgnRho g := by
  have hc' : (g 1 0 : ℂ) ≠ 0 := by exact_mod_cast hc
  simp only [lamOf, fixPt]
  field_simp
  ring

lemma sgnRho_root (g : Matrix (Fin 2) (Fin 2) ℤ) (h : (g 0 0 + g 1 1) ^ 2 ≤ 4 * g.det) :
    sgnRho g ^ 2 - ((g 0 0 : ℂ) + g 1 1) * sgnRho g + ((g 0 0 : ℂ) * g 1 1 - g 0 1 * g 1 0) = 0 := by
  have hd : ((g.det : ℤ) : ℂ) = (g 0 0 : ℂ) * g 1 1 - g 0 1 * g 1 0 := by
    rw [Matrix.det_fin_two]; push_cast; ring
  unfold sgnRho
  split_ifs
  · have := ellRho_root h
    rw [hd] at this; push_cast at this; exact this
  · have := conj_ellRho_root h
    rw [hd] at this; push_cast at this; exact this

lemma fixPt_fix (g : Matrix (Fin 2) (Fin 2) ℤ) (hc : g 1 0 ≠ 0) (h : (g 0 0 + g 1 1) ^ 2 ≤ 4 * g.det) :
    (g 0 0 : ℂ) * fixPt g + g 0 1 = lamOf g (fixPt g) * fixPt g := by
  have hc' : (g 1 0 : ℂ) ≠ 0 := by exact_mod_cast hc
  have hr := sgnRho_root g h
  rw [lamOf_fixPt g hc]
  simp only [fixPt]
  rw [div_eq_mul_inv]
  have hci : (g 1 0 : ℂ) * (g 1 0 : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hc'
  linear_combination (-(g 1 0 : ℂ)⁻¹) * hr - (g 0 1 : ℂ) * hci

lemma sgnRho_im (g : Matrix (Fin 2) (Fin 2) ℤ) :
    (sgnRho g).im = if 0 < g 1 0 then ellS (g 0 0 + g 1 1) g.det / 2
      else -(ellS (g 0 0 + g 1 1) g.det / 2) := by
  unfold sgnRho
  split_ifs <;> simp [ellRho_im]

lemma fixPt_im_pos (g : Matrix (Fin 2) (Fin 2) ℤ) (hc : g 1 0 ≠ 0)
    (h : (g 0 0 + g 1 1) ^ 2 < 4 * g.det) : 0 < (fixPt g).im := by
  have hl := congrArg Complex.im (lamOf_fixPt g hc)
  simp only [lamOf, Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im, zero_mul,
    add_zero] at hl
  rw [sgnRho_im] at hl
  have hs := ellS_pos h
  split_ifs at hl with hpos
  · have hp : (0 : ℝ) < g 1 0 := by exact_mod_cast hpos
    nlinarith
  · have hp : (g 1 0 : ℝ) < 0 := by
      have : g 1 0 < 0 := lt_of_le_of_ne (not_lt.1 hpos) hc
      exact_mod_cast this
    nlinarith

/-- An elliptic integer matrix (`t² < 4 det`) has `c ≠ 0`. -/
lemma ell_c_ne_zero (g : Matrix (Fin 2) (Fin 2) ℤ) (h : (g 0 0 + g 1 1) ^ 2 < 4 * g.det) : g 1 0 ≠ 0 := by
  intro hc
  rw [Matrix.det_fin_two, hc] at h
  nlinarith [sq_nonneg (g 0 0 - g 1 1)]

/-- **Elliptic orbital integral**: `∫_ℍ phiG = orbI m λ₀`, `λ₀ = ρ` (`c > 0`) or `conj ρ` (`c < 0`). -/
theorem integral_phiG_ell (g : Matrix (Fin 2) (Fin 2) ℤ) (h : (g 0 0 + g 1 1) ^ 2 < 4 * g.det) (m : ℕ) :
    ∫ z : ℍ, phiG (m + 2) g z = orbI m (sgnRho g) := by
  have hc := ell_c_ne_zero g h
  rw [integral_phiG g (fixPt_im_pos g hc h) (fixPt_fix g hc h.le) hc m, lamOf_fixPt g hc]

theorem integrable_phiG_ell (g : Matrix (Fin 2) (Fin 2) ℤ) (h : (g 0 0 + g 1 1) ^ 2 < 4 * g.det) (m : ℕ) :
    Integrable (phiG (m + 2) g) := by
  have hc := ell_c_ne_zero g h
  exact integrable_phiG g (fixPt_im_pos g hc h) (fixPt_fix g hc h.le) hc m

end RamanujanPetersson.EllTerm


