-- Prove2me | Definitions.Def_RPLib_S3_BergmanS
-- name    : RPLib_S3_BergmanS
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T12:26:02.681646+00:00
-- url     : https://prove2.me/theorems/cd6bb000-36ca-4dc9-8f86-71c8f948f84c
-- title:
--   The Eichler-Selberg trace formula in weight two: the `s`-deformed Bergman reproducing formula
-- statement:
--   The `s`-deformed Bergman reproducing formula.
--
--   For `w ∈ ℍ` put `ratio z w = Im z Im w / |z - conj w|^2` (an `SL₂(ℝ)`-invariant point-pair function with
--   values in `(0, 1/4]`). Under the Cayley map `z = cay w ζ` it is `(1 - |ζ|^2) / 4`, so the Hecke-trick factor
--   `ratio^s` is radial and the disc lemma `Bergman.integral_ball_smul` (exponent `k - 2 + s`) gives
--
--     `∫_ℍ f(z) conj((z - conj w)^(-k)) y^k ratio(z, w)^s dμ(z) = C_k(s) f(w)`,
--     `C_k(s) = 4 π i^k / ((k - 1 + s) 2^k 4^s)`  (`C_k(0) = bergmanConst k`),
--
--   for `f` holomorphic on `ℍ` with an integrable integrand. If `|f(z)| ≤ C / y^(k/2)` and `k/2 + s > 1` the
--   integrand is dominated by `C (Im w)^s kernel w (k/2 + s)`, hence integrable (`bergman_reproducing_s_of_bound`).
--   At `k = 2` this is the reproducing identity of the weight-two Hecke-trick kernel for every `s > 0`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224; F. Diamond and J. Shurman, A First Course in Modular Forms, GTM 228, Springer 2005, Chapter 5

import Mathlib
import Definitions.Def_RPLib_S3_Bergman

/-!
# S3-ES-Wt2 (O1): the `s`-deformed Bergman reproducing formula

For `w ∈ ℍ` put `ratio z w = Im z Im w / |z - conj w|^2` (an `SL₂(ℝ)`-invariant point-pair function with
values in `(0, 1/4]`). Under the Cayley map `z = cay w ζ` it is `(1 - |ζ|^2) / 4`, so the Hecke-trick factor
`ratio^s` is radial and the disc lemma `Bergman.integral_ball_smul` (exponent `k - 2 + s`) gives

  `∫_ℍ f(z) conj((z - conj w)^(-k)) y^k ratio(z, w)^s dμ(z) = C_k(s) f(w)`,
  `C_k(s) = 4 π i^k / ((k - 1 + s) 2^k 4^s)`  (`C_k(0) = bergmanConst k`),

for `f` holomorphic on `ℍ` with an integrable integrand. If `|f(z)| ≤ C / y^(k/2)` and `k/2 + s > 1` the
integrand is dominated by `C (Im w)^s kernel w (k/2 + s)`, hence integrable (`bergman_reproducing_s_of_bound`).
At `k = 2` this is the reproducing identity of the weight-two Hecke-trick kernel for every `s > 0`.
-/

open MeasureTheory Metric Set Filter Complex UpperHalfPlane
open scoped Real ComplexConjugate NNReal Manifold

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.BergmanS

open RamanujanPetersson.Bergman

/-- The invariant ratio `Im z Im w / |z - conj w|^2`. -/
def ratio (z w : ℂ) : ℝ := z.im * w.im / ‖z - conj w‖ ^ 2

lemma ratio_pos {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) : 0 < ratio z w := by
  have h : z - conj w ≠ 0 := by
    intro h
    have h' := congrArg Complex.im h
    simp only [sub_im, conj_im, sub_neg_eq_add, zero_im] at h'
    linarith
  unfold ratio
  have : 0 < ‖z - conj w‖ := norm_pos_iff.mpr h
  positivity

lemma ratio_cay {w : ℂ} (hw : 0 < w.im) {ζ : ℂ} (hζ : ζ ∈ ball (0:ℂ) 1) :
    ratio (cay w ζ) w = (1 - ‖ζ‖ ^ 2) / 4 := by
  have hA : 1 - ζ ≠ 0 := one_sub_ne_zero_of_mem_ball hζ
  have hA' : 0 < ‖1 - ζ‖ := norm_pos_iff.mpr hA
  have hn : ‖cay w ζ - conj w‖ = 2 * w.im / ‖1 - ζ‖ := by
    rw [cay_sub_conj, norm_div, Complex.sub_conj, norm_mul, norm_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]
  rw [ratio, hn, im_cay w ζ hA]
  field_simp
  ring

/-- The constant `C_k(s) = 4 π i^k / ((k - 1 + s) 2^k 4^s)`. -/
def bergmanConstS (k : ℕ) (s : ℝ) : ℂ :=
  4 * π * Complex.I ^ k / (((k:ℂ) - 1 + s) * 2 ^ k * (((4:ℝ) ^ s : ℝ) : ℂ))

lemma bergmanConstS_zero (k : ℕ) : bergmanConstS k 0 = bergmanConst k := by
  simp [bergmanConstS, bergmanConst]

lemma bergmanConstS_ne_zero {k : ℕ} {s : ℝ} (hs : 0 < (k:ℝ) - 1 + s) : bergmanConstS k s ≠ 0 := by
  unfold bergmanConstS
  have h1 : ((k:ℂ) - 1 + s) ≠ 0 := by
    have : (((k:ℝ) - 1 + s : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs.ne'
    simpa using this
  have h2 : (((4:ℝ) ^ s : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (by norm_num) s).ne'
  have h3 : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  exact div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) h3) (pow_ne_zero _ I_ne_zero))
    (mul_ne_zero (mul_ne_zero h1 (pow_ne_zero _ two_ne_zero)) h2)

/-- The `s`-reproducing integrand. -/
def integrandS (k : ℕ) (s : ℝ) (f : ℍ → ℂ) (w : ℍ) (z : ℍ) : ℂ :=
  f z * conj ((((z:ℂ) - conj (w:ℂ)) ^ k)⁻¹) * ((z.im : ℂ)) ^ k * ((ratio (z:ℂ) (w:ℂ) ^ s : ℝ) : ℂ)

/-- **`s`-reproducing formula.** For `k ≥ 2`, `k - 1 + s > 0`, `f` holomorphic on `ℍ` and `w ∈ ℍ`, if the
integrand is integrable then `∫_ℍ f(z) conj((z - conj w)^(-k)) y^k ratio(z, w)^s dμ(z) = C_k(s) f(w)`. -/
theorem bergman_reproducing_s {k : ℕ} (hk : 2 ≤ k) {s : ℝ} (hs : 0 < (k:ℝ) - 1 + s) {f : ℍ → ℂ}
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (w : ℍ) (hint : Integrable (integrandS k s f w)) :
    ∫ z : ℍ, integrandS k s f w z = bergmanConstS k s * f w := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 2 := ⟨k - 2, by omega⟩
  have hw : 0 < (w:ℂ).im := w.im_pos
  have hns : -1 < (n:ℝ) + s := by push_cast at hs; linarith
  set F : ℍ → ℂ := integrandS (n + 2) s f w with hF
  set G : ℂ → ℂ := fun ζ => f (ofComplex (cay w ζ)) / (1 - ζ) ^ (n + 2) with hG
  have hGd : DifferentiableOn ℂ G (ball 0 1) := by
    have h1 : DifferentiableOn ℂ (f ∘ ofComplex) {z : ℂ | 0 < z.im} :=
      UpperHalfPlane.mdifferentiable_iff.mp hf
    have h2 : DifferentiableOn ℂ (cay w) (ball 0 1) := fun ζ hζ =>
      (hasDerivAt_cay w (one_sub_ne_zero_of_mem_ball hζ)).differentiableAt.differentiableWithinAt
    have h3 : DifferentiableOn ℂ (fun ζ => (f ∘ ofComplex) (cay w ζ)) (ball 0 1) :=
      h1.comp h2 (fun ζ hζ => cay_im_pos hw hζ)
    exact h3.div (by fun_prop) (fun ζ hζ => pow_ne_zero _ (one_sub_ne_zero_of_mem_ball hζ))
  set t : ℝ := (4:ℝ) ^ s with ht_def
  have ht : 0 < t := Real.rpow_pos_of_pos (by norm_num) s
  set K : ℂ := 4 * (Complex.I / 2) ^ (n + 2) * ((t⁻¹ : ℝ) : ℂ) with hK
  have hpt : ∀ ζ ∈ ball (0:ℂ) 1, ‖((w:ℂ) - conj (w:ℂ)) / (1 - ζ) ^ 2‖ ^ 2 •
      (((cay w ζ).im ^ 2)⁻¹ • F (ofComplex (cay w ζ)))
      = K * ((1 - ‖ζ‖ ^ 2) ^ ((n:ℝ) + s) • G ζ) := by
    intro ζ hζ
    have hc : ((ofComplex (cay w ζ) : ℍ) : ℂ) = cay w ζ := by
      rw [ofComplex_apply_of_im_pos (cay_im_pos hw hζ)]
    have h0 := integrand_cay hw hζ n (f (ofComplex (cay w ζ)))
    have hpos : 0 < 1 - ‖ζ‖ ^ 2 := by
      have h1 : ‖ζ‖ < 1 := mem_ball_zero_iff.mp hζ
      nlinarith [norm_nonneg ζ]
    have hr : (1 - ‖ζ‖ ^ 2) ^ (n:ℝ) * ((1 - ‖ζ‖ ^ 2) / 4) ^ s = t⁻¹ * (1 - ‖ζ‖ ^ 2) ^ ((n:ℝ) + s) := by
      rw [Real.div_rpow hpos.le (by norm_num), Real.rpow_add hpos, ht_def]
      field_simp
    have hr' : (((1 - ‖ζ‖ ^ 2) ^ (n:ℝ) : ℝ) : ℂ) * ((((1 - ‖ζ‖ ^ 2) / 4) ^ s : ℝ) : ℂ)
        = ((t⁻¹ : ℝ) : ℂ) * (((1 - ‖ζ‖ ^ 2) ^ ((n:ℝ) + s) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, hr]
    simp only [hF, hG, integrandS]
    rw [← UpperHalfPlane.coe_im, hc, ratio_cay hw hζ]
    simp only [Complex.real_smul] at h0 ⊢
    rw [hK]
    linear_combination (((((1 - ‖ζ‖ ^ 2) / 4) ^ s : ℝ) : ℂ)) * h0
      + (4 * (Complex.I / 2) ^ (n + 2) * (f (ofComplex (cay w ζ)) / (1 - ζ) ^ (n + 2))) * hr'
  have hK0 : K ≠ 0 := by
    rw [hK]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ (div_ne_zero I_ne_zero two_ne_zero)))
      (ofReal_ne_zero.mpr (inv_ne_zero ht.ne'))
  have hint' : IntegrableOn (fun ζ => (1 - ‖ζ‖ ^ 2) ^ ((n:ℝ) + s) • G ζ) (ball 0 1) := by
    have h1 := (integrableOn_upper_iff_ball hw _).mp ((integrable_iff_integrableOn F).mp hint)
    have h2 := h1.congr_fun hpt measurableSet_ball
    refine IntegrableOn.congr_fun (Integrable.const_mul h2 K⁻¹) (fun ζ _ => ?_) measurableSet_ball
    rw [← mul_assoc, inv_mul_cancel₀ hK0, one_mul]
  rw [Bergman.integral_eq_setIntegral, setIntegral_upper_eq_ball hw,
    setIntegral_congr_fun measurableSet_ball hpt, integral_const_mul,
    integral_ball_smul hns hGd hint']
  have hG0 : G 0 = f w := by simp [hG, cay_zero, ofComplex_apply]
  rw [hG0, bergmanConstS, Complex.real_smul, hK]
  have hu : ((n:ℝ) + s + 1) ≠ 0 := by linarith
  have hu' : (((n:ℝ) + s + 1 : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hu
  have e1 : (((n + 2 : ℕ) : ℂ) - 1 + s) = (((n:ℝ) + s + 1 : ℝ) : ℂ) := by push_cast; ring
  have e2 : ((π / ((n:ℝ) + s + 1) : ℝ) : ℂ) = (π : ℂ) / (((n:ℝ) + s + 1 : ℝ) : ℂ) := by push_cast; ring
  have htc : ((t : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  rw [e1, e2, ← ht_def, Complex.ofReal_inv, div_pow]
  field_simp

lemma continuous_ratio_rpow (w : ℍ) (s : ℝ) : Continuous (fun z : ℍ => ratio (z:ℂ) (w:ℂ) ^ s) := by
  have hc : Continuous (fun z : ℍ => ratio (z:ℂ) (w:ℂ)) := by
    unfold ratio
    refine Continuous.div ?_ ?_ ?_
    · exact (Complex.continuous_im.comp UpperHalfPlane.continuous_coe).mul continuous_const
    · exact ((UpperHalfPlane.continuous_coe.sub continuous_const).norm).pow 2
    · intro z
      exact pow_ne_zero _ (norm_ne_zero_iff.mpr (coe_sub_conj_ne_zero z w))
  exact hc.rpow_const (fun z => Or.inl (ratio_pos z.im_pos w.im_pos).ne')

/-- **Domination.** If `|f(z)| ≤ C / y^(k/2)` then `|integrand| ≤ C (Im w)^s kernel w (k/2 + s)`. -/
lemma norm_integrandS_le {k : ℕ} {s : ℝ} {f : ℍ → ℂ} (w : ℍ) {C : ℝ}
    (hC : ∀ z : ℍ, ‖f z‖ ≤ C / z.im ^ ((k:ℝ) / 2)) (z : ℍ) :
    ‖integrandS k s f w z‖ ≤ C * w.im ^ s * kernel w ((k:ℝ) / 2 + s) z := by
  have hy : 0 < z.im := z.im_pos
  have hv : 0 < w.im := w.im_pos
  have hA : 0 < ‖(z:ℂ) - conj (w:ℂ)‖ := norm_pos_iff.mpr (coe_sub_conj_ne_zero z w)
  set A := ‖(z:ℂ) - conj (w:ℂ)‖ with hA_def
  have hY : 0 < z.im ^ ((k:ℝ) / 2) := Real.rpow_pos_of_pos hy _
  have hfz : ‖f z‖ * z.im ^ ((k:ℝ) / 2) ≤ C := (le_div_iff₀ hY).mp (hC z)
  have hrat : ratio (z:ℂ) (w:ℂ) = z.im * w.im / A ^ 2 := rfl
  have hr0 : 0 ≤ ratio (z:ℂ) (w:ℂ) ^ s := Real.rpow_nonneg (ratio_pos z.im_pos w.im_pos).le s
  have e1 : ratio (z:ℂ) (w:ℂ) ^ s = z.im ^ s * w.im ^ s / (A ^ 2) ^ s := by
    rw [hrat, Real.div_rpow (by positivity) (by positivity), Real.mul_rpow hy.le hv.le]
  have e2 : A ^ (2 * ((k:ℝ) / 2 + s)) = A ^ k * (A ^ 2) ^ s := by
    rw [show 2 * ((k:ℝ) / 2 + s) = (k:ℝ) + 2 * s by ring, Real.rpow_add hA, Real.rpow_natCast,
      Real.rpow_mul hA.le, Real.rpow_two]
  have e3 : z.im ^ k = z.im ^ ((k:ℝ) / 2) * z.im ^ ((k:ℝ) / 2) := by
    rw [← Real.rpow_add hy, ← Real.rpow_natCast]
    congr 1
    ring
  have e4 : z.im ^ ((k:ℝ) / 2 + s) = z.im ^ ((k:ℝ) / 2) * z.im ^ s := Real.rpow_add hy _ _
  have hk : kernel w ((k:ℝ) / 2 + s) z = z.im ^ ((k:ℝ) / 2 + s) / A ^ (2 * ((k:ℝ) / 2 + s)) := rfl
  have hD : 0 < A ^ k * (A ^ 2) ^ s := by positivity
  have hnorm : ‖integrandS k s f w z‖ = ‖f z‖ * (A ^ k)⁻¹ * z.im ^ k * ratio (z:ℂ) (w:ℂ) ^ s := by
    rw [integrandS, norm_mul, norm_mul, norm_mul, Complex.norm_conj, norm_inv, norm_pow, norm_pow,
      Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hy.le, Real.norm_of_nonneg hr0]
  rw [hnorm, hk, e1, e2, e3, e4]
  have hS : 0 ≤ z.im ^ ((k:ℝ) / 2) * z.im ^ s * w.im ^ s / (A ^ k * (A ^ 2) ^ s) := by positivity
  calc ‖f z‖ * (A ^ k)⁻¹ * (z.im ^ ((k:ℝ) / 2) * z.im ^ ((k:ℝ) / 2)) * (z.im ^ s * w.im ^ s / (A ^ 2) ^ s)
      = (‖f z‖ * z.im ^ ((k:ℝ) / 2)) * (z.im ^ ((k:ℝ) / 2) * z.im ^ s * w.im ^ s / (A ^ k * (A ^ 2) ^ s)) := by
        field_simp
    _ ≤ C * (z.im ^ ((k:ℝ) / 2) * z.im ^ s * w.im ^ s / (A ^ k * (A ^ 2) ^ s)) :=
        mul_le_mul_of_nonneg_right hfz hS
    _ = C * w.im ^ s * (z.im ^ ((k:ℝ) / 2) * z.im ^ s / (A ^ k * (A ^ 2) ^ s)) := by ring

/-- **Integrability for bounded weight-`k` functions**, `k/2 + s > 1`. -/
theorem integrable_integrandS_of_bound {k : ℕ} {s : ℝ} (hσ : 1 < (k:ℝ) / 2 + s) {f : ℍ → ℂ}
    (hf : Continuous f) (w : ℍ) {C : ℝ} (hC : ∀ z : ℍ, ‖f z‖ ≤ C / z.im ^ ((k:ℝ) / 2)) :
    Integrable (integrandS k s f w) := by
  refine Integrable.mono' ((integrable_kernel w hσ).const_mul (C * w.im ^ s)) ?_
    (Eventually.of_forall fun z => norm_integrandS_le w hC z)
  have h1 : Continuous (fun z : ℍ => (z : ℂ)) := UpperHalfPlane.continuous_coe
  have h2 : Continuous (fun z : ℍ => ((z.im : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp UpperHalfPlane.continuous_im
  have h3 : Continuous (fun z : ℍ => conj ((((z:ℂ) - conj (w:ℂ)) ^ k)⁻¹)) :=
    Complex.continuous_conj.comp (((h1.sub continuous_const).pow k).inv₀
      (fun z => pow_ne_zero _ (coe_sub_conj_ne_zero z w)))
  have h4 : Continuous (fun z : ℍ => ((ratio (z:ℂ) (w:ℂ) ^ s : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_ratio_rpow w s)
  exact (((hf.mul h3).mul (h2.pow k)).mul h4).aestronglyMeasurable

/-- **`s`-reproducing formula for bounded weight-`k` functions** (`k ≥ 2`, `k/2 + s > 1`; at `k = 2`: every
`s > 0`, e.g. weight-two cusp forms via `CuspFormClass.exists_bound`). -/
theorem bergman_reproducing_s_of_bound {k : ℕ} (hk : 2 ≤ k) {s : ℝ} (hσ : 1 < (k:ℝ) / 2 + s) {f : ℍ → ℂ}
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (w : ℍ) {C : ℝ}
    (hC : ∀ z : ℍ, ‖f z‖ ≤ C / z.im ^ ((k:ℝ) / 2)) :
    ∫ z : ℍ, integrandS k s f w z = bergmanConstS k s * f w := by
  have hk' : (2:ℝ) ≤ k := by exact_mod_cast hk
  exact bergman_reproducing_s hk (by linarith) hf w
    (integrable_integrandS_of_bound hσ hf.continuous w hC)

end RamanujanPetersson.BergmanS


