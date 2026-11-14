-- Prove2me | Definitions.Def_RPLib_S3_EllipticTermD
-- name    : RPLib_S3_EllipticTermD
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-13T21:08:38.823541+00:00
-- url     : https://prove2.me/theorems/c244e9c4-33f4-469f-8242-94d80e4a8985
-- title:
--   The Eichler-Selberg trace formula, elliptic term part D: volume and the scalar term
-- statement:
--   The hyperbolic area of the standard fundamental domain is $\pi/3$, so that of $\Gamma \backslash \mathbb{H}$ is $[SL_2(\mathbb{Z}) : \pm\Gamma]\,\pi/3$; the scalar matrices contribute $[\sqrt{n} \in \mathbb{N}]\, \frac{k-1}{12}\, n^{k/2 - 1}\, ([\sqrt n \delta = 1] + (-1)^k [\sqrt n \delta = -1])$ times the index.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer: the Eichler-Selberg trace formula on $S_k(\Gamma_1(M))$ for $k \ge 3$, proved by Zagier's kernel method). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976 (with the Correction in later printings); F. Diamond and J. Shurman, A First Course in Modular Forms, GTM 228, Springer 2005, doi:10.1007/978-0-387-27226-9, Section 2.3

import Mathlib
import Definitions.Def_RPLib_S3_EllipticTermC

/-!
# S3-EllCentralTerms, part D: the volume of the fundamental domain and the scalar term

* `volume_fd`: `vol 𝒟 = π / 3` for the hyperbolic measure on `ℍ`; `volume_real_fdom`:
  `vol (fdom Γ) = [SL₂(ℤ) : ±Γ] π / 3`.
* `scalPart k M n δ' z`: the scalar part `Σ'_{g ∈ Δ, g = a I} φ_g(z)` of the kernel diagonal (constant in `z`).
* `scal_trace_term`: `n^{k-1} B_k⁻¹ ∫_{Γ₁(M)\ℍ} scalPart = [SL₂(ℤ) : ±Γ₁(M)] · scalTrace M k n δ`, where
  `scalTrace = [√n ∈ ℕ] (k-1)/12 √n^{k-2} ([√n δ = 1] + (-1)^k [√n δ = -1])`.
-/

open MeasureTheory Set Filter Complex UpperHalfPlane ModularGroup CongruenceSubgroup
open scoped Real ENNReal NNReal Modular ComplexConjugate MatrixGroups

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EllTerm

open RamanujanPetersson.Bergman RamanujanPetersson.Kernel RP.FundDomain RP.Petersson

/-! ## Part 1: `vol 𝒟 = π / 3` -/

/-- `∫_a^∞ y⁻² dy = 1 / a`. -/
lemma lintegral_Ici_inv_sq {a : ℝ} (ha : 0 < a) :
    ∫⁻ y in Ici a, (((1 / ‖y‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (1 / a) := by
  rw [← Measure.restrict_congr_set Ioi_ae_eq_Ici]
  have hcongr : EqOn (fun y : ℝ => (((1 / ‖y‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞))
      (fun y => ENNReal.ofReal (y ^ (-2 : ℝ))) (Ioi a) := by
    intro y hy
    have hy' : 0 < y := ha.trans hy
    simp only
    rw [Real.rpow_neg hy'.le, Real.rpow_two, ← ENNReal.ofReal_coe_nnreal]
    congr 1
    rw [NNReal.coe_pow, NNReal.coe_div, NNReal.coe_one, coe_nnnorm, Real.norm_eq_abs, abs_of_pos hy',
      one_div, inv_pow]
  rw [setLIntegral_congr_fun measurableSet_Ioi hcongr]
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · rw [integral_Ioi_rpow_of_lt (by norm_num) ha, show ((-2 : ℝ) + 1) = -1 by norm_num,
      Real.rpow_neg_one]
    ring_nf
  · exact integrableOn_Ioi_rpow_of_lt (by norm_num) ha
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact Real.rpow_nonneg (ha.trans hy).le _

lemma arcsin_half : Real.arcsin (1 / 2) = π / 6 :=
  Real.arcsin_eq_of_sin_eq Real.sin_pi_div_six
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩

lemma continuousOn_inv_sqrt :
    ContinuousOn (fun x : ℝ => 1 / √(1 - x ^ 2)) (Icc (-(1 / 2 : ℝ)) (1 / 2)) := by
  apply ContinuousOn.div continuousOn_const
  · exact (by fun_prop : Continuous fun x : ℝ => √(1 - x ^ 2)).continuousOn
  · intro x hx
    rw [Real.sqrt_ne_zero']
    nlinarith [hx.1, hx.2]

/-- `∫_{-1/2}^{1/2} (1 - x²)^{-1/2} dx = π / 3`. -/
lemma integral_inv_sqrt :
    ∫ x in (-(1 / 2 : ℝ))..(1 / 2), 1 / √(1 - x ^ 2) = π / 3 := by
  have hle : (-(1 / 2 : ℝ)) ≤ 1 / 2 := by norm_num
  have hd : ∀ x ∈ uIcc (-(1 / 2 : ℝ)) (1 / 2), HasDerivAt Real.arcsin (1 / √(1 - x ^ 2)) x := by
    intro x hx
    rw [uIcc_of_le hle] at hx
    exact Real.hasDerivAt_arcsin (ne_of_gt (by linarith [hx.1])) (ne_of_lt (by linarith [hx.2]))
  have hint : IntervalIntegrable (fun x : ℝ => 1 / √(1 - x ^ 2)) volume (-(1 / 2 : ℝ)) (1 / 2) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hle]
    exact continuousOn_inv_sqrt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint, Real.arcsin_neg, arcsin_half]
  ring

/-- **Obligation 4.** The hyperbolic volume of the fundamental domain `𝒟` is `π / 3`. -/
theorem volume_fd : volume 𝒟 = ENNReal.ofReal (π / 3) := by
  rw [volume_eq_lintegral]
  set R : Set (ℝ × ℝ) := {p | p.1 ∈ Icc (-(1 / 2 : ℝ)) (1 / 2) ∧ √(1 - p.1 ^ 2) ≤ p.2} with hR
  have hR' : (UpperHalfPlane.coe '' 𝒟) = Complex.measurableEquivRealProd ⁻¹' R := by
    ext w
    simp only [mem_image, mem_preimage, Complex.measurableEquivRealProd_apply, hR, mem_ofPred_eq,
      mem_Icc]
    constructor
    · rintro ⟨z, hz, rfl⟩
      have h1 : 1 ≤ Complex.normSq (z : ℂ) := hz.1
      have h2 : |z.re| ≤ (1 : ℝ) / 2 := hz.2
      rw [Complex.normSq_apply] at h1
      have him : 0 < (z : ℂ).im := z.im_pos
      refine ⟨abs_le.1 h2, ?_⟩
      rw [Real.sqrt_le_iff]
      exact ⟨him.le, by nlinarith⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      have hs : 0 < √(1 - w.re ^ 2) := Real.sqrt_pos.2 (by nlinarith)
      have hpos : 0 < w.im := lt_of_lt_of_le hs h3
      have h4 := (Real.sqrt_le_iff.1 h3).2
      refine ⟨⟨w, hpos⟩, ⟨?_, ?_⟩, rfl⟩
      · change 1 ≤ Complex.normSq w
        rw [Complex.normSq_apply]
        nlinarith
      · change |w.re| ≤ (1 : ℝ) / 2
        exact abs_le.2 ⟨h1, h2⟩
  have hRm : MeasurableSet R :=
    (measurable_fst measurableSet_Icc).inter
      (measurableSet_le (by fun_prop : Continuous fun p : ℝ × ℝ => √(1 - p.1 ^ 2)).measurable
        measurable_snd)
  rw [hR']
  have key := Complex.volume_preserving_equiv_real_prod.setLIntegral_comp_preimage_emb
    Complex.measurableEquivRealProd.measurableEmbedding
    (fun p : ℝ × ℝ => (((1 / ‖p.2‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞)) R
  simp only [Complex.measurableEquivRealProd_apply] at key
  rw [key, Measure.volume_eq_prod, ← lintegral_indicator hRm,
    lintegral_prod _ ((by fun_prop : Measurable fun p : ℝ × ℝ =>
      (((1 / ‖p.2‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞)).indicator hRm).aemeasurable]
  have hin : ∀ x : ℝ, ∫⁻ y, R.indicator (fun p : ℝ × ℝ => (((1 / ‖p.2‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞)) (x, y) =
      (Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator (fun x => ENNReal.ofReal (1 / √(1 - x ^ 2))) x := by
    intro x
    by_cases hx : x ∈ Icc (-(1 / 2 : ℝ)) (1 / 2)
    · rw [indicator_of_mem hx]
      have hfun : (fun y => R.indicator (fun p : ℝ × ℝ => (((1 / ‖p.2‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞)) (x, y)) =
          (Ici (√(1 - x ^ 2))).indicator (fun y : ℝ => (((1 / ‖y‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞)) := by
        funext y
        simp only [indicator_apply, hR, mem_ofPred_eq, mem_Ici, hx, true_and]
      rw [hfun, lintegral_indicator measurableSet_Ici,
        lintegral_Ici_inv_sq (Real.sqrt_pos.2 (by nlinarith [hx.1, hx.2]))]
    · rw [indicator_of_notMem hx]
      have hfun : (fun y => R.indicator (fun p : ℝ × ℝ => (((1 / ‖p.2‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞)) (x, y)) =
          fun _ => 0 := by
        funext y
        exact indicator_of_notMem (fun h => hx h.1) _
      rw [hfun, lintegral_zero]
  rw [lintegral_congr hin, lintegral_indicator measurableSet_Icc, ← ofReal_integral_eq_lintegral_ofReal]
  · rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num), integral_inv_sqrt]
  · exact continuousOn_inv_sqrt.integrableOn_Icc
  · filter_upwards with x
    positivity

theorem volume_real_fd : volume.real 𝒟 = π / 3 := by
  rw [measureReal_def, volume_fd, ENNReal.toReal_ofReal (by positivity)]

/-- `vol (fdom Γ) = [SL₂(ℤ) : ±Γ] · π / 3`. -/
theorem volume_real_fdom (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] :
    volume.real (fdom Γ) = ((pmSL Γ).index : ℝ) * (π / 3) := by
  have h := setIntegral_iUnion_inv_smul_fd_eq_index_smul Γ Quotient.out Quotient.out_eq
    (f := fun _ : ℍ => (1 : ℝ)) (fun _ _ => rfl) (integrableOn_const volume_fd_lt_top.ne)
  rw [setIntegral_const, setIntegral_const, smul_eq_mul, smul_eq_mul, mul_one, mul_one, volume_real_fd,
    nsmul_eq_mul] at h
  exact h

/-! ## Part 2: the scalar term -/

/-- The scalar matrix `a I`. -/
def scalM (a : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![a, 0; 0, a]

@[simp] lemma scalM_00 (a : ℤ) : scalM a 0 0 = a := rfl
@[simp] lemma scalM_01 (a : ℤ) : scalM a 0 1 = 0 := rfl
@[simp] lemma scalM_10 (a : ℤ) : scalM a 1 0 = 0 := rfl
@[simp] lemma scalM_11 (a : ℤ) : scalM a 1 1 = a := rfl

lemma scalM_det (a : ℤ) : (scalM a).det = a * a := by
  rw [Matrix.det_fin_two]; simp

lemma mem_DeltaSet_scalM {M : ℕ} {n : ℤ} {δ' : ZMod M} (a : ℤ) :
    scalM a ∈ DeltaSet M n δ' ↔ a * a = n ∧ ((a : ℤ) : ZMod M) = δ' := by
  rw [mem_DeltaSet, scalM_det, scalM_10, scalM_00]
  simp

lemma eq_scalM {g : Matrix (Fin 2) (Fin 2) ℤ} (h10 : g 1 0 = 0) (h01 : g 0 1 = 0) (hd : g 0 0 = g 1 1) :
    g = scalM (g 0 0) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [scalM, h10, h01, hd]

/-- `φ_{aI}(z) = (-2 i a)^{-k}`, a constant. -/
lemma phiG_scalM (k : ℕ) {a : ℤ} (ha : a ≠ 0) (z : ℍ) :
    phiG k (scalM a) z = ((-2 * Complex.I * (a : ℂ)) ^ k)⁻¹ := by
  have hy : ((z.im : ℝ) : ℂ) ≠ 0 := by exact_mod_cast z.im_pos.ne'
  have hsub : (z : ℂ) - conj (z : ℂ) = 2 * (z.im : ℂ) * Complex.I := by
    rw [Complex.sub_conj, UpperHalfPlane.coe_im, Complex.ofReal_mul, Complex.ofReal_ofNat]
  have hQ : conj (Q (scalM a) (z : ℂ) (-conj (z : ℂ))) = (-2 * Complex.I * (a : ℂ)) * (z.im : ℂ) := by
    rw [Q_neg_conj]
    simp only [scalM_00, scalM_01, scalM_10, scalM_11, Int.cast_zero, zero_mul, zero_add, add_zero,
      map_sub, map_mul, Complex.conj_conj, map_intCast]
    linear_combination (-(a : ℂ)) * hsub
  rw [phiG_eq_div, hQ, ← inv_pow]
  congr 1
  rw [mul_comm (-2 * Complex.I * (a : ℂ)), div_mul_eq_div_div, div_self hy, one_div]

/-- The scalar part `Σ'_{g ∈ Δ, g = aI} φ_g(z)` of the kernel diagonal. -/
def scalPart (k M : ℕ) (n : ℤ) (δ' : ZMod M) (z : ℍ) : ℂ :=
  ∑' g : DeltaSet M n δ', if (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0 ∧ (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = 0 ∧
    (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 then phiG k g z else 0

/-- The summand of `aI`. -/
def scalTerm (k M : ℕ) (n : ℤ) (δ' : ZMod M) (a : ℤ) : ℂ :=
  if a * a = n ∧ ((a : ℤ) : ZMod M) = δ' then ((-2 * Complex.I * (a : ℂ)) ^ k)⁻¹ else 0

/-- The (constant) value of the scalar part. -/
def scalVal (k M n : ℕ) (δ' : ZMod M) : ℂ :=
  scalTerm k M n δ' (Nat.sqrt n : ℤ) + scalTerm k M n δ' (-(Nat.sqrt n : ℤ))

theorem scalPart_eq (k M : ℕ) (δ' : ZMod M) {n : ℕ} (hn : 0 < n) (z : ℍ) :
    scalPart k M n δ' z = scalVal k M n δ' := by
  set s : ℤ := (Nat.sqrt n : ℤ) with hs
  have hs0 : s ≠ 0 := by
    rw [hs]; exact_mod_cast (Nat.sqrt_pos.2 hn).ne'
  have hne : scalM s ≠ scalM (-s) := by
    intro h
    have := congrFun (congrFun h 0) 0
    simp only [scalM_00] at this
    omega
  set F : Matrix (Fin 2) (Fin 2) ℤ → ℂ := fun g =>
    if g 1 0 = 0 ∧ g 0 1 = 0 ∧ g 0 0 = g 1 1 then phiG k g z else 0 with hF
  have hmem : ∀ g : Matrix (Fin 2) (Fin 2) ℤ, g ∈ DeltaSet M n δ' →
      (g 1 0 = 0 ∧ g 0 1 = 0 ∧ g 0 0 = g 1 1) → g = scalM s ∨ g = scalM (-s) := by
    intro g hg hP
    obtain ⟨h10, h01, hd⟩ := hP
    have hgs := eq_scalM h10 h01 hd
    rw [hgs, mem_DeltaSet_scalM] at hg
    have habs : (g 0 0).natAbs * (g 0 0).natAbs = n := by
      simpa [Int.natAbs_mul] using congrArg Int.natAbs hg.1
    have hsn : s = ((g 0 0).natAbs : ℤ) := by
      rw [hs, ← habs, Nat.sqrt_eq]
    rcases Int.natAbs_eq (g 0 0) with h | h
    · left; rw [hgs, hsn, ← h]
    · right; rw [hgs, hsn, ← h]
  have hval : ∀ a : ℤ, a ≠ 0 → (DeltaSet M n δ').indicator F (scalM a) = scalTerm k M n δ' a := by
    intro a ha
    by_cases hD : scalM a ∈ DeltaSet M n δ'
    · rw [indicator_of_mem hD, scalTerm, if_pos ((mem_DeltaSet_scalM a).1 hD)]
      show (if scalM a 1 0 = 0 ∧ scalM a 0 1 = 0 ∧ scalM a 0 0 = scalM a 1 1 then phiG k (scalM a) z
        else 0) = _
      rw [if_pos ⟨rfl, rfl, rfl⟩]
      exact phiG_scalM k ha z
    · rw [indicator_of_notMem hD, scalTerm, if_neg (fun h => hD ((mem_DeltaSet_scalM a).2 h))]
  have h1 : scalPart k M n δ' z = ∑' g : DeltaSet M n δ', F g := rfl
  rw [h1, tsum_subtype (DeltaSet M n δ') F,
    tsum_eq_sum (s := ({scalM s, scalM (-s)} : Finset (Matrix (Fin 2) (Fin 2) ℤ)))]
  · rw [Finset.sum_pair hne, hval s hs0, hval (-s) (neg_ne_zero.2 hs0), scalVal]
  · intro g hg
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hg
    by_cases hD : g ∈ DeltaSet M n δ'
    · rw [indicator_of_mem hD]
      show (if g 1 0 = 0 ∧ g 0 1 = 0 ∧ g 0 0 = g 1 1 then phiG k g z else 0) = 0
      rw [if_neg]
      intro hP
      rcases hmem g hD hP with h | h
      · exact hg.1 h
      · exact hg.2 h
    · exact indicator_of_notMem hD _

theorem scal_integral {M : ℕ} [NeZero M] (k : ℕ) (δ' : ZMod M) {n : ℕ} (hn : 0 < n) :
    IntegrableOn (scalPart k M n δ') (fdom (Gamma1 M)) ∧
      ∫ z in fdom (Gamma1 M), scalPart k M n δ' z =
        scalVal k M n δ' * ((((pmSL (Gamma1 M)).index : ℝ) * (π / 3) : ℝ) : ℂ) := by
  have hfun : scalPart k M n δ' = fun _ => scalVal k M n δ' := funext (scalPart_eq k M δ' hn)
  rw [hfun]
  refine ⟨integrableOn_const (volume_fdom_lt_top _).ne, ?_⟩
  rw [setIntegral_const, volume_real_fdom, Complex.real_smul]
  ring

/-- `n^{k-1} B_k⁻¹ (-2 i a)^{-k} π/3 = (k-1)/12 a^{k-2}` for `n = a²`. -/
lemma scal_norm {k : ℕ} (hk : 2 ≤ k) {a : ℂ} (ha : a ≠ 0) :
    (a ^ 2) ^ (k - 1) * (bergmanConst k)⁻¹ * ((-2 * Complex.I * a) ^ k)⁻¹ * (π / 3) =
      ((k : ℂ) - 1) / 12 * a ^ (k - 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  have hinv : (-2 * Complex.I)⁻¹ = Complex.I / 2 := by
    apply inv_eq_of_mul_eq_one_right
    ring_nf
    rw [I_sq]
    ring
  have h1 : ((-2 * Complex.I * a) ^ (m + 2))⁻¹ = Complex.I ^ (m + 2) / 2 ^ (m + 2) * (a ^ (m + 2))⁻¹ := by
    rw [mul_pow, mul_inv, ← inv_pow, hinv, div_pow]
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hI : Complex.I ^ (m + 2) ≠ 0 := pow_ne_zero _ I_ne_zero
  have hm : ((m + 2 : ℕ) : ℂ) - 1 = (m : ℂ) + 1 := by push_cast; ring
  have hm1 : (m : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  rw [h1, bergmanConst, hm, show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega]
  field_simp
  ring

lemma scalTerm_val {M k : ℕ} (hk : 2 ≤ k) {n : ℕ} {a : ℤ} (ha : a ≠ 0) (haa : a * a = (n : ℤ))
    (δ' : ZMod M) (x : ℝ) :
    (n : ℂ) ^ (k - 1) * (bergmanConst k)⁻¹ * (scalTerm k M n δ' a * (((x * (π / 3)) : ℝ) : ℂ)) =
      if ((a : ℤ) : ZMod M) = δ' then (x : ℂ) * (((k : ℂ) - 1) / 12 * (a : ℂ) ^ (k - 2)) else 0 := by
  by_cases h : ((a : ℤ) : ZMod M) = δ'
  · rw [scalTerm, if_pos ⟨haa, h⟩, if_pos h]
    have hn : (n : ℂ) = (a : ℂ) ^ 2 := by
      have := congrArg (Int.cast : ℤ → ℂ) haa
      push_cast at this
      rw [← this]; ring
    have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha
    rw [hn, ← scal_norm hk ha']
    push_cast
    ring
  · rw [scalTerm, if_neg (fun h' => h h'.2), if_neg h]
    simp

/-- The scalar contribution, up to the index `[SL₂(ℤ) : ±Γ₁(M)]`:
`[√n ∈ ℕ] (k-1)/12 · √n^{k-2} · ([√n δ = 1] + (-1)^k [√n δ = -1])`. -/
def scalTrace (M k n : ℕ) (δ : ZMod M) : ℂ :=
  if Nat.sqrt n * Nat.sqrt n = n then
    ((k : ℂ) - 1) / 12 * (Nat.sqrt n : ℂ) ^ (k - 2) *
      ((if (Nat.sqrt n : ZMod M) * δ = 1 then 1 else 0) +
        (-1) ^ k * (if (Nat.sqrt n : ZMod M) * δ = -1 then 1 else 0))
  else 0

/-- **Obligation 5.** The scalar term of the trace. -/
theorem scal_trace_term {M : ℕ} [NeZero M] {k : ℕ} (hk : 3 ≤ k) {n : ℕ} (hn : 0 < n)
    (hnM : n.Coprime M) (δ : (ZMod M)ˣ) :
    IntegrableOn (scalPart k M n ((unitOf M n * δ : (ZMod M)ˣ) : ZMod M)) (fdom (Gamma1 M)) ∧
      (n : ℂ) ^ (k - 1) * (bergmanConst k)⁻¹ *
          ∫ z in fdom (Gamma1 M), scalPart k M n ((unitOf M n * δ : (ZMod M)ˣ) : ZMod M) z =
        ((pmSL (Gamma1 M)).index : ℂ) * scalTrace M k n (δ : ZMod M) := by
  obtain ⟨hint, hval⟩ := scal_integral (M := M) k ((unitOf M n * δ : (ZMod M)ˣ) : ZMod M) hn
  refine ⟨hint, ?_⟩
  rw [hval, scalVal, add_mul, mul_add, scalTrace]
  set s := Nat.sqrt n with hs
  have hs0 : (s : ℤ) ≠ 0 := by exact_mod_cast (Nat.sqrt_pos.2 hn).ne'
  by_cases hsq : s * s = n
  · rw [if_pos hsq]
    have h1 : (s : ℤ) * s = n := by exact_mod_cast hsq
    have h2 : (-(s : ℤ)) * (-(s : ℤ)) = n := by rw [neg_mul_neg]; exact h1
    rw [scalTerm_val (by omega) hs0 h1, scalTerm_val (by omega) (neg_ne_zero.2 hs0) h2]
    have hu : IsUnit (s : ZMod M) :=
      (ZMod.isUnit_iff_coprime s M).2 (Nat.Coprime.coprime_dvd_left (Dvd.intro s hsq) hnM)
    have hδ' : ((unitOf M n * δ : (ZMod M)ˣ) : ZMod M) = (s : ZMod M) * s * δ := by
      rw [Units.val_mul, coe_unitOf hnM, ← hsq]; push_cast; ring
    have c1 : (((s : ℤ) : ZMod M) = (s : ZMod M) * s * δ) ↔ (s : ZMod M) * δ = 1 := by
      push_cast
      constructor
      · intro h; apply hu.mul_left_cancel; rw [mul_one, ← mul_assoc]; exact h.symm
      · intro h; rw [mul_assoc, h, mul_one]
    have c2 : (((-(s : ℤ) : ℤ)) : ZMod M) = (s : ZMod M) * s * δ ↔ (s : ZMod M) * δ = -1 := by
      push_cast
      constructor
      · intro h; apply hu.mul_left_cancel; rw [mul_neg_one, ← mul_assoc]; exact h.symm
      · intro h; rw [mul_assoc, h, mul_neg_one]
    rw [hδ']
    simp only [c1, c2]
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
    rw [show m + 2 - 2 = m by omega]
    split_ifs <;> push_cast <;> ring
  · rw [if_neg hsq, mul_zero]
    have h1 : ¬ ((s : ℤ) * s = n) := fun h => hsq (by exact_mod_cast h)
    have h2 : ¬ ((-(s : ℤ)) * (-(s : ℤ)) = n) := by rw [neg_mul_neg]; exact h1
    rw [scalTerm, if_neg (fun h => h1 h.1), scalTerm, if_neg (fun h => h2 h.1)]
    simp

end RamanujanPetersson.EllTerm


