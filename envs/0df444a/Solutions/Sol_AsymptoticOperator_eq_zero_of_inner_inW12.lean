-- Prove2me | solution 1 for AsymptoticOperator.eq_zero_of_inner_inW12
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-10T12:20:08.940829+00:00
-- url     : https://prove2.me/submissions/2373d069-f94f-4018-af0e-bc90d32f4f8f

import Theorems.Thm_AsymptoticOperator_eq_zero_of_coeff_eq_zero
import Mathlib.MeasureTheory.SpecificCodomains.Pi

open MeasureTheory Matrix ConleyZehnder AsymptoticOperator ComplexConjugate

lemma ao2o_integrable {n : ℕ} (f : L2 n) :
    Integrable (fun t => complexify (f t)) (AddCircle.haarAddCircle : Measure UnitAddCircle) := by
  let L : Vec n →L[ℝ] (Fin n ⊕ Fin n → ℂ) :=
    ContinuousLinearMap.pi fun i => Complex.ofRealCLM.comp (EuclideanSpace.proj i)
  exact L.integrable_comp ((Lp.memLp f).integrable one_le_two)

lemma ao2o_coeff_apply {n : ℕ} (f : L2 n) (k : ℤ) (i : Fin n ⊕ Fin n) :
    coeff f k i = fourierCoeff (fun t => ((f t i : ℝ) : ℂ)) k :=
  eval_integral (integrable_pi_iff.1 ((ao2o_integrable f).fourier_smul (-k))) i

lemma ao2o_integrable_fourier (m : ℤ) :
    Integrable (fourier m : UnitAddCircle → ℂ) (AddCircle.haarAddCircle : Measure UnitAddCircle) :=
  ((Lp.memLp (fourierLp 2 m)).integrable one_le_two).congr (coeFn_fourierLp 2 m)

/-- The real test function `t ↦ Re(z e^{2πikt}) eⱼ`. -/
noncomputable def ao2oψ {n : ℕ} (k : ℤ) (j : Fin n ⊕ Fin n) (z : ℂ) : C(UnitAddCircle, Vec n) :=
  ⟨fun t => (z * fourier k t).re • EuclideanSpace.single j (1 : ℝ),
    (Complex.continuous_re.comp (continuous_const.mul (fourier k).continuous)).smul
      continuous_const⟩

lemma ao2o_re_eq (z : ℂ) (k : ℤ) (t : UnitAddCircle) :
    (((z * fourier k t).re : ℝ) : ℂ) = z / 2 * fourier k t + conj z / 2 * fourier (-k) t := by
  rw [Complex.re_eq_add_conj, map_mul, ← fourier_neg]
  ring

lemma ao2o_coeff_ψ {n : ℕ} (k m : ℤ) (j i : Fin n ⊕ Fin n) (z : ℂ) :
    coeff (ContinuousMap.toLp (E := Vec n) 2 (AddCircle.haarAddCircle : Measure UnitAddCircle) ℝ
        (ao2oψ k j z)) m i =
      (if i = j then (1 : ℂ) else 0) *
        (z / 2 * (Pi.single k (1 : ℂ) : ℤ → ℂ) m + conj z / 2 * (Pi.single (-k) (1 : ℂ) : ℤ → ℂ) m) := by
  rw [ao2o_coeff_apply]
  have hae : (fun t => (((ContinuousMap.toLp (E := Vec n) 2
        (AddCircle.haarAddCircle : Measure UnitAddCircle) ℝ (ao2oψ k j z)) t i : ℝ) : ℂ))
      =ᵐ[(AddCircle.haarAddCircle : Measure UnitAddCircle)]
      (if i = j then (1 : ℂ) else 0) •
        ((z / 2) • (fourier k : UnitAddCircle → ℂ) + (conj z / 2) • (fourier (-k) : UnitAddCircle → ℂ)) := by
    filter_upwards [ContinuousMap.coeFn_toLp (E := Vec n) (p := 2)
      (μ := (AddCircle.haarAddCircle : Measure UnitAddCircle)) (𝕜 := ℝ) (ao2oψ k j z)] with t ht
    rw [ht]
    simp only [ao2oψ, ContinuousMap.coe_mk, PiLp.smul_apply, PiLp.single_apply,
      Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    split_ifs <;> simp only [mul_one, one_mul, mul_zero, zero_mul, Complex.ofReal_zero, ao2o_re_eq,
      smul_eq_mul]
  rw [fourierCoeff_congr_ae hae, fourierCoeff.const_smul,
    fourierCoeff.add ((ao2o_integrable_fourier k).smul _) ((ao2o_integrable_fourier (-k)).smul _),
    Pi.add_apply, fourierCoeff.const_smul, fourierCoeff.const_smul, fourierCoeff_fourier, fourierCoeff_fourier]
  simp only [smul_eq_mul]

theorem solution {n : ℕ} (g : L2 n)
    (h : ∀ f : L2 n, InW12 f → inner ℝ f g = 0) : g = 0 := by
  apply eq_zero_of_coeff_eq_zero
  intro k
  funext j
  have key : ∀ z : ℂ, (z * coeff g k j).re = 0 := by
    intro z
    set φ := ContinuousMap.toLp (E := Vec n) 2 (AddCircle.haarAddCircle : Measure UnitAddCircle) ℝ
      (ao2oψ (-k) j z) with hφ
    have hW : InW12 φ := by
      unfold InW12
      apply summable_of_ne_finset_zero (s := {-k, - -k})
      intro m hm
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hm
      rw [hφ]
      simp only [ao2o_coeff_ψ, Pi.single_apply, if_neg hm.1, if_neg hm.2]
      simp
    have h0 := h φ hW
    have e1 : inner ℝ φ g = ∫ t, (z * fourier (-k) t).re * g t j
        ∂(AddCircle.haarAddCircle : Measure UnitAddCircle) := by
      rw [MeasureTheory.L2.inner_def]
      apply integral_congr_ae
      filter_upwards [ContinuousMap.coeFn_toLp (E := Vec n) (p := 2)
        (μ := (AddCircle.haarAddCircle : Measure UnitAddCircle)) (𝕜 := ℝ) (ao2oψ (-k) j z)] with t ht
      rw [hφ, ht]
      simp [ao2oψ, real_inner_smul_left, EuclideanSpace.inner_single_left]
    have hint : Integrable (fun t => fourier (-k) t * ((g t j : ℝ) : ℂ))
        (AddCircle.haarAddCircle : Measure UnitAddCircle) :=
      ((integrable_pi_iff.1 (ao2o_integrable g) j).fourier_smul (-k))
    have e2 : (z * coeff g k j).re = ∫ t, (z * fourier (-k) t).re * g t j
        ∂(AddCircle.haarAddCircle : Measure UnitAddCircle) := by
      rw [ao2o_coeff_apply]
      simp only [fourierCoeff, smul_eq_mul]
      have hre := integral_re (hint.const_mul z)
      simp only [RCLike.re_to_complex] at hre
      rw [← integral_const_mul, ← hre]
      congr 1
      funext t
      rw [← mul_assoc, Complex.re_mul_ofReal]
    rw [e2, ← e1, h0]
  apply Complex.ext
  · simpa using key 1
  · simpa using key Complex.I
