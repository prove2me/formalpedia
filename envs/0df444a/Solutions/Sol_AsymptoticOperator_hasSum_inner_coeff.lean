-- Prove2me | solution 1 for AsymptoticOperator.hasSum_inner_coeff
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-10T16:35:50.576681+00:00
-- url     : https://prove2.me/submissions/05ae888e-868b-474e-9c23-8b9744ec5c42

import Definitions.Def_AsymptoticOperator_Setting
import Mathlib.MeasureTheory.SpecificCodomains.Pi

open MeasureTheory Matrix ConleyZehnder AsymptoticOperator ComplexConjugate

lemma ao3p_coeff_apply {n : ℕ} (f : L2 n) (k : ℤ) (i : Fin n ⊕ Fin n) :
    coeff f k i = fourierCoeff (fun t => ((f t i : ℝ) : ℂ)) k := by
  let L : Vec n →L[ℝ] (Fin n ⊕ Fin n → ℂ) :=
    ContinuousLinearMap.pi fun i => Complex.ofRealCLM.comp (EuclideanSpace.proj i)
  have hint : Integrable (fun t => complexify (f t)) (AddCircle.haarAddCircle : Measure UnitAddCircle) :=
    L.integrable_comp ((Lp.memLp f).integrable one_le_two)
  exact eval_integral (integrable_pi_iff.1 (hint.fourier_smul (-k))) i

theorem solution {n : ℕ} (f g : L2 n) :
    HasSum (fun k : ℤ => (∑ i, conj (coeff f k i) * coeff g k i).re) (inner ℝ f g) := by
  let L : Fin n ⊕ Fin n → (Vec n →L[ℝ] ℂ) := fun i =>
    Complex.ofRealCLM.comp (EuclideanSpace.proj i)
  let F : Fin n ⊕ Fin n → Lp ℂ 2 (AddCircle.haarAddCircle : Measure UnitAddCircle) :=
    fun i => (L i).compLp f
  let G : Fin n ⊕ Fin n → Lp ℂ 2 (AddCircle.haarAddCircle : Measure UnitAddCircle) :=
    fun i => (L i).compLp g
  have hcF : ∀ i k, fourierCoeff (F i : UnitAddCircle → ℂ) k = coeff f k i := by
    intro i k
    rw [ao3p_coeff_apply, fourierCoeff_congr_ae ((L i).coeFn_compLp' f)]
    rfl
  have hcG : ∀ i k, fourierCoeff (G i : UnitAddCircle → ℂ) k = coeff g k i := by
    intro i k
    rw [ao3p_coeff_apply, fourierCoeff_congr_ae ((L i).coeFn_compLp' g)]
    rfl
  have hpar : ∀ i, HasSum (fun k : ℤ => conj (coeff f k i) * coeff g k i)
      (inner ℂ (F i) (G i)) := by
    intro i
    have h := fourierBasis.hasSum_inner_mul_inner (F i) (G i)
    have e : (fun k : ℤ => conj (coeff f k i) * coeff g k i) =
        fun k => inner ℂ (F i) (fourierBasis k) * inner ℂ (fourierBasis k) (G i) := by
      funext k
      rw [← inner_conj_symm, ← fourierBasis.repr_apply_apply, ← fourierBasis.repr_apply_apply,
        fourierBasis_repr, fourierBasis_repr, hcF, hcG]
    rw [e]; exact h
  have hsum := (hasSum_sum (s := Finset.univ) fun i _ => hpar i)
  have hre := Complex.reCLM.hasSum hsum
  simp only [Complex.reCLM_apply] at hre
  have ef : (fun k : ℤ => (∑ i, conj (coeff f k i) * coeff g k i).re) =
      fun k => (∑ i, conj (coeff f k i) * coeff g k i).re := rfl
  have ev : inner ℝ f g = (∑ i, inner ℂ (F i) (G i)).re := by
    have hpt : ∀ i, (inner ℂ (F i) (G i)).re =
        ∫ t, (f t i) * (g t i) ∂(AddCircle.haarAddCircle : Measure UnitAddCircle) := by
      intro i
      rw [MeasureTheory.L2.inner_def, ← RCLike.re_to_complex,
        ← integral_re (L2.integrable_inner (𝕜 := ℂ) (F i) (G i))]
      refine integral_congr_ae ?_
      filter_upwards [(L i).coeFn_compLp' f, (L i).coeFn_compLp' g] with t h1 h2
      simp only [F, G] at h1 h2 ⊢
      rw [h1, h2]
      simp [L, mul_comm]
    have hint : ∀ i, Integrable (fun t => (f t i) * (g t i))
        (AddCircle.haarAddCircle : Measure UnitAddCircle) := by
      intro i
      refine ((L2.integrable_inner (𝕜 := ℂ) (F i) (G i)).re).congr ?_
      filter_upwards [(L i).coeFn_compLp' f, (L i).coeFn_compLp' g] with t h1 h2
      simp only [F, G] at h1 h2 ⊢
      rw [h1, h2]
      simp [L, mul_comm]
    rw [Complex.re_sum]
    simp only [hpt]
    rw [← integral_finset_sum _ fun i _ => hint i, MeasureTheory.L2.inner_def]
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    simp [PiLp.inner_apply, mul_comm]
  exact ev ▸ hre
