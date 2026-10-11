-- Prove2me | solution 1 for AsymptoticOperator.inner_mul_symm
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-10T16:40:14.856411+00:00
-- url     : https://prove2.me/submissions/326947ca-0b6b-428b-936f-caf21f993777

import Theorems.Thm_AsymptoticOperator_eq_zero_of_coeff_eq_zero
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.MeasureTheory.SpecificCodomains.Pi

open MeasureTheory Matrix ConleyZehnder AsymptoticOperator

lemma ao3m_coeff_apply {n : ℕ} (f : L2 n) (k : ℤ) (i : Fin n ⊕ Fin n) :
    coeff f k i = fourierCoeff (fun t => ((f t i : ℝ) : ℂ)) k := by
  let L : Vec n →L[ℝ] (Fin n ⊕ Fin n → ℂ) :=
    ContinuousLinearMap.pi fun i => Complex.ofRealCLM.comp (EuclideanSpace.proj i)
  have hint : Integrable (fun t => complexify (f t)) (AddCircle.haarAddCircle : Measure UnitAddCircle) :=
    L.integrable_comp ((Lp.memLp f).integrable one_le_two)
  exact eval_integral (integrable_pi_iff.1 (hint.fourier_smul (-k))) i

lemma ao3m_coeff_sub {n : ℕ} (f g : L2 n) (k : ℤ) :
    coeff ((f - g : L2 n) : UnitAddCircle → Vec n) k = coeff f k - coeff g k := by
  funext i
  rw [Pi.sub_apply, ao3m_coeff_apply, ao3m_coeff_apply, ao3m_coeff_apply]
  have h : (fun t => (((f - g : L2 n) t i : ℝ) : ℂ)) =ᵐ[(AddCircle.haarAddCircle : Measure UnitAddCircle)]
      fun t => ((f t i : ℝ) : ℂ) - ((g t i : ℝ) : ℂ) := by
    filter_upwards [Lp.coeFn_sub f g] with t ht
    rw [ht]; simp
  rw [fourierCoeff_congr_ae h]
  have hf := (integrable_pi_iff.1 ((ContinuousLinearMap.pi fun i =>
    Complex.ofRealCLM.comp (EuclideanSpace.proj i) : Vec n →L[ℝ] (Fin n ⊕ Fin n → ℂ)).integrable_comp
      ((Lp.memLp f).integrable one_le_two))) i
  have hg := (integrable_pi_iff.1 ((ContinuousLinearMap.pi fun i =>
    Complex.ofRealCLM.comp (EuclideanSpace.proj i) : Vec n →L[ℝ] (Fin n ⊕ Fin n → ℂ)).integrable_comp
      ((Lp.memLp g).integrable one_le_two))) i
  simp only [fourierCoeff, smul_eq_mul, mul_sub]
  exact integral_sub (hf.fourier_smul (-k)) (hg.fourier_smul (-k))

/-- An explicit `L²` representative of `t ↦ S(t) f(t)` with its pointwise description. -/
lemma ao3m_exists_mul {n : ℕ} (S : C(UnitAddCircle, Mat n)) (f : L2 n) :
    ∃ m : L2 n, (∀ k : ℤ, coeff m k = coeffMul S f k) ∧
      ∀ᵐ t ∂(AddCircle.haarAddCircle : Measure UnitAddCircle),
        m t = toEuclideanCLM (n := Fin n ⊕ Fin n) (𝕜 := ℝ) (S t) (f t) := by
  let E := toEuclideanCLM (n := Fin n ⊕ Fin n) (𝕜 := ℝ)
  have hE : Continuous fun A : Mat n => E A :=
    LinearMap.continuous_of_finiteDimensional E.toAlgEquiv.toLinearMap
  let T : C(UnitAddCircle, Vec n →L[ℝ] Vec n) := ⟨fun t => E (S t), hE.comp S.continuous⟩
  have hmeas : AEStronglyMeasurable (fun t => T t (f t))
      (AddCircle.haarAddCircle : Measure UnitAddCircle) := by
    have hc : Continuous fun p : (Vec n →L[ℝ] Vec n) × Vec n => p.1 p.2 :=
      continuous_fst.clm_apply continuous_snd
    exact hc.comp_aestronglyMeasurable
      (T.continuous.aestronglyMeasurable.prodMk (Lp.aestronglyMeasurable f))
  have hmem : MemLp (fun t => T t (f t)) 2 (AddCircle.haarAddCircle : Measure UnitAddCircle) :=
    (Lp.memLp f).of_le_mul hmeas (ae_of_all _ fun t =>
      ((T t).le_opNorm (f t)).trans
        (mul_le_mul_of_nonneg_right (T.norm_coe_le_norm t) (norm_nonneg _)))
  refine ⟨hmem.toLp _, fun k => ?_, hmem.coeFn_toLp⟩
  simp only [coeff, coeffMul]
  refine congrFun (fourierCoeff_congr_ae ?_) k
  filter_upwards [hmem.coeFn_toLp] with t ht
  rw [ht]
  funext i
  simp only [T, E, ContinuousMap.coe_mk, complexify]
  change ((((S t) *ᵥ ((f t : Vec n) : Fin n ⊕ Fin n → ℝ)) i : ℝ) : ℂ) = _
  simp [mulVec, dotProduct, complexify]

lemma ao3m_inner_symm {n : ℕ} (A : Mat n) (hA : A.IsSymm) (v w : Vec n) :
    inner ℝ (toEuclideanCLM (n := Fin n ⊕ Fin n) (𝕜 := ℝ) A v) w =
      inner ℝ v (toEuclideanCLM (n := Fin n ⊕ Fin n) (𝕜 := ℝ) A w) := by
  change inner ℝ (WithLp.toLp 2 (A *ᵥ (v : Fin n ⊕ Fin n → ℝ))) w =
    inner ℝ v (WithLp.toLp 2 (A *ᵥ (w : Fin n ⊕ Fin n → ℝ)))
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, PiLp.toLp_apply]
  simp only [mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have : A j i = A i j := by
    have := congrFun (congrFun hA i) j
    simpa [transpose_apply] using this
  rw [this]; ring

theorem solution {n : ℕ} (S : C(UnitAddCircle, Mat n)) (hS : IsSymLoop S)
    (f g m m' : L2 n) (hm : ∀ k : ℤ, coeff m k = coeffMul S f k)
    (hm' : ∀ k : ℤ, coeff m' k = coeffMul S g k) :
    inner ℝ m g = inner ℝ f m' := by
  obtain ⟨p, hp, hpt⟩ := ao3m_exists_mul S f
  obtain ⟨q, hq, hqt⟩ := ao3m_exists_mul S g
  have h1 : m = p := sub_eq_zero.1 (eq_zero_of_coeff_eq_zero _ fun k => by
    rw [ao3m_coeff_sub, hm, hp, sub_self])
  have h2 : m' = q := sub_eq_zero.1 (eq_zero_of_coeff_eq_zero _ fun k => by
    rw [ao3m_coeff_sub, hm', hq, sub_self])
  subst h1 h2
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hpt, hqt] with t ht1 ht2
  rw [ht1, ht2]
  exact ao3m_inner_symm _ (hS t) _ _
