-- Prove2me | solution 1 for AsymptoticOperator.exists_clm_coeffMul
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-10T18:28:47.472353+00:00
-- url     : https://prove2.me/submissions/0713ddaf-ee68-45ef-9154-bb2dcdb7b0e2

import Definitions.Def_AsymptoticOperator_Setting
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Theorems.Thm_AsymptoticOperator_hasSum_inner_coeff
import Theorems.Thm_AsymptoticOperator_exists_coeff_eq
import Mathlib.Analysis.CStarAlgebra.Matrix

namespace AsymptoticOperator

noncomputable section

open MeasureTheory Matrix ConleyZehnder

variable {n : ℕ}

/-- `complexify` as a continuous `ℝ`-linear map. -/
def cxL (n : ℕ) : Vec n →L[ℝ] (Fin n ⊕ Fin n → ℂ) :=
  ContinuousLinearMap.pi fun i => Complex.ofRealCLM.comp (EuclideanSpace.proj i)

lemma cxL_apply (v : Vec n) : cxL n v = complexify v := rfl

lemma integrable_L2 (f : L2 n) : Integrable (f : UnitAddCircle → Vec n) (AddCircle.haarAddCircle : Measure UnitAddCircle) :=
  (Lp.memLp f).integrable one_le_two

lemma integrable_cx (f : L2 n) : Integrable (fun t => complexify (f t)) (AddCircle.haarAddCircle : Measure UnitAddCircle) :=
  (cxL n).integrable_comp (integrable_L2 f)

lemma integrable_mul (S : C(UnitAddCircle, Mat n)) (f : L2 n) :
    Integrable (fun t => (S t).map (fun x : ℝ => (x : ℂ)) *ᵥ complexify (f t)) (AddCircle.haarAddCircle : Measure UnitAddCircle) := by
  rw [integrable_pi_iff]
  intro i
  simp only [mulVec, dotProduct]
  refine integrable_finsetSum _ fun j _ => ?_
  have hj : Integrable (fun t => complexify (f t) j) (AddCircle.haarAddCircle : Measure UnitAddCircle) :=
    (integrable_pi_iff.1 (integrable_cx f)) j
  have hc : Continuous fun t => S t i j :=
    (continuous_apply j).comp ((continuous_apply i).comp S.continuous)
  let Sij : C(UnitAddCircle, ℝ) := ⟨fun t => S t i j, hc⟩
  refine hj.bdd_mul (c := ‖Sij‖) ?_ ?_
  · exact (Complex.continuous_ofReal.comp hc).aestronglyMeasurable
  · refine ae_of_all _ fun t => ?_
    simp only [Matrix.map_apply, Complex.norm_real]
    exact Sij.norm_coe_le_norm t

lemma complexify_add (v w : Vec n) : complexify (v + w) = complexify v + complexify w := by
  simp only [← cxL_apply, map_add]

lemma complexify_smul (c : ℝ) (v : Vec n) : complexify (c • v) = (c : ℂ) • complexify v := by
  funext i; simp [complexify]

lemma coeff_add (f g : L2 n) : coeff ((f + g : L2 n) : UnitAddCircle → Vec n) = coeff f + coeff g := by
  have h : (fun t => complexify ((f + g : L2 n) t)) =ᵐ[(AddCircle.haarAddCircle : Measure UnitAddCircle)]
      (fun t => complexify (f t)) + (fun t => complexify (g t)) := by
    filter_upwards [Lp.coeFn_add f g] with t ht
    simp only [ht, Pi.add_apply, complexify_add]
  funext k
  simp only [coeff]
  rw [fourierCoeff_congr_ae h, fourierCoeff.add (integrable_cx f) (integrable_cx g)]
  rfl

lemma coeff_smul (c : ℝ) (f : L2 n) : coeff ((c • f : L2 n) : UnitAddCircle → Vec n) = (c : ℂ) • coeff f := by
  have h : (fun t => complexify ((c • f : L2 n) t)) =ᵐ[(AddCircle.haarAddCircle : Measure UnitAddCircle)]
      (c : ℂ) • (fun t => complexify (f t)) := by
    filter_upwards [Lp.coeFn_smul c f] with t ht
    simp only [ht, Pi.smul_apply, complexify_smul]
  funext k
  simp only [coeff]
  rw [fourierCoeff_congr_ae h]
  exact fourierCoeff.const_smul _ _ k

lemma coeff_zero : coeff ((0 : L2 n) : UnitAddCircle → Vec n) = 0 := by
  have := coeff_smul (0 : ℝ) (0 : L2 n)
  rwa [zero_smul, Complex.ofReal_zero, zero_smul] at this

lemma coeffMul_add (S : C(UnitAddCircle, Mat n)) (f g : L2 n) :
    coeffMul S ((f + g : L2 n) : UnitAddCircle → Vec n) = coeffMul S f + coeffMul S g := by
  have h : (fun t => (S t).map (fun x : ℝ => (x : ℂ)) *ᵥ complexify ((f + g : L2 n) t)) =ᵐ[(AddCircle.haarAddCircle : Measure UnitAddCircle)]
      (fun t => (S t).map (fun x : ℝ => (x : ℂ)) *ᵥ complexify (f t)) +
        (fun t => (S t).map (fun x : ℝ => (x : ℂ)) *ᵥ complexify (g t)) := by
    filter_upwards [Lp.coeFn_add f g] with t ht
    simp only [ht, Pi.add_apply, complexify_add, mulVec_add]
  funext k
  simp only [coeffMul]
  rw [fourierCoeff_congr_ae h, fourierCoeff.add (integrable_mul S f) (integrable_mul S g)]
  rfl

lemma coeffMul_smul (S : C(UnitAddCircle, Mat n)) (c : ℝ) (f : L2 n) :
    coeffMul S ((c • f : L2 n) : UnitAddCircle → Vec n) = (c : ℂ) • coeffMul S f := by
  have h : (fun t => (S t).map (fun x : ℝ => (x : ℂ)) *ᵥ complexify ((c • f : L2 n) t)) =ᵐ[(AddCircle.haarAddCircle : Measure UnitAddCircle)]
      (c : ℂ) • (fun t => (S t).map (fun x : ℝ => (x : ℂ)) *ᵥ complexify (f t)) := by
    filter_upwards [Lp.coeFn_smul c f] with t ht
    simp only [ht, Pi.smul_apply, complexify_smul, mulVec_smul]
  funext k
  simp only [coeffMul]
  rw [fourierCoeff_congr_ae h]
  exact fourierCoeff.const_smul _ _ k

lemma coeffMul_zero (S : C(UnitAddCircle, Mat n)) :
    coeffMul S ((0 : L2 n) : UnitAddCircle → Vec n) = 0 := by
  have := coeffMul_smul S (0 : ℝ) (0 : L2 n)
  rwa [zero_smul, Complex.ofReal_zero, zero_smul] at this

lemma eq_zero_of_coeff_eq_zero (g : L2 n) (h : ∀ k, coeff g k = 0) : g = 0 := by
  have hcomp : ∀ i, ∀ᵐ t ∂(AddCircle.haarAddCircle : Measure UnitAddCircle), (g t) i = 0 := by
    intro i
    let L : Vec n →L[ℝ] ℂ := Complex.ofRealCLM.comp (EuclideanSpace.proj i)
    let g' : Lp ℂ 2 (AddCircle.haarAddCircle : Measure UnitAddCircle) := L.compLp g
    have hcoef : ∀ k, fourierCoeff (g' : UnitAddCircle → ℂ) k = 0 := by
      intro k
      rw [fourierCoeff_congr_ae (L.coeFn_compLp' g)]
      have hint := (integrable_cx g).fourier_smul (-k)
      have e := eval_integral (integrable_pi_iff.1 hint) i
      have : coeff g k i = fourierCoeff (fun t => L (g t)) k := by
        show (∫ t, fourier (-k) t • complexify (g t) ∂(AddCircle.haarAddCircle : Measure UnitAddCircle)) i =
          ∫ t, fourier (-k) t • L (g t) ∂(AddCircle.haarAddCircle : Measure UnitAddCircle)
        rw [e]; rfl
      rw [← this, h k]; rfl
    have h0 : g' = 0 := by
      apply fourierBasis.repr.injective
      rw [map_zero]
      ext k
      rw [fourierBasis_repr, hcoef]
      rfl
    filter_upwards [L.coeFn_compLp' g, Lp.coeFn_zero ℂ 2 (AddCircle.haarAddCircle : Measure UnitAddCircle)] with t h1 h2
    have : L (g t) = 0 := by
      rw [← h1]; change (g' : UnitAddCircle → ℂ) t = 0; rw [h0]; exact h2
    simpa [L] using this
  apply Lp.ext
  filter_upwards [ae_all_iff.2 hcomp, Lp.coeFn_zero (Vec n) 2 (AddCircle.haarAddCircle : Measure UnitAddCircle)] with t ht h0
  rw [h0]
  ext i
  exact ht i

end

end AsymptoticOperator

open MeasureTheory Matrix ConleyZehnder AsymptoticOperator ComplexConjugate Filter Topology

lemma ao6_coeff_apply {n : ℕ} (f : L2 n) (k : ℤ) (i : Fin n ⊕ Fin n) :
    coeff f k i = fourierCoeff (fun t => ((f t i : ℝ) : ℂ)) k := by
  let L : Vec n →L[ℝ] (Fin n ⊕ Fin n → ℂ) :=
    ContinuousLinearMap.pi fun i => Complex.ofRealCLM.comp (EuclideanSpace.proj i)
  have hint : Integrable (fun t => complexify (f t)) (AddCircle.haarAddCircle : Measure UnitAddCircle) :=
    L.integrable_comp ((Lp.memLp f).integrable one_le_two)
  exact eval_integral (integrable_pi_iff.1 (hint.fourier_smul (-k))) i

lemma ao6_coeff_neg {n : ℕ} (f : L2 n) (k : ℤ) (i : Fin n ⊕ Fin n) :
    coeff f (-k) i = conj (coeff f k i) := by
  rw [ao6_coeff_apply, ao6_coeff_apply]
  simp only [fourierCoeff]
  rw [← integral_conj]
  congr 1
  funext t
  rw [smul_eq_mul, smul_eq_mul, map_mul, Complex.conj_ofReal, neg_neg, fourier_neg,
    Complex.conj_conj]

lemma ao6_re_self {n : ℕ} (v : Fin n ⊕ Fin n → ℂ) :
    (∑ i, conj (v i) * v i).re = ∑ i, ‖v i‖ ^ 2 := by
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.conj_mul']
  norm_cast

/-- Parseval: `‖f‖² = ∑ₖ |f̂ₖ|²`. -/
lemma ao6_norm_sq {n : ℕ} (f : L2 n) :
    HasSum (fun k : ℤ => ∑ i, ‖coeff f k i‖ ^ 2) (‖f‖ ^ 2) := by
  have h := hasSum_inner_coeff f f
  simp only [ao6_re_self, real_inner_self_eq_norm_sq] at h
  exact h

lemma ao6_norm_le {n : ℕ} (f g : L2 n) (ε : ℝ)
    (h : ∀ k, ∑ i, ‖coeff f k i‖ ^ 2 ≤ ε * ∑ i, ‖coeff g k i‖ ^ 2) :
    ‖f‖ ^ 2 ≤ ε * ‖g‖ ^ 2 :=
  hasSum_le h (ao6_norm_sq f) ((ao6_norm_sq g).mul_left ε)

lemma ao6_coeff_sub {n : ℕ} (f g : L2 n) (k : ℤ) :
    coeff ((f - g : L2 n) : UnitAddCircle → Vec n) k = coeff f k - coeff g k := by
  rw [sub_eq_add_neg, ← neg_one_smul ℝ g, coeff_add, coeff_smul]
  simp [sub_eq_add_neg]

lemma ao6_ext {n : ℕ} (f g : L2 n) (h : ∀ k, coeff f k = coeff g k) : f = g :=
  sub_eq_zero.1 (AsymptoticOperator.eq_zero_of_coeff_eq_zero _ fun k => by
    rw [ao6_coeff_sub, h k, sub_self])

lemma ao6_mulVec_conj {n : ℕ} (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (v : Fin n ⊕ Fin n → ℂ) (i : Fin n ⊕ Fin n) :
    (M.map (starRingEnd ℂ) *ᵥ fun j => conj (v j)) i = conj ((M *ᵥ v) i) := by
  simp [mulVec, dotProduct, map_sum, map_mul]

/-- A bounded conjugate-symmetric Fourier multiplier as a continuous linear map. -/
lemma ao6_mult {n : ℕ} (m : ℤ → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (hm : ∀ k, m (-k) = (m k).map (starRingEnd ℂ)) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ (k : ℤ) (v : Fin n ⊕ Fin n → ℂ), ∑ i, ‖(m k *ᵥ v) i‖ ^ 2 ≤ C * ∑ i, ‖v i‖ ^ 2) :
    ∃ T : L2 n →L[ℝ] L2 n, ∀ (g : L2 n) (k : ℤ), coeff (T g) k = m k *ᵥ coeff g k := by
  have hex : ∀ g : L2 n, ∃ h : L2 n, ∀ k, coeff h k = m k *ᵥ coeff g k := by
    intro g
    apply exists_coeff_eq
    · exact Summable.of_nonneg_of_le (fun k => by positivity) (fun k => hb k _)
        ((ao6_norm_sq g).summable.mul_left C)
    · intro k i
      rw [hm k, show coeff g (-k) = fun j => conj (coeff g k j) from
        funext fun j => ao6_coeff_neg g k j]
      exact ao6_mulVec_conj _ _ _
  choose F hF using hex
  let L : L2 n →ₗ[ℝ] L2 n :=
    { toFun := F
      map_add' := fun f g => ao6_ext _ _ fun k => by
        simp only [hF, coeff_add, Pi.add_apply, mulVec_add]
      map_smul' := fun c f => ao6_ext _ _ fun k => by
        simp only [hF, coeff_smul, RingHom.id_apply, Pi.smul_apply, mulVec_smul] }
  refine ⟨L.mkContinuous (Real.sqrt C) fun g => ?_, fun g k => hF g k⟩
  have h2 : ‖F g‖ ^ 2 ≤ (Real.sqrt C * ‖g‖) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hC]
    exact ao6_norm_le _ _ C fun k => by rw [hF]; exact hb k _
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2

open MeasureTheory Matrix ConleyZehnder AsymptoticOperator

/-- `L²` representatives of `S f` with a uniform bound `‖S f‖ ≤ C ‖f‖`. -/
lemma ao6m_exists {n : ℕ} (S : C(UnitAddCircle, Mat n)) :
    ∃ C : ℝ, ∀ f : L2 n, ∃ m : L2 n, (∀ k : ℤ, coeff m k = coeffMul S f k) ∧ ‖m‖ ≤ C * ‖f‖ := by
  let E := toEuclideanCLM (n := Fin n ⊕ Fin n) (𝕜 := ℝ)
  have hE : Continuous fun A : Mat n => E A :=
    LinearMap.continuous_of_finiteDimensional E.toAlgEquiv.toLinearMap
  let T : C(UnitAddCircle, Vec n →L[ℝ] Vec n) := ⟨fun t => E (S t), hE.comp S.continuous⟩
  refine ⟨‖T‖, fun f => ?_⟩
  have hmeas : AEStronglyMeasurable (fun t => T t (f t))
      (AddCircle.haarAddCircle : Measure UnitAddCircle) := by
    have hc : Continuous fun p : (Vec n →L[ℝ] Vec n) × Vec n => p.1 p.2 :=
      continuous_fst.clm_apply continuous_snd
    exact hc.comp_aestronglyMeasurable
      (T.continuous.aestronglyMeasurable.prodMk (Lp.aestronglyMeasurable f))
  have hpt : ∀ t, ‖T t (f t)‖ ≤ ‖T‖ * ‖f t‖ := fun t =>
    ((T t).le_opNorm (f t)).trans
      (mul_le_mul_of_nonneg_right (T.norm_coe_le_norm t) (norm_nonneg _))
  have hmem : MemLp (fun t => T t (f t)) 2 (AddCircle.haarAddCircle : Measure UnitAddCircle) :=
    (Lp.memLp f).of_le_mul hmeas (ae_of_all _ hpt)
  refine ⟨hmem.toLp _, fun k => ?_, ?_⟩
  · simp only [coeff, coeffMul]
    refine congrFun (fourierCoeff_congr_ae ?_) k
    filter_upwards [hmem.coeFn_toLp] with t ht
    rw [ht]
    funext i
    simp only [T, E, ContinuousMap.coe_mk, complexify]
    change ((((S t) *ᵥ ((f t : Vec n) : Fin n ⊕ Fin n → ℝ)) i : ℝ) : ℂ) = _
    simp [mulVec, dotProduct, complexify]
  · refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
    filter_upwards [hmem.coeFn_toLp] with t ht
    rw [ht]
    exact hpt t

theorem solution {n : ℕ} (S : C(UnitAddCircle, Mat n)) :
    ∃ B : L2 n →L[ℝ] L2 n, ∀ (f : L2 n) (k : ℤ), coeff (B f) k = coeffMul S f k := by
  obtain ⟨C, hC⟩ := ao6m_exists S
  choose F hF hFn using hC
  let L : L2 n →ₗ[ℝ] L2 n :=
    { toFun := F
      map_add' := fun f g => ao6_ext _ _ fun k => by
        simp only [hF, coeff_add, coeffMul_add, Pi.add_apply]
      map_smul' := fun c f => ao6_ext _ _ fun k => by
        simp only [hF, coeff_smul, coeffMul_smul, RingHom.id_apply, Pi.smul_apply] }
  exact ⟨L.mkContinuous C hFn, hF⟩
