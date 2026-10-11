-- Prove2me | solution 1 for AsymptoticOperator.graphSet_add_mem
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-10T11:39:21.628432+00:00
-- url     : https://prove2.me/submissions/05570013-278d-4707-96ef-c5d29468361f

import Definitions.Def_AsymptoticOperator_Setting
import Mathlib.MeasureTheory.SpecificCodomains.Pi



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

namespace AsymptoticOperator

noncomputable section

open MeasureTheory Matrix ConleyZehnder

variable {n : ℕ}

lemma inW12_add {f g : L2 n} (hf : InW12 f) (hg : InW12 g) : InW12 (f + g) := by
  unfold InW12 at *
  rw [coeff_add]
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    ((hf.add hg).mul_left 2)
  simp only [Pi.add_apply]
  have h1 : (0 : ℝ) ≤ 1 + (k : ℝ) ^ 2 := by positivity
  have h2 : ∑ i, ‖coeff f k i + coeff g k i‖ ^ 2 ≤
      2 * (∑ i, ‖coeff f k i‖ ^ 2 + ∑ i, ‖coeff g k i‖ ^ 2) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have h3 := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le (coeff f k i) (coeff g k i)) 2
    nlinarith [sq_nonneg (‖coeff f k i‖ - ‖coeff g k i‖)]
  nlinarith

lemma inW12_smul (c : ℝ) {f : L2 n} (hf : InW12 f) : InW12 (c • f) := by
  unfold InW12 at *
  rw [coeff_smul]
  refine (hf.mul_left (c ^ 2)).congr fun k => ?_
  simp only [Pi.smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs,
    ← Finset.mul_sum]
  ring

lemma inW12_zero : InW12 (0 : L2 n) := by
  unfold InW12
  rw [coeff_zero]
  simp

lemma action_zero_rhs (S : C(UnitAddCircle, Mat n)) (k : ℤ) :
    -((2 * Real.pi * k : ℝ) * Complex.I) •
        ((J₀ n).map (fun x : ℝ => (x : ℂ)) *ᵥ coeff ((0 : L2 n) : UnitAddCircle → Vec n) k) -
      coeffMul S ((0 : L2 n) : UnitAddCircle → Vec n) k = 0 := by
  rw [coeff_zero, coeffMul_zero]
  simp

/-- The graph set as a submodule. -/
def graphSubmodule (S : C(UnitAddCircle, Mat n)) : Submodule ℝ (L2 n × L2 n) where
  carrier := graphSet S
  zero_mem' := by
    refine ⟨inW12_zero, fun k => ?_⟩
    simp only [Prod.fst_zero, Prod.snd_zero]
    rw [action_zero_rhs S k]
    exact congrFun coeff_zero k
  add_mem' := by
    rintro ⟨f₁, g₁⟩ ⟨f₂, g₂⟩ ⟨h₁, e₁⟩ ⟨h₂, e₂⟩
    refine ⟨inW12_add h₁ h₂, fun k => ?_⟩
    simp only [Prod.fst_add, Prod.snd_add, coeff_add, coeffMul_add, Pi.add_apply] at *
    rw [e₁ k, e₂ k, mulVec_add, smul_add]
    abel
  smul_mem' := by
    rintro c ⟨f, g⟩ ⟨h, e⟩
    refine ⟨inW12_smul c h, fun k => ?_⟩
    simp only [Prod.smul_fst, Prod.smul_snd, coeff_smul, coeffMul_smul, Pi.smul_apply] at *
    rw [e k, mulVec_smul, smul_sub, smul_comm ((c : ℂ))]

lemma graphSet_fst_zero (S : C(UnitAddCircle, Mat n)) (g : L2 n)
    (h : ((0 : L2 n), g) ∈ graphSet S) : g = 0 := by
  apply eq_zero_of_coeff_eq_zero
  intro k
  have e := h.2 k
  simp only at e
  rw [e]
  exact action_zero_rhs S k

theorem graph_existsUnique' {n : ℕ} (S : C(UnitAddCircle, Mat n)) :
    ∃! A : L2 n →ₗ.[ℝ] L2 n, (A.graph : Set (L2 n × L2 n)) = graphSet S := by
  have hg : ∀ (x : L2 n × L2 n) (_hx : x ∈ graphSubmodule S) (_hx' : x.fst = 0), x.snd = 0 := by
    rintro ⟨f, g⟩ hx (rfl : f = 0)
    exact graphSet_fst_zero S g hx
  refine ⟨(graphSubmodule S).toLinearPMap, ?_, fun A hA => ?_⟩
  · show (((graphSubmodule S).toLinearPMap.graph : Submodule ℝ _) : Set (L2 n × L2 n)) = _
    rw [Submodule.toLinearPMap_graph_eq _ hg]; rfl
  · apply LinearPMap.eq_of_eq_graph
    rw [Submodule.toLinearPMap_graph_eq _ hg]
    exact SetLike.coe_injective hA

end

end AsymptoticOperator

open AsymptoticOperator

open ConleyZehnder

theorem solution {n : ℕ} (S : C(UnitAddCircle, Mat n)) {p q : L2 n × L2 n}
    (hp : p ∈ graphSet S) (hq : q ∈ graphSet S) : p + q ∈ graphSet S :=
  (graphSubmodule S).add_mem hp hq
