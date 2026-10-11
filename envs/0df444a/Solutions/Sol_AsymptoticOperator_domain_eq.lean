-- Prove2me | solution 1 for AsymptoticOperator.domain_eq
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-10T12:03:17.798429+00:00
-- url     : https://prove2.me/submissions/e86f8899-038a-429e-ae9e-3d909339956c

import Theorems.Thm_AsymptoticOperator_graph_existsUnique
import Theorems.Thm_AsymptoticOperator_exists_coeff_eq
import Theorems.Thm_AsymptoticOperator_exists_coeff_eq_coeffMul
import Theorems.Thm_AsymptoticOperator_eq_zero_of_inner_inW12
import Mathlib.MeasureTheory.SpecificCodomains.Pi

open MeasureTheory Matrix ConleyZehnder AsymptoticOperator ComplexConjugate

lemma ao2_integrable {n : ℕ} (f : L2 n) :
    Integrable (fun t => complexify (f t)) (AddCircle.haarAddCircle : Measure UnitAddCircle) := by
  let L : Vec n →L[ℝ] (Fin n ⊕ Fin n → ℂ) :=
    ContinuousLinearMap.pi fun i => Complex.ofRealCLM.comp (EuclideanSpace.proj i)
  exact L.integrable_comp ((Lp.memLp f).integrable one_le_two)

lemma ao2_coeff_apply {n : ℕ} (f : L2 n) (k : ℤ) (i : Fin n ⊕ Fin n) :
    coeff f k i = fourierCoeff (fun t => ((f t i : ℝ) : ℂ)) k := by
  have hint := (ao2_integrable f).fourier_smul (-k)
  exact eval_integral (integrable_pi_iff.1 hint) i

lemma ao2_fourierCoeff_ofReal_neg (r : UnitAddCircle → ℝ) (k : ℤ) :
    fourierCoeff (fun t => ((r t : ℝ) : ℂ)) (-k) = conj (fourierCoeff (fun t => ((r t : ℝ) : ℂ)) k) := by
  simp only [fourierCoeff, smul_eq_mul]
  rw [← integral_conj]
  congr 1
  funext t
  rw [map_mul, Complex.conj_ofReal, ← fourier_neg, neg_neg]

lemma ao2_coeff_neg {n : ℕ} (f : L2 n) (k : ℤ) (i : Fin n ⊕ Fin n) :
    coeff f (-k) i = conj (coeff f k i) := by
  rw [ao2_coeff_apply, ao2_coeff_apply, ao2_fourierCoeff_ofReal_neg]

lemma ao2_coeff_sub {n : ℕ} (f g : L2 n) (k : ℤ) :
    coeff ((f - g : L2 n) : UnitAddCircle → Vec n) k = coeff f k - coeff g k := by
  funext i
  rw [Pi.sub_apply, ao2_coeff_apply, ao2_coeff_apply, ao2_coeff_apply]
  have h : (fun t => (((f - g : L2 n) t i : ℝ) : ℂ)) =ᵐ[(AddCircle.haarAddCircle : Measure UnitAddCircle)]
      fun t => ((f t i : ℝ) : ℂ) - ((g t i : ℝ) : ℂ) := by
    filter_upwards [Lp.coeFn_sub f g] with t ht
    rw [ht]; simp
  rw [fourierCoeff_congr_ae h]
  have hf := (integrable_pi_iff.1 (ao2_integrable f)) i
  have hg := (integrable_pi_iff.1 (ao2_integrable g)) i
  simp only [fourierCoeff, smul_eq_mul, mul_sub]
  exact integral_sub (hf.fourier_smul (-k)) (hg.fourier_smul (-k))

lemma ao2_J_inl {n : ℕ} (v : Fin n ⊕ Fin n → ℂ) (a : Fin n) :
    ((J₀ n).map (fun x : ℝ => (x : ℂ)) *ᵥ v) (Sum.inl a) = -v (Sum.inr a) := by
  simp [J₀, Matrix.J, mulVec, dotProduct, Fintype.sum_sum_type, one_apply]
  simp only [apply_ite (fun x : ℝ => (x : ℂ)), Complex.ofReal_one, Complex.ofReal_zero, ite_mul,
    one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

lemma ao2_J_inr {n : ℕ} (v : Fin n ⊕ Fin n → ℂ) (a : Fin n) :
    ((J₀ n).map (fun x : ℝ => (x : ℂ)) *ᵥ v) (Sum.inr a) = v (Sum.inl a) := by
  simp [J₀, Matrix.J, mulVec, dotProduct, Fintype.sum_sum_type, one_apply]
  simp only [apply_ite (fun x : ℝ => (x : ℂ)), Complex.ofReal_one, Complex.ofReal_zero, ite_mul,
    one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

lemma ao2_J_normSq {n : ℕ} (v : Fin n ⊕ Fin n → ℂ) :
    ∑ i, ‖((J₀ n).map (fun x : ℝ => (x : ℂ)) *ᵥ v) i‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  simp only [Fintype.sum_sum_type, ao2_J_inl, ao2_J_inr, norm_neg]
  ring

theorem solution {n : ℕ} (S : C(UnitAddCircle, Mat n)) :
    (∀ f : L2 n, f ∈ (asymptoticOperator S).domain ↔ InW12 f) ∧
      Dense ((asymptoticOperator S).domain : Set (L2 n)) := by
  have hex := (graph_existsUnique S).exists
  have hgraph : ((asymptoticOperator S).graph : Set (L2 n × L2 n)) = graphSet S := by
    unfold asymptoticOperator; rw [dif_pos hex]; exact hex.choose_spec
  have hmem : ∀ f : L2 n, f ∈ (asymptoticOperator S).domain ↔ InW12 f := by
    intro f
    rw [LinearPMap.mem_domain_iff]
    constructor
    · rintro ⟨g, hg⟩
      have : (f, g) ∈ graphSet S := by rw [← hgraph]; exact hg
      exact this.1
    · intro hf
      set c : ℤ → Fin n ⊕ Fin n → ℂ := fun k =>
        -((2 * Real.pi * k : ℝ) * Complex.I) • ((J₀ n).map (fun x : ℝ => (x : ℂ)) *ᵥ coeff f k)
        with hc
      have hnorm : ∀ k : ℤ, ∑ i, ‖c k i‖ ^ 2 = (2 * Real.pi * k) ^ 2 * ∑ i, ‖coeff f k i‖ ^ 2 := by
        intro k
        rw [← ao2_J_normSq (coeff f k), Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [hc, Pi.smul_apply, smul_eq_mul, norm_mul, norm_neg, Complex.norm_I,
          Complex.norm_real, mul_one, mul_pow, Real.norm_eq_abs, sq_abs]
      have hsum : Summable fun k : ℤ => ∑ i, ‖c k i‖ ^ 2 := by
        refine Summable.of_nonneg_of_le (fun k => Finset.sum_nonneg fun i _ => by positivity)
          (fun k => ?_) (hf.mul_left (4 * Real.pi ^ 2))
        rw [hnorm, ← mul_assoc]
        refine mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun i _ => by positivity)
        nlinarith [Real.pi_pos, sq_nonneg (Real.pi : ℝ), sq_nonneg ((k : ℝ) * Real.pi)]
      have hconj : ∀ k i, c (-k) i = conj (c k i) := by
        intro k i
        rcases i with a | a <;>
          simp only [hc, Pi.smul_apply, smul_eq_mul, ao2_J_inl, ao2_J_inr, ao2_coeff_neg,
            map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal, Int.cast_neg] <;>
          push_cast <;> ring
      obtain ⟨h, hh⟩ := exists_coeff_eq c hsum hconj
      obtain ⟨m, hm⟩ := exists_coeff_eq_coeffMul S f
      refine ⟨h - m, ?_⟩
      have : (f, h - m) ∈ graphSet S := ⟨hf, fun k => by rw [ao2_coeff_sub, hh, hm]⟩
      rw [← hgraph] at this
      exact this
  refine ⟨hmem, ?_⟩
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro g hg
  exact eq_zero_of_inner_inW12 g fun f hf =>
    Submodule.inner_right_of_mem_orthogonal ((hmem f).2 hf) hg
