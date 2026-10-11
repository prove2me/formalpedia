-- Prove2me | solution 1 for AsymptoticOperator.isSelfAdjoint
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-10T17:11:50.731977+00:00
-- url     : https://prove2.me/submissions/880e5166-6140-4a5f-bee6-593c1130f851

import Theorems.Thm_AsymptoticOperator_graph_existsUnique
import Theorems.Thm_AsymptoticOperator_domain_eq
import Theorems.Thm_AsymptoticOperator_isSymmetric
import Theorems.Thm_AsymptoticOperator_inW12_of_forall_inner
import Theorems.Thm_AsymptoticOperator_inner_mul_symm
import Theorems.Thm_AsymptoticOperator_exists_coeff_eq_coeffMul
import Theorems.Thm_AsymptoticOperator_eq_zero_of_coeff_eq_zero
import Mathlib.MeasureTheory.SpecificCodomains.Pi

open MeasureTheory Matrix ConleyZehnder AsymptoticOperator

lemma ao4s_coeff_apply {n : ℕ} (f : L2 n) (k : ℤ) (i : Fin n ⊕ Fin n) :
    coeff f k i = fourierCoeff (fun t => ((f t i : ℝ) : ℂ)) k := by
  let L : Vec n →L[ℝ] (Fin n ⊕ Fin n → ℂ) :=
    ContinuousLinearMap.pi fun i => Complex.ofRealCLM.comp (EuclideanSpace.proj i)
  have hint : Integrable (fun t => complexify (f t)) (AddCircle.haarAddCircle : Measure UnitAddCircle) :=
    L.integrable_comp ((Lp.memLp f).integrable one_le_two)
  exact eval_integral (integrable_pi_iff.1 (hint.fourier_smul (-k))) i

lemma ao4s_coeff_sub {n : ℕ} (f g : L2 n) (k : ℤ) :
    coeff ((f - g : L2 n) : UnitAddCircle → Vec n) k = coeff f k - coeff g k := by
  funext i
  rw [Pi.sub_apply, ao4s_coeff_apply, ao4s_coeff_apply, ao4s_coeff_apply]
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

theorem solution {n : ℕ} (S : C(UnitAddCircle, Mat n)) (hS : IsSymLoop S) :
    IsSelfAdjoint (asymptoticOperator S) := by
  have hex := (graph_existsUnique S).exists
  have hgraph : ((asymptoticOperator S).graph : Set (L2 n × L2 n)) = graphSet S := by
    have hA : asymptoticOperator S = hex.choose := by
      unfold asymptoticOperator; rw [dif_pos hex]
    rw [hA]; exact hex.choose_spec
  have hdense := (domain_eq S).2
  have hdom := (domain_eq S).1
  set A := asymptoticOperator S with hAdef
  have hact : ∀ x : A.domain, IsAsymptoticAction S x (A x) := fun x => by
    have h := A.mem_graph x
    rw [← SetLike.mem_coe, hgraph] at h
    exact h
  rw [LinearPMap.isSelfAdjoint_def]
  have hle : A ≤ A.adjoint := (isSymmetric S hS).le_adjoint hdense
  have hadj := LinearPMap.adjoint_isFormalAdjoint hdense
  refine (LinearPMap.eq_of_le_of_domain_eq hle (le_antisymm hle.1 fun y hy => ?_)).symm
  set w := A.adjoint ⟨y, hy⟩ with hw
  obtain ⟨m', hm'⟩ := exists_coeff_eq_coeffMul S y
  have hkey := inW12_of_forall_inner y (w + m') fun f p hf hp => by
    have hfd : f ∈ A.domain := (hdom f).2 hf
    obtain ⟨m, hm⟩ := exists_coeff_eq_coeffMul S f
    have hAf := (hact ⟨f, hfd⟩).2
    have hpe : p = A ⟨f, hfd⟩ + m := by
      have h0 : p - m - A ⟨f, hfd⟩ = 0 := by
        apply eq_zero_of_coeff_eq_zero
        intro k
        rw [ao4s_coeff_sub, ao4s_coeff_sub, hp k, hm k, hAf k]
        abel
      rw [sub_sub, sub_eq_zero] at h0
      rw [h0, add_comm]
    rw [hpe, inner_add_left, inner_add_right, inner_mul_symm S hS f y m m' hm hm',
      real_inner_comm, ← hadj ⟨y, hy⟩ ⟨f, hfd⟩, real_inner_comm]
  have hyw : IsAsymptoticAction S y w := by
    refine ⟨hkey.1, fun k => ?_⟩
    have e : w = (w + m') - m' := (add_sub_cancel_right w m').symm
    rw [e, ao4s_coeff_sub, hkey.2 k, hm' k]
  have hmem : ((y, w) : L2 n × L2 n) ∈ A.graph := by
    rw [← SetLike.mem_coe, hgraph]
    exact hyw
  exact LinearPMap.mem_domain_of_mem_graph hmem
