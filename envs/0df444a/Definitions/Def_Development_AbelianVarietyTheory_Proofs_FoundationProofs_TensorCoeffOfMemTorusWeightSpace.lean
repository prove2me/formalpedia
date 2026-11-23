-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_TensorCoeffOfMemTorusWeightSpace
-- name    : Development_AbelianVarietyTheory_Proofs_FoundationProofs_TensorCoeffOfMemTorusWeightSpace
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:02:22.445235+00:00
-- url     : https://prove2.me/theorems/a2ac238b-bab7-4a7c-ac8a-f71da97a2a5c
-- title:
--   Tensor Coeff Of Mem Torus Weight Space
-- statement:
--   Definitions and structural lemmas for Tensor Coeff Of Mem Torus Weight Space, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/TensorCoeffOfMemTorusWeightSpace.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsLeftCoactionIffIsCoactionComm
import Theorems.Thm_GlobalTheory_IsCoaction_injective
import Theorems.Thm_GlobalTheory_IsCoaction_rid_counit
import Theorems.Thm_GlobalTheory_mem_coactionWeightSpace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.mem_coactionWeightSpace


set_option autoImplicit false
open TensorProduct Coalgebra AddMonoidAlgebra DirectSum
namespace GlobalTheory
variable {R : Type*} [CommSemiring R] {X : Type*}
variable {M : Type*} [AddCommMonoid M] [Module R M] {M' : Type*} [AddCommMonoid M'] [Module R M']
variable (R M) in

noncomputable def tensorCoeff (x : X) : M ⊗[R] R[X] →ₗ[R] M :=
  (TensorProduct.rid R M).toLinearMap ∘ₗ
    (Finsupp.lapply x ∘ₗ (coeffLinearEquiv R : R[X] ≃ₗ[R] X →₀ R).toLinearMap).lTensor M
@[simp] theorem tensorCoeff_tmul (x : X) (m : M) (p : R[X]) :
    tensorCoeff R M x (m ⊗ₜ p) = p.coeff x • m := by
  simp [tensorCoeff]
theorem tensorCoeff_tmul_single_one [DecidableEq X] (x y : X) (m : M) :
    tensorCoeff R M x (m ⊗ₜ single y 1) = if y = x then m else 0 := by
  simp [Finsupp.single_apply]
theorem exists_eq_sum_tensorCoeff (t : M ⊗[R] R[X]) :
    ∃ s : Finset X, (∀ x ∉ s, tensorCoeff R M x t = 0) ∧
      t = ∑ x ∈ s, tensorCoeff R M x t ⊗ₜ[R] single x (1 : R) := by
  classical
  let E : M ⊗[R] R[X] ≃ₗ[R] X →₀ M :=
    (coeffLinearEquiv R : R[X] ≃ₗ[R] X →₀ R).lTensor M ≪≫ₗ finsuppScalarRight R R M X
  have hE : ∀ t x, E t x = tensorCoeff R M x t := by
    intro t x
    induction t with
    | zero => simp
    | add a b ha hb => simp [ha, hb]
    | tmul m p => simp [E, finsuppScalarRight_apply_tmul_apply]
  refine ⟨(E t).support, fun x hx => by rw [← hE]; simpa using hx, E.injective ?_⟩
  ext y
  rw [map_sum, Finsupp.finsetSum_apply]
  simp only [hE, tensorCoeff_tmul_single_one]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [← hE]; simpa using h
theorem tensorCoeff_ext {t t' : M ⊗[R] R[X]}
    (h : ∀ x, tensorCoeff R M x t = tensorCoeff R M x t') : t = t' := by
  classical
  obtain ⟨s, hs, e⟩ := exists_eq_sum_tensorCoeff t
  obtain ⟨s', hs', e'⟩ := exists_eq_sum_tensorCoeff t'
  refine e.trans (Eq.trans ?_ e'.symm)
  rw [Finset.sum_subset (Finset.subset_union_left (s₁ := s) (s₂ := s'))
      (fun x _ hx => by simp [hs x hx]),
    Finset.sum_subset (Finset.subset_union_right (s₁ := s) (s₂ := s'))
      (fun x _ hx => by simp [hs' x hx])]
  simp only [h]
noncomputable abbrev torusWeightSpace (ρ : M →ₗ[R] M ⊗[R] R[X]) (x : X) : Submodule R M :=
  coactionWeightSpace ρ (single x 1)
theorem IsCoaction.tensorCoeff_mem {ρ : M →ₗ[R] M ⊗[R] R[X]} (h : IsCoaction ρ) (x : X) (m : M) :
    tensorCoeff R M x (ρ m) ∈ torusWeightSpace ρ x := by
  classical
  have h1 : ∀ t : M ⊗[R] R[X], tensorCoeff R (M ⊗[R] R[X]) x (ρ.rTensor _ t) =
      ρ (tensorCoeff R M x t) := by
    intro t
    induction t with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul m p => simp
  have h2 : ∀ t : M ⊗[R] R[X], tensorCoeff R (M ⊗[R] R[X]) x
      ((TensorProduct.assoc R M R[X] R[X]).symm ((comul (R := R)).lTensor M t)) =
      tensorCoeff R M x t ⊗ₜ single x 1 := by
    intro t
    induction t with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb, add_tmul]
    | tmul m p =>
      induction p using AddMonoidAlgebra.induction_linear with
      | zero => simp
      | add a b ha hb => simp only [tmul_add, map_add, ha, hb, add_tmul]
      | single y r =>
        by_cases hy : y = x
        · subst hy; simp [smul_tmul']
        · simp [hy]
  rw [mem_coactionWeightSpace, ← h1, ← h2, ← h.coassoc, LinearEquiv.symm_apply_apply]
theorem IsCoaction.exists_eq_sum {ρ : M →ₗ[R] M ⊗[R] R[X]} (h : IsCoaction ρ) (m : M) :
    ∃ s : Finset X, m = ∑ x ∈ s, tensorCoeff R M x (ρ m) := by
  obtain ⟨s, -, e⟩ := exists_eq_sum_tensorCoeff (ρ m)
  refine ⟨s, ?_⟩
  conv_lhs => rw [← h.rid_counit m, e]
  simp
variable [DecidableEq X]
theorem tensorCoeff_of_mem_torusWeightSpace {ρ : M →ₗ[R] M ⊗[R] R[X]} {y : X} {m : M}
    (hm : m ∈ torusWeightSpace ρ y) (x : X) :
    tensorCoeff R M x (ρ m) = if y = x then m else 0 := by
  rw [mem_coactionWeightSpace.1 hm, tensorCoeff_tmul_single_one]
theorem IsCoaction.isInternal_torusWeightSpace {ρ : M →ₗ[R] M ⊗[R] R[X]} (h : IsCoaction ρ) :
    IsInternal (torusWeightSpace ρ) := by
  have key : ∀ (z : ⨁ x, torusWeightSpace ρ x) (x : X),
      tensorCoeff R M x (ρ (DirectSum.coeAddMonoidHom _ z)) = z x := by
    intro z x
    induction z using DirectSum.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb, DirectSum.add_apply, Submodule.coe_add]
    | of y m =>
      rw [coeAddMonoidHom_of, tensorCoeff_of_mem_torusWeightSpace m.2]
      split_ifs with hy
      · subst hy; simp
      · rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm hy)]; rfl
  refine ⟨fun z z' e => ?_, fun m => ?_⟩
  · ext x
    rw [← key, e, key]
  · obtain ⟨s, e⟩ := h.exists_eq_sum m
    refine ⟨∑ x ∈ s, DirectSum.of (fun x => torusWeightSpace ρ x) x ⟨_, h.tensorCoeff_mem x m⟩, ?_⟩
    rw [map_sum]
    simp only [coeAddMonoidHom_of]
    exact e.symm
@[instance_reducible]
noncomputable def IsCoaction.decomposition {ρ : M →ₗ[R] M ⊗[R] R[X]} (h : IsCoaction ρ) :
    Decomposition (torusWeightSpace ρ) :=
  h.isInternal_torusWeightSpace.chooseDecomposition
theorem coe_decompose_torusWeightSpace (ρ : M →ₗ[R] M ⊗[R] R[X])
    [Decomposition (torusWeightSpace ρ)] (m : M) (x : X) :
    (decompose (torusWeightSpace ρ) m x : M) = tensorCoeff R M x (ρ m) := by
  induction m using Decomposition.inductionOn (torusWeightSpace ρ) with
  | zero => simp
  | add a b ha hb =>
    simp only [decompose_add, map_add, ← ha, ← hb, DirectSum.add_apply, Submodule.coe_add]
  | @homogeneous y m =>
    rw [tensorCoeff_of_mem_torusWeightSpace m.2]
    split_ifs with hy
    · subst hy; exact decompose_of_mem_same _ m.2
    · exact decompose_of_mem_ne _ m.2 hy
noncomputable def gradingCoaction (ℳ : X → Submodule R M) [Decomposition ℳ] :
    M →ₗ[R] M ⊗[R] R[X] :=
  DirectSum.toModule R X _
      (fun x => (TensorProduct.mk R M R[X]).flip (single x 1) ∘ₗ (ℳ x).subtype) ∘ₗ
    (decomposeLinearEquiv ℳ).toLinearMap
theorem gradingCoaction_of_mem (ℳ : X → Submodule R M) [Decomposition ℳ] {x : X} {m : M}
    (hm : m ∈ ℳ x) : gradingCoaction ℳ m = m ⊗ₜ single x 1 := by
  lift m to ℳ x using hm
  simp [gradingCoaction]
theorem tensorCoeff_gradingCoaction (ℳ : X → Submodule R M) [Decomposition ℳ] (m : M) (x : X) :
    tensorCoeff R M x (gradingCoaction ℳ m) = decompose ℳ m x := by
  induction m using Decomposition.inductionOn ℳ with
  | zero => simp
  | add a b ha hb =>
    simp only [decompose_add, map_add, ha, hb, DirectSum.add_apply, Submodule.coe_add]
  | @homogeneous y m =>
    rw [gradingCoaction_of_mem ℳ m.2, tensorCoeff_tmul_single_one]
    split_ifs with hy
    · subst hy; exact (decompose_of_mem_same _ m.2).symm
    · exact (decompose_of_mem_ne _ m.2 hy).symm
theorem isCoaction_gradingCoaction (ℳ : X → Submodule R M) [Decomposition ℳ] :
    IsCoaction (gradingCoaction ℳ) where
  coassoc m := by
    induction m using Decomposition.inductionOn ℳ with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | homogeneous m => simp [gradingCoaction_of_mem ℳ m.2]
  counit m := by
    induction m using Decomposition.inductionOn ℳ with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb, add_tmul]
    | homogeneous m => simp [gradingCoaction_of_mem ℳ m.2]
@[simp] theorem torusWeightSpace_gradingCoaction (ℳ : X → Submodule R M) [Decomposition ℳ] :
    torusWeightSpace (gradingCoaction ℳ) = ℳ := by
  ext x m
  refine ⟨fun hm => ?_, fun hm => gradingCoaction_of_mem ℳ hm⟩
  have := tensorCoeff_of_mem_torusWeightSpace hm x
  rw [if_pos rfl, tensorCoeff_gradingCoaction] at this
  exact this ▸ (decompose ℳ m x).2
@[simp] theorem gradingCoaction_torusWeightSpace (ρ : M →ₗ[R] M ⊗[R] R[X])
    [Decomposition (torusWeightSpace ρ)] : gradingCoaction (torusWeightSpace ρ) = ρ := by
  refine LinearMap.ext fun m => tensorCoeff_ext fun x => ?_
  rw [tensorCoeff_gradingCoaction, coe_decompose_torusWeightSpace]
variable (R X M) in

noncomputable def coactionEquivGrading :
    {ρ : M →ₗ[R] M ⊗[R] R[X] // IsCoaction ρ} ≃ {ℳ : X → Submodule R M // IsInternal ℳ} where
  toFun ρ := ⟨torusWeightSpace ρ.1, ρ.2.isInternal_torusWeightSpace⟩
  invFun ℳ := letI := ℳ.2.chooseDecomposition; ⟨gradingCoaction ℳ.1, isCoaction_gradingCoaction _⟩
  left_inv ρ := Subtype.ext (by
    letI := ρ.2.decomposition
    exact gradingCoaction_torusWeightSpace ρ.1)
  right_inv ℳ := Subtype.ext (by
    letI := ℳ.2.chooseDecomposition
    exact torusWeightSpace_gradingCoaction ℳ.1)
section Algebra
variable [AddMonoid X] {A : Type*} [Semiring A] [Algebra R A]
omit [DecidableEq X] in

instance gradedMonoid_torusWeightSpace (ρ : A →ₐ[R] A ⊗[R] R[X]) :
    SetLike.GradedMonoid (torusWeightSpace ρ.toLinearMap) where
  one_mem := by
    rw [mem_coactionWeightSpace, AlgHom.toLinearMap_apply, map_one]; rfl
  mul_mem x y a b ha hb := by
    rw [mem_coactionWeightSpace, AlgHom.toLinearMap_apply] at ha hb ⊢
    rw [map_mul, ha, hb, Algebra.TensorProduct.tmul_mul_tmul, single_mul_single, _root_.mul_one]
@[instance_reducible]
noncomputable def IsCoaction.gradedAlgebra {ρ : A →ₐ[R] A ⊗[R] R[X]}
    (h : IsCoaction ρ.toLinearMap) : GradedAlgebra (torusWeightSpace ρ.toLinearMap) :=
  { gradedMonoid_torusWeightSpace ρ, h.decomposition with }
noncomputable def gradingCoactionAlgHom (𝒜 : X → Submodule R A) [GradedAlgebra 𝒜] :
    A →ₐ[R] A ⊗[R] R[X] :=
  AlgHom.ofLinearMap (gradingCoaction 𝒜)
    (gradingCoaction_of_mem 𝒜 (SetLike.one_mem_graded 𝒜))
    (fun a b => by
      induction a using Decomposition.inductionOn 𝒜 with
      | zero => simp
      | add a a' ha ha' => simp only [add_mul, map_add, ha, ha']
      | homogeneous a =>
        induction b using Decomposition.inductionOn 𝒜 with
        | zero => simp
        | add b b' hb hb' => simp only [mul_add, map_add, hb, hb']
        | homogeneous b =>
          rw [gradingCoaction_of_mem 𝒜 a.2, gradingCoaction_of_mem 𝒜 b.2,
            gradingCoaction_of_mem 𝒜 (SetLike.mul_mem_graded a.2 b.2),
            Algebra.TensorProduct.tmul_mul_tmul, single_mul_single, _root_.mul_one])
@[simp] theorem gradingCoactionAlgHom_toLinearMap (𝒜 : X → Submodule R A) [GradedAlgebra 𝒜] :
    (gradingCoactionAlgHom 𝒜).toLinearMap = gradingCoaction 𝒜 := rfl
variable (R X A) in

noncomputable def algCoactionEquivGrading :
    {ρ : A →ₐ[R] A ⊗[R] R[X] // IsCoaction ρ.toLinearMap} ≃
      {𝒜 : X → Submodule R A // Nonempty (GradedAlgebra 𝒜)} where
  toFun ρ := ⟨torusWeightSpace ρ.1.toLinearMap, ⟨ρ.2.gradedAlgebra⟩⟩
  invFun 𝒜 := letI := 𝒜.2.some; ⟨gradingCoactionAlgHom 𝒜.1, isCoaction_gradingCoaction _⟩
  left_inv ρ := Subtype.ext (AlgHom.toLinearMap_injective (by
    letI := (⟨ρ.2.gradedAlgebra⟩ : Nonempty _).some
    exact gradingCoaction_torusWeightSpace ρ.1.toLinearMap))
  right_inv 𝒜 := Subtype.ext (by
    letI := 𝒜.2.some
    exact torusWeightSpace_gradingCoaction 𝒜.1)
end Algebra
end GlobalTheory


