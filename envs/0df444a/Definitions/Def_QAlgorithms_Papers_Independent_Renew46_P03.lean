-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P03
-- name    : QAlgorithms_Papers_Independent_Renew46_P03
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T21:49:48.341997+00:00
-- url     : https://prove2.me/theorems/0289f4c4-53a1-4603-976e-db2cb6c6e7df
-- title:
--   Definitions for Operator Isomorphisms on Hilbert Space Tensor Products
-- statement:
--   The objects the formalized statements of *Operator Isomorphisms on Hilbert Space Tensor Products* (arXiv:2010.15901) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `IsConjugation`: PDF p.3: a bounded anti-linear map is a conjugation when it fixes some complete countable orthonormal basis. No involution or isometry is assumed.
--   - `IsAntilinearAdjoint`: PDF p.4: the defining pairing for the anti-linear adjoint. This is distinct from the adjoint of a complex-linear operator.
--   - `tensorVector`: PDF p.8: a simple tensor in the completed Hilbert tensor product.
--   - `tensorInsertion`: PDF p.8: the bounded insertion y ↦ x tensor y, constructed from the algebraic tensor map and its norm estimate.
--   - `tensorSlice`: PDF p.8: the tensor slice in direction x, computed as the Hilbert adjoint of insertion. The series specification on the page is included explicitly in tensor_slice_formulas, rather than assumed in this construction.
--   - `completedTensorAction`: PDF p.9: the tensor action of bounded operators, continuously extended from the algebraic tensor product to its Hilbert completion.
--   - `finiteVectorization`: Equation (2.1), PDF p.9: the finite-dimensional version of the independently defined one-basis series T_B, now a finite sum on all bounded operators.
--   - `unnormalizedBasisTensor`: PDF p.9: phi_plus is unnormalized, with no dimension factor.
-- source:
--   Operator Isomorphisms on Hilbert Space Tensor Products, arXiv:2010.15901v1, https://arxiv.org/abs/2010.15901v1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P34

/-!
Statements from S. Gudder, *Operator Isomorphisms on Hilbert Space Tensor Products*,
arXiv:2010.15901v1. The conjugations below are bounded conjugate-linear maps,
as required by the infinite-series step in the proof of Lemma 1.3.
Hilbert–Schmidt dependent nodes are explicitly deferred in the unit artifacts.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P03

universe u v

open QAlgorithms.Papers.Independent.Claimed50.P34 (HilbertTensor)

/-- PDF p.3: a bounded anti-linear map is a conjugation when it fixes some
complete countable orthonormal basis. No involution or isometry is assumed. -/
def IsConjugation {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (K : H →L⋆[ℂ] H) : Prop :=
  ∃ (ι : Type u) (_ : Countable ι) (b : HilbertBasis ι ℂ H), ∀ i, K (b i) = b i

/-- PDF p.4: the defining pairing for the anti-linear adjoint. This is distinct
from the adjoint of a complex-linear operator. -/
def IsAntilinearAdjoint {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (K L : H →L⋆[ℂ] H) : Prop :=
  ∀ x y : H, inner ℂ (L x) y = inner ℂ (K y) x

/-- PDF p.8: a simple tensor in the completed Hilbert tensor product. -/
def tensorVector {H1 : Type u} {H2 : Type v}
    [NormedAddCommGroup H1] [InnerProductSpace ℂ H1]
    [NormedAddCommGroup H2] [InnerProductSpace ℂ H2]
    (x : H1) (y : H2) : HilbertTensor H1 H2 :=
  (UniformSpace.Completion.toComplL (𝕜 := ℂ) (E := TensorProduct ℂ H1 H2)) (TensorProduct.tmul ℂ x y)

/-- PDF p.8: the bounded insertion y ↦ x tensor y, constructed from the
algebraic tensor map and its norm estimate. -/
def tensorInsertion {H1 : Type u} {H2 : Type v}
    [NormedAddCommGroup H1] [InnerProductSpace ℂ H1]
    [NormedAddCommGroup H2] [InnerProductSpace ℂ H2]
    (x : H1) : H2 →L[ℂ] HilbertTensor H1 H2 :=
  (UniformSpace.Completion.toComplL (𝕜 := ℂ) (E := TensorProduct ℂ H1 H2)).comp
    ((TensorProduct.mk ℂ H1 H2 x).mkContinuous ‖x‖
      (fun y => le_of_eq (TensorProduct.norm_tmul x y)))

/-- PDF p.8: the tensor slice in direction x, computed as the Hilbert adjoint
of insertion. The series specification on the page is included explicitly
in tensor_slice_formulas, rather than assumed in this construction. -/
def tensorSlice {H1 : Type u} {H2 : Type v}
    [NormedAddCommGroup H1] [InnerProductSpace ℂ H1]
    [NormedAddCommGroup H2] [InnerProductSpace ℂ H2] [CompleteSpace H2]
    (x : H1) : HilbertTensor H1 H2 →L[ℂ] H2 :=
  (tensorInsertion (H2 := H2) x).adjoint

/-- PDF p.9: the tensor action of bounded operators, continuously extended
from the algebraic tensor product to its Hilbert completion. -/
def completedTensorAction {H1 : Type u} {H2 : Type v}
    [NormedAddCommGroup H1] [InnerProductSpace ℂ H1]
    [NormedAddCommGroup H2] [InnerProductSpace ℂ H2]
    (A : H1 →L[ℂ] H1) (B : H2 →L[ℂ] H2) :
    HilbertTensor H1 H2 →L[ℂ] HilbertTensor H1 H2 :=
  ((UniformSpace.Completion.toComplL (𝕜 := ℂ) (E := TensorProduct ℂ H1 H2)).comp (TensorProduct.mapL A B)).extend
    (UniformSpace.Completion.toComplL (𝕜 := ℂ) (E := TensorProduct ℂ H1 H2))

/-- Equation (2.1), PDF p.9: the finite-dimensional version of the independently
defined one-basis series T_B, now a finite sum on all bounded operators. -/
def finiteVectorization {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ H) (A : H →L[ℂ] H) :
    HilbertTensor H H :=
  ∑ j, tensorVector (b j) (A (b j))

/-- PDF p.9: phi_plus is unnormalized, with no dimension factor. -/
def unnormalizedBasisTensor {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ H) : HilbertTensor H H :=
  ∑ j, tensorVector (b j) (b j)

section Sanity

/-! Small sanity examples for the local definitions. -/

example : IsConjugation
    (0 : lp (fun _ : PEmpty => ℂ) 2 →L⋆[ℂ] lp (fun _ : PEmpty => ℂ) 2) := by
  refine ⟨PEmpty, inferInstance, default, ?_⟩
  intro i
  exact PEmpty.elim i

example {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    IsAntilinearAdjoint (0 : H →L⋆[ℂ] H) 0 := by
  intro x y
  simp

example {H1 : Type u} {H2 : Type v}
    [NormedAddCommGroup H1] [InnerProductSpace ℂ H1]
    [NormedAddCommGroup H2] [InnerProductSpace ℂ H2] (x : H1) (y : H2) :
    tensorInsertion x y = tensorVector x y := rfl

example {H1 : Type u} {H2 : Type v}
    [NormedAddCommGroup H1] [InnerProductSpace ℂ H1]
    [NormedAddCommGroup H2] [InnerProductSpace ℂ H2] (x : H1) :
    tensorVector x (0 : H2) = 0 := by
  simp [tensorVector]

example {H1 : Type u} {H2 : Type v}
    [NormedAddCommGroup H1] [InnerProductSpace ℂ H1]
    [NormedAddCommGroup H2] [InnerProductSpace ℂ H2] [CompleteSpace H2] (x : H1) :
    tensorSlice (H2 := H2) x 0 = 0 := map_zero _

example {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (b : OrthonormalBasis (Fin 0) ℂ H) (A : H →L[ℂ] H) :
    finiteVectorization b A = 0 ∧ unnormalizedBasisTensor b = 0 := by
  simp [finiteVectorization, unnormalizedBasisTensor]

example {H1 : Type u} {H2 : Type v}
    [NormedAddCommGroup H1] [InnerProductSpace ℂ H1]
    [NormedAddCommGroup H2] [InnerProductSpace ℂ H2]
    (A : H1 →L[ℂ] H1) (B : H2 →L[ℂ] H2) :
    completedTensorAction A B 0 = 0 := map_zero _

end Sanity

end QAlgorithms.Papers.Independent.Renew46.P03


