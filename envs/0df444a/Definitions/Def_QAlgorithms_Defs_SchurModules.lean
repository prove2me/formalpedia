-- Prove2me | Definitions.Def_QAlgorithms_Defs_SchurModules
-- name    : QAlgorithms_Defs_SchurModules
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T18:41:10.466665+00:00
-- url     : https://prove2.me/theorems/300bc93f-620f-40da-b89f-2cfd32cca81b
-- title:
--   SchurModules
-- statement:
--   SchurModules
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\SchurModules.lean

import Definitions.Def_QAlgorithms_Defs_SpechtModules
import Definitions.Def_QAlgorithms_Defs_GradientMethods
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open scoped Matrix

namespace QAlgorithms.Schur

attribute [local instance] Classical.propDecidable

/-- The row-symmetrizer times column-antisymmetrizer on tensor space, using the
public cell numbering (1508.01797 pp.4-5, Young symmetrizer). This operator is
not asserted to be an orthogonal projector. -/
def tensorYoungOperator {d n : ℕ} (lambda : Partition d n) :
    Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ :=
  ∑ a ∈ rowPermutations lambda, ∑ b ∈ columnPermutations lambda,
    (((Equiv.Perm.sign b : ℤˣ) : ℤ) : ℂ) • tensorPermutation d n (a*b)

/-- The Schur module is the image of the tensor Young symmetrizer, with the
inner product inherited from tensor space (1508.01797 pp.4-5;
1508.01907 pp.4-5). This is one irreducible GL_d factor, not the full
lambda-isotypic component. -/
def schurModule {d n : ℕ} (lambda : Partition d n) :
    Submodule ℂ (EuclideanSpace ℂ (Fin n → Fin d)) :=
  LinearMap.range (Matrix.toEuclideanLin (tensorYoungOperator lambda))

/-- The homogeneous polynomial action of a d-by-d matrix on the constructed
Schur module, extended to singular matrices by the same tensor formula
(1508.01907 pp.4,7-8). The projection only supplies a subtype-valued expression:
tensor powers commute with the Young operator and preserve its image. -/
def polynomialRepresentation {d n : ℕ} (lambda : Partition d n)
    (A : Matrix (Fin d) (Fin d) ℂ) : schurModule lambda →ₗ[ℂ] schurModule lambda :=
  (schurModule lambda).orthogonalProjectionOnto.toLinearMap.comp
    ((Matrix.toEuclideanLin (piKron n A)).comp (schurModule lambda).subtype)

/-- The tensor word whose cell in row i carries alphabet symbol i, with
zero-based alphabet. Height at most d guarantees every symbol exists
(1508.01907 p.4, highest-weight tableau). -/
def highestWeightWord {d n : ℕ} (lambda : Partition d n) : Fin n → Fin d :=
  fun k =>
    let cell := (cellNumbering lambda).symm k
    ⟨cell.val.1, by
      have hcell : (cell.val.1,cell.val.2) ∈ lambda.val := cell.property
      have hleft : (cell.val.1,0) ∈ lambda.val :=
        lambda.val.up_left_mem (by rfl) (Nat.zero_le _) hcell
      exact (YoungDiagram.mem_iff_lt_colLen.mp hleft).trans_le lambda.property.2⟩

/-- The source normalized highest-weight vector: Young-symmetrize the row word
and divide by its Hilbert norm (1508.01907 pp.4,7). For the valid height-bounded
shape this vector is nonzero before normalization. Its phase is fixed by the
public symmetrizer; its rank-one operator is phase independent. -/
def highestWeightVector {d n : ℕ} (lambda : Partition d n) : schurModule lambda :=
  let raw : schurModule lambda :=
    ⟨act (tensorYoungOperator lambda) (ket (highestWeightWord lambda)),
      ⟨ket (highestWeightWord lambda),rfl⟩⟩
  ((‖raw‖⁻¹ : ℝ) : ℂ) • raw

/-- Empty tensor word has one basis vector and an identity Young action
(1508.01797 pp.4-5, tensor and permutation conventions). -/
theorem tensorYoung_zero {d : ℕ} (lambda : Partition d 0) : tensorYoungOperator lambda = 1 := by
  letI : Unique (Equiv.Perm (Fin 0)) := ⟨⟨1⟩,fun _ => Subsingleton.elim _ _⟩
  have hr : rowPermutations lambda = {1} := by
    ext pi
    have hp : pi = 1 := Subsingleton.elim _ _
    subst pi
    simp [rowPermutations]
  have hc : columnPermutations lambda = {1} := by
    ext pi
    have hp : pi = 1 := Subsingleton.elim _ _
    subst pi
    simp [columnPermutations]
  simp [tensorYoungOperator,hr,hc]
  ext y x
  rfl

/-- The zero-copy highest-weight state is the normalized unique empty tensor
(1508.01907 p.4, degree-zero representation convention). -/
example {d : ℕ} (lambda : Partition d 0) : ‖highestWeightVector lambda‖ = 1 := by
  change ‖normalizedVec (act (tensorYoungOperator lambda) (ket (highestWeightWord lambda)))‖ = 1
  rw [tensorYoung_zero]
  rw [show act (1 : Matrix (Fin 0 → Fin d) (Fin 0 → Fin d) ℂ)
    (ket (highestWeightWord lambda)) = ket (highestWeightWord lambda) by simp [act]]
  simp [normalizedVec,ket]

end QAlgorithms.Schur


