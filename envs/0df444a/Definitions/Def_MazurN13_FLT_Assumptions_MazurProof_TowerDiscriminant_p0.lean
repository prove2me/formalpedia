-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_TowerDiscriminant_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_TowerDiscriminant_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:14:45.089224+00:00
-- url     : https://prove2.me/theorems/be7d9170-42a2-447f-af6e-f3b2055d9ece
-- title:
--   FLT.Assumptions.MazurProof.TowerDiscriminant source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.TowerDiscriminant

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.TowerDiscriminant
Original leading source comments and nonproject imports are retained below. -/
import Mathlib.RingTheory.Discriminant
import Mathlib.Tactic.Ring

set_option autoImplicit false




/-!
# Discriminants of tower bases

For a tower `R → S → T`, the discriminant of the product basis is

`disc(b ⋅ c) = disc(b) ^ rank(c) * norm(disc(c))`.

The proof factors the trace matrix into a block-diagonal base trace matrix
and the left-multiplication representation of the relative trace matrix.
It is independent of any particular number field.
-/

open Matrix Module
open scoped Matrix

namespace MazurProof.TowerDiscriminant

noncomputable section

universe uR uS uT uι uκ

variable {R : Type uR} {S : Type uS} {T : Type uT}
variable [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra S T] [Algebra R T]
variable [IsScalarTower R S T]

variable {ι : Type uι} {κ : Type uκ}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype κ] [DecidableEq κ]

/-- A constant block-diagonal matrix has one determinant factor per block.
The sole reindexing changes `κ × ι`, used by `Matrix.comp`, to `ι × κ`,
used by `Matrix.blockDiagonal`. -/
private theorem det_comp_diagonal_const
    (A : Matrix ι ι R) :
    (Matrix.comp κ κ ι ι R
      (Matrix.diagonal fun _ : κ => A)).det =
      A.det ^ Fintype.card κ := by
  classical
  let M : Matrix (κ × ι) (κ × ι) R :=
    Matrix.comp κ κ ι ι R
      (Matrix.diagonal fun _ : κ => A)
  let e : κ × ι ≃ ι × κ := Equiv.prodComm κ ι
  change M.det = A.det ^ Fintype.card κ
  have hM :
      Matrix.reindex e e M =
        Matrix.blockDiagonal (fun _ : κ => A) := by
    ext ⟨i, k⟩ ⟨j, l⟩
    by_cases hkl : k = l <;>
      simp [M, e, Matrix.reindex_apply, Matrix.comp_apply,
        Matrix.blockDiagonal_apply, hkl]
  calc
    M.det = (Matrix.reindex e e M).det :=
      (Matrix.det_reindex_self e M).symm
    _ = (Matrix.blockDiagonal (fun _ : κ => A)).det := by
      rw [hM]
    _ = A.det ^ Fintype.card κ := by
      rw [Matrix.det_blockDiagonal]
      simp

/-- Exact trace-matrix factorization for the `κ × ι` ordering of a tower
basis. -/
private theorem traceMatrix_smulTower'_eq
    (b : Basis ι R S) (c : Basis κ S T) :
    Algebra.traceMatrix R (b.smulTower' c) =
      Matrix.comp κ κ ι ι R
          (Matrix.diagonal
            (fun _ : κ => Algebra.traceMatrix R b)) *
        Matrix.comp κ κ ι ι R
          ((Algebra.traceMatrix S c).map
            (Algebra.leftMulMatrix b)) := by
  classical
  ext ⟨k, i⟩ ⟨l, j⟩
  change
    Algebra.trace R T
        ((b.smulTower' c) (k, i) *
          (b.smulTower' c) (l, j)) = _
  rw [Basis.smulTower'_apply, Basis.smulTower'_apply]
  rw [← Algebra.trace_trace_of_basis b c]

  have hprod :
      (b i • c k) * (b j • c l) =
        (b i * b j) • (c k * c l) := by
    simp only [Algebra.smul_def, map_mul]
    ring

  have hrel :
      Algebra.trace S T ((b i • c k) * (b j • c l)) =
        (b i * b j) * Algebra.trace S T (c k * c l) := by
    calc
      Algebra.trace S T ((b i • c k) * (b j • c l)) =
          Algebra.trace S T ((b i * b j) • (c k * c l)) := by
            rw [hprod]
      _ = (b i * b j) • Algebra.trace S T (c k * c l) :=
        (Algebra.trace S T).map_smul
          (b i * b j) (c k * c l)
      _ = (b i * b j) * Algebra.trace S T (c k * c l) := by
        simp

  rw [hrel]
  simp only [Matrix.mul_apply, Matrix.comp_apply,
    Matrix.map_apply, Matrix.diagonal_apply,
    ← Finset.univ_product_univ, Finset.sum_product]
  rw [Fintype.sum_eq_single k]
  · simp only [if_pos]
    have hmul := congrFun
      (Algebra.traceMatrix_of_basis_mulVec b
        (Algebra.trace S T (c k * c l) * b j)) i
    simpa [Matrix.mulVec, dotProduct,
      Algebra.leftMulMatrix_eq_repr_mul,
      Basis.equivFun_apply, Algebra.traceMatrix_apply,
      Algebra.traceForm_apply, mul_assoc, mul_comm,
      mul_left_comm] using hmul.symm
  · intro k' hk'
    simp [hk'.symm]

/-- Tower-discriminant formula in the `κ × ι` ordering used internally by
the block matrices. -/
theorem discr_smulTower'
    (b : Basis ι R S) (c : Basis κ S T) :
    Algebra.discr R (b.smulTower' c) =
      Algebra.discr R b ^ Fintype.card κ *
        Algebra.norm R (Algebra.discr S c) := by
  classical
  change
    (Algebra.traceMatrix R (b.smulTower' c)).det =
      (Algebra.traceMatrix R b).det ^ Fintype.card κ *
        Algebra.norm R (Algebra.traceMatrix S c).det
  rw [traceMatrix_smulTower'_eq b c, Matrix.det_mul,
    det_comp_diagonal_const]
  have hdet :
      (Matrix.comp κ κ ι ι R
        ((Algebra.traceMatrix S c).map
          (Algebra.leftMulMatrix b))).det =
        (Algebra.leftMulMatrix b
          (Algebra.traceMatrix S c).det).det := by
    simpa using
      (Matrix.det_det
        (M := Algebra.traceMatrix S c)
        (Algebra.leftMulMatrix b).toRingHom).symm
  rw [hdet, ← Algebra.norm_eq_matrix_det b
    (Algebra.traceMatrix S c).det]

/-- Discriminant of the standard `ι × κ` tower basis. -/
theorem discr_smulTower
    (b : Basis ι R S) (c : Basis κ S T) :
    Algebra.discr R (b.smulTower c) =
      Algebra.discr R b ^ Fintype.card κ *
        Algebra.norm R (Algebra.discr S c) := by
  classical
  calc
    Algebra.discr R (b.smulTower c) =
        Algebra.discr R (b.smulTower' c) := by
      symm
      simpa [Basis.smulTower'] using
        (Algebra.discr_reindex R
          (b.smulTower c) (Equiv.prodComm ι κ))
    _ = Algebra.discr R b ^ Fintype.card κ *
          Algebra.norm R (Algebra.discr S c) :=
      discr_smulTower' b c

end

end MazurProof.TowerDiscriminant


