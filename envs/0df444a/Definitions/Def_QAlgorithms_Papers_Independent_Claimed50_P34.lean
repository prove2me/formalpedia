-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P34
-- name    : QAlgorithms_Papers_Independent_Claimed50_P34
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T12:49:46.676545+00:00
-- url     : https://prove2.me/theorems/6ed72748-a152-421d-9963-99c248a45d82
-- title:
--   Definitions for On the relation between states and maps in infinite dimensions
-- statement:
--   The objects the formalized statements of *On the relation between states and maps in infinite dimensions* (arXiv:0706.2617) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `HilbertTensor`: PDF p.7: the completed Hilbert tensor product, with the inner product on the algebraic tensor product supplied by Mathlib before taking completion. This definition alone does not identify the completion with actual operators.
--   - `FourTensor`: PDF pp.5–6: four tensor-factor coefficients in orthonormal primal/dual bases. The tensor norm is the Euclidean norm, equal to the trace Hilbert–Schmidt norm. Slot polarity is specified at each use, rather than identifying a space with its dual.
--   - `dualMatrix`: PDF p.4, equation (3): matrix of the conjugate action on the dual basis. This is entrywise conjugation, with neither transpose nor inverse.
--   - `factorAction`: PDF p.6, equation (17): independent actions on four factor slots, extended linearly from simple tensors. Pass dualMatrix for a conjugate-dual slot.
--   - `jamiolkowskiTensor`: PDF p.6, equations (12)–(13): J swaps the second and fourth slots. Source slots: H1, H1*, H2, H2*. Target slots: H1, H2*, H2, H1*. Reuse the pinned unnormalized reshuffle with explicit coordinate regrouping. The frozen Frontier18.P17.jamiolkowski instead divides by the input dimension; that normalized state correspondence is not the unitary tensor map here.
--   - `twistedJamiolkowski`: PDF p.6, equations (15)–(16): the twisted factor permutation. Source slots: H1, H1*, H2, H2*. Target slots: H1, H2, H2*, H1*.
-- source:
--   On the relation between states and maps in infinite dimensions, arXiv:0706.2617v1, https://arxiv.org/abs/0706.2617v1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P17

/-!
arXiv:0706.2617v1, Grabowski–Kus–Marmo.
The finite-dimensional statement uses the four-factor tensor realization of
Definition 1, equations (12)–(17). Primal and dual coordinate slots have distinct
roles: dual actions use entrywise conjugation, and no Riesz map is made linear.
The infinite-dimensional operator realization is explicitly deferred in HARD.md.
The completed tensor definition below is only partial infrastructure for it.
Compilation and independent moderation are pending the batch handoff.
-/

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Claimed50.P34

/-- PDF p.7: the completed Hilbert tensor product, with the inner product
on the algebraic tensor product supplied by Mathlib before taking completion.
This definition alone does not identify the completion with actual operators. -/
abbrev HilbertTensor (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] :=
  UniformSpace.Completion (TensorProduct ℂ E F)

/-- Sanity: Mathlib's simple tensor with a zero factor remains zero in completion.
No paper-local simple-tensor definition or identification with operators is needed. -/
example {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] (y : F) :
    ((TensorProduct.tmul ℂ (0 : E) y : TensorProduct ℂ E F) : HilbertTensor E F) = 0 := by
  simp

/-- PDF pp.5–6: four tensor-factor coefficients in orthonormal primal/dual bases.
The tensor norm is the Euclidean norm, equal to the trace Hilbert–Schmidt norm.
Slot polarity is specified at each use, rather than identifying a space with its dual. -/
abbrev FourTensor (a b c d : ℕ) :=
  EuclideanSpace ℂ (Fin a × Fin b × Fin c × Fin d)

/-- PDF p.4, equation (3): matrix of the conjugate action on the dual basis.
This is entrywise conjugation, with neither transpose nor inverse. -/
def dualMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun i j => star (A i j)

/-- PDF p.6, equation (17): independent actions on four factor slots, extended
linearly from simple tensors. Pass dualMatrix for a conjugate-dual slot. -/
def factorAction {a b c d : ℕ}
    (A : Matrix (Fin a) (Fin a) ℂ) (B : Matrix (Fin b) (Fin b) ℂ)
    (C : Matrix (Fin c) (Fin c) ℂ) (D : Matrix (Fin d) (Fin d) ℂ)
    (v : FourTensor a b c d) : FourTensor a b c d :=
  WithLp.toLp 2 (fun p =>
    ∑ q : Fin a × Fin b × Fin c × Fin d,
      (A p.1 q.1 * B p.2.1 q.2.1 * C p.2.2.1 q.2.2.1 *
        D p.2.2.2 q.2.2.2) * v q)

/-- PDF p.6, equations (12)–(13): J swaps the second and fourth slots.
Source slots: H1, H1*, H2, H2*. Target slots: H1, H2*, H2, H1*.
Reuse the pinned unnormalized reshuffle with explicit coordinate regrouping.
The frozen Frontier18.P17.jamiolkowski instead divides by the input dimension;
that normalized state correspondence is not the unitary tensor map here. -/
def jamiolkowskiTensor {n m : ℕ} : FourTensor n n m m →ₗ[ℂ] FourTensor n m m n where
  toFun v := WithLp.toLp 2 (fun p =>
    QAlgorithms.Papers.Independent.Frontier18.P17.reshuffle
      (fun (r s : Fin n × Fin m) => v (r.1, s.1, r.2, s.2))
      (p.1, p.2.2.2) (p.2.2.1, p.2.1))
  map_add' v w := by ext p; rfl
  map_smul' z v := by ext p; rfl

/-- PDF p.6, equations (15)–(16): the twisted factor permutation.
Source slots: H1, H1*, H2, H2*. Target slots: H1, H2, H2*, H1*. -/
def twistedJamiolkowski {n m : ℕ} :
    FourTensor n n m m →ₗ[ℂ] FourTensor n m m n where
  toFun v := WithLp.toLp 2 (fun p => v (p.1, p.2.2.2, p.2.1, p.2.2.1))
  map_add' v w := by ext p; rfl
  map_smul' z v := by ext p; rfl

/-- Sanity: dual coordinates conjugate a scalar, rather than invert it. -/
example (z : ℂ) : dualMatrix (fun (_ : Fin 1) (_ : Fin 1) => z) 0 0 = star z := rfl

/-- Sanity: the canonical four-factor action kills tensors if one factor map is zero. -/
example {a b c d : ℕ} (B : Matrix (Fin b) (Fin b) ℂ)
    (C : Matrix (Fin c) (Fin c) ℂ) (D : Matrix (Fin d) (Fin d) ℂ)
    (v : FourTensor a b c d) : factorAction 0 B C D v = 0 := by
  ext p
  simp [factorAction]

/-- Sanity: neither permutation introduces a normalization in dimension one. -/
example (v : FourTensor 1 1 1 1) :
    jamiolkowskiTensor v (0, 0, 0, 0) = v (0, 0, 0, 0) ∧
      twistedJamiolkowski v (0, 0, 0, 0) = v (0, 0, 0, 0) := ⟨rfl, rfl⟩

end QAlgorithms.Papers.Independent.Claimed50.P34


