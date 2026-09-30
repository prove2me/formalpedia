-- Prove2me | Definitions.Def_TauCeti_LinearAlgebra_Pi
-- name    : TauCeti_LinearAlgebra_Pi
-- status  : Definition
-- author  : @riccardo.brasca
-- created : 2026-09-29T19:36:42.528047+00:00
-- url     : https://prove2.me/theorems/a7c47841-66a0-4d74-89f7-9401b511c437
-- title:
--   Coordinate separation, supports, splittings and determinants of dependent products
-- statement:
--   For a finite family of finite free modules over a commutative ring and coordinatewise endomorphisms $f_i$, the determinant of their product endomorphism is
--
--   $$
--   \det\Bigl(\prod_i f_i\Bigr)=\prod_i\det(f_i).
--   $$
--
--   This relates product decompositions to algebraic norms.
--
--   **Formalization Note.** These foundational declarations are transplanted from the Tau Ceti contributors' [original source](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/LinearAlgebra/Pi.lean) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`), with compatibility adaptations for Lean 4.33.1. Mathematical proofs requiring separate theorem nodes are published separately.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/LinearAlgebra/Pi.lean

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Pi

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Coordinate separation, supports, splittings and determinants of dependent products

Distinct sums and differences of standard coordinate vectors can be separated at a coordinate
where their difference is regular. Two of these separations compare families that agree after
doubling, so they assume `2` is regular; separating two unordered sums needs no such hypothesis.
These elementary facts are useful for identifying root spaces from their coordinate weights.

For `s : Set ι`, the submodule `Submodule.pi sᶜ (fun _ ↦ ⊥)` of `ι → M` consists of the families
vanishing outside `s` — the `Pi` analogue of `Finsupp.supported`. This file records that
complementary supports meet in `⊥`. It also records the linear splitting of a dependent product
along a predicate on the indices, the linear splitting of a `Fin (n + 1)`-indexed product into its
initial segment and its last coordinate, and the determinant of a coordinatewise endomorphism of a
finite dependent product, which is used in finite-product norm calculations.

Mathlib has `Set.disjoint_pi`, but that is about `Set.pi` and characterises disjointness through
the fibres; it says nothing about the submodules cut out by a support condition.

## Main results

* `TauCeti.exists_isRegular_single_sub_single_sub`: distinct ordered differences of standard
  coordinate vectors differ regularly at some coordinate.
* `TauCeti.exists_isRegular_single_add_single_sub`: distinct unordered sums of two different
  standard coordinate vectors differ regularly at some coordinate.
* `TauCeti.exists_isRegular_neg_single_add_single_sub_single_add_single`: a negative coordinate
  sum and a coordinate sum on two different coordinates differ regularly at some coordinate.
* `Submodule.disjoint_pi_compl_bot_of_disjoint`: disjoint index sets give disjoint submodules of
  families vanishing outside them.
* `LinearEquiv.piEquivPiSubtypeProd`: `Equiv.piEquivPiSubtypeProd` as a linear equivalence,
  splitting `∀ i, M i` into the factors indexed by `p` and by `¬p`.
* `LinearEquiv.piFinSnoc`: the linear splitting of a tuple of length `n + 1` into its initial `n`
  coordinates and its last one, with `Fin.snoc` as its inverse.
* `LinearMap.det_pi_of_apply_eq_dependent`: the determinant of a coordinatewise endomorphism of a
  finite dependent product is the product of the determinants on its factors.
-/

namespace Submodule

variable {A M : Type*} [Semiring A] [AddCommMonoid M] [Module A M]



end Submodule

namespace LinearEquiv

section FinSnoc

variable (R : Type*) [Semiring R] {n : ℕ} (M : Fin (n + 1) → Type*)
  [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]







end FinSnoc

variable (R : Type*) {ι : Type*} [Semiring R] (p : ι → Prop) [DecidablePred p] (M : ι → Type*)
  [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]







end LinearEquiv

namespace TauCeti

open scoped BigOperators

universe u v

section CoordinateSeparation

variable {K ι : Type*} [CommRing K] [DecidableEq ι]







end CoordinateSeparation

variable {R : Type u} [CommRing R]
variable {ι : Type v} [Fintype ι]

/-- The determinant of a coordinatewise endomorphism of a finite dependent product. -/
 theorem _root_.LinearMap.det_pi_of_apply_eq_dependent {M : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] [∀ i, Module.Free R (M i)]
    [∀ i, Module.Finite R (M i)]
    (T : ((i : ι) → M i) →ₗ[R] ((i : ι) → M i)) (f : ∀ i, M i →ₗ[R] M i)
    (hT : ∀ x i, T x i = f i (x i)) :
    T.det = ∏ i, (f i).det := by
  classical
  let b (i : ι) := Module.Free.chooseBasis R (M i)
  let _ (i : ι) : Fintype (Module.Free.ChooseBasisIndex R (M i)) := Fintype.ofFinite _
  let B : Module.Basis (Σ i, Module.Free.ChooseBasisIndex R (M i)) R ((i : ι) → M i) :=
    Pi.basis b
  rw [← LinearMap.det_toMatrix B]
  have hmatrix :
      (LinearMap.toMatrix B B T) =
        Matrix.blockDiagonal' (fun i ↦ LinearMap.toMatrix (b i) (b i) (f i)) := by
    ext ⟨i₁, j₁⟩ ⟨i₂, j₂⟩
    simp only [LinearMap.toMatrix_apply', B, b, Pi.basis_apply, Matrix.blockDiagonal'_apply]
    split_ifs with h
    · subst i₂
      simp [hT]
    · simp [hT, h]
  rw [hmatrix]
  let _ : LinearOrder ι := Equiv.linearOrder (Fintype.equivFin ι)
  rw [(Matrix.blockTriangular_blockDiagonal' _).det_fintype]
  apply Finset.prod_congr rfl
  intro i hi
  let e : Module.Free.ChooseBasisIndex R (M i) ≃
      {a : Σ i, Module.Free.ChooseBasisIndex R (M i) // a.1 = i} :=
    { toFun := fun j ↦ ⟨⟨i, j⟩, rfl⟩
      invFun := fun a ↦ cast (by rw [a.2]) a.1.2
      left_inv := by intro j; rfl
      right_inv := by
        intro a
        apply Subtype.ext
        rcases a with ⟨⟨a, j⟩, ha⟩
        dsimp at ha
        subst a
        rfl }
  rw [← LinearMap.det_toMatrix (b i)]
  rw [← Matrix.det_reindex_self e]
  congr 1
  ext j k
  rcases j with ⟨⟨j₁, j₂⟩, hj⟩
  rcases k with ⟨⟨k₁, k₂⟩, hk⟩
  dsimp at hj hk
  subst j₁
  subst k₁
  simp [e, Matrix.toSquareBlock_def, Matrix.reindex]

end TauCeti

end


