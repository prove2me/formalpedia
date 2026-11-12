-- Prove2me | Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CenterSplitting
-- name    : OddOrder_GroupTheory_RepresentationTheory_CenterSplitting
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:49:51.441195+00:00
-- url     : https://prove2.me/theorems/67ad57cd-65e8-4d26-b937-36100711d80d
-- title:
--   Transporting the centre along an algebra isomorphism
-- statement:
--   For the orbit-count Brauer lemma of Peterfalvi (9.1), the splitting $Z(\bar{\mathbb{F}}_p[U])\cong(\mathrm{Fin}\,N\to k)$ is built by transporting the centre through the Wedderburn decomposition $k[U]\cong\prod_i\mathrm{Mat}_i(k)$. The first link is the basis-free fact that an algebra isomorphism restricts to an isomorphism of centres; the file also shows the centre of a product algebra is the product of the centres and the centre of a matrix algebra over a field is $k$ (scalar matrices).
--
--   Main declarations: `centerCongr` (An algebra isomorphism restricts to an isomorphism of centres `Z(A) ≃ₐ[R] Z(B)`); `centerCongrHom`; `centerPiEquiv`; `matrixCenterEquiv`; and 2 more.
--
--   The bundle also proves 5 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/RepresentationTheory/CenterSplitting.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/CenterSplitting.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CenterOrbitCount
import Mathlib.Algebra.Central.Matrix
import Mathlib.RepresentationTheory.Maschke
import Mathlib.RingTheory.SimpleModule.IsAlgClosed

namespace OddOrder.GroupTheory.CenterSplitting

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

/-- An algebra isomorphism carries the centre *onto* the centre. -/
theorem center_map_eq (e : A ≃ₐ[R] B) :
    (Subalgebra.center R A).map (e : A →ₐ[R] B) = Subalgebra.center R B := by
  apply le_antisymm
  · rw [Subalgebra.map_le]
    intro x hx
    exact e.map_mem_center hx
  · intro y hy
    refine Subalgebra.mem_map.mpr ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    exact e.symm.map_mem_center hy

/-- **An algebra isomorphism restricts to an isomorphism of centres** `Z(A) ≃ₐ[R] Z(B)`. -/
def _root_.AlgEquiv.centerCongr (e : A ≃ₐ[R] B) :
    Subalgebra.center R A ≃ₐ[R] Subalgebra.center R B :=
  (e.subalgebraMap (Subalgebra.center R A)).trans
    (Subalgebra.equivOfEq _ _ (center_map_eq e))

@[simp] theorem centerCongr_apply (e : A ≃ₐ[R] B) (x : Subalgebra.center R A) :
    (e.centerCongr x : B) = e (x : A) := rfl

/-- `AlgEquiv.centerCongr` packaged as a **monoid homomorphism** on automorphisms:
`(A ≃ₐ[R] A) →* (Z(A) ≃ₐ[R] Z(A))`.  Makes `MulAut`-actions descend to the centre as group
actions. -/
def _root_.AlgEquiv.centerCongrHom :
    (A ≃ₐ[R] A) →* (Subalgebra.center R A ≃ₐ[R] Subalgebra.center R A) where
  toFun := AlgEquiv.centerCongr
  map_one' := by ext x; simp [AlgEquiv.one_apply]
  map_mul' e₁ e₂ := by ext x; simp [AlgEquiv.mul_apply]

section Pi

variable {ι : Type*} [DecidableEq ι] {C : ι → Type*} [∀ i, Semiring (C i)] [∀ i, Algebra R (C i)]

omit [DecidableEq ι] in
/-- An element of a product algebra is central iff each component is central. -/
theorem mem_center_pi {f : ∀ i, C i} :
    f ∈ Subalgebra.center R (∀ i, C i) ↔ ∀ i, f i ∈ Subalgebra.center R (C i) := by
  classical
  rw [Subalgebra.mem_center_iff]
  constructor
  · intro h i
    rw [Subalgebra.mem_center_iff]
    intro a
    have hc := congrFun (h (Pi.single i a)) i
    simpa [Pi.mul_apply, Pi.single_apply] using hc
  · intro h g
    simp only [Subalgebra.mem_center_iff] at h
    funext i
    change g i * f i = f i * g i
    exact h i (g i)

/-- **The centre of a product algebra is the product of the centres**, as an `R`-algebra
isomorphism `Z(∏ᵢ Cᵢ) ≃ₐ[R] ∏ᵢ Z(Cᵢ)`. -/
def centerPiEquiv :
    Subalgebra.center R (∀ i, C i) ≃ₐ[R] (∀ i, Subalgebra.center R (C i)) where
  toFun f i := ⟨f.1 i, (mem_center_pi.mp f.2) i⟩
  invFun g := ⟨fun i => (g i).1, mem_center_pi.mpr fun i => (g i).2⟩
  left_inv f := by apply Subtype.ext; funext i; rfl
  right_inv g := by funext i; apply Subtype.ext; rfl
  map_mul' f f' := by funext i; apply Subtype.ext; rfl
  map_add' f f' := by funext i; apply Subtype.ext; rfl
  commutes' r := by funext i; apply Subtype.ext; rfl

omit [DecidableEq ι] in
@[simp] theorem centerPiEquiv_apply (f : Subalgebra.center R (∀ i, C i)) (i : ι) :
    ((centerPiEquiv f i : C i)) = (f : ∀ i, C i) i := rfl

end Pi

section Matrix

variable {k n : Type*} [Field k] [Fintype n] [DecidableEq n]

/-- The centre of a matrix algebra over a field is the range of the scalar embedding. -/
theorem matrix_center_eq_range :
    Subalgebra.center k (Matrix n n k) = (Matrix.scalarAlgHom n k).range := by
  rw [Matrix.subalgebraCenter_eq_scalarAlgHom_map, Subalgebra.center_eq_top, Algebra.map_top]

/-- The scalar embedding `k →ₐ Matrix n n k` is injective when `n` is nonempty. -/
theorem scalarAlgHom_injective [Nonempty n] :
    Function.Injective (Matrix.scalarAlgHom n k : k →ₐ[k] Matrix n n k) := by
  intro a b hab
  rw [Matrix.scalarAlgHom_apply, Matrix.scalarAlgHom_apply, Matrix.scalar_apply,
    Matrix.scalar_apply] at hab
  obtain ⟨i⟩ := ‹Nonempty n›
  simpa [Matrix.diagonal_apply_eq] using congrFun (congrFun hab i) i

/-- **The centre of a matrix algebra over a field is `k`** (scalar matrices), as an algebra
isomorphism `Z(Matrix n n k) ≃ₐ[k] k` (for `n` nonempty). -/
noncomputable def matrixCenterEquiv [Nonempty n] :
    Subalgebra.center k (Matrix n n k) ≃ₐ[k] k :=
  (Subalgebra.equivOfEq _ _ matrix_center_eq_range).trans
    (AlgEquiv.ofInjective (Matrix.scalarAlgHom n k) scalarAlgHom_injective).symm

end Matrix

section Wedderburn

variable (k G : Type*) [Field k] [IsAlgClosed k] [Group G] [Finite G] [NeZero (Nat.card G : k)]

/-- **The centre of `k[G]` splits as `(Fin N → k)`** when `k` is algebraically closed and
`char k ∤ |G|` (so `k[G]` is split semisimple).  `N` is the number of Wedderburn blocks = the number
of simple modules.  Assembled from the Wedderburn decomposition `k[G] ≅ ∏ᵢ Matᵢ(k)` and the three
centre links (`centerCongr`, `centerPiEquiv`, `matrixCenterEquiv`). -/
theorem exists_center_algEquiv_pi :
    ∃ N : ℕ, Nonempty (Subalgebra.center k (MonoidAlgebra k G) ≃ₐ[k] (Fin N → k)) := by
  obtain ⟨n, d, hd, ⟨e⟩⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed k (MonoidAlgebra k G)
  refine ⟨n, ⟨e.centerCongr.trans (centerPiEquiv.trans (AlgEquiv.piCongrRight fun i => ?_))⟩⟩
  haveI : Nonempty (Fin (d i)) := ⟨⟨0, Nat.pos_of_ne_zero (hd i).out⟩⟩
  exact matrixCenterEquiv

end Wedderburn

end OddOrder.GroupTheory.CenterSplitting


