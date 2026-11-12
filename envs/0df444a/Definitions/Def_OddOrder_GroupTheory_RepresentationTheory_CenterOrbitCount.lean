-- Prove2me | Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CenterOrbitCount
-- name    : OddOrder_GroupTheory_RepresentationTheory_CenterOrbitCount
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:47:58.633103+00:00
-- url     : https://prove2.me/theorems/68c1fd2b-34dc-4058-9e07-f25c4ac80718
-- title:
--   Orbit count for the $\sigma$-action on $Z(k[G])$ via the class-sum basis
-- statement:
--   For the kernel-FPF count ($\dagger$) of Peterfalvi (9.1), one of the two computations of $\dim Z(\bar{\mathbb{F}}_p[U])^{\langle e\rangle}$ goes through the class-sum basis: the automorphism $\sigma_e$ permutes conjugacy classes, so by the orbit cornerstone the invariant dimension equals the number of orbits.
--
--   Main declarations: `?` (A group automorphism `α` acts on conjugacy classes by `α • C = ConjClasses.map α C`); `centerEnd` (The endomorphism of `Z(k[G])` induced by `α : MulAut G` via `domCongr α`); `centerRep`; `CenterCarrier`; and 6 more.
--
--   The bundle also proves 3 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/RepresentationTheory/CenterOrbitCount.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/CenterOrbitCount.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CenterClassSumBasis
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_PermutationInvariants

open scoped MonoidAlgebra

open Module MulAction

namespace ConjClasses

/-- `ConjClasses.map` of the identity is the identity. -/
@[simp] theorem map_id {M : Type*} [Monoid M] (C : ConjClasses M) :
    ConjClasses.map (MonoidHom.id M) C = C := by
  obtain ⟨a, rfl⟩ := ConjClasses.mk_surjective C; rfl

end ConjClasses

namespace OddOrder.GroupTheory.CenterClassSum

variable {G : Type*} [Group G]

/-- A group automorphism `α` acts on conjugacy classes by `α • C = ConjClasses.map α C`. -/
instance : MulAction (MulAut G) (ConjClasses G) where
  smul α C := ConjClasses.map (α : G →* G) C
  one_smul C := by obtain ⟨a, rfl⟩ := ConjClasses.mk_surjective C; rfl
  mul_smul α β C := by obtain ⟨a, rfl⟩ := ConjClasses.mk_surjective C; rfl

@[simp] theorem mulAut_smul_mk (α : MulAut G) (a : G) :
    α • (ConjClasses.mk a) = ConjClasses.mk (α a) := rfl

/-- An algebra isomorphism carries the centre into the centre (`e z` commutes with everything, by
transporting the commutation of `z` with `e.symm w` through `e`). -/
theorem _root_.AlgEquiv.map_mem_center {k A B : Type*} [CommSemiring k] [Semiring A] [Semiring B]
    [Algebra k A] [Algebra k B] (e : A ≃ₐ[k] B) {z : A} (hz : z ∈ Subalgebra.center k A) :
    e z ∈ Subalgebra.center k B := by
  rw [Subalgebra.mem_center_iff] at hz ⊢
  intro w
  calc w * e z = e (e.symm w) * e z := by rw [e.apply_symm_apply]
    _ = e (e.symm w * z) := (map_mul e _ _).symm
    _ = e (z * e.symm w) := by rw [hz]
    _ = e z * e (e.symm w) := map_mul e _ _
    _ = e z * w := by rw [e.apply_symm_apply]

variable {k : Type*} [Field k]

/-- The endomorphism of `Z(k[G])` induced by `α : MulAut G` via `domCongr α`. -/
noncomputable def centerEnd (α : MulAut G) :
    Module.End k ↥(Subalgebra.center k (MonoidAlgebra k G)) where
  toFun z := ⟨MonoidAlgebra.domCongrAut (R := k) (A := k) α (z : MonoidAlgebra k G),
    (MonoidAlgebra.domCongrAut (R := k) (A := k) α).map_mem_center z.2⟩
  map_add' x y := by
    apply Subtype.ext
    change MonoidAlgebra.domCongrAut (R := k) (A := k) α
          ((x : MonoidAlgebra k G) + (y : MonoidAlgebra k G))
        = MonoidAlgebra.domCongrAut (R := k) (A := k) α (x : MonoidAlgebra k G)
          + MonoidAlgebra.domCongrAut (R := k) (A := k) α (y : MonoidAlgebra k G)
    rw [map_add]
  map_smul' c x := by
    apply Subtype.ext
    change MonoidAlgebra.domCongrAut (R := k) (A := k) α (c • (x : MonoidAlgebra k G))
        = c • MonoidAlgebra.domCongrAut (R := k) (A := k) α (x : MonoidAlgebra k G)
    rw [map_smul]

/-- The representation of `MulAut G` on the centre `Z(k[G])`: `α` acts by the algebra automorphism
`domCongr α` restricted to the centre. -/
noncomputable def centerRep :
    Representation k (MulAut G) ↥(Subalgebra.center k (MonoidAlgebra k G)) where
  toFun := centerEnd
  map_one' := by
    apply LinearMap.ext; intro z; apply Subtype.ext
    change MonoidAlgebra.domCongrAut (R := k) (A := k) (1 : MulAut G) (z : MonoidAlgebra k G)
        = (z : MonoidAlgebra k G)
    rw [map_one, AlgEquiv.one_apply]
  map_mul' α β := by
    apply LinearMap.ext; intro z; apply Subtype.ext
    change MonoidAlgebra.domCongrAut (R := k) (A := k) (α * β) (z : MonoidAlgebra k G)
        = MonoidAlgebra.domCongrAut (R := k) (A := k) α
            (MonoidAlgebra.domCongrAut (R := k) (A := k) β (z : MonoidAlgebra k G))
    rw [map_mul, AlgEquiv.mul_apply]

variable [Fintype G] [DecidableEq G] [Fintype (ConjClasses G)] [DecidableEq (ConjClasses G)]

omit [DecidableEq G] in
/-- `centerRep` permutes the class-sum basis according to the `MulAut G`-action on classes:
`centerRep α (centerBasis C) = centerBasis (α • C)`.  This is `domCongr_classSum` transported to the
centre subalgebra. -/
theorem centerRep_apply_centerBasis (α : MulAut G) (C : ConjClasses G) :
    centerRep (k := k) α (centerBasis (k := k) C) = centerBasis (k := k) (α • C) := by
  rw [centerBasis_apply, centerBasis_apply]
  apply Subtype.ext
  change MonoidAlgebra.domCongrAut (R := k) (A := k) α (classSum (k := k) C)
      = classSum (k := k) (ConjClasses.map (α : G →* G) C)
  exact domCongr_classSum α C

/-- A carrier synonym for the centre `Z(k[G])` that pins one canonical `Module k`-instance, so that
cornerstone applications do not trip the instance-diamond `isDefEq` blowup. -/
def CenterCarrier (k G : Type*) [Field k] [Group G] : Type _ :=
  ↥(Subalgebra.center k (MonoidAlgebra k G))

noncomputable instance : AddCommGroup (CenterCarrier k G) :=
  inferInstanceAs (AddCommGroup ↥(Subalgebra.center k (MonoidAlgebra k G)))

noncomputable instance : Module k (CenterCarrier k G) :=
  inferInstanceAs (Module k ↥(Subalgebra.center k (MonoidAlgebra k G)))

/-- `centerRep` retyped over the carrier synonym. -/
noncomputable def centerRep' : Representation k (MulAut G) (CenterCarrier k G) := centerRep

/-- `centerBasis` retyped over the carrier synonym. -/
noncomputable def centerBasis' : Basis (ConjClasses G) k (CenterCarrier k G) := centerBasis

omit [DecidableEq G] in
theorem centerRep'_apply_centerBasis' (α : MulAut G) (C : ConjClasses G) :
    centerRep' (k := k) α (centerBasis' (k := k) C) = centerBasis' (k := k) (α • C) :=
  centerRep_apply_centerBasis α C

end OddOrder.GroupTheory.CenterClassSum


