-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_RestrictedSubmoduleFieldIso_SixOne20261024_Defs
-- name    : LPCA_Solutions_LPCA_RestrictedSubmoduleFieldIso_SixOne20261024_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-24T20:05:13.795705+00:00
-- url     : https://prove2.me/theorems/29c0cda9-a476-44a7-ad6f-6f3d42ded684
-- title:
--   Restricted Submodule Field Iso — coordinate chain dependencies
-- statement:
--   This bundle supplies the selected constructions and proved compatibility results for restricted submodule field iso used in the coordinate Čech chain comparison. Each construction retains the rings, categories, grading indices and hypotheses in its formal declaration.
--
--   Restrict the ambient field comparison to an actual submodule, retaining
--   its original scalar action. The carrier identification is an explicit premise.
-- source:
--   https://arxiv.org/abs/2609.02858v1, Section 6, Theorem 6.1 and its formalization dependencies. Certified Lean source: Solutions/LPCA_RestrictedSubmoduleFieldIso.lean, selected declarations in lines 14–42; source SHA-256 a9ef49b6b22723bcf7d06494783cf5a1dba20948a4c55aa58e3c41d9506431ac; exact-source certificate Sapelo2 job 49296539.

import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Module.Submodule.Map

set_option autoImplicit false

namespace LPCA

open CategoryTheory

universe u

variable (R S : Type u) [Ring R] [Ring S]

/-- Restrict the ambient field comparison to an actual submodule, retaining
its original scalar action. The carrier identification is an explicit premise. -/
noncomputable def restrictedSubmoduleFieldIso (f : R →+* S)
    (M : ModuleCat.{u} S) (N : ModuleCat.{u} R)
    (e : (ModuleCat.restrictScalars f).obj M ≅ N)
    (Q : Submodule S M) (P : Submodule R N)
    (hQ : ∀ x : M, x ∈ Q ↔ e.hom x ∈ P) :
    (ModuleCat.restrictScalars f).obj (ModuleCat.of S Q) ≅ ModuleCat.of R P :=
  (show (ModuleCat.restrictScalars f).obj (ModuleCat.of S Q) ≃ₗ[R] P from
    { toFun := fun x => ⟨e.hom x.1, (hQ x.1).mp x.2⟩
      invFun := fun y => ⟨e.inv y.1, (hQ _).mpr (by
        change e.toLinearEquiv (e.toLinearEquiv.symm y.1) ∈ P
        simpa only [e.toLinearEquiv.apply_symm_apply] using y.2)⟩
      left_inv := by
        intro x
        apply Subtype.ext
        exact e.toLinearEquiv.symm_apply_apply x.1
      right_inv := by
        intro y
        apply Subtype.ext
        exact e.toLinearEquiv.apply_symm_apply y.1
      map_add' := by
        intro x y
        apply Subtype.ext
        exact e.hom.hom.map_add x.1 y.1
      map_smul' := by
        intro a x
        apply Subtype.ext
        exact e.hom.hom.map_smul a x.1 }).toModuleIso



end LPCA


