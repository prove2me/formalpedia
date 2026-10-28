-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_DirectSumIndexedMap_SixOne20261024_Defs
-- name    : LPCA_Solutions_LPCA_DirectSumIndexedMap_SixOne20261024_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-24T20:04:49.881995+00:00
-- url     : https://prove2.me/theorems/9b825371-5d5d-41e3-ab33-c68d60a21ef9
-- title:
--   Direct Sum Indexed Map — coordinate chain dependencies
-- statement:
--   This bundle supplies the selected constructions and proved compatibility results for direct sum indexed map used in the coordinate Čech chain comparison. Each construction retains the rings, categories, grading indices and hypotheses in its formal declaration.
-- source:
--   https://arxiv.org/abs/2609.02858v1, Section 6, Theorem 6.1 and its formalization dependencies. Certified Lean source: Solutions/LPCA_DirectSumIndexedMap.lean, selected declarations in lines 14–31; source SHA-256 cbee0632b0c562a5fbbd5af6f651bb2d377a15f5b7580d4f9684d18c8e60a3e9; exact-source certificate Sapelo2 job 49296539.

import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.DirectSum.Module
import Definitions.Def_LPCA_Solutions_LPCA_ModuleDirectSumColimit_Defs

set_option autoImplicit false

namespace LPCA

open CategoryTheory

universe u

variable (R : Type u) [Ring R]
variable {I J : Type u} [DecidableEq I] [DecidableEq J]

noncomputable def moduleDirectSumIndexedHom (A : I → ModuleCat.{u} R) (B : J → ModuleCat.{u} R)
    (f : I → J) (v : ∀ i, A i ⟶ B (f i)) :
    ModuleCat.of R (DirectSum I (fun i => A i)) ⟶ ModuleCat.of R (DirectSum J (fun j => B j)) :=
  ModuleCat.ofHom (DirectSum.toModule R I (DirectSum J (fun j => B j))
    (fun i => (DirectSum.lof R J (fun j => B j) (f i)).comp (v i).hom))

theorem moduleDirectSumIndexedHom_ι (A : I → ModuleCat.{u} R) (B : J → ModuleCat.{u} R)
    (f : I → J) (v : ∀ i, A i ⟶ B (f i)) (i : I) :
    ModuleCat.ofHom (DirectSum.lof R I (fun i => A i) i) ≫ moduleDirectSumIndexedHom R A B f v =
      v i ≫ ModuleCat.ofHom (DirectSum.lof R J (fun j => B j) (f i)) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change DirectSum.toModule R I (DirectSum J (fun j => B j))
    (fun i => (DirectSum.lof R J (fun j => B j) (f i)).comp (v i).hom)
    (DirectSum.lof R I (fun i => A i) i x) = _
  erw [DirectSum.toModule_lof]
  rfl

end LPCA


