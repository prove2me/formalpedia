-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_NativeLegHomExt_SixOne20261024_Defs
-- name    : LPCA_Solutions_LPCA_NativeLegHomExt_SixOne20261024_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-24T20:06:12.990388+00:00
-- url     : https://prove2.me/theorems/4d7d873f-5da0-4b54-a71b-3016384f6ec7
-- title:
--   Native Leg Hom Ext — coordinate chain dependencies
-- statement:
--   This bundle supplies the selected constructions and proved compatibility results for native leg hom ext used in the coordinate Čech chain comparison. Each construction retains the rings, categories, grading indices and hypotheses in its formal declaration.
-- source:
--   https://arxiv.org/abs/2609.02858v1, Section 6, Theorem 6.1 and its formalization dependencies. Certified Lean source: Solutions/LPCA_NativeLegHomExt.lean, selected declarations in lines 11–26; source SHA-256 00b63e1a7f45c5621cbc793055af8f2488a086657dfa9d6b748141fd5bad37dc; exact-source certificate Sapelo2 job 49296539.

import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.DirectSum.Module
import Definitions.Def_LPCA_Solutions_LPCA_ModuleDirectSumColimit_Defs

set_option autoImplicit false

namespace LPCA

open CategoryTheory CategoryTheory.Limits

universe u

theorem nativeLegHom_ext (R : Type u) [Ring R]
    {I : Type u} [DecidableEq I] (A : I → ModuleCat.{u} R)
    (H N : ModuleCat.{u} R) (j : ∀ i, A i ⟶ H)
    (E : H ≅ ModuleCat.of R (DirectSum I (fun i => A i)))
    (hj : ∀ i, j i ≫ E.hom = ModuleCat.ofHom (DirectSum.lof R I (fun i => A i) i))
    (F G : H ⟶ N) (h : ∀ i, j i ≫ F = j i ≫ G) : F = G := by
  have hi : ∀ i, ModuleCat.ofHom (DirectSum.lof R I (fun i => A i) i) ≫ E.inv = j i := by
    intro i
    rw [← hj i, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply (cancel_epi E.inv).mp
  apply (moduleDirectSumIsColimit R A).hom_ext
  intro i
  change ModuleCat.ofHom (DirectSum.lof R I (fun i => A i) i.as) ≫ E.inv ≫ F =
    ModuleCat.ofHom (DirectSum.lof R I (fun i => A i) i.as) ≫ E.inv ≫ G
  rw [← Category.assoc, hi i.as, ← Category.assoc, hi i.as]
  exact h i.as

end LPCA


