-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_DirectSumChartHomExt_SixOne20261024_Defs
-- name    : LPCA_Solutions_LPCA_DirectSumChartHomExt_SixOne20261024_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-24T20:06:34.606296+00:00
-- url     : https://prove2.me/theorems/92d2868b-0d2b-4183-bf39-6636a2fb63b4
-- title:
--   Direct Sum Chart Hom Ext — coordinate chain dependencies
-- statement:
--   This bundle supplies the selected constructions and proved compatibility results for direct sum chart hom ext used in the coordinate Čech chain comparison. Each construction retains the rings, categories, grading indices and hypotheses in its formal declaration.
-- source:
--   https://arxiv.org/abs/2609.02858v1, Section 6, Theorem 6.1 and its formalization dependencies. Certified Lean source: Solutions/LPCA_DirectSumChartHomExt.lean, selected declarations in lines 12–24; source SHA-256 5abd49c368bb543f1eb93c0a71f774b25057654a350fd4fadd41bffd776b71d3; exact-source certificate Sapelo2 job 49296539.

import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.DirectSum.Module
import Definitions.Def_LPCA_Solutions_LPCA_DirectSumChartAssembly_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_DirectSumGeneratorEquations_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_DirectSumRestriction_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ModuleDirectSumColimit_Defs
import Definitions.Def_LPCA_Solutions_LPCA_NativeLegHomExt_SixOne20261024_Defs

set_option autoImplicit false

namespace LPCA

open CategoryTheory

universe u

theorem directSumChartHom_ext (R : Type u) [Ring R]
    {I : Type u} [DecidableEq I] (A : I → ModuleCat.{u} R) (P N : ModuleCat.{u} R)
    (F : DirectSum I (fun i => A i) ≃ₗ[R] P) (f g : P ⟶ N)
    (h : ∀ i, ModuleCat.ofHom (directSumChartLeg R A P F i) ≫ f =
      ModuleCat.ofHom (directSumChartLeg R A P F i) ≫ g) : f = g := by
  apply nativeLegHom_ext R A P N (fun i => ModuleCat.ofHom (directSumChartLeg R A P F i))
    F.symm.toModuleIso ?_ f g h
  intro i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change F.symm (F (DirectSum.lof R I (fun i => A i) i x)) = _
  exact F.symm_apply_apply _

end LPCA


