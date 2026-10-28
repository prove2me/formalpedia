-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_NativeLegChartAssembly_SixOne20261024_Defs
-- name    : LPCA_Solutions_LPCA_NativeLegChartAssembly_SixOne20261024_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-24T20:07:11.321991+00:00
-- url     : https://prove2.me/theorems/c5540a97-9e6b-4396-b0e8-21e9a77be355
-- title:
--   Native Leg Chart Assembly — coordinate chain dependencies
-- statement:
--   This bundle supplies the selected constructions and proved compatibility results for native leg chart assembly used in the coordinate Čech chain comparison. Each construction retains the rings, categories, grading indices and hypotheses in its formal declaration.
--
--   Assemble homogeneous charts directly into the independently specified
--   target grading. No whole native polynomial upgrade is evaluated.
-- source:
--   https://arxiv.org/abs/2609.02858v1, Section 6, Theorem 6.1 and its formalization dependencies. Certified Lean source: Solutions/LPCA_NativeLegChartAssembly.lean, selected declarations in lines 16–49; source SHA-256 54c443a72ac1c909244e46dcbe2b39ef5b01ecbef7f7e462d5270dc3b2f3cade; exact-source certificate Sapelo2 job 49296539.

import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.DirectSum.Module
import Definitions.Def_LPCA_Solutions_LPCA_DirectSumChartAssembly_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_DirectSumGeneratorEquations_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_DirectSumRestriction_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_NativeLegAssembly_SixOne20261024_Defs

set_option autoImplicit false

namespace LPCA

open CategoryTheory

universe u

variable (R : Type u) [Ring R]
variable {I : Type u} [DecidableEq I]
variable (A B : I → ModuleCat.{u} R) (H : ModuleCat.{u} R)

theorem nativeChartLeg_inverse (F : DirectSum I (fun i => B i) ≃ₗ[R] H) (i : I) :
    ModuleCat.ofHom (directSumChartLeg R B H F i) ≫ F.symm.toModuleIso.hom =
      ModuleCat.ofHom (DirectSum.lof R I (fun i => B i) i) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact F.symm_apply_apply _

/-- Assemble homogeneous charts directly into the independently specified
target grading. No whole native polynomial upgrade is evaluated. -/
noncomputable def nativeLegChartAssembly (e : ∀ i, A i ≅ B i)
    (F : DirectSum I (fun i => B i) ≃ₗ[R] H) :
    DirectSum I (fun i => A i) ≃ₗ[R] H :=
  nativeLegAssemblyEquiv R A B e H
    (fun i => ModuleCat.ofHom (directSumChartLeg R B H F i)) F.symm.toModuleIso
    (nativeChartLeg_inverse R B H F)

theorem nativeLegChartAssembly_lof (e : ∀ i, A i ≅ B i)
    (F : DirectSum I (fun i => B i) ≃ₗ[R] H) (i : I) (x : A i) :
    nativeLegChartAssembly R A B H e F (DirectSum.lof R I (fun i => A i) i x) =
      directSumChartLeg R B H F i ((e i).hom x) :=
  nativeLegAssemblyEquiv_lof R A B e H _ F.symm.toModuleIso
    (nativeChartLeg_inverse R B H F) i x

noncomputable def nativeWholeChartEquiv (F : DirectSum I (fun i => A i) ≃ₗ[R] H)
    (Q : ModuleCat.{u} R) (G : DirectSum I (fun i => A i) ≃ₗ[R] Q) : H ≃ₗ[R] Q :=
  F.symm.trans G

theorem nativeWholeChartEquiv_leg (F : DirectSum I (fun i => A i) ≃ₗ[R] H)
    (Q : ModuleCat.{u} R) (G : DirectSum I (fun i => A i) ≃ₗ[R] Q) (i : I) (x : A i) :
    nativeWholeChartEquiv R A H F Q G (directSumChartLeg R A H F i x) =
      G (DirectSum.lof R I (fun i => A i) i x) := by
  change G (F.symm (F (DirectSum.lof R I (fun i => A i) i x))) = _
  rw [F.symm_apply_apply]

end LPCA


