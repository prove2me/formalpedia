-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_DirectSumChartAssembly_SixOne20261024_Defs
-- name    : LPCA_Solutions_LPCA_DirectSumChartAssembly_SixOne20261024_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-24T20:05:51.756738+00:00
-- url     : https://prove2.me/theorems/762150c3-6e9d-4420-94d6-59a182650b99
-- title:
--   Direct Sum Chart Assembly — coordinate chain dependencies
-- statement:
--   This bundle supplies the selected constructions and proved compatibility results for direct sum chart assembly used in the coordinate Čech chain comparison. Each construction retains the rings, categories, grading indices and hypotheses in its formal declaration.
-- source:
--   https://arxiv.org/abs/2609.02858v1, Section 6, Theorem 6.1 and its formalization dependencies. Certified Lean source: Solutions/LPCA_DirectSumChartAssembly.lean, selected declarations in lines 14–36; source SHA-256 7d5f25d2e86cfe3cbade08d6d2b2932a1ed0c850e952d2472809af7b12eae05b; exact-source certificate Sapelo2 job 49296539.

import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.DirectSum.Module
import Definitions.Def_LPCA_Solutions_LPCA_DirectSumGeneratorEquations_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_DirectSumRestriction_SixOne20261024_Defs

set_option autoImplicit false

namespace LPCA

universe u

variable (R : Type u) [Ring R]
variable {I : Type u} [DecidableEq I]
variable (A B : I → ModuleCat.{u} R) (P Q : ModuleCat.{u} R)

noncomputable def directSumChartLeg (F : DirectSum I (fun i => A i) ≃ₗ[R] P) (i : I) :
    A i →ₗ[R] P :=
  F.toLinearMap.comp (DirectSum.lof R I (fun i => A i) i)

noncomputable def directSumChartEquiv (F : DirectSum I (fun i => A i) ≃ₗ[R] P)
    (G : ∀ i, A i ≃ₗ[R] B i) (H : DirectSum I (fun i => B i) ≃ₗ[R] Q) : P ≃ₗ[R] Q :=
  F.symm.trans ((DirectSum.congrLinearEquiv G).trans H)

theorem directSumChartEquiv_leg (F : DirectSum I (fun i => A i) ≃ₗ[R] P)
    (G : ∀ i, A i ≃ₗ[R] B i) (H : DirectSum I (fun i => B i) ≃ₗ[R] Q) (i : I) (x : A i) :
    directSumChartEquiv R A B P Q F G H (directSumChartLeg R A P F i x) =
      H (DirectSum.lof R I (fun i => B i) i (G i x)) := by
  simp only [directSumChartEquiv, directSumChartLeg, LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
    directSumCongrEquiv_lof]

theorem directSumChartEquiv_leg_hom (F : DirectSum I (fun i => A i) ≃ₗ[R] P)
    (G : ∀ i, A i ≃ₗ[R] B i) (H : DirectSum I (fun i => B i) ≃ₗ[R] Q) (i : I) :
    (directSumChartEquiv R A B P Q F G H).toLinearMap.comp (directSumChartLeg R A P F i) =
      (H.toLinearMap.comp (DirectSum.lof R I (fun i => B i) i)).comp (G i).toLinearMap := by
  apply LinearMap.ext
  intro x
  exact directSumChartEquiv_leg R A B P Q F G H i x

end LPCA


