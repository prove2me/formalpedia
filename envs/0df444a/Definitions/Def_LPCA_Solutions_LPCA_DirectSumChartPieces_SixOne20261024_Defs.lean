-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_DirectSumChartPieces_SixOne20261024_Defs
-- name    : LPCA_Solutions_LPCA_DirectSumChartPieces_SixOne20261024_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-24T20:06:36.269051+00:00
-- url     : https://prove2.me/theorems/dda4e604-53d7-415f-aa5d-10fc7294f493
-- title:
--   Direct Sum Chart Pieces — coordinate chain dependencies
-- statement:
--   This bundle supplies the selected constructions and proved compatibility results for direct sum chart pieces used in the coordinate Čech chain comparison. Each construction retains the rings, categories, grading indices and hypotheses in its formal declaration.
-- source:
--   https://arxiv.org/abs/2609.02858v1, Section 6, Theorem 6.1 and its formalization dependencies. Certified Lean source: Solutions/LPCA_DirectSumChartPieces.lean, selected declarations in lines 15–57; source SHA-256 a096d113abdab390e00dbe12137d0f4eabd5c51cfd89951c9cfcbff7e218a44c; exact-source certificate Sapelo2 job 49296539.

import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.DirectSum.Module
import Definitions.Def_LPCA_Solutions_LPCA_DirectSumChartAssembly_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_DirectSumGeneratorEquations_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_DirectSumRestriction_SixOne20261024_Defs

set_option autoImplicit false

namespace LPCA

open CategoryTheory

universe u

variable (R : Type u) [Ring R]
variable {I : Type u} [DecidableEq I]
variable (A : I → ModuleCat.{u} R) (P : ModuleCat.{u} R)

theorem directSumChartLeg_injective (F : DirectSum I (fun i => A i) ≃ₗ[R] P) (i : I) :
    Function.Injective (directSumChartLeg R A P F i) := by
  intro x y h
  change F (DirectSum.lof R I (fun i => A i) i x) =
    F (DirectSum.lof R I (fun i => A i) i y) at h
  have h' := F.injective h
  simpa only [DirectSum.lof_apply] using congrArg (fun z => z i) h'

noncomputable def directSumChartPiece (F : DirectSum I (fun i => A i) ≃ₗ[R] P) (i : I) :
    Submodule R P := LinearMap.range (directSumChartLeg R A P F i)

theorem directSumChartPieces_internal (F : DirectSum I (fun i => A i) ≃ₗ[R] P) :
    DirectSum.IsInternal (directSumChartPiece R A P F) := by
  let E : ∀ i, A i ≃ₗ[R] directSumChartPiece R A P F i := fun i =>
    LinearEquiv.ofInjective (directSumChartLeg R A P F i) (directSumChartLeg_injective R A P F i)
  let G := (DirectSum.congrLinearEquiv (fun i => (E i).symm)).trans F
  have hE : ∀ i (x : directSumChartPiece R A P F i),
      directSumChartLeg R A P F i ((E i).symm x) = x.1 := by
    intro i x
    exact LinearEquiv.ofInjective_symm_apply (directSumChartLeg R A P F i) x
  have hG : DirectSum.coeLinearMap (directSumChartPiece R A P F) = G.toLinearMap := by
    apply DirectSum.linearMap_ext
    intro i
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply]
    rw [DirectSum.coeLinearMap_lof]
    change x.1 = F (DirectSum.lmap (fun i => (E i).symm.toLinearMap)
      (DirectSum.lof R I (fun i => directSumChartPiece R A P F i) i x))
    rw [DirectSum.lmap_lof]
    exact (hE i x).symm
  change Function.Bijective (DirectSum.coeLinearMap (directSumChartPiece R A P F))
  rw [hG]
  exact G.bijective

theorem directSumChartLeg_trans_hom (Q : ModuleCat.{u} R)
    (F : DirectSum I (fun i => A i) ≃ₗ[R] P) (G : P ≃ₗ[R] Q) (i : I) :
    ModuleCat.ofHom (directSumChartLeg R A Q (F.trans G) i) =
      ModuleCat.ofHom (directSumChartLeg R A P F i) ≫ ModuleCat.ofHom G.toLinearMap := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

end LPCA


