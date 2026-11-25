-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreMain
-- name    : Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreMain
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T12:58:30.996236+00:00
-- url     : https://prove2.me/theorems/19db9efa-ea83-4ce8-bc08-e55b10ed4404
-- title:
--   Core Main
-- statement:
--   Definitions and structural lemmas for Core Main, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreMain.lean

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCasGl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace
namespace PositivityTheory.KReal
section Gen
variable {r s : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
end Gen
def mainProdAct {r s : ℕ} {T T' : Type} [AddCommGroup T] [Module ℂ T] [AddCommGroup T'] [Module ℂ T']
    (act : Mat r s →ₗ[ℂ] Module.End ℂ T) (act' : Mat r s →ₗ[ℂ] Module.End ℂ T') :
    Mat r s →ₗ[ℂ] Module.End ℂ (T × T') where
  toFun W := (act W).prodMap (act' W)
  map_add' W W' := by
    refine LinearMap.ext fun x => ?_
    simp
  map_smul' a W := by
    refine LinearMap.ext fun x => ?_
    simp
end PositivityTheory.KReal
end


