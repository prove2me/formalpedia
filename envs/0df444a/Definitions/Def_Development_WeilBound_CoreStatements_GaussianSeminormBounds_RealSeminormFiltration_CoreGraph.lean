-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreGraph
-- name    : Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreGraph
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T12:24:13.985646+00:00
-- url     : https://prove2.me/theorems/558108bf-fa02-5684-9578-e895ccbfe1e6
-- title:
--   Core Graph
-- statement:
--   Definitions and structural lemmas for Core Graph, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreGraph.lean

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCyc
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
def prodAct {p q : ℕ} {A B : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    (ρA : Mat p q →ₗ[ℂ] Module.End ℂ A) (ρB : Mat p q →ₗ[ℂ] Module.End ℂ B) :
    Mat p q →ₗ[ℂ] Module.End ℂ (A × B) where
  toFun Z := (ρA Z).prodMap (ρB Z)
  map_add' Z Z' := by
    refine LinearMap.ext fun n => ?_
    simp
  map_smul' a Z := by
    refine LinearMap.ext fun n => ?_
    simp
end PositivityTheory.KReal
end


