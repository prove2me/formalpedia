-- Prove2me | Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_LocalLift
-- name    : Development_WeilBound_ThetaLifts_Reductions_LocalLift
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:31:44.01683+00:00
-- url     : https://prove2.me/theorems/04820e10-5c90-4acf-a38f-68411395e86f
-- title:
--   Local Lift
-- statement:
--   Definitions and structural lemmas for Local Lift, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/LocalLift.lean

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_NormExpSubLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E Filter Topology LineDeriv
open scoped Real RealInnerProductSpace FourierTransform
namespace PositivityTheory.ThKR.LL
variable {l : Type} [Fintype l] [DecidableEq l]
def bl (i j : l → l ⊕ l) : Matrix (l ⊕ l) (l ⊕ l) ℝ →ₗ[ℝ] (Eu l →L[ℝ] Eu l) where
  toFun g := Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) (g.submatrix i j)
  map_add' g h := by rw [← map_add]; rfl
  map_smul' c g := by rw [RingHom.id_apply, ← map_smul]; rfl
end PositivityTheory.ThKR.LL
namespace PositivityTheory.ThKR
open LL
end PositivityTheory.ThKR


