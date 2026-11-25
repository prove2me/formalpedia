-- Prove2me | Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_MetaplecticUnipotentBlockSecondDiag
-- name    : Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_MetaplecticUnipotentBlockSecondDiag
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T12:23:37.945941+00:00
-- url     : https://prove2.me/theorems/950c2afc-60d9-4590-b760-50c568e8b3ac
-- title:
--   Metaplectic Unipotent Block Second Diag
-- statement:
--   Definitions and structural lemmas for Metaplectic Unipotent Block Second Diag, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/MetaplecticDerivatives/MetaplecticUnipotentBlockSecondDiag.lean

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_ContinuousPair
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E Filter Topology PositivityTheory.ThKR.LL LineDeriv
open scoped Real RealInnerProductSpace FourierTransform
namespace PositivityTheory.ThKR.Mp
variable {l : Type} [Fintype l] [DecidableEq l]
def nn (S : Matrix l l ℝ) (t : ℝ) : Mat l := fromBlocks 1 (t • S) 0 1
def UU (S : Matrix l l ℝ) (t : ℝ) : Sch l →L[ℂ] Sch l :=
  fou l * (ph (-(t • Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S)) * fouInv l)
end PositivityTheory.ThKR.Mp


