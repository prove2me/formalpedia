-- Prove2me | Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_NormExpSubLe
-- name    : Development_WeilBound_ThetaLifts_Reductions_NormExpSubLe
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:29:41.45835+00:00
-- url     : https://prove2.me/theorems/a232e1fb-bea0-4e86-b0ca-f8fc2402962c
-- title:
--   Norm Exp Sub Le
-- statement:
--   Definitions and structural lemmas for Norm Exp Sub Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/NormExpSubLe.lean

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_IsoOfIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E Filter Topology
open scoped Real RealInnerProductSpace FourierTransform
namespace PositivityTheory.ThKR.LL
variable {l : Type} [Fintype l]
def mq (S : Eu l →L[ℝ] Eu l) : Sch l →L[ℂ] Sch l :=
  smulLeftCLM ℂ fun x : Eu l => ((-π * ⟪x, S x⟫ : ℝ) : ℂ) * I
def vf (H : Eu l →L[ℝ] Eu l) (f : Sch l) : Sch l :=
  bilinLeftCLM (ContinuousLinearMap.id ℝ (Eu l →L[ℝ] ℂ)) H.hasTemperateGrowth (fderivCLM ℝ (Eu l) ℂ f)
end PositivityTheory.ThKR.LL


