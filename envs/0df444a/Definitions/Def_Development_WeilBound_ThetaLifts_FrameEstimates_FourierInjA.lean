-- Prove2me | Definitions.Def_Development_WeilBound_ThetaLifts_FrameEstimates_FourierInjA
-- name    : Development_WeilBound_ThetaLifts_FrameEstimates_FourierInjA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:11:53.208254+00:00
-- url     : https://prove2.me/theorems/0fcc404e-2b6f-4387-a2bd-484f805064fc
-- title:
--   Fourier Inj A
-- statement:
--   Definitions and structural lemmas for Fourier Inj A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/FrameEstimates/FourierInjA.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory BoundedContinuousFunction
namespace PositivityTheory.ThKEst.FourInj
variable {X A : Type} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
end PositivityTheory.ThKEst.FourInj


