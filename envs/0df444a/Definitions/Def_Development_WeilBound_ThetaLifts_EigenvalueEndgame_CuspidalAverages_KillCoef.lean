-- Prove2me | Definitions.Def_Development_WeilBound_ThetaLifts_EigenvalueEndgame_CuspidalAverages_KillCoef
-- name    : Development_WeilBound_ThetaLifts_EigenvalueEndgame_CuspidalAverages_KillCoef
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:34:33.718884+00:00
-- url     : https://prove2.me/theorems/df82fd4a-aa97-48b5-9487-bb959792b016
-- title:
--   Kill Coef
-- statement:
--   Definitions and structural lemmas for Kill Coef, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/EigenvalueEndgame/CuspidalAverages/KillCoef.lean

import Definitions.Def_Development_WeilBound_ThetaLifts_EigenvalueEndgame_SignatureSplitting_ConvCont
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PositivityTheory.ThKEnd.Cusp
open MeasureTheory Topology Filter PositivityTheory.ThKEnd.Two
open scoped Pointwise
variable {G X : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] {Γ : Subgroup G} {n : X → G}
  {a : G} {lam : Measure X} [IsProbabilityMeasure lam] {φ c : G → ℂ}
end PositivityTheory.ThKEnd.Cusp
end


