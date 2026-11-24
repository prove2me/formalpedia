-- Prove2me | Definitions.Def_Development_WeilBound_ThetaLifts_SmallCones_RightOfCompact
-- name    : Development_WeilBound_ThetaLifts_SmallCones_RightOfCompact
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:58:44.851939+00:00
-- url     : https://prove2.me/theorems/7d13afc0-e049-4428-9338-265bff8fbb13
-- title:
--   Right Of Compact
-- statement:
--   Definitions and structural lemmas for Right Of Compact, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SmallCones/RightOfCompact.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Set
open scoped ENNReal NNReal Pointwise
namespace PositivityTheory.ThKCT.Unf
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
variable (ν : Measure G) [ν.IsHaarMeasure] (m : Measure G) [SFinite m] {P : Set G} {K : Subgroup G}
end PositivityTheory.ThKCT.Unf


