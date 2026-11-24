-- Prove2me | Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistB
-- name    : Development_WeilBound_ThetaLifts_LatticeBasics_LocDistB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:09:25.672384+00:00
-- url     : https://prove2.me/theorems/34871daa-1864-400f-8180-d6435ee456b7
-- title:
--   Loc Dist B
-- statement:
--   Definitions and structural lemmas for Loc Dist B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/LocDistB.lean

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology GlobalTheory.WeilM
namespace GlobalTheory.ThK.Dbl.LD
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
noncomputable def ind (K : Subgroup G) : G → ℂ := Set.indicator (K : Set G) fun _ => 1
end GlobalTheory.ThK.Dbl.LD


