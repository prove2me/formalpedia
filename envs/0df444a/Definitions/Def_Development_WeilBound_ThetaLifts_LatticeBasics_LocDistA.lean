-- Prove2me | Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistA
-- name    : Development_WeilBound_ThetaLifts_LatticeBasics_LocDistA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:53:55.732327+00:00
-- url     : https://prove2.me/theorems/5879ef8f-3a43-4368-849a-2a3801ed5c81
-- title:
--   Loc Dist A
-- statement:
--   Definitions and structural lemmas for Loc Dist A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/LocDistA.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCompactOpenAddSubgroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology GlobalTheory.WeilM
namespace GlobalTheory.ThK.Dbl.LD
def Bump {V : Type} [Zero V] [TopologicalSpace V] (g : V → ℂ) : Prop := g ∈ SB V ∧ (∀ x, g x = 0 ∨ g x = 1) ∧ g 0 = 1
end GlobalTheory.ThK.Dbl.LD


