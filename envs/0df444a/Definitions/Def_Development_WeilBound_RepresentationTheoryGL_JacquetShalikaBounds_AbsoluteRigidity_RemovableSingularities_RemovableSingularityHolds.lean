-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_RemovableSingularities_RemovableSingularityHolds
-- name    : Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_RemovableSingularities_RemovableSingularityHolds
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:06:25.639326+00:00
-- url     : https://prove2.me/theorems/ffb8d480-607c-4802-a193-9cc4e14d0e3a
-- title:
--   Removable Singularity Holds
-- statement:
--   Definitions and structural lemmas for Removable Singularity Holds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/JacquetShalikaBounds/AbsoluteRigidity/RemovableSingularities/RemovableSingularityHolds.lean

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_NewtonLow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
namespace PositivityTheory.RgJS
namespace RemovableSingularityAlt
def D (G : ℂ → ℂ) : ℕ → ℂ → ℂ
  | 0 => G
  | j + 1 => dslope (D G j) 1
end RemovableSingularityAlt
end PositivityTheory.RgJS


