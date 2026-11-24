-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_ResolutionCharZero_FromResIso
-- name    : Development_WeilBound_CoreStatements_ResolutionCharZero_FromResIso
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:36:27.273151+00:00
-- url     : https://prove2.me/theorems/27e9e233-682b-4f9f-ae57-bd00722b30ca
-- title:
--   From Res Iso
-- statement:
--   Definitions and structural lemmas for From Res Iso, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/ResolutionCharZero/FromResIso.lean

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Statements
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupIsoOffCenter
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
namespace PositivityTheory.ResPlug.FromRes
open FunctorialResolution
end PositivityTheory.ResPlug.FromRes


