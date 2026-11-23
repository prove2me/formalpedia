-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_CommuteGelfandInvariantMatrixUnitsOfGlRel
-- name    : Development_AbelianVarietyTheory_Proofs_HeightProofs_CommuteGelfandInvariantMatrixUnitsOfGlRel
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:03:26.407738+00:00
-- url     : https://prove2.me/theorems/ac165190-507a-422b-b8d6-e6acbc4b66ba
-- title:
--   Commute Gelfand Invariant Matrix Units Of Gl Rel
-- statement:
--   Definitions and structural lemmas for Commute Gelfand Invariant Matrix Units Of Gl Rel, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/CommuteGelfandInvariantMatrixUnitsOfGlRel.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PowEntryCommutator
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
namespace GlobalTheory.SmoothForms
section GelfandCentral
variable {A : Type} [Ring A] {n : ℕ}
end GelfandCentral
end GlobalTheory.SmoothForms


