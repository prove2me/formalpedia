-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsIsometryLift
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsIsometryLift
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T18:28:17.738829+00:00
-- url     : https://prove2.me/theorems/c6d24d0a-41b6-463c-8efd-f5a01017727e
-- title:
--   Exists Isometry Lift
-- statement:
--   Definitions and structural lemmas for Exists Isometry Lift, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsIsometryLift.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_LevelActionTransitions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ModNOfDvdModulus
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
namespace GlobalTheory.IsoLift
open GlobalTheory.SimLift GlobalTheory.IndefiniteRowSideFullHecke.LevelActionTransitions
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
end GlobalTheory.IsoLift
namespace GlobalTheory
open SimLift IsoLift IndefiniteRowSideFullHecke.LevelActionTransitions
end GlobalTheory


