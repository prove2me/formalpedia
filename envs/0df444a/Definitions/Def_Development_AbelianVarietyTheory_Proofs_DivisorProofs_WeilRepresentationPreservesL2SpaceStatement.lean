-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeilRepresentationPreservesL2SpaceStatement
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeilRepresentationPreservesL2SpaceStatement
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T22:45:55.440496+00:00
-- url     : https://prove2.me/theorems/896b8f34-ca4d-4bd6-b973-c409c179cb9c
-- title:
--   Weil Representation Preserves L2 Space Statement
-- statement:
--   Definitions and structural lemmas for Weil Representation Preserves L2 Space Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WeilRepresentationPreservesL2SpaceStatement.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeilRepresentationPreservesL2Space
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)


