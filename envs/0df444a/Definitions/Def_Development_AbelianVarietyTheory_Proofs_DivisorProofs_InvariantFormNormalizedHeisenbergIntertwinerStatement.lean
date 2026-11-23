-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InvariantFormNormalizedHeisenbergIntertwinerStatement
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_InvariantFormNormalizedHeisenbergIntertwinerStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:17:33.28957+00:00
-- url     : https://prove2.me/theorems/5a952d7d-83ed-433f-985b-bcb2587c2f59
-- title:
--   Invariant Form Normalized Heisenberg Intertwiner Statement
-- statement:
--   Definitions and structural lemmas for Invariant Form Normalized Heisenberg Intertwiner Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InvariantFormNormalizedHeisenbergIntertwinerStatement.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InvariantFormNormalizedHeisenbergIntertwiner
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumOpTransversal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_HeisenbergIntertwiningSumsCompEqIndex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_NormalizedHeisenbergIntertwinerComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIntertwinerHeisenbergCocycleOfFixedVector
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsWeilRepresentationHeisenberg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SpanHeisenbergTranslatesVacuumEqTop
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical GlobalTheory.FinWeil
open scoped BigOperators


