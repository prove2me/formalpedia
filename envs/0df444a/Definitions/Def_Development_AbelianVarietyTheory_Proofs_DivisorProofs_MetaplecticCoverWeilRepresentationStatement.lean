-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MetaplecticCoverWeilRepresentationStatement
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_MetaplecticCoverWeilRepresentationStatement
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T23:54:05.058778+00:00
-- url     : https://prove2.me/theorems/f694d692-7edc-4c11-80d5-2bfdbfe9134f
-- title:
--   Metaplectic Cover Weil Representation Statement
-- statement:
--   Definitions and structural lemmas for Metaplectic Cover Weil Representation Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MetaplecticCoverWeilRepresentationStatement.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MetaplecticCoverWeilRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IteratedLineDerivMemWeylAlg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsEqTransposeMulDiagonalMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate


