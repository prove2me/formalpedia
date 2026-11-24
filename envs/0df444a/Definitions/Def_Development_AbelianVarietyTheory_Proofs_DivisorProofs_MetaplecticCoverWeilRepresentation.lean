-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MetaplecticCoverWeilRepresentation
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_MetaplecticCoverWeilRepresentation
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T23:48:10.3568+00:00
-- url     : https://prove2.me/theorems/412739a6-bf42-42ee-9d0c-3236b262c90e
-- title:
--   Metaplectic Cover Weil Representation
-- statement:
--   Definitions and structural lemmas for Metaplectic Cover Weil Representation, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MetaplecticCoverWeilRepresentation.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IteratedLineDerivMemWeylAlg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsEqTransposeMulDiagonalMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MetaplecticGaussianNormalisedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousMetaplecticSchwartzActionProdStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzEqGaussianOfFderivEqMulVecStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SymplecticHolPartDetNeZeroAndIsSymmStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FderivEqMulVecOfSchrodingerAnnihilatedStatement
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


