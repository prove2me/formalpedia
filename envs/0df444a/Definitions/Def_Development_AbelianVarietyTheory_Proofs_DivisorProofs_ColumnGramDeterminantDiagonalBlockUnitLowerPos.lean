-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ColumnGramDeterminantDiagonalBlockUnitLowerPos
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ColumnGramDeterminantDiagonalBlockUnitLowerPos
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T01:37:28.149679+00:00
-- url     : https://prove2.me/theorems/96fcdd1b-3a05-47a3-bc5b-bd5ae0ad2da1
-- title:
--   Column Gram Determinant Diagonal Block Unit Lower Pos
-- statement:
--   Definitions and structural lemmas for Column Gram Determinant Diagonal Block Unit Lower Pos, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ColumnGramDeterminantDiagonalBlockUnitLowerPos.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NmatEqLowMat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix
namespace GlobalTheory.IntBall.ColGramPos
open scoped ComplexOrder
end GlobalTheory.IntBall.ColGramPos


