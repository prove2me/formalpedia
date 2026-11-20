-- Prove2me | Definitions.Def_DeletionCode_PaperProbability
-- name    : DeletionCode_PaperProbability
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T07:02:56.135883+00:00
-- url     : https://prove2.me/theorems/789d9459-e545-4047-b1b7-f42d8fd0a859
-- title:
--   Paper Probability
-- statement:
--   Definitions and structural lemmas for Paper Probability, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/PaperProbability.lean

import Definitions.Def_DeletionCode_NonseparatedFamily
import Definitions.Def_DeletionCode_ObstructionBound
import Definitions.Def_DeletionCode_PaperParameters
import Theorems.Thm_DeletionCode_PaperParameters_threshold

set_option autoImplicit true
namespace DeletionCode.PaperProbability
open MeasureTheory Windows HeaderRecovery SignedSupport CircleUniform
open ExceptionalCountArithmetic ExceptionalProbability ObstructionProbability
open scoped ENNReal
def threshold (t : ℕ) : ℕ := max (4 * t + 2) (exceptionalConstant t)
end DeletionCode.PaperProbability


