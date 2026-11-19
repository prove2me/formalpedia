-- Prove2me | Definitions.Def_DeletionCode_FiniteDiscard
-- name    : DeletionCode_FiniteDiscard
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T05:29:08.7359+00:00
-- url     : https://prove2.me/theorems/2b6578f4-a54e-4c87-9cb7-44994c81f528
-- title:
--   Finite Discard
-- statement:
--   Definitions and structural lemmas for Finite Discard, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/FiniteDiscard.lean

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Finiteness
set_option autoImplicit true
namespace DeletionCode.FiniteDiscard
open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable
variable {Ω V : Type*} [MeasurableSpace Ω] [DecidableEq V]
end
end DeletionCode.FiniteDiscard


