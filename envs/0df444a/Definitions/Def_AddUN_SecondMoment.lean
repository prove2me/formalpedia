-- Prove2me | Definitions.Def_AddUN_SecondMoment
-- name    : AddUN_SecondMoment
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T07:21:53.995791+00:00
-- url     : https://prove2.me/theorems/64032de1-2c48-4817-b875-2249e576c2f1
-- title:
--   Second Moment
-- statement:
--   Definitions and structural lemmas for Second Moment, from VictorLiwentao (VictorLiwentao/open-logic-24-add-un; see pinned Apache-2.0 LICENSE and source headers)'s pinned Additivity of universally null sets and Goto Question 6.3 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/SecondMoment.lean

module
public import Definitions.Def_AddUN_CantorMeasure
public import Mathlib.MeasureTheory.Integral.Bochner.Set
set_option autoImplicit false
@[expose] public section
@[expose] public section
open Set MeasureTheory
namespace MeasureTheory
noncomputable def ind (S : Set (ℕ → Bool)) (w : ℕ → Bool) : ℝ := S.indicator (fun _ ↦ 1) w
end MeasureTheory


