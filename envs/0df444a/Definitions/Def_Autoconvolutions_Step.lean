-- Prove2me | Definitions.Def_Autoconvolutions_Step
-- name    : Autoconvolutions_Step
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T11:48:10.340831+00:00
-- url     : https://prove2.me/theorems/d092b9e0-5816-42ee-a984-3fa8158ceae0
-- title:
--   Step
-- statement:
--   Definitions and structural lemmas for Step, from Vjekoslav Kovač's pinned Sharpness for autoconvolutions development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Step.lean

module
public import Definitions.Def_Autoconvolutions_Definitions
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.Convolution
set_option autoImplicit true
@[expose] public section
@[expose] public section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace Autoconvolutions
end Autoconvolutions


