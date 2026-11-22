-- Prove2me | Definitions.Def_Autoconvolutions_Interpolation
-- name    : Autoconvolutions_Interpolation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T11:48:08.033825+00:00
-- url     : https://prove2.me/theorems/930c019f-7555-47cb-b39e-ecb4596e2892
-- title:
--   Interpolation
-- statement:
--   Definitions and structural lemmas for Interpolation, from Vjekoslav Kovač's pinned Sharpness for autoconvolutions development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Interpolation.lean

module
public import Definitions.Def_Autoconvolutions_Definitions
public import Mathlib.Analysis.Convolution
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic
set_option autoImplicit true
@[expose] public section
@[expose] public section
open MeasureTheory Set Filter
open scoped ENNReal BigOperators
namespace Autoconvolutions
noncomputable def cell (a v : ℝ) : ℝ → ℝ := (Ico a (a+1)).indicator (fun _ => v)
noncomputable def tent (x : ℝ) : ℝ := max 0 (min x (2-x))
noncomputable def convCoeff (d : ℕ) (p : Fin (d+1) → ℝ) (k : ℤ) : ℝ :=
  ∑ i, ∑ j, if (i.val : ℤ) + j.val = k then p i * p j else 0
end Autoconvolutions


