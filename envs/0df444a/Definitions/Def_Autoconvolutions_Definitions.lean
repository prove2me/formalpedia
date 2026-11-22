-- Prove2me | Definitions.Def_Autoconvolutions_Definitions
-- name    : Autoconvolutions_Definitions
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T11:47:44.419815+00:00
-- url     : https://prove2.me/theorems/cbc3fa99-e13a-42e9-a19b-4ac6bad2e39e
-- title:
--   Definitions
-- statement:
--   Definitions and structural lemmas for Definitions, from Vjekoslav Kovač's pinned Sharpness for autoconvolutions development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Definitions.lean

module
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
set_option autoImplicit true
@[expose] public section
@[expose] public section
open MeasureTheory
open scoped ENNReal BigOperators
namespace Autoconvolutions
noncomputable def step (d : ℕ) (p : Fin (d + 1) → ℝ) (x : ℝ) : ℝ :=
  ∑ j, (Set.Ico (j.val : ℝ) ((j.val : ℝ) + 1)).indicator (fun _ => p j) x
noncomputable def auto (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ t : ℝ, f t * f (x - t) ∂volume
noncomputable def ratio (f : ℝ → ℝ) : ℝ :=
  (eLpNorm (auto f) 2 volume).toReal ^ 2 /
    ((eLpNorm (auto f) 1 volume).toReal * (eLpNorm (auto f) ∞ volume).toReal)
end Autoconvolutions


