-- Prove2me | Definitions.Def_MIPRE_Foundations_Introspection_AdaptivePowerBudget
-- name    : MIPRE_Foundations_Introspection_AdaptivePowerBudget
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T00:51:59.516405+00:00
-- url     : https://prove2.me/theorems/bb60e929-0720-462e-a58b-301a7f0079d5
-- title:
--   Definitions of AdaptivePowerBudget: Power bounds for the full finite adaptive recurrence Each replacement introduces three square roots
-- statement:
--   The definitions of the module `MIPRE.Foundations.Introspection.AdaptivePowerBudget` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Power bounds for the full finite adaptive recurrence. Each replacement introduces three square roots. For any fixed number of replacements the actual failure recurrence is bounded by an explicit constant times the corresponding iterated root of a common primitive error. A second explicit coefficient makes this bound at least one outside the proved admissible small-error regime. These numerical statements do not assume the existence or soundness of the strategy construction.
--
--   **Definitions** (2): `MIPRE.Introspection.adaptivePowerCoefficient` (The coefficient accumulated per replacement in a simple power bound.); `MIPRE.Introspection.adaptiveSoundnessCoefficient` (This fixed coefficient also pays for the trivial probability bound outside the admissible regime.).
--
--   **Embedded lemmas** (2): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `self_le_sqrt_of_unit`, `sqrt_scale_le`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Introspection.AdaptivePowerBudget` (`MIPRE/Foundations/Introspection/AdaptivePowerBudget.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 3 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/AdaptivePowerBudget.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/AdaptivePowerBudget.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Introspection_ErrorBounds
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveStageBudget
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveIterationBudget

/-! # Power bounds for the full finite adaptive recurrence

Each replacement introduces three square roots. For any fixed number of
replacements the actual failure recurrence is bounded by an explicit
constant times the corresponding iterated root of a common primitive
error. A second explicit coefficient makes this bound at least one outside
the proved admissible small-error regime. These numerical statements do not
assume the existence or soundness of the strategy construction.
-/

noncomputable section
namespace MIPRE.Introspection

theorem self_le_sqrt_of_unit {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t ≤ Real.sqrt t := by
  have hs := Real.sq_sqrt ht0
  have hr0 := Real.sqrt_nonneg t
  have hr1 := Real.sqrt_le_one.mpr ht1
  nlinarith [mul_nonneg hr0 (sub_nonneg.mpr hr1)]

theorem sqrt_scale_le {c t : ℝ} (hc : 1 ≤ c) :
    Real.sqrt (c * t) ≤ c * Real.sqrt t := by
  rw [Real.sqrt_mul (by linarith : 0 ≤ c)]
  exact mul_le_mul_of_nonneg_right
    (Real.sqrt_le_self_iff.mpr (Or.inr hc)) (Real.sqrt_nonneg t)

/-- The coefficient accumulated per replacement in a simple power bound. -/
def adaptivePowerCoefficient (r : ℕ) (edges : ℝ) : ℝ :=
  1 + 8 * adaptiveBudgetCoefficient r edges

/-- This fixed coefficient also pays for the trivial probability bound
outside the admissible regime. The denominator is strictly positive. -/
def adaptiveSoundnessCoefficient (r : ℕ) (edges : ℝ) (n : ℕ) : ℝ :=
  max (adaptivePowerCoefficient r edges ^ n)
    (1 / iteratedRoot (3 * n) (adaptiveSmallThreshold r edges n))

end MIPRE.Introspection
end


