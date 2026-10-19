-- Prove2me | Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveIterationBudget
-- name    : MIPRE_Foundations_Introspection_AdaptiveIterationBudget
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T00:51:32.612523+00:00
-- url     : https://prove2.me/theorems/7a884e2f-83b8-4bb4-8062-26b9e5c8d811
-- title:
--   Definitions of AdaptiveIterationBudget: A positive small-error threshold for every adaptive stage The failure recurrence has an explicit inverse threshold
-- statement:
--   The definitions of the module `MIPRE.Foundations.Introspection.AdaptiveIterationBudget` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). A positive small-error threshold for every adaptive stage. The failure recurrence has an explicit inverse threshold. For any fixed depth and number of replacements, sufficiently small initial and primitive errors keep every common stage budget at most one. The construction uses the proved triple-square-root replacement loss; no stage-smallness premise is built into the threshold.
--
--   **Definitions** (2): `MIPRE.Introspection.adaptiveBudgetCoefficient` (A coefficient controlling the whole stage when its three error inputs are all at most the same number.); `MIPRE.Introspection.adaptiveSmallThreshold` (Explicit inverse thresholds.).
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Introspection.AdaptiveIterationBudget` (`MIPRE/Foundations/Introspection/AdaptiveIterationBudget.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 2 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/AdaptiveIterationBudget.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/AdaptiveIterationBudget.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Introspection_ErrorBounds
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveStageBudget

/-! # A positive small-error threshold for every adaptive stage

The failure recurrence has an explicit inverse threshold. For any fixed
depth and number of replacements, sufficiently small initial and primitive
errors keep every common stage budget at most one. The construction uses
the proved triple-square-root replacement loss; no stage-smallness premise
is built into the threshold.
-/

noncomputable section
namespace MIPRE.Introspection

/-- A coefficient controlling the whole stage when its three error inputs
are all at most the same number. -/
def adaptiveBudgetCoefficient (r : ℕ) (edges : ℝ) : ℝ :=
  (512 * (r : ℝ) ^ 2 + 224) * edges + 128

/-- Explicit inverse thresholds. The half-size term controls the old
failure and the eighth-power term controls the new replacement loss. -/
def adaptiveSmallThreshold (r : ℕ) (edges : ℝ) : ℕ → ℝ
  | 0 => 1 / adaptiveBudgetCoefficient r edges
  | n + 1 => min (adaptiveSmallThreshold r edges n / 2)
      ((adaptiveSmallThreshold r edges n / 16) ^ 8 / adaptiveBudgetCoefficient r edges)

end MIPRE.Introspection
end


