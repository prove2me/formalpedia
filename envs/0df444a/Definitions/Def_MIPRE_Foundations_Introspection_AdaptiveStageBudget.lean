-- Prove2me | Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveStageBudget
-- name    : MIPRE_Foundations_Introspection_AdaptiveStageBudget
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T00:50:24.839606+00:00
-- url     : https://prove2.me/theorems/a8f82c83-3399-4b6f-9af1-f9d90d14b33e
-- title:
--   Definitions of AdaptiveStageBudget: One common quantitative budget for the adaptive stage The three actual-test estimates share one budget
-- statement:
--   The definitions of the module `MIPRE.Foundations.Introspection.AdaptiveStageBudget` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). One common quantitative budget for the adaptive stage. The three actual-test estimates share one budget. The malformed-answer contribution is included in the marginal constant. The replacement loss has three square roots, and the same recurrence can be used at every level.
--
--   **Definitions** (3): `MIPRE.Introspection.adaptiveFailureBudget` (An explicit failure recurrence with fixed primitive errors.); `MIPRE.Introspection.adaptiveStageBudget` (`e` is ordered-edge count times game failure; `z` and `h` are the primitive Z and fixed hiding errors.); `MIPRE.Introspection.adaptiveStepLoss` (The exact game-value loss from mixing, common-ancilla dilation, and projective measurement replacement.).
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Introspection.AdaptiveStageBudget` (`MIPRE/Foundations/Introspection/AdaptiveStageBudget.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 1 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/AdaptiveStageBudget.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/AdaptiveStageBudget.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Introspection_ErrorBounds

/-! # One common quantitative budget for the adaptive stage

The three actual-test estimates share one budget. The malformed-answer
contribution is included in the marginal constant. The replacement loss
has three square roots, and the same recurrence can be used at every level.
-/

namespace MIPRE.Introspection

/-- `e` is ordered-edge count times game failure; `z` and `h` are the
primitive Z and fixed hiding errors. `r` is the remaining CL depth. -/
def adaptiveStageBudget (r : ℕ) (e z h : ℝ) : ℝ :=
  64 * z + (512 * (r : ℝ) ^ 2 + 224) * e + 64 * h

/-- The exact game-value loss from mixing, common-ancilla dilation, and
projective measurement replacement. -/
noncomputable def adaptiveStepLoss (δ : ℝ) : ℝ :=
  2 * Real.sqrt (2 * Real.sqrt (56 * Real.sqrt δ))

/-- An explicit failure recurrence with fixed primitive errors. It records
the loss from each replacement; constructing the strategies is separate. -/
noncomputable def adaptiveFailureBudget (r : ℕ) (edges z h initial : ℝ) : ℕ → ℝ
  | 0 => initial
  | n + 1 => let e := adaptiveFailureBudget r edges z h initial n
      e + adaptiveStepLoss (adaptiveStageBudget r (edges * e) z h)

end MIPRE.Introspection


