-- Prove2me | Definitions.Def_MIPRE_Foundations_Introspection_ErrorBounds
-- name    : MIPRE_Foundations_Introspection_ErrorBounds
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T00:49:57.539321+00:00
-- url     : https://prove2.me/theorems/e354b142-6794-4ea2-8c3b-ad999d7807f3
-- title:
--   Definitions of ErrorBounds: Normalizing the final introspection error The paper's final soundness estimate absorbs any fixed concave power and…
-- statement:
--   The definitions of the module `MIPRE.Foundations.Introspection.ErrorBounds` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Normalizing the final introspection error. The paper's final soundness estimate absorbs any fixed concave power and constant multiple into `a * (x^a * ε^b + x^(-b))`. The coefficient and the new exponent are explicit here, including the normalization `a ≥ 1`, `0 < b ≤ 1`. No induction estimate is assumed or encoded by the definitions in this file.
--
--   **Definitions** (4): `MIPRE.Introspection.errorProfile` (The two terms of the introspection soundness loss, with `x = λ n`.); `MIPRE.Introspection.iteratedRoot` (Applying the square root a fixed finite number of times.); `MIPRE.Introspection.powerCoefficient` (The coefficient prescribed by the paper, enlarged also to be at least one.); `MIPRE.Introspection.rootExponent` (The exponent after `k` square roots.).
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Introspection.ErrorBounds` (`MIPRE/Foundations/Introspection/ErrorBounds.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/ErrorBounds.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/ErrorBounds.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Normalizing the final introspection error

The paper's final soundness estimate absorbs any fixed concave power and
constant multiple into `a * (x^a * ε^b + x^(-b))`. The coefficient and the new
exponent are explicit here, including the normalization `a ≥ 1`, `0 < b ≤ 1`.
No induction estimate is assumed or encoded by the definitions in this file.
-/

noncomputable section

namespace MIPRE.Introspection

/-- The two terms of the introspection soundness loss, with `x = λ n`. -/
def errorProfile (a b x ε : ℝ) : ℝ := a * (x ^ a * ε ^ b + x ^ (-b))

/-- The coefficient prescribed by the paper, enlarged also to be at least one. -/
def powerCoefficient (C a r : ℝ) : ℝ := max 1 (max (C * a ^ r) (a * r))

/-- The exponent after `k` square roots. -/
def rootExponent (k : ℕ) : ℝ := (1 / 2 : ℝ) ^ k

/-- Applying the square root a fixed finite number of times. -/
def iteratedRoot : ℕ → ℝ → ℝ
  | 0, t => t
  | k + 1, t => Real.sqrt (iteratedRoot k t)

end MIPRE.Introspection

end


