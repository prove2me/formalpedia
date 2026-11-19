-- Prove2me | Definitions.Def_LevyStochCalc_Probability_StoppedProgressive_F001
-- name    : LevyStochCalc_Probability_StoppedProgressive_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T23:30:06.903125+00:00
-- url     : https://prove2.me/theorems/17ddbc4d-acc7-4c7a-8837-e5f024e83d2e
-- title:
--   Source declarations: LevyStochCalc.Probability.StoppedProgressive
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Probability.StoppedProgressive. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_Progressive_F002
import Mathlib.Probability.Process.Stopping

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Stopping a progressively measurable process

Cutting a process off at a stopping time keeps it progressively measurable: before a time `t` the
region `{(ω, s) : s ≤ t, s ≤ τ ω}` is the complement, inside `Ω × (-∞, t]`, of a countable union
of rectangles `{τ ≤ q} × (q, t]` over the rationals, each measurable for the σ-algebra at `t`.
-/

open MeasureTheory

namespace LevyStochCalc.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The whole region cut out by a stopping time. -/
def stoppedSet (τ : Ω → WithTop ℝ) : Set (Ω × ℝ) :=
  {p : Ω × ℝ | ((p.2 : ℝ) : WithTop ℝ) ≤ τ p.1}
end LevyStochCalc.Probability


