-- Prove2me | Definitions.Def_LevyStochCalc_Probability_StoppedProgressive_F000
-- name    : LevyStochCalc_Probability_StoppedProgressive_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T22:30:06.703407+00:00
-- url     : https://prove2.me/theorems/c01f3eab-a821-4d38-8963-6c3cadff9eda
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

/-- A process cut off at a stopping time. -/
noncomputable def stopped (τ : Ω → WithTop ℝ) (H : Ω → ℝ → ℝ) (ω : Ω) (s : ℝ) : ℝ :=
  if (s : WithTop ℝ) ≤ τ ω then H ω s else 0
theorem abs_stopped_le (τ : Ω → WithTop ℝ) (H : Ω → ℝ → ℝ) (ω : Ω) (s : ℝ) :
    |stopped τ H ω s| ≤ |H ω s| := by
  rw [stopped]
  split_ifs
  · exact le_rfl
  · simp
/-- The region cut out by a stopping time before a time `t`. -/
def stoppedRegion (τ : Ω → WithTop ℝ) (t : ℝ) : Set (Ω × ℝ) :=
  {p : Ω × ℝ | p.2 ≤ t ∧ ((p.2 : ℝ) : WithTop ℝ) ≤ τ p.1}
theorem mem_stoppedRegion {τ : Ω → WithTop ℝ} {t : ℝ} {p : Ω × ℝ} :
    p ∈ stoppedRegion τ t ↔ p.2 ≤ t ∧ ((p.2 : ℝ) : WithTop ℝ) ≤ τ p.1 := Iff.rfl
end LevyStochCalc.Probability


