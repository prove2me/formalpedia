-- Prove2me | Definitions.Def_NearlyUnstableHawkes_Deterministic_CountingProcess
-- name    : NearlyUnstableHawkes_Deterministic_CountingProcess
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T01:41:25.558285+00:00
-- url     : https://prove2.me/theorems/4edc3739-25d9-41dd-bdad-03cfe53c0692
-- title:
--   §2.1, p. 5 — simple counting process on nonnegative time
-- statement:
--   A **simple counting process** $N_t$ starts at $N_0=0$, has nondecreasing, right-continuous paths taking values in the natural numbers, and has jumps of size at most one. Each $N_t$ is a measurable random variable. The process is observed through a finite horizon $T$.
--
--   $$N_0=0,\qquad N_t-N_{t-}\le 1\quad(0<t\le T).$$
--
--   This definition isolates the ordinary point-process structure used by the Hawkes model and its natural filtration.
--
--   **Formalization Note** Time is represented by real numbers, with all process conditions restricted to nonnegative time; the jump-size condition is restricted to the observation interval. The point process is allowed to continue after $T$.
-- source:
--   Jaisson and Rosenbaum, Limit theorems for nearly unstable Hawkes processes, arXiv:1310.2033v2, p. 5, §2.1

import Mathlib

noncomputable section

namespace NearlyUnstableHawkes.Deterministic

open MeasureTheory

/-- A simple counting process observed through `Tend`, independent of any intensity model. -/
structure IsCountingProcess {Ω : Type*} [MeasurableSpace Ω]
    (Tend : ℝ) (N : ℝ → Ω → ℕ) : Prop where
  measurable : ∀ t, 0 ≤ t → Measurable (N t)
  zero : ∀ ω, N 0 ω = 0
  monotone : ∀ ω, MonotoneOn (fun t => N t ω) (Set.Ici 0)
  right_continuous : ∀ ω t, 0 ≤ t →
    ContinuousWithinAt (fun s => (N s ω : ℝ)) (Set.Ici t) t
  unit_jumps : ∀ ω t, 0 < t → t ≤ Tend →
    (N t ω : ℝ) - Function.leftLim (fun s => (N s ω : ℝ)) t ≤ 1

end NearlyUnstableHawkes.Deterministic


