-- Prove2me | Definitions.Def_EthierKurtz_IsSourceLocalMartingale
-- name    : EthierKurtz_IsSourceLocalMartingale
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T05:43:47.661966+00:00
-- url     : https://prove2.me/theorems/67f1ac11-2395-4d08-abb5-626036ea03e4
-- title:
--   Continuous-time local martingale by stopped processes
-- statement:
--   A process admitting a localizing sequence of stopping times whose stopped processes are martingales.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986. Chapter 2, Section 3, local martingale convention; Chapter 5, Section 2, printed pp. 279, 286 (PDF pp. 288, 295).

import Mathlib

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators

namespace EthierKurtz

/-- Chapter 2 Section 3: stopped martingales along an increasing localizing
sequence. The source does not use the extra bottom-time indicator in `Locally`. -/
def IsSourceLocalMartingale {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (X : ℝ≥0 → Ω → ℝ) : Prop :=
  ∃ τ : ℕ → Ω → WithTop ℝ≥0, IsLocalizingSequence ℱ τ P ∧
    ∀ n, Martingale (stoppedProcess X (τ n)) ℱ P

end EthierKurtz


