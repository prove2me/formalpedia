-- Prove2me | Definitions.Def_auto_M05_f3f59_EthierKurtz_IsSourceLocalMartingale
-- name    : auto_M05_f3f59_EthierKurtz_IsSourceLocalMartingale
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T18:50:06.908449+00:00
-- url     : https://prove2.me/theorems/da23ac6a-d65f-4ceb-b2e6-b976e2aec556
-- title:
--   Local martingales by stopping
-- statement:
--   There is a sequence of stopping times increasing almost surely to infinity such that every stopped process is a martingale.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986, Chapter 5 §2, Theorem 2.9, printed p.287 (PDF p.296), equations (2.40)–(2.41); conventions pp.279–280,286 (PDF pp.288–289,295). https://doi.org/10.1002/9780470316658.ch5

import Definitions.Def_auto_M05_f3f59_EthierKurtz_itoStepSum

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators

namespace EthierKurtz

variable {Ω : Type*} [MeasurableSpace Ω]

def IsSourceLocalMartingale {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (X : ℝ≥0 → Ω → ℝ) : Prop :=
  ∃ τ : ℕ → Ω → WithTop ℝ≥0, IsLocalizingSequence ℱ τ P ∧
    ∀ n, Martingale (stoppedProcess X (τ n)) ℱ P

end EthierKurtz


