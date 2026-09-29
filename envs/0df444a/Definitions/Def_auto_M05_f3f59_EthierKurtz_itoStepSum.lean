-- Prove2me | Definitions.Def_auto_M05_f3f59_EthierKurtz_itoStepSum
-- name    : auto_M05_f3f59_EthierKurtz_itoStepSum
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T18:49:28.235985+00:00
-- url     : https://prove2.me/theorems/7ddeb13c-cc1b-4e56-8eeb-4515474caa5e
-- title:
--   Left dyadic integral sums
-- statement:
--   The finite left-point sum of coefficient values multiplied by the increments of a real-valued process on the dyadic partition of [0,t].
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986, Chapter 5 §2, Theorem 2.9, printed p.287 (PDF p.296), equations (2.40)–(2.41); conventions pp.279–280,286 (PDF pp.288–289,295). https://doi.org/10.1002/9780470316658.ch5

import Mathlib

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators

namespace EthierKurtz

variable {Ω : Type*} [MeasurableSpace Ω]

noncomputable def itoStepSum (W : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (n : ℕ)
    (a : ℕ → Ω → ℝ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range (2 ^ n), a k ω *
    (W (((k : ℝ≥0) + 1) * t / (2 : ℝ≥0) ^ n) ω -
      W ((k : ℝ≥0) * t / (2 : ℝ≥0) ^ n) ω)

end EthierKurtz


