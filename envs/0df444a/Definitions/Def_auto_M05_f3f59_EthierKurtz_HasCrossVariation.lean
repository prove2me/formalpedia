-- Prove2me | Definitions.Def_auto_M05_f3f59_EthierKurtz_HasCrossVariation
-- name    : auto_M05_f3f59_EthierKurtz_HasCrossVariation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T18:50:48.95484+00:00
-- url     : https://prove2.me/theorems/af435b25-9bed-42b0-bbee-8b33b3a23cba
-- title:
--   Quadratic covariation by increment products
-- statement:
--   At each time, dyadic sums of products of increments converge in probability to the proposed cross-variation process.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986, Chapter 5 §2, Theorem 2.9, printed p.287 (PDF p.296), equations (2.40)–(2.41); conventions pp.279–280,286 (PDF pp.288–289,295). https://doi.org/10.1002/9780470316658.ch5

import Definitions.Def_auto_M05_f3f59_EthierKurtz_IsSourceLocalMartingale

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators

namespace EthierKurtz

variable {Ω : Type*} [MeasurableSpace Ω]

def HasCrossVariation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X Y A : ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ t : ℝ≥0, TendstoInMeasure P
    (fun m ω => ∑ k ∈ Finset.range (2 ^ m),
      (X (((k : ℝ≥0) + 1) * t / 2 ^ m) ω - X ((k : ℝ≥0) * t / 2 ^ m) ω) *
      (Y (((k : ℝ≥0) + 1) * t / 2 ^ m) ω - Y ((k : ℝ≥0) * t / 2 ^ m) ω))
    atTop (A t)

end EthierKurtz


