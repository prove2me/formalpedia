-- Prove2me | Definitions.Def_EthierKurtz_SolvesSDEMartingaleProblem
-- name    : EthierKurtz_SolvesSDEMartingaleProblem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T05:52:28.700927+00:00
-- url     : https://prove2.me/theorems/0aba2ed1-44c8-453a-bb4d-6ca7ffdc1a09
-- title:
--   Continuous diffusion martingale-problem solution
-- statement:
--   A continuous adapted process with prescribed initial law for which every smooth compactly supported generator test is a martingale.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986. Chapter 4 martingale-problem convention, printed pp. 173–174 (PDF pp. 182–183), and Chapter 5, Section 3, printed pp. 291, 293–294 (PDF pp. 300, 302–303).

import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_EthierKurtz_SDEDiffusion
import Definitions.Def_EthierKurtz_sdeTestGenerator

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators ContDiff

namespace EthierKurtz

/-- The continuous martingale problem for the graph (3.3), relative to the
specified filtration. Unlike the time-homogeneous natural-past adapter in
Chapter 4, this uses time-dependent coefficients and the entire given past. -/
def SolvesSDEMartingaleProblem {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (σ : ℝ≥0 × SDEState d → SDEDiffusion d)
    (b : ℝ≥0 × SDEState d → SDEState d) (μ : Measure (SDEState d))
    (X : ℝ≥0 → Ω → SDEState d) : Prop :=
  (∀ w, Continuous (fun t => X t w)) ∧ Adapted ℱ X ∧
  Measure.map (X 0) P = μ ∧
  ∀ f : SDEState d → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f →
    (∀ (t : ℝ≥0) w, IntervalIntegrable
      (fun r : ℝ => sdeTestGenerator σ b f r.toNNReal (X r.toNNReal w))
      volume 0 t.val) ∧
    Martingale (fun t w => f (X t w) -
      ∫ r in (0 : ℝ)..t.val,
        sdeTestGenerator σ b f r.toNNReal (X r.toNNReal w)) ℱ P

end EthierKurtz


