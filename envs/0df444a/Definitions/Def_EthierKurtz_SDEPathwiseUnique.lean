-- Prove2me | Definitions.Def_EthierKurtz_SDEPathwiseUnique
-- name    : EthierKurtz_SDEPathwiseUnique
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T05:51:12.497189+00:00
-- url     : https://prove2.me/theorems/d7bed169-ea2b-4f77-b0c6-f836474185ce
-- title:
--   Pathwise uniqueness for an SDE
-- statement:
--   On every common probability space, filtration, and Brownian driver, weak solutions with almost surely equal initial values are indistinguishable.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986. Chapter 5, Section 3, pathwise uniqueness convention and Theorem 3.6, printed pp. 291, 296 (PDF pp. 300, 305).

import Definitions.Def_EthierKurtz_IsWeakSDESolution

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace EthierKurtz

universe u

/-- Pathwise uniqueness for every probability space and filtration: equal
initial variables on the same space with the same driver give indistinguishability. -/
def SDEPathwiseUnique {d : ℕ}
    (σ : ℝ≥0 × SDEState d → SDEDiffusion d)
    (b : ℝ≥0 × SDEState d → SDEState d) (μ : Measure (SDEState d)) : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω), IsProbabilityMeasure P →
    ∀ (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
      (W X Y : ℝ≥0 → Ω → SDEState d),
      IsWeakSDESolution P ℱ σ b μ W X →
      IsWeakSDESolution P ℱ σ b μ W Y →
      X 0 =ᵐ[P] Y 0 → ∀ᵐ ω ∂P, ∀ t, X t ω = Y t ω

end EthierKurtz


