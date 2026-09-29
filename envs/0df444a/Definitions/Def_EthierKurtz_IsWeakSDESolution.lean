-- Prove2me | Definitions.Def_EthierKurtz_IsWeakSDESolution
-- name    : EthierKurtz_IsWeakSDESolution
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T05:50:08.71309+00:00
-- url     : https://prove2.me/theorems/ae30c552-6bb8-4e7f-b2a3-69391f583a3e
-- title:
--   Weak stochastic integral equation solution
-- statement:
--   A continuous weak SDE solution with an adapted Brownian driver, independent future increments, prescribed initial law, and the stochastic integral equation.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986. Chapter 5, Section 3, equations (3.1)–(3.2), printed pp. 290–291 (PDF pp. 299–300).

import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_EthierKurtz_SDEDiffusion
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_EthierKurtz_completedSDEPast
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace EthierKurtz

/-- General weak solution in the sense of source p. 291, with an arbitrary
filtration. The Brownian past is independent of the ENTIRE future increment
process. The previously defined local Itô relation is reused unchanged. -/
def IsWeakSDESolution {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (σ : ℝ≥0 × SDEState d → SDEDiffusion d)
    (b : ℝ≥0 × SDEState d → SDEState d) (μ : Measure (SDEState d))
    (W X : ℝ≥0 → Ω → SDEState d) : Prop :=
  IsStandardBrownian P W ∧
  (∀ t, Measurable[ℱ t] (W t)) ∧
  (∀ t, Indep (ℱ t)
    (MeasurableSpace.comap (fun ω (r : Set.Ici t) => W r.val ω - W t ω)
      inferInstance) P) ∧
  (∀ t, Measurable (X t)) ∧
  (∀ ω, Continuous (fun t => X t ω)) ∧
  (∀ t, Measurable[completedSDEPast P ℱ t] (X t)) ∧
  Measure.map (X 0) P = μ ∧
  ∃ J : ℝ≥0 → Ω → SDEDiffusion d,
    (∀ ω, Continuous (fun t => J t ω)) ∧
    (∀ t, Measurable[completedSDEPast P ℱ t] (J t)) ∧
    (∀ i j, HasBrownianItoIntegral P (completedSDEPast P ℱ)
      (fun t ω => W t ω j) (fun t ω => σ (t, X t ω) (i, j))
      (fun t ω => J t ω (i, j))) ∧
    (∀ (t : ℝ≥0) ω i, IntervalIntegrable
      (fun r : ℝ => b (r.toNNReal, X r.toNNReal ω) i) volume 0 t.val) ∧
    ∀ᵐ ω ∂P, ∀ t i, X t ω i = X 0 ω i + (∑ j, J t ω (i, j)) +
      ∫ r in (0 : ℝ)..t.val, b (r.toNNReal, X r.toNNReal ω) i

end EthierKurtz


