-- Prove2me | Definitions.Def_EthierKurtz_SolvesBrownianSDE
-- name    : EthierKurtz_SolvesBrownianSDE
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T05:49:18.956283+00:00
-- url     : https://prove2.me/theorems/6644353c-9202-43e1-a2c2-102f89dc98c2
-- title:
--   Strong Brownian stochastic integral equation solution
-- statement:
--   A continuous completed-past-adapted process satisfying the Brownian stochastic integral equation simultaneously at all times outside one null set.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986. Chapter 5, Section 3, equations (3.1)–(3.2), printed pp. 290–291 (PDF pp. 299–300).

import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_EthierKurtz_SDEDiffusion
import Definitions.Def_EthierKurtz_completedBrownianPast
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace EthierKurtz

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

/-- Equation (3.1), with completion-adapted continuous paths. Component integrals
are continuous adapted versions, and the equation holds outside ONE null set
at all times. The theorem supplies W's Brownian property and ξ's independence,
which make W Brownian for the prescribed filtration. -/
def SolvesBrownianSDE (P : Measure Ω)
    (σ : ℝ≥0 × SDEState d → SDEDiffusion d)
    (b : ℝ≥0 × SDEState d → SDEState d)
    (W : ℝ≥0 → Ω → SDEState d) (ξ : Ω → SDEState d)
    (X : ℝ≥0 → Ω → SDEState d) : Prop :=
  (∀ t, Measurable (X t)) ∧
  (∀ ω, Continuous (fun t => X t ω)) ∧
  (∀ t, Measurable[completedBrownianPast P W ξ t] (X t)) ∧
  (X 0 =ᵐ[P] ξ) ∧
  ∃ J : ℝ≥0 → Ω → SDEDiffusion d,
    (∀ ω, Continuous (fun t => J t ω)) ∧
    (∀ t, Measurable[completedBrownianPast P W ξ t] (J t)) ∧
    (∀ i j, HasBrownianItoIntegral P (completedBrownianPast P W ξ)
      (fun t ω => W t ω j) (fun t ω => σ (t, X t ω) (i, j))
      (fun t ω => J t ω (i, j))) ∧
    (∀ (t : ℝ≥0) ω i, IntervalIntegrable (fun u : ℝ => b (u.toNNReal, X u.toNNReal ω) i)
      volume 0 t.val) ∧
    ∀ᵐ ω ∂P, ∀ t i, X t ω i = X 0 ω i + (∑ j, J t ω (i, j)) +
      ∫ u in (0 : ℝ)..t.val, b (u.toNNReal, X u.toNNReal ω) i

end EthierKurtz


