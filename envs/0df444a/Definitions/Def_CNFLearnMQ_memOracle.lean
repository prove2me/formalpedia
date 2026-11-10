-- Prove2me | Definitions.Def_CNFLearnMQ_memOracle
-- name    : CNFLearnMQ_memOracle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:12:15.291747+00:00
-- url     : https://prove2.me/theorems/81e483f0-7488-47ba-b120-12c68e3b46c7
-- title:
--   Membership oracle and uniform solution law of a CNF formula
-- statement:
--   For a CNF formula $\Phi$ on $n$ variables, the **membership oracle** answers a query $X$ with $1$ if $X$ satisfies every clause of $\Phi$ and $0$ otherwise. When $\Omega(\Phi)\neq\emptyset$, the **sample law** $\mu_\Phi$ is the uniform distribution on the solution set $\Omega(\Phi)$, written as a probability mass function: mass $1/|\Omega(\Phi)|$ on each solution.
--
--   These two objects are what a learner is run against in every probabilistic statement of the mission.
--
--   **Formalization Note** The mass function agrees pointwise with the published `solutionLaw Φ h` (a sanity check proves this).
-- source:
--   Feng, Yu, Zhang, Learning CNF Formulas with Uniform Random Solutions and Membership Queries, STOC 2027 submission (manuscript sha256 519ee6d4…), Definition 1.1, p.3; §3, p.13

import Mathlib
import Definitions.Def_CNFLearning873_Valiant_SolutionLaw
import Definitions.Def_CNFLearnMQ_cores

set_option autoImplicit false

namespace CNFLearnMQ

open CNFLearning873.Valiant

variable {n : ℕ}

/-- Membership-query access to `Φ` (Feng, Yu, Zhang, STOC 2027 submission (manuscript sha256
519ee6d4…), Definition 1.1, p.3): the query on `X` returns `true` iff `X` satisfies `Φ`. -/
noncomputable def memOracle (Φ : CNF n) (X : Assignment n) : Bool := by
  classical
  exact decide (SatAll Φ X)

/-- Sample access to `µ_Φ`, the uniform distribution on the solutions of `Φ` (§3, p.13), as a
probability mass function. It agrees pointwise with the published `solutionLaw Φ h`
(`RandomQueryXOR.uniformOn`): both put mass `1/|Ω(Φ)|` on each solution. -/
noncomputable def solutionPMF (Φ : CNF n) (h : (solutions Φ).Nonempty) : PMF (Assignment n) :=
  PMF.uniformOfFinset (solutions Φ) h

end CNFLearnMQ


