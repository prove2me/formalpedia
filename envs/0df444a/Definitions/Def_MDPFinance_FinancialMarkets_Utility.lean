-- Prove2me | Definitions.Def_MDPFinance_FinancialMarkets_Utility
-- name    : MDPFinance_FinancialMarkets_Utility
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:47:29.44584+00:00
-- url     : https://prove2.me/theorems/247d1a8d-cbc6-40fa-8670-cc7057dbf802
-- title:
--   Definition 3.4.1 / 3.4.3 — utility functions and the Arrow–Pratt coefficient
-- statement:
--   A **utility function** on $\mathrm{dom}\,U \subseteq \mathbb{R}$ is strictly increasing,
--   strictly concave and continuous. For a twice-differentiable utility function, the
--   **Arrow–Pratt absolute risk aversion coefficient** at $x$ is $\alpha_{AP}(x) := -U''(x)/U'(x)$.
--
--   **Formalization Note.** `StrictConcaveOn` already implies continuity on the interior of
--   `domU` when `domU` is open (the book notes this too), but `hcont` is kept as an independent
--   field to match the book's own definition literally (needed at boundary points, e.g.
--   $\mathrm{dom}\,U = [0,\infty)$, where the book separately requires right-continuity at $0$).
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 71-72, PDF 84-86, Definition 3.4.1 / Definition 3.4.3

import Mathlib

namespace MDPFinance.FinancialMarkets

/-- Definition 3.4.1 (Bäuerle–Rieder, p. 71, PDF 84). A function `U : domU → ℝ` is called a
utility function if `U` is strictly increasing, strictly concave and continuous on `domU`. -/
structure IsUtilityFunction (domU : Set ℝ) (U : ℝ → ℝ) : Prop where
  hmono : StrictMonoOn U domU
  hconcave : StrictConcaveOn ℝ domU U
  hcont : ContinuousOn U domU

/-- Definition 3.4.3 (Bäuerle–Rieder, p. 72, PDF 86). Let `U` be a twice differentiable utility
function. The Arrow–Pratt absolute risk aversion coefficient of `U` at level `x` is
`α_AP(x) := -U''(x) / U'(x)`. -/
noncomputable def arrowPrattCoefficient (U : ℝ → ℝ) (x : ℝ) : ℝ :=
  -(deriv (deriv U) x) / (deriv U x)

end MDPFinance.FinancialMarkets


