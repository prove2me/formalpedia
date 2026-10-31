-- Prove2me | Definitions.Def_DiffCtrlRobust_IsDiscOptimal
-- name    : DiffCtrlRobust_IsDiscOptimal
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:50:20.780001+00:00
-- url     : https://prove2.me/theorems/c876faa7-a091-4396-9a0b-8da144fc36bb
-- title:
--   $\alpha$-discounted optimality of a stationary Markov control
-- statement:
--   A control $v\in\mathfrak U_{\mathsf{sm}}$ is $\alpha$-discounted optimal for the model $(b,\sigma,c)$ if for all $x\in\mathbb R^d$
--
--   $$
--   \mathcal J^{v}_\alpha(x,c)=\inf_{U\in\mathfrak U}\mathcal J^U_\alpha(x,c)=V_\alpha(x).
--   $$
--
--   The infimum runs over all admissible controls, not only over Markov ones.
--
--   **Formalization Note** The definition also requires that a solution under $v$ exists from every $x$, which rules out vacuous optimality. Under (A1)–(A3) a solution always exists and is unique.
-- source:
--   Pradhan & Yüksel, arXiv:2205.05894v2, §2.1, pp.6–7, (2.3)

import Definitions.Def_DiffCtrlRobust_SolvesMarkov
import Definitions.Def_DiffCtrlRobust_markovCost
import Definitions.Def_DiffCtrlRobust_value

open MeasureTheory ProbabilityTheory Filter EthierKurtz
open scoped ENNReal NNReal Topology BigOperators

namespace DiffCtrlRobust

/-- The stationary Markov control `v` is `α`-discounted optimal for the model `(b, σ, c)`
(arXiv:2205.05894v2, (2.3), pp.6–7): for all `x`, its cost equals the optimal value `V_α(x)`, which
is an infimum over all admissible controls.

**Formalization Note.** The clause that a solution exists from every `x` rules out a control
that is optimal vacuously. Under (A1)–(A3) it always holds, and the solution is unique, so the
cost of `v` from `x` is well defined. -/
def IsDiscOptimal {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {U : Type*} [MeasurableSpace U]
    (P : Measure Ω) (W : ℝ≥0 → Ω → SDEState d) (α : ℝ) (b : SDEState d → U → SDEState d)
    (σ : SDEState d → SDEDiffusion d) (c : SDEState d → U → ℝ) (v : Usm d U) : Prop :=
  ∀ x, (∃ X, SolvesMarkov P W b σ v x X) ∧
    ∀ X, SolvesMarkov P W b σ v x X → markovCost P α c v X = value P W α b σ c x

end DiffCtrlRobust


