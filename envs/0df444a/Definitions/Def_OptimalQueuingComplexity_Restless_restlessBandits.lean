-- Prove2me | Definitions.Def_OptimalQueuingComplexity_Restless_restlessBandits
-- name    : OptimalQueuingComplexity_Restless_restlessBandits
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T12:11:24.833988+00:00
-- url     : https://prove2.me/theorems/65e1f441-8cc2-4d4e-9482-a08c88b6a570
-- title:
--   Decision version of RESTLESS BANDITS with deterministic transition rules
-- statement:
--   For an instance of RESTLESS BANDITS with deterministic transition rules (bandits $1,\dots,n$, state space $S$, rules $P, Q$, costs $c, d$, initial states and threshold $K$), the decision problem asks whether $n \ge 1$ and
--   $$\exists\, \pi : S^n \to \{1, \dots, n\} \quad\text{such that}\quad J(\pi) = \limsup_{T\to\infty} \frac{1}{T}\sum_{t=1}^{T} C(t) \;\le\; K .$$
--
--   The paper states the optimization problem, "finding a policy with minimal average expected cost"; this is its decision version, with the threshold part of the input. The paper's reduction produces instances with nonnegative costs in which the question is whether the average cost can be made zero, which is the case $K = 0$.
--
--   **Formalization Note.** The decision version is a convention of this formalization, not a definition printed in the paper. The non-strict inequality $\le K$ is used: with $K = 0$ and nonnegative costs a strict inequality would never hold.
-- source:
--   Papadimitriou & Tsitsiklis, The Complexity of Optimal Queuing Network Control, Math. Oper. Res. 24(2) (1999), p. 303, Section 3 ("We are interested in finding a policy with minimal average expected cost"); decision version of this mission, matching p. 304 ("the average cost is zero if and only if the computation halts")

import Mathlib
import Definitions.Def_OptimalQueuingComplexity_Restless_Instance

namespace OptimalQueuingComplexity.Restless

/-- **RESTLESS BANDITS (deterministic transition rules), decision version.** The paper
(p. 303) poses the optimization problem "finding a policy with minimal average expected cost";
its decision version asks, for an instance with at least one bandit, whether some policy has
average cost at most the instance's threshold `K`:
`∃ π : S^n → {1, …, n}, limsup_{T→∞} (1/T) ∑_{t=1}^{T} C(t) ≤ K`. -/
def restlessBandits (I : Instance) : Prop :=
  0 < I.n ∧ ∃ π : Policy I, I.avgCost π ≤ I.K

end OptimalQueuingComplexity.Restless


