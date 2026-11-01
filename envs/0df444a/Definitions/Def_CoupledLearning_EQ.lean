-- Prove2me | Definitions.Def_CoupledLearning_EQ
-- name    : CoupledLearning_EQ
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:38:48.232996+00:00
-- url     : https://prove2.me/theorems/fb5dc996-4033-4b26-8ae5-42d818e485f0
-- title:
--   Equilibrium set $EQ(\theta)$ of the game $G(\theta)$
-- statement:
--   For a belief $\theta$, $EQ(\theta)$ is the set of equilibria of $G(\theta)$: the feasible profiles $q\in Q$ such that for every player $i$ and every $x\in Q_i$,
--
--   $$\sum_{s\in S}\theta(s)\,u_i^s(x,q_{-i})\le\sum_{s\in S}\theta(s)\,u_i^s(q).$$
--
--   Equivalently each $q_i$ is a best response $q_i\in BR_i(\theta,q_{-i})=\arg\max_{x\in Q_i}\sum_s\theta(s)u_i^s(x,q_{-i})$. Assumptions 2 and 3 and conclusion (2b) of Theorem 1 are about this set.
--
--   **Formalization Note** These are pure Nash equilibria with deviations restricted to $Q_i$; the deviation $(x,q_{-i})$ is `Function.update q i x`.
-- source:
--   Wu, Amin, Ozdaglar, Convergence and Stability of Coupled Belief–Strategy Learning Dynamics in Continuous Games, arXiv:2206.05637v2, §2, p.8; p.9 (best response); p.12 (EQ(θ))

import Mathlib
import Definitions.Def_CoupledLearning_Prof
import Definitions.Def_CoupledLearning_expectedUtility

namespace CoupledLearning

/-- `EQ(θ)`, the set of equilibria of the game `G(θ)` (arXiv:2206.05637v2, p.8, p.9 and p.12):
the feasible profiles `q ∈ Q` at which no player `i` can raise the expected utility
`∑_s θ(s) u_i^s(·, q_{-i})` by switching to another strategy `x ∈ Q_i`.

**Formalization Note.** These are the pure Nash equilibria of `G(θ)` with deviations restricted to
`Q_i`, i.e. the profiles where each `q_i` lies in the best response `BR_i(θ, q_{-i})` of p.9. The
deviation `(x, q_{-i})` is `Function.update q i x`. -/
def EQ {I S : Type*} [Fintype S] [DecidableEq I] {d : I → ℕ}
    (Q : (i : I) → Set (EuclideanSpace ℝ (Fin (d i)))) (u : S → I → Prof d → ℝ) (θ : S → ℝ) :
    Set (Prof d) :=
  {q | q ∈ Qset Q ∧ ∀ i, ∀ x ∈ Q i,
      expectedUtility u θ i (Function.update q i x) ≤ expectedUtility u θ i q}

end CoupledLearning


