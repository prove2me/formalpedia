-- Prove2me | Definitions.Def_FoundationsRL_Contextual_OracleGuarantee
-- name    : FoundationsRL_Contextual_OracleGuarantee
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-18T04:58:58.937313+00:00
-- url     : https://prove2.me/theorems/4f7bd980-afd2-419d-abf3-d1414fae54b9
-- title:
--   Definition 3 — Online regression oracle guarantee
-- statement:
--   This definition formalizes the guarantee an **online regression oracle** provides
--   (Definition 3, Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive
--   Decision Making*, p. 47), the abstraction used to plug supervised-learning methods into
--   contextual bandit algorithms.
--
--   Fix a context space $X$, $A$ actions, and a horizon $T$. Let $x : \{1,\dots,T\} \to X$ be a
--   context sequence, $f^\star : X \times \Pi \to \mathbb{R}$ the ground-truth reward function,
--   and suppose that at each round $t$ the oracle produces an estimate
--   $\hat f_t : X \times \Pi \to \mathbb{R}$ from the data
--   $(x_1,\pi_1,r_1),\dots,(x_{t-1},\pi_{t-1},r_{t-1})$, where $\pi_i \sim p_i$ is the
--   decision-maker's realized randomization at round $i$. The oracle's guarantee is that
--
--   $$
--   \sum_{t=1}^T \mathbb{E}_{\pi_t \sim p_t}\bigl[(\hat f_t(x_t,\pi_t) - f^\star(x_t,\pi_t))^2\bigr]
--   \le \mathrm{EstSq}(F, T, \delta)
--   $$
--
--   with probability at least $1-\delta$, where $\mathrm{EstSq}(F,T,\delta)$ is a bound depending
--   on the model class $F \ni f^\star$, the horizon, and the failure probability (e.g.
--   $\log(|F|/\delta)$ for the exponential weights method applied to a finite class $F$).
--   `OracleGuarantee` records exactly the displayed sum-of-expected-squared-errors bound, for a
--   fixed realized run.
--
--   This guarantee is what lets contextual bandit algorithms such as $\varepsilon$-Greedy and
--   SquareCB convert any online (square-loss) regression method into a decision-making procedure
--   with a regret bound that depends on the statistical complexity of $F$ rather than on the size
--   of the context space.
--
--   **Formalization Note** The source states the guarantee as an event of probability at least
--   $1-\delta$ over the randomness that produces $\hat f_t$ and the realized decisions; since
--   every downstream proposition in this mission (Propositions 8-10) derives its own
--   probability-$1-\delta$ conclusion purely algebraically from this one event, `OracleGuarantee`
--   packages the event itself as an explicit hypothesis on a fixed realized run, rather than as a
--   statement quantified over an underlying probability space of histories.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, p. 47, Definition 3

import Mathlib

namespace FoundationsRL.Contextual

/-- The guarantee provided by an online regression oracle (Foster & Rakhlin, *Foundations of
Reinforcement Learning and Interactive Decision Making*, arXiv:2312.16730v1, Definition 3,
p. 47). Given a context sequence `x : Fin T → X`, the ground-truth reward function `fstar`,
a sequence of oracle estimates `fhat : Fin T → X → Fin A → ℝ`, and the decision-maker's
realized randomization `p : Fin T → Fin A → ℝ` at each round (`p t` a probability vector over
`Fin A`), `OracleGuarantee A T x fhat fstar p EstSq` packages the event

`∑_{t=1}^T E_{π_t ∼ p_t}[(fhat_t(x_t, π_t) - fstar(x_t, π_t))^2] ≤ EstSq(F, T, δ)`

that Definition 3 asserts holds with probability at least `1 - δ`. Every result in this
mission (Propositions 8-10) is a purely algebraic consequence of this bound once it holds, so
the probability-`1 - δ` event of the source is captured here as an explicit hypothesis on
the realized run, rather than as a statement quantified over the randomness that produces
`fhat` and `p`. -/
def OracleGuarantee {X : Type*} (A T : ℕ) (x : Fin T → X) (fhat : Fin T → X → Fin A → ℝ)
    (fstar : X → Fin A → ℝ) (p : Fin T → Fin A → ℝ) (EstSq : ℝ) : Prop :=
  ∑ t : Fin T, ∑ a : Fin A, p t a * (fhat t (x t) a - fstar (x t) a) ^ 2 ≤ EstSq

end FoundationsRL.Contextual


