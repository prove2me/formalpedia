-- Prove2me | Definitions.Def_DermanSeqDecisions_Stationary_totalCost
-- name    : DermanSeqDecisions_Stationary_totalCost
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T09:43:37.226988+00:00
-- url     : https://prove2.me/theorems/fe35fd55-bf61-4520-b5a2-d6803e02b226
-- title:
--   Expected total cost $S_R(i) = \sum_{t \ge 0} W_t$, possibly infinite
-- statement:
--   Consider Derman's controlled system: a finite set of states (Derman's $0, \dots, L$), a finite set of decisions $d_1, \dots, d_K$, transition probabilities $q_{ij}(k)$ and nonnegative costs $w_{ik}$. A **procedure** $R$ (Derman's class $C$) chooses the decision at time $t$ at random, with probabilities that may depend on the whole history $X_0, \Delta_0, \dots, X_t$ of states and decisions. Started from $X_0 = i$ with probability one, it incurs at time $t$ the expected cost
--   $$W_t = E_R\big[w_{X_t \Delta_t} \mid X_0 = i\big].$$
--
--   The **expected total cost** of $R$ from $i$ is
--   $$S_R(i) = \sum_{t=0}^{\infty} W_t \in [0, \infty].$$
--
--   This is the criterion of Derman's Problem 2: when a state $L$ is absorbing and costs nothing, $S_R(i)$ is the expected total cost of taking the system from $i$ to $L$ under $R$. It may be infinite, for instance when $R$ never reaches $L$.
--
--   **Formalization Note** $W_t$ is `expCost θ i t` from the published model `SennottDP.AvgFinite.Model`, and the sum is taken in $[0, \infty]$, so a divergent sum is $\infty$ rather than a default value. $S_R(i)$ equals `discCost θ 1 i`; it is named separately because the paper treats it as its own criterion.
-- source:
--   Derman, On Sequential Decisions and Markov Chains, Management Science 9(1):16–24 (1962), DOI 10.1287/mnsc.9.1.16, p. 17, Problem 2 (definition of S_R(i))

import Mathlib
import Definitions.Def_SennottDP_AvgFinite_Model

open scoped ENNReal NNReal
open SennottDP.AvgFinite

namespace DermanSeqDecisions.Stationary

/-- Derman's expected total cost `S_R(i) = ∑_{t=0}^∞ W_t` of Problem 2
(Derman, *On Sequential Decisions and Markov Chains*, Management Science 9(1):16–24 (1962),
DOI 10.1287/mnsc.9.1.16, §1, p. 17, Problem 2): the sum over all times `t` of the expected cost
`W_t = E_θ[w(X_t, Δ_t) | X_0 = i]` incurred at time `t` by the procedure `θ` started in state `i`.

**Formalization Note.** `W_t` is `SennottDP.AvgFinite.expCost θ i t`. The sum is taken in
`[0, ∞]` (`ℝ≥0∞`), so that, as on p. 18, `S_R(i)` may be `∞`; it is never a real `tsum` with a
default value `0`. It coincides with `discCost θ 1 i`; it is given its own name because the paper
treats it as its own criterion. -/
noncomputable def totalCost {S : Type*} {Act : Type*} [Countable S] {M : MDC S Act}
    (θ : Policy M) (i : S) : ℝ≥0∞ :=
  ∑' t : ℕ, expCost θ i t

end DermanSeqDecisions.Stationary


