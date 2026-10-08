-- Prove2me | Definitions.Def_KellyReversibility_Symmetric_Equilibrium
-- name    : KellyReversibility_Symmetric_Equilibrium
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T02:36:58.550073+00:00
-- url     : https://prove2.me/theorems/b07199b3-2b69-427f-90f2-413fb322284d
-- title:
--   Equilibrium distribution and the rate characterization (3.8), (3.10) of quasi-reversibility
-- statement:
--   Let $S$ be a state space and $q(x, y)$ transition rates on it.
--
--   1. **Equilibrium distribution** (§1.1, p. 3). A function $\pi$ on $S$ is the *equilibrium distribution* for $q$ when the numbers $\pi(x)$ are positive, sum to unity, and satisfy the equilibrium equations (1.3)
--   $$\pi(x)\sum_{y \in S} q(x, y) = \sum_{y \in S} \pi(y)\, q(y, x) \qquad \text{for all } x \in S,$$
--   with both series convergent.
--
--   2. **One more customer of class $k$** (p. 66). Given counts $N_k(x)$ of the customers of each class $k$ in state $x$, $\mathcal S(k, x)$ is the set of states $x'$ with $N_k(x') = N_k(x) + 1$ and $N_{k'}(x') = N_{k'}(x)$ for all $k' \ne k$.
--
--   3. **Quasi-reversibility in rate form** (pp. 66–67). With the reversed rates $q'(x, x') = \pi(x') q(x', x) / \pi(x)$ of (3.9), the process satisfies (3.8) and (3.10) when there are numbers $\alpha(k)$ such that for every class $k$ and state $x$
--   $$\sum_{x' \in \mathcal S(k, x)} q(x, x') = \alpha(k), \qquad \sum_{x' \in \mathcal S(k, x)} q'(x, x') = \alpha(k),$$
--   both series converging. Kelly states (p. 67) that relations (3.8) and (3.10) characterize quasi-reversibility for a stationary Markov process: the arrival rate of class $k$ does not depend on the state, in the process and in its reversal.
--
--   **Formalization Note** Full balance and the reversed rates are the published `KellyStochasticNetworks.FullBalance` and `KellyStochasticNetworks.reversedRates`. Because Lean's `tsum` of a non-summable family is $0$, the convergence of each series is required explicitly. Quasi-reversibility is defined through its rate characterization; the book's definition (independence of the current state from future arrivals and past departures) is about the process and is not formalized here.
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, p. 3 (equilibrium distribution, Eq. (1.3)); pp. 65–67 (PDF pp. 68–70), definition of quasi-reversibility, 𝒮(c, x) and Eqs. (3.8)–(3.10)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance

namespace KellyReversibility.Symmetric

/-- `π` is the equilibrium distribution of the Markov process with transition rates `q`
(Kelly 1979, §1.1, p. 3): the numbers `π(x)` are positive, sum to unity, and satisfy the
equilibrium equations (1.3) `π(x) ∑_y q(x, y) = ∑_y π(y) q(y, x)` for every state `x`; both
sums are required to converge, since Lean's `tsum` of a non-summable family is `0`. -/
def IsEquilibriumDistribution {S : Type*} (π : S → ℝ) (q : S → S → ℝ) : Prop :=
  (∀ x, 0 < π x) ∧ HasSum π 1 ∧ (∀ x, Summable (q x)) ∧
    (∀ x, Summable (fun y => π y * q y x)) ∧ KellyStochasticNetworks.FullBalance π q

/-- `OneMoreOf count x' x k`: state `x'` contains one more customer of class `k` than state
`x`, and the same number of customers of every other class.  These `x'` form the set
`𝒮(k, x)` of Kelly 1979, p. 66, given the class counts `count : S → K → ℕ` read off a state. -/
def OneMoreOf {S K : Type*} (count : S → K → ℕ) (x' x : S) (k : K) : Prop :=
  count x' k = count x k + 1 ∧ ∀ k', k' ≠ k → count x' k' = count x k'

open Classical in
/-- The rate characterization (3.8) and (3.10) of quasi-reversibility (Kelly 1979, p. 67) for
a stationary Markov process with transition rates `q` and equilibrium distribution `π`, whose
classes of customers are counted by `count`: there are rates `α(k)` such that for every state
`x` and class `k`,
`∑_{x' ∈ 𝒮(k, x)} q(x, x') = α(k)` (3.8) and `∑_{x' ∈ 𝒮(k, x)} q'(x, x') = α(k)` (3.10),
where `q'(x, x') = π(x') q(x', x) / π(x)` are the rates (3.9) of the reversed process.  Both
sums converge (`HasSum`). -/
def QuasiReversibleRates {S K : Type*} (π : S → ℝ) (q : S → S → ℝ) (count : S → K → ℕ) :
    Prop :=
  ∃ α : K → ℝ, ∀ (k : K) (x : S),
    HasSum (fun x' => if OneMoreOf count x' x k then q x x' else 0) (α k) ∧
    HasSum (fun x' => if OneMoreOf count x' x k then
      KellyStochasticNetworks.reversedRates π q x x' else 0) (α k)

end KellyReversibility.Symmetric


