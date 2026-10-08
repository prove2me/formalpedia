-- Prove2me | Definitions.Def_KellyReversibility_Networks_QuasiReversible
-- name    : KellyReversibility_Networks_QuasiReversible
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T02:24:26.724307+00:00
-- url     : https://prove2.me/theorems/03a98b23-f67e-4af8-af2a-f44c198dd51b
-- title:
--   Quasi-reversible queue: rate characterization (3.8), (3.10)
-- statement:
--   Consider a queue whose state $x$ is a Markov process with transition rates $q(x,x')$ and equilibrium distribution $\pi$, and in which $N(x,c)$ is the number of customers of class $c$ in state $x$. Let $\mathcal S(c,x)$ be the set of states containing one more customer of class $c$ than $x$ and the same numbers of customers of every other class, so that a transition from $x$ to $x'\in\mathcal S(c,x)$ is the arrival of a class-$c$ customer. Let
--   $$q'(x,x')=\frac{\pi(x')\,q(x',x)}{\pi(x)}$$
--   be the transition rates of the reversed queue (3.9).
--
--   The queue is **quasi-reversible** when there are numbers $\alpha(c)$ such that, for every class $c$ and every state $x$,
--   $$\sum_{x'\in\mathcal S(c,x)}q(x,x')=\alpha(c)\quad(3.8),\qquad \sum_{x'\in\mathcal S(c,x)}q'(x,x')=\alpha(c)\quad(3.10).$$
--   That is, the class-$c$ arrival rate of the queue and of the reversed queue are the same and do not depend on the state.
--
--   Kelly defines quasi-reversibility (p. 65) by the property that the state at time $t_0$ is independent of the arrival times of each class after $t_0$ and of the departure times before $t_0$; he notes on p. 67 that relations (3.8) and (3.10) characterize this property for a stationary Markov process. This definition takes the characterization as the definition.
--
--   **Formalization Note** The state space $X$ and the class set are arbitrary types, and both sums are stated with `HasSum`, so they are required to converge to $\alpha(c)$. The reversed rates are the published `KellyStochasticNetworks.reversedRates`.
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, pp. 65–67, §3.2, Definition (p. 65) and Eqs. (3.8)–(3.10)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance

namespace KellyReversibility.Networks

/-- `𝒮(c, x)`: the states with one more customer of class `c` than state `x` and the same
numbers of customers of every other class (p. 66). `N x c` is the number of class-`c` customers
in state `x`. -/
def arrivalSet {X 𝒞 : Type*} (N : X → 𝒞 → ℕ) (c : 𝒞) (x : X) : Set X :=
  {x' | N x' c = N x c + 1 ∧ ∀ c', c' ≠ c → N x' c' = N x c'}

/-- **Quasi-reversibility, rate characterization** (relations (3.8) and (3.10), p. 67). For a
queue with transition rates `q`, equilibrium distribution `π` and class counts `N`, there are
rates `α(c)` such that for every class `c` and every state `x` both the class-`c` arrival rate
`∑_{x' ∈ 𝒮(c,x)} q(x, x')` of the queue and the class-`c` arrival rate
`∑_{x' ∈ 𝒮(c,x)} q'(x, x')` of the reversed queue, `q'(x, x') = π(x') q(x', x) / π(x)`, equal
`α(c)`, independently of `x`. -/
def QuasiReversible {X 𝒞 : Type*} (q : X → X → ℝ) (π : X → ℝ) (N : X → 𝒞 → ℕ) : Prop :=
  ∃ α : 𝒞 → ℝ, ∀ (c : 𝒞) (x : X),
    HasSum (fun x' : arrivalSet N c x => q x x') (α c) ∧
    HasSum (fun x' : arrivalSet N c x => KellyStochasticNetworks.reversedRates π q x x') (α c)

end KellyReversibility.Networks


