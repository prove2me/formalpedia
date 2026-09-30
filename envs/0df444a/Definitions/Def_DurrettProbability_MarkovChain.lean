-- Prove2me | Definitions.Def_DurrettProbability_MarkovChain
-- name    : DurrettProbability_MarkovChain
-- status  : Definition
-- author  : @naimengye
-- created : 2026-09-18T17:22:47.445974+00:00
-- url     : https://prove2.me/theorems/b90972d5-610c-46f2-b94c-2a4dcd6fa18f
-- title:
--   Countable-state Markov chains: n-step and first-passage probabilities, recurrence, irreducibility, aperiodicity, stationarity
-- statement:
--   The apparatus of chapter 5 of Durrett, *Probability: Theory and Examples*, for a Markov chain on a
--   countable state space $S$.
--
--   A **transition probability** is a function $p(x,y)\ge0$ whose rows are summable and sum to one. Its
--   **$n$-step** probabilities are the matrix powers: $p^0(x,y)=1$ if $x=y$ and $0$ otherwise, and
--   $$p^{n+1}(x,y)=\sum_z p(x,z)\,p^n(z,y).$$
--
--   The **first-passage probabilities** $f^n(x,y)=\mathbb{P}_x(T_y=n)$ record reaching $y$ for the
--   first time at step $n$:
--   $$f^1(x,y)=p(x,y),\qquad f^{n+1}(x,y)=\sum_{z\ne y}p(x,z)\,f^n(z,y),$$
--   the chain taking one step and then reaching $y$ for the first time without having visited it. From
--   them,
--   $$\rho_{xy}=\mathbb{P}_x(T_y<\infty)=\sum_{n\ge1}f^n(x,y),
--   \qquad \mathbb{E}_yT_y=\sum_{n\ge1}n\,f^n(y,y).$$
--
--   A state $y$ is **recurrent** when $\rho_{yy}=1$: the chain returns with probability one. The chain
--   is **irreducible** when $\rho_{xy}>0$ for every pair, so every state is reachable from every other.
--   A state $x$ is **aperiodic** when the greatest common divisor of $I_x=\{n\ge1:p^n(x,x)>0\}$ is $1$
--   — the chain can return to $x$ at times that are not confined to a proper lattice. A probability
--   vector $\pi$ is a **stationary distribution** when $\sum_x\pi(x)p(x,y)=\pi(y)$ for every $y$.
--
--   **Formalization Note** The chain's law on path space is deliberately not constructed. Every
--   quantity above is defined by an explicit recursion on the transition matrix, which is what the
--   book's own computations use and what these sections need; building the path measure is a separate
--   project, and the price of not building it is that path-level statements such as the almost-sure
--   limit of the visit counts cannot be expressed here.
--
--   Sums over the state space are unconditional sums, so the state space is not assumed finite. An
--   infinite mean return time appears as a non-summable series rather than as an extended real.
--   Aperiodicity is phrased as "the only natural number dividing every element of $I_x$ is $1$", which
--   is $\gcd I_x=1$ without needing a greatest common divisor of a set; it is false when $I_x$ is
--   empty, as it should be, since the period of such a state is undefined.
-- source:
--   Durrett, Probability: Theory and Examples, Version 5 (11 January 2019), chapter 5, pp. 281-312 (PDF pp. 289-320): the n-step transition probabilities and the first-passage decomposition section 5.3, rho_{xy} and recurrence p. 282, irreducibility p. 282, stationary measures section 5.5, and the period d_x = gcd{n >= 1 : p^n(x,x) > 0} p. 312. sha256 aeac36cbf5e44c53d69fa60a2d29a393e2d0e8c955ee103bd845d925fd910886

import Mathlib

open Filter

namespace DurrettProbability

variable {S : Type*}

/-- The `n`-step transition probabilities `pⁿ(x,y)` of a transition probability `p` on a
countable state space, with `p⁰(x,y) = 1` if `x = y` and `0` otherwise.
Durrett, *Probability: Theory and Examples*, section 5.2. -/
noncomputable def stepProb [DecidableEq S] (p : S → S → ℝ) : ℕ → S → S → ℝ
  | 0, x, y => if x = y then 1 else 0
  | (n + 1), x, y => ∑' z, p x z * stepProb p n z y

/-- The first-passage probabilities `fⁿ(x,y) = P_x(T_y = n)`: `f¹(x,y) = p(x,y)` and
`fⁿ⁺¹(x,y) = ∑_{z ≠ y} p(x,z) fⁿ(z,y)`, the chain reaching `y` for the first time at step `n`. -/
noncomputable def firstPassage [DecidableEq S] (p : S → S → ℝ) : ℕ → S → S → ℝ
  | 0, _, _ => 0
  | 1, x, y => p x y
  | (n + 2), x, y => ∑' z, if z = y then 0 else p x z * firstPassage p (n + 1) z y

/-- `ρ_{xy} = P_x(T_y < ∞) = ∑_{n ≥ 1} fⁿ(x,y)`, the probability that the chain started at `x`
ever visits `y`. -/
noncomputable def hitProb [DecidableEq S] (p : S → S → ℝ) (x y : S) : ℝ :=
  ∑' n : ℕ, firstPassage p (n + 1) x y

/-- `E_y T_y = ∑_{n ≥ 1} n fⁿ(y,y)`, the expected return time to `y`. -/
noncomputable def meanReturnTime [DecidableEq S] (p : S → S → ℝ) (y : S) : ℝ :=
  ∑' n : ℕ, ((n : ℝ) + 1) * firstPassage p (n + 1) y y

/-- A state is **recurrent** when the chain returns to it with probability one, `ρ_{yy} = 1`. -/
def Recurrent [DecidableEq S] (p : S → S → ℝ) (y : S) : Prop := hitProb p y y = 1

/-- The chain is **irreducible** when every state can be reached from every other,
`ρ_{xy} > 0` for all `x, y`. -/
def Irreducible [DecidableEq S] (p : S → S → ℝ) : Prop := ∀ x y, 0 < hitProb p x y

/-- A state `x` is **aperiodic** when the greatest common divisor of
`I_x = {n ≥ 1 : pⁿ(x,x) > 0}` is `1`: the only natural number dividing every element of `I_x`
is `1`.  (For `I_x` empty this fails, as it should: the period of such a state is undefined.) -/
def Aperiodic [DecidableEq S] (p : S → S → ℝ) (x : S) : Prop :=
  ∀ d : ℕ, (∀ n : ℕ, 1 ≤ n → 0 < stepProb p n x x → d ∣ n) → d = 1

/-- `π` is a **stationary distribution** for `p`: a probability vector fixed by `p`. -/
def StationaryDist (p : S → S → ℝ) (π : S → ℝ) : Prop :=
  (∀ x, 0 ≤ π x) ∧ (∑' x, π x) = 1 ∧ ∀ y, (∑' x, π x * p x y) = π y

/-- The standing hypotheses on a transition probability: non-negative entries and rows that are
summable and sum to one. -/
def IsTransition (p : S → S → ℝ) : Prop :=
  (∀ x y, 0 ≤ p x y) ∧ (∀ x, Summable (p x)) ∧ ∀ x, (∑' y, p x y) = 1

end DurrettProbability


