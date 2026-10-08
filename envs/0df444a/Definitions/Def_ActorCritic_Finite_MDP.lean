-- Prove2me | Definitions.Def_ActorCritic_Finite_MDP
-- name    : ActorCritic_Finite_MDP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T02:12:55.265231+00:00
-- url     : https://prove2.me/theorems/99c3cec7-20db-49ec-b4ca-4a7b603ea803
-- title:
--   §2 — finite cost MDP, parameterized randomized stationary policies, transition matrices P(θ), P_θ and finite Markov-chain notions
-- statement:
--   This module fixes the general objects of §2 of Konda and Tsitsiklis.
--
--   1. **Finite cost MDP.** Finite sets $\mathbb X$ (states) and $\mathbb U$ (actions), transition probabilities $p(y\mid x,u)\ge0$ with $\sum_{y}p(y\mid x,u)=1$ for every $(x,u)$, and a one-stage cost $c:\mathbb X\times\mathbb U\to\mathbb R$.
--   2. **Parameterized family of randomized stationary policies (RSPs).** For each $\theta\in\mathbb R^n$ and $x\in\mathbb X$, $\mu_\theta(\cdot\mid x)$ is a probability vector on $\mathbb U$: $\mu_\theta(u\mid x)\ge0$ and $\sum_u\mu_\theta(u\mid x)=1$.
--   3. **Transition matrices.** The state chain $\{X_k\}$ under the RSP $\theta$ has transition matrix
--   $$
--   P(\theta)_{xy}=\sum_{u}\mu_\theta(u\mid x)\,p(y\mid x,u),
--   $$
--   and the state–action chain $\{X_k,U_k\}$ has transition matrix $P_\theta\big((x,u),(y,\bar u)\big)=p(y\mid x,u)\,\mu_\theta(\bar u\mid y)$.
--   4. **Finite Markov-chain notions.** A square matrix $A$ indexed by a finite set is *irreducible* if for all $i,j$ some power has $(A^k)_{ij}>0$; it is *aperiodic* if for every $i$ the only natural number dividing every return time $k\ge1$ with $(A^k)_{ii}>0$ is $1$ (the gcd of the return times is $1$); a vector $q$ is *stationary* for $A$ if $q\ge0$, $\sum_iq_i=1$ and $qA=q$.
--
--   These are the data on which every statement of the mission is built.
--
--   **Formalization Note** The transition probability $p(y\mid x,u)$ is stored as `p x u y` (current state, action, next state). Parameters live in `EuclideanSpace ℝ (Fin n)`, so that $|\cdot|$ is the Euclidean norm and Mathlib's `gradient` is the paper's $\nabla$. Positivity of $\mu_\theta$ (Assumption 2.1(a)) is not part of the structure; it is a separate hypothesis.
-- source:
--   Konda and Tsitsiklis, On Actor-Critic Algorithms, SIAM J. Control Optim. 42 (2003), pp. 1144–1145, §2 and Assumption 2.1(c)–(d)

import Mathlib

namespace ActorCritic.Finite

/-- A Markov decision process with finite state space `X` and finite action space `U`
(Konda–Tsitsiklis 2003, §2, p. 1144). `p x u y` is the probability `p(y | x, u)` that the next
state is `y` when the current state is `x` and the current action is `u` (argument order:
current state, action, next state). `c x u` is the one-stage cost `c(x, u)`, an arbitrary real
number. -/
structure FiniteMDP (X U : Type) [Fintype X] [Fintype U] where
  /-- transition probabilities `p(y | x, u)`, written `p x u y` -/
  p : X → U → X → ℝ
  /-- one-stage cost `c(x, u)` -/
  c : X → U → ℝ
  p_nonneg : ∀ x u y, 0 ≤ p x u y
  p_sum_one : ∀ x u, ∑ y, p x u y = 1

/-- A family `{μ_θ ; θ ∈ ℝⁿ}` of randomized stationary policies (RSPs) on a finite action space
(§2, p. 1144): `μ θ x u` is the probability `μ_θ(u | x)` of taking action `u` in state `x` under
the policy with parameter `θ`. Each `μ θ x` is a probability vector on `U`. Positivity
(Assumption 2.1(a)) is *not* built in; it is a separate hypothesis. -/
structure RSPFamily (X U : Type) [Fintype U] (n : ℕ) where
  /-- the policy probabilities `μ_θ(u | x)` -/
  μ : EuclideanSpace ℝ (Fin n) → X → U → ℝ
  μ_nonneg : ∀ θ x u, 0 ≤ μ θ x u
  μ_sum_one : ∀ θ x, ∑ u, μ θ x u = 1

variable {X U : Type} [Fintype X] [Fintype U] {n : ℕ}

/-- The transition matrix `P(θ)` of the state chain `{X_k}` under the RSP `θ`:
`P(θ)_{xy} = ∑_u μ_θ(u | x) p(y | x, u)` (Assumption 2.1(d), p. 1145). -/
noncomputable def stateMatrix (M : FiniteMDP X U) (π : RSPFamily X U n)
    (θ : EuclideanSpace ℝ (Fin n)) : Matrix X X ℝ :=
  fun x y => ∑ u, π.μ θ x u * M.p x u y

/-- The transition matrix `P_θ` of the state–action chain `{X_k, U_k}` under the RSP `θ`:
`P_θ((x, u), (y, ū)) = p(y | x, u) μ_θ(ū | y)` (§2 and the operator `P_θ` of p. 1151 in the
finite case). -/
noncomputable def pairMatrix (M : FiniteMDP X U) (π : RSPFamily X U n)
    (θ : EuclideanSpace ℝ (Fin n)) : Matrix (X × U) (X × U) ℝ :=
  fun w w' => M.p w.1 w.2 w'.1 * π.μ θ w'.1 w'.2

/-- A square matrix `A` over a finite index set is *irreducible*: every entry of some power
of `A` is positive, i.e. every state leads to every state. -/
def IsIrreducible {S : Type} [Fintype S] [DecidableEq S] (A : Matrix S S ℝ) : Prop :=
  ∀ i j, ∃ k : ℕ, 0 < (A ^ k) i j

/-- A square matrix `A` over a finite index set is *aperiodic*: for every state `i`, the greatest
common divisor of the return times `{k ≥ 1 | (A^k)_{ii} > 0}` equals `1`, stated as "the only
natural number dividing every return time is `1`". (If `i` has no return time, every `d`
divides all of them and `i` is not aperiodic.) -/
def IsAperiodic {S : Type} [Fintype S] [DecidableEq S] (A : Matrix S S ℝ) : Prop :=
  ∀ i, ∀ d : ℕ, (∀ k : ℕ, 1 ≤ k → 0 < (A ^ k) i i → d ∣ k) → d = 1

/-- `q` is a stationary probability vector of the stochastic matrix `A`: `q ≥ 0`, `∑ q = 1`
and `q A = q`. -/
def IsStationary {S : Type} [Fintype S] (A : Matrix S S ℝ) (q : S → ℝ) : Prop :=
  (∀ i, 0 ≤ q i) ∧ ∑ i, q i = 1 ∧ Matrix.vecMul q A = q

end ActorCritic.Finite


