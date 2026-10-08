-- Prove2me | Definitions.Def_Dubey1986_Inefficiency_MultiMatrix
-- name    : Dubey1986_Inefficiency_MultiMatrix
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:32:03.563829+00:00
-- url     : https://prove2.me/theorems/4ea15c28-1c00-4df5-8063-c6709c16b962
-- title:
--   pp. 12–13 — multi-matrix games: $T$-efficiency, efficiency, strong equilibria of the mixed extension, pure strategies
-- statement:
--   The multi-matrix games of Nash (§4). Each player $i$ of a finite set has a finite set $K_i$ of pure strategies and mixed strategies $X_i=\{x\in\mathbb R^{K_i}: \sum_j x_j=1,\ x_j\ge 0\}$. A game is given by payoffs $a^i\in\mathbb R^K$, $K=K_1\times\dots\times K_n$, and player $i$'s payoff on mixed profiles is the expectation $\Pi_{a^i}(x)=\sum_{k\in K} x_k a^i_k$ with $x_k=x_{j(1)}\cdots x_{j(n)}$.
--
--   For a mixed profile $\sigma$, a set of players $T$ and mixed strategies $\tau$, $(\sigma|\tau)$ replaces $\sigma_i$ by $\tau_i$ for $i\in T$. The profile $\sigma$ is **$T$-efficient** if no choice of mixed strategies $\tau_i$, $i\in T$, gives $\Pi_{a^i}(\sigma|\tau)\ge\Pi_{a^i}(\sigma)$ for all $i\in T$ and $\Pi_{a^j}(\sigma|\tau)>\Pi_{a^j}(\sigma)$ for some $j\in T$; it is **efficient** if it is $N$-efficient, and a **strong Nash equilibrium** if it is $T$-efficient for every $T$. A mixed strategy is **pure** if it is a vertex of $X_i$: weight $1$ on one pure strategy and $0$ elsewhere.
--
--   **Formalization Note** Lotteries, mixed profiles, expected payoffs and mixed Nash equilibria are those of the published `agt_games` vocabulary (`AGT.IsLottery`, `AGT.IsMixedProfile`, `AGT.expectedPayoff`, `AGT.IsMixedNash`); this file adds only the efficiency notions and purity.
-- source:
--   Dubey, Inefficiency of Nash Equilibria, IIASA WP-83-74 (July 1983), pp. 12–13 (§4) with the definitions (1)–(4) of p. 2

import Mathlib
import Definitions.Def_agt_games

namespace Dubey1986.Inefficiency

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {S : ι → Type*} [∀ i, Fintype (S i)]

/-- `(σ|τ)` for mixed profiles: replace `σ i` by `τ i` for each `i ∈ T`. -/
def mixedUpdate (σ : ∀ i, S i → ℝ) (T : Finset ι) (τ : ∀ i, S i → ℝ) : ∀ i, S i → ℝ :=
  fun i => if i ∈ T then τ i else σ i

/-- The mixed profile `σ` is `T`-efficient in the mixed extension `Π_a` of the multi-matrix
game `a`: no lotteries `τ i` (`i ∈ T`) weakly raise every `Π_{a^i}`, `i ∈ T`, and strictly
raise some `Π_{a^j}`, `j ∈ T`. -/
def IsMixedTEfficient (a : ι → (∀ i, S i) → ℝ) (T : Finset ι) (σ : ∀ i, S i → ℝ) : Prop :=
  ¬ ∃ τ : ∀ i, S i → ℝ, (∀ i ∈ T, AGT.IsLottery (τ i)) ∧
      (∀ i ∈ T, AGT.expectedPayoff a σ i ≤ AGT.expectedPayoff a (mixedUpdate σ T τ) i) ∧
      ∃ j ∈ T, AGT.expectedPayoff a σ j < AGT.expectedPayoff a (mixedUpdate σ T τ) j

/-- `σ` is an efficient point of `Π_a`. -/
def IsMixedEfficient (a : ι → (∀ i, S i) → ℝ) (σ : ∀ i, S i → ℝ) : Prop :=
  AGT.IsMixedProfile σ ∧ IsMixedTEfficient a Finset.univ σ

/-- `σ` is a strong Nash equilibrium of `Π_a`. -/
def IsMixedStrong (a : ι → (∀ i, S i) → ℝ) (σ : ∀ i, S i → ℝ) : Prop :=
  AGT.IsMixedProfile σ ∧ ∀ T, IsMixedTEfficient a T σ

/-- The weight vector `p` is a pure strategy: the vertex of the probability simplex at some
`s` (weight `1` on `s`, `0` elsewhere). -/
def IsPure {α : Type*} (p : α → ℝ) : Prop :=
  ∃ s, p s = 1 ∧ ∀ t, t ≠ s → p t = 0

end Dubey1986.Inefficiency


