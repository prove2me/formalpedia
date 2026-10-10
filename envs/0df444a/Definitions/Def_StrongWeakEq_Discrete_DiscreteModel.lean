-- Prove2me | Definitions.Def_StrongWeakEq_Discrete_DiscreteModel
-- name    : StrongWeakEq_Discrete_DiscreteModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T22:37:56.00009+00:00
-- url     : https://prove2.me/theorems/67917125-47fd-4912-a491-35ec927403c1
-- title:
--   §5, pp. 15–16, (5.1)–(5.5), Definition 5.1 — simplex, admissible transition matrices, standing assumptions, V, H, V(i, u ⊗₁ u*), equilibrium
-- statement:
--   Let $S=\{1,\dots,N\}$ be a finite state space. A discrete-time, time-homogeneous Markov chain $X=(X_t)_{t=0,1,\dots}$ on $S$ is controlled through its transition matrix $u=(u_{ij})$, whose $i$-th row $u_i$ is the law of the next state when the chain is at $i$.
--
--   1. The **probability simplex** is
--   $$\mathfrak P=\Big\{\alpha\in\mathbb R^N_+:\ \sum_{i=1}^N\alpha_i=1\Big\}. \qquad (5.1)$$
--   2. For each state $i$ an admissible set $\mathcal A_i\subseteq\mathfrak P$ of transition rows is given, and the **admissible controls** are $\mathcal A=\{u\in\mathbb R^{N\times N}: u_i\in\mathcal A_i\ \forall i\in S\}$.
--   3. A **payoff** $\kappa:\bar{\mathbb N}\times S\times\mathfrak P\to\mathbb R$, $\bar{\mathbb N}=\{0,1,2,\dots\}$, gives $\kappa(t,i,\alpha)$, the payoff at time $t$ when $X_t=i$ and the row in force is $\alpha$. The **standing assumptions** of §5 are: $\mathcal A_i\subseteq\mathfrak P$, $\kappa(t,i,\cdot)$ is continuous on $\mathfrak P$, and
--   $$\sum_{t=0}^\infty\ \sup_{(i,\alpha)\in S\times\mathfrak P}|\kappa(t,i,\alpha)|<\infty. \qquad (5.2)$$
--   4. The **expected payoff** of $u$ from state $i$ is
--   $$V(i,u)=\mathbb E_{i,u}\Big[\sum_{t=0}^\infty\kappa(t,X_t,u_{X_t})\Big]=\sum_{t=0}^\infty\sum_{j=1}^N (u^t)_{ij}\,\kappa(t,j,u_j), \qquad (5.3)$$
--   and the **shifted payoff** is $H_i(u)=\mathbb E_{i,u}\big[\sum_{t\ge0}\kappa(t+1,X_t,u_{X_t})\big]=\sum_{t}\sum_j (u^t)_{ij}\kappa(t+1,j,u_j)$ (5.5).
--   5. For $u,u^*\in\mathcal A$, the **concatenation** $u\otimes_1u^*$ lets $u$ govern the step at time $0$ and $u^*$ every later step. Its value from $i$ is
--   $$V(i,u\otimes_1u^*)=\kappa(0,i,u_i)+\sum_{t=0}^\infty\sum_{j=1}^N (u\,(u^*)^t)_{ij}\,\kappa(t+1,j,u^*_j),$$
--   since $X_{t+1}$ has law the $i$-th row of $u(u^*)^t$.
--   6. $u^*\in\mathcal A$ is an **equilibrium** (Definition 5.1) if $V(i,u^*)\ge V(i,u\otimes_1u^*)$ for all $(i,u)\in S\times\mathcal A$.
--
--   These objects are the discrete-time counterpart of the continuous-time model of §2: an equilibrium is a transition matrix from which no one-step deviation at time $0$, followed by a return to $u^*$, is profitable.
--
--   **Formalization Note** States $1,\dots,N$ are `Fin N` (state $k$ is index $k-1$). Rows are `Fin N → ℝ`, controls `Matrix (Fin N) (Fin N) ℝ`. Expectations are written through the one-dimensional marginals of the chain, $\mathbb P_{i,u}(X_t=j)=(u^t)_{ij}$, after exchanging expectation and sum (Fubini, justified by (5.2)); no Markov process is constructed. The infinite sums are `tsum`s; under (5.2) and $u\in\mathcal A$ they converge absolutely. Continuity of $\kappa$ on $\bar{\mathbb N}\times S\times\mathfrak P$ is continuity of each $\kappa(t,i,\cdot)$ on $\mathfrak P$, as $\bar{\mathbb N}$ and $S$ are discrete. (5.2) is encoded as a summable majorant $b_t\ge\sup|\kappa(t,\cdot,\cdot)|$. $\kappa$ is a function on all of $\mathbb R^N$ in the third argument; only its values on $\mathfrak P$ enter. $V(i,u\otimes_1u^*)$ is defined by the process (row $u$ at time $0$), not by formula (5.4), which is a separate milestone.
-- source:
--   Huang & Zhou, Strong and Weak Equilibria for Time-Inconsistent Stochastic Control in Continuous Time, arXiv:1809.09243v3, pp. 15–16, (5.1)–(5.3), (5.5), Definition 5.1

import Mathlib

namespace StrongWeakEq.Discrete

/-- (5.1), p. 15: the probability simplex `𝔓` of distributions on `S`. -/
def Simplex (N : ℕ) : Set (Fin N → ℝ) :=
  {α | (∀ j, 0 ≤ α j) ∧ ∑ j, α j = 1}

/-- p. 15: `𝒜 = {u ∈ ℝ^{N×N} : uᵢ ∈ 𝒜ᵢ ∀ i}`. -/
def DControls {N : ℕ} (A : Fin N → Set (Fin N → ℝ)) : Set (Matrix (Fin N) (Fin N) ℝ) :=
  {u | ∀ i, u i ∈ A i}

/-- The standing assumptions of §5 (p. 15): `𝒜ᵢ ⊆ 𝔓`; `κ` is continuous (`κ(t,i,·)` on `𝔓`; `ℕ` and `S`
are discrete); (5.2) `∑_t sup_{(i,α) ∈ S × 𝔓} |κ(t,i,α)| < ∞`, as a summable majorant. -/
structure DStanding {N : ℕ} (A : Fin N → Set (Fin N → ℝ))
    (κ : ℕ → Fin N → (Fin N → ℝ) → ℝ) : Prop where
  rows : ∀ i, A i ⊆ Simplex N
  cont : ∀ t i, ContinuousOn (κ t i) (Simplex N)
  summ : ∃ b : ℕ → ℝ, Summable b ∧ ∀ t i, ∀ α ∈ Simplex N, |κ t i α| ≤ b t

/-- (5.3), p. 15: `V(i,u) = E_{i,u}[∑_t κ(t, X_t, u_{X_t})] = ∑_t ∑_j (uᵗ)ᵢⱼ κ(t, j, uⱼ)`. -/
noncomputable def dValue {N : ℕ} (κ : ℕ → Fin N → (Fin N → ℝ) → ℝ)
    (u : Matrix (Fin N) (Fin N) ℝ) (i : Fin N) : ℝ :=
  ∑' t : ℕ, ∑ j, (u ^ t) i j * κ t j (u j)

/-- (5.5), p. 16: `Hᵢ(u) = E_{i,u}[∑_t κ(t+1, X_t, u_{X_t})]`. -/
noncomputable def dH {N : ℕ} (κ : ℕ → Fin N → (Fin N → ℝ) → ℝ)
    (u : Matrix (Fin N) (Fin N) ℝ) (i : Fin N) : ℝ :=
  ∑' t : ℕ, ∑ j, (u ^ t) i j * κ (t + 1) j (u j)

/-- p. 15: `V(i, u ⊗₁ u*)`, the value when `u` governs time `0` and `u*` every later time:
`κ(0,i,uᵢ) + ∑_{t≥0} ∑_j (u u*ᵗ)ᵢⱼ κ(t+1, j, u*ⱼ)`. -/
noncomputable def dConcatValue {N : ℕ} (κ : ℕ → Fin N → (Fin N → ℝ) → ℝ)
    (u us : Matrix (Fin N) (Fin N) ℝ) (i : Fin N) : ℝ :=
  κ 0 i (u i) + ∑' t : ℕ, ∑ j, (u * us ^ t) i j * κ (t + 1) j (us j)

/-- Definition 5.1, p. 15: `u* ∈ 𝒜` is an equilibrium if `V(i,u*) ≥ V(i, u ⊗₁ u*)` for all
`(i,u) ∈ S × 𝒜`. -/
def IsDEquilibrium {N : ℕ} (A : Fin N → Set (Fin N → ℝ))
    (κ : ℕ → Fin N → (Fin N → ℝ) → ℝ) (us : Matrix (Fin N) (Fin N) ℝ) : Prop :=
  us ∈ DControls A ∧ ∀ i, ∀ u ∈ DControls A, dConcatValue κ u us i ≤ dValue κ us i

end StrongWeakEq.Discrete


