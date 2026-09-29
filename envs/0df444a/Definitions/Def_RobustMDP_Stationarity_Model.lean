-- Prove2me | Definitions.Def_RobustMDP_Stationarity_Model
-- name    : RobustMDP_Stationarity_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T17:22:50.019403+00:00
-- url     : https://prove2.me/theorems/aff0faf1-27d3-47d1-982c-603016461d28
-- title:
--   Discounted infinite-horizon MDP with rectangular row uncertainty: policies of both players and the discounted costs $C_N$, $C_\infty$
-- statement:
--   Let $\mathcal X = \{0,\dots,n-1\}$ be a finite state space and $\mathcal A$ a finite, nonempty, state-independent action set. A **robust discounted MDP** is given by
--
--   1. a stage cost $c(i,a) \ge 0$ for every state $i$ and action $a$;
--   2. for every action $a$ and state $i$, a nonempty set $\mathcal P_i^a\subseteq\Delta_n$ of possible next-state distributions (rows), where $\Delta_n=\{p\in\mathbb R^n_+ : p^\top\mathbf 1=1\}$ is the probability simplex. No convexity or closedness is assumed.
--
--   **Rectangularity.** One stage of nature is a collection of transition matrices $(P^a)_{a\in\mathcal A}\in\mathcal Q=\bigotimes_a\mathcal P^a$, $\mathcal P^a=\mathcal P_1^a\times\dots\times\mathcal P_n^a$: the $i$-th row of $P^a$ is chosen from $\mathcal P_i^a$ independently of all other rows and actions.
--
--   **Policies.** A controller policy $\pi=(\mathbf a_0,\mathbf a_1,\dots)\in\Pi$ is a sequence of maps $\mathbf a_t:\mathcal X\to\mathcal A$ (deterministic, Markov); it is *stationary* ($\pi\in\Pi_s$) when all $\mathbf a_t$ coincide. A nature policy $\tau=(P_t^a)\in\mathcal T$ is a sequence of stage choices in $\mathcal Q$; it is *stationary* ($\tau\in\mathcal T_s$) when all stages coincide.
--
--   **Costs.** For a discount factor $\nu$ and initial state $i_0$, let $\mu_0=e_{i_0}$ and $\mu_{t+1}(j)=\sum_i\mu_t(i)\,P_t^{\mathbf a_t(i)}(i,j)$ be the law of the state at time $t$. The discounted finite-horizon cost (terminal cost zero) and its infinite-horizon limit are
--   $$
--   C_N(\pi,\tau)=\sum_{t=0}^{N-1}\nu^t\sum_{i}\mu_t(i)\,c(i,\mathbf a_t(i)),\qquad C_\infty(\pi,\tau)=\sum_{t=0}^{\infty}\nu^t\sum_{i}\mu_t(i)\,c(i,\mathbf a_t(i)).
--   $$
--   Finally $c_{\max}=\max_{i,a}c(i,a)$ and $\varepsilon_N=\nu^N c_{\max}/(1-\nu)$.
--
--   These are the objects compared in Theorem 4: every combination of stationary or time-varying controller and nature.
--
--   **Formalization Note** States are `Fin n`; a stationary controller policy is a map `Fin n → A` embedded in $\Pi$ as the constant sequence, and a stationary nature policy is a constant sequence of choices. $C_N$ reads only the first $N$ stages of $\pi,\tau$, so on sequences it is exactly the paper's finite-horizon cost (2) with $c_t=\nu^t c$ and $c_N=0$. $C_\infty$ is a `tsum` of the nonnegative stage costs; for $0\le\nu<1$ these are bounded by $\nu^t c_{\max}$, so the series converges and its sum is $\lim_N C_N$. The nonemptiness of each $\mathcal P_i^a$ is implicit in the paper and explicit here.
-- source:
--   Nilim and El Ghaoui, Robust Control of Markov Decision Processes with Uncertain Transition Matrices, Oper. Res. 53 (2005), pp. 780–782 (§2.1–2.2: Δ_n, Eq. (2), rectangular uncertainty, 𝒯, 𝒯_s, Π_s), p. 785 (§4: discounted cost), p. 786 (c_max and ε_N in the proof of Theorem 4)

import Mathlib

namespace RobustMDP.Stationarity

/-- An infinite-horizon Markov decision process with rectangular uncertainty on its transition
rows and a discounted cost (Nilim–El Ghaoui 2005, §2.1–2.2, §3 and §4, pp. 781–782, 785).
States are `Fin n`, and `A` is the (state-independent) action set.

* `cost i a` is the constant stage cost `c(i, a)`, nonnegative and finite; the cost at stage `t`
  is `c_t(i, a) = ν^t c(i, a)` and the terminal cost is zero (§4);
* `rows a i` is the set `𝒫_i^a ⊆ Δ_n` of possible next-state distributions from state `i` under
  action `a`. Rectangularity (`𝒫^a = 𝒫_1^a × ⋯ × 𝒫_n^a`) is built in: nature chooses each row
  independently from its own set. Only inclusion in the simplex is assumed (no convexity, no
  closedness); nonemptiness is implicit in the paper and made explicit here. -/
structure Model (n : ℕ) (A : Type) where
  cost : Fin n → A → ℝ
  rows : A → Fin n → Set (Fin n → ℝ)
  cost_nonneg : ∀ i a, 0 ≤ cost i a
  rows_subset_simplex : ∀ a i, rows a i ⊆ stdSimplex ℝ (Fin n)
  rows_nonempty : ∀ a i, (rows a i).Nonempty

/-- One stage of nature: a collection of transition matrices `(P^a)_{a ∈ 𝒜} ∈ 𝒬 = ⊗_a 𝒫^a`
(p. 782). `P a i j` is the probability of moving from `i` to `j` under action `a`; the `i`-th row
`P a i` lies in `𝒫_i^a`. -/
abbrev Model.Choice {n : ℕ} {A : Type} (M : Model n A) :=
  {P : A → Fin n → Fin n → ℝ // ∀ a i, P a i ∈ M.rows a i}

/-- A (deterministic, Markov, time-varying) controller policy `π = (𝐚_0, 𝐚_1, …)`,
`𝐚_t : 𝒳 → 𝒜`: an element of `Π` (p. 781). A stationary policy (an element of `Π_s`) is a single
`𝐚 : Fin n → A`, embedded in `Π` as the constant sequence `fun _ => 𝐚`. -/
abbrev Policy (n : ℕ) (A : Type) := ℕ → Fin n → A

/-- A (time-varying) policy of nature `τ = (P_t^a)_{a ∈ 𝒜, t ∈ ℕ} ∈ 𝒯` (p. 781): one choice in
`𝒬` per stage, made independently across stages. A stationary policy of nature (an element of
`𝒯_s`) is a constant sequence `fun _ => P`. -/
abbrev Model.NaturePolicy {n : ℕ} {A : Type} (M : Model n A) := ℕ → M.Choice

/-- The distribution of the state `i_t` at time `t` under controller policy `π` and nature
policy `τ`, from the initial state `i₀`: `μ_0 = e_{i₀}` and
`μ_{t+1}(j) = ∑_i μ_t(i) P_t^{𝐚_t(i)}(i, j)`. -/
noncomputable def Model.stateDist {n : ℕ} {A : Type} (M : Model n A) (i₀ : Fin n)
    (π : Policy n A) (τ : M.NaturePolicy) : ℕ → Fin n → ℝ
  | 0 => fun j => if j = i₀ then 1 else 0
  | t + 1 => fun j => ∑ i, M.stateDist i₀ π τ t i * (τ t).1 (π t i) i j

/-- The expected discounted cost incurred at stage `t`:
`𝐄[ν^t c(i_t, 𝐚_t(i_t))] = ν^t ∑_i μ_t(i) c(i, 𝐚_t(i))`. -/
noncomputable def Model.stageCost {n : ℕ} {A : Type} (M : Model n A) (ν : ℝ) (i₀ : Fin n)
    (π : Policy n A) (τ : M.NaturePolicy) (t : ℕ) : ℝ :=
  ν ^ t * ∑ i, M.stateDist i₀ π τ t i * M.cost i (π t i)

/-- The finite-horizon expected total cost (2) with the discounted cost function (p. 781):
`C_N(π, τ) = 𝐄(∑_{t=0}^{N-1} ν^t c(i_t, 𝐚_t(i_t)))`, terminal cost zero. It depends only on the
first `N` components of `π` and `τ`. -/
noncomputable def Model.finiteCost {n : ℕ} {A : Type} (M : Model n A) (ν : ℝ) (i₀ : Fin n)
    (N : ℕ) (π : Policy n A) (τ : M.NaturePolicy) : ℝ :=
  ∑ t ∈ Finset.range N, M.stageCost ν i₀ π τ t

/-- The infinite-horizon discounted cost `C_∞(π, τ)`, the limit of `C_N(π, τ)` as `N → ∞`
(p. 781), written as the sum `∑_{t ≥ 0}` of the nonnegative stage costs. For `0 ≤ ν < 1` the
stage costs are bounded by `ν^t c_max`, so the series is summable and the sum is that limit. -/
noncomputable def Model.infCost {n : ℕ} {A : Type} (M : Model n A) (ν : ℝ) (i₀ : Fin n)
    (π : Policy n A) (τ : M.NaturePolicy) : ℝ :=
  ∑' t, M.stageCost ν i₀ π τ t

/-- `c_max := max_{i ∈ 𝒳, a ∈ 𝒜} c(i, a)` (p. 786). -/
noncomputable def Model.cmax {n : ℕ} {A : Type} (M : Model n A) : ℝ :=
  ⨆ i : Fin n, ⨆ a : A, M.cost i a

/-- `ε_N := ν^N c_max / (1 - ν)` (p. 786). -/
noncomputable def Model.epsN {n : ℕ} {A : Type} (M : Model n A) (ν : ℝ) (N : ℕ) : ℝ :=
  ν ^ N * M.cmax / (1 - ν)

end RobustMDP.Stationarity


