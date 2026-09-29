-- Prove2me | Definitions.Def_RobustMDP_FiniteHorizon_Model
-- name    : RobustMDP_FiniteHorizon_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T17:17:11.257954+00:00
-- url     : https://prove2.me/theorems/99aa5dc3-5aa0-49d9-b5b3-0492adb89be2
-- title:
--   Finite-horizon MDP with rectangular uncertainty on the transition rows, and the policies of controller and nature
-- statement:
--   A **finite-horizon robust MDP** consists of
--
--   1. a finite state space $\mathcal X=\{1,\dots,n\}$, a decision horizon $T=\{0,1,\dots,N-1\}$ and a finite nonempty action set $\mathcal A$ (the same in every state);
--   2. stage costs $c_t(i,a)\ge 0$ for $t\in T$, $i\in\mathcal X$, $a\in\mathcal A$, and a terminal cost $c_N(i)$ (no sign assumed);
--   3. for every action $a$ and state $i$, a nonempty set $\mathcal P_i^a\subseteq\Delta_n=\{p\in\mathbb R^n_+ : p^{\mathsf T}\mathbf 1=1\}$ of possible next-state distributions from $i$ under $a$. No convexity or closedness is assumed.
--
--   A **controller policy** $\pi=(\mathbf a_0,\dots,\mathbf a_{N-1})$ is a sequence of maps $\mathbf a_t:\mathcal X\to\mathcal A$ (deterministic, Markov); the strategy space is $\Pi=\mathcal A^{nN}$.
--
--   A **policy of nature** $\tau=(P_t^a)_{a\in\mathcal A,\,t\in T}$ is a collection of transition matrices whose $i$-th rows satisfy $p_i^a(t)\in\mathcal P_i^a$ for every $t$, $a$, $i$. The admissible set is
--
--   $$
--   \mathcal T=\Big(\bigotimes_{a\in\mathcal A}\mathcal P^a\Big)^N,\qquad \mathcal P^a=\mathcal P_1^a\times\cdots\times\mathcal P_n^a .
--   $$
--
--   The product form is the paper's **rectangular uncertainty property**: each row of each matrix at each stage is chosen independently from its own set, and nature may change its choice from stage to stage (time-varying uncertainty).
--
--   **Formalization Note** States are `Fin n`, stages `Fin N`. A policy of nature is the subtype of functions $\tau(t,a,i)\in\mathbb R^n$ with $\tau(t,a,i)\in\mathcal P_i^a$; rectangularity is built in by this product structure. Nonemptiness of each $\mathcal P_i^a$ is implicit in the paper (otherwise nature has no admissible policy) and is a field of the structure.
-- source:
--   Nilim and El Ghaoui, Robust Control of Markov Decision Processes with Uncertain Transition Matrices, Oper. Res. 53 (2005), pp. 781–782, §2.1–2.2 and §3 (standing assumption)

import Mathlib

namespace RobustMDP.FiniteHorizon

/-- A finite-horizon Markov decision process with rectangular uncertainty on its transition rows
(Nilim–El Ghaoui 2005, §2.1–2.2 and §3, pp. 781–782). States are `Fin n`, the decision horizon is
`T = {0, …, N-1}`, and `A` is the (state-independent) action set.

* `cost t i a` is the stage cost `c_t(i, a)`, nonnegative and finite;
* `terminalCost i` is the terminal cost `c_N(i)` (no sign assumed, as in the paper);
* `rows a i` is the set `𝒫_i^a ⊆ Δ_n` of possible next-state distributions from state `i` under
  action `a`. The rectangular uncertainty property `𝒫^a = 𝒫_1^a × ⋯ × 𝒫_n^a` is built in: nature
  chooses each row independently from its own set. Only inclusion in the simplex is assumed (no
  convexity, no closedness); nonemptiness is implicit in the paper and made explicit here. -/
structure Model (n N : ℕ) (A : Type) where
  cost : Fin N → Fin n → A → ℝ
  terminalCost : Fin n → ℝ
  rows : A → Fin n → Set (Fin n → ℝ)
  cost_nonneg : ∀ t i a, 0 ≤ cost t i a
  rows_subset_simplex : ∀ a i, rows a i ⊆ stdSimplex ℝ (Fin n)
  rows_nonempty : ∀ a i, (rows a i).Nonempty

/-- A (deterministic, Markov) controller policy `π = (𝐚_0, …, 𝐚_{N-1})`, `𝐚_t : 𝒳 → 𝒜`;
the strategy space `Π = 𝒜^{nN}` (p. 781). -/
abbrev ControlPolicy (n N : ℕ) (A : Type) := Fin N → Fin n → A

/-- An admissible policy of nature `τ = (P_t^a)_{a ∈ 𝒜, t ∈ T} ∈ 𝒯 = (⊗_a 𝒫^a)^N` (p. 781):
for every stage `t`, action `a` and state `i`, the `i`-th row `τ t a i` of the transition matrix
`P_t^a` lies in `𝒫_i^a`, chosen independently for each `(t, a, i)` (time-varying uncertainty). -/
abbrev Model.NaturePolicy {n N : ℕ} {A : Type} (M : Model n N A) :=
  {τ : Fin N → A → Fin n → Fin n → ℝ // ∀ t a i, τ t a i ∈ M.rows a i}

end RobustMDP.FiniteHorizon


