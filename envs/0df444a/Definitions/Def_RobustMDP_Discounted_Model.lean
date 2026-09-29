-- Prove2me | Definitions.Def_RobustMDP_Discounted_Model
-- name    : RobustMDP_Discounted_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T23:54:58.466094+00:00
-- url     : https://prove2.me/theorems/f6d35975-ab34-45fc-9840-61651d236d51
-- title:
--   Discounted MDP with rectangular uncertainty on the transition rows; stationary policies of controller and nature
-- statement:
--   A **discounted robust Markov decision process** consists of the following data.
--
--   1. A finite state space $\mathcal X = \{1, \dots, n\}$ and a finite nonempty action set $\mathcal A$, the same in every state.
--   2. A cost $c(i, a) \ge 0$ for every state $i$ and action $a$. The cost incurred at stage $t$ is $c_t(i, a) = \nu^t c(i, a)$, and there is no terminal cost.
--   3. A discount factor $\nu \in [0, 1)$.
--   4. For every action $a$ and state $i$, a nonempty set $\mathcal P_i^a \subseteq \Delta_n$ of probability vectors, where $\Delta_n = \{p \in \mathbb R^n_+ : p^T \mathbf 1 = 1\}$. It describes the uncertainty on the $i$th row of the transition matrix $P^a$ of action $a$.
--
--   Uncertainty is **rectangular**: the set of admissible matrices for action $a$ is the product
--   $$\mathcal P^a = \mathcal P_1^a \times \cdots \times \mathcal P_n^a,$$
--   so each row of each matrix is chosen independently of the others. No convexity or closedness of the row sets is assumed.
--
--   A **stationary control policy** $\pi = (\mathbf a, \mathbf a, \dots)$ is a single decision rule $\mathbf a : \mathcal X \to \mathcal A$ used at every stage; $\Pi_s$ is the set of them. A **stationary policy of nature**, an element of $\mathcal T_s$, is one collection of matrices $(P^a)_{a \in \mathcal A}$ with $P^a \in \mathcal P^a$, used at every stage.
--
--   This is the model of the paper's discounted infinite-horizon problem (6), on which every statement of the mission is built.
--
--   **Formalization Note** States are `Fin n`. Nonemptiness of the row sets is implicit in the paper (otherwise nature has no admissible policy) and is a field of the structure. The discount range is the one printed in Theorem 3, $[0,1)$; §4 prints $(0,1)$. A policy of nature is the subtype of functions `P : A → Fin n → Fin n → ℝ` with `P a i ∈ 𝒫_i^a`, where `P a i j` is the probability of moving from $i$ to $j$ under $a$.
-- source:
--   Nilim and El Ghaoui, Robust Control of Markov Decision Processes with Uncertain Transition Matrices, Oper. Res. 53 (2005), pp. 781–782, §2.1–2.2 (stationary policies, Eq. (6)), p. 782 §3, and p. 785 §4

import Mathlib

namespace RobustMDP.Discounted

/-- A discounted infinite-horizon Markov decision process with rectangular uncertainty on its
transition rows (Nilim–El Ghaoui 2005, §2.1–2.2 pp. 781–782, §3 p. 782, §4 p. 785).
States are `Fin n` and `A` is the (state-independent) action set.

* `cost i a` is the constant cost `c(i, a)`, nonnegative and finite; the stage-`t` cost is
  `c_t(i, a) = ν^t c(i, a)` and the terminal cost is zero;
* `discount` is the discount factor `ν ∈ [0, 1)` (the range printed in Theorem 3);
* `rows a i` is the set `𝒫_i^a ⊆ Δ_n` of possible next-state distributions from state `i` under
  action `a`. The rectangular uncertainty property `𝒫^a = 𝒫_1^a × ⋯ × 𝒫_n^a` is built in: nature
  chooses each row independently from its own set. Only inclusion in the simplex is assumed (no
  convexity, no closedness); nonemptiness is implicit in the paper and made explicit here. -/
structure Model (n : ℕ) (A : Type) where
  cost : Fin n → A → ℝ
  discount : ℝ
  rows : A → Fin n → Set (Fin n → ℝ)
  cost_nonneg : ∀ i a, 0 ≤ cost i a
  discount_nonneg : 0 ≤ discount
  discount_lt_one : discount < 1
  rows_subset_simplex : ∀ a i, rows a i ⊆ stdSimplex ℝ (Fin n)
  rows_nonempty : ∀ a i, (rows a i).Nonempty

/-- A stationary (deterministic, Markov) controller policy `π = (𝐚, 𝐚, …)`, `𝐚 : 𝒳 → 𝒜`,
the same decision rule at every stage; the space `Π_s` (p. 782). -/
abbrev StationaryPolicy (n : ℕ) (A : Type) := Fin n → A

/-- A stationary admissible policy of nature, an element of `𝒯_s` (p. 781): one collection of
transition matrices `(P^a)_{a ∈ 𝒜}` used at every stage, where the `i`-th row `P a i` of `P^a`
lies in `𝒫_i^a`, chosen independently for each `(a, i)`. `P a i j` is the probability of moving
from state `i` to state `j` under action `a`. -/
abbrev Model.StationaryNature {n : ℕ} {A : Type} (M : Model n A) :=
  {P : A → Fin n → Fin n → ℝ // ∀ a i, P a i ∈ M.rows a i}

end RobustMDP.Discounted


