-- Prove2me | Definitions.Def_ConvexRMDP_RMDP
-- name    : ConvexRMDP_RMDP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:15:30.909583+00:00
-- url     : https://prove2.me/theorems/6900c40a-3392-4422-994e-20e8ad2187c3
-- title:
--   sa-rectangular robust Markov decision process $(S, A, r, \gamma, \mathcal U)$
-- statement:
--   An **sa-rectangular robust Markov decision process** consists of
--
--   1. a finite set of states $\mathcal S$ and a finite set of actions $\mathcal A$;
--   2. rewards $r_{sa} \ge 0$ for every $(s,a) \in \mathcal S \times \mathcal A$;
--   3. a discount factor $\gamma \in (0,1)$;
--   4. for every pair $(s,a)$, a nonempty **uncertainty set** $\mathcal U_{sa} \subseteq \Delta(\mathcal S)$ of possible next-state distributions, where $\Delta(\mathcal S) = \{p \in \mathbb R^{\mathcal S}_+ : \sum_{s'} p_{s'} = 1\}$.
--
--   The uncertainty set of the model is the product
--   $$
--   \mathcal U = \times_{(s,a) \in \mathcal S \times \mathcal A} \mathcal U_{sa},
--   $$
--   so nature chooses the transition row of each state-action pair independently of the others (**sa-rectangularity**). No convexity, closedness or compactness of the sets $\mathcal U_{sa}$ is assumed.
--
--   This is the model on which every operator and theorem of the mission is built: the regularized robust Bellman operator $\tilde T$ and the operator $\tilde t$ of the convex formulation.
--
--   **Formalization Note** States and actions are finite types; $\mathbb R^{\mathcal S}$ is the function type `S → ℝ` and $\Delta(\mathcal S)$ is Mathlib's `stdSimplex`. Nonnegativity of rewards and $\gamma \in (0,1)$ are the paper's standing assumptions of §3.1; nonemptiness of each $\mathcal U_{sa}$ is implicit in the paper (its formulas take a minimum over $\mathcal U_{sa}$) and is a field here. The initial distribution $\alpha$ of the paper plays no role in these results and is omitted. Nonemptiness of $\mathcal A$ is a separate hypothesis of the theorems.
-- source:
--   Grand-Clément & Petrik, On the Convex Formulations of Robust Markov Decision Processes, arXiv:2209.10187v2 (13 Dec 2023), §3.1, p.6 (standing assumptions: finite S and A, r ≥ 0, γ ∈ (0,1)); §3.2, Assumption 3.1, p.8

import Mathlib

namespace ConvexRMDP

/-- **An sa-rectangular robust Markov decision process** (Grand-Clément & Petrik,
arXiv:2209.10187v2, §3.1, p.6 and §3.2, Assumption 3.1, p.8).

The states `S` and actions `A` are finite types. The data are
* `r s a`, the instantaneous reward `r_{sa}`, nonnegative (standing assumption of §3.1, p.6);
* `γ`, the discount factor, `γ ∈ (0,1)` (§3.1, p.6);
* `U s a ⊆ Δ(S)`, the uncertainty set `𝒰_{sa}` for the next-state distribution from `s` under `a`.
  The uncertainty set is `𝒰 = ×_{(s,a)} 𝒰_{sa}` (Assumption 3.1), so sa-rectangularity is built in:
  nature picks each row `p ∈ 𝒰_{sa}` independently.

**Formalization Note.** `ℝ^S` is `S → ℝ`; `Δ(S)` is Mathlib's `stdSimplex ℝ S`. Each `𝒰_{sa}` is
assumed nonempty (the paper's `min_{p ∈ 𝒰_{sa}}` presupposes it); no convexity, closedness or
compactness is assumed. The initial distribution `α` of §3.1 plays no role in the results built on
this structure and is omitted. Nonemptiness of `A` is a separate hypothesis of the theorems. -/
structure RMDP (S A : Type*) [Fintype S] [Fintype A] where
  /-- The rewards `r_{sa}`. -/
  r : S → A → ℝ
  /-- The discount factor `γ`. -/
  γ : ℝ
  /-- The uncertainty sets `𝒰_{sa} ⊆ Δ(S)`. -/
  U : S → A → Set (S → ℝ)
  r_nonneg : ∀ s a, 0 ≤ r s a
  γ_pos : 0 < γ
  γ_lt_one : γ < 1
  U_subset : ∀ s a, U s a ⊆ stdSimplex ℝ S
  U_nonempty : ∀ s a, (U s a).Nonempty

end ConvexRMDP


