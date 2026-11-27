-- Prove2me | Definitions.Def_ConvexRMDP_Supplement_SRMDP
-- name    : ConvexRMDP_Supplement_SRMDP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T01:52:51.71537+00:00
-- url     : https://prove2.me/theorems/a80d6449-5243-5ebd-bf58-39e63fc27b74
-- title:
--   s-rectangular robust Markov decision process ($\mathcal U=\times_s\mathcal U_s$, $\mathcal U_s\subseteq\Delta(S)^A$ convex compact)
-- statement:
--   An **s-rectangular robust Markov decision process** consists of
--
--   1. finite sets of states $\mathcal S$ and actions $\mathcal A$;
--   2. rewards $r_{sa} \ge 0$ and a discount factor $\gamma \in (0,1)$;
--   3. for every state $s$, a nonempty, convex and compact **uncertainty set** $\mathcal U_s \subseteq (\Delta(\mathcal S))^{\mathcal A}$ of families $P = (P_a)_{a \in \mathcal A}$ of next-state distributions.
--
--   The uncertainty set of the model is $\mathcal U = \times_{s \in \mathcal S} \mathcal U_s$: nature chooses the transition rows of all actions of a state jointly, independently across states.
--
--   **Formalization Note** An element of $(\Delta(\mathcal S))^{\mathcal A}$ is a function `P : A → S → ℝ` with every row `P a` in `stdSimplex ℝ S`. Nonemptiness of each $\mathcal U_s$ is implicit in the paper (its operators take a minimum over $\mathcal U_s$). This is a separate structure from the sa-rectangular `ConvexRMDP.RMDP`, whose sets are indexed by state–action pairs.
-- source:
--   Grand-Clément & Petrik, arXiv:2209.10187v2, §3.1, p.6 (standing assumptions) and §6, p.20 (s-rectangular uncertainty set)

import Mathlib

namespace ConvexRMDP

namespace Supplement

/-- **An s-rectangular robust Markov decision process** (Grand-Clément & Petrik,
arXiv:2209.10187v2, §3.1, p.6 and §6, p.20).

The states `S` and actions `A` are finite types; `r s a ≥ 0` are the rewards and `γ ∈ (0,1)` the
discount factor (standing assumptions of §3.1). The uncertainty set is `𝒰 = ×_{s ∈ S} 𝒰_s` with each
`𝒰_s ⊆ (Δ(S))^A` a convex compact set (§6, p.20): an element `P ∈ 𝒰_s` is a family `(P_a)_{a ∈ A}` of
next-state distributions, `P a s'` the probability of moving from `s` to `s'` under `a`. Nature picks
the whole family `P ∈ 𝒰_s` jointly for the actions of `s`, independently across states.

**Formalization Note.** `(Δ(S))^A` is `{P : A → S → ℝ | ∀ a, P a ∈ stdSimplex ℝ S}`. Each `𝒰_s` is
also assumed nonempty (the operators of §6 take a minimum over `𝒰_s`). Rectangularity across states
is the indexing by `s`. This is not the sa-rectangular `ConvexRMDP.RMDP`, whose sets are indexed by
`(s,a)`. -/
structure SRMDP (S A : Type*) [Fintype S] [Fintype A] where
  /-- The rewards `r_{sa}`. -/
  r : S → A → ℝ
  /-- The discount factor `γ`. -/
  γ : ℝ
  /-- The uncertainty sets `𝒰_s ⊆ (Δ(S))^A`. -/
  U : S → Set (A → S → ℝ)
  r_nonneg : ∀ s a, 0 ≤ r s a
  γ_pos : 0 < γ
  γ_lt_one : γ < 1
  U_subset : ∀ s, U s ⊆ {P | ∀ a, P a ∈ stdSimplex ℝ S}
  U_nonempty : ∀ s, (U s).Nonempty
  U_convex : ∀ s, Convex ℝ (U s)
  U_compact : ∀ s, IsCompact (U s)

end Supplement

end ConvexRMDP


