-- Prove2me | Definitions.Def_ImprovedMMS_Additive_Envy
-- name    : ImprovedMMS_Additive_Envy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T01:19:27.436093+00:00
-- url     : https://prove2.me/theorems/d154476b-84a6-45cc-b98d-749e4c403480
-- title:
--   §3.2.3, pp. 19–20 — semi-satisfied agents, ϵ_i, envy, winners, losers, cycle-envy-freeness, G_C and topological orderings
-- statement:
--   Each agent $a_i$ holds two sets of goods $f_i$ and $g_i$, and $V_i$ is its valuation.
--
--   1. Agent $a_i$ is **semi-satisfied** if $f_i\neq\emptyset$ but $g_i=\emptyset$; then $\epsilon_i=3/4-V_i(f_i)$.
--   2. (Definition 3.9) Agent $a_i$ **envies** a different agent $a_j$ if $V_i(f_j)\ge V_i(f_i)$. For a set $T$ of agents, $a_i\in T$ is a **winner** of $T$ if it envies no other agent of $T$, and a **loser** of $T$ if no other agent of $T$ envies it.
--   3. (Definition 3.10) A set $T$ is **cycle-envy-free** if every non-empty subset of $T$ contains at least one winner and one loser.
--   4. The **representation graph** $G_C$ of a set $C$ has a vertex $v_i$ for each $a_i\in C$ and a directed edge $v_i\to v_j$ whenever $a_i$ envies $a_j$.
--   5. (Definition 3.12) A **topological ordering** $\prec_O$ of $C$ is a total order of $C$ in which every edge of $G_C$ goes forward: if $a_i$ envies $a_j$ then $a_i\prec_O a_j$.
--
--   These notions organise the bag-filling phase of the existence proof, where semi-satisfied agents are served in an order that avoids envy cycles.
--
--   **Formalization Note** Bundles are `f g : Fin n → Finset (Fin m)`. Definition 3.9's inequality $V_i(f_j)\ge V_i(f_i)$ always holds at $j=i$, which would put a self-loop at every vertex of $G_C$ and make Lemma 3.11 false; envy is therefore between **distinct** agents (`envies v f i j := i ≠ j ∧ …`), as the words "no other agent" in the definitions of winner and loser indicate. A topological ordering is given by positions `pos : Fin n → ℕ`, injective on `C`, with `pos i < pos j` for every edge $v_i\to v_j$ of $G_C$; $a_i\prec_O a_j$ means `pos i < pos j`.
-- source:
--   Ghodsi, Hajiaghayi, Seddighin, Seddighin & Yami, Fair Allocation of Indivisible Goods: Improvement and Generalization, arXiv:1704.00222v3, p. 19 ((ii) semi-satisfied, ϵ_i; Definition 3.9), p. 20 (Definition 3.10, representation graph G_C, Definition 3.12)

import Mathlib

namespace ImprovedMMS.Additive

variable {n m : ℕ}

/-- p. 19 (ii): agent `i` is semi-satisfied by the sets `f_i, g_i` allocated to it if `f_i ≠ ∅`
but `g_i = ∅`. -/
def IsSemiSatisfied (f g : Fin n → Finset (Fin m)) (i : Fin n) : Prop :=
  (f i).Nonempty ∧ g i = ∅

/-- p. 19 (ii): `ϵ_i = 3/4 − V_i(f_i)`. -/
noncomputable def eps (v : Fin n → Finset (Fin m) → ℝ) (f : Fin n → Finset (Fin m)) (i : Fin n) : ℝ :=
  3 / 4 - v i (f i)

/-- Definition 3.9, p. 19: agent `i` envies a different agent `j` if `V_i(f_j) ≥ V_i(f_i)`. -/
def envies (v : Fin n → Finset (Fin m) → ℝ) (f : Fin n → Finset (Fin m)) (i j : Fin n) : Prop :=
  i ≠ j ∧ v i (f i) ≤ v i (f j)

/-- Definition 3.9, p. 19: `i` is a winner of `T` if `i ∈ T` envies no other agent of `T`. -/
def IsWinner (v : Fin n → Finset (Fin m) → ℝ) (f : Fin n → Finset (Fin m))
    (T : Finset (Fin n)) (i : Fin n) : Prop :=
  i ∈ T ∧ ∀ j ∈ T, ¬ envies v f i j

/-- Definition 3.9, p. 19: `i` is a loser of `T` if no other agent of `T` envies `i ∈ T`. -/
def IsLoser (v : Fin n → Finset (Fin m) → ℝ) (f : Fin n → Finset (Fin m))
    (T : Finset (Fin n)) (i : Fin n) : Prop :=
  i ∈ T ∧ ∀ j ∈ T, ¬ envies v f j i

/-- Definition 3.10, p. 20: `C` is cycle-envy-free if every non-empty subset of `C` contains at
least one winner and one loser. -/
def IsCycleEnvyFree (v : Fin n → Finset (Fin m) → ℝ) (f : Fin n → Finset (Fin m))
    (C : Finset (Fin n)) : Prop :=
  ∀ T ⊆ C, T.Nonempty → (∃ i, IsWinner v f T i) ∧ (∃ i, IsLoser v f T i)

/-- p. 20: the edge relation of the representation digraph `G_C`: an edge `v_i → v_j` for
`a_i, a_j ∈ C` with `a_i` envying `a_j`. -/
def envyGraph (v : Fin n → Finset (Fin m) → ℝ) (f : Fin n → Finset (Fin m))
    (C : Finset (Fin n)) (i j : Fin n) : Prop :=
  i ∈ C ∧ j ∈ C ∧ envies v f i j

/-- Definition 3.12, p. 20: a topological ordering `≺_O` of `C`, given by distinct positions
`pos` on `C` (`a_i ≺_O a_j ↔ pos i < pos j`) in which every edge of `G_C` goes forward. -/
def IsTopologicalOrder (v : Fin n → Finset (Fin m) → ℝ) (f : Fin n → Finset (Fin m))
    (C : Finset (Fin n)) (pos : Fin n → ℕ) : Prop :=
  Set.InjOn pos (C : Set (Fin n)) ∧ ∀ i ∈ C, ∀ j ∈ C, envyGraph v f C i j → pos i < pos j

end ImprovedMMS.Additive


