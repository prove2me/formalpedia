-- Prove2me | Definitions.Def_ImprovedMMS_Additive_Bipartite
-- name    : ImprovedMMS_Additive_Bipartite
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T01:19:27.214918+00:00
-- url     : https://prove2.me/theorems/634bf8b7-3ef5-4620-a9e6-06d64e09ac5e
-- title:
--   §3.2.2, pp. 18–20 — bipartite matchings, maximum matchings, N(T), alternating reach, F_H(M, X̂) (Def. 3.5) and MCMWM
-- statement:
--   Let $H$ be a bipartite graph with vertex sides $\hat{\mathcal X}$ and $\hat{\mathcal Y}$ and edge set $E(H)\subseteq\hat{\mathcal X}\times\hat{\mathcal Y}$, and let $w$ be a real weight on pairs $(\hat x,\hat y)$.
--
--   1. A **matching** $M$ is a set of edges no two of which share an endpoint; it is **maximum** if it has the highest number of edges among all matchings of $H$.
--   2. For $T\subseteq\hat{\mathcal X}$, $N(T)$ is the set of neighbours of $T$ in $\hat{\mathcal Y}$.
--   3. (Definition 3.5) Let $M$ be a maximum matching, $\hat{\mathcal Y}_1$ the vertices of $\hat{\mathcal Y}$ not saturated by $M$, $\hat{\mathcal Y}_2$ the vertices of $\hat{\mathcal Y}$ connected to $\hat{\mathcal Y}_1$ by an alternating path, and $\hat{\mathcal X}_2=M(\hat{\mathcal Y}_2)$ the vertices of $\hat{\mathcal X}$ matched by $M$ to vertices of $\hat{\mathcal Y}_2$. Then
--   $$F_H(M,\hat{\mathcal X})=\hat{\mathcal X}\setminus\hat{\mathcal X}_2.$$
--   4. The sub-graph of $H$ induced on $\hat{\mathcal X}'\cup\hat{\mathcal Y}'$ keeps the edges with both ends in these sets.
--   5. A **maximum cardinality maximum weighted matching** (MCMWM) is a maximum matching whose total weight $\sum_{(\hat x,\hat y)\in M}w(\hat x,\hat y)$ is the highest among all maximum matchings.
--
--   These are the graph tools the paper uses to cluster agents and goods (Lemmas 3.6, 3.7, Corollary 3.8) and to build cycle-envy-free sets of semi-satisfied agents (Lemma 3.13).
--
--   **Formalization Note** The sides are finite sets `X : Finset α`, `Y : Finset β`, edges a `Finset (α × β)` (theorems assume `E ⊆ X ×ˢ Y`), and a matching `Mt ⊆ E`. The alternating reach is the inductive predicate `AltReach E Mt Y`: every vertex of `Y` unsaturated by `Mt` is reached, and if `y` is reached, `(x, y)` is a non-matching edge and `(x, y')` a matching edge, then `y'` is reached. Since edges from $\hat{\mathcal Y}$ to $\hat{\mathcal X}$ are then always non-matching and edges back always matching, reachability by such walks is reachability by alternating paths. `FH E Mt X Y` is the set of `x ∈ X` with no reached `y` matched to `x`.
-- source:
--   Ghodsi, Hajiaghayi, Seddighin, Seddighin & Yami, Fair Allocation of Indivisible Goods: Improvement and Generalization, arXiv:1704.00222v3, p. 18 (maximum matching, Definition 3.5), p. 19 (N(T), induced sub-graph), p. 20 (MCMWM)

import Mathlib

namespace ImprovedMMS.Additive

variable {α β : Type*}

/-- A matching of the bipartite graph with edge set `E ⊆ X × Y`: a set `Mt ⊆ E` of edges no two
of which share an `X`-end or a `Y`-end. -/
def IsMatching (E Mt : Finset (α × β)) : Prop :=
  Mt ⊆ E ∧ (∀ e ∈ Mt, ∀ e' ∈ Mt, e.1 = e'.1 → e = e') ∧
    (∀ e ∈ Mt, ∀ e' ∈ Mt, e.2 = e'.2 → e = e')

/-- p. 18: a maximum matching, i.e. a matching with the highest number of edges. -/
def IsMaxMatching (E Mt : Finset (α × β)) : Prop :=
  IsMatching E Mt ∧ ∀ M' : Finset (α × β), IsMatching E M' → M'.card ≤ Mt.card

/-- `N(T)`: the set of neighbours of a set `T` of `X`-vertices. -/
def nbhd [DecidableEq α] [DecidableEq β] (E : Finset (α × β)) (T : Finset α) : Finset β :=
  (E.filter (fun e => e.1 ∈ T)).image Prod.snd

/-- Definition 3.5, p. 18: the `Y`-vertices connected by an alternating path (with respect to
`Mt`) to a vertex of `Y₁`, the vertices of `Y` not saturated by `Mt`. Starting from an unsaturated
`y ∈ Y`, a path alternates a non-matching edge `(x, y)` and the matching edge `(x, y')`. -/
inductive AltReach (E Mt : Finset (α × β)) (Y : Finset β) : β → Prop
  | unsat {y : β} : y ∈ Y → (∀ x : α, (x, y) ∉ Mt) → AltReach E Mt Y y
  | step {y y' : β} {x : α} : AltReach E Mt Y y → (x, y) ∈ E → (x, y) ∉ Mt → (x, y') ∈ Mt →
      AltReach E Mt Y y'

open Classical in
/-- Definition 3.5, p. 18: `F_H(M, X) = X \ X₂`, where `X₂ = M(Y₂)` is the set of `X`-vertices
matched by `Mt` to a vertex `y ∈ Y₂` connected to `Y₁` by an alternating path. -/
noncomputable def FH (E Mt : Finset (α × β)) (X : Finset α) (Y : Finset β) : Finset α :=
  X.filter (fun x => ¬ ∃ y : β, AltReach E Mt Y y ∧ (x, y) ∈ Mt)

/-- The edge set of the sub-graph induced on `X' ∪ Y'`. -/
def inducedEdges [DecidableEq α] [DecidableEq β] (E : Finset (α × β)) (X' : Finset α)
    (Y' : Finset β) : Finset (α × β) :=
  E.filter (fun e => e.1 ∈ X' ∧ e.2 ∈ Y')

/-- p. 20: a maximum cardinality maximum weighted matching (MCMWM) of the graph with edges `E`
and weights `w`: a maximum matching whose total weight `∑_{(x,y) ∈ Mt} w(x, y)` is the highest
among all maximum matchings. -/
def IsMCMWM (E : Finset (α × β)) (w : α → β → ℝ) (Mt : Finset (α × β)) : Prop :=
  IsMaxMatching E Mt ∧
    ∀ M' : Finset (α × β), IsMaxMatching E M' → ∑ e ∈ M', w e.1 e.2 ≤ ∑ e ∈ Mt, w e.1 e.2

end ImprovedMMS.Additive


