-- Prove2me | Definitions.Def_ProjSchedTW_OrderPolyhedra_Orders
-- name    : ProjSchedTW_OrderPolyhedra_Orders
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T15:16:59.742734+00:00
-- url     : https://prove2.me/theorems/fe1141dd-fb60-4b0e-bcfb-6b275e45dfb5
-- title:
--   Definitions 2.3.1, 2.3.2, 2.3.5 — strict orders, order polyhedra, order networks, breaking up forbidden sets
-- statement:
--   Strict orders in the activity set and the objects built from them (§2.3 of Neumann, Schwindt & Zimmermann).
--
--   A **strict order** in $V$ is a relation $O \subseteq V \times V$ that is asymmetric and transitive (Definition 1.4.1). For a strict order $O$, the **order polyhedron** is
--   $$\mathcal S_T(O) = \{ S \in \mathcal S_T \mid S_j \ge S_i + p_i \text{ for all } (i,j) \in O \}$$
--   (Definition 2.3.1). $O$ is **time-feasible** if $\mathcal S_T(O) \neq \emptyset$, and a time-feasible strict order is **feasible** if $\mathcal S_T(O) \subseteq \mathcal S$.
--
--   The **order network** $N(O)$ (Definition 2.3.2) arises from the project network $N$ by adding, for each $(i,j) \in O$, the arc $\langle i,j\rangle$ with weight $p_i$, or, if $\langle i,j\rangle \in E$ already, replacing its weight by $\max(\delta_{ij}, p_i)$.
--
--   For a schedule $S$, the **schedule-induced strict order** is
--   $$O(S) = \{ (i,j) \in V \times V \mid i \ne j,\ S_j \ge S_i + p_i \}$$
--   (Definition 2.3.5).
--
--   A strict order $O$ **breaks up** a set $F \subseteq V$ if for each minimal forbidden subset $F' \subseteq F$ there are $i, j \in F'$ such that $N(O)$ contains a path from $i$ to $j$ of length at least $p_i$; a schedule $S$ **partitions** $F$ if $O(S)$ breaks up $F$ (p. 36).
--
--   These definitions carry the geometric (order polyhedra) and the combinatorial (paths in order networks) descriptions of the feasible region.
--
--   **Formalization Note** Strict orders are finite sets of pairs (`Finset (Fin (n+2) × Fin (n+2))`). The book defines "breaks up" through the longest path length from $i$ to $j$ in $N(O)$; for a time-feasible $O$ the network $N(O)$ has no cycle of positive length, so "the longest path length is at least $p_i$" is the same as "some path has length at least $p_i$", which is what is written here, and no supremum over paths is needed.
-- source:
--   Neumann, Schwindt & Zimmermann, Project Scheduling with Time Windows and Scarce Resources, 2nd ed., Springer 2003, p. 16, Definition 1.4.1; p. 30, Definitions 2.3.1, 2.3.2; p. 32, Definition 2.3.5; p. 36 (break up, partition)

import Mathlib
import Definitions.Def_ProjSchedTW_OrderPolyhedra_Project
import Definitions.Def_ProjSchedTW_OrderPolyhedra_Resources

namespace ProjSchedTW.OrderPolyhedra

/-- A strict order in `V` (Definition 1.4.1, p. 16), identified with the set `O ⊆ V × V` of its
pairs: asymmetric (`(i,j) ∈ O` and `(j,i) ∈ O` never both hold) and transitive. -/
def IsStrictOrderSet {n : ℕ} (O : Finset (Fin (n + 2) × Fin (n + 2))) : Prop :=
  (∀ i j : Fin (n + 2), (i, j) ∈ O → (j, i) ∉ O) ∧
  (∀ h i j : Fin (n + 2), (h, i) ∈ O → (i, j) ∈ O → (h, j) ∈ O)

/-- The order polyhedron `S_T(O) = {S ∈ S_T | S_j ≥ S_i + p_i for all (i,j) ∈ O}`
(Definition 2.3.1, p. 30). -/
def Project.orderPolyhedron {n : ℕ} {K : Type} (P : Project n K)
    (O : Finset (Fin (n + 2) × Fin (n + 2))) : Set (Fin (n + 2) → ℝ) :=
  {S | P.IsTimeFeasible S ∧ ∀ e ∈ O, S e.1 + (P.p e.1 : ℝ) ≤ S e.2}

/-- A time-feasible strict order (Definition 2.3.1, p. 30): a strict order `O` with
`S_T(O) ≠ ∅`. -/
def Project.IsTimeFeasibleOrder {n : ℕ} {K : Type} (P : Project n K)
    (O : Finset (Fin (n + 2) × Fin (n + 2))) : Prop :=
  IsStrictOrderSet O ∧ (P.orderPolyhedron O).Nonempty

/-- A feasible strict order (Definition 2.3.1, p. 30): a time-feasible strict order `O` with
`S_T(O) ⊆ 𝒮`, i.e. every schedule of its order polyhedron is feasible. -/
def Project.IsFeasibleOrder {n : ℕ} {K : Type} (P : Project n K)
    (O : Finset (Fin (n + 2) × Fin (n + 2))) : Prop :=
  P.IsTimeFeasibleOrder O ∧ ∀ S ∈ P.orderPolyhedron O, P.IsFeasible S

open Classical in
/-- The order network `N(O)` (Definition 2.3.2, p. 30): the project network `N` with, for each
pair `(i,j) ∈ O`, the arc `⟨i,j⟩` added with weight `p_i`, or, if `N` already contains the arc
`⟨i,j⟩` with weight `δ_ij`, its weight replaced by `max(δ_ij, p_i)`. -/
noncomputable def Project.orderNetwork {n : ℕ} {K : Type} (P : Project n K)
    (O : Finset (Fin (n + 2) × Fin (n + 2))) : Network n where
  arcs := ↑P.E ∪ ↑O
  wt i j :=
    if (i, j) ∈ O then
      (if (i, j) ∈ P.E then max (P.δ i j) (P.p i : ℤ) else (P.p i : ℤ))
    else P.δ i j

open Classical in
/-- The schedule-induced strict order `O(S) = {(i,j) ∈ V × V | i ≠ j, S_j ≥ S_i + p_i}`
(Definition 2.3.5, p. 32). -/
noncomputable def Project.scheduleOrder {n : ℕ} {K : Type} (P : Project n K)
    (S : Fin (n + 2) → ℝ) : Finset (Fin (n + 2) × Fin (n + 2)) :=
  Finset.univ.filter (fun e => e.1 ≠ e.2 ∧ S e.1 + (P.p e.1 : ℝ) ≤ S e.2)

/-- `O` breaks up the set `F` (p. 36): for each minimal forbidden subset `F' ⊆ F` there are
activities `i, j ∈ F'` such that the order network `N(O)` contains a path from `i` to `j` of
length at least `p_i` (equivalently, for a time-feasible `O`, the longest path length from `i` to
`j` in `N(O)` is at least `p_i`). -/
def Project.BreaksUp {n : ℕ} {K : Type} (P : Project n K)
    (O : Finset (Fin (n + 2) × Fin (n + 2))) (F : Finset (Fin (n + 2))) : Prop :=
  ∀ F' ⊆ F, P.IsMinimalForbidden F' →
    ∃ i ∈ F', ∃ j ∈ F', (P.orderNetwork O).HasPathOfLengthAtLeast i j (P.p i)

/-- The schedule `S` partitions the set `F` into feasible subsets (p. 36) if the
schedule-induced strict order `O(S)` breaks up `F`. -/
def Project.Partitions {n : ℕ} {K : Type} (P : Project n K) (S : Fin (n + 2) → ℝ)
    (F : Finset (Fin (n + 2))) : Prop :=
  P.BreaksUp (P.scheduleOrder S) F

end ProjSchedTW.OrderPolyhedra


