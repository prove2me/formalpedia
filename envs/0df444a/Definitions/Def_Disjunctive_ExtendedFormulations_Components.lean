-- Prove2me | Definitions.Def_Disjunctive_ExtendedFormulations_Components
-- name    : Disjunctive_ExtendedFormulations_Components
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T16:31:45.538884+00:00
-- url     : https://prove2.me/theorems/969cb95f-4e6d-43f1-b633-1fea43263bd4
-- title:
--   Components and bipartiteness of an induced subgraph
-- statement:
--   This definition fixes the component-counting and bipartiteness machinery Theorem 5.4 needs,
--   built directly from reachability and 2-colorability rather than Mathlib's induced-subgraph API.
--
--   Two vertices are **reachable within $S$** if connected by a walk using only edges between vertices
--   of $S$. $C$ **is a component of $G(S)$** if $C \subseteq S$ is nonempty, every pair of its
--   vertices is reachable within $S$, and no vertex of $C$ is adjacent (within $S$) to a vertex of
--   $S \setminus C$ — the standard "maximal connected subset" characterization of a graph component.
--   $C$ **spans a bipartite subgraph** if it admits a 2-coloring under which every edge inside $C$
--   joins different colors; $c(S)$, the **component count**, is the number of such maximal components
--   of $G(S)$.
--
--   **Formalization Note.** Components are characterized directly (connected + maximal), avoiding
--   Mathlib's `SimpleGraph.induce`/`ConnectedComponent` quotient machinery, since the "maximal
--   connected subset" reading is exactly what the book's own prose means by "a component of $G(S)$.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 76-77, Section 5.2.4

import Mathlib

namespace Disjunctive.ExtendedFormulations

open Classical

/-- `u` and `v` are connected by a walk staying inside `S` (Balas §5.2.4, p. 76, used to define
the components of `G(S)`). -/
def ReachableWithin {V : Type*} (G : SimpleGraph V) (S : Finset V) (u v : V) : Prop :=
  Relation.ReflTransGen (fun x y => x ∈ S ∧ y ∈ S ∧ G.Adj x y) u v

/-- `C` is a connected component of the induced subgraph `G(S)` (Balas §5.2.4, p. 76): a
nonempty subset of `S`, connected within itself, with no edge of `G` leaving it inside `S`. -/
def IsComponentOf {V : Type*} [DecidableEq V] (G : SimpleGraph V) (S C : Finset V) : Prop :=
  C ⊆ S ∧ C.Nonempty ∧ (∀ u ∈ C, ∀ v ∈ C, ReachableWithin G S u v) ∧
    ∀ i ∈ C, ∀ j ∈ S, j ∉ C → ¬ G.Adj i j

/-- `C` spans a bipartite subgraph of `G`: a 2-coloring of `C` under which every edge of `G`
inside `C` is bichromatic (Balas §5.2.4, p. 77, "nonbipartite" is the negation). -/
def IsBipartiteOn {V : Type*} (G : SimpleGraph V) (C : Finset V) : Prop :=
  ∃ f : V → Bool, ∀ i ∈ C, ∀ j ∈ C, G.Adj i j → f i ≠ f j

/-- `c(S)`, the number of connected components of `G(S)` (Balas §5.2.4, p. 76). -/
noncomputable def ComponentCount {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (S : Finset V) : ℕ :=
  (S.powerset.filter (IsComponentOf G S)).card

end Disjunctive.ExtendedFormulations


