-- Prove2me | Definitions.Def_LabelConnected_Treewidth_Witnesses
-- name    : LabelConnected_Treewidth_Witnesses
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T15:27:27.453514+00:00
-- url     : https://prove2.me/theorems/d98f65e3-af67-41ab-b1b6-fcfb8bb0073e
-- title:
--   T-witnesses and T-graphs (Definition 2.1); M-witnesses, M-graphs and minimum M-witnesses (Definition 2.2)
-- statement:
--   A multigraph $G$ is a **T-graph** if it has two spanning trees $T_1, T_2$ sharing at most one edge, $|T_1 \cap T_2| \le 1$; such a pair is a **T-witness** (Definition 2.1). Parallel copies are distinct edges.
--
--   An **M-witness** of $G$ (Definition 2.2) consists of pairwise edge-disjoint subgraphs $C, F_1, F_2$, where $C$ is a cycle of length at least four and each $F_i$ is a spanning forest with exactly four components, each containing a vertex of $C$:
--   $$|E(C)| \ge 4,\quad E(C), F_1, F_2 \text{ pairwise disjoint},\quad \#\mathrm{comp}(V, F_i) = 4,\quad \text{every component of } (V,F_i) \text{ meets } V(C).$$
--   $G$ is an **M-graph** if it admits an M-witness and is not a T-graph. An M-witness is **minimum** if $|E(C)|$ is minimum among all M-witnesses of $G$; `HasMWitnessLE ends k` says some M-witness has a cycle of length at most $k$.
--
--   **Formalization Note.** `IsTWitness`, `IsTGraph`, `IsFourComponentForest`, `IsMWitness` (the cycle as a `Cycle`, the forests as edge sets), `HasMWitness`, `HasMWitnessLE`, `IsMGraph`, `IsMinimumMWitness`.
-- source:
--   Klasing, Mertzios, Molter, Morawietz, Spirakis, Recognizing Label-Connected Graphs, arXiv:2611.05144 (PDF sha256 8dde27a5…), §2, p. 7, Definitions 2.1 and 2.2

import Mathlib
import Definitions.Def_LabelConnected_Treewidth_Multigraph

open Classical

namespace LabelConnected.Treewidth

/-! # T-witnesses, T-graphs, M-witnesses and M-graphs (Definitions 2.1 and 2.2)

Klasing, Mertzios, Molter, Morawietz, Spirakis, *Recognizing Label-Connected Graphs*,
arXiv:2611.05144 (PDF sha256 8dde27a5…), §2, p. 7:
"Definition 2.1 (T-graph and T-witness). A multigraph is a T-graph if it has two spanning trees
sharing at most one edge. We call such a pair a T-witness."
"Definition 2.2 (M-witness and M-graph). An M-witness of a multigraph G consists of pairwise
edge-disjoint subgraphs C, F1, F2, where C is a cycle of length at least four and each Fi is a
spanning forest with exactly four components, each containing a vertex of C. A graph is an M-graph
if it admits an M-witness and is not a T-graph. An M-witness is minimum if |E(C)| is minimum among
all M-witnesses of G."

**Formalization Note.** Spanning trees and forests are edge sets (`Finset E`), so two parallel
copies are different edges; "sharing at most one edge" is `|T₁ ∩ T₂| ≤ 1`. The cycle is a
`Cycle ends` (a cyclic sequence of distinct vertices and distinct edges); edge-disjointness of
`C, F₁, F₂` is disjointness of `E(C), F₁, F₂`. -/

variable {n : ℕ} {E : Type} [Fintype E] [DecidableEq E]

/-- `(T₁, T₂)` is a **T-witness**: two spanning trees sharing at most one edge. -/
def IsTWitness (ends : E → Fin n × Fin n) (T₁ T₂ : Finset E) : Prop :=
  IsSpanningTree ends T₁ ∧ IsSpanningTree ends T₂ ∧ (T₁ ∩ T₂).card ≤ 1

/-- `G` is a **T-graph**: it has a T-witness. -/
def IsTGraph (ends : E → Fin n × Fin n) : Prop :=
  ∃ T₁ T₂ : Finset E, IsTWitness ends T₁ T₂

/-- `F` is a spanning forest of `G` with exactly four components, each containing a vertex of the
cycle `c`. -/
def IsFourComponentForest (ends : E → Fin n × Fin n) (c : Cycle ends) (F : Finset E) : Prop :=
  IsForest ends F ∧ numComponents ends F = 4 ∧
    ∀ K : (adjGraph ends (F : Set E)).ConnectedComponent, ∃ v ∈ c.vertSet, compOf ends F v = K

/-- `(C, F₁, F₂)` is an **M-witness**: `C` a cycle of length at least four, `F₁, F₂` spanning forests
with exactly four components each containing a vertex of `C`, the three pairwise edge-disjoint. -/
def IsMWitness (ends : E → Fin n × Fin n) (c : Cycle ends) (F₁ F₂ : Finset E) : Prop :=
  4 ≤ c.len ∧ Disjoint c.edgeSet F₁ ∧ Disjoint c.edgeSet F₂ ∧ Disjoint F₁ F₂ ∧
    IsFourComponentForest ends c F₁ ∧ IsFourComponentForest ends c F₂

/-- `G` admits an M-witness. -/
def HasMWitness (ends : E → Fin n × Fin n) : Prop :=
  ∃ (c : Cycle ends) (F₁ F₂ : Finset E), IsMWitness ends c F₁ F₂

/-- `G` admits an M-witness whose cycle has length at most `k`. -/
def HasMWitnessLE (ends : E → Fin n × Fin n) (k : ℕ) : Prop :=
  ∃ (c : Cycle ends) (F₁ F₂ : Finset E), IsMWitness ends c F₁ F₂ ∧ c.len ≤ k

/-- `G` is an **M-graph**: it admits an M-witness and is not a T-graph. -/
def IsMGraph (ends : E → Fin n × Fin n) : Prop :=
  HasMWitness ends ∧ ¬ IsTGraph ends

/-- A **minimum** M-witness: `|E(C)|` is minimum among all M-witnesses of `G`. -/
def IsMinimumMWitness (ends : E → Fin n × Fin n) (c : Cycle ends) (F₁ F₂ : Finset E) : Prop :=
  IsMWitness ends c F₁ F₂ ∧
    ∀ (c' : Cycle ends) (F₁' F₂' : Finset E), IsMWitness ends c' F₁' F₂' → c.len ≤ c'.len

end LabelConnected.Treewidth


