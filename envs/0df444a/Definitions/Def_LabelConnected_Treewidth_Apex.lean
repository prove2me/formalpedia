-- Prove2me | Definitions.Def_LabelConnected_Treewidth_Apex
-- name    : LabelConnected_Treewidth_Apex
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T15:27:13.591447+00:00
-- url     : https://prove2.me/theorems/78c31402-c02a-4ee5-bb51-0f90d7fd3191
-- title:
--   The apex formulation of M-witnesses: apex graphs and solutions (C, D1, D2, A)
-- statement:
--   Add a new vertex $a$ (the **apex**) to $G$ and, for every vertex $v$, an auxiliary **apex edge** $av$. A **solution** is a tuple $(C, D_1, D_2, A)$ of pairwise disjoint sets $C, D_1, D_2$ of original edges and a set $A$ of apex edges such that
--   1. $C$ is the edge set of a connected 2-regular graph with at least four vertices;
--   2. every apex edge in $A$ ends at a vertex of $C$, and $|A| \le 4$;
--   3. $\widehat G_i = (V \cup \{a\},\ D_i \cup A)$ is connected for each $i \in \{1, 2\}$.
--
--   Here the graph of condition 1 is $(V(C), C)$, $V(C)$ the endpoints of $C$, degrees counted with multiplicity.
--
--   **Formalization Note.** The apex is `none : Option (Fin n)`, the original vertex $v$ is `some v`, and the apex edge $av$ is identified with $v$, so $A$ is a `Finset (Fin n)`. `apexGraph ends D A` is the simple graph underlying $(V \cup \{a\}, D \cup A)$; `IsConnTwoRegularFour`, `IsApexSolution`.
-- source:
--   Klasing, Mertzios, Molter, Morawietz, Spirakis, Recognizing Label-Connected Graphs, arXiv:2611.05144 (PDF sha256 8dde27a5…), §6.1, pp. 26–27, The M-Witness Formulation

import Mathlib
import Definitions.Def_LabelConnected_Treewidth_Multigraph

open Classical

namespace LabelConnected.Treewidth

/-! # The apex formulation of M-witnesses (proof of Theorem 6.2)

Klasing, Mertzios, Molter, Morawietz, Spirakis, *Recognizing Label-Connected Graphs*,
arXiv:2611.05144 (PDF sha256 8dde27a5…), §6.1, "The M-Witness Formulation", pp. 26–27: "Add a new
vertex a to the graph […]. For every v ∈ V, introduce an auxiliary edge av, called an apex edge.
[…] We seek pairwise disjoint sets C, D1, D2 of original edges and a common set A of apex edges
such that
1. C is the edge set of a connected 2-regular graph with at least four vertices;
2. every apex edge in A ends at a vertex of C, and |A| ≤ 4;
3. Ĝi = (V ∪ {a}, Di ∪ A) is connected for each i ∈ {1, 2}.
[…] We call a tuple (C, D1, D2, A) satisfying them a solution."

**Formalization Note.** The apex vertex `a` is `none : Option (Fin n)`, an original vertex `v` is
`some v`; the apex edge `av` is identified with `v`, so `A : Finset (Fin n)`. The graph
`(V(C), C)` in condition 1 has vertex set `V(C)`, the endpoints of `C`; degrees count
multiplicities (`mdeg`). `Ĝᵢ` is the simple graph underlying `(V ∪ {a}, Dᵢ ∪ A)`, which has the same
connectivity. -/

variable {n : ℕ} {E : Type} [Fintype E] [DecidableEq E]

/-- `Ĝ = (V ∪ {a}, D ∪ A)`: the original vertices `some v`, the apex `none`, the edges of `D` and
the apex edges `a v` for `v ∈ A`. -/
def apexGraph (ends : E → Fin n × Fin n) (D : Finset E) (A : Finset (Fin n)) :
    SimpleGraph (Option (Fin n)) :=
  SimpleGraph.fromRel fun x y =>
    (∃ e ∈ D, x = some (ends e).1 ∧ y = some (ends e).2) ∨ (x = none ∧ ∃ v ∈ A, y = some v)

/-- Condition 1: `C` is the edge set of a connected 2-regular graph `(V(C), C)` with at least four
vertices. -/
def IsConnTwoRegularFour (ends : E → Fin n × Fin n) (C : Finset E) : Prop :=
  (∀ v ∈ vertsOf ends C, mdeg ends C v = 2) ∧
  (∀ u ∈ vertsOf ends C, ∀ w ∈ vertsOf ends C, (adjGraph ends (C : Set E)).Reachable u w) ∧
  4 ≤ (vertsOf ends C).card

/-- `(C, D₁, D₂, A)` is a **solution** of the apex formulation. -/
def IsApexSolution (ends : E → Fin n × Fin n) (C D₁ D₂ : Finset E) (A : Finset (Fin n)) : Prop :=
  Disjoint C D₁ ∧ Disjoint C D₂ ∧ Disjoint D₁ D₂ ∧
  IsConnTwoRegularFour ends C ∧
  (A ⊆ vertsOf ends C ∧ A.card ≤ 4) ∧
  (apexGraph ends D₁ A).Connected ∧ (apexGraph ends D₂ A).Connected

end LabelConnected.Treewidth


