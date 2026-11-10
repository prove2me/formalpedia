-- Prove2me | Definitions.Def_CountOrderings_NFree_EdgePoset
-- name    : CountOrderings_NFree_EdgePoset
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T22:56:25.154697+00:00
-- url     : https://prove2.me/theorems/92b88aa4-050b-467d-9b20-432e407a6c5e
-- title:
--   Finite directed acyclic graphs and their edge posets
-- statement:
--   A **directed graph with finitely many edges** $G$ has a set of vertices $V$, a finite set of edges $E$, and for each edge $e$ a tail $\mathrm{src}(e) \in V$ and a head $\mathrm{tgt}(e) \in V$ (parallel edges and loops are allowed). An edge $f$ **directly follows** $e$ if $\mathrm{tgt}(e) = \mathrm{src}(f)$. $G$ is **acyclic** (a DAG) if no nonempty sequence of edges, each directly following the previous one, starts and ends with the same edge.
--
--   The **edge poset** $P(G)$ of a finite DAG $G$ has the edges of $G$ as elements, ordered by
--   $$e \preceq f \iff e = f \text{ or there is a directed path whose first edge is } e \text{ and whose last edge is } f .$$
--   Equivalently, every edge entering a vertex precedes every edge leaving it, and $\preceq$ is the transitive closure of this rule. Acyclicity makes $\preceq$ antisymmetric, so $P(G)$ is a finite poset.
--
--   **Formalization Note.** The vertex type may contain infinitely many isolated vertices; only the edge type must be finite. Restricting to endpoints of edges gives the same edge poset, so this includes every finite DAG of the source. The file also contains the elementary fact that a graph is acyclic as soon as some natural-number rank on edges strictly increases from every edge to every edge directly following it; it is used to certify that the graphs of §6 are acyclic.
-- source:
--   Arenas, Schild and Subercaseaux, Hardness of Counting Orderings: Taking Gadget Amplification to the Limit, STOC 2027 submission, p. 16 (PDF p. 17), §6 (edge poset of a directed acyclic graph)

import Mathlib

namespace CountOrderings.NFree

/-- A **finite directed graph** (parallel edges and loops allowed): a vertex type `V`, a finite
edge type `E`, and for every edge its tail `src` and head `tgt`. -/
structure FinDigraph where
  V : Type
  E : Type
  [fintypeE : Fintype E]
  [decEqE : DecidableEq E]
  src : E → V
  tgt : E → V

attribute [instance] FinDigraph.fintypeE FinDigraph.decEqE

/-- Edge `f` directly follows edge `e`: `f` leaves the vertex that `e` enters. -/
def FinDigraph.Follows (G : FinDigraph) (e f : G.E) : Prop := G.tgt e = G.src f

/-- `G` is **acyclic** (a DAG): no nonempty sequence of consecutive edges returns to its first
edge, i.e. there is no directed cycle. -/
def FinDigraph.IsAcyclic (G : FinDigraph) : Prop :=
  ∀ e : G.E, ¬ Relation.TransGen G.Follows e e

/-- A **finite directed acyclic graph**. -/
structure FinDAG extends FinDigraph where
  acyclic : toFinDigraph.IsAcyclic

/-- The order of the **edge poset**: `e ⪯ f` iff `e = f` or there is a directed path whose first
edge is `e` and whose last edge is `f`. -/
def FinDAG.EdgeLE (G : FinDAG) (e f : G.E) : Prop :=
  Relation.ReflTransGen G.Follows e f

/-- The **edge poset** `P(G)` of a finite DAG `G`: its elements are the edges of `G`, ordered by
`FinDAG.EdgeLE` (so every edge entering a vertex precedes every edge leaving it, transitively). -/
def EdgePoset (G : FinDAG) : Type := G.E

instance (G : FinDAG) : Fintype (EdgePoset G) := inferInstanceAs (Fintype G.E)

instance (G : FinDAG) : DecidableEq (EdgePoset G) := inferInstanceAs (DecidableEq G.E)

instance (G : FinDAG) : PartialOrder (EdgePoset G) where
  le := G.EdgeLE
  le_refl _ := Relation.ReflTransGen.refl
  le_trans _ _ _ := Relation.ReflTransGen.trans
  le_antisymm e f hef hfe := by
    rcases Relation.reflTransGen_iff_eq_or_transGen.mp hef with h | h
    · exact h.symm
    · exact absurd (h.trans_left hfe) (G.acyclic e)

/-- A graph is acyclic as soon as some rank on edges strictly increases from each edge to every
edge that directly follows it. -/
theorem FinDigraph.isAcyclic_of_rank (G : FinDigraph) (rk : G.E → ℕ)
    (hrk : ∀ e f, G.Follows e f → rk e < rk f) : G.IsAcyclic := by
  intro e he
  have key : ∀ a b, Relation.TransGen G.Follows a b → rk a < rk b := by
    intro a b hab
    induction hab with
    | single h => exact hrk _ _ h
    | tail _ h ih => exact lt_trans ih (hrk _ _ h)
  exact lt_irrefl _ (key e e he)

end CountOrderings.NFree


