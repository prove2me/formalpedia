-- Prove2me | Definitions.Def_TwoConnSS_partGraph
-- name    : TwoConnSS_partGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:47:15.98207+00:00
-- url     : https://prove2.me/theorems/7a561d9b-75c1-47c5-889a-479d224fd9ac
-- title:
--   The parts $Q(S,M)$ and the auxiliary component graph $\hat G_S$
-- statement:
--   Let $(S, M)$ be a weak 2-edge-cover with a pairing. The **parts** $Q(S, M)$ are the components of $S$ with at least two vertices, the unpaired singletons, and the pairs of $M$; they partition $V$. The multigraph $\hat G_S$ is obtained from $G$ by identifying each part, deleting loops and keeping parallel edges.
--
--   The mission uses:
--   1. the underlying simple graph of $\hat G_S$ (two parts adjacent when an edge of $G$ joins them);
--   2. `HasLongPartCycle`: $\hat G_S$ has a cycle through at least $q$ parts;
--   3. `SharePartBlock`: two parts lie in one 2VC block of $\hat G_S$, i.e. a cycle of $\hat G_S$ passes through both (a cycle of the simple graph, or two parallel edges between them).
-- source:
--   A. Jabal Ameli, Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning Subgraphs, STOC 2027 submission (manuscript sha256 22d0f2a8…2ae6a), §8.1.1, p.33; §6, p.24

import Mathlib
import Definitions.Def_TwoConnSS_IsCanonA

namespace TwoConnSS

open Classical

variable {V : Type*} [Fintype V]

/-- The vertex set `{u, v}` of a pair `m = {u, v}`. -/
noncomputable def pairSet (m : Sym2 V) : Finset V :=
  Finset.univ.filter fun v => v ∈ m

/-- The parts `Q(S, M)` (p.33): "the nontrivial connected components of S, the unpaired singletons,
and the pairs in M. These objects partition V(G)." -/
noncomputable def parts (S M : Finset (Sym2 V)) : Finset (Finset V) :=
  (comps S).filter (fun C => 2 ≤ C.card) ∪ (unpaired S M).image (fun v => {v}) ∪ M.image pairSet

/-- **The underlying simple graph of the auxiliary component multigraph `Ĝ_S`.**
Jabal Ameli, *Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning
Subgraphs*, STOC 2027 submission (manuscript sha256 22d0f2a8…), §8.1.1, p.33: "Write Ĝ_S = Ĝ_{S,M}
for the multigraph obtained from G by identifying each member of this partition, deleting loops, and
retaining parallel edges." Two distinct parts are adjacent when some edge of `G` joins them.

Also defined here: `pairSet` and the parts `Q(S, M)`.

**Formalization Note.** The vertex type is `Finset V`; only parts have neighbours. Parallel edges
of `Ĝ_S` matter only for two-vertex blocks, which `SharePartBlock` counts directly. -/
def partGraph (G : SimpleGraph V) (S M : Finset (Sym2 V)) : SimpleGraph (Finset V) where
  Adj P Q := P ∈ parts S M ∧ Q ∈ parts S M ∧ P ≠ Q ∧ ∃ u ∈ P, ∃ v ∈ Q, G.Adj u v
  symm := ⟨fun _ _ h => ⟨h.2.1, h.1, h.2.2.1.symm,
    let ⟨u, hu, v, hv, huv⟩ := h.2.2.2; ⟨v, hv, u, hu, huv.symm⟩⟩⟩
  loopless := ⟨fun _ h => h.2.2.1 rfl⟩

/-- `Ĝ_S` has a cycle through at least `q` vertices (a long cycle, p.56: "a long cycle has at
least q vertices"). -/
def HasLongPartCycle (G : SimpleGraph V) (S M : Finset (Sym2 V)) (q : ℕ) : Prop :=
  ∃ (P : Finset V) (w : (partGraph G S M).Walk P P), w.IsCycle ∧ q ≤ w.length

/-- Two parts `P ≠ Q` lie in one 2VC block of the multigraph `Ĝ_S` (p.24: "A 2VC block of GS is a
maximal 2VC subgraph of this multigraph; we also allow a two-vertex block containing parallel
edges"): some cycle of `Ĝ_S` passes through both, either a cycle of the underlying simple graph or
two parallel edges between `P` and `Q`. -/
def SharePartBlock (G : SimpleGraph V) (S M : Finset (Sym2 V)) (P Q : Finset V) : Prop :=
  (∃ (R : Finset V) (w : (partGraph G S M).Walk R R), w.IsCycle ∧ P ∈ w.support ∧ Q ∈ w.support) ∨
  (P ∈ parts S M ∧ Q ∈ parts S M ∧ P ≠ Q ∧
    2 ≤ (Finset.univ.filter fun x : V × V => x.1 ∈ P ∧ x.2 ∈ Q ∧ G.Adj x.1 x.2).card)

end TwoConnSS


