-- Prove2me | Definitions.Def_SDC_density
-- name    : SDC_density
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-23T04:13:32.802121+00:00
-- url     : https://prove2.me/theorems/90bb50fa-0b24-4e8a-b3d6-9d2ef47b593b
-- title:
--   Homomorphism counts and densities: the counting framework of the counterexample
-- statement:
--   The counting framework of the counterexample: the homomorphism count homCount F G (the number of adjacency-preserving vertex maps from F to G, as a cardinal); the homomorphism density homDensity F G (the homomorphism count normalized by the number of vertex maps); the edge count and the edge density of a host (twice the number of edges normalized by the number of ordered pairs of vertices); together with the two host families used as calibration anchors - the star starGraph t and the complete bipartite graph completeBipartite a b.
-- source:
--   Uploaded manuscript A finite counterexample to Sidorenko conjecture (SidorenkoCounterexample.lean.txt), namespace OAI.SidorenkoCounterexample: the homomorphism counting and density definitions are taken verbatim from the manuscript and re-namespaced to SDC, with the edge-set cardinality of a host named as edgeCard; the host families starGraph and completeBipartite are mission-authored, in the manuscript pattern-graph construction style.

import Mathlib
import Definitions.Def_SDC_graphs

/-!
# Homomorphism counts and densities for the Sidorenko counterexample

The framework layer of the SDC mission: the homomorphism counting and
density definitions of the uploaded manuscript A finite counterexample to
Sidorenko conjecture (the uploaded file SidorenkoCounterexample.lean.txt,
namespace OAI.SidorenkoCounterexample), re-namespaced to SDC: the
homomorphism count homCount F G (the number of adjacency-preserving vertex
maps from F to G, as a cardinal), the homomorphism density homDensity F G
(normalized by the number of vertex maps), the edge count and edge density
of a host, together with the two host families used as calibration
anchors: the star starGraph t and the complete bipartite graph
completeBipartite a b.

The density definitions are taken verbatim from the manuscript, with the
edge-set cardinality of a host named as edgeCard (definitionally the
manuscript expression). The host families are mission-authored, in the
manuscript pattern-graph construction style.
-/

namespace SDC

/-- The number of graph homomorphisms from F to G, as a cardinal: the
number of maps of vertices that preserve adjacency. -/
noncomputable def homCount {V W : Type*} (F : SimpleGraph V) (G : SimpleGraph W) : ℕ :=
  Nat.card {hom : V → W // ∀ left right, F.Adj left right → G.Adj (hom left) (hom right)}

/-- The homomorphism density of F in G: the number of homomorphisms from
F to G, normalized by the number of vertex maps. -/
noncomputable def homDensity {V W : Type*} (F : SimpleGraph V) (G : SimpleGraph W) : ℝ :=
  (homCount F G : ℝ) / (Nat.card W : ℝ) ^ Nat.card V

/-- The number of edges of G. -/
noncomputable def edgeCard {W : Type*} (G : SimpleGraph W) : ℕ := Nat.card G.edgeSet

/-- The edge density of G: twice the number of edges, normalized by the
number of ordered pairs of vertices. -/
noncomputable def edgeDensity {W : Type*} (G : SimpleGraph W) : ℝ :=
  2 * (edgeCard G : ℝ) / (Nat.card W : ℝ) ^ 2

/-- Adjacency of the star with t leaves: the center (on the left) is
adjacent to every leaf (on the right) and to nothing else. -/
def starAdj (t : ℕ) : Fin 1 ⊕ Fin t → Fin 1 ⊕ Fin t → Prop
  | Sum.inl _, Sum.inr _ => True
  | Sum.inr _, Sum.inl _ => True
  | _, _ => False

/-- The star with t leaves: one center vertex and t leaves. -/
def starGraph (t : ℕ) : SimpleGraph (Fin 1 ⊕ Fin t) where
  Adj := starAdj t
  symm.symm := by intro left right; cases left <;> cases right <;> simp [starAdj]
  loopless.irrefl := by intro vertex; cases vertex <;> simp [starAdj]

/-- Adjacency of the complete bipartite graph: the two parts (on the left
and on the right) span all cross edges and no others. -/
def cbAdj (a b : ℕ) : Fin a ⊕ Fin b → Fin a ⊕ Fin b → Prop
  | Sum.inl _, Sum.inr _ => True
  | Sum.inr _, Sum.inl _ => True
  | _, _ => False

/-- The complete bipartite graph with parts of sizes a and b. -/
def completeBipartite (a b : ℕ) : SimpleGraph (Fin a ⊕ Fin b) where
  Adj := cbAdj a b
  symm.symm := by intro left right; cases left <;> cases right <;> simp [cbAdj]
  loopless.irrefl := by intro vertex; cases vertex <;> simp [cbAdj]

end SDC


