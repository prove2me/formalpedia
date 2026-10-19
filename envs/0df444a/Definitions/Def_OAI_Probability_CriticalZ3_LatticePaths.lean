-- Prove2me | Definitions.Def_OAI_Probability_CriticalZ3_LatticePaths
-- name    : OAI_Probability_CriticalZ3_LatticePaths
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T18:00:54.502161+00:00
-- url     : https://prove2.me/theorems/022982cb-cb6e-4bfd-a123-0f23b884b4c8
-- title:
--   A uniform interface for bond and site percolation
-- statement:
--   A single formalism covering both percolation models on finite lattice graphs.
--
--   1. **Models.** The model is bond or site; its bits are bonds or vertices respectively, and a configuration assigns a boolean to each bit. A box's bits are its bonds or its vertices.
--   2. **Open vertices and adjacency.** In the bond model every vertex counts as open and adjacency uses an open bond. In the site model a vertex is open if its bit is $1$, and adjacency requires a graph edge between two open vertices.
--   3. **Connections.** Connection is bond-connectivity or site-connectivity, and a vertex meets $T$ if it is connected to a vertex of $T$:
--   $$
--   o\leadsto T\iff\exists y\in T:\ o\leftrightarrow y .
--   $$
--   4. **Boxes inside graphs.** A lattice graph contains a box if it contains all of its vertices and bonds; then every lattice point of the box is a vertex of the graph, and nearest neighbours are joined by some bond.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/LatticePaths.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/LatticePaths.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the CriticalZ3 mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder
import Definitions.Def_OAI_Probability_CriticalZ3_Symmetry
import Definitions.Def_OAI_Probability_CriticalZ3_QuarterFaces
import Definitions.Def_OAI_Probability_CriticalZ3_Resampling
import Definitions.Def_OAI_Probability_CriticalZ3_HyperedgeComparison
import Definitions.Def_OAI_Probability_CriticalZ3_LatticeGraph
import Definitions.Def_OAI_Probability_CriticalZ3_BoxGeometry

namespace OAI

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical Filter
open _root_.MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3
open Classical

inductive Model | bond | site

namespace Model
abbrev Bit : Model → Type
  | bond => Bond
  | site => Vertex
abbrev Config (m : Model) := m.Bit → Bool
instance (m : Model) : Countable m.Bit := by cases m <;> infer_instance
instance (m : Model) : DecidableEq m.Bit := by cases m <;> infer_instance
end Model

namespace Box
noncomputable def bits (B : Box) : (m : Model) → Finset m.Bit
  | .bond => B.bonds
  | .site => B.vertices
end Box

namespace LatticeGraph
variable (G : LatticeGraph)
noncomputable def bits : (m : Model) → Finset m.Bit
  | .bond => G.edges
  | .site => G.vertices

def Open : (m : Model) → m.Config → G.Node → Prop
  | .bond,_,_ => True
  | .site,ω,x => ω x.1 = true

def Adj : (m : Model) → m.Config → G.Node → G.Node → Prop
  | .bond,ω,x,y => G.BondAdj ω x y
  | .site,ω,x,y => G.graph.Adj x y ∧ ω x.1 = true ∧ ω y.1 = true

def Conn : (m : Model) → m.Config → G.Node → G.Node → Prop
  | .bond,ω,x,y => G.BondConn ω x y
  | .site,ω,x,y => G.SiteConn ω x y

def Meets (m : Model) (ω : m.Config) (o : G.Node) (T : Set Vertex) : Prop :=
  ∃ y : G.Node, y.1 ∈ T ∧ G.Conn m ω o y

def ContainsBox (B : Box) : Prop := B.vertices ⊆ G.vertices ∧ B.bonds ⊆ G.edges

theorem containsBox_node {B : Box} (h : G.ContainsBox B) {x : Vertex}
    (hx : B.Contains x) : x ∈ G.vertices := h.1 ((B.mem_vertices x).mpr hx)

theorem neighbor_incidence {x y : Vertex} (h : NearestNeighbor x y) :
    ∃ e : Bond, Incidence e x y := by
  obtain ⟨i,h | h⟩ := h
  · exact ⟨(x,i),Or.inl ⟨rfl,h⟩⟩
  · exact ⟨(y,i),Or.inr ⟨rfl,h⟩⟩

end LatticeGraph
end CriticalZ3

end OAI


