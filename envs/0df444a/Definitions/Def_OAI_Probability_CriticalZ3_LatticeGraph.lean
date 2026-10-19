-- Prove2me | Definitions.Def_OAI_Probability_CriticalZ3_LatticeGraph
-- name    : OAI_Probability_CriticalZ3_LatticeGraph
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T17:57:31.951472+00:00
-- url     : https://prove2.me/theorems/1aef9047-3f60-48bd-983d-2c203dec4ad3
-- title:
--   Finite subgraphs of the cubic lattice
-- statement:
--   Finite pieces of $\mathbb Z^3$ with bond and site percolation on them.
--
--   1. **Incidence.** A bond $(x,i)$ joins $x$ and $x+e_i$; incidence is symmetric and its endpoints are distinct since $x+e_i\ne x$.
--   2. **Lattice graphs.** A finite lattice graph consists of finitely many vertices and bonds whose endpoints are among the vertices. It yields a simple graph on its vertices and a hypergraph with one two-element hyperedge per bond.
--   3. **Connections.** For a bond configuration, $x$ and $y$ are bond-connected if joined by a path of open bonds of the graph. For a site configuration, they are site-connected if joined by a path of open vertices starting at an open vertex:
--   $$
--   x=v_0\sim v_1\sim\cdots\sim v_k=y,\qquad v_j\ \text{open}.
--   $$
--   A vertex meets a set $T$ if it is connected to some vertex of $T$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/LatticeGraph.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/LatticeGraph.lean by skeleton subtraction
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

namespace OAI

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical Filter
open _root_.MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3
-- [generator] trimmed: open Classical MeasureTheory ProbabilityTheory
open Classical _root_.MeasureTheory ProbabilityTheory

/-- An unoriented nearest-neighbor bond, in its unique positive-axis indexing. -/
def Incidence (e : Bond) (x y : Vertex) : Prop :=
  (x = e.1 ∧ y = step e.1 e.2) ∨ (y = e.1 ∧ x = step e.1 e.2)

theorem step_ne (x : Vertex) (i : Fin 3) : step x i ≠ x := by
  intro h
  have := congrFun h i
  simp [step] at this

theorem incidence_symm {e : Bond} {x y : Vertex} (h : Incidence e x y) :
    Incidence e y x := h.symm

theorem incidence_ne {e : Bond} {x y : Vertex} (h : Incidence e x y) : x ≠ y := by
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact (step_ne _ _).symm
  · exact step_ne _ _

structure LatticeGraph where
  vertices : Finset Vertex
  edges : Finset Bond
  left_mem : ∀ e ∈ edges, e.1 ∈ vertices
  right_mem : ∀ e ∈ edges, step e.1 e.2 ∈ vertices

namespace LatticeGraph
variable (G : LatticeGraph)

abbrev Node := G.vertices

noncomputable def graph : SimpleGraph G.Node where
  Adj x y := ∃ e ∈ G.edges, Incidence e x y
  symm := ⟨by rintro x y ⟨e,he,h⟩; exact ⟨e,he,incidence_symm h⟩⟩
  loopless := ⟨by rintro x ⟨e,_,h⟩; exact incidence_ne h rfl⟩

noncomputable def hypergraph : HyperedgeComparison.Hypergraph G.Node G.edges :=
  fun e x => x.1 = e.1.1 ∨ x.1 = step e.1.1 e.1.2

def BondAdj (ω : BondConfig) (x y : G.Node) : Prop :=
  ∃ e ∈ G.edges, Incidence e x y ∧ ω e = true

def BondConn (ω : BondConfig) (x y : G.Node) : Prop :=
  Relation.ReflTransGen (G.BondAdj ω) x y

def SiteConn (ω : SiteConfig) (x y : G.Node) : Prop :=
  HyperedgeComparison.Site.Connected G.graph (fun z => ω z.1) x y

def BondMeets (ω : BondConfig) (o : G.Node) (T : Set Vertex) : Prop :=
  ∃ y : G.Node, y.1 ∈ T ∧ G.BondConn ω o y

def SiteMeets (ω : SiteConfig) (o : G.Node) (T : Set Vertex) : Prop :=
  ∃ y : G.Node, y.1 ∈ T ∧ G.SiteConn ω o y

end LatticeGraph
end CriticalZ3

end OAI


