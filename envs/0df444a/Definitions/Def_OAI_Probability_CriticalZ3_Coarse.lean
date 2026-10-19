-- Prove2me | Definitions.Def_OAI_Probability_CriticalZ3_Coarse
-- name    : OAI_Probability_CriticalZ3_Coarse
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T18:30:16.595458+00:00
-- url     : https://prove2.me/theorems/8b11671c-365f-4357-a946-09fe7314439b
-- title:
--   Coarse-grained blocks of the cubic lattice indexed by planar cells
-- statement:
--   A coarse-graining of a slab of $\mathbb Z^3$ by planar cells $v\in\mathbb Z^2$ at scale $r$.
--
--   1. **Blocks.** The centre of $v$ is $\bigl((20r+1)v_1,(20r+1)v_2,0\bigr)$; $Q_r(v)$ is the cube of radius $10r$ and $B_r(v)$ the cube of radius $4r$ around it. Neighbouring blocks $Q_r(v)$ and $Q_r(w)$ are joined by the interface bonds with one endpoint in each.
--   2. **Frames.** For a direction $d$, a signed symmetry maps the origin to the centre of $v$ and the relay endpoint $(20r+1,0,0)$ to the centre of the neighbour $v+$outward$(d)$.
--   3. **Graphs and bits.** A lattice graph is a subgraph of another if its vertices and bonds are included; a box gives a lattice graph. The bits of a block are those of $Q_r(v)$ plus the interface to its parent (bond model). The root bits and the bits exposed by a set $D$ of processed cells are unions of these.
--   4. **Extension.** A lattice graph containing $Q_r(v)$ is extended by $Q_r(x)$ and the interface. The extension contains $Q_r(x)$ and contains the old graph as a subgraph.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/Coarse.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/Coarse.lean by skeleton subtraction
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
import Definitions.Def_OAI_Probability_CriticalZ3_LatticePaths
import Definitions.Def_OAI_Probability_CriticalZ3_EntryLayers
import Definitions.Def_OAI_Probability_CriticalZ3_SeedTrials
import Definitions.Def_OAI_Probability_CriticalZ3_Conditioning
import Definitions.Def_OAI_Probability_CriticalZ3_ConditionalQuality
import Definitions.Def_OAI_Probability_CriticalZ3_TrialCounts
import Definitions.Def_OAI_Probability_CriticalZ3_ShellProbability
import Definitions.Def_OAI_Probability_CriticalZ3_SeedQuality
import Definitions.Def_OAI_Probability_CriticalZ3_Scales
import Definitions.Def_OAI_Probability_CriticalZ3_Relay
import Definitions.Def_OAI_Probability_CriticalZ3_RelayProbability
import Definitions.Def_OAI_Probability_CriticalZ3_FiniteTrails
import Definitions.Def_OAI_Probability_CriticalZ3_PlanarBoundary
import Definitions.Def_OAI_Probability_CriticalZ3_Matching
import Definitions.Def_OAI_Probability_CriticalZ3_Peierls

namespace OAI

-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology Function
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology Function

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3
-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
namespace Coarse
abbrev Point := PlanarBoundary.Point
abbrev Direction := PlanarBoundary.Direction
abbrev outward := PlanarBoundary.outward

def center (r : ℕ) (v : Point) : Vertex := ![(20*(r:ℤ)+1)*v.1,(20*(r:ℤ)+1)*v.2,0]
def Q (r : ℕ) (v : Point) : Box := Box.cube (center r v) (10*r)
def B (r : ℕ) (v : Point) : Box := Box.cube (center r v) (4*r)
def PairRegion (r : ℕ) (v x : Point) : Set Vertex := {y | (Q r v).Contains y ∨ (Q r x).Contains y}

@[simp] theorem center_zero (r : ℕ) : center r 0 = 0 := by ext i; fin_cases i <;> simp [center]

theorem zero_in_Q (r : ℕ) : (Q r 0).Contains 0 := by
  rw [Q,center_zero]
  exact Box.center_mem_cube _ _

noncomputable def interface (r : ℕ) (v w : Point) : Finset Bond :=
  (((Q r v).vertices ∪ (Q r w).vertices) ×ˢ Finset.univ).filter
    (fun e => ((Q r v).Contains e.1 ∧ (Q r w).Contains (step e.1 e.2)) ∨
      ((Q r w).Contains e.1 ∧ (Q r v).Contains (step e.1 e.2)))

@[simp] theorem mem_interface (r : ℕ) (v w : Point) (e : Bond) : e ∈ interface r v w ↔
    ((Q r v).Contains e.1 ∧ (Q r w).Contains (step e.1 e.2)) ∨
      ((Q r w).Contains e.1 ∧ (Q r v).Contains (step e.1 e.2)) := by
  simp only [interface,Finset.mem_filter,Finset.mem_product,Finset.mem_union,
    Box.mem_vertices,Finset.mem_univ,and_true]
  exact ⟨fun h => h.2,fun h => ⟨h.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1),h⟩⟩

def frame (r : ℕ) (v : Point) (d : Direction) : SignedSymmetry where
  perm := if d = 0 ∨ d = 2 then Equiv.swap 0 1 else Equiv.refl _
  signs := fun i => if d = 0 then decide (i ≠ 1) else if d = 3 then decide (i ≠ 0) else true
  shift := center r v

@[simp] theorem frame_zero (r : ℕ) (v : Point) (d : Direction) : (frame r v d).vertex 0 = center r v := by
  ext i
  simp [frame,SignedSymmetry.vertex]

@[simp] theorem frame_next (r : ℕ) (v : Point) (d : Direction) :
    (frame r v d).vertex (LatticeRelay.axisCenter (20*(r:ℤ)+1)) = center r (v+outward d) := by
  ext i
  fin_cases d <;> fin_cases i <;> simp [frame,SignedSymmetry.vertex,LatticeRelay.axisCenter,
    center,outward,PlanarBoundary.outward,Equiv.swap_apply_def] <;> ring

end Coarse
end CriticalZ3

namespace CriticalZ3
-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
namespace LatticeGraph

def Subgraph (G H : LatticeGraph) : Prop := G.vertices ⊆ H.vertices ∧ G.edges ⊆ H.edges

noncomputable def ofBox (B : Box) : LatticeGraph where
  vertices := B.vertices
  edges := B.bonds
  left_mem := fun _ he => (B.mem_vertices _).mpr ((B.mem_bonds _).mp he).1
  right_mem := fun _ he => (B.mem_vertices _).mpr ((B.mem_bonds _).mp he).2

@[simp] theorem ofBox_contains (B : Box) : (ofBox B).ContainsBox B := ⟨fun _ h => h,fun _ h => h⟩
end LatticeGraph

namespace Coarse
noncomputable def linkBits : (m : Model) → ℕ → Point → Point → Finset m.Bit
  | .bond,r,v,w => interface r v w
  | .site,_,_,_ => ∅
noncomputable def block (m : Model) (r : ℕ) (v parent : Point) : Finset m.Bit :=
  (Q r v).bits m ∪ linkBits m r v parent
noncomputable def rootBits (m : Model) (r : ℕ) : Finset m.Bit :=
  (Q r 0).bits m ∪ Finset.univ.biUnion (fun d : Direction => linkBits m r 0 (outward d))
noncomputable def exposed (m : Model) (r : ℕ) (D : Finset Point) : Finset m.Bit :=
  rootBits m r ∪ D.biUnion (fun v => (Q r v).bits m) ∪
    (D ×ˢ D).biUnion (fun e => linkBits m r e.1 e.2)

noncomputable def extendGraph (r : ℕ) (G : LatticeGraph) (v x : Point)
    (hv : G.ContainsBox (Q r v)) : LatticeGraph where
  vertices := G.vertices ∪ (Q r x).vertices
  edges := G.edges ∪ (Q r x).bonds ∪ interface r v x
  left_mem := by
    intro e he
    rcases Finset.mem_union.mp he with he|he
    · rcases Finset.mem_union.mp he with he|he
      · exact Finset.mem_union_left _ (G.left_mem _ he)
      · exact Finset.mem_union_right _ ((Box.mem_vertices _ _).mpr ((Box.mem_bonds _ _).mp he).1)
    · rcases (mem_interface _ _ _ _).mp he with he|he
      · exact Finset.mem_union_left _ (hv.1 ((Box.mem_vertices _ _).mpr he.1))
      · exact Finset.mem_union_right _ ((Box.mem_vertices _ _).mpr he.1)
  right_mem := by
    intro e he
    rcases Finset.mem_union.mp he with he|he
    · rcases Finset.mem_union.mp he with he|he
      · exact Finset.mem_union_left _ (G.right_mem _ he)
      · exact Finset.mem_union_right _ ((Box.mem_vertices _ _).mpr ((Box.mem_bonds _ _).mp he).2)
    · rcases (mem_interface _ _ _ _).mp he with he|he
      · exact Finset.mem_union_right _ ((Box.mem_vertices _ _).mpr he.2)
      · exact Finset.mem_union_left _ (hv.1 ((Box.mem_vertices _ _).mpr he.2))

theorem extendGraph_subgraph (r : ℕ) (G : LatticeGraph) (v x : Point)
    (hv : G.ContainsBox (Q r v)) : G.Subgraph (extendGraph r G v x hv) :=
  ⟨Finset.subset_union_left,fun _ h => Finset.mem_union_left _ (Finset.mem_union_left _ h)⟩

theorem extendGraph_contains (r : ℕ) (G : LatticeGraph) (v x : Point)
    (hv : G.ContainsBox (Q r v)) : (extendGraph r G v x hv).ContainsBox (Q r x) :=
  ⟨Finset.subset_union_right,fun _ h => Finset.mem_union_left _ (Finset.mem_union_right _ h)⟩

end Coarse
end CriticalZ3

end OAI


