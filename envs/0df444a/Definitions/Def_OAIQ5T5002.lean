-- Prove2me | Definitions.Def_OAIQ5T5002
-- name    : OAIQ5T5002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T12:00:13.354481+00:00
-- url     : https://prove2.me/theorems/8249aa12-0cb2-47fc-b24d-c168ab92b72c
-- title:
--   Definitions bundle OAIQ5T5002 of the split of OpenAI, Planar Graph Metrics Embed into L1 with Constant Distortion
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PlanarL1.planar_graph_metrics_embed_L1`, carved from OpenAI's openai/math development (OpenAI, *Planar Graph Metrics Embed into L1 with Constant Distortion*, OpenAI Math Release, September 23, 2026, result family 89, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 87 declarations of OpenAI's Lean: 57 definitions, 1 inductive type or structure, 2 instances and 27 theorems. The definitions and types are `OAI.PlanarL1.Topology.Drawing.Split.arc`, `OAI.PlanarL1.Topology.Drawing.Split.drawing`, `OAI.PlanarL1.Topology.Drawing.Split.flip`, `OAI.PlanarL1.Topology.Drawing.Split.graph`, `OAI.PlanarL1.Topology.Drawing.Split.param`, `OAI.PlanarL1.Topology.Drawing.Split.piecePath`, `OAI.PlanarL1.Topology.Drawing.edgeRegion`, `OAI.PlanarL1.Topology.Drawing.forbidden`, `OAI.PlanarL1.Topology.Drawing.head`, `OAI.PlanarL1.Topology.Drawing.middleObstacle`, `OAI.PlanarL1.Topology.Drawing.port`, `OAI.PlanarL1.Topology.Drawing.portVertex`, `OAI.PlanarL1.Topology.Drawing.pullback`, `OAI.PlanarL1.Topology.ExteriorPorts.retarget`, `OAI.PlanarL1.Topology.ExteriorPorts.update`, `OAI.PlanarL1.Topology.ExteriorPorts.updatedRegion`, `OAI.PlanarL1.Topology.PLDrawing.Incident`, `OAI.PlanarL1.Topology.PLDrawing.PortMove`, `OAI.PlanarL1.Topology.PLDrawing.affine`, `OAI.PlanarL1.Topology.PLDrawing.expandedPoint`, `OAI.PlanarL1.Topology.PLDrawing.expandedRegion`, `OAI.PlanarL1.Topology.PLDrawing.movedPoint`, `OAI.PlanarL1.Topology.PLDrawing.movedRegion`, `OAI.PlanarL1.Topology.PLDrawing.portTail`, `OAI.PlanarL1.Topology.PLDrawing.radialPoint`, `OAI.PlanarL1.Topology.PLDrawing.radialRegion`, `OAI.PlanarL1.Topology.PLDrawing.retubePoint`, `OAI.PlanarL1.Topology.PLDrawing.retubeRegion`, `OAI.PlanarL1.Topology.PLDrawing.starPoint`, `OAI.PlanarL1.Topology.PLDrawing.starRegion`, `OAI.PlanarL1.Topology.SegmentChain.IsMinimal`, `OAI.PlanarL1.Topology.SegmentChain.affine`, `OAI.PlanarL1.Topology.SegmentChain.append`, `OAI.PlanarL1.Topology.SegmentChain.cutFirst`, `OAI.PlanarL1.Topology.SegmentChain.eraseLoop`, `OAI.PlanarL1.Topology.SegmentChain.mapSet`, `OAI.PlanarL1.Topology.SegmentChain.nil`, `OAI.PlanarL1.Topology.SegmentChain.shortcut`, `OAI.PlanarL1.Topology.SegmentChain.shortcutAt`, `OAI.PlanarL1.Topology.SegmentChain.tail` and 18 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/PlanarL1, in whole or in part: [`PlanarL1_Drawing`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/PlanarL1/PlanarL1/Drawing.lean), [`PlanarL1_Growth`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/PlanarL1/PlanarL1/Growth.lean), [`PlanarL1_HeightTree`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/PlanarL1/PlanarL1/HeightTree.lean), [`PlanarL1_Layout`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/PlanarL1/PlanarL1/Layout.lean), [`PlanarL1_PlanarMetric`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/PlanarL1/PlanarL1/PlanarMetric.lean), [`PlanarL1_Polygonal`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/PlanarL1/PlanarL1/Polygonal.lean), [`PlanarL1_Retubing`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/PlanarL1/PlanarL1/Retubing.lean), [`PlanarL1_Surgery`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/PlanarL1/PlanarL1/Surgery.lean), [`PlanarL1_WeightedMetric`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/PlanarL1/PlanarL1/WeightedMetric.lean).
--
--   **Imports.** It imports the published bundle `Def_PlanarL1`; the bundles `OAIQ5T5000` and `OAIQ5T5001` of this split.
--
--   **Imported by** (directly, in this split): the proof of `OAI.PlanarL1.planar_graph_metrics_embed_L1`.
-- source:
--   OpenAI, Planar Graph Metrics Embed into L1 with Constant Distortion, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 89; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Planar-Graph-Metrics-Embed-into-L1-with-Constant-Distortion-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/PlanarL1 at commit adc7f12

import Mathlib
import Definitions.Def_PlanarL1
import Definitions.Def_OAIQ5T5000
import Definitions.Def_OAIQ5T5001

section
-- module Solutions.OAIQ5_T5.PlanarL1_Drawing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PlanarL1.Topology
open Set Metric

namespace Drawing
variable {V : Type} {G : SimpleGraph V} (D : Drawing G)

variable [Fintype V]
/-- A compact forbidden set for a vertex disk: other vertices and the
parts of every drawn edge that must stay outside that disk. -/
def forbidden (w : V) : Set ℂ :=
  (⋃ v : {v : V // v≠w}, {D.point v.val}) ∪
    ⋃ d : G.Dart, D.edge d.fst d.snd d.adj '' excludedTimes w d

end Drawing

end PlanarL1.Topology


namespace PlanarL1.Topology
open Set Metric

namespace ForwardDart
variable {V : Type} [LinearOrder V] {G : SimpleGraph V}

instance instFintypeOfDecidableRelAdj [Fintype V] [DecidableRel G.Adj] : Fintype (ForwardDart G) :=
  inferInstanceAs (Fintype {d : G.Dart // d.fst<d.snd})
lemma eq_of_endpoints (d e : ForwardDart G)
    (h : (d.val.fst=e.val.fst ∧ d.val.snd=e.val.snd) ∨
      (d.val.fst=e.val.snd ∧ d.val.snd=e.val.fst)) : d=e := by
  rcases h with h | h
  · apply Subtype.ext
    exact SimpleGraph.Dart.ext _ _ (Prod.ext h.1 h.2)
  · have hd := d.property
    rw [h.1,h.2] at hd
    exact False.elim (not_lt_of_gt e.property hd)
end ForwardDart

namespace Drawing
variable {V : Type} {G : SimpleGraph V} (D : Drawing G)

variable [Fintype V] [LinearOrder V] {D} {r : ℝ} (T : ∀ d : ForwardDart G, D.EdgeTrim r d.val)

/-- Obstacles for the middle of an edge: all vertices and the radial heads
of every other unoriented edge. -/
noncomputable def middleObstacle (d : ForwardDart G) : Set ℂ :=
  Set.range D.point ∪ ⋃ e : {e : ForwardDart G // e≠d},
    (segment ℝ (D.point e.val.val.fst)
      (D.edge e.val.val.fst e.val.val.snd e.val.val.adj (T e.val).first)) ∪
    (segment ℝ (D.point e.val.val.snd)
      (D.edge e.val.val.fst e.val.val.snd e.val.val.adj (T e.val).last))

end Drawing
end PlanarL1.Topology



end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_WeightedMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! ## Shortest-path spanning tree . -/

namespace PlanarL1.Weighted
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] {G : SimpleGraph V} {l : V → V → ℝ}

noncomputable def shortestParents (hc : G.Connected) (hs : ∀ u v, l u v=l v u)
    (hl : ∀ u v, G.Adj u v → 0<l u v) (o : V) : DescendingParents V where
  root := o
  height := graphDistance G l o
  parent v := if hv : v=o then o else (exists_predecessor hc hs hl o v hv).choose
  at_root := by simp
  descent v hv := by
    rw [dite_eq_right hv]
    exact (exists_predecessor hc hs hl o v hv).choose_spec.2.2

end PlanarL1.Weighted



end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_HeightTree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section



namespace PlanarL1.Weighted
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] {G : SimpleGraph V} {l : V → V → ℝ}

/-- Each orientation is one distinct new branch incidence. Paired incidences
are not identified until the column switch is installed. -/
def ExtraDart (hc : G.Connected) (hs : ∀ u v, l u v=l v u)
    (hl : ∀ u v, G.Adj u v → 0<l u v) (o : V) :=
  {d : G.Dart // ¬ (shortestParents hc hs hl o).graph.Adj d.fst d.snd}

namespace ExtraDart
variable (hc : G.Connected) (hs : ∀ u v, l u v=l v u)
  (hl : ∀ u v, G.Adj u v → 0<l u v) (o : V)

noncomputable def reverse (d : ExtraDart hc hs hl o) : ExtraDart hc hs hl o :=
  ⟨d.val.symm,fun h => d.property h.symm⟩

lemma reverse_reverse (d : ExtraDart hc hs hl o) :
    reverse hc hs hl o (reverse hc hs hl o d)=d := by
  apply Subtype.ext
  exact SimpleGraph.Dart.symm_symm d.val

noncomputable def tipHeight (d : ExtraDart hc hs hl o) : ℝ :=
  (l d.val.fst d.val.snd + graphDistance G l o d.val.fst + graphDistance G l o d.val.snd)/2

lemma height_le_tip (d : ExtraDart hc hs hl o) :
    graphDistance G l o d.val.fst ≤ tipHeight hc hs hl o d := by
  have h := (abs_le.mp (height_edge hc hs (fun u v h => (hl u v h).le) o d.val.adj)).2
  unfold tipHeight
  linarith

end ExtraDart

namespace EnlargedTree
variable (hc : G.Connected) (hs : ∀ u v, l u v=l v u)
  (hl : ∀ u v, G.Adj u v → 0<l u v) (o : V)

abbrev Node := V ⊕ ExtraDart hc hs hl o

noncomputable def parent : Node hc hs hl o → Node hc hs hl o
  | .inl v => .inl ((shortestParents hc hs hl o).parent v)
  | .inr d => .inl d.val.fst

noncomputable def height : Node hc hs hl o → ℝ
  | .inl v => graphDistance G l o v
  | .inr d => ExtraDart.tipHeight hc hs hl o d

lemma parent_wf : WellFounded (fun u v : Node hc hs hl o =>
    v ≠ .inl o ∧ u = parent hc hs hl o v) := by
  let D := shortestParents hc hs hl o
  have ha : ∀ v : V, Acc (fun u v : Node hc hs hl o =>
      v ≠ .inl o ∧ u = parent hc hs hl o v) (.inl v) := by
    intro v
    induction v using D.wellFounded.induction with
    | h v ih =>
      constructor
      rintro u ⟨hv,rfl⟩
      exact ih (D.parent v) (D.descent v (fun he => hv (congrArg Sum.inl he)))
  constructor
  intro v
  cases v with
  | inl v => exact ha v
  | inr d =>
    constructor
    rintro u ⟨_,rfl⟩
    exact ha d.val.fst

/-- An abstract height tree, including zero-length branches. -/
noncomputable def tree : HeightTree (Node hc hs hl o) where
  root := .inl o
  parent := parent hc hs hl o
  at_root := congrArg Sum.inl (shortestParents hc hs hl o).at_root
  wf := parent_wf hc hs hl o
  height := height hc hs hl o
  height_mono := by
    intro v
    cases v with
    | inl v =>
      change (shortestParents hc hs hl o).height _ ≤ (shortestParents hc hs hl o).height v
      by_cases hv : v=o
      · subst v
        have hr : (shortestParents hc hs hl o).parent o=o := (shortestParents hc hs hl o).at_root
        rw [hr]
      · exact ((shortestParents hc hs hl o).descent v hv).le
    | inr d => exact ExtraDart.height_le_tip hc hs hl o d

/-- Graph-distance potentials extended to the two endpoints of each split
edge by their shortest distance through either of that edge's endpoints. -/
noncomputable def potential (z : V) : Node hc hs hl o → ℝ
  | .inl v => graphDistance G l z v
  | .inr d => min
      (graphDistance G l z d.val.fst + ExtraDart.tipHeight hc hs hl o d - graphDistance G l o d.val.fst)
      (graphDistance G l z d.val.snd + ExtraDart.tipHeight hc hs hl o d - graphDistance G l o d.val.snd)

end EnlargedTree
end PlanarL1.Weighted

namespace PlanarL1.Weighted
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] {G : SimpleGraph V} {l : V → V → ℝ}
  (hc : G.Connected) (hs : ∀ u v, l u v=l v u)
  (hl : ∀ u v, G.Adj u v → 0<l u v) (o : V)

noncomputable instance ExtraDart.fintype : Fintype (ExtraDart hc hs hl o) :=
  by unfold ExtraDart; exact Fintype.ofFinite _

namespace EnlargedTree
variable {hc hs hl o} {n : ℕ} (L : (tree hc hs hl o).Layout n)

/-- The leaf pairs are precisely the two incidences of each original non-tree
edge, not extra shortcuts. -/
def ExactPairs : Prop := ∀ i j, L.pair.Adj i j ↔ ∃ d : ExtraDart hc hs hl o,
  L.leaf i=Sum.inr d ∧ L.leaf j=Sum.inr (ExtraDart.reverse hc hs hl o d)

end EnlargedTree
end PlanarL1.Weighted



end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_Polygonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PlanarL1.Topology
open Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace SegmentChain
variable {S : Set E} {x y : E} {n : ℕ} (P : SegmentChain S x y n)

def nil (x : E) : SegmentChain S x x 0 where
  vertex _ := x
  start := rfl
  finish := rfl
  segment_mem i hi := False.elim (Nat.not_lt_zero i hi)

noncomputable def append {z : E} (h : segment ℝ y z ⊆ S) : SegmentChain S x z (n+1) where
  vertex k := if k≤n then P.vertex k else z
  start := by simpa using P.start
  finish := by simp
  segment_mem i hi := by
    by_cases hin : i<n
    · simpa [hin.le,show i+1≤n by omega] using P.segment_mem i hin
    · have hie : i=n := by omega
      subst i
      simpa [P.finish] using h

/-- Remove a closed loop in a segment chain. -/
noncomputable def eraseLoop (i j : ℕ) (hij : i<j) (hjn : j≤n)
    (heq : P.vertex i=P.vertex j) : SegmentChain S x y (n-j+i) where
  vertex k := if k≤ i then P.vertex k else P.vertex (k+j-i)
  start := by simpa using P.start
  finish := by
    rcases eq_or_lt_of_le hjn with rfl | hjn
    · simpa using heq.trans P.finish
    · have hle : ¬ n-j+i≤ i := by omega
      simp only [hle,ite_false]
      convert P.finish using 1
      all_goals try with_reducible_and_instances rfl
      all_goals congr 1; omega
  segment_mem k hk := by
    by_cases hki : k< i
    · simpa [hki.le,show k+1≤ i by omega] using P.segment_mem k (by omega)
    · by_cases hke : k=i
      · subst k
        simp only [le_refl,ite_true,show ¬ i+1≤ i by omega,ite_false]
        have he : i+1+j-i=j+1 := by omega
        rw [he,heq]
        exact P.segment_mem j (by omega)
      · have hgt : i<k := by omega
        simp only [show ¬ k≤ i by omega,show ¬ k+1≤ i by omega,ite_false]
        have he : k+1+j-i=(k+j-i)+1 := by omega
        rw [he]
        exact P.segment_mem (k+j-i) (by omega)

/-- Replace several successive edges by one segment already known to lie
in the permitted set. -/
noncomputable def shortcut (i j : ℕ) (hij : i<j) (hjn : j≤n)
    (hseg : segment ℝ (P.vertex i) (P.vertex j) ⊆ S) :
    SegmentChain S x y (n-j+i+1) where
  vertex k := if k≤ i then P.vertex k else P.vertex (k+j-i-1)
  start := by simpa using P.start
  finish := by
    simp only [show ¬ n-j+i+1≤ i by omega,ite_false]
    convert P.finish using 1
    all_goals try with_reducible_and_instances rfl
    all_goals congr 1; omega
  segment_mem k hk := by
    by_cases hki : k< i
    · simpa [hki.le,show k+1≤ i by omega] using P.segment_mem k (by omega)
    · by_cases hke : k=i
      · subst k
        simp only [le_refl,ite_true,show ¬ i+1≤ i by omega,ite_false]
        have he : i+1+j-i-1=j := by omega
        simpa [he] using hseg
      · have hgt : i<k := by omega
        simp only [show ¬ k≤ i by omega,show ¬ k+1≤ i by omega,ite_false]
        have he : k+1+j-i-1=(k+j-i-1)+1 := by omega
        rw [he]
        exact P.segment_mem (k+j-i-1) (by omega)

/-- Delete the part between two intersecting, nonadjacent segments. -/
noncomputable def shortcutAt (i j : ℕ) (hij : i<j) (hjn : j<n) (z : E)
    (hzi : z ∈ segment ℝ (P.vertex i) (P.vertex (i+1)))
    (hzj : z ∈ segment ℝ (P.vertex j) (P.vertex (j+1))) :
    SegmentChain S x y (n-j+i+1) where
  vertex k := if k≤ i then P.vertex k else if k=i+1 then z else P.vertex (k+j-i-1)
  start := by simpa using P.start
  finish := by
    simp only [show ¬ n-j+i+1≤ i by omega,ite_false,show n-j+i+1≠i+1 by omega]
    convert P.finish using 1
    all_goals try with_reducible_and_instances rfl
    all_goals congr 1; omega
  segment_mem k hk := by
    by_cases hki : k< i
    · simpa [hki.le,show k+1≤ i by omega] using P.segment_mem k (by omega)
    · by_cases hke : k=i
      · subst k
        simp only [le_refl,ite_true,show ¬ i+1≤ i by omega,ite_false]
        exact ((convex_segment (P.vertex i) (P.vertex (i+1))).segment_subset
          (left_mem_segment ℝ _ _) hzi).trans (P.segment_mem i (by omega))
      · by_cases hke : k=i+1
        · subst k
          simp only [show ¬ i+1≤ i by omega,show ¬ i+1+1≤ i by omega,ite_false,
            ite_true,show ¬ i+1+1=i+1 by omega]
          have he : i+1+1+j-i-1=j+1 := by omega
          simpa [he] using ((convex_segment (P.vertex j) (P.vertex (j+1))).segment_subset
            hzj (right_mem_segment ℝ _ _)).trans (P.segment_mem j hjn)
        · have hgt : i+1<k := by omega
          simp only [show ¬ k≤ i by omega,show ¬ k+1≤ i by omega,ite_false,
            show k≠i+1 by omega,show k+1≠i+1 by omega]
          have he : k+1+j-i-1=(k+j-i-1)+1 := by omega
          rw [he]
          exact P.segment_mem (k+j-i-1) (by omega)
end SegmentChain

namespace SegmentChain
variable {S : Set E} {x y : E} {n : ℕ} (P : SegmentChain S x y n)

def IsMinimal (_P : SegmentChain S x y n) : Prop :=
  ∀ m, Nonempty (SegmentChain S x y m) → n ≤ m

end SegmentChain

end PlanarL1.Topology

namespace PlanarL1.Topology
open Set Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma PolygonallyJoined.mono {S T : Set E} {x y : E}
    (h : PolygonallyJoined S x y) (hST : S ⊆ T) : PolygonallyJoined T x y := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail h hab ih => exact ih.tail (hab.trans hST)

namespace Drawing
variable {V : Type} [LinearOrder V] {G : SimpleGraph V} (D : Drawing G)
variable {r : ℝ} (T : ∀ d : ForwardDart G, D.EdgeTrim r d.val)

/-- A boundary port and its incident vertex. -/
def portVertex (d : ForwardDart G) (b : Bool) : V := if b then d.val.snd else d.val.fst
noncomputable def port (d : ForwardDart G) (b : Bool) : ℂ :=
  D.edge d.val.fst d.val.snd d.val.adj (if b then (T d).last else (T d).first)
noncomputable def head (d : ForwardDart G) (b : Bool) : Set ℂ :=
  segment ℝ (D.point (portVertex d b)) (D.port T d b)

noncomputable def edgeRegion (U : ForwardDart G → Set ℂ) (d : ForwardDart G) : Set ℂ :=
  U d ∪ (D.head T d false ∪ D.head T d true)

end Drawing
end PlanarL1.Topology

namespace PlanarL1.Topology
open Set

namespace SegmentChain
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {S T : Set E} {x y : E} {n : ℕ} (P : SegmentChain S x y n)

def mapSet (h : S ⊆ T) : SegmentChain T x y n where
  vertex := P.vertex
  start := P.start
  finish := P.finish
  segment_mem i hi := (P.segment_mem i hi).trans h

end SegmentChain

end PlanarL1.Topology


namespace PlanarL1.Topology
open Set Metric Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace PLDrawing
variable {V : Type} [LinearOrder V] {G : SimpleGraph V} (P : PLDrawing G)

def Incident (d : ForwardDart G) (v : V) : Prop := v=d.val.fst ∨ v=d.val.snd

noncomputable def expandedPoint (B : Set V) (c : ℝ) (v : V) : ℂ :=
  by classical exact if v∈B then P.point v else c•P.point v

def portTail (c : ℝ) (v : V) : Set ℂ := segment ℝ (c•P.point v) (P.point v)

def expandedRegion (B : Set V) (c : ℝ) (d : ForwardDart G) : Set ℂ :=
  (fun z : ℂ => c•z) '' (P.chain d).trace ∪
    ⋃ v : {v : V // v∈B ∧ Incident d v}, P.portTail c v.val

end PLDrawing
end PlanarL1.Topology



end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_Surgery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section



namespace PlanarL1.Topology.PLDrawing
open Set Metric Filter
variable {V : Type} [LinearOrder V] {G : SimpleGraph V}

variable (P : PLDrawing G)

noncomputable def radialPoint (B : Set V) (c : ℝ) (t : V → ℝ) (v : V) : ℂ :=
  by classical exact if v∈B then t v • P.point v else c • P.point v

def radialRegion (B : Set V) (c : ℝ) (t : V → ℝ) (d : ForwardDart G) : Set ℂ :=
  (fun z : ℂ => c•z) '' (P.chain d).trace ∪
    ⋃ v : {v : V // v∈B ∧ Incident d v}, segment ℝ (c•P.point v.val) (t v.val•P.point v.val)

end PlanarL1.Topology.PLDrawing




namespace PlanarL1.Topology
open Set Metric Filter

namespace PLDrawing
variable {V : Type} [LinearOrder V] {G : SimpleGraph V} (P : PLDrawing G)

noncomputable def movedPoint (v : V) (q : ℂ) (w : V) : ℂ :=
  by classical exact if w=v then q else P.point w

def movedRegion (v : V) (S : Set ℂ) (d : ForwardDart G) : Set ℂ :=
  (P.chain d).trace ∪ {z | Incident d v ∧ z∈S}

end PLDrawing
end PlanarL1.Topology




namespace PlanarL1.Topology
open Set

namespace PLDrawing
variable {V W : Type} [LinearOrder V] [LinearOrder W] [LinearOrder (V⊕W)] {G : SimpleGraph V}
variable (P : PLDrawing G) (v : V) (q : W → ℂ) (A : W → Set ℂ)

def starPoint : V⊕W → ℂ := Sum.elim P.point q

def starRegion : V⊕W → V⊕W → Set ℂ
  | .inl a,.inl b => P.region a b
  | .inl _,.inr w => A w
  | .inr w,.inl _ => A w
  | .inr _,.inr _ => ∅

end PLDrawing
end PlanarL1.Topology




namespace PlanarL1.Topology
open Set

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace SegmentChain
variable {S : Set E} {x y : E} {n : ℕ} (P : SegmentChain S x y n)

noncomputable def affine (f : E →ᵃ[ℝ] F) : SegmentChain (f '' S) (f x) (f y) n where
  vertex i := f (P.vertex i)
  start := congrArg f P.start
  finish := congrArg f P.finish
  segment_mem i hi := by rw [← image_segment]; exact Set.image_mono (P.segment_mem i hi)

lemma affine_trace (f : E →ᵃ[ℝ] F) : (P.affine f).trace=f '' P.trace := by
  simp only [trace,affine,Set.image_union,Set.image_singleton,Set.image_iUnion,image_segment]

lemma affine_simple (f : E →ᵃ[ℝ] F) (hf : Function.Injective f) (hP : P.IsSimple) :
    (P.affine f).IsSimple := by
  constructor
  · intro i hi j hj he; exact hP.1 hi hj (hf he)
  · intro i j hij hjn z hz hz'
    change z ∈ segment ℝ (f (P.vertex i)) (f (P.vertex (i+1))) at hz
    change z ∈ segment ℝ (f (P.vertex j)) (f (P.vertex (j+1))) at hz'
    rw [← image_segment] at hz hz'
    obtain ⟨w,hw,rfl⟩ := hz
    obtain ⟨w',hw',he⟩ := hz'
    have hwe : w'=w := hf he
    subst w'
    obtain ⟨hij',hw⟩ := hP.2 i j hij hjn w hw hw'
    exact ⟨hij',congrArg f hw⟩

end SegmentChain

namespace PLDrawing
variable {V : Type} [LinearOrder V] {G : SimpleGraph V} (P : PLDrawing G)

noncomputable def affine (f : ℂ ≃ᵃ[ℝ] ℂ) : PLDrawing G where
  point v := f (P.point v)
  point_injective := f.injective.comp P.point_injective
  count := P.count
  chain d := ((P.chain d).affine f.toAffineMap).mapSet (Set.subset_univ _)
  simple d := ((P.chain d).affine_simple f.toAffineMap f.injective (P.simple d))
  on_vertex d v hv := by
    change f (P.point v) ∈ ((P.chain d).affine f.toAffineMap).trace at hv
    rw [(P.chain d).affine_trace f.toAffineMap] at hv
    obtain ⟨w,hw,he⟩ := hv
    have he' : w=P.point v := f.injective he
    exact P.on_vertex d v (he' ▸ hw)
  intersect d e hde z hz hz' := by
    change z ∈ ((P.chain d).affine f.toAffineMap).trace at hz
    change z ∈ ((P.chain e).affine f.toAffineMap).trace at hz'
    rw [(P.chain d).affine_trace f.toAffineMap] at hz
    rw [(P.chain e).affine_trace f.toAffineMap] at hz'
    obtain ⟨w,hw,rfl⟩ := hz
    obtain ⟨w',hw',he⟩ := hz'
    have he' : w'=w := f.injective he
    subst w'
    have hi := P.intersect d e hde w hw hw'
    exact ⟨hi.1.imp (congrArg f) (congrArg f),hi.2.imp (congrArg f) (congrArg f)⟩

end PLDrawing
end PlanarL1.Topology



end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_Retubing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section



namespace PlanarL1.Topology
open Set Metric Filter

namespace PLDrawing
variable {V : Type} [LinearOrder V] {G : SimpleGraph V} (P : PLDrawing G)

noncomputable def retubePoint (B : Set V) (c : ℝ) (t : V → ℝ) (v : V) (q : ℂ) (w : V) : ℂ :=
  by classical exact if w=v then q else P.radialPoint B c t w

def retubeRegion (B : Set V) (c : ℝ) (t : V → ℝ) (v : V) (q : ℂ) (d : ForwardDart G) : Set ℂ :=
  P.radialRegion B c t d ∪ {z | Incident d v ∧ z∈segment ℝ (P.point v) q}

end PLDrawing
end PlanarL1.Topology




namespace PlanarL1.Topology
open Set Metric Filter

namespace PLDrawing
variable {V : Type} [LinearOrder V] {G : SimpleGraph V} (P : PLDrawing G)

/-- The exact geometric output needed when retubing a tree with exterior stems.
The old disk may be discarded, but no new curve leaves it except along the
selected stem segment. -/
structure PortMove (p : V → ℂ) (Q : PLDrawing G) (B : Set V) (v : V) (q : ℂ) (S T : Set ℂ) : Prop where
  selected : Q.point v=q
  point_mem : ∀ w, Q.point w∈closure T
  trace_mem : ∀ d, (Q.chain d).trace ⊆ closure T
  point_control : ∀ w, Q.point w∈closure S ∪ segment ℝ (p v) q
  trace_control : ∀ d, (Q.chain d).trace ⊆ closure S ∪ segment ℝ (p v) q
  on_frontier : ∀ w∈B, w≠v → Q.point w∈frontier T
  tail_old : ∀ w∈B, w≠v → segment ℝ (Q.point w) (p w) ⊆ closure S
  tail_frontier : ∀ w∈B, w≠v → ∀ z∈segment ℝ (Q.point w) (p w),
    z∈frontier S → z=p w
  tail_new : ∀ w∈B, w≠v → ∀ z∈segment ℝ (Q.point w) (p w),
    z∈closure T → z=Q.point w
  tails_disjoint : ∀ w∈B, w≠v → ∀ u∈B, u≠v → w≠u →
    Disjoint (segment ℝ (Q.point w) (p w)) (segment ℝ (Q.point u) (p u))

end PLDrawing
end PlanarL1.Topology




namespace PlanarL1.Topology
open Set

variable {V : Type}

namespace ExteriorPorts
variable {p target : V → ℂ} {B : Set V} {S : Set ℂ} (E : ExteriorPorts p target B S)

lemma tail_disjoint_region {a : V → ℂ} {v : V} {q : ℂ} {T : Set ℂ}
    (h : PortFrame p a B v q S T) (hinj : Function.Injective p)
    (hport : ∀ w∈B, p w∈frontier S)
    {w u : V} (hw : w∈B) (he : w≠v) (hu : u∈B) (hwu : w≠u) :
    Disjoint (segment ℝ (a w) (p w)) (E.region u) := by
  apply Set.disjoint_left.mpr
  intro z hz hz'
  have heq := E.inside u hu z hz' (h.tail_old w hw he hz)
  have heqw := h.tail_frontier w hw he z hz (heq ▸ hport u hu)
  exact hwu (hinj (heqw.symm.trans heq))

noncomputable def updatedRegion (a : V → ℂ) (v : V) (U : Set ℂ) (w : V) : Set ℂ := by
  classical exact if w=v then U else segment ℝ (a w) (p w) ∪ E.region w

/-- Replacing one residual stem, and adjoining the released radial tails to
all other stems, preserves literal disjoint exterior routes. -/
noncomputable def update {a : V → ℂ} {v : V} {q : ℂ} {T U : Set ℂ}
    (h : PortFrame p a B v q S T) (hinj : Function.Injective p)
    (hport : ∀ w∈B, p w∈frontier S) (hv : v∈B)
    (hout : ∀ w∈B, w≠v → Disjoint (closure T) (E.region w))
    (hU : IsCompact U) (hqU : q∈U) (hUsub : U ⊆ E.region v)
    (hUin : ∀ z∈U, z∈closure T → z=q)
    (hUjoin : PolygonallyJoined U q (target v)) : ExteriorPorts a target B T where
  region := E.updatedRegion a v U
  compact w hw := by
    classical
    by_cases he : w=v
    · simpa only [updatedRegion,ite_eq_left he] using hU
    · simpa only [updatedRegion,ite_eq_right he] using (compact_segment_complex _ _).union (E.compact w hw)
  start w hw := by
    classical
    by_cases he : w=v
    · subst w; simpa only [updatedRegion,ite_true,h.selected] using hqU
    · simp only [updatedRegion,ite_eq_right he]; exact Or.inl (left_mem_segment ℝ _ _)
  joined w hw := by
    classical
    by_cases he : w=v
    · subst w; simpa only [updatedRegion,ite_true,h.selected] using hUjoin
    · simp only [updatedRegion,ite_eq_right he]
      exact (Relation.ReflTransGen.single (fun z hz => Or.inl hz)).trans
        ((E.joined w hw).mono Set.subset_union_right)
  inside w hw z hz hz' := by
    classical
    by_cases he : w=v
    · subst w
      rw [h.selected]
      exact hUin z (by simpa only [updatedRegion,ite_true] using hz) hz'
    · simp only [updatedRegion,ite_eq_right he] at hz
      rcases hz with hz|hz
      · exact h.tail_new w hw he z hz hz'
      · exact False.elim (Set.disjoint_left.mp (hout w hw he) hz' hz)
  disjoint w hw u hu hwu := by
    classical
    by_cases hwv : w=v <;> by_cases huv : u=v
    · exact False.elim (hwu (hwv.trans huv.symm))
    · subst w
      simp only [updatedRegion,ite_true,ite_eq_right huv]
      apply Disjoint.union_right
      · exact (E.tail_disjoint_region h hinj hport hu huv hv huv).symm.mono_left hUsub
      · exact (E.disjoint v hv u hu hwu).mono_left hUsub
    · subst u
      simp only [updatedRegion,ite_true,ite_eq_right hwv]
      apply Disjoint.union_left
      · exact (E.tail_disjoint_region h hinj hport hw hwv hv hwv).mono_right hUsub
      · exact (E.disjoint w hw v hv hwu).mono_right hUsub
    · simp only [updatedRegion,ite_eq_right hwv,ite_eq_right huv]
      apply Disjoint.union_left
      · apply Disjoint.union_right
        · exact h.tails_disjoint w hw hwv u hu huv hwu
        · exact E.tail_disjoint_region h hinj hport hw hwv hu hwu
      · apply Disjoint.union_right
        · exact (E.tail_disjoint_region h hinj hport hu huv hw (Ne.symm hwu)).symm
        · exact E.disjoint w hw u hu hwu

end ExteriorPorts
end PlanarL1.Topology




namespace PlanarL1.Topology
open Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace SegmentChain
variable {S : Set E} {x y : E} {n : ℕ} (P : SegmentChain S x y (n+1))

noncomputable def tail : SegmentChain S (P.vertex 1) y n where
  vertex i := P.vertex (i+1)
  start := rfl
  finish := P.finish
  segment_mem i hi := P.segment_mem (i+1) (by omega)

noncomputable def cutFirst (z : E) (hz : z∈segment ℝ x (P.vertex 1)) :
    SegmentChain S z y (n+1) where
  vertex i := if i=0 then z else P.vertex i
  start := by simp
  finish := by simpa using P.finish
  segment_mem i hi := by
    by_cases he : i=0
    · subst i
      simp only [ite_true,Nat.zero_add,one_ne_zero,ite_false]
      apply (P.segment_mem 0 (by omega)).trans' -- rewrite the first endpoint
      simpa only [P.start,zero_add] using (convex_segment x (P.vertex 1)).segment_subset hz (right_mem_segment ℝ _ _)
    · simpa only [ite_eq_right he,Nat.succ_ne_zero,ite_false] using P.segment_mem i hi

end SegmentChain
end PlanarL1.Topology



end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_Growth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section




namespace PlanarL1.Topology
open Set
variable {V W : Type} [LinearOrder V] [LinearOrder W]
  {G : SimpleGraph V} {H : SimpleGraph W}

noncomputable def ExteriorPorts.retarget {p t : V → ℂ} {B : Set V} {S : Set ℂ}
    (E : ExteriorPorts p t B S) (t' : V → ℂ) (ht : ∀ w, t w=t' w) :
    ExteriorPorts p t' B S := {
  region := E.region
  compact := E.compact
  start := E.start
  joined := fun w hw => by rw [← ht w]; exact E.joined w hw
  inside := E.inside
  disjoint := E.disjoint }

end PlanarL1.Topology




namespace PlanarL1.Topology
open Set
variable {W : Type} [LinearOrder W] [Finite W] [LinearOrder (PUnit⊕W)]

noncomputable def singletonDrawing (y : ℂ) : PLDrawing (⊥ : SimpleGraph PUnit) where
  point := fun _ => y
  point_injective := fun _ _ _ => Subsingleton.elim _ _
  count := fun d => False.elim d.val.adj
  chain := fun d => False.elim d.val.adj
  simple := fun d => False.elim d.val.adj
  on_vertex := fun d => False.elim d.val.adj
  intersect := fun d => False.elim d.val.adj

end PlanarL1.Topology




end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_Layout
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section




namespace PlanarL1.Topology
open Set
variable {V : Type} [LinearOrder V] {G : SimpleGraph V} (P : PLDrawing G)
  {p : V → ℂ} {B : Set V} {D : Set ℂ} (E : ExteriorPorts p P.point B D)

/-- The untouched raw carrier together with the actual exterior stubs. -/
def stemCarrier (S : Set V) : Set ℂ := P.carrier S ∪ ⋃ v : S, E.region v.val

end PlanarL1.Topology




namespace PlanarL1.Topology.Drawing
open Set
variable {V : Type} [LinearOrder V] {G : SimpleGraph V} (D : Drawing G)

lemma forward_interior_meet (d e : ForwardDart G) {s t : unitInterval}
    (hs : 0<(s:ℝ)) (hs' : (s:ℝ)<1) (ht : 0<(t:ℝ)) (ht' : (t:ℝ)<1)
    (he : D.edge d.val.fst d.val.snd d.val.adj s=D.edge e.val.fst e.val.snd e.val.adj t) :
    d=e ∧ s=t := by
  have hd := ForwardDart.eq_of_endpoints d e (D.interior_disjoint _ _ _ _ _ _ s t hs hs' ht ht' he)
  subst e
  exact ⟨rfl,D.edge_injective _ _ _ he⟩

namespace Split
attribute [local instance] Classical.propDecidable
variable (S : Set (ForwardDart G))

lemma tipTime_pos (k : Fin 2) : 0<(tipTime k:ℝ) := by dsimp [tipTime]; positivity
lemma tipTime_lt_one (k : Fin 2) : (tipTime k:ℝ)<1 := by
  have hk : (k.val:ℝ)<2 := by exact_mod_cast k.isLt
  dsimp [tipTime]; linarith

lemma point_injective : Function.Injective (point D S) := by
  intro a b he
  cases a with
  | inl a => cases b with
    | inl b => exact congrArg Sum.inl (D.point_injective he)
    | inr b => exact False.elim (D.interior_avoid _ _ _ _ a (tipTime_pos b.2) (tipTime_lt_one b.2) he.symm)
  | inr a => cases b with
    | inl b => exact False.elim (D.interior_avoid _ _ _ _ b (tipTime_pos a.2) (tipTime_lt_one a.2) he)
    | inr b =>
      obtain ⟨hd,ht⟩ := D.forward_interior_meet a.1.val b.1.val
        (tipTime_pos a.2) (tipTime_lt_one a.2) (tipTime_pos b.2) (tipTime_lt_one b.2) he
      have hk : a.2=b.2 := by
        apply Fin.ext
        have hh := congrArg Subtype.val ht
        change ((a.2.val:ℝ)+1)/3=((b.2.val:ℝ)+1)/3 at hh
        exact_mod_cast (show (a.2.val:ℝ)=(b.2.val:ℝ) by linarith)
      exact congrArg Sum.inr (Prod.ext (Subtype.ext hd) hk)

lemma first_lt_last (p : Piece S) : (first S p:ℝ)<(last S p:ℝ) := by
  cases p with
  | inl p => exact zero_lt_one
  | inr p => dsimp [first,last,meshTime]; push_cast; linarith

lemma src_ne_dst (D : Drawing G) (p : Piece S) : src S p≠dst S p := by
  intro he
  have hp := congrArg (point D S) he
  rw [src_point,dst_point] at hp
  have ht := congrArg Subtype.val (D.edge_injective _ _ _ hp)
  exact (ne_of_lt (first_lt_last S p)) ht

lemma interior_point_avoid (p : Piece S) {t : unitInterval}
    (ht₀ : (first S p:ℝ)<(t:ℝ)) (ht₁ : (t:ℝ)<(last S p:ℝ)) (v : Node S) :
    D.edge (label S p).val.fst (label S p).val.snd (label S p).val.adj t≠point D S v := by
  have ht : 0<(t:ℝ) := lt_of_le_of_lt (first S p).property.1 ht₀
  have ht' : (t:ℝ)<1 := lt_of_lt_of_le ht₁ (last S p).property.2
  intro he
  cases v with
  | inl v => exact D.interior_avoid _ _ _ t v ht ht' he
  | inr v =>
    obtain ⟨hd,htt⟩ := D.forward_interior_meet (label S p) v.1.val ht ht'
      (tipTime_pos v.2) (tipTime_lt_one v.2) he
    cases p with
    | inl p =>
      change p.val=v.1.val at hd
      exact p.property (hd.symm ▸ v.1.property)
    | inr p =>
      rw [htt] at ht₀ ht₁
      change (p.2.val:ℝ)/3 < ((v.2.val:ℝ)+1)/3 at ht₀
      change ((v.2.val:ℝ)+1)/3 < ((p.2.val+1:ℕ):ℝ)/3 at ht₁
      have hlo : p.2.val<v.2.val+1 := by exact_mod_cast (show (p.2.val:ℝ)<(v.2.val:ℝ)+1 by linarith)
      have hhi : v.2.val+1<p.2.val+1 := by
        exact_mod_cast (show (v.2.val:ℝ)+1<(p.2.val:ℝ)+1 by push_cast at ht₁; linarith)
      omega

lemma interior_piece_unique (p q : Piece S) {s t : unitInterval}
    (hs₀ : (first S p:ℝ)<(s:ℝ)) (hs₁ : (s:ℝ)<(last S p:ℝ))
    (ht₀ : (first S q:ℝ)<(t:ℝ)) (ht₁ : (t:ℝ)<(last S q:ℝ))
    (he : D.edge (label S p).val.fst (label S p).val.snd (label S p).val.adj s=
      D.edge (label S q).val.fst (label S q).val.snd (label S q).val.adj t) : p=q := by
  obtain ⟨hd,hst⟩ := D.forward_interior_meet (label S p) (label S q)
    (lt_of_le_of_lt (first S p).property.1 hs₀) (lt_of_lt_of_le hs₁ (last S p).property.2)
    (lt_of_le_of_lt (first S q).property.1 ht₀) (lt_of_lt_of_le ht₁ (last S q).property.2) he
  subst t
  cases p with
  | inl p => cases q with
    | inl q => exact congrArg Sum.inl (Subtype.ext hd)
    | inr q =>
      change p.val=q.1.val at hd
      exact False.elim (p.property (hd.symm ▸ q.1.property))
  | inr p => cases q with
    | inl q =>
      change p.1.val=q.val at hd
      exact False.elim (q.property (hd ▸ p.1.property))
    | inr q =>
      have hk : p.2=q.2 := by
        apply Fin.ext
        change (p.2.val:ℝ)/3 < (s:ℝ) at hs₀
        change (s:ℝ)<((p.2.val+1:ℕ):ℝ)/3 at hs₁
        change (q.2.val:ℝ)/3 < (s:ℝ) at ht₀
        change (s:ℝ)<((q.2.val+1:ℕ):ℝ)/3 at ht₁
        push_cast at hs₁ ht₁
        have hpq : p.2.val<q.2.val+1 := by exact_mod_cast (show (p.2.val:ℝ)<(q.2.val:ℝ)+1 by linarith)
        have hqp : q.2.val<p.2.val+1 := by exact_mod_cast (show (q.2.val:ℝ)<(p.2.val:ℝ)+1 by linarith)
        omega
      exact congrArg Sum.inr (Prod.ext (Subtype.ext hd) hk)

end Split
end PlanarL1.Topology.Drawing



end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_PlanarMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section



namespace PlanarL1.Topology.Drawing.Split
open Set
variable {V : Type} [LinearOrder V] {G : SimpleGraph V} (D : Drawing G)
  (S : Set (ForwardDart G))

noncomputable def param (p : Piece S) (t : unitInterval) : unitInterval :=
  Icc.convexComb (first S p) (last S p) t

lemma param_injective (p : Piece S) : Function.Injective (param S p) := by
  intro a b he
  apply Subtype.ext
  have hh := congrArg Subtype.val he
  change (1-(a:ℝ))*(first S p:ℝ)+(a:ℝ)*(last S p:ℝ)=
    (1-(b:ℝ))*(first S p:ℝ)+(b:ℝ)*(last S p:ℝ) at hh
  have hp := first_lt_last S p
  nlinarith

lemma param_interior (p : Piece S) (t : unitInterval) (ht : 0<(t:ℝ)) (ht' : (t:ℝ)<1) :
    (first S p:ℝ)<(param S p t:ℝ) ∧ (param S p t:ℝ)<(last S p:ℝ) := by
  have hp := first_lt_last S p
  change (first S p:ℝ)<(1-(t:ℝ))*(first S p:ℝ)+(t:ℝ)*(last S p:ℝ) ∧
    (1-(t:ℝ))*(first S p:ℝ)+(t:ℝ)*(last S p:ℝ)<(last S p:ℝ)
  constructor <;> nlinarith

noncomputable def piecePath (p : Piece S) : Path (point D S (src S p)) (point D S (dst S p)) :=
  ((D.edge (label S p).val.fst (label S p).val.snd (label S p).val.adj).subpath
    (first S p) (last S p)).cast (src_point D S p) (dst_point D S p)

lemma piecePath_injective (p : Piece S) : Function.Injective (piecePath D S p) :=
  (D.edge_injective _ _ _).comp (param_injective S p)

def flip (d : Directed S) : Directed S := (d.1,!d.2)

lemma start_flip (d : Directed S) : start S (flip S d)=finish S d := by
  rcases d with ⟨p,(_|_)⟩ <;> rfl

lemma finish_flip (d : Directed S) : finish S (flip S d)=start S d := by
  rcases d with ⟨p,(_|_)⟩ <;> rfl

lemma start_ne_finish (D : Drawing G) (d : Directed S) : start S d≠finish S d := by
  rcases d with ⟨p,(_|_)⟩
  · exact src_ne_dst S D p
  · exact (src_ne_dst S D p).symm

noncomputable def arc (d : Directed S) : Path (point D S (start S d)) (point D S (finish S d)) :=
  if h : d.2=true then (piecePath D S d.1).symm.cast (by simp [start,h]) (by simp [finish,h])
  else (piecePath D S d.1).cast (by simp [start,h]) (by simp [finish,h])

lemma arc_injective (d : Directed S) : Function.Injective (arc D S d) := by
  rcases d with ⟨p,(_|_)⟩
  · simpa only [arc,Bool.false_eq_true,↓reduceDIte,Path.cast_coe] using piecePath_injective D S p
  · intro s t he
    have hh : piecePath D S p (unitInterval.symm s)=piecePath D S p (unitInterval.symm t) := he
    apply Subtype.ext
    have hh' := congrArg Subtype.val (piecePath_injective D S p hh)
    change 1-(s:ℝ)=1-(t:ℝ) at hh'
    linarith

lemma arc_location (d : Directed S) (t : unitInterval) (ht : 0<(t:ℝ)) (ht' : (t:ℝ)<1) :
    ∃ r : unitInterval, (first S d.1:ℝ)<(r:ℝ) ∧ (r:ℝ)<(last S d.1:ℝ) ∧
      arc D S d t=D.edge (label S d.1).val.fst (label S d.1).val.snd (label S d.1).val.adj r := by
  rcases d with ⟨p,(_|_)⟩
  · exact ⟨param S p t,(param_interior S p t ht ht').1,(param_interior S p t ht ht').2,rfl⟩
  · have hs : 0<(unitInterval.symm t:ℝ) := by change 0<1-(t:ℝ); linarith
    have hs' : (unitInterval.symm t:ℝ)<1 := by change 1-(t:ℝ)<1; linarith
    exact ⟨param S p (unitInterval.symm t),(param_interior S p _ hs hs').1,
      (param_interior S p _ hs hs').2,rfl⟩

noncomputable def graph : SimpleGraph (Node S) where
  Adj u v := ∃ d : Directed S, start S d=u ∧ finish S d=v
  symm := ⟨by
    rintro u v ⟨d,hu,hv⟩
    exact ⟨flip S d,(start_flip S d).trans hv,(finish_flip S d).trans hu⟩⟩
  loopless := ⟨by
    rintro u ⟨d,hu,hv⟩
    exact start_ne_finish S D d (hu.trans hv.symm)⟩

noncomputable def drawing : Drawing (graph D S) where
  point := point D S
  point_injective := point_injective D S
  edge u v h := (arc D S h.choose).cast (congrArg (point D S) h.choose_spec.1.symm)
    (congrArg (point D S) h.choose_spec.2.symm)
  edge_injective u v h := arc_injective D S h.choose
  interior_avoid := by
    intro u v h t w ht ht' he
    obtain ⟨r,hr,hr',heq⟩ := arc_location D S h.choose t ht ht'
    exact interior_point_avoid D S h.choose.1 hr hr' w (heq.symm.trans he)
  interior_disjoint := by
    intro u v h x y k s t hs hs' ht ht' he
    obtain ⟨r,hr,hr',heq⟩ := arc_location D S h.choose s hs hs'
    obtain ⟨q,hq,hq',heq'⟩ := arc_location D S k.choose t ht ht'
    have hp := interior_piece_unique D S h.choose.1 k.choose.1 hr hr' hq hq'
      (heq.symm.trans (he.trans heq'))
    have hu := h.choose_spec.1
    have hv := h.choose_spec.2
    have hx := k.choose_spec.1
    have hy := k.choose_spec.2
    rcases hh : h.choose with ⟨p,b⟩
    rcases hk : k.choose with ⟨p',b'⟩
    rw [hh,hk] at hp
    change p=p' at hp
    subst p'
    rw [hh] at hu hv
    rw [hk] at hx hy
    cases b <;> cases b' <;> simp only [start,finish,Bool.false_eq_true,↓reduceIte] at hu hv hx hy
    all_goals aesop

end PlanarL1.Topology.Drawing.Split




namespace PlanarL1.Topology.Drawing
variable {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W}

noncomputable def pullback (D : Drawing G) (f : W → V) (hf : Function.Injective f)
    (hG : ∀ u v, H.Adj u v → G.Adj (f u) (f v)) : Drawing H where
  point := D.point ∘ f
  point_injective := D.point_injective.comp hf
  edge u v h := D.edge (f u) (f v) (hG u v h)
  edge_injective u v h := D.edge_injective _ _ _
  interior_avoid u v h t w ht ht' := D.interior_avoid _ _ _ t (f w) ht ht'
  interior_disjoint := by
    intro u v h x y k s t hs hs' ht ht' he
    exact (D.interior_disjoint _ _ _ _ _ _ s t hs hs' ht ht' he).elim
      (fun h => Or.inl ⟨hf h.1,hf h.2⟩) (fun h => Or.inr ⟨hf h.1,hf h.2⟩)

end PlanarL1.Topology.Drawing

namespace PlanarL1.Weighted.EnlargedTree
open PlanarL1.Topology PlanarL1.Topology.Drawing
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [LinearOrder V] {G : SimpleGraph V} {l : V → V → ℝ}
  (hc : G.Connected) (hs : ∀ u v, l u v=l v u)
  (hl : ∀ u v, G.Adj u v → 0<l u v) (o : V)

def splitSet : Set (ForwardDart G) :=
  {d | ¬(shortestParents hc hs hl o).graph.Adj d.val.fst d.val.snd}

noncomputable def splitTip (d : ExtraDart hc hs hl o) : Split.Tip (splitSet hc hs hl o) :=
  if h : d.val.fst<d.val.snd then (⟨⟨d.val,h⟩,d.property⟩,0)
  else (⟨⟨d.val.symm,lt_of_le_of_ne (le_of_not_gt h) d.val.adj.ne.symm⟩,
    fun ht => d.property ht.symm⟩,1)

lemma splitTip_injective : Function.Injective (splitTip hc hs hl o) := by
  intro d e he
  by_cases hd : d.val.fst<d.val.snd <;> by_cases hh : e.val.fst<e.val.snd
  · simp only [splitTip,dite_eq_left hd,dite_eq_left hh] at he
    exact Subtype.ext (congrArg (fun t => t.1.val.val) he)
  · have hk := congrArg Prod.snd he
    simp [splitTip,hd,hh] at hk
  · have hk := congrArg Prod.snd he
    simp [splitTip,hd,hh] at hk
  · simp only [splitTip,dite_eq_right hd,dite_eq_right hh] at he
    have hh := congrArg (fun t => t.1.val.val.symm) he
    exact Subtype.ext hh

noncomputable def splitMap : Node hc hs hl o → Split.Node (splitSet hc hs hl o)
  | .inl v => .inl v
  | .inr d => .inr (splitTip hc hs hl o d)

lemma splitMap_injective : Function.Injective (splitMap hc hs hl o) := by
  intro u v he
  cases u with
  | inl u => cases v with
    | inl v => exact congrArg Sum.inl (Sum.inl.inj he)
    | inr v => exact False.elim (Sum.inl_ne_inr he)
  | inr u => cases v with
    | inl v => exact False.elim (Sum.inr_ne_inl he)
    | inr v => exact congrArg Sum.inr (splitTip_injective hc hs hl o (Sum.inr.inj he))

noncomputable def drawingGraph (D : Drawing G) : SimpleGraph (Node hc hs hl o) :=
  SimpleGraph.comap (splitMap hc hs hl o) (Split.graph D (splitSet hc hs hl o))

noncomputable def enlargedDrawing (D : Drawing G) : Drawing (drawingGraph hc hs hl o D) :=
  (Split.drawing D (splitSet hc hs hl o)).pullback (splitMap hc hs hl o)
    (splitMap_injective hc hs hl o) (fun _ _ h => h)

end PlanarL1.Weighted.EnlargedTree




namespace PlanarL1.Weighted.EnlargedTree
open PlanarL1.Topology
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] {G : SimpleGraph V} {l : V → V → ℝ}
  (hc : G.Connected) (hs : ∀ u v, l u v=l v u)
  (hl : ∀ u v, G.Adj u v → 0<l u v) (o : V)

lemma reverse_ne (d : ExtraDart hc hs hl o) : ExtraDart.reverse hc hs hl o d≠d := by
  intro he
  have hh := congrArg (fun d : ExtraDart hc hs hl o => d.val.fst) he
  exact d.val.adj.ne hh.symm

noncomputable def matchingGraph : SimpleGraph {v : Node hc hs hl o // (tree hc hs hl o).IsLeaf v} where
  Adj i j := ∃ d : ExtraDart hc hs hl o, i.val=.inr d ∧ j.val=.inr (ExtraDart.reverse hc hs hl o d)
  symm := ⟨by
    rintro i j ⟨d,hi,hj⟩
    refine ⟨ExtraDart.reverse hc hs hl o d,hj,?_⟩
    rw [ExtraDart.reverse_reverse]; exact hi⟩
  loopless := ⟨by
    rintro i ⟨d,hi,hj⟩
    exact reverse_ne hc hs hl o d (Sum.inr.inj (hj.symm.trans hi))⟩

end PlanarL1.Weighted.EnlargedTree


end

end OAI
end


