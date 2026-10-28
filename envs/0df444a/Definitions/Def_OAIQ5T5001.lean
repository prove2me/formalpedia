-- Prove2me | Definitions.Def_OAIQ5T5001
-- name    : OAIQ5T5001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T11:54:41.919638+00:00
-- url     : https://prove2.me/theorems/ecf99726-0e09-45ad-955f-157cb6af71c6
-- title:
--   Definitions bundle OAIQ5T5001 of the split of OpenAI, Planar Graph Metrics Embed into L1 with Constant Distortion
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PlanarL1.planar_graph_metrics_embed_L1`, carved from OpenAI's openai/math development (OpenAI, *Planar Graph Metrics Embed into L1 with Constant Distortion*, OpenAI Math Release, September 23, 2026, result family 89, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 31 declarations of OpenAI's Lean: 6 definitions, 2 inductive types or structures, 4 instances and 19 theorems. The definitions and types are `OAI.PlanarL1.Topology.Drawing.excludedTimes`, `OAI.PlanarL1.Topology.PortFrame`, `OAI.PlanarL1.Topology.annularConnector`, `OAI.PlanarL1.Topology.exteriorToDisk`, `OAI.PlanarL1.Topology.leafExtension`, `OAI.PlanarL1.Topology.starPorts`, `OAI.PlanarL1.Weighted.DescendingParents`, `OAI.PlanarL1.Weighted.DescendingParents.graph`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/PlanarL1, in whole or in part: [`PlanarL1_DiskCrossing`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/PlanarL1/PlanarL1/DiskCrossing.lean), [`PlanarL1_Drawing`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/PlanarL1/PlanarL1/Drawing.lean), [`PlanarL1_Growth`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/PlanarL1/PlanarL1/Growth.lean), [`PlanarL1_Retubing`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/PlanarL1/PlanarL1/Retubing.lean), [`PlanarL1_Surgery`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/PlanarL1/PlanarL1/Surgery.lean), [`PlanarL1_TreeDisk`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/PlanarL1/PlanarL1/TreeDisk.lean), [`PlanarL1_WeightedMetric`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/PlanarL1/PlanarL1/WeightedMetric.lean).
--
--   **Imports.** It imports the published bundle `Def_PlanarL1`.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ5T5002`.
-- source:
--   OpenAI, Planar Graph Metrics Embed into L1 with Constant Distortion, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 89; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Planar-Graph-Metrics-Embed-into-L1-with-Constant-Distortion-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/PlanarL1 at commit adc7f12

import Mathlib
import Definitions.Def_PlanarL1

section
-- module Solutions.OAIQ5_T5.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib's newer `TensorProduct.inductionOn` (no `zero` case: it is the `tmul` case at
`0 ⊗ₜ 0`); ours has only `TensorProduct.induction_on`, which asks for one. Not named
`TensorProduct.inductionOn`: inside `namespace OAI` that would make `open TensorProduct` open
`OAI.TensorProduct` instead of Mathlib's. -/
@[elab_as_elim]
theorem tensorInductionOn {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {motive : TensorProduct R M N → Prop} (z : TensorProduct R M N)
    (tmul : ∀ x y, motive (TensorProduct.tmul R x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z (by simpa using tmul 0 0) tmul add
/-- Mathlib's newer case names for `FreeGroup.induction_on` (`one`, where ours says `C1`). -/
@[elab_as_elim]
theorem freeGroupInductionOn {α : Type*} {C : FreeGroup α → Prop} (z : FreeGroup α) (one : C 1)
    (of : ∀ x, C (FreeGroup.of x)) (inv_of : ∀ x, C (FreeGroup.of x) → C (FreeGroup.of x)⁻¹)
    (mul : ∀ x y, C x → C y → C (x * y)) : C z :=
  FreeGroup.induction_on z one of inv_of mul
/-- The first projection of a probability measure on a product: found by instance search in d13f23b
(total `Measure.map`), here a measurable map. -/
instance isProbabilityMeasure_map_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.fst) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
instance isProbabilityMeasure_map_snd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.snd) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
instance isProbabilityMeasure_map_subtype_val {α : Type*} [MeasurableSpace α] {p : α → Prop}
    {μ : MeasureTheory.Measure {a // p a}} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Subtype.val) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable
/-- Mathlib d13f23b's `YoungDiagram.card_transpose`. -/
@[simp]
theorem _root_.YoungDiagram.card_transpose (μ : YoungDiagram) : μ.transpose.card = μ.card := by
  unfold YoungDiagram.card
  apply Finset.card_bij (fun c _ => c.swap)
  · intro c hc
    have : c ∈ μ.transpose := hc
    rw [YoungDiagram.mem_transpose] at this
    exact this
  · intro a _ b _ h
    simpa using h
  · intro b hb
    refine ⟨b.swap, ?_, by simp⟩
    show b.swap ∈ μ.transpose
    rw [YoungDiagram.mem_transpose]
    simpa using hb
/-- For a measurable equivalence `e`, `IsProbabilityMeasure (μ.map e)` is found by instance search
(Mathlib d13f23b finds it for every map `f`: there `Measure.map` of a non-measurable map is a Dirac
mass, here it is `0`, so only the measurable case can be shimmed). -/
instance isProbabilityMeasure_map_measurableEquiv {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
    (e : α ≃ᵐ β) : MeasureTheory.IsProbabilityMeasure (μ.map e) :=
  MeasureTheory.Measure.isProbabilityMeasure_map e.measurable.aemeasurable
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_DiskCrossing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! ## General cyclic-endpoint disk separation -/

namespace PlanarL1.Topology
open Complex Real Set

/- An explicit annular extension reduces arbitrary cyclic boundary endpoints
  to the already-proved cardinal-endpoint disk crossing obstruction. -/
noncomputable def annularConnector (a b : ℝ) :
    Path (Circle.exp a : ℂ) ((2 : ℂ) * (Circle.exp b : ℂ)) where
  toFun t := ((1 + (t : ℝ) : ℝ) : ℂ) *
    (Circle.exp ((1 - (t : ℝ)) * a + (t : ℝ) * b) : ℂ)
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by norm_num

end PlanarL1.Topology



end

end OAI
end

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
variable {V : Type}
  {G : SimpleGraph V}

/-- Away from the first/last third of an incident edge, every vertex is
uniformly separated from that edge. The set is closed even at both cutoffs. -/
def excludedTimes (w : V) (d : G.Dart) : Set unitInterval :=
  {t | (w≠d.fst ∨ (1/3:ℝ)≤(t:ℝ)) ∧ (w≠d.snd ∨ (t:ℝ)≤(2/3:ℝ))}

end Drawing

end PlanarL1.Topology


namespace PlanarL1.Topology
open Set Metric

lemma compact_segment_complex (x y : ℂ) : IsCompact (segment ℝ x y) := by
  rw [segment_eq_image' ℝ x y]
  exact isCompact_Icc.image (by fun_prop)

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

namespace PlanarL1
namespace Weighted
variable {V : Type} {G : SimpleGraph V} {l : V → V → ℝ}

lemma length_eq_sum_darts {u v : V} (p : G.Walk u v) :
    walkLength l p = (p.darts.map (fun d => l d.fst d.snd)).sum := by
  induction p with
  | nil => rfl
  | cons h p ih => simp only [walkLength,SimpleGraph.Walk.darts_cons,List.map_cons,List.sum_cons,ih]

lemma length_nonneg (hl : ∀ u v, G.Adj u v → 0 ≤ l u v) {u v : V} (p : G.Walk u v) :
    0 ≤ walkLength l p := by
  induction p with
  | nil => exact le_rfl
  | cons h p ih => exact add_nonneg (hl _ _ h) ih

lemma length_append {u v w : V} (p : G.Walk u v) (q : G.Walk v w) :
    walkLength l (p.append q) = walkLength l p+walkLength l q := by
  simp only [length_eq_sum_darts,SimpleGraph.Walk.darts_append,List.map_append,List.sum_append]

lemma length_reverse (hs : ∀ u v, l u v=l v u) {u v : V} (p : G.Walk u v) :
    walkLength l p.reverse=walkLength l p := by
  simp only [length_eq_sum_darts,SimpleGraph.Walk.darts_reverse,List.map_reverse,List.map_map,List.sum_reverse]
  congr 2
  funext d
  exact hs d.snd d.fst

lemma length_bypass [DecidableEq V] (hl : ∀ u v, G.Adj u v → 0 ≤ l u v)
    {u v : V} (p : G.Walk u v) : walkLength l p.bypass ≤ walkLength l p := by
  rw [length_eq_sum_darts,length_eq_sum_darts]
  apply (p.darts_bypass_sublist_darts.map _).sum_le_sum
  intro a ha
  obtain ⟨d,_,rfl⟩ := List.mem_map.mp ha
  exact hl d.fst d.snd d.adj

/-- Positivity permits deletion of repetitions, so the literal walk-infimum
is achieved by one of finitely many simple paths. No integral edge lengths
or approximation of the metric is used. -/
lemma exists_shortest [Fintype V] (hl : ∀ u v, G.Adj u v → 0 ≤ l u v)
    {u v : V} (hc : G.Reachable u v) :
    ∃ p : G.Path u v, ∀ q : G.Walk u v, walkLength l p.val ≤ walkLength l q := by
  classical
  obtain ⟨q⟩ := hc
  have he : (Finset.univ : Finset (G.Path u v)).Nonempty := ⟨q.toPath,Finset.mem_univ _⟩
  obtain ⟨p,_,hp⟩ := Finset.univ.exists_min_image (fun p : G.Path u v => walkLength l p.val) he
  refine ⟨p,fun q => ?_⟩
  exact (hp q.toPath (Finset.mem_univ _)).trans (length_bypass hl q)

lemma distance_eq_length [Fintype V] (hl : ∀ u v, G.Adj u v → 0 ≤ l u v)
    {u v : V} (hc : G.Reachable u v) :
    ∃ p : G.Path u v, graphDistance G l u v=walkLength l p.val ∧
      ∀ q : G.Walk u v, walkLength l p.val ≤ walkLength l q := by
  obtain ⟨p,hp⟩ := exists_shortest hl hc
  refine ⟨p,?_,hp⟩
  apply le_antisymm
  · exact csInf_le ⟨0,by rintro a ⟨q,rfl⟩; exact length_nonneg hl q⟩ ⟨p.val,rfl⟩
  · exact le_csInf ⟨walkLength l p.val,⟨p.val,rfl⟩⟩ (by rintro a ⟨q,rfl⟩; exact hp q)

lemma distance_le_walk (hl : ∀ u v, G.Adj u v → 0 ≤ l u v)
    {u v : V} (p : G.Walk u v) : graphDistance G l u v ≤ walkLength l p :=
  csInf_le ⟨0,by rintro a ⟨q,rfl⟩; exact length_nonneg hl q⟩ ⟨p,rfl⟩

lemma distance_symm [Fintype V] (hl : ∀ u v, G.Adj u v → 0 ≤ l u v)
    (hs : ∀ u v, l u v=l v u) {u v : V} (hc : G.Reachable u v) :
    graphDistance G l u v=graphDistance G l v u := by
  have hb {u v : V} (hc : G.Reachable u v) : graphDistance G l v u ≤ graphDistance G l u v := by
    obtain ⟨p,he,_⟩ := distance_eq_length hl hc
    rw [he,← length_reverse hs p.val]
    exact distance_le_walk hl p.val.reverse
  exact le_antisymm (hb hc.symm) (hb hc)

lemma distance_triangle [Fintype V] (hl : ∀ u v, G.Adj u v → 0 ≤ l u v)
    {u v w : V} (huv : G.Reachable u v) (hvw : G.Reachable v w) :
    graphDistance G l u w ≤ graphDistance G l u v+graphDistance G l v w := by
  obtain ⟨p,hp,_⟩ := distance_eq_length hl huv
  obtain ⟨q,hq,_⟩ := distance_eq_length hl hvw
  rw [hp,hq,← length_append]
  exact distance_le_walk hl (p.val.append q.val)

lemma edge_bound (hl : ∀ u v, G.Adj u v → 0 ≤ l u v)
    {u v : V} (h : G.Adj u v) : graphDistance G l u v ≤ l u v := by
  simpa only [walkLength,add_zero] using distance_le_walk hl (.cons h .nil)

lemma height_edge [Fintype V] (hc : G.Connected)
    (hs : ∀ u v, l u v=l v u) (hl : ∀ u v, G.Adj u v → 0 ≤ l u v)
    (o : V) {u v : V} (h : G.Adj u v) :
    |graphDistance G l o u-graphDistance G l o v| ≤ l u v := by
  apply abs_le.mpr
  have h₁ := distance_triangle hl (hc.preconnected o u) (hc.preconnected u v)
  have h₂ := distance_triangle hl (hc.preconnected o v) (hc.preconnected v u)
  have h₃ := edge_bound hl h
  have h₄ := edge_bound hl h.symm
  rw [hs v u] at h₄
  constructor <;> linarith

/-- Each non-root vertex has a strictly lower predecessor on a genuine
weighted shortest path. This is the input to the shortest-path spanning tree
in ; positivity, not integral weights, supplies the descent. -/
lemma exists_predecessor [Fintype V] (hc : G.Connected)
    (hs : ∀ u v, l u v=l v u) (hl : ∀ u v, G.Adj u v → 0 < l u v)
    (o v : V) (hv : v ≠ o) : ∃ u, G.Adj u v ∧
      graphDistance G l o v=graphDistance G l o u+l u v ∧
      graphDistance G l o u < graphDistance G l o v := by
  have hn : ∀ u v, G.Adj u v → 0 ≤ l u v := fun u v h => (hl u v h).le
  obtain ⟨p,he,hp⟩ := distance_eq_length hn (hc.preconnected v o)
  cases hw : p.val with
  | nil => exact (hv rfl).elim
  | @cons v u o h q =>
    have htail : graphDistance G l u o=walkLength l q := by
      apply le_antisymm (distance_le_walk hn q)
      obtain ⟨r,hr,_⟩ := distance_eq_length hn (hc.preconnected u o)
      have hb := hp (.cons h r.val)
      rw [hw] at hb
      simp only [walkLength] at hb
      rw [hr]
      linarith
    have heq : graphDistance G l o v=graphDistance G l o u+l u v := by
      rw [distance_symm hn hs (hc.preconnected o v),he,hw,walkLength,
        ← htail,distance_symm hn hs (hc.preconnected u o),hs v u]
      ring
    exact ⟨u,h.symm,heq,by linarith [hl v u h,hs v u]⟩

end Weighted
end PlanarL1



end

section

/-! ## Shortest-path spanning tree . -/

namespace PlanarL1.Weighted
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] {G : SimpleGraph V} {l : V → V → ℝ}

/-- A predecessor system whose heights strictly decrease to its root. The
well-foundedness here uses finiteness, not any discretization of real lengths. -/
structure DescendingParents (V : Type*) where
  root : V
  height : V → ℝ
  parent : V → V
  at_root : parent root=root
  descent : ∀ v, v ≠ root → height (parent v)<height v

namespace DescendingParents
variable (D : DescendingParents V)

omit [Fintype V] in
lemma parent_ne (v : V) (hv : v ≠ D.root) : D.parent v ≠ v := by
  intro he
  have h := D.descent v hv
  rw [he] at h
  exact lt_irrefl _ h

noncomputable def graph : SimpleGraph V where
  Adj u v := (u ≠ D.root ∧ D.parent u=v) ∨ (v ≠ D.root ∧ D.parent v=u)
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by
    intro v h
    rcases h with h | h <;> exact D.parent_ne v h.1 h.2⟩

lemma wellFounded : WellFounded (fun u v : V => D.height u<D.height v) := by
  let : IsTrans V (fun u v => D.height u<D.height v) := ⟨fun _ _ _ => lt_trans⟩
  let : Std.Irrefl (fun u v => D.height u<D.height v) := ⟨fun _ => lt_irrefl _⟩
  exact Finite.wellFounded_of_trans_of_irrefl _

end DescendingParents

end PlanarL1.Weighted



end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_TreeDisk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section



namespace PlanarL1.Topology
open Set Real

/-- Radial inversion fixes the unit circle and puts the exterior into the disk.
This avoids any one-point-compactification assumption in the complementary
region of a prospective tree neighborhood. -/
noncomputable def exteriorToDisk (z : ℂ) : ℂ := star (z⁻¹)

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




namespace PlanarL1.Topology
open Set

/-- Adding finitely many new leaves to one vertex; no geometric or metric
conclusion is included in this graph definition. -/
def leafExtension {V W : Type} (G : SimpleGraph V) (v : V) : SimpleGraph (V⊕W) where
  Adj x y := match x,y with
    | .inl a,.inl b => G.Adj a b
    | .inl a,.inr _ => a=v
    | .inr _,.inl a => a=v
    | .inr _,.inr _ => False
  symm := ⟨by
    intro x y h
    cases x <;> cases y <;> dsimp at h ⊢
    all_goals first | exact h | exact h.symm⟩
  loopless := ⟨by intro x; cases x <;> simp⟩

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
open Set

variable {V : Type}

/-- Released radial port tails; unlike `PortMove` this does not prescribe the
selected route, which may already have passed through several bends. -/
structure PortFrame (p a : V → ℂ) (B : Set V) (v : V) (q : ℂ) (S T : Set ℂ) : Prop where
  selected : a v=q
  on_frontier : ∀ w∈B, w≠v → a w∈frontier T
  tail_old : ∀ w∈B, w≠v → segment ℝ (a w) (p w) ⊆ closure S
  tail_frontier : ∀ w∈B, w≠v → ∀ z∈segment ℝ (a w) (p w),
    z∈frontier S → z=p w
  tail_new : ∀ w∈B, w≠v → ∀ z∈segment ℝ (a w) (p w),
    z∈closure T → z=a w
  tails_disjoint : ∀ w∈B, w≠v → ∀ u∈B, u≠v → w≠u →
    Disjoint (segment ℝ (a w) (p w)) (segment ℝ (a u) (p u))

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
open Set Metric Filter
variable {V W : Type} [LinearOrder V] [Finite V] [LinearOrder W] [Finite W]
  [LinearOrder (V⊕W)] {G : SimpleGraph V} {B : Set V}

/-- After processing a frontier vertex, the old remaining ports and all its
new children are the frontier. -/
def starPorts (B : Set V) (v : V) : Set (V⊕W) :=
  {w | Sum.elim (fun u => u∈B ∧ u≠v) (fun _ => True) w}

end PlanarL1.Topology




end

end OAI
end


