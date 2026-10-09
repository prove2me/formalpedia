-- Prove2me | Definitions.Def_RayBundle_UnitEdgeGraphGeometry
-- name    : RayBundle_UnitEdgeGraphGeometry
-- status  : Definition
-- author  : @jawneeboy
-- created : 2026-10-08T18:56:30.239086+00:00
-- url     : https://prove2.me/theorems/e064c66e-d939-42dc-9db2-69f02000279f
-- title:
--   Unit-edge metric realization of a connected graph with enumerated edges
-- statement:
--   Let $T$ be a connected simple graph on a vertex type $V$, with an explicit edge enumeration $e:\mathbb N\simeq E(T)$; in particular its edge set is countably infinite. Let $|T|_e$ be the unit-edge metric realization formed by successive isometric interval attachments and their metric inductive limit. Write $\iota:V\to|T|_e$ for its vertex map and $\epsilon_n:[0,1]\to|T|_e$ for its $n$th edge map.
--
--   The construction starts with the real-valued graph metric on $V$, attaches one closed unit interval for each enumerated edge, and takes the metric inductive limit of the isometric stages. The bundle includes the vertex and edge maps and proved infrastructure needed by their definitions and metric instances. The proposed theorem targets are supplied separately with standalone proofs.
-- source:
--   Standard unit-edge metric-graph convention: Nicholas Touikan, On geodesic ray bundles in hyperbolic groups, Proceedings of the American Mathematical Society 146 (2018), 4165–4173, Section 2. https://arxiv.org/abs/1706.01979 The present construction and supporting lemmas are proved in the supplied Lean development; these targets are not assigned numbered theorem attributions in that paper.

import Definitions.Def_RayBundle_MetricPathGeometry
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Gluing
import Mathlib.Topology.MetricSpace.Isometry

-- Source: RayBundle.Def_Cayley_connectedGraphMetric
namespace RayBundle

universe u

/-- The real-valued vertex metric of a connected graph, without a global instance on its vertices. -/
@[instance_reducible] noncomputable def connectedGraphMetric {V : Type u} (T : SimpleGraph V)
    (hT : T.Connected) : MetricSpace V where
  dist x y := T.dist x y
  dist_self x := by simp
  dist_comm x y := by simp [T.dist_comm]
  dist_triangle x y z := by exact_mod_cast hT.dist_triangle (u := x) (v := y) (w := z)
  eq_of_dist_eq_zero h := hT.dist_eq_zero_iff.mp (by exact_mod_cast h)

end RayBundle

-- Source: RayBundle.Def_Cayley_graphEdgePair
namespace RayBundle

universe u

/-- Choose an orientation for an enumerated undirected edge. -/
noncomputable def graphEdgePair {V : Type u} (T : SimpleGraph V)
    (e : ℕ ≃ T.edgeSet) (n : ℕ) : V × V := (e n).val.out

end RayBundle

-- Source: RayBundle.Thm_Cayley_graphEdgePair_adj
namespace RayBundle

universe u

theorem graphEdgePair_adj {V : Type u} (T : SimpleGraph V)
    (e : ℕ ≃ T.edgeSet) (n : ℕ) : T.Adj (graphEdgePair T e n).1 (graphEdgePair T e n).2 := by
  have h := (e n).property
  change s((graphEdgePair T e n).1, (graphEdgePair T e n).2) ∈ T.edgeSet
  have he : s((graphEdgePair T e n).1, (graphEdgePair T e n).2) = (e n).val := by
    change Quot.mk _ (e n).val.out = (e n).val
    exact Quot.out_eq _
  rw [he]
  exact h

end RayBundle

-- Source: RayBundle.Def_Cayley_UnitEdgeStage
namespace RayBundle

universe u

/-- A metric stage carrying an isometric copy of the original vertex space. -/
structure UnitEdgeStage (V : Type u) [MetricSpace V] where
  carrier : Type u
  metric : MetricSpace carrier
  vertex : V → carrier
  vertexIsometry : letI := metric; Isometry vertex

end RayBundle

-- Source: RayBundle.Def_Cayley_unitEdgeStageMetric
namespace RayBundle

universe u

instance unitEdgeStageMetric {V : Type u} [MetricSpace V] (A : UnitEdgeStage V) :
    MetricSpace A.carrier := A.metric

end RayBundle

-- Source: RayBundle.Def_Cayley_UnitEdgeExtension
namespace RayBundle

universe u

/-- One attached unit interval, with the old stage embedded isometrically. -/
structure UnitEdgeExtension {V : Type u} [MetricSpace V] (A : UnitEdgeStage V)
    (a b : V) where
  stage : UnitEdgeStage V
  old : A.carrier → stage.carrier
  oldIsometry : Isometry old
  edge : Set.Icc (0 : ℝ) 1 → stage.carrier
  edgeIsometry : Isometry edge
  vertex_eq : ∀ v, stage.vertex v = old (A.vertex v)
  edge_zero : edge ⟨0, by simp⟩ = stage.vertex a
  edge_one : edge ⟨1, by simp⟩ = stage.vertex b
  edge_old_lower : ∀ t x, min t.val (1 - t.val) ≤ dist (edge t) (old x)

end RayBundle

-- Source: RayBundle.Def_Cayley_UnitEdgeStage_attach
namespace RayBundle

universe u

/-- Attach a unit interval along two old vertices at distance one. -/
noncomputable def UnitEdgeStage.attach {V : Type u} [MetricSpace V]
    (A : UnitEdgeStage V) (a b : V) (hab : dist a b = 1) : UnitEdgeExtension A a b := by
  let Z := {t : ℝ // t = 0 ∨ t = 1}
  letI : Nonempty Z := ⟨⟨0, Or.inl rfl⟩⟩
  let f : Z → A.carrier := fun t => if t.val = 0 then A.vertex a else A.vertex b
  let j : Z → Set.Icc (0 : ℝ) 1 := fun t => ⟨t.val, by
    rcases t.property with h | h <;> simp [h]⟩
  have hf : Isometry f := by
    apply Isometry.of_dist_eq
    intro x y
    change dist (f x) (f y) = dist (x.val) (y.val)
    rcases x.property with hx | hx <;> rcases y.property with hy | hy
    all_goals simp only [f, hx, hy]
    all_goals simp [A.vertexIsometry.dist_eq, hab, dist_comm b a,
      Real.dist_eq]
  have hj : Isometry j := Isometry.of_dist_eq fun _ _ => rfl
  let B : UnitEdgeStage V :=
    { carrier := Metric.GlueSpace hf hj
      metric := inferInstance
      vertex := Metric.toGlueL hf hj ∘ A.vertex
      vertexIsometry := (Metric.toGlueL_isometry (X := A.carrier)
        (Y := Set.Icc (0 : ℝ) 1) (Z := Z) hf hj).comp A.vertexIsometry }
  refine
    { stage := B
      old := Metric.toGlueL hf hj
      oldIsometry := Metric.toGlueL_isometry hf hj
      edge := Metric.toGlueR hf hj
      edgeIsometry := Metric.toGlueR_isometry hf hj
      vertex_eq := fun _ => rfl
      edge_zero := ?_
      edge_one := ?_
      edge_old_lower := ?_ }
  · have h := congrFun (Metric.toGlue_commute hf hj) (⟨0, Or.inl rfl⟩ : Z)
    simpa [B, Function.comp_def, f, j] using h.symm
  · have h := congrFun (Metric.toGlue_commute hf hj) (⟨1, Or.inr rfl⟩ : Z)
    simpa [B, Function.comp_def, f, j] using h.symm
  · intro t x
    change min t.val (1 - t.val) ≤ Metric.glueDist f j 0 (.inr t) (.inl x)
    simp only [Metric.glueDist, add_zero]
    apply le_ciInf
    intro z
    have ht0 := t.property.1
    have ht1 := t.property.2
    have hx : 0 ≤ dist x (f z) := dist_nonneg
    rcases z.property with hz | hz
    · have hd : dist t (j z) = t.val := by
        change |t.val - z.val| = t.val
        simp [hz, abs_of_nonneg ht0]
      rw [hd]
      linarith [min_le_left t.val (1 - t.val)]
    · have hd : dist t (j z) = 1 - t.val := by
        change |t.val - z.val| = 1 - t.val
        rw [hz, abs_of_nonpos (by linarith)]
        ring
      rw [hd]
      linarith [min_le_right t.val (1 - t.val)]

end RayBundle

-- Source: RayBundle.Def_Cayley_UnitEdgeStage_sequence
namespace RayBundle

universe u

noncomputable def UnitEdgeStage.sequence {V : Type u} [MetricSpace V]
    (a b : ℕ → V) (hab : ∀ n, dist (a n) (b n) = 1) : ℕ → UnitEdgeStage V
  | 0 => { carrier := V, metric := inferInstance, vertex := id, vertexIsometry := isometry_id }
  | n + 1 => ((sequence a b hab n).attach (a n) (b n) (hab n)).stage

end RayBundle

-- Source: RayBundle.Def_Cayley_UnitEdgeStage_sequenceStep
namespace RayBundle

universe u

noncomputable def UnitEdgeStage.sequenceStep {V : Type u} [MetricSpace V]
    (a b : ℕ → V) (hab : ∀ n, dist (a n) (b n) = 1) (n : ℕ) :
    (sequence a b hab n).carrier → (sequence a b hab (n + 1)).carrier :=
  ((sequence a b hab n).attach (a n) (b n) (hab n)).old

end RayBundle

-- Source: RayBundle.Thm_Cayley_UnitEdgeStage_sequenceStep_isometry
namespace RayBundle

universe u

theorem UnitEdgeStage.sequenceStep_isometry {V : Type u} [MetricSpace V]
    (a b : ℕ → V) (hab : ∀ n, dist (a n) (b n) = 1) (n : ℕ) :
    Isometry (sequenceStep a b hab n) :=
  ((sequence a b hab n).attach (a n) (b n) (hab n)).oldIsometry

end RayBundle

-- Source: RayBundle.Def_Cayley_UnitEdgeRealization
namespace RayBundle

universe u

/-- The metric inductive limit of successive unit-edge attachments; no completion is taken. -/
noncomputable abbrev UnitEdgeRealization {V : Type u} [MetricSpace V]
    (a b : ℕ → V) (hab : ∀ n, dist (a n) (b n) = 1) : Type u :=
  Metric.InductiveLimit (UnitEdgeStage.sequenceStep_isometry a b hab)

end RayBundle

-- Source: RayBundle.Def_Cayley_GraphRealization
namespace RayBundle

universe u

/-- Attach each edge of an enumerated connected graph exactly once. -/
noncomputable def GraphRealization {V : Type u} (T : SimpleGraph V) (hT : T.Connected)
    (e : ℕ ≃ T.edgeSet) : Type u := by
  letI := connectedGraphMetric T hT
  exact UnitEdgeRealization (fun n => (graphEdgePair T e n).1)
    (fun n => (graphEdgePair T e n).2) (fun n => by
      change (T.dist _ _ : ℝ) = 1
      exact_mod_cast T.dist_eq_one_iff_adj.mpr (graphEdgePair_adj T e n))

end RayBundle

-- Source: RayBundle.Def_Cayley_unitEdgeRealizationMetric
namespace RayBundle

universe u

noncomputable instance unitEdgeRealizationMetric {V : Type u} [MetricSpace V]
    (a b : ℕ → V) (hab : ∀ n, dist (a n) (b n) = 1) :
    MetricSpace (UnitEdgeRealization a b hab) :=
  inferInstanceAs (MetricSpace (Metric.InductiveLimit
    (UnitEdgeStage.sequenceStep_isometry a b hab)))

end RayBundle

-- Source: RayBundle.Def_Cayley_graphRealizationMetric
namespace RayBundle

universe u

noncomputable instance graphRealizationMetric {V : Type u} (T : SimpleGraph V)
    (hT : T.Connected) (e : ℕ ≃ T.edgeSet) : MetricSpace (GraphRealization T hT e) := by
  letI := connectedGraphMetric T hT
  unfold GraphRealization
  infer_instance

end RayBundle

-- Source: RayBundle.Def_Cayley_UnitEdgeRealization_vertex
namespace RayBundle

universe u

noncomputable def UnitEdgeRealization.vertex {V : Type u} [MetricSpace V]
    (a b : ℕ → V) (hab : ∀ n, dist (a n) (b n) = 1) : V → UnitEdgeRealization a b hab :=
  Metric.toInductiveLimit (UnitEdgeStage.sequenceStep_isometry a b hab) 0

end RayBundle

-- Source: RayBundle.Def_Cayley_GraphRealization_vertex
namespace RayBundle

universe u

noncomputable def GraphRealization.vertex {V : Type u} (T : SimpleGraph V)
    (hT : T.Connected) (e : ℕ ≃ T.edgeSet) : V → GraphRealization T hT e := by
  letI := connectedGraphMetric T hT
  exact UnitEdgeRealization.vertex _ _ _

end RayBundle

-- Source: RayBundle.Def_Cayley_UnitEdgeRealization_edge
namespace RayBundle

universe u

noncomputable def UnitEdgeRealization.edge {V : Type u} [MetricSpace V]
    (a b : ℕ → V) (hab : ∀ n, dist (a n) (b n) = 1) (n : ℕ) :
    Set.Icc (0 : ℝ) 1 → UnitEdgeRealization a b hab :=
  Metric.toInductiveLimit (UnitEdgeStage.sequenceStep_isometry a b hab) (n + 1) ∘
    ((UnitEdgeStage.sequence a b hab n).attach (a n) (b n) (hab n)).edge

end RayBundle

-- Source: RayBundle.Def_Cayley_GraphRealization_edge
namespace RayBundle

universe u

noncomputable def GraphRealization.edge {V : Type u} (T : SimpleGraph V)
    (hT : T.Connected) (e : ℕ ≃ T.edgeSet) (n : ℕ) :
    Set.Icc (0 : ℝ) 1 → GraphRealization T hT e := by
  letI := connectedGraphMetric T hT
  exact UnitEdgeRealization.edge _ _ _ n

end RayBundle


