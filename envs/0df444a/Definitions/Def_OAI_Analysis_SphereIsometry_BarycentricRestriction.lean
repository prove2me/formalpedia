-- Prove2me | Definitions.Def_OAI_Analysis_SphereIsometry_BarycentricRestriction
-- name    : OAI_Analysis_SphereIsometry_BarycentricRestriction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T21:44:17.286094+00:00
-- url     : https://prove2.me/theorems/a3c5ffa4-2ec2-4d6b-bcda-191213db46c3
-- title:
--   Embeddings of finite complexes and their subdivisions
-- statement:
--   These notions belong to a self-contained fixed-point toolkit used in the proof of Tingley's theorem: Sperner's lemma on iterated barycentric subdivisions, Brouwer's fixed point theorem for the probability simplex, Schauder's theorem for compact convex sets, the Kuratowski measure of noncompactness, and a Darbo–Sadovskii fixed point theorem for condensing maps. Let $K,L$ be finite complexes on vertex sets $V,W$.
--
--   1. **Embedding.** An injection $e:V\to W$ such that
--   $$
--   e(s)\in L\iff s\in K\quad\text{for all }s\subseteq V .
--   $$
--   The inclusion of a full simplex into a larger full simplex is an example.
--   2. **Subdivided embedding.** Faces map to faces, giving an embedding of the barycentric subdivisions.
--   3. **Preimages and carriers.** Faces of $L$ inside the image come from faces of $K$, and carriers map compatibly with a coordinate embedding. So faces whose carrier lies in the image coordinates are exactly the images of faces of $K$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/SphereIsometry/BarycentricRestriction.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/SphereIsometry/BarycentricRestriction.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TingleySphereIsometry mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.SeparationQuotient
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Seminorm
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Rat.Encodable
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Encodable.Pi
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Constructions
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.Cauchy
import Definitions.Def_TingleySphereIsometry
import Definitions.Def_OAI_Analysis_SphereIsometry_Basic
import Definitions.Def_OAI_Analysis_SphereIsometry_UnitRepresentatives
import Definitions.Def_OAI_Analysis_SphereIsometry_UltraRealLimit
import Definitions.Def_OAI_Analysis_SphereIsometry_UltraNormed
import Definitions.Def_OAI_Analysis_SphereIsometry_UltraSphere
import Definitions.Def_OAI_Analysis_SphereIsometry_DefectSequence
import Definitions.Def_OAI_Analysis_SphereIsometry_SphereCompletion
import Definitions.Def_OAI_Analysis_SphereIsometry_DefectAttainment
import Definitions.Def_OAI_Analysis_SphereIsometry_RadialContact
import Definitions.Def_OAI_Analysis_SphereIsometry_ReturnMap
import Definitions.Def_OAI_Analysis_SphereIsometry_Supports
import Definitions.Def_OAI_Analysis_SphereIsometry_PositiveConvexFace
import Definitions.Def_OAI_Analysis_SphereIsometry_ExtremalPropagation
import Definitions.Def_OAI_Analysis_SphereIsometry_PositiveScheduling
import Definitions.Def_OAI_Analysis_SphereIsometry_InvariantConvexSet
import Definitions.Def_OAI_Analysis_SphereIsometry_AlignmentSet
import Definitions.Def_OAI_Analysis_SphereIsometry_ReturnMapEstimate
import Definitions.Def_OAI_Analysis_SphereIsometry_DiameterBounds
import Definitions.Def_OAI_Analysis_SphereIsometry_KuratowskiBasic
import Definitions.Def_OAI_Analysis_SphereIsometry_ReturnMapBounds
import Definitions.Def_OAI_Analysis_SphereIsometry_ScalarBins
import Definitions.Def_OAI_Analysis_SphereIsometry_ReturnMapNoncompactness
import Definitions.Def_OAI_Analysis_SphereIsometry_ProbabilitySimplex
import Definitions.Def_OAI_Analysis_SphereIsometry_SimplexLimit
import Definitions.Def_OAI_Analysis_SphereIsometry_FiniteComplex
import Definitions.Def_OAI_Analysis_SphereIsometry_BarycentricFlags
import Definitions.Def_OAI_Analysis_SphereIsometry_SubdivisionData
import Definitions.Def_OAI_Analysis_SphereIsometry_BarycentricBasic
import Definitions.Def_OAI_Analysis_SphereIsometry_BarycentricSupport
import Definitions.Def_OAI_Analysis_SphereIsometry_ConvexDiameter
import Definitions.Def_OAI_Analysis_SphereIsometry_BarycentricMesh
import Definitions.Def_OAI_Analysis_SphereIsometry_IteratedPoints
import Definitions.Def_OAI_Analysis_SphereIsometry_SpernerFacet
import Definitions.Def_OAI_Analysis_SphereIsometry_SpernerIncidence
import Definitions.Def_OAI_Analysis_SphereIsometry_SpernerBoundary

namespace OAI

/-! # Embeddings of complexes and exact restriction under subdivision -/

noncomputable section

namespace Tingley.FiniteComplex

universe u v w z
variable {V : Type u} {W : Type v} [Fintype V] [Fintype W]
variable [DecidableEq V] [DecidableEq W]

structure Embedding (K : FiniteComplex V) (L : FiniteComplex W) where
  toEmbedding : V ↪ W
  map_mem_iff : ∀ s : Finset V, s.map toEmbedding ∈ L.faces ↔ s ∈ K.faces

namespace Embedding

variable {K : FiniteComplex V} {L : FiniteComplex W}

def full (e : V ↪ W) : Embedding (FiniteComplex.full : FiniteComplex V)
    (FiniteComplex.full : FiniteComplex W) where
  toEmbedding := e
  map_mem_iff := fun _ => by simp

def faceMap (e : Embedding K L) : FaceVertex K ↪ FaceVertex L where
  toFun s := ⟨s.val.map e.toEmbedding,
    (e.map_mem_iff s.val).mpr s.property.1, Finset.map_nonempty.mpr s.property.2⟩
  inj' := by
    intro a b h
    apply Subtype.ext
    exact Finset.map_injective e.toEmbedding (congrArg Subtype.val h)

@[simp] theorem faceMap_val (e : Embedding K L) (s : FaceVertex K) :
    (e.faceMap s).val = s.val.map e.toEmbedding := rfl

def sd (e : Embedding K L) : Embedding K.sd L.sd where
  toEmbedding := e.faceMap
  map_mem_iff := by
    intro c
    rw [mem_sd_iff, mem_sd_iff]
    constructor
    · intro hc a ha b hb
      have h := hc (e.faceMap a) (Finset.mem_map.mpr ⟨a, ha, rfl⟩)
        (e.faceMap b) (Finset.mem_map.mpr ⟨b, hb, rfl⟩)
      exact h.imp Finset.map_subset_map.mp Finset.map_subset_map.mp
    · intro hc a ha b hb
      obtain ⟨a', ha', rfl⟩ := Finset.mem_map.mp ha
      obtain ⟨b', hb', rfl⟩ := Finset.mem_map.mp hb
      exact (hc a' ha' b' hb').imp Finset.map_subset_map.mpr Finset.map_subset_map.mpr

def preimage (e : Embedding K L) (s : Finset W) : Finset V :=
  Finset.univ.filter (fun v => e.toEmbedding v ∈ s)

@[simp] theorem mem_preimage (e : Embedding K L) {s : Finset W} {v : V} :
    v ∈ e.preimage s ↔ e.toEmbedding v ∈ s := by
  simp [preimage]

theorem map_preimage (e : Embedding K L) (s : Finset W)
    (hs : ∀ w ∈ s, ∃ v, e.toEmbedding v = w) :
    (e.preimage s).map e.toEmbedding = s := by
  ext w
  constructor
  · intro hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hw
    exact (e.mem_preimage).mp hv
  · intro hw
    obtain ⟨v, rfl⟩ := hs w hw
    exact Finset.mem_map.mpr ⟨v, e.mem_preimage.mpr hw, rfl⟩

theorem exists_face_preimage (e : Embedding K L) {s : Finset W} (hs : s ∈ L.faces)
    (hrange : ∀ w ∈ s, ∃ v, e.toEmbedding v = w) :
    ∃ t ∈ K.faces, t.map e.toEmbedding = s := by
  refine ⟨e.preimage s, ?_, e.map_preimage s hrange⟩
  apply (e.map_mem_iff _).mp
  rwa [e.map_preimage s hrange]

variable {I : Type w} {J : Type z} [DecidableEq I] [DecidableEq J]

theorem faceCarrier_map (e : Embedding K L) (i : I ↪ J)
    {cV : V → Finset I} {cW : W → Finset J}
    (h : ∀ v, cW (e.toEmbedding v) = (cV v).map i) (s : Finset V) :
    faceCarrier cW (s.map e.toEmbedding) = (faceCarrier cV s).map i := by
  ext j
  constructor
  · intro hj
    obtain ⟨w, hw, hj⟩ := mem_faceCarrier.mp hj
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hw
    rw [h] at hj
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hj
    exact Finset.mem_map.mpr ⟨a, mem_faceCarrier.mpr ⟨v, hv, ha⟩, rfl⟩
  · intro hj
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hj
    obtain ⟨v, hv, ha⟩ := mem_faceCarrier.mp ha
    refine mem_faceCarrier.mpr ⟨e.toEmbedding v,
      Finset.mem_map.mpr ⟨v, hv, rfl⟩, ?_⟩
    rw [h]
    exact Finset.mem_map.mpr ⟨a, ha, rfl⟩

theorem sdCarrier_faceMap (e : Embedding K L) (i : I ↪ J)
    {cV : V → Finset I} {cW : W → Finset J}
    (h : ∀ v, cW (e.toEmbedding v) = (cV v).map i) (s : FaceVertex K) :
    L.sdCarrier cW (e.faceMap s) = (K.sdCarrier cV s).map i :=
  e.faceCarrier_map i h s.val

theorem faceMap_range_iff (e : Embedding K L) {cW : W → Finset J} {A : Finset J}
    (h : ∀ w, cW w ⊆ A ↔ ∃ v, e.toEmbedding v = w) (s : FaceVertex L) :
    L.sdCarrier cW s ⊆ A ↔ ∃ t : FaceVertex K, e.faceMap t = s := by
  constructor
  · intro hs
    have hvertices : ∀ w ∈ s.val, ∃ v, e.toEmbedding v = w := by
      intro w hw
      apply (h w).mp
      intro j hj
      exact hs (mem_faceCarrier.mpr ⟨w, hw, hj⟩)
    obtain ⟨t, ht, hts⟩ := e.exists_face_preimage s.property.1 hvertices
    have hne : t.Nonempty := by
      have : (t.map e.toEmbedding).Nonempty := hts.symm ▸ s.property.2
      exact Finset.map_nonempty.mp this
    refine ⟨⟨t, ht, hne⟩, ?_⟩
    exact Subtype.ext hts
  · rintro ⟨t, rfl⟩
    intro j hj
    obtain ⟨w, hw, hj⟩ := mem_faceCarrier.mp hj
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hw
    exact (h _).mpr ⟨v, rfl⟩ hj

theorem face_range_iff (e : Embedding K L) {cW : W → Finset J} {A : Finset J}
    (h : ∀ w, cW w ⊆ A ↔ ∃ v, e.toEmbedding v = w) {s : Finset W}
    (hs : s ∈ L.faces) :
    faceCarrier cW s ⊆ A ↔ ∃ t ∈ K.faces, t.map e.toEmbedding = s := by
  constructor
  · intro hsub
    apply e.exists_face_preimage hs
    intro w hw
    apply (h w).mp
    intro j hj
    exact hsub (mem_faceCarrier.mpr ⟨w, hw, hj⟩)
  · rintro ⟨t, ht, rfl⟩
    intro j hj
    obtain ⟨w, hw, hj⟩ := mem_faceCarrier.mp hj
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hw
    exact (h _).mpr ⟨v, rfl⟩ hj

end Embedding

end Tingley.FiniteComplex

end

end OAI


