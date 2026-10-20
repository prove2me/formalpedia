-- Prove2me | Definitions.Def_OAI_Analysis_SphereIsometry_SubdivisionRestriction
-- name    : OAI_Analysis_SphereIsometry_SubdivisionRestriction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T21:45:24.466237+00:00
-- url     : https://prove2.me/theorems/a8c363c7-5ef7-4031-a29b-17da5dc2b14f
-- title:
--   Restricting iterated subdivisions to the last face
-- statement:
--   These notions belong to a self-contained fixed-point toolkit used in the proof of Tingley's theorem: Sperner's lemma on iterated barycentric subdivisions, Brouwer's fixed point theorem for the probability simplex, Schauder's theorem for compact convex sets, the Kuratowski measure of noncompactness, and a Darbo–Sadovskii fixed point theorem for condensing maps.
--
--   1. **Iterated embeddings.** A coordinate embedding $e:I\to J$ induces embeddings of the $k$-th iterated subdivisions. They are compatible with carriers, and a face of the larger subdivision is in the image iff its carrier lies in $e(I)$.
--   2. **Last face.** For $I=\{0,\dots,m\}\subset J=\{0,\dots,m+1\}$, this embeds the level-$k$ subdivision of the $m$-simplex onto the faces of the $(m+1)$-dimensional one whose carrier omits the last coordinate. Top cells map to codimension-one faces lying on that boundary face:
--   $$
--   \{\text{top cells of dim }m\}\ \longleftrightarrow\ \{\text{codim-one faces with carrier}\subseteq\{0..m\}\}.
--   $$
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/SphereIsometry/SubdivisionRestriction.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/SphereIsometry/SubdivisionRestriction.lean by skeleton subtraction
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
import Definitions.Def_OAI_Analysis_SphereIsometry_BarycentricRestriction

namespace OAI

/-! # The exact original-face restriction of every concrete subdivision -/

noncomputable section

namespace Tingley

variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

def iterEmbedding (e : I ↪ J) : (k : ℕ) →
    FiniteComplex.Embedding (iterData I k).complex (iterData J k).complex
  | 0 => FiniteComplex.Embedding.full e
  | k + 1 => (iterEmbedding e k).sd

theorem iterEmbedding_carrier (e : I ↪ J) (k : ℕ)
    (v : (iterData I k).Vertex) :
    (iterData J k).carrier ((iterEmbedding e k).toEmbedding v) =
      ((iterData I k).carrier v).map e := by
  induction k with
  | zero =>
      change I at v
      change ({e v} : Finset J) = ({v} : Finset I).map e
      exact (Finset.map_singleton e v).symm
  | succ k ih =>
      exact (iterEmbedding e k).sdCarrier_faceMap e ih v

theorem iterEmbedding_range_iff (e : I ↪ J) (k : ℕ)
    (v : (iterData J k).Vertex) :
    (iterData J k).carrier v ⊆ Finset.univ.map e ↔
      ∃ w, (iterEmbedding e k).toEmbedding w = v := by
  induction k with
  | zero =>
      change J at v
      change ({v} : Finset J) ⊆ Finset.univ.map e ↔ ∃ w : I, e w = v
      simp only [Finset.singleton_subset_iff, Finset.mem_map,
        Finset.mem_univ, true_and]
  | succ k ih => exact (iterEmbedding e k).faceMap_range_iff ih v

theorem iterEmbedding_faceCarrier (e : I ↪ J) (k : ℕ)
    (s : Finset (iterData I k).Vertex) :
    FiniteComplex.faceCarrier (iterData J k).carrier
        (s.map (iterEmbedding e k).toEmbedding) =
      (FiniteComplex.faceCarrier (iterData I k).carrier s).map e :=
  (iterEmbedding e k).faceCarrier_map e (iterEmbedding_carrier e k) s

theorem iterEmbedding_face_range_iff (e : I ↪ J) (k : ℕ)
    {s : Finset (iterData J k).Vertex} (hs : s ∈ (iterData J k).complex.faces) :
    FiniteComplex.faceCarrier (iterData J k).carrier s ⊆ Finset.univ.map e ↔
      ∃ t ∈ (iterData I k).complex.faces, t.map (iterEmbedding e k).toEmbedding = s :=
  (iterEmbedding e k).face_range_iff (iterEmbedding_range_iff e k) hs

def lastFaceEmbedding (m k : ℕ) : IterVertex m k ↪ IterVertex (m + 1) k :=
  (iterEmbedding (Fin.castSuccEmb : Fin (m + 1) ↪ Fin ((m + 1) + 1)) k).toEmbedding

theorem lastFace_carrier (m k : ℕ) (v : IterVertex m k) :
    iterCarrier (m + 1) k (lastFaceEmbedding m k v) =
      (iterCarrier m k v).map Fin.castSuccEmb :=
  iterEmbedding_carrier Fin.castSuccEmb k v

theorem lastFace_faceCarrier (m k : ℕ) (s : Finset (IterVertex m k)) :
    faceCarrier (m + 1) k (s.map (lastFaceEmbedding m k)) =
      (faceCarrier m k s).map Fin.castSuccEmb :=
  iterEmbedding_faceCarrier Fin.castSuccEmb k s

theorem lastFace_range_iff (m k : ℕ) (v : IterVertex (m + 1) k) :
    Fin.last (m + 1) ∉ iterCarrier (m + 1) k v ↔
      ∃ w, lastFaceEmbedding m k w = v := by
  have h := iterEmbedding_range_iff
    (Fin.castSuccEmb : Fin (m + 1) ↪ Fin ((m + 1) + 1)) k v
  simpa only [iterCarrier, lastFaceEmbedding, Finset.map_eq_image,
    Fin.coe_castSuccEmb, Fin.image_castSucc, Finset.subset_compl_singleton] using h

theorem lastFace_mem_iff (m k : ℕ) (s : Finset (IterVertex m k)) :
    s.map (lastFaceEmbedding m k) ∈ iterComplex (m + 1) k ↔ s ∈ iterComplex m k :=
  (iterEmbedding Fin.castSuccEmb k).map_mem_iff s

theorem lastFace_face_range_iff {m k : ℕ} {s : Finset (IterVertex (m + 1) k)}
    (hs : s ∈ iterComplex (m + 1) k) :
    Fin.last (m + 1) ∉ faceCarrier (m + 1) k s ↔
      ∃ t ∈ iterComplex m k, t.map (lastFaceEmbedding m k) = s := by
  have h := iterEmbedding_face_range_iff
    (Fin.castSuccEmb : Fin (m + 1) ↪ Fin ((m + 1) + 1)) k hs
  simpa only [faceCarrier, iterCarrier, iterComplex, lastFaceEmbedding,
    Finset.map_eq_image, Fin.coe_castSuccEmb, Fin.image_castSucc,
    Finset.subset_compl_singleton] using h

theorem lastFace_map_top_mem (m k : ℕ) {s : Finset (IterVertex m k)}
    (hs : s ∈ topCells m k) :
    s.map (lastFaceEmbedding m k) ∈ codimFaces (m + 1) k := by
  obtain ⟨hsface, hscard⟩ := mem_topCells.mp hs
  exact mem_codimFaces.mpr ⟨(lastFace_mem_iff m k s).mpr hsface, by simpa using hscard⟩

theorem lastFace_top_image (m k : ℕ) :
    (topCells m k).map (Finset.mapEmbedding (lastFaceEmbedding m k)).toEmbedding =
      (codimFaces (m + 1) k).filter
        (fun s => Fin.last (m + 1) ∉ faceCarrier (m + 1) k s) := by
  ext s
  constructor
  · intro hs
    obtain ⟨t, ht, rfl⟩ := Finset.mem_map.mp hs
    apply Finset.mem_filter.mpr
    refine ⟨lastFace_map_top_mem m k ht, ?_⟩
    change Fin.last (m + 1) ∉ faceCarrier (m + 1) k (t.map (lastFaceEmbedding m k))
    rw [lastFace_faceCarrier]
    simp only [Finset.mem_map, not_exists, not_and]
    intro i hi
    exact Fin.castSucc_ne_last i
  · intro hs
    obtain ⟨hscodim, hboundary⟩ := Finset.mem_filter.mp hs
    obtain ⟨hsface, hscard⟩ := mem_codimFaces.mp hscodim
    obtain ⟨t, htface, hts⟩ := (lastFace_face_range_iff hsface).mp hboundary
    apply Finset.mem_map.mpr
    refine ⟨t, mem_topCells.mpr ⟨htface, ?_⟩, hts⟩
    have hcard := congrArg Finset.card hts
    simpa [hscard] using hcard

end Tingley

end

end OAI


