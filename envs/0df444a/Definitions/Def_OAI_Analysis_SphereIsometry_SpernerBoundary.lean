-- Prove2me | Definitions.Def_OAI_Analysis_SphereIsometry_SpernerBoundary
-- name    : OAI_Analysis_SphereIsometry_SpernerBoundary
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T21:42:53.535995+00:00
-- url     : https://prove2.me/theorems/6d710f41-4cd7-42f1-a8e7-758ee5c5c0a6
-- title:
--   Sperner labels on the boundary face
-- statement:
--   These notions belong to a self-contained fixed-point toolkit used in the proof of Tingley's theorem: Sperner's lemma on iterated barycentric subdivisions, Brouwer's fixed point theorem for the probability simplex, Schauder's theorem for compact convex sets, the Kuratowski measure of noncompactness, and a Darbo–Sadovskii fixed point theorem for condensing maps. Vertices carry carriers $\subseteq\{0,\dots,m\}$, and labels are admissible if each vertex's label lies in its carrier.
--
--   1. **Carrier containment.** The labels of a face lie in its carrier.
--   2. **Boundary facets.** A good facet on the boundary must have carrier exactly $\{0,\dots,m-1\}$, i.e. it lies on the face omitting the last coordinate.
--   3. **Restricted labels.** On an embedded lower-dimensional face, labels avoid the last coordinate and can be reindexed into $\{0,\dots,m-1\}$. Embedded faces are good exactly when the lower-dimensional faces are fully labelled. The good-face count is preserved, which feeds the induction on dimension.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/SphereIsometry/SpernerBoundary.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/SphereIsometry/SpernerBoundary.lean by skeleton subtraction
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

namespace OAI

/-!
# Boundary labels and restriction of the finite Sperner count

Admissible labels lie in the union of the vertex carriers. A good boundary
facet therefore has exactly the carrier omitting the last coordinate. Mapping
lower-dimensional faces through a vertex embedding preserves the label count
after the coordinate embedding `Fin.castSucc`.
-/

namespace Tingley

variable {V W I : Type*} [DecidableEq V] [DecidableEq W] [DecidableEq I]

omit [DecidableEq V] in
/-- Vertexwise carrier membership implies membership in the face carrier. -/
theorem sperner_label_image_subset_carrier (label : V → I)
    (carrier : V → Finset I) (σ : Finset V)
    (hlabel : ∀ v ∈ σ, label v ∈ carrier v) :
    σ.image label ⊆ σ.biUnion carrier := by
  intro i hi
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hi
  exact Finset.mem_biUnion.mpr ⟨v, hv, hlabel v hv⟩

omit [DecidableEq V] in
/-- A good boundary facet can only lie on the original face missing the last
coordinate. The conclusion follows from containment and equal cardinality. -/
theorem carrier_eq_spernerSmallLabels {m : ℕ} (label : V → Fin (m + 1))
    (carrier : V → Finset (Fin (m + 1))) (σ : Finset V)
    (hlabel : ∀ v ∈ σ, label v ∈ carrier v)
    (hgood : σ.image label = spernerSmallLabels m)
    (hcard : (σ.biUnion carrier).card = m) :
    σ.biUnion carrier = spernerSmallLabels m := by
  have hsub : spernerSmallLabels m ⊆ σ.biUnion carrier := by
    rw [← hgood]
    exact sperner_label_image_subset_carrier label carrier σ hlabel
  exact (Finset.eq_of_subset_of_card_le hsub
    (by rw [hcard, card_spernerSmallLabels])).symm

omit [DecidableEq V] in
/-- For a good face, the boundary cardinality condition is equivalent to
omission of the last coordinate from its carrier. -/
theorem good_carrier_card_iff_last_not_mem {m : ℕ} (label : V → Fin (m + 1))
    (carrier : V → Finset (Fin (m + 1))) (σ : Finset V)
    (hlabel : ∀ v ∈ σ, label v ∈ carrier v)
    (hgood : σ.image label = spernerSmallLabels m) :
    (σ.biUnion carrier).card = m ↔ Fin.last m ∉ σ.biUnion carrier := by
  constructor
  · intro hcard
    rw [carrier_eq_spernerSmallLabels label carrier σ hlabel hgood hcard]
    simp
  · intro hlast
    have hsub : σ.biUnion carrier ⊆ spernerSmallLabels m := by
      intro i hi
      apply mem_spernerSmallLabels.mpr
      intro hilast
      exact hlast (hilast ▸ hi)
    have hsup : spernerSmallLabels m ⊆ σ.biUnion carrier := by
      rw [← hgood]
      exact sperner_label_image_subset_carrier label carrier σ hlabel
    rw [Finset.Subset.antisymm hsub hsup, card_spernerSmallLabels]

omit [DecidableEq V] in
/-- Among good faces, all boundary faces are exactly those on the last face.
This is the filter identity used before transporting the incidence count. -/
theorem good_boundary_filter_eq_last_face_filter {m : ℕ}
    (label : V → Fin (m + 1)) (carrier : V → Finset (Fin (m + 1)))
    (faces : Finset (Finset V)) (hlabel : ∀ v, label v ∈ carrier v) :
    faces.filter (fun σ => σ.image label = spernerSmallLabels m ∧
        (σ.biUnion carrier).card = m) =
      (faces.filter (fun σ => Fin.last m ∉ σ.biUnion carrier)).filter
        (fun σ => σ.image label = spernerSmallLabels m) := by
  classical
  ext σ
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hσ, hg, hc⟩
    exact ⟨⟨hσ, (good_carrier_card_iff_last_not_mem label carrier σ
      (fun v _ => hlabel v) hg).mp hc⟩, hg⟩
  · rintro ⟨⟨hσ, hl⟩, hg⟩
    exact ⟨hσ, hg, (good_carrier_card_iff_last_not_mem label carrier σ
      (fun v _ => hlabel v) hg).mpr hl⟩

/-- Remove the last coordinate from labels on an embedded boundary face. -/
def spernerRestrictedLabel {n : ℕ} (e : W ↪ V) (label : V → Fin (n + 1))
    (hne : ∀ w, label (e w) ≠ Fin.last n) : W → Fin n :=
  fun w => (label (e w)).castPred (hne w)

omit [DecidableEq V] [DecidableEq W] in
@[simp] theorem castSucc_spernerRestrictedLabel {n : ℕ} (e : W ↪ V)
    (label : V → Fin (n + 1)) (hne : ∀ w, label (e w) ≠ Fin.last n) (w : W) :
    (spernerRestrictedLabel e label hne w).castSucc = label (e w) :=
  Fin.castSucc_castPred _ _

/-- The smaller label set is exactly the image of the smaller coordinate type. -/
theorem image_univ_castSucc_eq_spernerSmallLabels (n : ℕ) :
    (Finset.univ : Finset (Fin n)).image Fin.castSucc = spernerSmallLabels n := by
  ext i
  constructor
  · intro hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
    exact mem_spernerSmallLabels.mpr j.castSucc_ne_last
  · intro hi
    obtain ⟨j, hj⟩ := Fin.eq_castSucc_of_ne_last (mem_spernerSmallLabels.mp hi)
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj⟩

omit [DecidableEq W] in
/-- Compatible vertex and coordinate embeddings commute with the label image. -/
theorem mapped_label_image_eq {n : ℕ} (e : W ↪ V)
    (label : V → Fin (n + 1)) (lowerLabel : W → Fin n)
    (hlabel : ∀ w, label (e w) = (lowerLabel w).castSucc) (σ : Finset W) :
    (σ.map e).image label = (σ.image lowerLabel).image Fin.castSucc := by
  rw [Finset.map_eq_image, Finset.image_image, Finset.image_image]
  apply Finset.image_congr
  intro w _
  exact hlabel w

omit [DecidableEq W] in
/-- A mapped face is good exactly when its lower-dimensional face is full. -/
theorem mapped_fully_labelled_iff {n : ℕ} (e : W ↪ V)
    (label : V → Fin (n + 1)) (lowerLabel : W → Fin n)
    (hlabel : ∀ w, label (e w) = (lowerLabel w).castSucc) (σ : Finset W) :
    (σ.map e).image label = spernerSmallLabels n ↔
      σ.image lowerLabel = Finset.univ := by
  rw [mapped_label_image_eq e label lowerLabel hlabel σ,
    ← image_univ_castSucc_eq_spernerSmallLabels n]
  exact Finset.image_inj (Fin.castSucc_injective n)

omit [DecidableEq V] [DecidableEq W] in
/-- Restricting an admissible embedded label preserves membership in the
lower-dimensional carrier. -/
theorem restricted_label_mem_carrier {n : ℕ} (e : W ↪ V)
    (label : V → Fin (n + 1)) (hne : ∀ w, label (e w) ≠ Fin.last n)
    (carrier : W → Finset (Fin n))
    (hlabel : ∀ w, label (e w) ∈ (carrier w).image Fin.castSucc) (w : W) :
    spernerRestrictedLabel e label hne w ∈ carrier w := by
  obtain ⟨i, hi, hieq⟩ := Finset.mem_image.mp (hlabel w)
  have heq : i = spernerRestrictedLabel e label hne w :=
    Fin.castSucc_injective n
      (hieq.trans (castSucc_spernerRestrictedLabel e label hne w).symm)
  simpa only [heq] using hi

omit [DecidableEq W] in
/-- A finite family of faces can be filtered before or after an injective
vertex map, without changing its cardinality. -/
theorem mapped_family_filter_card (e : W ↪ V)
    (lowerFamily : Finset (Finset W)) (higherFamily : Finset (Finset V))
    (p : Finset W → Prop) (q : Finset V → Prop)
    [DecidablePred p] [DecidablePred q]
    (hfamily : higherFamily = lowerFamily.image (fun σ => σ.map e))
    (hpred : ∀ σ ∈ lowerFamily, q (σ.map e) ↔ p σ) :
    (higherFamily.filter q).card = (lowerFamily.filter p).card := by
  classical
  have hfilter : lowerFamily.filter (fun σ => q (σ.map e)) = lowerFamily.filter p :=
    Finset.filter_congr hpred
  rw [hfamily, Finset.filter_image, hfilter]
  exact Finset.card_image_of_injective _ (Finset.map_injective e)

omit [DecidableEq W] in
/-- Exact transport of the good-face count under a raw face-family bijection. -/
theorem mapped_good_family_card {n : ℕ} (e : W ↪ V)
    (label : V → Fin (n + 1)) (lowerLabel : W → Fin n)
    (hlabel : ∀ w, label (e w) = (lowerLabel w).castSucc)
    (lowerFamily : Finset (Finset W)) (higherFamily : Finset (Finset V))
    (hfamily : higherFamily = lowerFamily.image (fun σ => σ.map e)) :
    (higherFamily.filter (fun τ => τ.image label = spernerSmallLabels n)).card =
      (lowerFamily.filter (fun σ => σ.image lowerLabel = Finset.univ)).card := by
  classical
  exact mapped_family_filter_card e lowerFamily higherFamily _ _ hfamily
    (fun σ _ => mapped_fully_labelled_iff e label lowerLabel hlabel σ)

omit [DecidableEq W] in
/-- Count transport in the `Finset.map` form produced by the subdivision
restriction theorem. -/
theorem mapped_good_family_card_of_map {n : ℕ} (e : W ↪ V)
    (label : V → Fin (n + 1)) (lowerLabel : W → Fin n)
    (hlabel : ∀ w, label (e w) = (lowerLabel w).castSucc)
    (lowerFamily : Finset (Finset W)) (higherFamily : Finset (Finset V))
    (hfamily : higherFamily = lowerFamily.map (Finset.mapEmbedding e).toEmbedding) :
    (higherFamily.filter (fun τ => τ.image label = spernerSmallLabels n)).card =
      (lowerFamily.filter (fun σ => σ.image lowerLabel = Finset.univ)).card := by
  classical
  apply mapped_good_family_card e label lowerLabel hlabel lowerFamily higherFamily
  calc
    higherFamily = lowerFamily.map (Finset.mapEmbedding e).toEmbedding := hfamily
    _ = lowerFamily.image (fun σ => σ.map e) := Finset.map_eq_image _ _

end Tingley

end OAI


