-- Prove2me | Definitions.Def_OAI_Analysis_SphereIsometry_Sperner
-- name    : OAI_Analysis_SphereIsometry_Sperner
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T21:51:06.090561+00:00
-- url     : https://prove2.me/theorems/e7acd88b-af8b-4218-9b6e-5588f7bc468a
-- title:
--   Sperner's lemma for iterated barycentric subdivisions
-- statement:
--   These notions belong to a self-contained fixed-point toolkit used in the proof of Tingley's theorem: Sperner's lemma on iterated barycentric subdivisions, Brouwer's fixed point theorem for the probability simplex, Schauder's theorem for compact convex sets, the Kuratowski measure of noncompactness, and a Darbo–Sadovskii fixed point theorem for condensing maps. Label each vertex $v$ of the $k$-th iterated subdivision of the $m$-simplex by a coordinate in its carrier.
--
--   1. **Odd count.** The number of fully labelled top cells (whose labels are all of $\{0,\dots,m\}$) is odd. The proof is by induction on $m$, using the incidence counts, restriction to the last face, and the double counting parity.
--   2. **Existence.** In particular there is a top cell $\sigma$ with
--   $$
--   \mathrm{label}(\sigma)=\{0,\dots,m\} .
--   $$
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/SphereIsometry/Sperner.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/SphereIsometry/Sperner.lean by skeleton subtraction
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
import Definitions.Def_OAI_Analysis_SphereIsometry_SubdivisionRestriction
import Definitions.Def_OAI_Analysis_SphereIsometry_BarycentricIncidence
import Definitions.Def_OAI_Analysis_SphereIsometry_SubdivisionIncidence
import Definitions.Def_OAI_Analysis_SphereIsometry_BarycentricZero

namespace OAI

/-!
# Geometric Sperner parity for the concrete iterated subdivisions

The labels belong to the actual recursively constructed vertex carriers.
The incidence theorem and the exact original-face restriction discharge the
finite counting hypotheses. Induction on dimension proves an odd number of
fully labelled top cells at every subdivision depth.
-/

namespace Tingley

theorem iterated_sperner_odd (m k : ℕ)
    (label : IterVertex m k → Fin (m + 1))
    (hlabel : ∀ v, label v ∈ iterCarrier m k v) :
    Odd (((topCells m k).filter
      (fun σ => σ.image label = Finset.univ)).card) := by
  classical
  induction m with
  | zero =>
      have hfull : ∀ σ ∈ topCells 0 k, σ.image label = Finset.univ := by
        intro σ hσ
        have hcard : σ.card = 1 := (mem_topCells.mp hσ).2
        have hne : σ.Nonempty := Finset.card_pos.mp (by rw [hcard]; exact Nat.zero_lt_one)
        obtain ⟨v, hv⟩ := hne
        apply Finset.eq_univ_iff_forall.mpr
        intro i
        refine Finset.mem_image.mpr ⟨v, hv, ?_⟩
        apply Fin.ext
        exact (Nat.lt_one_iff.mp (label v).isLt).trans
          (Nat.lt_one_iff.mp i.isLt).symm
      have hfilter : (topCells 0 k).filter
          (fun σ => σ.image label = Finset.univ) = topCells 0 k :=
        Finset.filter_eq_self.mpr hfull
      rw [hfilter, iter_topCells_zero_card]
      exact ⟨0, rfl⟩
  | succ m ih =>
      let e := lastFaceEmbedding m k
      have hne : ∀ v, label (e v) ≠ Fin.last (m + 1) := by
        intro v hv
        have hlast : Fin.last (m + 1) ∉ iterCarrier (m + 1) k (e v) :=
          (lastFace_range_iff m k (e v)).mpr ⟨v, rfl⟩
        exact hlast (hv ▸ hlabel (e v))
      let lowerLabel : IterVertex m k → Fin (m + 1) :=
        spernerRestrictedLabel e label hne
      have hcast : ∀ v, label (e v) = (lowerLabel v).castSucc :=
        fun v => (castSucc_spernerRestrictedLabel e label hne v).symm
      have hlower : ∀ v, lowerLabel v ∈ iterCarrier m k v := by
        apply restricted_label_mem_carrier e label hne (iterCarrier m k)
        intro v
        have h := hlabel (e v)
        change label (lastFaceEmbedding m k v) ∈
          iterCarrier (m + 1) k (lastFaceEmbedding m k v) at h
        rw [lastFace_carrier] at h
        simpa only [e, Finset.map_eq_image, Fin.coe_castSuccEmb] using h
      have hboundaryCard :
          (((codimFaces (m + 1) k).filter
            (fun τ => τ.image label = spernerSmallLabels (m + 1) ∧
              (faceCarrier (m + 1) k τ).card = m + 1)).card) =
          (((topCells m k).filter
            (fun σ => σ.image lowerLabel = Finset.univ)).card) := by
        change (((codimFaces (m + 1) k).filter
          (fun τ => τ.image label = spernerSmallLabels (m + 1) ∧
            (τ.biUnion (iterCarrier (m + 1) k)).card = m + 1)).card) = _
        rw [good_boundary_filter_eq_last_face_filter label
          (iterCarrier (m + 1) k) (codimFaces (m + 1) k) hlabel]
        exact mapped_good_family_card_of_map e label lowerLabel hcast
          (topCells m k)
          ((codimFaces (m + 1) k).filter
            (fun τ => Fin.last (m + 1) ∉ faceCarrier (m + 1) k τ))
          (lastFace_top_image m k).symm
      apply FiniteComplex.sperner_odd_of_boundary_odd
        (iterData (Fin ((m + 1) + 1)) k).complex (m + 1) label
        (fun τ => (faceCarrier (m + 1) k τ).card = m + 1)
      · intro τ hτ
        exact incidentTop_card_eq_if_boundary (Nat.succ_pos m) hτ
      · change Odd (((codimFaces (m + 1) k).filter
          (fun τ => τ.image label = spernerSmallLabels (m + 1) ∧
            (faceCarrier (m + 1) k τ).card = m + 1)).card)
        rw [hboundaryCard]
        exact ih lowerLabel hlower

/-- Each actual subdivision contains an actual fully labelled top cell. -/
theorem iterated_sperner_exists (m k : ℕ)
    (label : IterVertex m k → Fin (m + 1))
    (hlabel : ∀ v, label v ∈ iterCarrier m k v) :
    ∃ σ, σ ∈ topCells m k ∧ σ.image label = Finset.univ := by
  classical
  have hodd := iterated_sperner_odd m k label hlabel
  have hcard : ((topCells m k).filter
      (fun σ => σ.image label = Finset.univ)).card ≠ 0 := by
    intro hzero
    rw [hzero] at hodd
    simp at hodd
  obtain ⟨σ, hσ⟩ := Finset.card_ne_zero.mp hcard
  exact ⟨σ, (Finset.mem_filter.mp hσ).1, (Finset.mem_filter.mp hσ).2⟩

end Tingley

end OAI


