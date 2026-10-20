-- Prove2me | Definitions.Def_OAI_Analysis_SphereIsometry_SpernerIncidence
-- name    : OAI_Analysis_SphereIsometry_SpernerIncidence
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T21:42:04.611983+00:00
-- url     : https://prove2.me/theorems/3c91e6ae-a601-46c6-8c05-52b714b52fee
-- title:
--   Double counting for Sperner's lemma
-- statement:
--   These notions belong to a self-contained fixed-point toolkit used in the proof of Tingley's theorem: Sperner's lemma on iterated barycentric subdivisions, Brouwer's fixed point theorem for the probability simplex, Schauder's theorem for compact convex sets, the Kuratowski measure of noncompactness, and a Darbo–Sadovskii fixed point theorem for condensing maps. Let $K$ be a finite complex of dimension $m$ with labels on its vertices, and a boundary predicate on codimension-one faces.
--
--   1. **Good facets as faces.** The good facets of a top cell are the codimension-one faces of $K$ inside it with small-label image.
--   2. **Parity count.** Suppose every boundary codimension-one face lies in exactly one top cell and every interior one in exactly two. Counting pairs (top cell, good facet) in two orders gives
--   $$
--   \#\{\text{fully labelled top cells}\}\equiv\#\{\text{good boundary facets}\}\pmod2 .
--   $$
--   3. **Oddness.** An odd number of good boundary facets forces an odd, hence nonzero, number of fully labelled top cells.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/SphereIsometry/SpernerIncidence.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/SphereIsometry/SpernerIncidence.lean by skeleton subtraction
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

namespace OAI

/-!
# Counting labelled incidences in a finite complex

The two orders of summation count the same actual top-cell/facet pairs. Local
facet parity leaves the fully labelled top cells on one side. Degree two
facets cancel on the other side, leaving only the degree one boundary facets.
-/

open scoped BigOperators

namespace Tingley.FiniteComplex

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem goodFacets_eq_codim_filter (K : FiniteComplex V) (m : ℕ)
    (label : V → Fin (m + 1)) {σ : Finset V} (hσ : σ ∈ K.topCells m) :
    (K.codimFaces m).filter
        (fun τ => τ ⊆ σ ∧ τ.image label = spernerSmallLabels m) =
      spernerGoodFacets m label σ := by
  classical
  ext τ
  rw [Finset.mem_filter, mem_spernerGoodFacets]
  constructor
  · rintro ⟨hτ, hsub, hlabel⟩
    exact ⟨hsub, (mem_codimFaces.mp hτ).2, hlabel⟩
  · rintro ⟨hsub, hcard, hlabel⟩
    exact ⟨mem_codimFaces.mpr
      ⟨K.down_closed (mem_topCells.mp hσ).1 hsub, hcard⟩, hsub, hlabel⟩

/-- Finite incidence parity, before the boundary restriction is identified with
the lower-dimensional simplex. All hypotheses concern finite face incidence. -/
theorem sperner_count_mod_two (K : FiniteComplex V) (m : ℕ)
    (label : V → Fin (m + 1)) (boundary : Finset V → Prop)
    [DecidablePred boundary]
    (hdegree : ∀ τ ∈ K.codimFaces m,
      (K.incidentTop m τ).card = if boundary τ then 1 else 2) :
    (((K.topCells m).filter (fun σ => σ.image label = Finset.univ)).card : ZMod 2) =
      (((K.codimFaces m).filter
        (fun τ => τ.image label = spernerSmallLabels m ∧ boundary τ)).card : ZMod 2) := by
  classical
  have hrow : ∀ σ ∈ K.topCells m,
      (∑ τ ∈ K.codimFaces m,
        if τ ⊆ σ ∧ τ.image label = spernerSmallLabels m then (1 : ZMod 2) else 0) =
      if σ.image label = Finset.univ then 1 else 0 := by
    intro σ hσ
    rw [Finset.sum_boole, goodFacets_eq_codim_filter K m label hσ]
    exact spernerGoodFacets_card_mod_two label σ (mem_topCells.mp hσ).2
  have hcolumn : ∀ τ ∈ K.codimFaces m,
      (∑ σ ∈ K.topCells m,
        if τ ⊆ σ ∧ τ.image label = spernerSmallLabels m then (1 : ZMod 2) else 0) =
      if τ.image label = spernerSmallLabels m ∧ boundary τ then 1 else 0 := by
    intro τ hτ
    by_cases hg : τ.image label = spernerSmallLabels m
    · simp only [hg, and_true, true_and]
      rw [Finset.sum_boole]
      change ((K.incidentTop m τ).card : ZMod 2) = if boundary τ then 1 else 0
      rw [hdegree τ hτ]
      by_cases hb : boundary τ
      · simp [hb]
      · simp only [hb, ite_false]
        exact ZMod.natCast_self 2
    · simp [hg]
  calc
    (((K.topCells m).filter (fun σ => σ.image label = Finset.univ)).card : ZMod 2) =
        ∑ σ ∈ K.topCells m,
          if σ.image label = Finset.univ then (1 : ZMod 2) else 0 :=
      Finset.natCast_card_filter _ _
    _ = ∑ σ ∈ K.topCells m, ∑ τ ∈ K.codimFaces m,
          if τ ⊆ σ ∧ τ.image label = spernerSmallLabels m then (1 : ZMod 2) else 0 :=
      Finset.sum_congr rfl (fun σ hσ => (hrow σ hσ).symm)
    _ = ∑ τ ∈ K.codimFaces m, ∑ σ ∈ K.topCells m,
          if τ ⊆ σ ∧ τ.image label = spernerSmallLabels m then (1 : ZMod 2) else 0 :=
      Finset.sum_comm
    _ = ∑ τ ∈ K.codimFaces m,
          if τ.image label = spernerSmallLabels m ∧ boundary τ then (1 : ZMod 2) else 0 :=
      Finset.sum_congr rfl hcolumn
    _ = (((K.codimFaces m).filter
          (fun τ => τ.image label = spernerSmallLabels m ∧ boundary τ)).card : ZMod 2) :=
      Finset.sum_boole _ _

/-- An odd number of good boundary facets gives an odd number of fully labelled cells. -/
theorem sperner_odd_of_boundary_odd (K : FiniteComplex V) (m : ℕ)
    (label : V → Fin (m + 1)) (boundary : Finset V → Prop)
    [DecidablePred boundary]
    (hdegree : ∀ τ ∈ K.codimFaces m,
      (K.incidentTop m τ).card = if boundary τ then 1 else 2)
    (hboundary : Odd (((K.codimFaces m).filter
      (fun τ => τ.image label = spernerSmallLabels m ∧ boundary τ)).card)) :
    Odd (((K.topCells m).filter (fun σ => σ.image label = Finset.univ)).card) := by
  apply ZMod.natCast_eq_one_iff_odd.mp
  rw [sperner_count_mod_two K m label boundary hdegree]
  exact ZMod.natCast_eq_one_iff_odd.mpr hboundary

end Tingley.FiniteComplex

end OAI


