-- Prove2me | Definitions.Def_OAI_Analysis_SphereIsometry_CompactConvexFixedPoint
-- name    : OAI_Analysis_SphereIsometry_CompactConvexFixedPoint
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T21:56:41.991693+00:00
-- url     : https://prove2.me/theorems/44613215-c015-4402-ba62-0f2214fed3f2
-- title:
--   Schauder's fixed point theorem for compact convex sets
-- statement:
--   These notions belong to a self-contained fixed-point toolkit used in the proof of Tingley's theorem: Sperner's lemma on iterated barycentric subdivisions, Brouwer's fixed point theorem for the probability simplex, Schauder's theorem for compact convex sets, the Kuratowski measure of noncompactness, and a Darbo–Sadovskii fixed point theorem for condensing maps. Let $K$ be a nonempty compact convex subset of a real normed space.
--
--   1. **From approximate to exact.** If $g$ is continuous on compact $K$ and has points with arbitrarily small displacement $\|x-g(x)\|$, the continuous displacement attains the minimum $0$, so $g$ has a fixed point.
--   2. **Schauder.** Every continuous $g:K\to K$ has a fixed point:
--   $$
--   g(x)=x\quad\text{for some }x\in K ,
--   $$
--   with no completeness assumption on the ambient space.
--   3. **Subtype maps.** A selfmap of the subtype $K$ is extended to the ambient space by an arbitrary value off $K$; only continuity on $K$ matters.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/SphereIsometry/CompactConvexFixedPoint.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/SphereIsometry/CompactConvexFixedPoint.lean by skeleton subtraction
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
import Definitions.Def_OAI_Analysis_SphereIsometry_Sperner
import Definitions.Def_OAI_Analysis_SphereIsometry_SimplexFixedPoint
import Definitions.Def_OAI_Analysis_SphereIsometry_CompactApproximation

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e

namespace OAI

/-!
# Compact convex fixed points

Finite-net approximate fixed points force the minimum of the continuous
displacement function to be zero. Ambient completeness is not required.
-/

noncomputable section

namespace Tingley

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
theorem exists_fixedPoint_of_isCompact_of_approximate
    {K : Set E} (hK : IsCompact K) (hne : K.Nonempty)
    {g : E → E} (hg : ContinuousOn g K)
    (happrox : ∀ δ : ℝ, 0 < δ → ∃ x ∈ K, ‖x - g x‖ < δ) :
    ∃ x ∈ K, g x = x := by
  have hd : ContinuousOn (fun x => ‖x - g x‖) K := (continuousOn_id.sub hg).norm
  obtain ⟨z, hz, hmin⟩ := hK.exists_isMinOn hne hd
  have hzero : ‖z - g z‖ = 0 := by
    by_contra hnezero
    have hpos : 0 < ‖z - g z‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm hnezero)
    obtain ⟨x, hx, hsmall⟩ := happrox ‖z - g z‖ hpos
    exact (not_lt_of_ge ((isMinOn_iff.mp hmin) x hx)) hsmall
  exact ⟨z, hz, (sub_eq_zero.mp (norm_eq_zero.mp hzero)).symm⟩

/-- The compact-convex fixed-point theorem, obtained from the explicit
finite-net coefficient map and the proved simplex theorem. -/
theorem exists_fixedPoint_of_isCompact_convex
    {K : Set E} (hK : IsCompact K) (hne : K.Nonempty) (hconv : Convex ℝ K)
    {g : E → E} (hg : ContinuousOn g K) (hmap : MapsTo g K K) :
    ∃ x ∈ K, g x = x := by
  apply exists_fixedPoint_of_isCompact_of_approximate hK hne hg
  intro δ hδ
  exact exists_approximate_fixedPoint_of_isCompact_convex hK hne hconv hg hmap hδ

/-- An explicit ambient representative of a subtype self-map. Its values
outside the subtype are immaterial; only continuity on that subtype is used. -/
def extendSelfMap {K : Set E} (g : K → K) (x : E) : E := by
  classical
  exact if hx : x ∈ K then (g ⟨x, hx⟩ : E) else x

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem extendSelfMap_of_mem {K : Set E} (g : K → K) {x : E} (hx : x ∈ K) :
    extendSelfMap g x = (g ⟨x, hx⟩ : E) := by
  simp only [extendSelfMap, dite_eq_left hx]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
@[simp] theorem extendSelfMap_coe {K : Set E} (g : K → K) (x : K) :
    extendSelfMap g (x : E) = (g x : E) :=
  extendSelfMap_of_mem g x.property

end Tingley

end

end OAI


