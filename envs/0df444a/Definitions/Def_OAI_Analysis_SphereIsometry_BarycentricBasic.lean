-- Prove2me | Definitions.Def_OAI_Analysis_SphereIsometry_BarycentricBasic
-- name    : OAI_Analysis_SphereIsometry_BarycentricBasic
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T21:28:31.079988+00:00
-- url     : https://prove2.me/theorems/b7b53485-1036-410d-bf07-1e002724f669
-- title:
--   Barycenters of finite faces
-- statement:
--   These notions belong to a self-contained fixed-point toolkit used in the proof of Tingley's theorem: Sperner's lemma on iterated barycentric subdivisions, Brouwer's fixed point theorem for the probability simplex, Schauder's theorem for compact convex sets, the Kuratowski measure of noncompactness, and a Darbo–Sadovskii fixed point theorem for condensing maps. Let $p:V\to E$ assign points of a real vector space to vertices.
--
--   1. **Finite barycenter.** For a finite set $S$ of vertices,
--   $$
--   b(S)=\frac1{|S|}\sum_{v\in S}p(v),
--   $$
--   which is $0$ for $S=\varnothing$. It is the center of mass with equal weights. For nonempty $S$ it lies in every convex set containing all $p(v)$, $v\in S$, and in the convex hull of $p(T)$ for $S\subseteq T$. Its coordinates are the averages of the coordinates.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/SphereIsometry/BarycentricBasic.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/SphereIsometry/BarycentricBasic.lean by skeleton subtraction
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

namespace OAI

/-!
# Finite barycenters

The point attached to a nonempty face in barycentric subdivision is its
ordinary finite average. The definition also assigns zero to the empty set.
-/

noncomputable section

open scoped BigOperators

namespace Tingley

variable {V W E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

def finiteBarycenter (p : V → E) (S : Finset V) : E :=
  (S.card : ℝ)⁻¹ • ∑ v ∈ S, p v

theorem finiteBarycenter_eq_centerMass (p : V → E) (S : Finset V) :
    finiteBarycenter p S = S.centerMass (fun _ => (1 : ℝ)) p := by
  simp [finiteBarycenter, Finset.centerMass]

@[simp] theorem finiteBarycenter_empty (p : V → E) :
    finiteBarycenter p ∅ = 0 := by
  simp [finiteBarycenter]

@[simp] theorem finiteBarycenter_singleton (p : V → E) (v : V) :
    finiteBarycenter p {v} = p v := by
  simp [finiteBarycenter]

theorem finiteBarycenter_mem_convex {K : Set E} (hK : Convex ℝ K)
    {p : V → E} {S : Finset V} (hs : S.Nonempty)
    (hp : ∀ v ∈ S, p v ∈ K) : finiteBarycenter p S ∈ K := by
  rw [finiteBarycenter_eq_centerMass]
  apply hK.centerMass_mem
  · intro v hv
    exact zero_le_one
  · simpa using (Nat.cast_pos.mpr (Finset.card_pos.mpr hs) : 0 < (S.card : ℝ))
  · exact hp

theorem finiteBarycenter_mem_convexHull {p : V → E} {S T : Finset V}
    (hs : S.Nonempty) (hst : S ⊆ T) :
    finiteBarycenter p S ∈ convexHull ℝ (p '' (↑T : Set V)) := by
  apply finiteBarycenter_mem_convex (convex_convexHull ℝ _) hs
  intro v hv
  exact subset_convexHull ℝ _ ⟨v, hst hv, rfl⟩

theorem finiteBarycenter_apply {ι : Type*} [Fintype ι]
    (p : V → ι → ℝ) (S : Finset V) (i : ι) :
    finiteBarycenter p S i = (S.card : ℝ)⁻¹ * ∑ v ∈ S, p v i := by
  simp [finiteBarycenter, Finset.sum_apply]

end Tingley

end

end OAI


