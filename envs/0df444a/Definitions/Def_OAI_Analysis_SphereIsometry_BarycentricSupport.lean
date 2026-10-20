-- Prove2me | Definitions.Def_OAI_Analysis_SphereIsometry_BarycentricSupport
-- name    : OAI_Analysis_SphereIsometry_BarycentricSupport
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T21:29:36.925852+00:00
-- url     : https://prove2.me/theorems/ce2a71e1-5f3c-4c3d-bfa8-3a9b5a6e3d90
-- title:
--   Supports of barycenters of simplex points
-- statement:
--   These notions belong to a self-contained fixed-point toolkit used in the proof of Tingley's theorem: Sperner's lemma on iterated barycentric subdivisions, Brouwer's fixed point theorem for the probability simplex, Schauder's theorem for compact convex sets, the Kuratowski measure of noncompactness, and a Darbo–Sadovskii fixed point theorem for condensing maps.
--
--   1. **Positive carrier.** For $x\in\mathbb R^\iota$, $\{i:\ x_i>0\}$.
--   2. **Averages.** If $S$ is nonempty and every $p(v)$, $v\in S$, lies in the probability simplex, so does the barycenter $b(S)$. Its positive coordinates are exactly
--   $$
--   \{i:\ b(S)_i>0\}=\bigcup_{v\in S}\{i:\ p(v)_i>0\} .
--   $$
--   So iterated barycenters have carriers equal to the unions of the old carriers.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/SphereIsometry/BarycentricSupport.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/SphereIsometry/BarycentricSupport.lean by skeleton subtraction
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

namespace OAI

/-!
# Supports of finite barycenters

A nonempty average of simplex vectors is a simplex vector. Its strict-positive
coordinate support is exactly the union of the supports being averaged.
These statements concern the actual finite average and require no geometric
coverage assumption.
-/

noncomputable section

open scoped BigOperators Classical

namespace Tingley

variable {V ι : Type*} [Fintype ι]

/-- The coordinates at which a vector is strictly positive. -/
def positiveCarrier (x : ι → ℝ) : Finset ι :=
  Finset.univ.filter (fun i => 0 < x i)

@[simp] theorem mem_positiveCarrier {x : ι → ℝ} {i : ι} :
    i ∈ positiveCarrier x ↔ 0 < x i := by
  simp [positiveCarrier]

/-- A nonempty finite average stays in the standard simplex. -/
theorem finiteBarycenter_mem_stdSimplex (p : V → ι → ℝ) {S : Finset V}
    (hs : S.Nonempty) (hp : ∀ v ∈ S, p v ∈ probabilitySimplexSet ι) :
    finiteBarycenter p S ∈ probabilitySimplexSet ι := by
  exact finiteBarycenter_mem_convex (convex_probabilitySimplexSet ι) hs hp

/-- A coordinate of a nonempty nonnegative average is positive exactly when
one of the averaged coordinates is positive. -/
theorem finiteBarycenter_pos_iff (p : V → ι → ℝ) {S : Finset V}
    (hs : S.Nonempty) (hp : ∀ v ∈ S, ∀ i, 0 ≤ p v i) (i : ι) :
    0 < finiteBarycenter p S i ↔ ∃ v ∈ S, 0 < p v i := by
  have hcard : 0 < (S.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hs)
  have hinv : 0 < (S.card : ℝ)⁻¹ := inv_pos.mpr hcard
  rw [finiteBarycenter_apply]
  constructor
  · intro h
    have hsum : 0 < ∑ v ∈ S, p v i := pos_of_mul_pos_right h hinv.le
    by_contra hn
    have hzero : ∀ v ∈ S, p v i = 0 := by
      intro v hv
      apply le_antisymm _ (hp v hv i)
      exact le_of_not_gt (fun hpos => hn ⟨v, hv, hpos⟩)
    have heq : ∑ v ∈ S, p v i = 0 := Finset.sum_eq_zero hzero
    rw [heq] at hsum
    exact (lt_irrefl (0 : ℝ)) hsum
  · intro h
    exact mul_pos hinv (Finset.sum_pos' (fun v hv => hp v hv i) h)

/-- The support of a nonempty nonnegative average is the exact support union. -/
theorem positiveCarrier_finiteBarycenter (p : V → ι → ℝ) {S : Finset V}
    (hs : S.Nonempty) (hp : ∀ v ∈ S, ∀ i, 0 ≤ p v i) :
    positiveCarrier (finiteBarycenter p S) =
      S.biUnion (fun v => positiveCarrier (p v)) := by
  ext i
  simp only [mem_positiveCarrier, Finset.mem_biUnion]
  exact finiteBarycenter_pos_iff p hs hp i

end Tingley

end

end OAI


