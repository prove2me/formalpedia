-- Prove2me | Definitions.Def_OAI_Analysis_SphereIsometry_KuratowskiTotalBounded
-- name    : OAI_Analysis_SphereIsometry_KuratowskiTotalBounded
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T22:06:29.608119+00:00
-- url     : https://prove2.me/theorems/838b5649-e18a-4764-bd06-9d86c3f5ccba
-- title:
--   Kuratowski covers and total boundedness
-- statement:
--   These notions belong to a self-contained fixed-point toolkit used in the proof of Tingley's theorem: Sperner's lemma on iterated barycentric subdivisions, Brouwer's fixed point theorem for the probability simplex, Schauder's theorem for compact convex sets, the Kuratowski measure of noncompactness, and a Darbo–Sadovskii fixed point theorem for condensing maps. Let $E$ be a metric space.
--
--   1. **Total boundedness.** $H$ is totally bounded iff for every $\varepsilon>0$ it has a finite cover by sets of diameter at most $\varepsilon$, i.e.
--   $$
--   \chi(H)=0\iff H\text{ totally bounded}\quad(H\text{ bounded}).
--   $$
--   2. **Selected sequences.** Let $F_0\supseteq F_1\supseteq\dots$ be such that for every $\varepsilon>0$ some late $F_n$ has a finite cover of diameter $\varepsilon$. Then a sequence with $x_n\in F_n$ has totally bounded range: finitely many early points together with a fine cover of a late member cover it.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/SphereIsometry/KuratowskiTotalBounded.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/SphereIsometry/KuratowskiTotalBounded.lean by skeleton subtraction
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
import Definitions.Def_OAI_Analysis_SphereIsometry_CompactConvexFixedPoint
import Definitions.Def_OAI_Analysis_SphereIsometry_CoefficientBins
import Definitions.Def_OAI_Analysis_SphereIsometry_ConvexCoverRegroup
import Definitions.Def_OAI_Analysis_SphereIsometry_KuratowskiConvexHull
import Definitions.Def_OAI_Analysis_SphereIsometry_CondensingIteration

namespace OAI

/-!
# Finite diameter covers and total boundedness

The Kuratowski cover predicate is equivalent to arbitrarily fine finite metric
covers. Its zero value characterizes total boundedness on bounded sets. A
selected point from each member of a nested family has totally bounded range
when sufficiently late members admit arbitrarily fine diameter covers.
-/

noncomputable section

open Set

namespace Tingley

universe u

variable {E : Type u} [PseudoMetricSpace E]

/-- Total boundedness is equivalent to finite pairwise-diameter covers at every
positive scale. No completeness or nonemptiness hypothesis is needed. -/
theorem totallyBounded_iff_finiteDiameterCover {H : Set E} :
    TotallyBounded H ↔ ∀ ε : ℝ, 0 < ε → FiniteDiameterCover H ε := by
  classical
  constructor
  · intro hH ε hε
    obtain ⟨t, ht, hcover⟩ :=
      Metric.totallyBounded_iff.mp hH (ε / 2) (half_pos hε)
    let : Fintype t := ht.fintype
    refine FiniteDiameterCover.of_fintype
      (fun c : t => Metric.ball (c : E) (ε / 2)) ?_ ?_
    · intro x hx
      obtain ⟨c, hct, hxc⟩ := Set.mem_iUnion₂.mp (hcover hx)
      exact Set.mem_iUnion.mpr ⟨⟨c, hct⟩, hxc⟩
    · intro c x hx y hy
      have hxy : dist x y < ε := calc
        dist x y ≤ dist x (c : E) + dist y (c : E) := dist_triangle_right _ _ _
        _ < ε / 2 + ε / 2 :=
          add_lt_add (Metric.mem_ball.mp hx) (Metric.mem_ball.mp hy)
        _ = ε := add_halves ε
      exact hxy.le
  · intro hcover
    apply Metric.totallyBounded_of_finite_discretization
    intro ε hε
    obtain ⟨n, A, hA, hdiam⟩ := hcover (ε / 2) (half_pos hε)
    have hmem : ∀ x : H, ∃ i : Fin n, (x : E) ∈ A i :=
      fun x => Set.mem_iUnion.mp (hA x.property)
    let label : H → Fin n := fun x => Classical.choose (hmem x)
    have hlabel : ∀ x : H, (x : E) ∈ A (label x) :=
      fun x => Classical.choose_spec (hmem x)
    refine ⟨ULift.{u} (Fin n), inferInstance,
      (fun x => ⟨label x⟩), ?_⟩
    intro x y hxy
    have heq : label x = label y :=
      congrArg (fun z : ULift.{u} (Fin n) => z.down) hxy
    have hy : (y : E) ∈ A (label x) := by
      rw [heq]
      exact hlabel y
    exact (hdiam (label x) (x : E) (hlabel x) (y : E) hy).trans_lt
      (half_lt_self hε)

/-- Cover the entire selected range by finitely many prefix singletons and a
small cover of a sufficiently late member. The cutoff may depend on the scale;
no fixed member of the original family is assumed totally bounded. -/
theorem totallyBounded_range_of_nested_finiteDiameterCover
    (C : ℕ → Set E) (hanti : Antitone C)
    (x : ℕ → E) (hx : ∀ n, x n ∈ C n)
    (hsmall : ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, FiniteDiameterCover (C N) ε) :
    TotallyBounded (Set.range x) := by
  classical
  apply totallyBounded_iff_finiteDiameterCover.mpr
  intro ε hε
  obtain ⟨N, k, A, hcover, hdiam⟩ := hsmall ε hε
  let B : Sum (Fin N) (Fin k) → Set E :=
    Sum.elim (fun i => {x (i : ℕ)}) A
  refine FiniteDiameterCover.of_fintype B ?_ ?_
  · rintro y ⟨n, rfl⟩
    by_cases hn : n < N
    · exact Set.mem_iUnion.mpr ⟨Sum.inl ⟨n, hn⟩, rfl⟩
    · have hxn : x n ∈ C N := hanti (Nat.le_of_not_gt hn) (hx n)
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover hxn)
      exact Set.mem_iUnion.mpr ⟨Sum.inr i, hi⟩
  · intro i
    cases i with
    | inl i =>
      change DiameterLE ({x (i : ℕ)} : Set E) ε
      intro y hy z hz
      rcases Set.mem_singleton_iff.mp hy with rfl
      rcases Set.mem_singleton_iff.mp hz with rfl
      simpa only [dist_self] using hε.le
    | inr i =>
      exact hdiam i

end Tingley

end

end OAI


