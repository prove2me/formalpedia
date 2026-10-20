-- Prove2me | Definitions.Def_OAI_Analysis_SphereIsometry_KuratowskiNested
-- name    : OAI_Analysis_SphereIsometry_KuratowskiNested
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T22:08:54.740437+00:00
-- url     : https://prove2.me/theorems/10d3d797-14b2-4de1-ba92-5c692cd369d5
-- title:
--   Nested sets with vanishing measure of noncompactness
-- statement:
--   These notions belong to a self-contained fixed-point toolkit used in the proof of Tingley's theorem: Sperner's lemma on iterated barycentric subdivisions, Brouwer's fixed point theorem for the probability simplex, Schauder's theorem for compact convex sets, the Kuratowski measure of noncompactness, and a Darbo–Sadovskii fixed point theorem for condensing maps. Let $E$ be a complete metric space.
--
--   1. **Fine covers.** A decreasing sequence of nonempty closed sets in which late members have arbitrarily fine finite diameter covers has a nonempty compact intersection.
--   2. **Kuratowski form.** If $F_0\supseteq F_1\supseteq\dots$ are nonempty, closed and bounded with $\chi(F_n)\to0$, then
--   $$
--   \bigcap_nF_n\ \text{is nonempty and compact}.
--   $$
--   This is Kuratowski's intersection theorem; no member needs to be compact.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/SphereIsometry/KuratowskiNested.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/SphereIsometry/KuratowskiNested.lean by skeleton subtraction
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
import Definitions.Def_OAI_Analysis_SphereIsometry_KuratowskiTotalBounded

namespace OAI

/-!
# Nested sets with vanishing Kuratowski measure

Small finite diameter covers make the range of a selected sequence totally
bounded. Its compact closure supplies a point in all the nested closed sets.
The whole intersection is compact by its own arbitrarily fine finite covers.
-/

noncomputable section

open Filter Set
open scoped Topology

namespace Tingley

section Pseudometric

variable {E : Type*} [PseudoMetricSpace E] [CompleteSpace E]

/-- A nested sequence with arbitrarily fine finite diameter covers has a
nonempty compact intersection. No original member is assumed compact. -/
theorem nonempty_isCompact_iInter_of_finiteDiameterCover
    (C : ℕ → Set E) (hanti : Antitone C)
    (hne : ∀ n, (C n).Nonempty)
    (hclosed : ∀ n, IsClosed (C n))
    (hsmall : ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, FiniteDiameterCover (C N) ε) :
    (⋂ n, C n).Nonempty ∧ IsCompact (⋂ n, C n) := by
  classical
  let x : ℕ → E := fun n => Classical.choose (hne n)
  have hx : ∀ n, x n ∈ C n := fun n => Classical.choose_spec (hne n)
  have htotal : TotallyBounded (range x) :=
    totallyBounded_range_of_nested_finiteDiameterCover C hanti x hx hsmall
  let K : Set E := closure (range x)
  have hKclosed : IsClosed K := isClosed_closure
  have hKcompact : IsCompact K :=
    TotallyBounded.isCompact_of_isClosed htotal.closure hKclosed
  let D : ℕ → Set E := fun n => K ∩ C n
  have hDanti : ∀ n, D (n + 1) ⊆ D n := by
    intro n z hz
    exact ⟨hz.1, hanti (Nat.le_succ n) hz.2⟩
  have hDnonempty : ∀ n, (D n).Nonempty := by
    intro n
    exact ⟨x n, subset_closure (mem_range_self n), hx n⟩
  have hDclosed : ∀ n, IsClosed (D n) :=
    fun n => hKclosed.inter (hclosed n)
  have hDcompact : IsCompact (D 0) := hKcompact.inter_right (hclosed 0)
  have hnonempty : (⋂ n, C n).Nonempty := by
    obtain ⟨z, hz⟩ :=
      IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
        D hDanti hDnonempty hDcompact hDclosed
    refine ⟨z, mem_iInter.mpr ?_⟩
    intro n
    exact (mem_iInter.mp hz n).2
  have hinter : TotallyBounded (⋂ n, C n) := by
    apply totallyBounded_iff_finiteDiameterCover.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := hsmall ε hε
    exact hN.mono_set (fun z hz => mem_iInter.mp hz N)
  exact ⟨hnonempty,
    TotallyBounded.isCompact_of_isClosed hinter (isClosed_iInter hclosed)⟩

end Pseudometric

section Metric

variable {E : Type*} [MetricSpace E] [CompleteSpace E]

/-- A decreasing sequence of nonempty closed sets in a complete metric space
has a nonempty compact intersection when its Kuratowski measures tend to zero.
Boundedness of the first set supplies boundedness at every later index. -/
theorem nonempty_isCompact_iInter_of_chi_tendsto_zero
    (C : ℕ → Set E)
    (hanti : Antitone C)
    (hne : ∀ n, (C n).Nonempty)
    (hclosed : ∀ n, IsClosed (C n))
    (hbound : Bornology.IsBounded (C 0))
    (hchi : Tendsto (fun n => chi (C n)) atTop (𝓝 0)) :
    (⋂ n, C n).Nonempty ∧ IsCompact (⋂ n, C n) := by
  have hbounded : ∀ n, Bornology.IsBounded (C n) :=
    fun n => hbound.subset (hanti (Nat.zero_le n))
  apply nonempty_isCompact_iInter_of_finiteDiameterCover C hanti hne hclosed
  intro ε hε
  obtain ⟨N, hN⟩ := (hchi.eventually (gt_mem_nhds hε)).exists
  obtain ⟨δ, _hδ, hδε, hcover⟩ := exists_cover_of_chi_lt (hbounded N) hN
  exact ⟨N, hcover.mono_radius hδε.le⟩

end Metric

end Tingley

end

end OAI


