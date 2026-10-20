-- Prove2me | Definitions.Def_OAI_Analysis_SphereIsometry_ProbabilitySimplex
-- name    : OAI_Analysis_SphereIsometry_ProbabilitySimplex
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T21:21:56.205183+00:00
-- url     : https://prove2.me/theorems/7b95459d-2492-4386-b381-30add60d2df0
-- title:
--   The probability simplex
-- statement:
--   These notions belong to a self-contained fixed-point toolkit used in the proof of Tingley's theorem: Sperner's lemma on iterated barycentric subdivisions, Brouwer's fixed point theorem for the probability simplex, Schauder's theorem for compact convex sets, the Kuratowski measure of noncompactness, and a Darbo–Sadovskii fixed point theorem for condensing maps. Let $\iota$ be a finite index set.
--
--   1. **Simplex.**
--   $$
--   \Delta_\iota=\Bigl\{a\in\mathbb R^\iota:\ a_i\ge0,\ \sum_ia_i=1\Bigr\},
--   $$
--   a compact convex set containing every point mass.
--   2. **Positive coordinates.** Every $a\in\Delta_\iota$ has a coordinate with $a_i>0$. For $a,b\in\Delta_\iota$ there is $i$ with $a_i>0$ and $b_i\le a_i$. This is the labelling rule used in Sperner's argument: a point is labelled by a coordinate that the map does not increase.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/SphereIsometry/ProbabilitySimplex.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/SphereIsometry/ProbabilitySimplex.lean by skeleton subtraction
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

namespace OAI

/-!
# Finite probability simplices

The coordinates are nonnegative real numbers with sum one. The positive-coordinate
selection lemma is the boundary-compatible labelling rule used in Sperner's argument.
-/

open scoped BigOperators

namespace Tingley

def probabilitySimplexSet (ι : Type*) [Fintype ι] : Set (ι → ℝ) :=
  {weights | (∀ index, 0 ≤ weights index) ∧ ∑ index, weights index = 1}

theorem convex_probabilitySimplexSet (ι : Type*) [Fintype ι] :
    Convex ℝ (probabilitySimplexSet ι) := by
  intro left hleft right hright first second hfirst hsecond hsum
  refine ⟨fun index => add_nonneg (mul_nonneg hfirst (hleft.1 index))
    (mul_nonneg hsecond (hright.1 index)), ?_⟩
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum, hleft.2, hright.2, mul_one, hsum]

theorem single_mem_probabilitySimplexSet {ι : Type*} [Fintype ι] [DecidableEq ι]
    (index : ι) : Pi.single index 1 ∈ probabilitySimplexSet ι :=
  ⟨le_update_iff.2 ⟨zero_le_one, fun _ _ => le_rfl⟩, by simp⟩

theorem mem_Icc_of_mem_probabilitySimplexSet {ι : Type*} [Fintype ι]
    {weights : ι → ℝ} (hweights : weights ∈ probabilitySimplexSet ι) (index : ι) :
    weights index ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨hweights.1 index, hweights.2 ▸
    Finset.single_le_sum (fun other _ => hweights.1 other) (Finset.mem_univ index)⟩

abbrev ProbabilitySimplex (ι : Type*) [Fintype ι] := ↥(probabilitySimplexSet ι)

instance probabilitySimplex_compactSpace (ι : Type*) [Fintype ι] :
    CompactSpace (ProbabilitySimplex ι) := by
  apply isCompact_iff_compactSpace.mp
  apply IsCompact.of_isClosed_subset
    (isCompact_Icc : IsCompact (Set.Icc (0 : ι → ℝ) 1))
  · change IsClosed ({weights : ι → ℝ | ∀ index, 0 ≤ weights index} ∩
      {weights | ∑ index, weights index = 1})
    apply IsClosed.inter
    · rw [Set.ofPred_forall]
      exact isClosed_iInter fun index =>
        isClosed_le continuous_const (continuous_apply index)
    · exact isClosed_eq (by fun_prop) continuous_const
  · intro weights hweights
    exact ⟨fun index => (mem_Icc_of_mem_probabilitySimplexSet hweights index).1,
      fun index => (mem_Icc_of_mem_probabilitySimplexSet hweights index).2⟩

namespace ProbabilitySimplex

variable {ι : Type*} [Fintype ι]

theorem coordinate_nonneg (a : ProbabilitySimplex ι) (i : ι) : 0 ≤ a.val i :=
  a.property.1 i

theorem sum_coordinates (a : ProbabilitySimplex ι) : ∑ i, a.val i = 1 :=
  a.property.2

noncomputable def pointMass (i : ι) : ProbabilitySimplex ι := by
  classical
  exact ⟨Pi.single i 1, single_mem_probabilitySimplexSet i⟩

instance [Nonempty ι] : Nonempty (ProbabilitySimplex ι) :=
  ⟨pointMass (Classical.choice ‹Nonempty ι›)⟩

theorem exists_positive_coordinate (a : ProbabilitySimplex ι) :
    ∃ i, 0 < a.val i := by
  classical
  by_contra h
  have hz : a.val = 0 := by
    funext i
    exact le_antisymm (le_of_not_gt (fun hi => h ⟨i, hi⟩)) (a.coordinate_nonneg i)
  have hs := a.sum_coordinates
  simp [hz] at hs

end ProbabilitySimplex

theorem exists_positive_dominating_coordinate {ι : Type*} [Fintype ι]
    (a b : ProbabilitySimplex ι) :
    ∃ i, 0 < a.val i ∧ b.val i ≤ a.val i := by
  classical
  by_contra h
  have hstrict : ∀ i, 0 < a.val i → a.val i < b.val i := by
    intro i hi
    exact lt_of_not_ge (fun hle => h ⟨i, hi, hle⟩)
  have hweak : ∀ i, a.val i ≤ b.val i := by
    intro i
    by_cases hi : 0 < a.val i
    · exact (hstrict i hi).le
    · have hz : a.val i = 0 :=
        le_antisymm (le_of_not_gt hi) (a.coordinate_nonneg i)
      rw [hz]
      exact b.coordinate_nonneg i
  obtain ⟨i, hi⟩ := a.exists_positive_coordinate
  have hsum : (∑ j, a.val j) < ∑ j, b.val j :=
    Finset.sum_lt_sum (fun j _ => hweak j) ⟨i, Finset.mem_univ i, hstrict i hi⟩
  rw [a.sum_coordinates, b.sum_coordinates] at hsum
  exact (lt_irrefl (1 : ℝ)) hsum

end Tingley

end OAI


