-- Prove2me | Definitions.Def_OAI_Analysis_SphereIsometry_SimplexLimit
-- name    : OAI_Analysis_SphereIsometry_SimplexLimit
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T21:22:37.058742+00:00
-- url     : https://prove2.me/theorems/3c70ba73-dfb2-4fad-8c06-57cb3d67a973
-- title:
--   From shrinking labelled cells to a simplex fixed point
-- statement:
--   These notions belong to a self-contained fixed-point toolkit used in the proof of Tingley's theorem: Sperner's lemma on iterated barycentric subdivisions, Brouwer's fixed point theorem for the probability simplex, Schauder's theorem for compact convex sets, the Kuratowski measure of noncompactness, and a Darbo–Sadovskii fixed point theorem for condensing maps.
--
--   1. **Reindexing.** A bijection of index sets induces a homeomorphism of probability simplices.
--   2. **Shrinking families.** Let $P:\Delta_\iota\to\Delta_\iota$ be continuous. Suppose that for each level $k$ there are points $a_{k,i}$ ($i\in\iota$) with mutual distances at most $\delta_k\to0$ and
--   $$
--   P(a_{k,i})_i\le(a_{k,i})_i .
--   $$
--   Then $P$ has a fixed point. A limit $x$ of a subsequence satisfies $P(x)_i\le x_i$ for all $i$, and both sides sum to $1$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/SphereIsometry/SimplexLimit.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/SphereIsometry/SimplexLimit.lean by skeleton subtraction
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

namespace OAI

/-!
# Extracting a fixed point from shrinking labelled simplex cells

The analytic limit step of the simplex fixed-point argument starts with
a concrete family of simplex points, one for each coordinate at every subdivision level.
The finite Sperner argument supplies this family, and the subdivision estimates supply its
shrinking diameter. No fixed-point principle is assumed here.
-/

open Filter
open scoped BigOperators Topology

namespace Tingley

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Relabelling the coordinates is a homeomorphism of probability simplexes. -/
def probabilitySimplexReindex (e : ι ≃ κ) : ProbabilitySimplex ι ≃ₜ ProbabilitySimplex κ where
  toFun x :=
    ⟨fun j => x.val (e.symm j),
      ⟨fun j => x.property.1 _, (e.symm.sum_comp x.val).trans x.property.2⟩⟩
  invFun y :=
    ⟨fun i => y.val (e i),
      ⟨fun i => y.property.1 _, (e.sum_comp y.val).trans y.property.2⟩⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    exact congrArg x.val (e.symm_apply_apply i)
  right_inv y := by
    apply Subtype.ext
    funext j
    exact congrArg y.val (e.apply_symm_apply j)
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_pi fun j =>
      (continuous_apply (e.symm j)).comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_pi fun i =>
      (continuous_apply (e i)).comp continuous_subtype_val

@[simp]
theorem probabilitySimplexReindex_apply_val (e : ι ≃ κ) (x : ProbabilitySimplex ι) (j : κ) :
    (probabilitySimplexReindex e x).val j = x.val (e.symm j) := rfl

@[simp]
theorem probabilitySimplexReindex_symm_apply_val (e : ι ≃ κ) (y : ProbabilitySimplex κ) (i : ι) :
    ((probabilitySimplexReindex e).symm y).val i = y.val (e i) := rfl

variable [Nonempty ι]

/-- Coordinate inequalities at points in shrinking cells produce an actual fixed point.

Only one sequence is passed to compactness. The mesh estimate forces all the coordinate-labelled
sequences along that same subsequence to converge to the same simplex point. -/
theorem probabilitySimplex_fixedPoint_of_shrinking_family
    (P : ProbabilitySimplex ι → ProbabilitySimplex ι) (hP : Continuous P)
    (a : ℕ → ι → ProbabilitySimplex ι) (δ : ℕ → ℝ)
    (hδ : Tendsto δ atTop (𝓝 0))
    (hmesh : ∀ k i j, dist (a k i) (a k j) ≤ δ k)
    (hcoordinate : ∀ k i, (P (a k i)).val i ≤ (a k i).val i) :
    ∃ x, P x = x := by
  classical
  let i₀ : ι := Classical.choice inferInstance
  obtain ⟨x, φ, hφ, hx⟩ := CompactSpace.tendsto_subseq (fun k => a k i₀)
  have hδφ : Tendsto (fun k => δ (φ k)) atTop (𝓝 0) :=
    hδ.comp hφ.tendsto_atTop
  have ha : ∀ i, Tendsto (fun k => a (φ k) i) atTop (𝓝 x) := by
    intro i
    apply hx.congr_dist
    exact squeeze_zero (fun _ => dist_nonneg)
      (fun k => hmesh (φ k) i₀ i) hδφ
  have hle : ∀ i, (P x).val i ≤ x.val i := by
    intro i
    have hc : Continuous (fun y : ProbabilitySimplex ι => y.val i) :=
      (continuous_apply i).comp continuous_subtype_val
    exact le_of_tendsto_of_tendsto'
      (((hc.comp hP).tendsto x).comp (ha i))
      ((hc.tendsto x).comp (ha i))
      (fun k => hcoordinate (φ k) i)
  have hsum : (∑ i, (x.val i - (P x).val i)) = 0 := by
    rw [Finset.sum_sub_distrib, x.property.2, (P x).property.2, sub_self]
  have hzero : ∀ i ∈ Finset.univ, x.val i - (P x).val i = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sub_nonneg.mpr (hle i))).mp hsum
  refine ⟨x, ?_⟩
  apply Subtype.ext
  funext i
  exact (sub_eq_zero.mp (hzero i (Finset.mem_univ i))).symm

end Tingley

end OAI


