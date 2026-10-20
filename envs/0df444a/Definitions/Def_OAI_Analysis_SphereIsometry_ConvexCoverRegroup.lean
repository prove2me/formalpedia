-- Prove2me | Definitions.Def_OAI_Analysis_SphereIsometry_ConvexCoverRegroup
-- name    : OAI_Analysis_SphereIsometry_ConvexCoverRegroup
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T22:01:43.909983+00:00
-- url     : https://prove2.me/theorems/223bbcdb-6ff0-4d41-a2ca-730dab79138d
-- title:
--   Regrouping convex combinations along a finite cover
-- statement:
--   These notions belong to a self-contained fixed-point toolkit used in the proof of Tingley's theorem: Sperner's lemma on iterated barycentric subdivisions, Brouwer's fixed point theorem for the probability simplex, Schauder's theorem for compact convex sets, the Kuratowski measure of noncompactness, and a Darbo–Sadovskii fixed point theorem for condensing maps. Let $B_1,\dots,B_n$ be sets in a real vector space.
--
--   1. **Finite mixtures.** Points $\sum_iw_iz_i$ with probability weights $w$ and $z_i\in B_i$ for every $i$, including those with weight $0$. If every $B_i$ is convex, the set of finite mixtures is convex.
--   2. **Regrouping.** If $H\subseteq\bigcup_iB_i$ with all $B_i$ nonempty, then every point of $\mathrm{conv}\,H$ can be written as
--   $$
--   \sum_iw_iz_i,\qquad z_i\in\mathrm{conv}(B_i\cap H)\ \text{or a point of }B_i .
--   $$
--   So a convex combination along any finite cover regroups into one hull point per cover member.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/SphereIsometry/ConvexCoverRegroup.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/SphereIsometry/ConvexCoverRegroup.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

/-!
# Regrouping a convex hull over a finite cover

For a finite family of nonempty sets, every point in the convex hull of their
union is a convex combination with one point from each individual convex hull.
The proof establishes convexity of the represented set. Zero coefficients are
handled by choosing points inside the corresponding sets, without assuming
that those sets contain the origin.
-/

namespace Tingley

open scoped BigOperators

variable {E ι : Type*} [AddCommGroup E] [Module ℝ E] [Fintype ι]

/-- Points represented by probability weights and one point in each member of
a finite family of sets. Membership is required even at zero-weight indices. -/
def finiteMixtures (B : ι → Set E) : Set E :=
  {x | ∃ (w : ι → ℝ) (z : ι → E),
    (∀ i, 0 ≤ w i) ∧ (∑ i, w i) = 1 ∧
    (∀ i, z i ∈ B i) ∧ (∑ i, w i • z i) = x}

/-- Mixing probability-weighted representations preserves representation when
each coordinate set is convex. No nonemptiness premise is needed here. -/
theorem convex_finiteMixtures (B : ι → Set E) (hB : ∀ i, Convex ℝ (B i)) :
    Convex ℝ (finiteMixtures B) := by
  classical
  rintro x ⟨wx, zx, hwx, hwxsum, hzx, hx⟩
    y ⟨wy, zy, hwy, hwysum, hzy, hy⟩ a b ha hb hab
  have hex (i : ι) :
      ∃ u ∈ B i, (a * wx i + b * wy i) • u =
        (a * wx i) • zx i + (b * wy i) • zy i :=
    (hB i).exists_mem_add_smul_eq (hzx i) (hzy i)
      (mul_nonneg ha (hwx i)) (mul_nonneg hb (hwy i))
  choose u hu hueq using hex
  refine ⟨fun i => a * wx i + b * wy i, u, ?_, ?_, hu, ?_⟩
  · intro i
    exact add_nonneg (mul_nonneg ha (hwx i)) (mul_nonneg hb (hwy i))
  · calc
      (∑ i, (a * wx i + b * wy i)) =
          a * (∑ i, wx i) + b * (∑ i, wy i) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ = 1 := by simp only [hwxsum, hwysum, mul_one, hab]
  · calc
      (∑ i, (a * wx i + b * wy i) • u i) =
          ∑ i, ((a * wx i) • zx i + (b * wy i) • zy i) :=
        Finset.sum_congr rfl fun i _ => hueq i
      _ = a • (∑ i, wx i • zx i) + b • (∑ i, wy i • zy i) := by
        simp only [Finset.sum_add_distrib, mul_smul, Finset.smul_sum]
      _ = a • x + b • y := by rw [hx, hy]

/-- Regroup a point of a convex hull along an arbitrary finite cover by
nonempty sets. Cover members may be infinite, overlapping, or nonclosed. -/
theorem convexHull_cover_representation
    (H : Set E) (A : ι → Set E)
    (hne : ∀ i, (A i).Nonempty)
    (hcover : ∀ x ∈ H, ∃ i, x ∈ A i)
    {x : E} (hx : x ∈ convexHull ℝ H) :
    ∃ (w : ι → ℝ) (z : ι → E),
      (∀ i, 0 ≤ w i) ∧ (∑ i, w i) = 1 ∧
      (∀ i, z i ∈ convexHull ℝ (A i)) ∧
      (∑ i, w i • z i) = x := by
  classical
  choose base hbase using hne
  have hcontains : H ⊆ finiteMixtures (fun i => convexHull ℝ (A i)) := by
    intro y hy
    obtain ⟨j, hj⟩ := hcover y hy
    refine ⟨fun i => if i = j then 1 else 0,
      fun i => if i = j then y else base i, ?_, ?_, ?_, ?_⟩
    · intro i
      by_cases hij : i = j <;> simp [hij]
    · simp
    · intro i
      by_cases hij : i = j
      · subst i
        simpa only [ite_eq_left rfl, ite_true] using subset_convexHull ℝ (A j) hj
      · simpa only [ite_eq_right hij] using subset_convexHull ℝ (A i) (hbase i)
    · rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ j)]
      · simp
      · intro i _ hij
        simp [hij]
  exact convexHull_min hcontains
    (convex_finiteMixtures _ fun i => convex_convexHull ℝ (A i)) hx

end Tingley

end OAI


