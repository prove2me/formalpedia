-- Prove2me | Definitions.Def_OAI_Analysis_SphereIsometry_CoefficientBins
-- name    : OAI_Analysis_SphereIsometry_CoefficientBins
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T21:59:58.385384+00:00
-- url     : https://prove2.me/theorems/62a1d57e-3672-4183-9883-06c41732275b
-- title:
--   Finite partitions of the coefficient simplex
-- statement:
--   These notions belong to a self-contained fixed-point toolkit used in the proof of Tingley's theorem: Sperner's lemma on iterated barycentric subdivisions, Brouwer's fixed point theorem for the probability simplex, Schauder's theorem for compact convex sets, the Kuratowski measure of noncompactness, and a Darbo–Sadovskii fixed point theorem for condensing maps.
--
--   1. **Coefficient simplex.** Vectors $w\in\mathbb R^n$ with $w_i\ge0$ and $\sum_iw_i=1$, so each $w_i\le1$.
--   2. **Coefficient bins.** For every $\eta>0$ there are $K$ and finitely many bins, indexed by labels in $\{0,\dots,K\}^n$ via the floor grid $\lfloor Kw_i\rfloor$, that cover the coefficient simplex and have $\ell_1$ diameter at most $\eta$:
--   $$
--   \sum_i|w_i-w'_i|\le\eta\quad\text{for }w,w'\text{ in one bin}.
--   $$
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/SphereIsometry/CoefficientBins.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/SphereIsometry/CoefficientBins.lean by skeleton subtraction
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

namespace OAI

/-!
# Finite bins for probability coefficients

An integer floor grid partitions the coefficient simplex into finitely many
parts of arbitrarily small l1 diameter. The proof uses only the Archimedean
property and finite sums, and also applies when the coefficient index is empty.
-/

open scoped BigOperators

namespace Tingley

/-- Nonnegative coefficients with total mass one. -/
def CoefficientSimplex (n : ℕ) : Set (Fin n → ℝ) :=
  {w | (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1}

 theorem coefficient_le_one {n : ℕ} {w : Fin n → ℝ}
    (hw : w ∈ CoefficientSimplex n) (i : Fin n) : w i ≤ 1 := by
  calc
    w i ≤ ∑ j, w j :=
      Finset.single_le_sum (fun j _ => hw.1 j) (Finset.mem_univ i)
    _ = 1 := hw.2

 theorem abs_sub_lt_of_same_floor {K a b : ℝ} {q : ℕ}
    (hK : 0 < K) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hqa : Nat.floor (K * a) = q) (hqb : Nat.floor (K * b) = q) :
    |a - b| < 1 / K := by
  have ha' := (Nat.floor_eq_iff (mul_nonneg hK.le ha)).mp hqa
  have hb' := (Nat.floor_eq_iff (mul_nonneg hK.le hb)).mp hqb
  have hab : a - b < 1 / K := by
    apply (lt_div_iff₀' hK).mpr
    nlinarith only [ha'.2, hb'.1]
  have hba : b - a < 1 / K := by
    apply (lt_div_iff₀' hK).mpr
    nlinarith only [hb'.2, ha'.1]
  exact abs_lt.mpr ⟨by linarith only [hba], hab⟩

/-- A finite family of coefficient bins with l1 diameter at most `η`.

The label type has `(K + 1)^n` elements. The last coordinate label retains
coefficients equal to one. For `n = 0`, the simplex and all bins are empty;
no nonemptiness hypothesis on the coefficient index is needed.
-/
theorem exists_coefficient_bins (n : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ K : ℕ, ∃ bins : (Fin n → Fin (K + 1)) → Set (Fin n → ℝ),
      (∀ w ∈ CoefficientSimplex n, ∃ q, w ∈ bins q) ∧
      (∀ q, ∀ w ∈ bins q, ∀ v ∈ bins q, ∑ i, |w i - v i| ≤ η) := by
  obtain ⟨K, hgrid⟩ := exists_nat_gt ((n : ℝ) / η)
  have hK : (0 : ℝ) < K :=
    lt_of_le_of_lt (div_nonneg (Nat.cast_nonneg n) hη.le) hgrid
  have hsmall : (n : ℝ) / K < η := by
    apply (div_lt_iff₀ hK).mpr
    simpa only [mul_comm] using (div_lt_iff₀ hη).mp hgrid
  let bins : (Fin n → Fin (K + 1)) → Set (Fin n → ℝ) := fun q =>
    {w | w ∈ CoefficientSimplex n ∧
      ∀ i, Nat.floor ((K : ℝ) * w i) = (q i).val}
  refine ⟨K, bins, ?_, ?_⟩
  · intro w hw
    have hcode (i : Fin n) : Nat.floor ((K : ℝ) * w i) < K + 1 := by
      apply Nat.lt_succ_of_le
      apply Nat.floor_le_of_le
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (coefficient_le_one hw i) hK.le
    let q : Fin n → Fin (K + 1) := fun i =>
      ⟨Nat.floor ((K : ℝ) * w i), hcode i⟩
    refine ⟨q, ?_⟩
    change w ∈ CoefficientSimplex n ∧
      ∀ i, Nat.floor ((K : ℝ) * w i) = (q i).val
    exact ⟨hw, fun _ => rfl⟩
  · intro q w hw v hv
    change (w ∈ CoefficientSimplex n ∧
      ∀ i, Nat.floor ((K : ℝ) * w i) = (q i).val) at hw
    change (v ∈ CoefficientSimplex n ∧
      ∀ i, Nat.floor ((K : ℝ) * v i) = (q i).val) at hv
    have hcoord (i : Fin n) : |w i - v i| < 1 / (K : ℝ) :=
      abs_sub_lt_of_same_floor hK (hw.1.1 i) (hv.1.1 i) (hw.2 i) (hv.2 i)
    calc
      ∑ i, |w i - v i| ≤ ∑ _i : Fin n, 1 / (K : ℝ) :=
        Finset.sum_le_sum (fun i _ => (hcoord i).le)
      _ = (n : ℝ) / K := by
        rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul, mul_one_div]
      _ ≤ η := hsmall.le

end Tingley

end OAI


