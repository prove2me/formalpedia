-- Prove2me | Definitions.Def_OAI_Analysis_SphereIsometry_PositiveConvexFace
-- name    : OAI_Analysis_SphereIsometry_PositiveConvexFace
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T21:08:04.931954+00:00
-- url     : https://prove2.me/theorems/c57370f4-f099-4fed-bb10-1cfcb5e17bc3
-- title:
--   Faces of the unit ball cut by a supporting functional
-- statement:
--   These notions belong to a proof of Tingley's theorem in full generality: every surjective isometry $f$ between the unit spheres $S_X,S_Y$ of real normed spaces extends to the linear isometry $x\mapsto\|x\|\,f(x/\|x\|)$ of $X$ onto $Y$. The proof studies the cross-radius defects $\delta_q(x,y)=\|f(x)-qf(y)\|-\|x-qy\|$ for $0\le q\le1$. It shows that a positive maximal defect may be assumed to be attained, after passing to ultrapowers and completions, and rules out an attained positive defect by a fixed-point construction of aligned chords. Let $\varphi$ be a functional with $\|\varphi\|\le1$.
--
--   1. **Positive barycenters.** If $\varphi$ equals $1$ at a strictly positive convex combination of unit vectors $v_i$, then $\varphi(v_i)=1$ for every $i$.
--   2. **Support face.**
--   $$
--   F_\varphi=\{x:\ \|x\|\le1,\ \varphi(x)=1\},
--   $$
--   a convex subset of the unit sphere. Convex hulls of subsets of $F_\varphi$ stay in $F_\varphi$, hence on the sphere.
--   3. **Enlarged hulls.** If $\varphi$ equals $1$ at the vectors $v_i$ and at a new vector $w$, the convex hull of $\{w,v_i\}$ lies in the unit sphere. So a propagation rule applies to every new hull point.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/SphereIsometry/PositiveConvexFace.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/SphereIsometry/PositiveConvexFace.lean by skeleton subtraction
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

namespace OAI

/-!
# Positive combinations in a common support face

A norm-bounded functional that is one on a strictly positive barycenter is
one on every vertex. The resulting simultaneous support keeps the enlarged
convex hull in the unit sphere. For an infinite sequence, finite-prefix hull
containment passes to a closed ambient set without choosing a common support
for the entire sequence.
-/

noncomputable section

open scoped BigOperators
open Set

namespace Tingley

section Scalar

variable {ι : Type*} [Fintype ι]

theorem eq_one_of_positive_weighted_sum (weights b : ι → ℝ)
    (hpos : ∀ i, 0 < weights i) (hsum : ∑ i, weights i = 1)
    (hb : ∀ i, b i ≤ 1) (hsaturated : ∑ i, weights i * b i = 1) :
    ∀ i, b i = 1 := by
  classical
  have hnonneg : ∀ i ∈ (Finset.univ : Finset ι), 0 ≤ weights i * (1 - b i) :=
    fun i _ => mul_nonneg (hpos i).le (sub_nonneg.mpr (hb i))
  have hzero : ∑ i, weights i * (1 - b i) = 0 := by
    calc
      _ = (∑ i, weights i) - ∑ i, weights i * b i := by
        simp only [mul_sub, mul_one, Finset.sum_sub_distrib]
      _ = 0 := by rw [hsum, hsaturated, sub_self]
  intro i
  have hi := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hzero i
    (Finset.mem_univ i)
  exact (sub_eq_zero.mp ((mul_eq_zero.mp hi).resolve_left (ne_of_gt (hpos i)))).symm

end Scalar

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

section FiniteCombination

variable {ι : Type*} [Fintype ι]

theorem support_eq_one_of_positive_sum (φ : X →L[ℝ] ℝ) (hφ : ‖φ‖ ≤ 1)
    (weights : ι → ℝ) (v : ι → X)
    (hpos : ∀ i, 0 < weights i) (hsum : ∑ i, weights i = 1)
    (hv : ∀ i, ‖v i‖ ≤ 1) (ha : φ (∑ i, weights i • v i) = 1) :
    ∀ i, φ (v i) = 1 := by
  apply eq_one_of_positive_weighted_sum weights (fun i => φ (v i)) hpos hsum
  · exact fun i => (apply_le_norm hφ (v i)).trans (hv i)
  · simpa only [map_sum, map_smul, smul_eq_mul] using ha

end FiniteCombination

/-- The closed unit ball cut by the level-one hyperplane of one functional. -/
def supportFace (φ : X →L[ℝ] ℝ) : Set X :=
  {x | ‖x‖ ≤ 1 ∧ φ x = 1}

theorem convex_supportFace (φ : X →L[ℝ] ℝ) : Convex ℝ (supportFace φ) := by
  rintro x ⟨hx, hφx⟩ y ⟨hy, hφy⟩ a b ha hb hab
  constructor
  · calc
      ‖a • x + b • y‖ ≤ ‖a • x‖ + ‖b • y‖ := norm_add_le _ _
      _ = a * ‖x‖ + b * ‖y‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
      _ ≤ a * 1 + b * 1 :=
        add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
      _ = 1 := by simpa only [mul_one] using hab
  · simpa only [map_add, map_smul, smul_eq_mul, hφx, hφy, mul_one] using hab

theorem supportFace_subset_sphere (φ : X →L[ℝ] ℝ) (hφ : ‖φ‖ ≤ 1) :
    supportFace φ ⊆ {x : X | ‖x‖ = 1} := by
  intro x hx
  exact le_antisymm hx.1 (hx.2 ▸ apply_le_norm hφ x)

theorem convexHull_subset_supportFace (φ : X →L[ℝ] ℝ)
    {S : Set X} (hS : S ⊆ supportFace φ) :
    convexHull ℝ S ⊆ supportFace φ :=
  convexHull_min hS (convex_supportFace φ)

section Enlargement

variable {ι : Type*} [Fintype ι]

theorem enlarged_convexHull_in_supportFace (φ : X →L[ℝ] ℝ) (hφ : ‖φ‖ ≤ 1)
    (weights : ι → ℝ) (v : ι → X) (w : X)
    (hpos : ∀ i, 0 < weights i) (hsum : ∑ i, weights i = 1)
    (hv : ∀ i, ‖v i‖ = 1) (hw : ‖w‖ = 1)
    (ha : φ (∑ i, weights i • v i) = 1) (hwφ : φ w = 1) :
    convexHull ℝ (insert w (Set.range v)) ⊆ {x : X | ‖x‖ = 1 ∧ φ x = 1} := by
  have hall := support_eq_one_of_positive_sum φ hφ weights v hpos hsum
    (fun i => (hv i).le) ha
  have hvertices : insert w (Set.range v) ⊆ supportFace φ := by
    intro x hx
    rcases hx with rfl | ⟨i, rfl⟩
    · exact ⟨hw.le, hwφ⟩
    · exact ⟨(hv i).le, hall i⟩
  intro x hx
  have hxface := convexHull_subset_supportFace φ hvertices hx
  exact ⟨supportFace_subset_sphere φ hφ hxface, hxface.2⟩

/-- The actual geometric propagation rule can now be applied to every new hull point. -/
theorem convexHull_insert_subset_of_common_support (φ : X →L[ℝ] ℝ) (hφ : ‖φ‖ ≤ 1)
    (weights : ι → ℝ) (v : ι → X) (w : X) (E : Set X)
    (hpos : ∀ i, 0 < weights i) (hsum : ∑ i, weights i = 1)
    (hv : ∀ i, ‖v i‖ = 1) (hw : ‖w‖ = 1)
    (ha : φ (∑ i, weights i • v i) = 1) (hwφ : φ w = 1)
    (hprop : ∀ x, ‖x‖ = 1 → φ x = 1 → x ∈ E) :
    convexHull ℝ (insert w (Set.range v)) ⊆ E := by
  intro x hx
  have h := enlarged_convexHull_in_supportFace φ hφ weights v w hpos hsum hv hw ha hwφ hx
  exact hprop x h.1 h.2

end Enlargement

end Tingley

end

end OAI


