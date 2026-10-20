-- Prove2me | Definitions.Def_OAI_Analysis_SphereIsometry_RadialExtension
-- name    : OAI_Analysis_SphereIsometry_RadialExtension
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T22:27:07.064539+00:00
-- url     : https://prove2.me/theorems/6c55f387-74ae-49c7-8754-c88f497e2da3
-- title:
--   The radial extension of a sphere isometry
-- statement:
--   These notions belong to a proof of Tingley's theorem in full generality: every surjective isometry $f$ between the unit spheres $S_X,S_Y$ of real normed spaces extends to the linear isometry $x\mapsto\|x\|\,f(x/\|x\|)$ of $X$ onto $Y$. The proof studies the cross-radius defects $\delta_q(x,y)=\|f(x)-qf(y)\|-\|x-qy\|$ for $0\le q\le1$. It shows that a positive maximal defect may be assumed to be attained, after passing to ultrapowers and completions, and rules out an attained positive defect by a fixed-point construction of aligned chords. Let $f:S_X\to S_Y$ be a bijective isometry.
--
--   1. **Radial extension.**
--   $$
--   F(x)=\|x\|\,f\Bigl(\frac x{\|x\|}\Bigr)\ (x\ne0),\qquad F(0)=0 .
--   $$
--   It preserves norms, extends $f$, and satisfies $F(ru)=rf(u)$ for $r\ge0$ and $u\in S_X$.
--   2. **Zero defect.** If all defects vanish, then $\|f(u)-qf(v)\|=\|u-qv\|$ for $q\in[0,1]$. By factoring out the larger radius, $\|af(u)-bf(v)\|=\|au-bv\|$ for all $a,b\ge0$. So $F$ is an isometry of $X$, and it is onto because $f$ is.
--   3. **Linear isometry.** By the Mazur–Ulam theorem, the surjective isometry $F$ with $F(0)=0$ is a real-linear isometric isomorphism.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/SphereIsometry/RadialExtension.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/SphereIsometry/RadialExtension.lean by skeleton subtraction
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
import Definitions.Def_OAI_Analysis_SphereIsometry_KuratowskiNested
import Definitions.Def_OAI_Analysis_SphereIsometry_CondensingFixedPoint
import Definitions.Def_OAI_Analysis_SphereIsometry_ReturnMapFixedPoint
import Definitions.Def_OAI_Analysis_SphereIsometry_AlignedConfiguration
import Definitions.Def_OAI_Analysis_SphereIsometry_Alignment
import Definitions.Def_OAI_Analysis_SphereIsometry_ChordSecant
import Definitions.Def_OAI_Analysis_SphereIsometry_RadialPerturbation
import Definitions.Def_OAI_Analysis_SphereIsometry_LargeChord
import Definitions.Def_OAI_Analysis_SphereIsometry_SmallChord
import Definitions.Def_OAI_Analysis_SphereIsometry_ChordContradiction

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = e hc := @dif_neg c h hc α t e

namespace OAI

/-!
# The radial extension of a sphere isometry with zero defect

The extension is defined on actual vectors, including zero. A zero cross-radius
bound gives its all-pairs isometry; sphere surjectivity gives its surjectivity.
Mazur–Ulam then supplies real linearity. Uniqueness is proved against arbitrary
real-linear extensions, without assuming they are continuous or surjective.
-/

noncomputable section

namespace Tingley

universe u v

variable {X : Type u} {Y : Type v}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- The actual radial extension, with a separate zero branch. -/
def radialExtension (f : UnitSphere X ≃ᵢ UnitSphere Y) (x : X) : Y := by
  classical
  exact if hx : x = 0 then 0 else ‖x‖ • (f (normalize x hx) : Y)

@[simp] theorem radialExtension_zero (f : UnitSphere X ≃ᵢ UnitSphere Y) :
    radialExtension f 0 = 0 := by
  simp [radialExtension]

theorem radialExtension_of_ne_zero (f : UnitSphere X ≃ᵢ UnitSphere Y)
    (x : X) (hx : x ≠ 0) :
    radialExtension f x = ‖x‖ • (f (normalize x hx) : Y) := by
  simp only [radialExtension, dite_eq_right hx]

@[simp] theorem radialExtension_norm (f : UnitSphere X ≃ᵢ UnitSphere Y) (x : X) :
    ‖radialExtension f x‖ = ‖x‖ := by
  by_cases hx : x = 0
  · subst x
    simp only [radialExtension_zero, norm_zero]
  · rw [radialExtension_of_ne_zero f x hx,
      norm_smul_of_nonneg (norm_nonneg x), UnitSphere.norm_coe, mul_one]

/-- Every nonnegative radial representation has the expected image. -/
theorem radialExtension_smul_unit (f : UnitSphere X ≃ᵢ UnitSphere Y)
    (r : ℝ) (hr : 0 ≤ r) (u : UnitSphere X) :
    radialExtension f (r • (u : X)) = r • (f u : Y) := by
  by_cases hr0 : r = 0
  · subst r
    simp only [zero_smul, radialExtension_zero]
  · have hn : ‖r • (u : X)‖ = r := by
      rw [norm_smul_of_nonneg hr, UnitSphere.norm_coe, mul_one]
    have hne : r • (u : X) ≠ 0 := by
      intro h
      apply hr0
      rw [← hn, h, norm_zero]
    have hnormalize : normalize (r • (u : X)) hne = u := by
      apply Subtype.ext
      change ‖r • (u : X)‖⁻¹ • (r • (u : X)) = (u : X)
      rw [hn, smul_smul, inv_mul_cancel₀ hr0, one_smul]
    rw [radialExtension_of_ne_zero f _ hne, hn, hnormalize]

@[simp] theorem radialExtension_unit (f : UnitSphere X ≃ᵢ UnitSphere Y)
    (u : UnitSphere X) : radialExtension f (u : X) = (f u : Y) := by
  simpa only [one_smul] using radialExtension_smul_unit f 1 zero_le_one u

/-- The zero bound gives exact preservation at every radius in the closed unit interval. -/
theorem crossRadius_eq_of_zero_defect (f : UnitSphere X ≃ᵢ UnitSphere Y)
    (h0 : HasDefectBound f 0) (q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (u v : UnitSphere X) :
    ‖(f u : Y) - q • (f v : Y)‖ = ‖(u : X) - q • (v : X)‖ := by
  exact sub_eq_zero.mp (signedDefect_eq_zero_of_bound_zero h0 hq u v)

/-- Factor by the larger positive radius; the smaller radius may be zero. -/
theorem scaled_norm_sub_eq (f : UnitSphere X ≃ᵢ UnitSphere Y)
    (h0 : HasDefectBound f 0) (u v : UnitSphere X) (a b : ℝ)
    (ha : 0 < a) (hb : 0 ≤ b) (hba : b ≤ a) :
    ‖a • (f u : Y) - b • (f v : Y)‖ = ‖a • (u : X) - b • (v : X)‖ := by
  have hq : b / a ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hb ha.le, (div_le_one ha).mpr hba⟩
  have hab : a * (b / a) = b := by
    rw [div_eq_mul_inv, mul_left_comm, mul_inv_cancel₀ (ne_of_gt ha), mul_one]
  calc
    ‖a • (f u : Y) - b • (f v : Y)‖ =
        ‖a • ((f u : Y) - (b / a) • (f v : Y))‖ := by
      rw [smul_sub, smul_smul, hab]
    _ = a * ‖(f u : Y) - (b / a) • (f v : Y)‖ :=
      norm_smul_of_nonneg ha.le _
    _ = a * ‖(u : X) - (b / a) • (v : X)‖ := by
      rw [crossRadius_eq_of_zero_defect f h0 (b / a) hq u v]
    _ = ‖a • ((u : X) - (b / a) • (v : X))‖ :=
      (norm_smul_of_nonneg ha.le _).symm
    _ = ‖a • (u : X) - b • (v : X)‖ := by
      rw [smul_sub, smul_smul, hab]

/-- Every pair is covered, including zero vectors and either order of radii. -/
theorem radialExtension_norm_sub (f : UnitSphere X ≃ᵢ UnitSphere Y)
    (h0 : HasDefectBound f 0) (x y : X) :
    ‖radialExtension f x - radialExtension f y‖ = ‖x - y‖ := by
  by_cases hx : x = 0
  · subst x
    simpa only [radialExtension_zero, zero_sub, norm_neg] using radialExtension_norm f y
  by_cases hy : y = 0
  · subst y
    simpa only [radialExtension_zero, sub_zero] using radialExtension_norm f x
  have hordered (a b : X) (ha : a ≠ 0) (hb : b ≠ 0) (hba : ‖b‖ ≤ ‖a‖) :
      ‖radialExtension f a - radialExtension f b‖ = ‖a - b‖ := by
    have h := scaled_norm_sub_eq f h0 (normalize a ha) (normalize b hb)
      ‖a‖ ‖b‖ (norm_pos_iff.mpr ha) (norm_nonneg b) hba
    rw [norm_smul_normalize, norm_smul_normalize] at h
    simpa only [radialExtension_of_ne_zero f a ha,
      radialExtension_of_ne_zero f b hb] using h
  rcases le_total ‖y‖ ‖x‖ with hle | hle
  · exact hordered x y hx hy hle
  · calc
      ‖radialExtension f x - radialExtension f y‖ =
          ‖radialExtension f y - radialExtension f x‖ := norm_sub_rev _ _
      _ = ‖y - x‖ := hordered y x hy hx hle
      _ = ‖x - y‖ := norm_sub_rev _ _

theorem radialExtension_isometry (f : UnitSphere X ≃ᵢ UnitSphere Y)
    (h0 : HasDefectBound f 0) : Isometry (radialExtension f) := by
  apply Isometry.of_dist_eq
  intro x y
  simpa only [dist_eq_norm] using radialExtension_norm_sub f h0 x y

/-- Surjectivity follows directly from the actual inverse on unit spheres. -/
theorem radialExtension_surjective (f : UnitSphere X ≃ᵢ UnitSphere Y) :
    Function.Surjective (radialExtension f) := by
  intro y
  by_cases hy : y = 0
  · subst y
    exact ⟨0, radialExtension_zero f⟩
  · refine ⟨‖y‖ • (f.symm (normalize y hy) : X), ?_⟩
    rw [radialExtension_smul_unit f ‖y‖ (norm_nonneg y), f.apply_symm_apply]
    exact norm_smul_normalize y hy

/-- The metric equivalence is built only after isometry and surjectivity are proved. -/
def radialIsometryEquiv (f : UnitSphere X ≃ᵢ UnitSphere Y)
    (h0 : HasDefectBound f 0) : X ≃ᵢ Y where
  toEquiv := Equiv.ofBijective (radialExtension f)
    ⟨(radialExtension_isometry f h0).injective, radialExtension_surjective f⟩
  isometry_toFun := radialExtension_isometry f h0

@[simp] theorem coe_radialIsometryEquiv (f : UnitSphere X ≃ᵢ UnitSphere Y)
    (h0 : HasDefectBound f 0) : ⇑(radialIsometryEquiv f h0) = radialExtension f := rfl

@[simp] theorem radialIsometryEquiv_apply (f : UnitSphere X ≃ᵢ UnitSphere Y)
    (h0 : HasDefectBound f 0) (x : X) :
    radialIsometryEquiv f h0 x = radialExtension f x := rfl

/-- Mazur–Ulam applied to the derived whole-space isometry fixing zero. -/
def radialLinearIsometryEquiv (f : UnitSphere X ≃ᵢ UnitSphere Y)
    (h0 : HasDefectBound f 0) : X ≃ₗᵢ[ℝ] Y :=
  (radialIsometryEquiv f h0).toRealLinearIsometryEquivOfMapZero
    (by change radialExtension f 0 = 0; exact radialExtension_zero f)

@[simp] theorem coe_radialLinearIsometryEquiv (f : UnitSphere X ≃ᵢ UnitSphere Y)
    (h0 : HasDefectBound f 0) :
    ⇑(radialLinearIsometryEquiv f h0) = radialExtension f := rfl

@[simp] theorem radialLinearIsometryEquiv_apply (f : UnitSphere X ≃ᵢ UnitSphere Y)
    (h0 : HasDefectBound f 0) (x : X) :
    radialLinearIsometryEquiv f h0 x = radialExtension f x := rfl

@[simp] theorem radialLinearIsometryEquiv_unit (f : UnitSphere X ≃ᵢ UnitSphere Y)
    (h0 : HasDefectBound f 0) (u : UnitSphere X) :
    radialLinearIsometryEquiv f h0 (u : X) = (f u : Y) :=
  radialExtension_unit f u

end Tingley

end

end OAI


