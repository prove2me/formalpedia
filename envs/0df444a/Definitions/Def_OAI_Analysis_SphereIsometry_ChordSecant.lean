-- Prove2me | Definitions.Def_OAI_Analysis_SphereIsometry_ChordSecant
-- name    : OAI_Analysis_SphereIsometry_ChordSecant
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T22:19:32.737268+00:00
-- url     : https://prove2.me/theorems/9b156cee-62aa-47ce-bec5-e43ad7e9a356
-- title:
--   Secant estimates along an aligned chord
-- statement:
--   These notions belong to a proof of Tingley's theorem in full generality: every surjective isometry $f$ between the unit spheres $S_X,S_Y$ of real normed spaces extends to the linear isometry $x\mapsto\|x\|\,f(x/\|x\|)$ of $X$ onto $Y$. The proof studies the cross-radius defects $\delta_q(x,y)=\|f(x)-qf(y)\|-\|x-qy\|$ for $0\le q\le1$. It shows that a positive maximal defect may be assumed to be attained, after passing to ultrapowers and completions, and rules out an attained positive defect by a fixed-point construction of aligned chords. Let $C$ be an aligned configuration for $f$ with defect bound $M>0$ at $(y,t)$, $0<t<1$: $x=ty+pv$, $z=ty-rv$, $f(x)=tf(y)+sw$, $f(z)=tf(y)-uw$ with $s-p=r-u=M$, $d=p+r\le2$, $A=p/d$, $B=u/d$.
--
--   1. **Support lower bound.** If $\|pv+ty\|=1$ and $0<\theta\le t/p$, every support $\varphi$ at $v+\theta y$ has $\varphi(v)\ge(1-t)/p$.
--   2. **Secant step and slope.** $\gamma=\min(t/s,(1-t)/u)$, $\theta=\gamma s/p$, and
--   $$
--   \sigma=\frac{\|\frac ruv+\gamma y\|-\|\frac psv+\gamma y\|}{\frac ru-\frac ps} .
--   $$
--   3. **Secant bounds.** The defects at radii $t-s\gamma$ (at $x$) and $t+u\gamma$ (at $z$) are expressed through these norms. With the global bound they give, for every support $\varphi$ at $v+\theta y$,
--   $$
--   \tfrac{1-t}p\le\varphi(v)\le\sigma ,
--   $$
--   with $\sigma\le1-B$ if $B\le1-t$ and $\sigma\le B$ otherwise. In the first case $1-t\le dA(1-B)$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/SphereIsometry/ChordSecant.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/SphereIsometry/ChordSecant.lean by skeleton subtraction
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

namespace OAI

/-! The secant estimate for every supporting functional of an aligned chord. -/

noncomputable section

namespace Tingley

variable {X Y : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- The lower support bound uses the actual unit endpoint, and holds for every
support at an earlier positive point of the same affine line. -/
theorem support_direction_lower {v y : X} {p t θ : ℝ}
    (hy : ‖y‖ = 1) (hp : 0 < p) (ht : 0 < t)
    (hθ : 0 < θ) (hθβ : θ ≤ t / p)
    (hx : ‖p • v + t • y‖ = 1)
    (φ : X →L[ℝ] ℝ) (hφ : SupportAt φ (v + θ • y)) :
    (1 - t) / p ≤ φ v := by
  have hpb : p * (t / p) = t := by field_simp [hp.ne']
  have hscale : p • (v + (t / p) • y) = p • v + t • y := by
    rw [smul_add, smul_smul, hpb]
  have hn : p * ‖v + (t / p) • y‖ = 1 := by
    rw [← norm_smul_of_nonneg hp.le, hscale, hx]
  have endpoint_lower : ∀ ψ : X →L[ℝ] ℝ,
      SupportAt ψ (v + (t / p) • y) → 1 - t ≤ p * ψ v := by
    intro ψ hψ
    have hyψ : ψ y ≤ 1 := by simpa only [hy] using apply_le_norm hψ.1 y
    have he := congrArg (fun a : ℝ => p * a) hψ.2
    simp only [map_add, map_smul, smul_eq_mul] at he
    rw [mul_add, ← mul_assoc, hpb, hn] at he
    have htψ := mul_le_mul_of_nonneg_left hyψ ht.le
    nlinarith
  apply (div_le_iff₀ hp).2
  rcases lt_or_eq_of_le hθβ with hlt | heq
  · obtain ⟨ψ, hψ⟩ := exists_support (v + (t / p) • y)
    have h₁ := apply_le_norm hφ.1 (v + (t / p) • y)
    have h₂ := apply_le_norm hψ.1 (v + θ • y)
    rw [← hψ.2] at h₁
    rw [← hφ.2] at h₂
    simp only [map_add, map_smul, smul_eq_mul] at h₁ h₂
    have hk : 0 ≤ ψ y - φ y := by
      by_contra hk
      have hprod := mul_neg_of_pos_of_neg (sub_pos.mpr hlt) (lt_of_not_ge hk)
      nlinarith
    have hprod := mul_nonneg hθ.le hk
    have hv : ψ v ≤ φ v := by nlinarith
    have hvp := mul_le_mul_of_nonneg_left hv hp.le
    have hend := endpoint_lower ψ hψ
    nlinarith
  · have hend := endpoint_lower φ (by simpa only [heq] using hφ)
    nlinarith

namespace AlignedConfiguration

variable {f : UnitSphere X ≃ᵢ UnitSphere Y} {y : UnitSphere X} {t M : ℝ}
variable (C : AlignedConfiguration f y t M)

def secantStep : ℝ := min (t / C.s) ((1 - t) / C.u)
def secantTheta : ℝ := C.secantStep * C.s / C.p
def secantSlope : ℝ :=
  (‖(C.r / C.u) • (C.v : X) + C.secantStep • (y : X)‖ -
    ‖(C.p / C.s) • (C.v : X) + C.secantStep • (y : X)‖) /
    (C.r / C.u - C.p / C.s)

theorem secantStep_pos (ht : 0 < t ∧ t < 1) : 0 < C.secantStep :=
  lt_min (div_pos ht.1 C.s_pos) (div_pos (sub_pos.mpr ht.2) C.u_pos)

theorem secantTheta_pos (ht : 0 < t ∧ t < 1) : 0 < C.secantTheta :=
  div_pos (mul_pos (C.secantStep_pos ht) C.s_pos) C.p_pos

theorem secantTheta_le (_ht : 0 < t ∧ t < 1) : C.secantTheta ≤ t / C.p := by
  apply (div_le_div_iff_of_pos_right C.p_pos).2
  calc
    C.secantStep * C.s ≤ (t / C.s) * C.s :=
      mul_le_mul_of_nonneg_right (min_le_left _ _) C.s_pos.le
    _ = t := div_mul_cancel₀ _ C.s_pos.ne'

theorem secant_denominator_pos (hM : 0 < M) : 0 < C.r / C.u - C.p / C.s := by
  have hid := C.chord_identity
  have hprod : 0 < M * C.d := mul_pos hM C.d_pos
  have hlt : C.p / C.s < C.r / C.u := by
    apply (div_lt_div_iff₀ C.s_pos C.u_pos).2
    nlinarith
  exact sub_pos.mpr hlt

theorem step_comparison_iff : t / C.s ≤ (1 - t) / C.u ↔ C.B ≤ 1 - t := by
  rw [div_le_div_iff₀ C.s_pos C.u_pos]
  change t * C.u ≤ (1 - t) * C.s ↔ C.u / C.d ≤ 1 - t
  rw [div_le_iff₀ C.d_pos]
  have hd : C.d = C.s + C.u := C.chord_sum
  rw [hd]
  constructor <;> intro h <;> nlinarith

theorem secantStep_eq_smallB (hB : C.B ≤ 1 - t) : C.secantStep = t / C.s :=
  min_eq_left ((C.step_comparison_iff).2 hB)

theorem secantStep_eq_largeB (_ht : 0 < t ∧ t < 1) (hB : 1 - t < C.B) :
    C.secantStep = (1 - t) / C.u := by
  apply min_eq_right
  exact (lt_of_not_ge fun h => (not_le_of_gt hB) ((C.step_comparison_iff).1 h)).le

theorem secant_radii_mem (ht : 0 < t ∧ t < 1) :
    t - C.s * C.secantStep ∈ Set.Icc (0 : ℝ) 1 ∧
      t + C.u * C.secantStep ∈ Set.Icc (0 : ℝ) 1 := by
  have hh := (C.secantStep_pos ht).le
  have hs := mul_le_mul_of_nonneg_right
    (show C.secantStep ≤ t / C.s from min_le_left _ _) C.s_pos.le
  have hu := mul_le_mul_of_nonneg_right
    (show C.secantStep ≤ (1 - t) / C.u from min_le_right _ _) C.u_pos.le
  rw [div_mul_cancel₀ _ C.s_pos.ne'] at hs
  rw [div_mul_cancel₀ _ C.u_pos.ne'] at hu
  have hsh := mul_nonneg C.s_pos.le hh
  have huh := mul_nonneg C.u_pos.le hh
  constructor <;> constructor <;> nlinarith [ht.1, ht.2]

theorem secant_defect_first :
    signedDefect f (t - C.s * C.secantStep) C.x y =
      C.s * (‖(C.w : Y) + C.secantStep • (f y : Y)‖ -
        ‖(C.p / C.s) • (C.v : X) + C.secantStep • (y : X)‖) := by
  have hsp : C.s * (C.p / C.s) = C.p := by field_simp [C.s_pos.ne']
  have hx : (C.x : X) - (t - C.s * C.secantStep) • (y : X) =
      C.s • ((C.p / C.s) • (C.v : X) + C.secantStep • (y : X)) := by
    rw [C.x_eq, smul_add, smul_smul, hsp]
    module
  have hfx : (f C.x : Y) - (t - C.s * C.secantStep) • (f y : Y) =
      C.s • ((C.w : Y) + C.secantStep • (f y : Y)) := by
    rw [C.fx_eq]
    module
  rw [signedDefect, hx, hfx, norm_smul_of_nonneg C.s_pos.le,
    norm_smul_of_nonneg C.s_pos.le]
  ring

theorem secant_defect_opposite :
    -signedDefect f (t + C.u * C.secantStep) C.z y =
      C.u * (‖(C.r / C.u) • (C.v : X) + C.secantStep • (y : X)‖ -
        ‖(C.w : Y) + C.secantStep • (f y : Y)‖) := by
  have hur : C.u * (C.r / C.u) = C.r := by field_simp [C.u_pos.ne']
  have hz : (C.z : X) - (t + C.u * C.secantStep) • (y : X) =
      -(C.u • ((C.r / C.u) • (C.v : X) + C.secantStep • (y : X))) := by
    rw [C.z_eq, smul_add, smul_smul, hur]
    module
  have hfz : (f C.z : Y) - (t + C.u * C.secantStep) • (f y : Y) =
      -(C.u • ((C.w : Y) + C.secantStep • (f y : Y))) := by
    rw [C.fz_eq]
    module
  rw [signedDefect, hz, hfz, norm_neg, norm_neg,
    norm_smul_of_nonneg C.u_pos.le, norm_smul_of_nonneg C.u_pos.le]
  ring

theorem secant_weighted_identity (hM : 0 < M) :
    M * C.secantSlope =
      (C.u * signedDefect f (t - C.s * C.secantStep) C.x y +
        C.s * (-signedDefect f (t + C.u * C.secantStep) C.z y)) / C.d := by
  rw [C.secant_defect_first, C.secant_defect_opposite]
  unfold secantSlope
  have hd : C.r / C.u - C.p / C.s = M * C.d / (C.u * C.s) := by
    have hid := C.chord_identity
    field_simp [C.u_pos.ne', C.s_pos.ne']
    nlinarith
  rw [hd]
  field_simp [hM.ne', C.d_pos.ne', C.u_pos.ne', C.s_pos.ne']
  ring

theorem secant_upper_smallB (hM : 0 < M) (ht : 0 < t ∧ t < 1)
    (hb : HasDefectBound f M) (hB : C.B ≤ 1 - t) :
    C.secantSlope ≤ 1 - C.B := by
  have hq := (C.secant_radii_mem ht).2
  have hd := (abs_le.mp (hb _ hq C.z y)).1
  have hz : t - C.s * C.secantStep = 0 := by
    rw [C.secantStep_eq_smallB hB]
    field_simp [C.s_pos.ne']
    ring
  have hi := C.secant_weighted_identity hM
  rw [hz, signedDefect_zero, mul_zero, zero_add] at hi
  have hle : C.s * (-signedDefect f (t + C.u * C.secantStep) C.z y) ≤
      C.s * M := mul_le_mul_of_nonneg_left (by linarith) C.s_pos.le
  have hi' := (eq_div_iff C.d_pos.ne').1 hi
  rw [C.one_sub_B]
  apply (le_div_iff₀ C.d_pos).2
  apply (mul_le_mul_iff_right₀ hM).mp
  calc
    M * (C.secantSlope * C.d) = (M * C.secantSlope) * C.d := by ring
    _ = C.s * (-signedDefect f (t + C.u * C.secantStep) C.z y) := hi'
    _ ≤ C.s * M := hle
    _ = M * C.s := mul_comm _ _

theorem secant_upper_largeB (hM : 0 < M) (ht : 0 < t ∧ t < 1)
    (hb : HasDefectBound f M) (hB : 1 - t < C.B) :
    C.secantSlope ≤ C.B := by
  have hq := (C.secant_radii_mem ht).1
  have hd := (abs_le.mp (hb _ hq C.x y)).2
  have ho : t + C.u * C.secantStep = 1 := by
    rw [C.secantStep_eq_largeB ht hB]
    field_simp [C.u_pos.ne']
    ring
  have hi := C.secant_weighted_identity hM
  rw [ho, signedDefect_one, neg_zero, mul_zero, add_zero] at hi
  have hle := mul_le_mul_of_nonneg_left hd C.u_pos.le
  have hi' := (eq_div_iff C.d_pos.ne').1 hi
  change C.secantSlope ≤ C.u / C.d
  apply (le_div_iff₀ C.d_pos).2
  apply (mul_le_mul_iff_right₀ hM).mp
  calc
    M * (C.secantSlope * C.d) = (M * C.secantSlope) * C.d := by ring
    _ = C.u * signedDefect f (t - C.s * C.secantStep) C.x y := hi'
    _ ≤ C.u * M := hle
    _ = M * C.u := mul_comm _ _

/-- No support is selected in this statement: it applies to every norm-bounded
functional norming the displayed vector, including the support reused in the
strictness argument. -/
theorem secant_bounds (hM : 0 < M) (ht : 0 < t ∧ t < 1)
    (hb : HasDefectBound f M) (φ : X →L[ℝ] ℝ)
    (hφ : SupportAt φ ((C.v : X) + C.secantTheta • (y : X))) :
    (1 - t) / C.p ≤ φ C.v ∧ φ C.v ≤ C.secantSlope ∧
      (C.B ≤ 1 - t → C.secantSlope ≤ 1 - C.B) ∧
      (1 - t < C.B → C.secantSlope ≤ C.B) := by
  have hlower : (1 - t) / C.p ≤ φ C.v := by
    apply support_direction_lower y.property C.p_pos ht.1
      (C.secantTheta_pos ht) (C.secantTheta_le ht) _ φ hφ
    rw [add_comm, ← C.x_eq]
    exact C.x.property
  have hα : 0 < C.p / C.s := div_pos C.p_pos C.s_pos
  have hαθ : (C.p / C.s) * C.secantTheta = C.secantStep := by
    unfold secantTheta
    field_simp [C.p_pos.ne', C.s_pos.ne']
  have hscale : (C.p / C.s) • ((C.v : X) + C.secantTheta • (y : X)) =
      (C.p / C.s) • (C.v : X) + C.secantStep • (y : X) := by
    rw [smul_add, smul_smul, hαθ]
  have hlo : SupportAt φ
      ((C.p / C.s) • (C.v : X) + C.secantStep • (y : X)) := by
    rw [← hscale]
    exact hφ.smul_nonneg hα.le
  have hdiff :
      ((C.r / C.u) • (C.v : X) + C.secantStep • (y : X)) -
        ((C.p / C.s) • (C.v : X) + C.secantStep • (y : X)) =
      (C.r / C.u - C.p / C.s) • (C.v : X) := by module
  have hsec := hlo.subgradient
    ((C.r / C.u) • (C.v : X) + C.secantStep • (y : X))
  rw [hdiff, map_smul, smul_eq_mul] at hsec
  have hupper : φ C.v ≤ C.secantSlope := by
    apply (le_div_iff₀ (C.secant_denominator_pos hM)).2
    nlinarith
  exact ⟨hlower, hupper, C.secant_upper_smallB hM ht hb,
    C.secant_upper_largeB hM ht hb⟩

theorem small_secant_product (hM : 0 < M) (ht : 0 < t ∧ t < 1)
    (hb : HasDefectBound f M) (hB : C.B ≤ 1 - t) :
    1 - t ≤ C.d * C.A * (1 - C.B) := by
  obtain ⟨φ, hφ⟩ := exists_support ((C.v : X) + C.secantTheta • (y : X))
  obtain ⟨hlower, hsec, hsmall, _⟩ := C.secant_bounds hM ht hb φ hφ
  have hle := hlower.trans (hsec.trans (hsmall hB))
  calc
    1 - t ≤ (1 - C.B) * C.p := (div_le_iff₀ C.p_pos).1 hle
    _ = C.d * C.A * (1 - C.B) := by rw [← C.p_eq_d_mul_A]; ring

end AlignedConfiguration
end Tingley

end

end OAI


