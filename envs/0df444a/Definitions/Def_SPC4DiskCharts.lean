-- Prove2me | Definitions.Def_SPC4DiskCharts
-- name    : SPC4DiskCharts
-- status  : Definition
-- author  : @ryanshin
-- created : 2026-09-05T19:25:14.117612+00:00
-- url     : https://prove2.me/theorems/6ebea99b-e307-46e9-ac9c-852ef65723a8
-- title:
--   Explicit radial–stereographic chart interface for the closed disk
-- statement:
--   For every positive Euclidean dimension, construct the translated interior chart and radial–stereographic boundary charts on the closed unit ball. Their total inverses use explicit clamps. These open partial homeomorphisms give the charted-space interface SPC4Disk.diskChartedSpace.
--
--   This bundle includes the inverse and continuity proofs needed to construct the charts. It does not include the proof of smooth chart compatibility (SPC4Disk.diskIsManifold), the boundary theorem, or any Poincaré conjecture.
-- source:
--   Unpublished archived Disk.lean, chart construction through original line 469, source SHA-256 889a9eccf9d2350aee7051ab7b6895e565f9f1a0c84e7120fb45c15acae0097e.

/-
  Disk.lean — toward a smooth manifold-with-boundary structure on the closed
  unit ball in ℝⁿ (Milestone 1 of PROJECT_BALL: the interior chart).

  Pattern follows `IccLeftChart` (Geometry/Manifold/Instances/Real.lean):
  charts into `EuclideanHalfSpace n`, inverses made total by clamping.

  The interior chart shifts the open unit ball by `2 • e₀` into the interior
  of the half-space; its inverse shifts back and radially clamps
  (`w ↦ (1 ⊓ ‖w‖⁻¹) • w`), which is the identity on the closed ball and total
  everywhere (at `w = 0`, Lean's `0⁻¹ = 0` gives the correct value `0`).
  Continuity of the inverse is only ever needed on the chart target, where
  the clamp is literally the shift-back — no global continuity lemma needed.
-/
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Geometry.Manifold.Instances.Icc

set_option autoImplicit false

namespace SPC4Disk

open Set Metric

open scoped ContDiff Manifold

noncomputable section

variable {n : ℕ} [NeZero n]

omit [NeZero n] in
/-- Each coordinate of a Euclidean vector is bounded by its norm. -/
lemma EuclideanSpace.abs_coord_le_norm (w : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    |w i| ≤ ‖w‖ := by
  rw [EuclideanSpace.norm_eq]
  have h1 : |w i| ^ 2 ≤ ∑ j, ‖w j‖ ^ 2 := by
    have := Finset.single_le_sum (f := fun j => ‖w j‖ ^ 2)
      (fun j _ => by positivity) (Finset.mem_univ i)
    simpa [Real.norm_eq_abs, sq_abs] using this
  have h2 : (0 : ℝ) ≤ ∑ j, ‖w j‖ ^ 2 := by positivity
  nlinarith [Real.sq_sqrt h2, Real.sqrt_nonneg (∑ j, ‖w j‖ ^ 2), abs_nonneg (w i)]

/-- The center offset: twice the first standard basis vector. -/
def diskShift (n : ℕ) [NeZero n] : EuclideanSpace ℝ (Fin n) :=
  EuclideanSpace.single (0 : Fin n) (2 : ℝ)

/-- The radial clamp: identity on the closed unit ball, radial projection
outside. Total by `0⁻¹ = 0`. -/
def radialClamp (w : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  (1 ⊓ ‖w‖⁻¹) • w

omit [NeZero n] in
lemma radialClamp_of_le (w : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖ ≤ 1) :
    radialClamp w = w := by
  rcases eq_or_ne w 0 with h | h
  · simp [radialClamp, h]
  · have hpos : 0 < ‖w‖ := norm_pos_iff.mpr h
    have : (1 : ℝ) ≤ ‖w‖⁻¹ := (one_le_inv₀ hpos).mpr hw
    simp [radialClamp, inf_of_le_left this]

omit [NeZero n] in
lemma norm_radialClamp_le (w : EuclideanSpace ℝ (Fin n)) :
    ‖radialClamp w‖ ≤ 1 := by
  rcases le_or_gt ‖w‖ 1 with h | h
  · rw [radialClamp_of_le w h]; exact h
  · have hpos : 0 < ‖w‖ := lt_trans one_pos h
    have hinv : ‖w‖⁻¹ ≤ 1 := (inv_le_one₀ hpos).mpr h.le
    have h0 : (0 : ℝ) ≤ ‖w‖⁻¹ := inv_nonneg.mpr hpos.le
    rw [radialClamp, inf_of_le_right hinv, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg h0, inv_mul_cancel₀ (ne_of_gt hpos)]

/-- The interior chart of the closed unit ball: shift into the half-space. -/
def DiskInteriorChart :
    OpenPartialHomeomorph (closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)
      (EuclideanHalfSpace n) where
  source := { z | ‖z.val‖ < 1 }
  target := { z | ‖z.val - diskShift n‖ < 1 }
  toFun z := ⟨z.val + diskShift n, by
    have hz : ‖z.val‖ ≤ 1 :=
      mem_closedBall_zero_iff.mp z.2
    have h1 : |z.val 0| ≤ 1 :=
      le_trans (EuclideanSpace.abs_coord_le_norm _ 0) hz
    have h2 : (z.val + diskShift n) 0 =
        z.val 0 + 2 := by
      simp [diskShift]
    rw [h2]
    have := abs_le.mp h1
    linarith [this.1]⟩
  invFun z := ⟨radialClamp (z.val - diskShift n),
    mem_closedBall_zero_iff.mpr (norm_radialClamp_le _)⟩
  map_source' := by
    intro z hz
    simpa [add_sub_cancel_right] using hz
  map_target' := by
    intro z hz
    simpa [radialClamp_of_le _ (le_of_lt hz)] using hz
  left_inv' := by
    intro z hz
    ext1
    simp only [add_sub_cancel_right]
    exact radialClamp_of_le _ (le_of_lt hz)
  right_inv' := by
    intro z hz
    ext1
    simp only [radialClamp_of_le _ (le_of_lt hz), sub_add_cancel]
  open_source := by
    have h : IsOpen { w : EuclideanSpace ℝ (Fin n) | ‖w‖ < 1 } := by
      simpa [ball, dist_zero_right] using
        isOpen_ball (x := (0 : EuclideanSpace ℝ (Fin n))) (ε := 1)
    exact h.preimage continuous_subtype_val
  open_target := by
    have h : IsOpen { w : EuclideanSpace ℝ (Fin n) | ‖w - diskShift n‖ < 1 } := by
      simpa [ball, dist_eq_norm] using isOpen_ball (x := diskShift n) (ε := 1)
    exact h.preimage continuous_subtype_val
  continuousOn_toFun := by
    apply Continuous.continuousOn
    exact (continuous_subtype_val.add continuous_const).subtype_mk _
  continuousOn_invFun := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hg : Continuous (fun z :
        { z : EuclideanHalfSpace n | ‖z.val - diskShift n‖ < 1 } =>
        (⟨z.val.val - diskShift n,
          mem_closedBall_zero_iff.mpr (le_of_lt z.property)⟩ :
          closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)) :=
      ((continuous_subtype_val.comp continuous_subtype_val).sub
        continuous_const).subtype_mk _
    exact hg.congr fun z =>
      Subtype.ext (radialClamp_of_le _ (le_of_lt z.property)).symm

/-! ### Toward the boundary charts (Milestone 2a): the total radial unit map -/

/-- The radial unit vector of `x`, with junk value `p` at `x = 0`. Total, so
it can serve as a chart component; charts will exclude `0` from their
sources. -/
def unitOr (p : sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
    (x : EuclideanSpace ℝ (Fin n)) : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 :=
  if h : x = 0 then p else
    ⟨‖x‖⁻¹ • x, by
      have hpos : 0 < ‖x‖ := norm_pos_iff.mpr h
      simp [norm_smul, inv_mul_cancel₀ (ne_of_gt hpos)]⟩

omit [NeZero n] in
lemma unitOr_val_of_ne (p : sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
    {x : EuclideanSpace ℝ (Fin n)} (h : x ≠ 0) :
    (unitOr p x).val = ‖x‖⁻¹ • x := by
  simp [unitOr, h]

omit [NeZero n] in
lemma smul_unitOr (p : sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
    {x : EuclideanSpace ℝ (Fin n)} (h : x ≠ 0) :
    ‖x‖ • (unitOr p x).val = x := by
  rw [unitOr_val_of_ne p h, smul_smul,
    mul_inv_cancel₀ (norm_ne_zero_iff.mpr h), one_smul]

omit [NeZero n] in
lemma unitOr_smul (p : sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
    {r : ℝ} (hr : 0 < r) (u : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    unitOr p (r • u.val) = u := by
  have hu : ‖u.val‖ = 1 := mem_sphere_zero_iff_norm.mp u.2
  have hune : u.val ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hu
    exact one_ne_zero hu.symm
  have hne : r • u.val ≠ 0 := smul_ne_zero (ne_of_gt hr) hune
  ext1
  rw [unitOr_val_of_ne p hne, norm_smul, hu, mul_one, Real.norm_eq_abs,
    abs_of_pos hr, smul_smul, inv_mul_cancel₀ (ne_of_gt hr), one_smul]

omit [NeZero n] in
lemma continuousOn_unitOr (p : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    ContinuousOn (unitOr p) { x : EuclideanSpace ℝ (Fin n) | x ≠ 0 } := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hg : Continuous (fun z : { x : EuclideanSpace ℝ (Fin n) | x ≠ 0 } =>
      (⟨‖z.val‖⁻¹ • z.val, by
        have hpos : 0 < ‖z.val‖ := norm_pos_iff.mpr z.property
        simp [norm_smul, inv_mul_cancel₀ (ne_of_gt hpos)]⟩ :
        sphere (0 : EuclideanSpace ℝ (Fin n)) 1)) := by
    refine Continuous.subtype_mk ?_ _
    exact ((continuous_norm.comp continuous_subtype_val).inv₀
      (fun z => norm_ne_zero_iff.mpr z.property)).smul continuous_subtype_val
  exact hg.congr fun z => Subtype.ext (unitOr_val_of_ne p z.property).symm

/-! ### Milestone 2(b): the boundary chart's forward map

Work at dimension `m + 1` (mirroring Sphere.lean's convention). For a
boundary direction `p ∈ 𝕊ᵐ`, the chart sends `x` to
`(1 - ‖x‖, stereographic' m (-p) x̂)`: first coordinate = distance to the
boundary (nonnegative on the ball, zero exactly on the boundary), remaining
coordinates = stereographic image of the radial unit vector. Total via
`unitOr p` (fallback `p` lies in the stereographic chart's source `{-p}ᶜ`). -/

section BoundaryChart

variable {m : ℕ}

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

/-- Forward map of the boundary chart at direction `p`. -/
def DiskBoundaryChartFun (p : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (z : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
    EuclideanHalfSpace (m + 1) :=
  ⟨WithLp.toLp 2 (Fin.cons (1 - ‖z.val‖)
      (fun i => stereographic' m (-p) (unitOr p z.val) i)), by
    have hz : ‖z.val‖ ≤ 1 := mem_closedBall_zero_iff.mp z.2
    simpa using sub_nonneg.mpr hz⟩

lemma DiskBoundaryChartFun_val_zero
    (p : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (z : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
    (DiskBoundaryChartFun p z).val 0 = 1 - ‖z.val‖ := by
  simp [DiskBoundaryChartFun]

lemma DiskBoundaryChartFun_val_succ
    (p : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (z : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) (i : Fin m) :
    (DiskBoundaryChartFun p z).val i.succ =
      stereographic' m (-p) (unitOr p z.val) i := by
  simp [DiskBoundaryChartFun]

/-- The radius clamp used by the inverse boundary chart, and its value on
honest inputs. -/
lemma diskClamp_eq {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    (0 ⊔ (1 ⊓ (1 - r))) = 1 - r := by
  rw [inf_of_le_right (by linarith), sup_of_le_right (by linarith)]

/-- Inverse of the boundary chart: radius from the first coordinate (clamped
into `[0,1]`), direction from the inverse stereographic image of the
remaining coordinates. Total. -/
def DiskBoundaryChartInv (p : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (y : EuclideanHalfSpace (m + 1)) :
    closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 :=
  ⟨(0 ⊔ (1 ⊓ (1 - y.val 0))) •
      ((stereographic' m (-p)).symm
        (WithLp.toLp 2 (Fin.tail (fun i => y.val i)))).val, by
    have h1 : (0 : ℝ) ≤ 0 ⊔ (1 ⊓ (1 - y.val 0)) := le_max_left _ _
    have h2 : (0 ⊔ (1 ⊓ (1 - y.val 0))) ≤ 1 :=
      max_le zero_le_one (min_le_left _ _)
    have hu : ‖((stereographic' m (-p)).symm
        (WithLp.toLp 2 (Fin.tail (fun i => y.val i)))).val‖ = 1 :=
      mem_sphere_zero_iff_norm.mp ((stereographic' m (-p)).symm _).2
    rw [mem_closedBall_zero_iff, norm_smul, hu, mul_one, Real.norm_eq_abs,
      abs_of_nonneg h1]
    exact h2⟩

/-- Off the ray through `-p`, the unit map avoids `-p`: the condition that
will define the boundary chart's source. -/
lemma unitOr_ne_neg (p : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    {x : EuclideanSpace ℝ (Fin (m + 1))} (hx : x ≠ 0)
    (hray : x ≠ ‖x‖ • ((-p : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
      EuclideanSpace ℝ (Fin (m + 1)))) :
    unitOr p x ≠ -p := by
  intro h
  apply hray
  conv_lhs => rw [← smul_unitOr p hx]
  rw [h]

/-- **Left inverse law** for the boundary chart: on the chart's source
(nonzero, off the `-p` ray), the inverse undoes the forward map. -/
lemma DiskBoundaryChartInv_comp_fun
    (p : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (z : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (hx : z.val ≠ 0) (hp : unitOr p z.val ≠ -p) :
    DiskBoundaryChartInv p (DiskBoundaryChartFun p z) = z := by
  have hz1 : ‖z.val‖ ≤ 1 := mem_closedBall_zero_iff.mp z.2
  have htail : WithLp.toLp 2
      (Fin.tail (fun i => (DiskBoundaryChartFun p z).val i)) =
      stereographic' m (-p) (unitOr p z.val) := by
    ext i
    simp [DiskBoundaryChartFun]
  have hmem : (unitOr p z.val : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) ∈
      (stereographic' m (-p)).source := by
    simp [stereographic'_source, hp]
  ext1
  simp only [DiskBoundaryChartInv, DiskBoundaryChartFun_val_zero, htail,
    (stereographic' m (-p)).left_inv hmem]
  rw [diskClamp_eq (by linarith) (by linarith [norm_nonneg z.val]),
    sub_sub_cancel, smul_unitOr p hx]

/-- **Right inverse law** for the boundary chart: on the chart's target
(`y 0 < 1`), the forward map undoes the inverse. -/
lemma DiskBoundaryChartFun_comp_inv
    (p : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (y : EuclideanHalfSpace (m + 1)) (hy : y.val 0 < 1) :
    DiskBoundaryChartFun p (DiskBoundaryChartInv p y) = y := by
  have h0 : (0 : ℝ) ≤ y.val 0 := y.2
  have hr : 0 < 1 - y.val 0 := by linarith
  set u := (stereographic' m (-p)).symm
    (WithLp.toLp 2 (Fin.tail (fun i => y.val i))) with hu
  have hnorm : ‖(DiskBoundaryChartInv p y).val‖ = 1 - y.val 0 := by
    simp only [DiskBoundaryChartInv, ← hu]
    rw [diskClamp_eq h0 hy.le, norm_smul,
      mem_sphere_zero_iff_norm.mp u.2, mul_one, Real.norm_eq_abs, abs_of_pos hr]
  have huor : unitOr p (DiskBoundaryChartInv p y).val = u := by
    simp only [DiskBoundaryChartInv, ← hu]
    rw [diskClamp_eq h0 hy.le]
    exact unitOr_smul p hr u
  ext1
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [DiskBoundaryChartFun_val_zero, hnorm, sub_sub_cancel]
  · rw [DiskBoundaryChartFun_val_succ, huor, hu,
      (stereographic' m (-p)).right_inv (by simp)]
    rfl

/-- The inverse boundary-chart map is continuous — globally: the clamp and
the (everywhere-defined) inverse stereographic map are both continuous. -/
lemma continuous_DiskBoundaryChartInv
    (p : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
    Continuous (DiskBoundaryChartInv p) := by
  have hsymm : Continuous (stereographic' m (-p)).symm := by
    rw [← continuousOn_univ]
    simpa using (stereographic' m (-p)).symm.continuousOn
  have htail : Continuous (fun y : EuclideanHalfSpace (m + 1) =>
      (WithLp.toLp 2 (Fin.tail (fun i => y.val i)) : EuclideanSpace ℝ (Fin m))) := by
    refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun j => ?_)
    exact (PiLp.continuous_apply 2 _ j.succ).comp continuous_subtype_val
  have happ : Continuous (fun y : EuclideanHalfSpace (m + 1) => y.val 0) :=
    (PiLp.continuous_apply 2 _ 0).comp continuous_subtype_val
  unfold DiskBoundaryChartInv
  refine Continuous.subtype_mk ?_ _
  exact (continuous_const.max (continuous_const.min (continuous_const.sub happ))).smul
    (continuous_subtype_val.comp (hsymm.comp htail))

/-- The forward boundary-chart map is continuous on the chart's source. -/
lemma continuousOn_DiskBoundaryChartFun
    (p : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
    ContinuousOn (DiskBoundaryChartFun p)
      { z : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 |
        z.val ≠ 0 ∧ z.val ≠ ‖z.val‖ •
          ((-p : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
            EuclideanSpace ℝ (Fin (m + 1))) } := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hval : Continuous (fun z : ↥{ z : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 |
      z.val ≠ 0 ∧ z.val ≠ ‖z.val‖ •
        ((-p : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
          EuclideanSpace ℝ (Fin (m + 1))) } => z.val.val) :=
    continuous_subtype_val.comp continuous_subtype_val
  have hunit : Continuous (fun z : ↥{ z : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 |
      z.val ≠ 0 ∧ z.val ≠ ‖z.val‖ •
        ((-p : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
          EuclideanSpace ℝ (Fin (m + 1))) } => unitOr p z.val.val) :=
    (continuousOn_unitOr p).comp_continuous hval fun z => z.2.1
  have hstereo : Continuous (fun z : ↥{ z : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 |
      z.val ≠ 0 ∧ z.val ≠ ‖z.val‖ •
        ((-p : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
          EuclideanSpace ℝ (Fin (m + 1))) } => stereographic' m (-p) (unitOr p z.val.val)) := by
    refine (stereographic' m (-p)).continuousOn.comp_continuous hunit fun z => ?_
    rw [stereographic'_source]
    exact unitOr_ne_neg p z.2.1 z.2.2
  unfold DiskBoundaryChartFun
  refine Continuous.subtype_mk ((PiLp.continuous_toLp 2 _).comp (continuous_pi fun j => ?_)) _
  refine Fin.cases ?_ (fun i => ?_) j
  · simp only [Fin.cons_zero]
    exact continuous_const.sub hval.norm
  · simpa [Function.comp_def] using (PiLp.continuous_apply 2 _ i).comp hstereo

/-- **The boundary chart** of the closed unit ball at boundary direction `p`:
`x ↦ (1 - ‖x‖, stereographic' m (-p) x̂)`, an `OpenPartialHomeomorph` onto
`{y | y 0 < 1}`, defined away from the origin and the ray through `-p`.
Together with `DiskInteriorChart`, these charts cover the closed ball. -/
def DiskBoundaryChart (p : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
    OpenPartialHomeomorph (closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
      (EuclideanHalfSpace (m + 1)) where
  source := { z | z.val ≠ 0 ∧ z.val ≠ ‖z.val‖ •
    ((-p : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
      EuclideanSpace ℝ (Fin (m + 1))) }
  target := { y | y.val 0 < 1 }
  toFun := DiskBoundaryChartFun p
  invFun := DiskBoundaryChartInv p
  map_source' := by
    intro z hz
    simp only [mem_ofPred_eq, DiskBoundaryChartFun_val_zero]
    have := norm_pos_iff.mpr hz.1
    linarith
  map_target' := by
    intro y hy
    simp only [mem_ofPred_eq] at hy ⊢
    have h0 : (0 : ℝ) ≤ y.val 0 := y.2
    have hr : 0 < 1 - y.val 0 := by linarith
    set u := (stereographic' m (-p)).symm
      (WithLp.toLp 2 (Fin.tail (fun i => y.val i))) with hu
    have husrc : u ∈ (stereographic' m (-p)).source :=
      (stereographic' m (-p)).map_target (by simp)
    rw [stereographic'_source] at husrc
    have hune : u.val ≠ ((-p : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
        EuclideanSpace ℝ (Fin (m + 1))) :=
      fun h => husrc (Subtype.ext h)
    have huval : ‖u.val‖ = 1 := mem_sphere_zero_iff_norm.mp u.2
    have hu0 : u.val ≠ 0 := by
      intro h; rw [h, norm_zero] at huval; exact one_ne_zero huval.symm
    have hval : (DiskBoundaryChartInv p y).val = (1 - y.val 0) • u.val := by
      show (0 ⊔ (1 ⊓ (1 - y.val 0))) • u.val = (1 - y.val 0) • u.val
      rw [diskClamp_eq h0 (by linarith)]
    constructor
    · rw [hval]
      exact smul_ne_zero (by linarith) hu0
    · rw [hval]
      have hnorm : ‖(1 - y.val 0) • u.val‖ = 1 - y.val 0 := by
        rw [norm_smul, huval, mul_one, Real.norm_eq_abs, abs_of_pos hr]
      rw [hnorm]
      intro h
      exact hune (smul_right_injective _
        (by linarith : (1 : ℝ) - y.val 0 ≠ 0) h)
  left_inv' := fun z hz =>
    DiskBoundaryChartInv_comp_fun p z hz.1 (unitOr_ne_neg p hz.1 hz.2)
  right_inv' := fun y hy => DiskBoundaryChartFun_comp_inv p y hy
  open_source := by
    rw [Set.ofPred_and]
    apply IsOpen.inter
    · exact isOpen_ne.preimage continuous_subtype_val
    · have h1 : Continuous (fun x : EuclideanSpace ℝ (Fin (m + 1)) =>
          x - ‖x‖ • ((-p : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
            EuclideanSpace ℝ (Fin (m + 1)))) :=
        continuous_id.sub (continuous_norm.smul continuous_const)
      have h2 : IsOpen { x : EuclideanSpace ℝ (Fin (m + 1)) |
          x ≠ ‖x‖ • ((-p : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
            EuclideanSpace ℝ (Fin (m + 1))) } := by
        have h3 := (isOpen_ne (x := (0 : EuclideanSpace ℝ (Fin (m + 1))))).preimage h1
        convert h3 using 1
        ext x
        simp [eq_neg_iff_add_eq_zero]
      exact h2.preimage continuous_subtype_val
  open_target := by
    exact isOpen_Iio.preimage ((PiLp.continuous_apply 2 _ 0).comp continuous_subtype_val)
  continuousOn_toFun := continuousOn_DiskBoundaryChartFun p
  continuousOn_invFun := (continuous_DiskBoundaryChartInv p).continuousOn

/-! ### Milestone 3: the charted-space structure on the closed ball -/

/-- A fixed base point on the sphere, used as the `unitOr` fallback in chart
selection. -/
def diskNorth : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 :=
  ⟨EuclideanSpace.single 0 1, by simp⟩

open Classical in
/-- The closed unit ball in ℝ^{m+1} is a charted space over the Euclidean
half-space: the interior chart at interior points, a boundary chart in the
radial direction at boundary points. -/
instance diskChartedSpace : ChartedSpace (EuclideanHalfSpace (m + 1))
    (closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) where
  atlas := {DiskInteriorChart} ∪ Set.range DiskBoundaryChart
  chartAt z :=
    if ‖z.val‖ < 1 then DiskInteriorChart
    else DiskBoundaryChart (unitOr diskNorth z.val)
  mem_chart_source z := by
    split_ifs with h
    · exact h
    · have h1 : ‖z.val‖ = 1 :=
        le_antisymm (mem_closedBall_zero_iff.mp z.2) (not_lt.mp h)
      have h0 : z.val ≠ 0 := by
        intro h0
        rw [h0, norm_zero] at h1
        exact zero_ne_one h1
      have hz : (unitOr diskNorth z.val).val = z.val := by
        have := smul_unitOr diskNorth h0
        rwa [h1, one_smul] at this
      refine ⟨h0, ?_⟩
      rw [h1, one_smul, coe_neg_sphere, hz]
      intro heq
      apply h0
      have h2 : (2 : ℝ) • z.val = 0 := by
        rw [two_smul]
        exact eq_neg_iff_add_eq_zero.mp heq
      simpa using (smul_eq_zero.mp h2).resolve_left (by norm_num)
  chart_mem_atlas z := by
    split_ifs with h
    · exact Set.mem_union_left _ rfl
    · exact Set.mem_union_right _ ⟨_, rfl⟩

/-! ### Milestone 3(b1): smoothness of the unit-vector map away from zero -/



/-! ### Milestone 3(b2), core: the vector-level angular map is smooth

The boundary chart's angular component, written at the vector level
(linear isometry ∘ `stereoToFun` ∘ unit map), is `C^k` away from the origin
and the bad inner-product locus. Connecting this to the chart's subtype-level
formula is the congr step, deferred to assembly. -/







/-! ### Milestone 3(b3): the reverse transition is globally smooth

With the clamp evaluated at its on-overlap value `1 - y 0`, the
boundary-to-interior formula is `C^k` on all of the model space:
`stereoInvFunAux` is globally smooth, the tail extraction and basis equiv are
linear, and the radius factor is polynomial. -/









/-! ### The main theorem: the closed ball is a smooth manifold with boundary

All four chart-transition cases are verified: same-chart cases via
`symm_trans_mem_contDiffGroupoid`, mixed and boundary-boundary cases by
`ContDiffOn.congr` against the transition formulas proved above, matched
through the half-space model. This file contains no `sorry`. -/



/-! ### Milestone 4(a): the boundary of the disk is the unit sphere

Using Mathlib's `InteriorBoundary` machinery: points with `‖z‖ < 1` are
interior (the interior chart's image has first coordinate `≥ 2 - ‖z‖ > 0`),
points with `‖z‖ = 1` are boundary (the boundary chart's image has first
coordinate `1 - ‖z‖ = 0`, on the frontier of the half-space). -/









end BoundaryChart

/-! ### The ball form of the smooth four-dimensional Poincaré conjecture

With the closed ball now a verified smooth manifold with boundary and its
boundary identified with the sphere, the ball form of SPC4 is statable —
to our knowledge for the first time in any proof assistant.

On paper this is equivalent to `SPC4` (the closed form): remove a ball from
a homotopy 4-sphere to pass from the closed form to the ball form, and glue
a 4-handle by Cerf's Γ₄ = 0 to return. Both directions need collar and
gluing technology absent from Mathlib, so the equivalence is not formalized
here. The boundary condition is phrased topologically (`≃ₜ`); the smooth
refinement awaits boundary-as-manifold machinery. -/





/-! ### The boundary of the disk is smoothly the sphere

Combining the session's three infrastructure layers: the topological
identification `diskBoundaryHomeoSphere`, the pullback transport of smooth
structures (`Homeomorph.pullbackChartedSpace`), and the
structomorphism–diffeomorphism bridge (`Structomorph.toDiffeomorph`). With
the transported structure — the canonical choice pending general
boundary-as-manifold machinery — the boundary of the closed ball is
**diffeomorphic** to the sphere. -/

section BoundarySmooth

variable {m : ℕ}





end BoundarySmooth

/-! ### The explicit collar of the disk boundary

The map `(u, t) ↦ (1 - t/2) • u` embeds `sphere × [0, 1]` into the closed
ball as an annular neighborhood of the boundary (radii in `[1/2, 1]`). This
is the explicit collar the disk enjoys — the first step toward the collar
technology that the equivalence between the ball and closed forms of SPC4
ultimately requires. This section provides the map, its membership, its
continuity, and the smoothness of its vector-level form; smoothness as a map
into the disk manifold-with-boundary (chart-level) is the sequel. -/

section Collar

variable {m : ℕ}

























end Collar

/-! ### Smoothness of the inclusion of the disk

The disk analog of `contMDiff_coe_sphere` and `contMDiff_subtypeVal_Icc`:
the inclusion of the closed ball into the ambient space is smooth. The chart
representatives are exactly the chart-inverse formulas whose smoothness the
`IsManifold` development already established. -/

section ValSmooth

variable {m : ℕ}
















end ValSmooth

/-!
## The collar neighbourhood as a manifold

The collar is not merely a topological embedding: it identifies the closed
annulus `{z ∈ D | 1/2 ≤ ‖z‖}` with the product manifold-with-boundary
`Sᵐ × [0, 1]`.  Transporting the product structure along that homeomorphism
(`Homeomorph.pullbackChartedSpace`) makes the annulus a smooth
manifold-with-corners, and the structomorphism–diffeomorphism bridge turns
the transport into an honest **diffeomorphism**

  `annulus ≃ₘ Sᵐ × [0, 1]`.

This is the model form of a collar neighbourhood used in every
glue-along-the-boundary argument, and in particular in the classical
reduction of `SPC4` to `SPC4Ball`.
-/

section Annulus

variable {m : ℕ}





















end Annulus

end
end SPC4Disk


