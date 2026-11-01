-- Prove2me | Definitions.Def_OAIQ091C006
-- name    : OAIQ091C006
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T16:51:59.706169+00:00
-- url     : https://prove2.me/theorems/9c3aa1ba-9f0c-4af1-9197-d4993e4ade01
-- title:
--   Definitions bundle OAIQ091C006 of the split of OpenAI, Positively curved Einstein four-manifolds (result family 348)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PositiveEinsteinFour.classification`, `OAI.PositiveEinsteinFour.classificationOn` and `OAI.PositiveEinsteinFour.orientedClassification`, carved from OpenAI's openai/math development (OpenAI, *Positively curved Einstein four-manifolds (result family 348)*, OpenAI Math Release, September 23, 2026, result family 348, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 86 declarations of OpenAI's Lean: 24 definitions, 1 instance and 61 theorems. The definitions and types are `OAI.PositiveEinsteinFour.Angular.angularPairingLinear`, `OAI.PositiveEinsteinFour.Angular.coefficientTable`, `OAI.PositiveEinsteinFour.Angular.coordinateFlip`, `OAI.PositiveEinsteinFour.Angular.coordinatePermutation`, `OAI.PositiveEinsteinFour.Angular.directionIsometry`, `OAI.PositiveEinsteinFour.Angular.directional`, `OAI.PositiveEinsteinFour.Angular.fiveOmit`, `OAI.PositiveEinsteinFour.Angular.fiveProduct`, `OAI.PositiveEinsteinFour.Angular.mixing`, `OAI.PositiveEinsteinFour.Angular.mixingCoefficient`, `OAI.PositiveEinsteinFour.Angular.pairMix`, `OAI.PositiveEinsteinFour.Angular.pairMixLinear`, `OAI.PositiveEinsteinFour.Angular.pairing`, `OAI.PositiveEinsteinFour.Angular.planeCoordinateDerivative`, `OAI.PositiveEinsteinFour.Angular.planeIsometry`, `OAI.PositiveEinsteinFour.Angular.planeLinear`, `OAI.PositiveEinsteinFour.Angular.planeRotation`, `OAI.PositiveEinsteinFour.Angular.quadratic`, `OAI.PositiveEinsteinFour.Angular.sphereRotationGenerator`, `OAI.PositiveEinsteinFour.Angular.sphericalIntegralCLM`, `OAI.PositiveEinsteinFour.Angular.sphericalIntegralLinear`, `OAI.PositiveEinsteinFour.Angular.sphericalIntegralNormedGroup`, `OAI.PositiveEinsteinFour.Angular.sphericalIntegralNormedSpace`, `OAI.PositiveEinsteinFour.Angular.tailProjection`.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `EinsteinFour_ActualSphericalMoments`, `EinsteinFour_AngularDerivativeMoments`, `EinsteinFour_AngularGradient`, `EinsteinFour_AngularNormal`, `EinsteinFour_AngularQuadratic`, `EinsteinFour_AngularRotation`, `EinsteinFour_AngularSixth`, `EinsteinFour_CurvatureTensors02`, `EinsteinFour_SphericalFourthMoment`, `EinsteinFour_SphericalIntegralDerivative`, `EinsteinFour_SphericalMeasureCharts`, `EinsteinFour_SphericalMeasureInvariance`, `EinsteinFour_SphericalMeasureMass`, `EinsteinFour_SphericalMomentRecurrence`, `EinsteinFour_SphericalMoments`, `EinsteinFour_SphericalPairMix`, `EinsteinFour_SphericalRotation`, `EinsteinFour_SphericalSecondMoment`, `EinsteinFour_SphericalSixthMoment`, `EinsteinFour_WeylEstimates01`.
--
--   **Imports.** It imports the published bundle `Def_EinsteinFour`; the bundles `OAIQ091C000` and `OAIQ091C001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ091C016` and `OAIQ091C035`.
-- source:
--   OpenAI, Positively curved Einstein four-manifolds (result family 348), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 348; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Positively-curved-Einstein-four-manifolds-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_EinsteinFour
import Definitions.Def_OAIQ091C000
import Definitions.Def_OAIQ091C001

section
-- module Solutions.OAIQ091_EF.EinsteinFour_SphericalMoments
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceSubtypeMatrixFinOfNatNatRealMemSubmonoidOrientedOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite sphere moments needed for the angular Jacobi calculation.
The conditional input below is precisely the degree 2, 4 and 6 specialization
of Folland, *How to Integrate a Polynomial over a Sphere*, American
Mathematical Monthly 108 (2001), 446–448, Theorem on p.447, after division by
the area of S³. DOI: 10.1080/00029890.2001.11919774.
It contains no curvature or geometric inequality.
-/

namespace PositiveEinsteinFour.Angular

open EinsteinFour MeasureTheory

noncomputable section

instance instCompactSpaceDirections : CompactSpace Directions := by
  apply isCompact_iff_compactSpace.mp
  simpa only [Metric.sphere, dist_zero_right] using! isCompact_sphere (0 : FourSpace) 1

theorem continuous_integrable (h : FollandMoments) {f : Directions → ℝ}
    (hf : Continuous f) : Integrable f sphereMeasure := by
  let : IsProbabilityMeasure sphereMeasure := h.probability
  exact hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

end

end PositiveEinsteinFour.Angular

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_SphericalMeasureInvariance
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceSubtypeMatrixFinOfNatNatRealMemSubmonoidOrientedOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed Hausdorff spherical measure is invariant under all orthogonal
changes of coordinates. This is the measure-theoretic input for the finite
second, fourth and sixth moment computation. -/

namespace PositiveEinsteinFour.Angular

open EinsteinFour MeasureTheory

noncomputable section

def directionIsometry (e : FourSpace ≃ₗᵢ[ℝ] FourSpace) : Directions ≃ᵢ Directions where
  toFun q := ⟨e q.val, (e.norm_map q.val).trans q.property⟩
  invFun q := ⟨e.symm q.val, (e.symm.norm_map q.val).trans q.property⟩
  left_inv q := Subtype.ext (e.symm_apply_apply q.val)
  right_inv q := Subtype.ext (e.apply_symm_apply q.val)
  isometry_toFun := fun q r => e.isometry q.val r.val

theorem sphereMeasure_preserving (e : Directions ≃ᵢ Directions) :
    MeasurePreserving e sphereMeasure sphereMeasure := by
  constructor
  · exact e.continuous.measurable
  · unfold sphereMeasure
    rw [Measure.map_smul, e.map_hausdorffMeasure]

theorem sphereIntegral_isometry (e : Directions ≃ᵢ Directions) (f : Directions → ℝ) :
    (∫ q, f (e q) ∂sphereMeasure) = ∫ q, f q ∂sphereMeasure := by
  exact (sphereMeasure_preserving e).integral_comp e.toHomeomorph.measurableEmbedding f

end
end PositiveEinsteinFour.Angular

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_SphericalMeasureCharts
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact smooth coordinate-face charts and a Lipschitz projection for the
actual unit three-sphere. These are used only to establish finite positive
Hausdorff mass; no spherical integration formula is assumed. -/

namespace PositiveEinsteinFour.Angular

open EinsteinFour MeasureTheory
open scoped BigOperators ContDiff _root_.Topology NNReal

noncomputable section

theorem faceVector_contDiff (i : Fin 4) (t : Bool) :
    ContDiff ℝ ∞ (faceVector i t) := by
  apply (contDiff_piLp (p := (2 : ENNReal))).mpr
  intro k
  rcases Fin.eq_self_or_eq_succAbove i k with rfl | ⟨j, rfl⟩
  · simpa only [faceVector, PiLp.toLp_apply, Fin.insertNth_apply_same] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : ThreeSpace => faceSign t))
  · simpa only [faceVector, PiLp.toLp_apply, Fin.insertNth_apply_succAbove] using
      (contDiff_piLp_apply (p := (2 : ENNReal)) (i := j) :
        ContDiff ℝ ∞ (fun u : ThreeSpace => u j))

theorem faceChart_contDiff (i : Fin 4) (t : Bool) : ContDiff ℝ ∞ (faceChart i t) := by
  have hf := faceVector_contDiff i t
  have hn := hf.norm ℝ (faceVector_ne_zero i t)
  exact (hn.inv (fun u => norm_ne_zero_iff.mpr (faceVector_ne_zero i t u))).smul hf

theorem faceChart_lipschitz (i : Fin 4) (t : Bool) :
    ∃ K : ℝ≥0, LipschitzOnWith K (faceChart i t) (Metric.closedBall (0 : ThreeSpace) 2) :=
  (faceChart_contDiff i t).contDiffOn.exists_lipschitzOnWith (by first | simp | exact_mod_cast le_top)
    (convex_closedBall _ _) (isCompact_closedBall _ _)

/-- The eight normalized cube faces cover the sphere using a fixed compact
three-dimensional parameter ball. -/
theorem exists_faceChart (q : Directions) :
    ∃ i : Fin 4, ∃ t : Bool, ∃ u ∈ Metric.closedBall (0 : ThreeSpace) 2,
      faceChart i t u = q.val := by
  classical
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ
    (fun i : Fin 4 => |q.val i|) Finset.univ_nonempty
  have hmax (j : Fin 4) : |q.val j| ≤ |q.val i| := hi j (Finset.mem_univ j)
  have hqi : q.val i ≠ 0 := by
    intro he
    have hz : q.val = 0 := by
      ext j
      exact abs_eq_zero.mp (le_antisymm (by simpa [he] using hmax j) (abs_nonneg _))
    have := q.property
    rw [hz, norm_zero] at this
    norm_num at this
  have ha : 0 < |q.val i| := abs_pos.mpr hqi
  obtain ⟨t, ht⟩ : ∃ t : Bool, faceSign t = q.val i / |q.val i| := by
    by_cases hp : 0 < q.val i
    · refine ⟨true, ?_⟩
      simp [faceSign, abs_of_pos hp, hqi]
    · have hn : q.val i < 0 := lt_of_le_of_ne (le_of_not_gt hp) hqi
      refine ⟨false, ?_⟩
      simp [faceSign, abs_of_neg hn, hqi]
  let u : ThreeSpace := WithLp.toLp 2 (fun j => q.val (i.succAbove j) / |q.val i|)
  have hub (j : Fin 3) : |u j| ≤ 1 := by
    change |q.val (i.succAbove j) / (|q.val i|)| ≤ 1
    rw [abs_div, abs_abs, div_le_one ha]
    exact hmax _
  have husq : ‖u‖ ^ 2 ≤ 3 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _ ≤ ∑ _j : Fin 3, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro j _
        have h := hub j
        have hn := abs_nonneg (u j)
        nlinarith [sq_abs (u j)]
      _ = 3 := by norm_num
  have hu : u ∈ Metric.closedBall (0 : ThreeSpace) 2 := by
    rw [Metric.mem_closedBall, dist_zero_right]
    nlinarith [norm_nonneg u]
  have hraw : faceVector i t u = |q.val i|⁻¹ • q.val := by
    ext j
    rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩
    · simp only [faceVector, PiLp.toLp_apply, Fin.insertNth_apply_same,
        ht, PiLp.smul_apply, smul_eq_mul]
      ring
    · simp only [faceVector, PiLp.toLp_apply, Fin.insertNth_apply_succAbove,
        u, PiLp.smul_apply, smul_eq_mul]
      ring
  refine ⟨i, t, u, hu, ?_⟩
  unfold faceChart
  rw [hraw, norm_smul_of_nonneg (inv_nonneg.mpr ha.le), q.property, mul_one,
    inv_inv, smul_smul, mul_inv_cancel₀ ha.ne', one_smul]

/-- Dropping one coordinate does not increase Euclidean distance. -/
def tailProjection (v : FourSpace) : ThreeSpace :=
  WithLp.toLp 2 (fun j => v j.succ)

theorem tailProjection_norm_le (v : FourSpace) : ‖tailProjection v‖ ≤ ‖v‖ := by
  have h : ‖v‖ ^ 2 = (v 0) ^ 2 + ‖tailProjection v‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ,
      EuclideanSpace.real_norm_sq_eq]
    rfl
  nlinarith [sq_nonneg (v 0), norm_nonneg v, norm_nonneg (tailProjection v)]

theorem tailProjection_lipschitz : LipschitzWith 1 tailProjection := by
  apply LipschitzWith.mk_one
  intro v w
  rw [dist_eq_norm, dist_eq_norm]
  have he : tailProjection v - tailProjection w = tailProjection (v - w) := rfl
  rw [he]
  exact tailProjection_norm_le (v - w)

/-- The projection of the actual sphere contains a nonempty open ball. -/
theorem ball_subset_tailProjection_sphere :
    Metric.ball (0 : ThreeSpace) 1 ⊆
      tailProjection '' {v : FourSpace | ‖v‖ = 1} := by
  intro u hu
  have hnorm : ‖u‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hu
  have hrad : 0 ≤ 1 - ‖u‖ ^ 2 := by nlinarith [norm_nonneg u]
  let v : FourSpace := WithLp.toLp 2 (Fin.cons (Real.sqrt (1 - ‖u‖ ^ 2)) (fun j => u j))
  have hv : ‖v‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]
    change (Real.sqrt (1 - ‖u‖ ^ 2)) ^ 2 + (∑ j : Fin 3, (u j) ^ 2) = 1
    rw [Real.sq_sqrt hrad, ← EuclideanSpace.real_norm_sq_eq u]
    ring
  refine ⟨v, ?_, ?_⟩
  · change ‖v‖ = 1
    nlinarith [norm_nonneg v]
  · ext j
    rfl

end
end PositiveEinsteinFour.Angular

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_SphericalMeasureMass
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceSubtypeMatrixFinOfNatNatRealMemSubmonoidOrientedOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite positive mass of the actual Hausdorff measure on the unit
three-sphere, and hence the probability normalization used by the moments. -/

namespace PositiveEinsteinFour.Angular

open EinsteinFour MeasureTheory
open scoped BigOperators

noncomputable section

/-- Compact smooth face images have finite three-dimensional measure. -/
theorem faceChart_measure_lt_top (i : Fin 4) (t : Bool) :
    (Measure.hausdorffMeasure 3 : Measure FourSpace)
      (faceChart i t '' Metric.closedBall (0 : ThreeSpace) 2) < ⊤ := by
  let _ := threeSpace_hausdorff_haar
  obtain ⟨K, hK⟩ := faceChart_lipschitz i t
  have hB : (Measure.hausdorffMeasure 3 : Measure ThreeSpace)
      (Metric.closedBall 0 2) < ⊤ := (isCompact_closedBall _ _).measure_lt_top
  refine lt_of_le_of_lt (hK.hausdorffMeasure_image_le (by norm_num : (0 : ℝ) ≤ 3)) ?_
  rw [show (3 : ℝ) = (3 : ℕ) by norm_num, ENNReal.rpow_natCast]
  exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top) hB

theorem sphere_hausdorff_measure_lt_top :
    (Measure.hausdorffMeasure 3 : Measure FourSpace) {v | ‖v‖ = 1} < ⊤ := by
  have hc : {v : FourSpace | ‖v‖ = 1} ⊆
      ⋃ a : Fin 4 × Bool, faceChart a.1 a.2 '' Metric.closedBall (0 : ThreeSpace) 2 := by
    intro v hv
    obtain ⟨i, t, u, hu, he⟩ := exists_faceChart ⟨v, hv⟩
    exact Set.mem_iUnion.mpr ⟨(i,t), u, hu, he⟩
  apply lt_of_le_of_lt (measure_mono hc)
  simpa only [Set.biUnion_univ] using
    (measure_biUnion_lt_top (μ := (Measure.hausdorffMeasure 3 : Measure FourSpace))
      (s := (Set.univ : Set (Fin 4 × Bool))) Set.finite_univ
      (fun a _ => faceChart_measure_lt_top a.1 a.2))

theorem sphere_hausdorff_measure_pos :
    0 < (Measure.hausdorffMeasure 3 : Measure FourSpace) {v | ‖v‖ = 1} := by
  let _ := threeSpace_hausdorff_haar
  have hb : 0 < (Measure.hausdorffMeasure 3 : Measure ThreeSpace)
      (Metric.ball (0 : ThreeSpace) 1) :=
    Metric.isOpen_ball.measure_pos _ (Metric.nonempty_ball.mpr (by norm_num))
  have hp := tailProjection_lipschitz.hausdorffMeasure_image_le
    (by norm_num : (0 : ℝ) ≤ 3) {v : FourSpace | ‖v‖ = 1}
  simp only [ENNReal.coe_one, ENNReal.one_rpow, one_mul] at hp
  exact lt_of_lt_of_le (lt_of_lt_of_le hb (measure_mono ball_subset_tailProjection_sphere)) hp

theorem direction_hausdorff_mass_pos :
    0 < (Measure.hausdorffMeasure 3 : Measure Directions) Set.univ := by
  rw [direction_hausdorff_mass_eq]
  exact sphere_hausdorff_measure_pos

theorem direction_hausdorff_mass_lt_top :
    (Measure.hausdorffMeasure 3 : Measure Directions) Set.univ < ⊤ := by
  rw [direction_hausdorff_mass_eq]
  exact sphere_hausdorff_measure_lt_top

/-- The concrete normalization is a genuine probability measure. -/
theorem actual_sphereMeasure_probability : IsProbabilityMeasure sphereMeasure := by
  constructor
  unfold sphereMeasure
  rw [Measure.smul_apply, smul_eq_mul,
    ENNReal.inv_mul_cancel direction_hausdorff_mass_pos.ne'
      direction_hausdorff_mass_lt_top.ne]

end
end PositiveEinsteinFour.Angular

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_SphericalSecondMoment
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceSubtypeMatrixFinOfNatNatRealMemSubmonoidOrientedOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The quadratic spherical moment follows from actual Hausdorff-measure
invariance and the unit-sphere equation. Only probability normalization is
needed; no moment identity is assumed. -/

namespace PositiveEinsteinFour.Angular

open EinsteinFour MeasureTheory

noncomputable section

def coordinateFlip (i : Fin 4) : Directions ≃ᵢ Directions :=
  directionIsometry (LinearIsometryEquiv.piLpCongrRight 2 (fun j : Fin 4 =>
    if j = i then (LinearIsometryEquiv.neg ℝ : ℝ ≃ₗᵢ[ℝ] ℝ) else
      LinearIsometryEquiv.refl ℝ ℝ))

@[simp] theorem coordinateFlip_apply (i j : Fin 4) (q : Directions) :
    (coordinateFlip i q).val j = if j = i then -q.val j else q.val j := by
  classical
  by_cases h : j = i <;>
    simp [coordinateFlip, directionIsometry, LinearIsometryEquiv.piLpCongrRight_apply, h]

def coordinatePermutation (p : Equiv.Perm (Fin 4)) : Directions ≃ᵢ Directions :=
  directionIsometry (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ p)

@[simp] theorem coordinatePermutation_apply (p : Equiv.Perm (Fin 4))
    (q : Directions) (j : Fin 4) :
    (coordinatePermutation p q).val j = q.val (p.symm j) := rfl

theorem sphereIntegral_odd (e : Directions ≃ᵢ Directions) (f : Directions → ℝ)
    (h : ∀ q, f (e q) = -f q) : (∫ q, f q ∂sphereMeasure) = 0 := by
  have hi := sphereIntegral_isometry e f
  have heq : (fun q => f (e q)) = fun q => -f q := funext h
  rw [heq, integral_neg] at hi
  linarith

theorem integral_coordinate_mul_zero (i j : Fin 4) (hij : i ≠ j) :
    (∫ q : Directions, q.val i * q.val j ∂sphereMeasure) = 0 := by
  apply sphereIntegral_odd (coordinateFlip i)
  intro q
  simp [hij.symm]

theorem integral_coordinate_pow_eq (i j : Fin 4) (n : ℕ) :
    (∫ q : Directions, q.val i ^ n ∂sphereMeasure) =
      ∫ q : Directions, q.val j ^ n ∂sphereMeasure := by
  have h := sphereIntegral_isometry (coordinatePermutation (Equiv.swap i j))
    (fun q : Directions => q.val i ^ n)
  simpa using h.symm

theorem integral_coordinate_square_eq (i j : Fin 4) :
    (∫ q : Directions, q.val i ^ 2 ∂sphereMeasure) =
      ∫ q : Directions, q.val j ^ 2 ∂sphereMeasure :=
  integral_coordinate_pow_eq i j 2

theorem integral_two_powers_odd (i j : Fin 4) (hij : i ≠ j) (n m : ℕ)
    (hn : Odd n) :
    (∫ q : Directions, q.val i ^ n * q.val j ^ m ∂sphereMeasure) = 0 := by
  apply sphereIntegral_odd (coordinateFlip i)
  intro q
  simp only [coordinateFlip_apply, ite_true, if_true, ite_eq_right hij.symm, hn.neg_pow, neg_mul]

theorem sum_coordinate_sq (q : Directions) : (∑ i, q.val i ^ 2) = 1 := by
  rw [← EuclideanSpace.real_norm_sq_eq, q.property]
  norm_num

variable [IsProbabilityMeasure sphereMeasure]

theorem sphere_continuous_integrable {f : Directions → ℝ} (hf : Continuous f) :
    Integrable f sphereMeasure :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

theorem integral_coordinate_square (i : Fin 4) :
    (∫ q : Directions, q.val i ^ 2 ∂sphereMeasure) = 1 / 4 := by
  have hi (j : Fin 4) : Integrable (fun q : Directions => q.val j ^ 2) sphereMeasure :=
    sphere_continuous_integrable ((continuous_coordinate j).pow 2)
  have hs : (∑ j : Fin 4, ∫ q : Directions, q.val j ^ 2 ∂sphereMeasure) = 1 := by
    rw [← integral_finsetSum _ (fun j _ => hi j)]
    simp_rw [sum_coordinate_sq]
    simp
  have heq (j : Fin 4) := integral_coordinate_square_eq j i
  simp_rw [heq] at hs
  norm_num at hs
  linarith

theorem actual_spherical_second (i j : Fin 4) :
    (∫ q : Directions, q.val i * q.val j ∂sphereMeasure) = momentTwo i j := by
  by_cases hij : i = j
  · subst j
    simpa [momentTwo, delta, pow_two] using integral_coordinate_square i
  · rw [integral_coordinate_mul_zero i j hij]
    simp [momentTwo, delta, hij]

end
end PositiveEinsteinFour.Angular

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_SphericalPairMix
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A forty-five degree orthogonal change in a coordinate plane. This fixed
finite-dimensional change gives the fourth and sixth sphere moments. -/

namespace PositiveEinsteinFour.Angular

open EinsteinFour

noncomputable section

def pairMixLinear (i j : Fin 4) : FourSpace →ₗ[ℝ] FourSpace where
  toFun q := WithLp.toLp 2 (fun k => if k = i then (q i + q j) / Real.sqrt 2 else
    if k = j then (q i - q j) / Real.sqrt 2 else q k)
  map_add' q r := by
    ext k
    by_cases hki : k = i
    · subst k
      simp only [PiLp.add_apply, ite_true, if_true]
      ring
    · by_cases hkj : k = j
      · subst k
        simp only [PiLp.add_apply, ite_eq_right hki, ite_true, if_true]
        ring
      · simp [hki, hkj]
  map_smul' a q := by
    ext k
    by_cases hki : k = i
    · subst k
      simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply, ite_true, if_true]
      ring
    · by_cases hkj : k = j
      · subst k
        simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply, ite_eq_right hki, ite_true, if_true]
        ring
      · simp [hki, hkj]

theorem pairMix_apply (i j k : Fin 4) (q : FourSpace) :
    pairMixLinear i j q k = if k = i then (q i + q j) / Real.sqrt 2 else
      if k = j then (q i - q j) / Real.sqrt 2 else q k := rfl

theorem pairMix_norm (i j : Fin 4) (hij : i ≠ j) (q : FourSpace) :
    ‖pairMixLinear i j q‖ = ‖q‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  have hd (k : Fin 4) : (pairMixLinear i j q k) ^ 2 - q k ^ 2 =
      (if k = i then ((q i + q j) / Real.sqrt 2) ^ 2 - q i ^ 2 else 0) +
      (if k = j then ((q i - q j) / Real.sqrt 2) ^ 2 - q j ^ 2 else 0) := by
    by_cases hki : k = i
    · subst k
      simp [pairMix_apply, hij]
    · by_cases hkj : k = j
      · subst k
        simp [pairMix_apply, hij.symm]
      · simp [pairMix_apply, hki, hkj]
  have hs : (∑ k : Fin 4, ((pairMixLinear i j q k) ^ 2 - q k ^ 2)) = 0 := by
    simp_rw [hd]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]
    rw [div_pow, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  rw [Finset.sum_sub_distrib] at hs
  linarith

theorem pairMix_involutive (i j : Fin 4) (hij : i ≠ j) :
    Function.Involutive (pairMixLinear i j) := by
  intro q
  ext k
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  by_cases hki : k = i
  · subst k
    simp only [pairMix_apply, ite_true, if_true, ite_eq_right hij.symm]
    calc
      _ = (2 * q i) / (Real.sqrt 2 ^ 2) := by ring
      _ = _ := by rw [hs]; ring
  · by_cases hkj : k = j
    · subst k
      simp only [pairMix_apply, ite_eq_right hij.symm, ite_eq_left]
      calc
        _ = (2 * q j) / (Real.sqrt 2 ^ 2) := by ring
        _ = _ := by rw [hs]; ring
    · simp [pairMix_apply, hki, hkj]

def pairMix (i j : Fin 4) (hij : i ≠ j) : FourSpace ≃ₗᵢ[ℝ] FourSpace where
  toLinearEquiv :=
    { pairMixLinear i j with
      invFun := pairMixLinear i j
      left_inv := pairMix_involutive i j hij
      right_inv := pairMix_involutive i j hij }
  norm_map' := pairMix_norm i j hij

@[simp] theorem pairMix_coordinate (i j : Fin 4) (hij : i ≠ j)
    (q : FourSpace) (k : Fin 4) :
    pairMix i j hij q k = if k = i then (q i + q j) / Real.sqrt 2 else
      if k = j then (q i - q j) / Real.sqrt 2 else q k := rfl

end
end PositiveEinsteinFour.Angular

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_SphericalFourthMoment
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceSubtypeMatrixFinOfNatNatRealMemSubmonoidOrientedOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The quartic sphere moments from the explicit orthogonal coordinate
changes. Probability normalization remains separate from the moment proof. -/

namespace PositiveEinsteinFour.Angular

open EinsteinFour MeasureTheory

noncomputable section

variable [IsProbabilityMeasure sphereMeasure]

omit [IsProbabilityMeasure sphereMeasure] in
theorem sqrt_two_fourth : Real.sqrt 2 ^ 4 = 4 := by
  calc
    _ = (Real.sqrt 2 ^ 2) ^ 2 := by ring
    _ = 4 := by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num

theorem integral_fourth_three_mixed (i j : Fin 4) (hij : i ≠ j) :
    (∫ q : Directions, q.val i ^ 4 ∂sphereMeasure) =
      3 * ∫ q : Directions, q.val i ^ 2 * q.val j ^ 2 ∂sphereMeasure := by
  let f : Fin 5 → Directions → ℝ := ![
    fun q => q.val i ^ 4,
    fun q => 4 * (q.val i ^ 3 * q.val j),
    fun q => 6 * (q.val i ^ 2 * q.val j ^ 2),
    fun q => 4 * (q.val i * q.val j ^ 3),
    fun q => q.val j ^ 4]
  have hf (k : Fin 5) : Integrable (f k) sphereMeasure := by
    fin_cases k <;> dsimp [f] <;> apply sphere_continuous_integrable <;> fun_prop
  have hp (q : Directions) : (∑ k, f k q) =
      4 * ((q.val i + q.val j) / Real.sqrt 2) ^ 4 := by
    have he : q.val i ^ 4 + 4 * (q.val i ^ 3 * q.val j) +
        6 * (q.val i ^ 2 * q.val j ^ 2) + 4 * (q.val i * q.val j ^ 3) + q.val j ^ 4 =
        4 * ((q.val i + q.val j) / Real.sqrt 2) ^ 4 := by
      rw [div_pow, sqrt_two_fourth]
      ring
    simpa [f, Fin.sum_univ_succ, add_assoc] using he
  have hr := sphereIntegral_isometry (directionIsometry (pairMix i j hij))
    (fun q : Directions => q.val i ^ 4)
  have hr' : (∫ q : Directions, ((q.val i + q.val j) / Real.sqrt 2) ^ 4 ∂sphereMeasure) =
      ∫ q : Directions, q.val i ^ 4 ∂sphereMeasure := by
    change (∫ q : Directions, (pairMix i j hij q.val i) ^ 4 ∂sphereMeasure) = _ at hr
    simpa only [pairMix_coordinate, ite_true, if_true] using hr
  have hs : (∑ k, ∫ q, f k q ∂sphereMeasure) =
      4 * ∫ q : Directions, q.val i ^ 4 ∂sphereMeasure := by
    rw [← integral_finsetSum _ (fun k _ => hf k)]
    calc
      _ = ∫ q : Directions, 4 * ((q.val i + q.val j) / Real.sqrt 2) ^ 4 ∂sphereMeasure :=
        integral_congr_ae (Filter.Eventually.of_forall hp)
      _ = _ := by rw [integral_const_mul, hr']
  have hz31 := integral_two_powers_odd i j hij 3 1 (by decide)
  have hz13 := integral_two_powers_odd i j hij 1 3 (by decide)
  simp only [pow_one] at hz31 hz13
  simp [f, Fin.sum_univ_succ, integral_const_mul, hz31, hz13] at hs
  rw [integral_coordinate_pow_eq j i 4] at hs
  linarith

omit [IsProbabilityMeasure sphereMeasure] in
theorem sum_single_exception (i : Fin 4) (a b : ℝ) :
    (∑ j : Fin 4, if j = i then a else b) = a + 3 * b := by
  have he (j : Fin 4) : (if j = i then a else b) =
      (if j = i then a - b else 0) + b := by
    split_ifs <;> ring
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem integral_coordinate_fourth (i : Fin 4) :
    (∫ q : Directions, q.val i ^ 4 ∂sphereMeasure) = 1 / 8 := by
  have hi (j : Fin 4) : Integrable
      (fun q : Directions => q.val i ^ 2 * q.val j ^ 2) sphereMeasure :=
    sphere_continuous_integrable (by fun_prop)
  have hs : (∑ j : Fin 4, ∫ q : Directions, q.val i ^ 2 * q.val j ^ 2 ∂sphereMeasure) =
      1 / 4 := by
    rw [← integral_finsetSum _ (fun j _ => hi j)]
    have he (q : Directions) : (∑ j, q.val i ^ 2 * q.val j ^ 2) = q.val i ^ 2 := by
      rw [← Finset.mul_sum, sum_coordinate_sq, mul_one]
    simp_rw [he]
    exact integral_coordinate_square i
  have he (j : Fin 4) :
      (∫ q : Directions, q.val i ^ 2 * q.val j ^ 2 ∂sphereMeasure) =
      if j = i then (∫ q : Directions, q.val i ^ 4 ∂sphereMeasure) else
        (∫ q : Directions, q.val i ^ 4 ∂sphereMeasure) / 3 := by
    by_cases hji : j = i
    · subst j
      simp only [ite_true, if_true, ← pow_add]
    · rw [ite_eq_right hji]
      have h := integral_fourth_three_mixed i j (Ne.symm hji)
      linarith
  simp_rw [he] at hs
  rw [sum_single_exception] at hs
  linarith

theorem integral_coordinate_square_square (i j : Fin 4) (hij : i ≠ j) :
    (∫ q : Directions, q.val i ^ 2 * q.val j ^ 2 ∂sphereMeasure) = 1 / 24 := by
  have h := integral_fourth_three_mixed i j hij
  rw [integral_coordinate_fourth] at h
  linarith

theorem actual_spherical_fourth (i j k l : Fin 4) :
    (∫ q : Directions, q.val i * q.val j * q.val k * q.val l ∂sphereMeasure) =
      momentFour i j k l := by
  by_cases hij : i = j
  · subst j
    by_cases hik : i = k
    · subst k
      by_cases hil : i = l
      · subst l
        have he : (fun q : Directions => q.val i * q.val i * q.val i * q.val i) =
            fun q => q.val i ^ 4 := by funext q; ring
        rw [he, integral_coordinate_fourth]
        norm_num [momentFour, delta]
      · have hz : (∫ q : Directions, q.val i * q.val i * q.val i * q.val l
            ∂sphereMeasure) = 0 := by
          apply sphereIntegral_odd (coordinateFlip l)
          intro q
          simp [hil]
        rw [hz]
        simp [momentFour, delta, hil]
    · by_cases hkl : k = l
      · subst l
        have he : (fun q : Directions => q.val i * q.val i * q.val k * q.val k) =
            fun q => q.val i ^ 2 * q.val k ^ 2 := by funext q; ring
        rw [he, integral_coordinate_square_square i k hik]
        simp [momentFour, delta, hik]
      · have hz : (∫ q : Directions, q.val i * q.val i * q.val k * q.val l
            ∂sphereMeasure) = 0 := by
          apply sphereIntegral_odd (coordinateFlip k)
          intro q
          simp [hik, (Ne.symm hkl)]
        rw [hz]
        simp [momentFour, delta, hik, hkl]
  · by_cases hik : i = k
    · subst k
      by_cases hjl : j = l
      · subst l
        have he : (fun q : Directions => q.val i * q.val j * q.val i * q.val j) =
            fun q => q.val i ^ 2 * q.val j ^ 2 := by funext q; ring
        rw [he, integral_coordinate_square_square i j hij]
        simp [momentFour, delta, hij, (Ne.symm hij)]
      · have hz : (∫ q : Directions, q.val i * q.val j * q.val i * q.val l
            ∂sphereMeasure) = 0 := by
          apply sphereIntegral_odd (coordinateFlip j)
          intro q
          simp [hij, (Ne.symm hjl)]
        rw [hz]
        simp [momentFour, delta, hij, (Ne.symm hij), hjl]
    · by_cases hil : i = l
      · subst l
        by_cases hjk : j = k
        · subst k
          have he : (fun q : Directions => q.val i * q.val j * q.val j * q.val i) =
              fun q => q.val i ^ 2 * q.val j ^ 2 := by funext q; ring
          rw [he, integral_coordinate_square_square i j hij]
          simp [momentFour, delta, hij, (Ne.symm hij)]
        · have hz : (∫ q : Directions, q.val i * q.val j * q.val k * q.val i
              ∂sphereMeasure) = 0 := by
            apply sphereIntegral_odd (coordinateFlip j)
            intro q
            simp [hij, (Ne.symm hjk)]
          rw [hz]
          simp [momentFour, delta, hij, (Ne.symm hij), hik, (Ne.symm hik), hjk]
      · have hz : (∫ q : Directions, q.val i * q.val j * q.val k * q.val l
            ∂sphereMeasure) = 0 := by
          apply sphereIntegral_odd (coordinateFlip i)
          intro q
          simp [(Ne.symm hij), (Ne.symm hik), (Ne.symm hil)]
        rw [hz]
        simp [momentFour, delta, hij, hik, hil]

end
end PositiveEinsteinFour.Angular

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_SphericalRotation
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual coordinate-plane rotations on the unit sphere, with their
ordinary derivatives. These yield the sixth-moment recurrence. -/

namespace PositiveEinsteinFour.Angular

open EinsteinFour

noncomputable section

def planeLinear (i j : Fin 4) (a b : ℝ) : FourSpace →ₗ[ℝ] FourSpace where
  toFun q := WithLp.toLp 2 (fun k => if k = i then a * q i + b * q j else
    if k = j then a * q j - b * q i else q k)
  map_add' q r := by
    ext k
    by_cases hki : k = i
    · subst k
      simp only [PiLp.add_apply, ite_true, if_true]
      ring
    · by_cases hkj : k = j
      · subst k
        simp only [PiLp.add_apply, ite_eq_right hki, ite_true, if_true]
        ring
      · simp [hki, hkj]
  map_smul' c q := by
    ext k
    by_cases hki : k = i
    · subst k
      simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply, ite_true, if_true]
      ring
    · by_cases hkj : k = j
      · subst k
        simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply,
          ite_eq_right hki, ite_true, if_true]
        ring
      · simp [hki, hkj]

theorem planeLinear_apply (i j k : Fin 4) (a b : ℝ) (q : FourSpace) :
    planeLinear i j a b q k = if k = i then a * q i + b * q j else
      if k = j then a * q j - b * q i else q k := rfl

theorem planeLinear_norm (i j : Fin 4) (hij : i ≠ j)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) (q : FourSpace) :
    ‖planeLinear i j a b q‖ = ‖q‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  have hd (k : Fin 4) : (planeLinear i j a b q k) ^ 2 - q k ^ 2 =
      (if k = i then (a * q i + b * q j) ^ 2 - q i ^ 2 else 0) +
      (if k = j then (a * q j - b * q i) ^ 2 - q j ^ 2 else 0) := by
    by_cases hki : k = i
    · subst k
      simp [planeLinear_apply, hij]
    · by_cases hkj : k = j
      · subst k
        simp [planeLinear_apply, hij.symm]
      · simp [planeLinear_apply, hki, hkj]
  have hs : (∑ k : Fin 4, ((planeLinear i j a b q k) ^ 2 - q k ^ 2)) = 0 := by
    simp_rw [hd]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]
    calc
      _ = (a ^ 2 + b ^ 2 - 1) * (q i ^ 2 + q j ^ 2) := by ring
      _ = 0 := by rw [hab]; ring
  rw [Finset.sum_sub_distrib] at hs
  linarith

theorem planeLinear_inverse (i j : Fin 4) (hij : i ≠ j)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    Function.LeftInverse (planeLinear i j a (-b)) (planeLinear i j a b) := by
  intro q
  ext k
  by_cases hki : k = i
  · subst k
    simp only [planeLinear_apply, ite_true, if_true, ite_eq_right hij.symm]
    calc
      _ = (a ^ 2 + b ^ 2) * q i := by ring
      _ = _ := by rw [hab]; ring
  · by_cases hkj : k = j
    · subst k
      simp only [planeLinear_apply, ite_true, if_true, ite_eq_right hij.symm]
      calc
        _ = (a ^ 2 + b ^ 2) * q j := by ring
        _ = _ := by rw [hab]; ring
    · simp [planeLinear_apply, hki, hkj]

def planeIsometry (i j : Fin 4) (hij : i ≠ j)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) : FourSpace ≃ₗᵢ[ℝ] FourSpace where
  toLinearEquiv :=
    { planeLinear i j a b with
      invFun := planeLinear i j a (-b)
      left_inv := planeLinear_inverse i j hij a b hab
      right_inv := by
        intro q
        change planeLinear i j a b (planeLinear i j a (-b) q) = q
        have h := planeLinear_inverse i j hij a (-b) (by simpa using hab)
        simpa only [neg_neg] using h q }
  norm_map' := planeLinear_norm i j hij a b hab

def planeRotation (i j : Fin 4) (hij : i ≠ j) (t : ℝ) :
    FourSpace ≃ₗᵢ[ℝ] FourSpace :=
  planeIsometry i j hij (Real.cos t) (Real.sin t) (by
    nlinarith [Real.sin_sq_add_cos_sq t])

@[simp] theorem planeRotation_apply (i j : Fin 4) (hij : i ≠ j)
    (t : ℝ) (q : FourSpace) (k : Fin 4) :
    planeRotation i j hij t q k =
      if k = i then Real.cos t * q i + Real.sin t * q j else
      if k = j then Real.cos t * q j - Real.sin t * q i else q k := rfl

theorem planeRotation_zero (i j : Fin 4) (hij : i ≠ j) (q : FourSpace) :
    planeRotation i j hij 0 q = q := by
  ext k
  simp only [planeRotation_apply, Real.cos_zero, Real.sin_zero, one_mul, zero_mul,
    add_zero, sub_zero]
  split_ifs <;> simp_all

def planeCoordinateDerivative (i j : Fin 4) (t : ℝ) (q : FourSpace) (k : Fin 4) : ℝ :=
  if k = i then -Real.sin t * q i + Real.cos t * q j else
    if k = j then -Real.sin t * q j - Real.cos t * q i else 0

theorem hasDerivAt_planeRotation_coordinate (i j : Fin 4) (hij : i ≠ j)
    (q : FourSpace) (k : Fin 4) (t : ℝ) :
    HasDerivAt (fun s => planeRotation i j hij s q k)
      (planeCoordinateDerivative i j t q k) t := by
  simp only [planeRotation_apply, planeCoordinateDerivative]
  by_cases hki : k = i
  · simp only [ite_eq_left hki]
    exact ((Real.hasDerivAt_cos t).mul_const (q i)).add
      ((Real.hasDerivAt_sin t).mul_const (q j))
  · by_cases hkj : k = j
    · simp only [ite_eq_right hki, ite_eq_left hkj]
      exact ((Real.hasDerivAt_cos t).mul_const (q j)).sub
        ((Real.hasDerivAt_sin t).mul_const (q i))
    · simp only [ite_eq_right hki, ite_eq_right hkj]
      exact hasDerivAt_const t (q k)

theorem continuous_planeRotation_coordinate (i j : Fin 4) (hij : i ≠ j) (k : Fin 4) :
    Continuous (fun p : ℝ × Directions => planeRotation i j hij p.1 p.2.val k) := by
  simp only [planeRotation_apply]
  by_cases hki : k = i
  · simp only [ite_eq_left hki]
    fun_prop
  · by_cases hkj : k = j
    · simp only [ite_eq_right hki, ite_eq_left hkj]
      fun_prop
    · simp only [ite_eq_right hki, ite_eq_right hkj]
      fun_prop

theorem continuous_planeCoordinateDerivative (i j k : Fin 4) :
    Continuous (fun p : ℝ × Directions => planeCoordinateDerivative i j p.1 p.2.val k) := by
  unfold planeCoordinateDerivative
  by_cases hki : k = i
  · simp only [ite_eq_left hki]
    fun_prop
  · by_cases hkj : k = j
    · simp only [ite_eq_right hki, ite_eq_left hkj]
      fun_prop
    · simp only [ite_eq_right hki, ite_eq_right hkj]
      fun_prop

theorem planeCoordinateDerivative_zero (i j : Fin 4) (hij : i ≠ j)
    (q : FourSpace) (k : Fin 4) :
    planeCoordinateDerivative i j 0 q k = delta k i * q j - delta k j * q i := by
  unfold planeCoordinateDerivative delta
  by_cases hki : k = i
  · subst k
    simp [hij]
  · by_cases hkj : k = j
    · subst k
      simp [hij.symm]
    · simp [hki, hkj]

end
end PositiveEinsteinFour.Angular

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_SphericalIntegralDerivative
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceSubtypeMatrixFinOfNatNatRealMemSubmonoidOrientedOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Differentiating a continuous family on the compact sphere commutes with
its normalized integral when the pointwise derivative is jointly continuous. -/

namespace PositiveEinsteinFour.Angular

open EinsteinFour MeasureTheory

noncomputable section

local instance sphericalIntegralNormedGroup : NormedAddCommGroup C(Directions, ℝ) :=
  ContinuousMap.instNormedAddCommGroup
local instance sphericalIntegralNormedSpace : NormedSpace ℝ C(Directions, ℝ) :=
  ContinuousMap.normedSpace

variable [IsProbabilityMeasure sphereMeasure]

def sphericalIntegralLinear : C(Directions, ℝ) →ₗ[ℝ] ℝ where
  toFun f := ∫ q, f q ∂sphereMeasure
  map_add' f g := by
    change (∫ q, f q + g q ∂sphereMeasure) = _
    exact integral_add (sphere_continuous_integrable f.continuous)
      (sphere_continuous_integrable g.continuous)
  map_smul' a f := by
    change (∫ q, a * f q ∂sphereMeasure) = a * ∫ q, f q ∂sphereMeasure
    exact integral_const_mul a _

def sphericalIntegralCLM : C(Directions, ℝ) →L[ℝ] ℝ :=
  sphericalIntegralLinear.mkContinuous 1 (fun f => by
    change ‖∫ q, f q ∂sphereMeasure‖ ≤ 1 * ‖f‖
    simpa using norm_integral_le_of_norm_le_const (μ := sphereMeasure)
      (Filter.Eventually.of_forall (fun q => f.norm_coe_le_norm q)))

theorem sphereIntegral_hasDerivAt {F G : ℝ → C(Directions, ℝ)}
    (hG : Continuous (fun p : ℝ × Directions => G p.1 p.2))
    (hpoint : ∀ t q, HasDerivAt (fun s => F s q) (G t q) t) (t : ℝ) :
    HasDerivAt (fun s => ∫ q, F s q ∂sphereMeasure)
      (∫ q, G t q ∂sphereMeasure) t := by
  exact sphericalIntegralCLM.hasFDerivAt.comp_hasDerivAt t
    (Averages.continuousField_hasDerivAt_of_joint hG hpoint t)

end
end PositiveEinsteinFour.Angular

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_SphericalMomentRecurrence
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceSubtypeMatrixFinOfNatNatRealMemSubmonoidOrientedOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The infinitesimal rotation identity for the degree-six spherical moment.
The five factors left after differentiation determine the recurrence. -/

namespace PositiveEinsteinFour.Angular

open EinsteinFour MeasureTheory

noncomputable section

def fiveProduct (a : Fin 5 → Fin 4) (q : FourSpace) : ℝ := ∏ r, q (a r)

def fiveOmit (a : Fin 5 → Fin 4) (q : FourSpace) (r : Fin 5) : ℝ :=
  ∏ s ∈ Finset.univ.erase r, q (a s)

def sphereRotationGenerator (i j : Fin 4) (a : Fin 5 → Fin 4) (q : FourSpace) : ℝ :=
  (delta j i * q j - q i) * fiveProduct a q + q j *
    ∑ r, (delta (a r) i * q j - delta (a r) j * q i) * fiveOmit a q r

theorem fiveProduct_eq_mul_omit (a : Fin 5 → Fin 4) (q : FourSpace) (r : Fin 5) :
    q (a r) * fiveOmit a q r = fiveProduct a q := by
  simpa only [fiveProduct, fiveOmit, mul_comm] using
    Finset.prod_erase_mul Finset.univ (fun s => q (a s)) (Finset.mem_univ r)

theorem sum_sphereRotationGenerator (i : Fin 4) (a : Fin 5 → Fin 4)
    (q : FourSpace) (hq : ∑ j, q j ^ 2 = 1) :
    (∑ j, sphereRotationGenerator i j a q) =
      (∑ r, delta (a r) i * fiveOmit a q r) - 8 * q i * fiveProduct a q := by
  have hfirst : (∑ j, (delta j i * q j - q i) * fiveProduct a q) =
      -3 * q i * fiveProduct a q := by
    simp_rw [sub_mul, Finset.sum_sub_distrib, ← Finset.sum_mul]
    simp [delta]
    ring
  have hterm (r : Fin 5) :
      (∑ j, q j * ((delta (a r) i * q j - delta (a r) j * q i) * fiveOmit a q r)) =
      (delta (a r) i - q i * q (a r)) * fiveOmit a q r := by
    have he (j : Fin 4) :
        q j * ((delta (a r) i * q j - delta (a r) j * q i) * fiveOmit a q r) =
        (delta (a r) i * q j ^ 2 - q i * (delta (a r) j * q j)) * fiveOmit a q r := by
      ring
    simp_rw [he]
    rw [← Finset.sum_mul, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, hq]
    simp [delta]
  have hsecond :
      (∑ j, q j * ∑ r, (delta (a r) i * q j - delta (a r) j * q i) * fiveOmit a q r) =
      (∑ r, delta (a r) i * fiveOmit a q r) - 5 * q i * fiveProduct a q := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [hterm, sub_mul, Finset.sum_sub_distrib]
    have he (r : Fin 5) : q i * q (a r) * fiveOmit a q r = q i * fiveProduct a q := by
      rw [mul_assoc, fiveProduct_eq_mul_omit]
    simp_rw [he]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  simp only [sphereRotationGenerator, Finset.sum_add_distrib]
  rw [hfirst, hsecond]
  ring

variable [IsProbabilityMeasure sphereMeasure]

local instance sphericalRecurrenceNormedGroup_rfabd5a_1 : NormedAddCommGroup C(Directions, ℝ) :=
  ContinuousMap.instNormedAddCommGroup
local instance sphericalRecurrenceNormedSpace_rfabd5a_1 : NormedSpace ℝ C(Directions, ℝ) :=
  ContinuousMap.normedSpace
theorem integral_sphereRotationGenerator_zero (i j : Fin 4) (a : Fin 5 → Fin 4) :
    (∫ q : Directions, sphereRotationGenerator i j a q.val ∂sphereMeasure) = 0 := by
  by_cases hij : i = j
  · subst j
    simp [sphereRotationGenerator, delta]
  let Z (k : Fin 4) (p : ℝ × Directions) := planeRotation i j hij p.1 p.2.val k
  let V (k : Fin 4) (p : ℝ × Directions) := planeCoordinateDerivative i j p.1 p.2.val k
  have hZ (k : Fin 4) : Continuous (Z k) := continuous_planeRotation_coordinate i j hij k
  have hV (k : Fin 4) : Continuous (V k) := continuous_planeCoordinateDerivative i j k
  have hP : Continuous (fun p : ℝ × Directions => ∏ r, Z (a r) p) :=
    continuous_finsetProd Finset.univ (fun r _ => hZ (a r))
  have hD : Continuous (fun p : ℝ × Directions =>
      ∑ r, (∏ s ∈ Finset.univ.erase r, Z (a s) p) * V (a r) p) :=
    continuous_finsetSum Finset.univ (fun r _ =>
      (continuous_finsetProd (Finset.univ.erase r) (fun s _ => hZ (a s))).mul (hV (a r)))
  have hF : Continuous (fun p : ℝ × Directions => Z j p * ∏ r, Z (a r) p) :=
    (hZ j).mul hP
  have hG : Continuous (fun p : ℝ × Directions =>
      V j p * (∏ r, Z (a r) p) + Z j p *
        ∑ r, (∏ s ∈ Finset.univ.erase r, Z (a s) p) * V (a r) p) :=
    ((hV j).mul hP).add ((hZ j).mul hD)
  let F (t : ℝ) : C(Directions, ℝ) :=
    ⟨fun q => Z j (t, q) * ∏ r, Z (a r) (t, q),
      hF.comp (continuous_const.prodMk continuous_id)⟩
  let G (t : ℝ) : C(Directions, ℝ) :=
    ⟨fun q => V j (t, q) * (∏ r, Z (a r) (t, q)) + Z j (t, q) *
        ∑ r, (∏ s ∈ Finset.univ.erase r, Z (a s) (t, q)) * V (a r) (t, q),
      hG.comp (continuous_const.prodMk continuous_id)⟩
  have hpoint (t : ℝ) (q : Directions) : HasDerivAt (fun s => F s q) (G t q) t := by
    have hd (k : Fin 4) : HasDerivAt (fun s => Z k (s, q)) (V k (t, q)) t :=
      hasDerivAt_planeRotation_coordinate i j hij q.val k t
    have hp := HasDerivAt.fun_finsetProd (u := Finset.univ) (fun r _ => hd (a r))
    change HasDerivAt (fun s => Z j (s, q) * ∏ r, Z (a r) (s, q))
      (V j (t, q) * (∏ r, Z (a r) (t, q)) + Z j (t, q) *
        ∑ r, (∏ s ∈ Finset.univ.erase r, Z (a s) (t, q)) * V (a r) (t, q)) t
    simpa only [smul_eq_mul, Pi.mul_apply] using! (hd j).mul hp
  have hi := sphereIntegral_hasDerivAt (F := F) (G := G) hG hpoint 0
  have hconst (t : ℝ) : (∫ q, F t q ∂sphereMeasure) =
      ∫ q : Directions, q.val j * fiveProduct a q.val ∂sphereMeasure := by
    have h := sphereIntegral_isometry (directionIsometry (planeRotation i j hij t))
      (fun q : Directions => q.val j * fiveProduct a q.val)
    change (∫ q : Directions, (planeRotation i j hij t q.val) j *
      (∏ r, (planeRotation i j hij t q.val) (a r)) ∂sphereMeasure) = _ at h
    exact h
  have hfun : (fun t => ∫ q, F t q ∂sphereMeasure) =
      fun _ : ℝ => ∫ q : Directions, q.val j * fiveProduct a q.val ∂sphereMeasure :=
    funext hconst
  rw [hfun] at hi
  have hz : (∫ q, G 0 q ∂sphereMeasure) = 0 :=
    hi.unique (hasDerivAt_const 0 _)
  have hg0 (q : Directions) : G 0 q = sphereRotationGenerator i j a q.val := by
    have hz0 (k : Fin 4) : Z k (0, q) = q.val k :=
      congrArg (fun v : FourSpace => v k) (planeRotation_zero i j hij q.val)
    have hv0 (k : Fin 4) : V k (0, q) =
        delta k i * q.val j - delta k j * q.val i :=
      planeCoordinateDerivative_zero i j hij q.val k
    change V j (0, q) * (∏ r, Z (a r) (0, q)) + Z j (0, q) *
      (∑ r, (∏ s ∈ Finset.univ.erase r, Z (a s) (0, q)) * V (a r) (0, q)) = _
    simp_rw [hz0, hv0]
    simp only [show delta j j = 1 by simp [delta], one_mul]
    unfold sphereRotationGenerator fiveProduct fiveOmit
    congr 1
    congr 1
    apply Finset.sum_congr rfl
    intro r _
    ring
  calc
    _ = ∫ q, G 0 q ∂sphereMeasure :=
      integral_congr_ae (Filter.Eventually.of_forall (fun q => (hg0 q).symm))
    _ = 0 := hz

theorem spherical_sixth_recurrence (i : Fin 4) (a : Fin 5 → Fin 4) :
    8 * (∫ q : Directions, q.val i * fiveProduct a q.val ∂sphereMeasure) =
      ∑ r, delta (a r) i * (∫ q : Directions, fiveOmit a q.val r ∂sphereMeasure) := by
  have hM : Integrable (fun q : Directions => q.val i * fiveProduct a q.val) sphereMeasure :=
    sphere_continuous_integrable (by unfold fiveProduct; fun_prop)
  have hO (r : Fin 5) : Integrable (fun q : Directions => delta (a r) i *
      fiveOmit a q.val r) sphereMeasure :=
    sphere_continuous_integrable (by unfold fiveOmit; fun_prop)
  have hR (j : Fin 4) : Integrable (fun q : Directions =>
      sphereRotationGenerator i j a q.val) sphereMeasure :=
    sphere_continuous_integrable (by unfold sphereRotationGenerator fiveProduct fiveOmit; fun_prop)
  have hz : (∫ q : Directions, ∑ j, sphereRotationGenerator i j a q.val ∂sphereMeasure) = 0 := by
    rw [integral_finsetSum _ (fun j _ => hR j)]
    simp only [integral_sphereRotationGenerator_zero, Finset.sum_const_zero]
  have he : (fun q : Directions => ∑ j, sphereRotationGenerator i j a q.val) =
      fun q => (∑ r, delta (a r) i * fiveOmit a q.val r) -
        8 * (q.val i * fiveProduct a q.val) := by
    funext q
    simpa only [mul_assoc] using sum_sphereRotationGenerator i a q.val (sum_coordinate_sq q)
  rw [he, integral_sub (integrable_finsetSum _ (fun r _ => hO r)) (hM.const_mul 8),
    integral_finsetSum _ (fun r _ => hO r), integral_const_mul] at hz
  simp_rw [integral_const_mul] at hz
  linarith

omit [IsProbabilityMeasure sphereMeasure] in
theorem fiveOmit_eq_succAbove (a : Fin 5 → Fin 4) (q : FourSpace) (r : Fin 5) :
    fiveOmit a q r = ∏ s : Fin 4, q (a (r.succAbove s)) := by
  have he : (Finset.univ : Finset (Fin 5)).erase r =
      Finset.univ.map (Fin.succAboveEmb r) := by
    ext k
    simp [Finset.mem_map]
  unfold fiveOmit
  rw [he, Finset.prod_map]
  rfl

end
end PositiveEinsteinFour.Angular

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_SphericalSixthMoment
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceSubtypeMatrixFinOfNatNatRealMemSubmonoidOrientedOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The degree-six formula follows from the infinitesimal rotation recurrence
and the already proved quartic formula. Only positivity and finiteness of the
unnormalized Hausdorff mass remain in the spherical input. -/

namespace PositiveEinsteinFour.Angular

open EinsteinFour MeasureTheory

noncomputable section

theorem fiveOmit_vector (j k l m n : Fin 4) (q : FourSpace) (r : Fin 5) :
    fiveOmit ![j, k, l, m, n] q r =
      ![q k * q l * q m * q n, q j * q l * q m * q n,
        q j * q k * q m * q n, q j * q k * q l * q n,
        q j * q k * q l * q m] r := by
  rw [fiveOmit_eq_succAbove]
  fin_cases r <;> simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  all_goals norm_num [Fin.succAbove, Fin.lt_def, Fin.castSucc, Fin.succ]
  all_goals try simp [Fin.castAdd, Fin.castLE, Matrix.cons_val]
  all_goals ring

theorem delta_comm (i j : Fin 4) : delta i j = delta j i := by
  simp only [delta, eq_comm]

variable [IsProbabilityMeasure sphereMeasure]

theorem actual_spherical_sixth (i j k l m n : Fin 4) :
    (∫ q : Directions, q.val i * q.val j * q.val k * q.val l * q.val m * q.val n
      ∂sphereMeasure) = momentSix i j k l m n := by
  have h := spherical_sixth_recurrence i ![j, k, l, m, n]
  have hp (q : Directions) : q.val i * fiveProduct ![j, k, l, m, n] q.val =
      q.val i * q.val j * q.val k * q.val l * q.val m * q.val n := by
    simp only [fiveProduct, Fin.prod_univ_succ, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Fin.prod_univ_zero, mul_one]
    ring
  simp_rw [hp, fiveOmit_vector] at h
  simp only [Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.sum_univ_zero, add_zero, actual_spherical_fourth] at h
  simp_rw [delta_comm] at h
  unfold momentSix
  linarith

theorem follandMoments_of_probability : FollandMoments where
  probability := inferInstance
  second := actual_spherical_second
  fourth := actual_spherical_fourth
  sixth := actual_spherical_sixth

end
end PositiveEinsteinFour.Angular

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ActualSphericalMoments
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The degree-two, four and six Folland formulas for the actual normalized
Hausdorff measure. Both the moments and its probability normalization are
proved here, so the geometric application need not assume them. -/

namespace PositiveEinsteinFour.Angular

theorem actual_follandMoments : FollandMoments := by
  let := actual_sphereMeasure_probability
  exact follandMoments_of_probability

end PositiveEinsteinFour.Angular

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_AngularQuadratic
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Angular averages of two quadratic forms, from the precise fourth
spherical moment. This is used for the two Weyl blocks in the normal Jacobi
matrix; no curvature average is an input. -/

namespace PositiveEinsteinFour.Angular

open MeasureTheory Matrix

noncomputable section

def quadratic (C : Mat4) (q : Directions) : ℝ :=
  ∑ i, ∑ j, C i j * (q.val i * q.val j)

end

end PositiveEinsteinFour.Angular

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_AngularRotation
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual change of normal bases `I_s q` and `J_t q`. Its spherical
orthogonality is a consequence of the fourth monomial moment. -/

namespace PositiveEinsteinFour.Angular

open Matrix

noncomputable section

def mixingCoefficient (r s : Fin 3) : Mat4 :=
  (TraceHessian.quaternionMatrix r)ᵀ * oppositeMatrix s

def coefficientTable (r s : Fin 3) : Mat4 :=
  ![![![![-1, 0, 0, 0], ![0, -1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]], ![![0, 0, 0, 1], ![0, 0, -1, 0], ![0, -1, 0, 0], ![1, 0, 0, 0]], ![![0, 0, -1, 0], ![0, 0, 0, -1], ![-1, 0, 0, 0], ![0, -1, 0, 0]]], ![![![0, 0, 0, -1], ![0, 0, -1, 0], ![0, -1, 0, 0], ![-1, 0, 0, 0]], ![![-1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, -1, 0], ![0, 0, 0, 1]], ![![0, 1, 0, 0], ![1, 0, 0, 0], ![0, 0, 0, -1], ![0, 0, -1, 0]]], ![![![0, 0, 1, 0], ![0, 0, 0, -1], ![1, 0, 0, 0], ![0, -1, 0, 0]], ![![0, -1, 0, 0], ![-1, 0, 0, 0], ![0, 0, 0, -1], ![0, 0, -1, 0]], ![![-1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, -1]]]] r s

def mixing (r s : Fin 3) (q : Directions) : ℝ :=
  quadratic (mixingCoefficient r s) q

theorem direction_sum_sq (q : Directions) : (∑ i, q.val i ^ 2) = 1 := by
  have h := congrArg (fun x : ℝ => x ^ 2) q.property
  simpa only [EuclideanSpace.real_norm_sq_eq, one_pow] using h

end

end PositiveEinsteinFour.Angular

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_AngularNormal
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The pointwise and averaged normal Jacobi curvature form. -/

namespace PositiveEinsteinFour.Angular

open Matrix MeasureTheory

noncomputable section

def pairing (T U : Mat3) : ℝ := ∑ i, ∑ j, T i j * U i j

end

end PositiveEinsteinFour.Angular

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_AngularGradient
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The directional-derivative part of the angular average. -/

namespace PositiveEinsteinFour.Angular

open Matrix MeasureTheory

noncomputable section

def directional (Z : Gradient) (q : Directions) : Mat3 :=
  ∑ i, q.val i • Z i

end

end PositiveEinsteinFour.Angular

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_AngularSixth
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sixth spherical moments for the directional derivative of normal curvature.
All moments are the explicit Folland specialization from `SphericalMoments`. -/

namespace PositiveEinsteinFour.Angular

open Matrix MeasureTheory

noncomputable section

theorem delta_symm (a b : Fin 4) : delta a b = delta b a := by
  simp [delta, eq_comm]

end

end PositiveEinsteinFour.Angular

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_AngularDerivativeMoments
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The opposite Weyl blocks have zero mixed directional energy. -/

namespace PositiveEinsteinFour.Angular

open Matrix MeasureTheory

noncomputable section

/-- The Frobenius pairing, packaged only to expand finite directional sums. -/
def angularPairingLinear : Mat3 →ₗ[ℝ] Mat3 →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ pairing
    (by intro T V U; simp only [pairing, Matrix.add_apply, add_mul,
          Finset.sum_add_distrib])
    (by intro c T U; simp only [pairing, Matrix.smul_apply, smul_eq_mul,
          mul_assoc, ← Finset.mul_sum])
    (by intro T U V; simp only [pairing, Matrix.add_apply, mul_add,
          Finset.sum_add_distrib])
    (by intro c T U
        have hp (i j : Fin 3) : T i j * (c * U i j) = c * (T i j * U i j) := by ring
        simp only [pairing, Matrix.smul_apply, smul_eq_mul]
        simp_rw [hp, ← Finset.mul_sum])

end

end PositiveEinsteinFour.Angular

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylEstimates01
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The scalar trace of each quaternion curvature block is fixed by the
Einstein contraction and the first Bianchi identity. -/

namespace PositiveEinsteinFour.AlgebraicCurvature

open Matrix TraceHessian Angular
open PositiveEinsteinFour.Geometry (curvatureBlock curvatureBlock_symmetric)
open scoped BigOperators

noncomputable section

theorem weyl_blocks_traceFree (R : CurvatureArray) (hf : FirstSkew R)
    (hl : LastSkew R) (hb : FirstBianchi R)
    (hr : ∀ j k, ricci R j k = if j = k then 3 else 0) :
    traceFree (curvatureBlock (fun p q => R p.1 p.2 q.2 q.1) quaternionMatrix - 1) ∧
      traceFree (curvatureBlock (fun p q => R p.1 p.2 q.2 q.1) oppositeMatrix - 1) := by
  let K := matrixOf R
  have hn : tensorOf K = R := tensorOf_matrixOf hf hl
  have hs : Kᵀ = K := matrixOf_symmetric (pairSymmetric_of_bianchi hf hl hb)
  have hK : EinsteinRelations K := einsteinRelations_of_ricci K hs
    (by intro j k; rw [hn]; exact hr j k)
  have hs50 : K 5 0 = K 0 5 := congrArg (fun A => A 0 5) hs
  have hs41 : K 4 1 = K 1 4 := congrArg (fun A => A 1 4) hs
  have hs32 : K 3 2 = K 2 3 := congrArg (fun A => A 2 3) hs
  have hzero := hr 0 0
  have hcycle := hb 0 1 2 3
  rw [← hn] at hzero hcycle
  norm_num [ricci, tensorOf, pairIndex, pairSign, Fin.sum_univ_succ] at hzero
  simp [tensorOf, pairIndex, pairSign, hs32] at hcycle
  have hcplus : curvatureBlock (fun p q => R p.1 p.2 q.2 q.1) quaternionMatrix =
      plusFormula K := by
    have hh := curvatureBlock_tensorOf K quaternionMatrix quaternionMatrix_transpose
    rw [plusFormula_eq] at hh
    simpa only [hn] using hh
  have hcminus : curvatureBlock (fun p q => R p.1 p.2 q.2 q.1) oppositeMatrix =
      minusFormula K := by
    have hh := curvatureBlock_tensorOf K oppositeMatrix QuaternionFrame.oppositeMatrix_transpose
    rw [minusFormula_eq] at hh
    simpa only [hn] using hh
  rw [hcplus, hcminus]
  constructor
  · change (∑ i : Fin 3, (plusFormula K i i - (1 : Mat3) i i)) = 0
    simp [Matrix.one_apply, Fin.sum_univ_three,
      plusFormula, hK.d0, hK.d1, hK.d2, hs50, hs41, hs32]
    linarith only [hzero, hcycle]
  · change (∑ i : Fin 3, (minusFormula K i i - (1 : Mat3) i i)) = 0
    simp [Matrix.one_apply, Fin.sum_univ_three,
      minusFormula, hK.d0, hK.d1, hK.d2, hs50, hs41, hs32]
    linarith only [hzero, hcycle]

end
end PositiveEinsteinFour.AlgebraicCurvature
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_CurvatureTensors02
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The zero-Ricci block reconstruction needed for the actual curvature derivative. -/

namespace PositiveEinsteinFour.AlgebraicCurvature

open Matrix TraceHessian Angular
open PositiveEinsteinFour.Geometry (curvatureBlock)
open scoped BigOperators

noncomputable section


theorem ricci_zero_decomposition (R : CurvatureArray) (hf : FirstSkew R)
    (hl : LastSkew R) (hp : PairSymmetric R) (hr : ∀ j k, ricci R j k = 0) :
    R = blockTensor (curvatureBlock (fun p q => R p.1 p.2 q.2 q.1) quaternionMatrix)
        quaternionMatrix +
      blockTensor (curvatureBlock (fun p q => R p.1 p.2 q.2 q.1) oppositeMatrix)
        oppositeMatrix := by
  let K := matrixOf R
  have hn : tensorOf K = R := tensorOf_matrixOf hf hl
  have hk : EinsteinRelations K := relations_of_ricci_zero K (matrixOf_symmetric hp)
    (by intro j k; rw [hn]; exact hr j k)
  have hcplus : curvatureBlock (fun p q => R p.1 p.2 q.2 q.1) quaternionMatrix =
      plusFormula K := by
    have hh := curvatureBlock_tensorOf K quaternionMatrix quaternionMatrix_transpose
    rw [plusFormula_eq] at hh
    simpa only [hn] using hh
  have hcminus : curvatureBlock (fun p q => R p.1 p.2 q.2 q.1) oppositeMatrix =
      minusFormula K := by
    have hh := curvatureBlock_tensorOf K oppositeMatrix QuaternionFrame.oppositeMatrix_transpose
    rw [minusFormula_eq] at hh
    simpa only [hn] using hh
  rw [hcplus, hcminus]
  exact hn.symm.trans (tensorOf_eq_blocksTensor K hk)

end
end PositiveEinsteinFour.AlgebraicCurvature
end


end OAI
end


