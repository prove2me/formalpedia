-- Prove2me | Definitions.Def_OAIQ091C026
-- name    : OAIQ091C026
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T18:11:18.503637+00:00
-- url     : https://prove2.me/theorems/f5887dac-9c08-491a-b3bc-5f140372485c
-- title:
--   Definitions bundle OAIQ091C026 of the split of OpenAI, Positively curved Einstein four-manifolds (result family 348)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PositiveEinsteinFour.classification`, `OAI.PositiveEinsteinFour.classificationOn` and `OAI.PositiveEinsteinFour.orientedClassification`, carved from OpenAI's openai/math development (OpenAI, *Positively curved Einstein four-manifolds (result family 348)*, OpenAI Math Release, September 23, 2026, result family 348, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 38 declarations of OpenAI's Lean: 4 definitions and 34 theorems. The definitions and types are `OAI.PositiveEinsteinFour.Geometry.actualJacobiRealizationData`, `OAI.PositiveEinsteinFour.Geometry.actualMinimizingFramePairs`, `OAI.PositiveEinsteinFour.Geometry.exponentialFamilyCoordinates`, `OAI.PositiveEinsteinFour.Geometry.framePolarDomain`.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: [`EinsteinFour_GeodesicGeometry04`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/GeodesicGeometry04.lean), [`EinsteinFour_GeodesicGeometry05`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/GeodesicGeometry05.lean), [`EinsteinFour_GeodesicGeometry12`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/GeodesicGeometry12.lean), [`EinsteinFour_HeatKernels10`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/HeatKernels10.lean), [`EinsteinFour_HodgeTheory11`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/HodgeTheory11.lean), [`EinsteinFour_ScalarRegularity06`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/ScalarRegularity06.lean).
--
--   **Imports.** It imports the published bundle `Def_EinsteinFour`; the bundles `OAIQ091C019`, `OAIQ091C039`, `OAIQ091C021` and `OAIQ091C022` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ091C029`, `OAIQ091C047`, `OAIQ091C048`, `OAIQ091C050` and `OAIQ091C053`.
-- source:
--   OpenAI, Positively curved Einstein four-manifolds (result family 348), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 348; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Positively-curved-Einstein-four-manifolds-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_EinsteinFour
import Definitions.Def_OAIQ091C019
import Definitions.Def_OAIQ091C039
import Definitions.Def_OAIQ091C021
import Definitions.Def_OAIQ091C022

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeodesicGeometry04
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p2
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Identification and integration of the actual Jacobi determinant with
its first-conjugate-point truncation. The family is the single global
solution attached to each actual frame, independent of endpoint time. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Jacobi MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem actualRegularJacobi_truncatedDensity_eq (g : SmoothMetric M) (hRic : RicciThree g)
    (e : FrameBundle g) (t : ℝ) :
    (actualRegularJacobi g hRic e t).truncatedDensity =
      truncatedJacobiDensity (actualJacobiMatrix g hRic) (t, e) := by
  classical
  simp only [RegularJacobi.truncatedDensity, actualRegularJacobi_J,
    truncatedJacobiDensity, preconjugateSet, actualJacobiMatrix, Set.mem_ofPred_eq]
  rfl

theorem actualRegularJacobi_truncatedDensity_scaled (g : SmoothMetric M)
    (hRic : RicciThree g) (e : FrameBundle g) (u : ℝ) :
    (actualRegularJacobi g hRic e (Real.pi * u)).truncatedDensity =
      truncatedJacobiDensity (fun p => actualJacobiMatrix g hRic (Real.pi * p.1, p.2))
        (u, e) := by
  rw [truncatedJacobiDensity_rescale _ Real.pi Real.pi_pos]
  exact actualRegularJacobi_truncatedDensity_eq g hRic e _

variable [MeasurableSpace M] [BorelSpace M] [Nonempty M]

theorem actualJacobiDensity_integrable_of_continuous (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g)
    (hJ : Continuous (actualJacobiMatrix g hRic)) (t : ℝ) :
    Integrable (fun e => (actualRegularJacobi g hRic e t).truncatedDensity)
      (canonicalFrameMeasure g o) := by
  let : CompactSpace (FrameBundle g) := actual_compactFrameBundle g
  have h := integrable_truncatedJacobiDensity_slice (canonicalFrameMeasure g o)
    (actualJacobiMatrix g hRic) hJ t
  apply h.congr
  exact Filter.Eventually.of_forall (fun e =>
    (actualRegularJacobi_truncatedDensity_eq g hRic e t).symm)

theorem actualJacobiDensity_intervalIntegrable_of_continuous (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g)
    (hJ : Continuous (actualJacobiMatrix g hRic)) (a b : ℝ) (hab : a ≤ b) :
    IntervalIntegrable
      (fun u => ∫ e, (actualRegularJacobi g hRic e (Real.pi * u)).truncatedDensity
        ∂canonicalFrameMeasure g o) volume a b := by
  let : CompactSpace (FrameBundle g) := actual_compactFrameBundle g
  have hJ' : Continuous
      (fun p : ℝ × FrameBundle g => actualJacobiMatrix g hRic (Real.pi * p.1, p.2)) :=
    hJ.comp ((continuous_const.mul continuous_fst).prodMk continuous_snd)
  have h := intervalIntegrable_truncatedJacobiDensity_average
    (canonicalFrameMeasure g o) _ hJ' a b hab
  have heq : (fun u => ∫ e, truncatedJacobiDensity
      (fun p => actualJacobiMatrix g hRic (Real.pi * p.1, p.2)) (u, e)
        ∂canonicalFrameMeasure g o) =
      (fun u => ∫ e, (actualRegularJacobi g hRic e (Real.pi * u)).truncatedDensity
        ∂canonicalFrameMeasure g o) := by
    funext u
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun e =>
      (actualRegularJacobi_truncatedDensity_scaled g hRic e u).symm)
  rwa [heq] at h

theorem actualJacobiDensity_integrable (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (t : ℝ) :
    Integrable (fun e => (actualRegularJacobi g hRic e t).truncatedDensity)
      (canonicalFrameMeasure g o) :=
  actualJacobiDensity_integrable_of_continuous g o hRic
    (actualJacobiJ_joint_continuous g hRic) t

theorem actualJacobiDensity_intervalIntegrable (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (a b : ℝ) (hab : a ≤ b) :
    IntervalIntegrable
      (fun u => ∫ e, (actualRegularJacobi g hRic e (Real.pi * u)).truncatedDensity
        ∂canonicalFrameMeasure g o) volume a b :=
  actualJacobiDensity_intervalIntegrable_of_continuous g o hRic
    (actualJacobiJ_joint_continuous g hRic) a b hab

end
end PositiveEinsteinFour.Geometry
end


section

/-! The polar-volume inequality for the metric and its Jacobi fields. See
Petersen, Riemannian Geometry, §§5.7, 6.3 and 7.1. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]

def actualJacobiRealizationData (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (hpolar : ActualJacobiPolarInput g o hRic) :
    JacobiRealizationData (canonicalParallelMetricData g o hRic).toMetricGreenData where
  jacobi u e := actualRegularJacobi g hRic e (Real.pi * u)
  curvature u e r := by
    rw [actualRegularJacobi_R]
    rfl
  densityIntegrable u _ _ := actualJacobiDensity_integrable g o hRic (Real.pi * u)
  firstIntegral := actualJacobiDensity_intervalIntegrable g o hRic 0 (5 / 8) (by norm_num)
  secondIntegral := actualJacobiDensity_intervalIntegrable g o hRic (5 / 8) 1 (by norm_num)
  polar := hpolar

end
end PositiveEinsteinFour.Geometry
end


section

/-! Before the first conjugate point the Jacobi determinant is positive.
The proof removes the initial zero by `dslope`, then uses continuity and
invertibility on the whole closed interval. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Jacobi
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem actualJacobi_abs_det_eq_truncatedDensity (g : SmoothMetric M)
    (hRic : RicciThree g) (e : FrameBundle g) (t : ℝ) (ht : 0 < t)
    (hpre : ∀ s, 0 < s → s ≤ t → IsUnit ((actualJacobiSolution g hRic e).J s)) :
    |((actualJacobiSolution g hRic e).J t).det| =
      (actualRegularJacobi g hRic e t).truncatedDensity := by
  classical
  have hp : ∀ s, 0 < s → s ≤ t → IsUnit ((actualRegularJacobi g hRic e t).J s) := by
    simpa only [actualRegularJacobi_J] using hpre
  rw [RegularJacobi.truncatedDensity, ite_eq_left hp, actualRegularJacobi_J]
  exact abs_of_pos (actualJacobi_det_pos_of_preconjugate g hRic e t ht hpre)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The first positive singular time of the actual Jacobi matrix is attained.
Normalizing by time removes the initial zero; compactness then gives a
positive first zero, and the trace-three comparison bounds it by π. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Jacobi Matrix Set
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.L2Operator

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem actualJacobi_isUnit_before_firstConjugate (g : SmoothMetric M)
    (hRic : RicciThree g) (e : FrameBundle g) (s : ℝ)
    (hs : 0 < s) (hsc : s < actualFirstConjugateTime g hRic e) :
    IsUnit ((actualJacobiSolution g hRic e).J s) :=
  (Classical.choose_spec (exists_actualFirstConjugateTime g hRic e)).2.2.2 s hs hsc

theorem actualJacobi_preconjugate_iff_lt (g : SmoothMetric M) (hRic : RicciThree g)
    (e : FrameBundle g) (t : ℝ) :
    (∀ s, 0 < s → s ≤ t → IsUnit ((actualJacobiSolution g hRic e).J s)) ↔
      t < actualFirstConjugateTime g hRic e := by
  constructor
  · intro hp
    by_contra hnot
    exact actualFirstConjugateTime_singular g hRic e
      (hp _ (actualFirstConjugateTime_pos g hRic e) (le_of_not_gt hnot))
  · intro ht s hs hst
    exact actualJacobi_isUnit_before_firstConjugate g hRic e s hs (hst.trans_lt ht)

end
end PositiveEinsteinFour.Geometry
end


section

/-! A radial determinant cutoff at or before the first conjugate point is
bounded by the actual truncated Jacobi density.  The endpoint contributes
zero, and the first conjugate time bounds the support by `[0, π]`. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Jacobi Matrix MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem actualJacobi_det_firstConjugate_eq_zero (g : SmoothMetric M)
    (hRic : RicciThree g) (e : FrameBundle g) :
    ((actualJacobiSolution g hRic e).J (actualFirstConjugateTime g hRic e)).det = 0 := by
  by_contra hdet
  apply actualFirstConjugateTime_singular g hRic e
  exact (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)

theorem actualJacobi_cutoff_le_truncatedDensity (g : SmoothMetric M)
    (hRic : RicciThree g) (e : FrameBundle g) (b r : ℝ)
    (hb : b ≤ actualFirstConjugateTime g hRic e) (hr : 0 < r) :
    (if r ≤ b then ENNReal.ofReal |((actualJacobiSolution g hRic e).J r).det| else 0) ≤
      ENNReal.ofReal (actualRegularJacobi g hRic e r).truncatedDensity := by
  classical
  by_cases hrb : r ≤ b
  · rw [ite_eq_left hrb]
    rcases lt_or_eq_of_le (hrb.trans hb) with hrc | hrc
    · rw [actualJacobi_abs_det_eq_truncatedDensity g hRic e r hr
        ((actualJacobi_preconjugate_iff_lt g hRic e r).mpr hrc)]
    · subst r
      rw [actualJacobi_det_firstConjugate_eq_zero, abs_zero, ENNReal.ofReal_zero]
      exact zero_le
  · rw [ite_eq_right hrb]
    exact zero_le

theorem actualJacobi_cutoff_le_truncatedIndicator (g : SmoothMetric M)
    (hRic : RicciThree g) (e : FrameBundle g) (b r : ℝ)
    (hb : b ≤ actualFirstConjugateTime g hRic e) (hr : 0 < r) :
    (if r ≤ b then ENNReal.ofReal |((actualJacobiSolution g hRic e).J r).det| else 0) ≤
      (Icc (0 : ℝ) Real.pi).indicator
        (fun s => ENNReal.ofReal (actualRegularJacobi g hRic e s).truncatedDensity) r := by
  classical
  by_cases hrπ : r ≤ Real.pi
  · rw [Set.indicator_of_mem (show r ∈ Icc (0 : ℝ) Real.pi from ⟨hr.le, hrπ⟩)]
    exact actualJacobi_cutoff_le_truncatedDensity g hRic e b r hb hr
  · have hrb : ¬ r ≤ b := fun h => hrπ
      ((h.trans hb).trans (actualFirstConjugateTime_le_pi g hRic e))
    rw [ite_eq_right hrb]
    exact zero_le

theorem actualJacobi_cutoff_lintegral_le (g : SmoothMetric M)
    (hRic : RicciThree g) (e : FrameBundle g) (b : ℝ)
    (hb : b ≤ actualFirstConjugateTime g hRic e) :
    (∫⁻ r : Ioi (0 : ℝ),
      (if r.val ≤ b then ENNReal.ofReal |((actualJacobiSolution g hRic e).J r.val).det|
        else 0) ∂((volume : Measure ℝ).comap Subtype.val)) ≤
      ∫⁻ r in Icc (0 : ℝ) Real.pi,
        ENNReal.ofReal (actualRegularJacobi g hRic e r).truncatedDensity := by
  classical
  let f : ℝ → ℝ≥0∞ := fun r =>
    if r ≤ b then ENNReal.ofReal |((actualJacobiSolution g hRic e).J r).det| else 0
  let h : ℝ → ℝ≥0∞ := fun r =>
    ENNReal.ofReal (actualRegularJacobi g hRic e r).truncatedDensity
  change (∫⁻ r : Ioi (0 : ℝ), f r.val ∂((volume : Measure ℝ).comap Subtype.val)) ≤ _
  rw [lintegral_subtype_comap measurableSet_Ioi f]
  calc
    (∫⁻ r in Ioi (0 : ℝ), f r) ≤
        ∫⁻ r in Ioi (0 : ℝ), (Icc (0 : ℝ) Real.pi).indicator h r := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      exact actualJacobi_cutoff_le_truncatedIndicator g hRic e b r hb hr
    _ ≤ ∫⁻ r, (Icc (0 : ℝ) Real.pi).indicator h r :=
      lintegral_mono' Measure.restrict_le_self le_rfl
    _ = ∫⁻ r in Icc (0 : ℝ) Real.pi, h r := lintegral_indicator measurableSet_Icc h

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual exponential endpoint is jointly C1 in a nonzero normal
vector and its initial coordinate frame. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Matrix Set Filter
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

variable [T2Space M] [CompactSpace M]

def exponentialFamilyCoordinates (g : SmoothMetric M) (o : FrameOrientation g)
    (c d : M) (z : HeatRadialFrameSpace) : FourSpace :=
  (radialCoordinateFlow g o c d 1 (heatRadialCotangentState g c z.1 z.2)).1

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual exponential is a local coordinate chart along every radial
geodesic strictly before its first conjugate point. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem frameExponential_preconjugate_isUnit (g : SmoothMetric M)
    (hRic : RicciThree g) (d : M) (e : FrameBundle g) (t : ℝ) (ht : 0 < t)
    (htc : t < actualFirstConjugateTime g hRic e)
    (hd : (parallelFrameFlowMap g 0 t e).base ∈ (chartAt FourSpace d).source) :
    IsUnit (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ)
      (frameChartMatrix g d (parallelFrameFlowMap g 0 t e) *
        jacobiBlockMatrix 1 (t⁻¹ • (actualJacobiSolution g hRic e).J t))) := by
  have hE := Matrix.isUnit_det_of_left_inverse
    (frameChartMatrix_normalizes g d (parallelFrameFlowMap g 0 t e) hd)
  have hJ := (Matrix.isUnit_iff_isUnit_det _).mp
    (actualJacobi_isUnit_before_firstConjugate g hRic e t ht htc)
  have hB : IsUnit (jacobiBlockMatrix 1 (t⁻¹ • (actualJacobiSolution g hRic e).J t)) := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    rw [jacobiBlockMatrix_scaled_det]
    exact isUnit_iff_ne_zero.mpr (div_ne_zero hJ.ne_zero (pow_ne_zero _ ht.ne'))
  have hA := ((Matrix.isUnit_iff_isUnit_det _).mpr hE).mul hB
  exact hA.map (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ)).toMonoidHom

end
end PositiveEinsteinFour.Geometry
end


section

/-! Local inverses of the actual exponential are C1 wherever its actual
coordinate derivative is invertible. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Filter Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem frameExponential_local_inverse_contMDiffAt (g : SmoothMetric M)
    (o : FrameOrientation g) (e : FrameBundle g) (x : FourSpace)
    (C : OpenPartialHomeomorph FourSpace M) (hx : x ∈ C.source)
    (hC : EqOn C (frameExponential g o e) C.source)
    (hL : IsUnit (fderiv ℝ (fun v : FourSpace =>
      chartAt FourSpace (frameExponential g o e x) (frameExponential g o e v)) x)) :
    ContMDiffAt I4 I4 1 C.symm (frameExponential g o e x) :=
  frameExponential_chart_local_inverse_contMDiffAt g o e _ x C hx hC
    (mem_chart_source FourSpace _) hL

end
end PositiveEinsteinFour.Geometry
end


section

/-! The open polar parameter domain before the first conjugate point, and
actual local exponential charts in all of its directions. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

def framePolarDomain (g : SmoothMetric M) (hRic : RicciThree g)
    (e : FrameBundle g) : Set (Directions × ℝ) :=
  {p | 0 < p.2 ∧ p.2 < actualFirstConjugateTime g hRic
    (e.rotate (orientedToOrthogonal (directionOrientedMatrix p.1)))}

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeodesicGeometry05
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Measurability of the actual distance-minimizing radial domain. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set MeasureTheory
open scoped Manifold ContDiff _root_.Topology ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [PreconnectedSpace M]

theorem actualCutTime_upperSemicontinuous (g : SmoothMetric M) :
    UpperSemicontinuous (actualCutTime g) := by
  apply upperSemicontinuous_iff_isClosed_preimage.mpr
  intro t
  by_cases ht : 0 ≤ t
  · have heq : actualCutTime g ⁻¹' Ici t =
        {e : FrameBundle g | metricEDistance g e.base (frameGeodesic g 0 e t) =
          ENNReal.ofReal t} := by
      ext e
      change t ≤ actualCutTime g e ↔ _
      constructor
      · intro h
        have hm : t ∈ frameMinimizingTimes g e := by
          rw [frameMinimizingTimes_eq_Icc]
          exact ⟨ht, h⟩
        exact hm.2
      · intro h
        have hm : t ∈ frameMinimizingTimes g e := ⟨ht, h⟩
        rw [frameMinimizingTimes_eq_Icc] at hm
        exact hm.2
    rw [heq]
    have hpoint : Continuous (fun e : FrameBundle g => frameGeodesic g 0 e t) :=
      (continuous_frameBase g).comp (parallelFrameFlowMap_continuous_slice g 0 t)
    exact isClosed_eq ((metricEDistance_continuous g).comp
      ((continuous_frameBase g).prodMk hpoint)) continuous_const
  · have heq : actualCutTime g ⁻¹' Ici t = univ := by
      apply eq_univ_of_forall
      intro e
      exact (lt_of_not_ge ht).le.trans (actualCutTime_mem g e).1
    rw [heq]
    exact isClosed_univ

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual path metric is bounded by a uniform speed bound on an interval. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set MeasureTheory Bundle
open scoped Manifold ContDiff ENNReal
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [PreconnectedSpace M]

omit [T3Space M] [PreconnectedSpace M] in
theorem metricDistance_le_of_speed_bound (g : SmoothMetric M) {γ : ℝ → M}
    {a b C : ℝ} (hab : a ≤ b) (hC : 0 ≤ C)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I4 1 γ (Icc a b))
    (hs : ∀ t ∈ Icc a b, metricTangentNorm g (γ t)
      (mfderiv 𝓘(ℝ, ℝ) I4 γ t 1) ≤ C) :
    metricDistance g (γ a) (γ b) ≤ C * (b-a) := by
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  have hb : metricEDistance g (γ a) (γ b) ≤ ENNReal.ofReal (C*(b-a)) := by
    apply (Manifold.riemannianEDist_le_pathELength hγ rfl rfl hab).trans
    rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc]
    change (∫⁻ t in Icc a b, metricTangentENorm g (γ t)
      (mfderiv 𝓘(ℝ, ℝ) I4 γ t 1)) ≤ _
    calc
      _ ≤ ∫⁻ _t in Icc a b, ENNReal.ofReal C := by
        apply setLIntegral_mono' measurableSet_Icc
        intro t ht
        rw [metricTangentENorm_eq_ofReal]
        exact ENNReal.ofReal_le_ofReal (hs t ht)
      _ = ENNReal.ofReal (C*(b-a)) := by
        rw [lintegral_const,Measure.restrict_apply_univ,Real.volume_Icc,
          ENNReal.ofReal_mul hC]
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  simpa only [metricDistance,ENNReal.toReal_ofReal (mul_nonneg hC (sub_nonneg.mpr hab))] using ht

end
end PositiveEinsteinFour.Geometry
end


section

/-! Endpoint limits for a continuous curve whose interior has bounded speed. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Filter
open scoped Manifold ContDiff _root_.Topology
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [PreconnectedSpace M]

theorem metricDistance_le_of_interior_speed_bound (g : SmoothMetric M) {γ : ℝ → M}
    {a b C : ℝ} (hab : a ≤ b) (hC : 0 ≤ C) (hγ : Continuous γ)
    (hd : ∀ t ∈ Ioo a b, ContMDiffAt 𝓘(ℝ, ℝ) I4 1 γ t)
    (hs : ∀ t ∈ Ioo a b, metricTangentNorm g (γ t)
      (mfderiv 𝓘(ℝ, ℝ) I4 γ t 1) ≤ C) :
    metricDistance g (γ a) (γ b) ≤ C * (b-a) := by
  rcases hab.eq_or_lt with hab | hab
  · subst b
    rw [(metricDistance_eq_zero_iff g _ _).mpr rfl]
    simp
  have hmid (c d : ℝ) (hac : a < c) (hcd : c ≤ d) (hdb : d < b) :
      metricDistance g (γ c) (γ d) ≤ C*(d-c) := by
    apply metricDistance_le_of_speed_bound g hcd hC
    · intro t ht
      exact (hd t ⟨hac.trans_le ht.1,ht.2.trans_lt hdb⟩).contMDiffWithinAt
    · intro t ht
      exact hs t ⟨hac.trans_le ht.1,ht.2.trans_lt hdb⟩
  let c : ℝ → ℝ := fun t => a+t*(b-a)
  let d : ℝ → ℝ := fun t => b-t*(b-a)
  have hc : Tendsto c (𝓝[>] (0 : ℝ)) (𝓝 a) := by
    have h : Continuous c := continuous_const.add (continuous_id.mul continuous_const)
    simpa [c] using (h.tendsto 0).mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have hd' : Tendsto d (𝓝[>] (0 : ℝ)) (𝓝 b) := by
    have h : Continuous d := continuous_const.sub (continuous_id.mul continuous_const)
    simpa [d] using (h.tendsto 0).mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have hlim : Tendsto (fun t => metricDistance g (γ (c t)) (γ (d t)))
      (𝓝[>] (0 : ℝ)) (𝓝 (metricDistance g (γ a) (γ b))) :=
    (metricDistance_continuous g).continuousAt.tendsto.comp
      ((hγ.continuousAt.tendsto.comp hc).prodMk_nhds (hγ.continuousAt.tendsto.comp hd'))
  apply le_of_tendsto hlim
  have ht : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < (1/2 : ℝ) :=
    nhdsWithin_le_nhds (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1/2))
  filter_upwards [self_mem_nhdsWithin,ht] with t ht0 ht1
  have htpos : 0 < t := ht0
  have hac : a < c t := by dsimp [c]; nlinarith
  have hcd : c t ≤ d t := by dsimp [c,d]; nlinarith
  have hdb : d t < b := by dsimp [d]; nlinarith
  exact (hmid (c t) (d t) hac hcd hdb).trans
    (mul_le_mul_of_nonneg_left (by dsimp [c,d]; nlinarith) hC)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Finitely many exceptional parameters do not change a uniform path-speed bound. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [PreconnectedSpace M]

theorem metricDistance_le_of_speed_bound_off_finite (g : SmoothMetric M) (E : Finset ℝ)
    {γ : ℝ → M} {a b C : ℝ} (hab : a ≤ b) (hC : 0 ≤ C) (hγ : Continuous γ)
    (hd : ∀ t ∈ Ioo a b, t ∉ E → ContMDiffAt 𝓘(ℝ, ℝ) I4 1 γ t)
    (hs : ∀ t ∈ Ioo a b, t ∉ E → metricTangentNorm g (γ t)
      (mfderiv 𝓘(ℝ, ℝ) I4 γ t 1) ≤ C) :
    metricDistance g (γ a) (γ b) ≤ C * (b-a) := by
  classical
  induction E using Finset.induction_on generalizing a b with
  | empty =>
    exact metricDistance_le_of_interior_speed_bound g hab hC hγ
      (fun t ht => hd t ht (by simp)) (fun t ht => hs t ht (by simp))
  | @insert t E ht ih =>
    by_cases hti : t ∈ Ioo a b
    · have hleft : metricDistance g (γ a) (γ t) ≤ C*(t-a) := by
        apply ih hti.1.le
        · intro x hx hxE
          exact hd x ⟨hx.1,hx.2.trans hti.2⟩
            (by simp only [Finset.mem_insert,not_or]; exact ⟨ne_of_lt hx.2,hxE⟩)
        · intro x hx hxE
          exact hs x ⟨hx.1,hx.2.trans hti.2⟩
            (by simp only [Finset.mem_insert,not_or]; exact ⟨ne_of_lt hx.2,hxE⟩)
      have hright : metricDistance g (γ t) (γ b) ≤ C*(b-t) := by
        apply ih hti.2.le
        · intro x hx hxE
          exact hd x ⟨hti.1.trans hx.1,hx.2⟩
            (by simp only [Finset.mem_insert,not_or]; exact ⟨ne_of_gt hx.1,hxE⟩)
        · intro x hx hxE
          exact hs x ⟨hti.1.trans hx.1,hx.2⟩
            (by simp only [Finset.mem_insert,not_or]; exact ⟨ne_of_gt hx.1,hxE⟩)
      calc
        _ ≤ metricDistance g (γ a) (γ t) + metricDistance g (γ t) (γ b) :=
          metricDistance_triangle g _ _ _
        _ ≤ C*(t-a)+C*(b-t) := add_le_add hleft hright
        _ = _ := by ring
    · apply ih hab
      · intro x hx hxE
        exact hd x hx (by
          simp only [Finset.mem_insert,not_or]
          exact ⟨fun h => hti (h ▸ hx),hxE⟩)
      · intro x hx hxE
        exact hs x hx (by
          simp only [Finset.mem_insert,not_or]
          exact ⟨fun h => hti (h ▸ hx),hxE⟩)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual minimizing vectors over all positive frames form a compact
set. This gives uniform control of fibers near a unique minimizing vector. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Filter Metric
open scoped Manifold ContDiff _root_.Topology
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [PreconnectedSpace M]

def actualMinimizingFramePairs (g : SmoothMetric M) (o : FrameOrientation g) :
    Set (FrameBundle g × FourSpace) :=
  {p | p.1 ∈ o.positive ∧ p.2 ∈ actualMinimizingTangentDomain g o p.1}

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarRegularity06
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Averaging the actual polar bound over the canonical frame probability.
Right invariance under each oriented rotation removes the angular average;
Tonelli then puts the time and frame integrals in the manuscript's order. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular Jacobi MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instIsProbabilityMeasureDirectionsSphereMeasure_5
omit [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem measurable_actualJacobiDensity (g : SmoothMetric M) (hRic : RicciThree g) :
    Measurable (fun p : ℝ × FrameBundle g =>
      (actualRegularJacobi g hRic p.2 p.1).truncatedDensity) := by
  simpa only [actualRegularJacobi_truncatedDensity_eq] using
    measurable_truncatedJacobiDensity (actualJacobiMatrix g hRic)
      (actualJacobiJ_joint_continuous g hRic)

omit [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem measurable_actualRadialMass (g : SmoothMetric M) (hRic : RicciThree g) :
    Measurable (actualRadialMass g hRic) := by
  have h := ENNReal.measurable_ofReal.comp (measurable_actualJacobiDensity g hRic)
  exact (h.comp measurable_swap).lintegral_prod_right'

theorem canonical_actualRadialMass_integral (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) :
    (∫⁻ e, actualRadialMass g hRic e ∂canonicalFrameMeasure g o) =
      ∫⁻ r in Icc (0 : ℝ) Real.pi, ∫⁻ e,
        ENNReal.ofReal (actualRegularJacobi g hRic e r).truncatedDensity
        ∂canonicalFrameMeasure g o := by
  have h := ENNReal.measurable_ofReal.comp (measurable_actualJacobiDensity g hRic)
  exact lintegral_lintegral_swap (h.comp measurable_swap).aemeasurable

end
end PositiveEinsteinFour.Geometry
end


section

/-! Discharge of the published polar-volume input for the actual metric,
actual Jacobi solution and canonical frame measure. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular Jacobi MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]

theorem actualJacobi_average_integrableOn (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (a b : ℝ) :
    IntegrableOn (fun r => ∫ e, (actualRegularJacobi g hRic e r).truncatedDensity
      ∂canonicalFrameMeasure g o) (Icc a b) := by
  let : CompactSpace (FrameBundle g) := actual_compactFrameBundle g
  have h := (integrable_truncatedJacobiDensity_product (canonicalFrameMeasure g o)
    (actualJacobiMatrix g hRic) (actualJacobiJ_joint_continuous g hRic) a b).integral_prod_left
  simpa only [actualRegularJacobi_truncatedDensity_eq] using! h

theorem canonical_actualRadialMass_eq (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) :
    (∫⁻ e, actualRadialMass g hRic e ∂canonicalFrameMeasure g o) =
      ENNReal.ofReal (∫ r in Icc (0 : ℝ) Real.pi,
        ∫ e, (actualRegularJacobi g hRic e r).truncatedDensity
          ∂canonicalFrameMeasure g o) := by
  rw [canonical_actualRadialMass_integral]
  have hn : ∀ᵐ r ∂volume.restrict (Icc (0 : ℝ) Real.pi),
      0 ≤ ∫ e, (actualRegularJacobi g hRic e r).truncatedDensity
        ∂canonicalFrameMeasure g o := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    exact actualJacobi_average_nonneg g o hRic r hr.1
  rw [ofReal_integral_eq_lintegral_ofReal
    (actualJacobi_average_integrableOn g o hRic 0 Real.pi) hn]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
  symm
  exact ofReal_integral_eq_lintegral_ofReal (actualJacobiDensity_integrable g o hRic r)
    (Filter.Eventually.of_forall fun e =>
      (actualRegularJacobi g hRic e r).truncatedDensity_nonneg hr.1)

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HeatKernels10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The time derivative and exact cutoff residual of the actual normal
bundle parametrix. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter Metric
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem heatNormalOneParametrix_time_differentiable {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g} {D : HeatNormalFrameData g o c e}
    (E : HeatNormalOneExtension D) (t : ℝ) (ht : 0 < t) (x : FourSpace)
    (k l : Fin 4) : DifferentiableAt ℝ (fun s => heatNormalOneParametrix E s x k l) t := by
  exact ((fourHeatGaussian_hasDerivAt_time t ht x).mul
    (fourHeatPolynomial_hasDerivAt (fun m y => E.amplitude m y k l) t x)).differentiableAt

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HodgeTheory11
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! A uniform density-weighted scalar polynomial bound over the actual frame family. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Filter Metric
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise
noncomputable section

theorem heatFamilyScalarPolynomial_continuous (E : HeatFamilySmoothCoefficients)
    (χ : FourSpace → ℝ) (hχ : Continuous χ) :
    Continuous (fun z : ℝ × HeatRadialFrameSpace => heatFamilyScalarPolynomial E χ z.1 z.2) :=
  (hχ.comp (continuous_fst.comp continuous_snd)).mul
    (heatFamilyPolynomial_continuous _ (fun m => (E.scalarAmplitude_regular m (by omega)).continuous))

theorem heatFamilyScalarPolynomial_weight_bound (E : HeatFamilySmoothCoefficients)
    (χ : FourSpace → ℝ) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (K : Set CoordinateFrameSpace) (hK : IsCompact K) :
    ∃ B ≥ (0 : ℝ), ∀ q ∈ K, ∀ t ∈ Icc (0 : ℝ) 1, ∀ x,
      (E.U (x, q) ^ 2)⁻¹ * (heatFamilyScalarPolynomial E χ t (x, q)) ^ 2 ≤ B := by
  let W := fun z : ℝ × HeatRadialFrameSpace => (E.U z.2 ^ 2)⁻¹ *
    (heatFamilyScalarPolynomial E χ z.1 z.2) ^ 2
  have hW : Continuous W :=
    (((E.U_regular.continuous.comp continuous_snd).pow 2).inv₀
      (fun z => pow_ne_zero 2 (E.U_pos z.2).ne')).mul
      ((heatFamilyScalarPolynomial_continuous E χ hχ).pow 2)
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod (hc.prod hK)).bddAbove_image hW.continuousOn
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro q hq t ht x
  by_cases hx : x ∈ tsupport χ
  · exact (hB ⟨(t, (x, q)), ⟨ht, hx, hq⟩, rfl⟩).trans (le_max_left _ _)
  · simp only [heatFamilyScalarPolynomial, image_eq_zero_of_notMem_tsupport hx,
      zero_mul, zero_pow (by norm_num : 2 ≠ 0), mul_zero]
    exact le_max_right _ _

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M}
  {F : HeatFamilyOneCoefficients} {r : ℝ} {e : FrameBundle g}

theorem heatUniformScalarPolynomial_weight_bound (F : HeatFamilyOneCoefficients)
    (r : ℝ) (hr : 0 < r) (K : Set CoordinateFrameSpace) (hK : IsCompact K) :
    ∃ B ≥ (0 : ℝ), ∀ (e : FrameBundle g) (N : HeatCommonEulerMember g o c F r e),
      frameCoordinateState g c e ∈ K → ∀ t ∈ Icc (0 : ℝ) 1, ∀ x,
      frameExponentialJacobian g o e x * ((N.scalarData hr).polynomial t x) ^ 2 ≤ B := by
  let χ : FourSpace → ℝ := heatNormalChartBump r hr
  have hs : tsupport χ ⊆ ball (0 : FourSpace) r := by
    rw [(heatNormalChartBump r hr).tsupport_eq]
    exact closedBall_subset_ball (by change r / 2 < r; linarith)
  obtain ⟨B, hB, hb⟩ := heatFamilyScalarPolynomial_weight_bound F.base χ
    (heatNormalChartBump r hr).continuous (heatNormalChartBump r hr).hasCompactSupport K hK
  refine ⟨B, hB, ?_⟩
  intro e N hq t ht x
  by_cases hx : x ∈ tsupport χ
  · have hh := heatNormalLeadingAmplitude_normalization g o e x
      (Real.sqrt_pos.mpr (N.normal.metric_pos x (hs hx)))
    rw [← (N.normal.actual x (hs hx)).2.2.2.2, N.normal.U_family] at hh
    rw [eq_inv_of_mul_eq_one_right hh, N.scalarPolynomial_family]
    exact hb _ hq t ht x
  · rw [N.scalarPolynomial_family]
    have hz : (heatNormalChartBump r hr) x = 0 := image_eq_zero_of_notMem_tsupport hx
    simp only [heatFamilyScalarPolynomial, hz,
      zero_mul, zero_pow (by norm_num : 2 ≠ 0), mul_zero]
    exact hB

end
end PositiveEinsteinFour.Geometry
end


section

/-! Uniform inverse-time growth of the actual scalar normal columns. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Filter MeasureTheory
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M}

theorem heatUniformScalar_square_integral_bound (F : HeatFamilyOneCoefficients)
    (r : ℝ) (hr : 0 < r) (K : Set CoordinateFrameSpace) (hK : IsCompact K) :
    ∃ C ≥ (0 : ℝ), ∀ (e : FrameBundle g) (N : HeatCommonEulerMember g o c F r e),
      frameCoordinateState g c e ∈ K → ∀ t ∈ Ioc (0 : ℝ) 1,
      (∫ x, frameExponentialJacobian g o e x *
        ((N.scalarData hr).extension.scalarCutoff (N.scalarData hr).cutoff t x) ^ 2) ≤ C / t ^ 2 := by
  obtain ⟨B, hB, hbound⟩ := heatUniformScalarPolynomial_weight_bound (g := g) (o := o) (c := c) F r hr K hK
  refine ⟨B / (64 * Real.pi ^ 2), by positivity, ?_⟩
  intro e N hq t ht
  let P := N.scalarData hr
  have hp (x : FourSpace) : frameExponentialJacobian g o e x *
      (P.extension.scalarCutoff P.cutoff t x) ^ 2 ≤ B * fourHeatGaussian t x ^ 2 := by
    rw [P.cutoff_gaussian, mul_pow]
    calc
      _ = (frameExponentialJacobian g o e x * (P.polynomial t x) ^ 2) *
          fourHeatGaussian t x ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (hbound e N hq t ⟨ht.1.le, ht.2⟩ x) (sq_nonneg _)
  have hi : Integrable (fun x : FourSpace => B * fourHeatGaussian t x ^ 2) :=
    (fourHeatGaussian_square_integrable t ht.1).const_mul B
  have hc : Continuous (fun x => frameExponentialJacobian g o e x *
      (P.extension.scalarCutoff P.cutoff t x) ^ 2) :=
    (frameExponentialJacobian_continuous g o e).mul
      ((P.extension.scalarCutoff_regular P.cutoff P.cutoff_regular t).continuous.pow 2)
  have hfi : Integrable (fun x => frameExponentialJacobian g o e x *
      (P.extension.scalarCutoff P.cutoff t x) ^ 2) :=
    hi.mono' hc.aestronglyMeasurable (Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (mul_nonneg (frameExponentialJacobian_nonneg g o e x) (sq_nonneg _))]
      exact hp x)
  calc
    _ ≤ ∫ x : FourSpace, B * fourHeatGaussian t x ^ 2 := integral_mono hfi hi hp
    _ = _ := by rw [integral_const_mul, fourHeatGaussian_square_mass t ht.1]; ring

variable [MeasurableSpace M] [BorelSpace M] [Nonempty M]

theorem heatUniformScalarColumn_growth (F : HeatFamilyOneCoefficients)
    (r : ℝ) (hr : 0 < r) (K : Set CoordinateFrameSpace) (hK : IsCompact K) :
    ∃ C ≥ (0 : ℝ), ∀ (e : FrameBundle g) (N : HeatCommonEulerMember g o c F r e),
      frameCoordinateState g c e ∈ K → ∀ t ∈ Ioc (0 : ℝ) 1,
      ‖(N.scalarData hr).column t‖ ≤ C / t := by
  obtain ⟨B, hB, hbound⟩ := heatUniformScalar_square_integral_bound (g := g) (o := o) (c := c) F r hr K hK
  let K := (normalizedChartFactor g).toReal * B
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K + 1, by positivity, ?_⟩
  intro e N hq t ht
  let P := N.scalarData hr
  have hn : ‖P.column t‖ ^ 2 ≤ K / t ^ 2 := by
    rw [P.column_norm_sq_integral]
    exact (mul_le_mul_of_nonneg_left (hbound e N hq t ht) (by positivity)).trans_eq (by dsimp [K]; ring)
  have hs : (‖P.column t‖ * t) ^ 2 ≤ K := by
    calc
      _ = ‖P.column t‖ ^ 2 * t ^ 2 := by ring
      _ ≤ (K / t ^ 2) * t ^ 2 := mul_le_mul_of_nonneg_right hn (sq_nonneg t)
      _ = K := by field_simp [ht.1.ne']
  apply (le_div_iff₀ ht.1).mpr
  nlinarith [sq_nonneg K, norm_nonneg (P.column t)]

theorem heatUniformScalarNormalizedColumn_growth (F : HeatFamilyOneCoefficients)
    (r : ℝ) (hr : 0 < r) (K : Set CoordinateFrameSpace) (hK : IsCompact K) :
    ∃ C ≥ (0 : ℝ), ∀ (e : FrameBundle g) (N : HeatCommonEulerMember g o c F r e),
      frameCoordinateState g c e ∈ K → ∀ t ∈ Ioc (0 : ℝ) 1,
      ‖(N.scalarData hr).normalizedColumn t‖ ≤ C / t := by
  obtain ⟨C, hC, hc⟩ := heatUniformScalarColumn_growth (g := g) (o := o) (c := c) F r hr K hK
  refine ⟨‖((normalizedChartFactor g).toReal)⁻¹‖ * C, by positivity, ?_⟩
  intro e N hq t ht
  change ‖((normalizedChartFactor g).toReal)⁻¹ • (N.scalarData hr).column t‖ ≤ _
  rw [norm_smul]
  exact (mul_le_mul_of_nonneg_left (hc e N hq t ht) (norm_nonneg _)).trans_eq (by ring)

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeodesicGeometry12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! In the unit-Weyl branch, actual self-dual harmonic forms are parallel.
The conclusion is derived from the global Bochner identity. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Matrix TraceHessian MeasureTheory
open scoped BigOperators Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g}

local instance parallelHarmonicAddGroup_rdb4ef5_1 : AddCommGroup (smoothHarmonicTwoForms (o := o)) :=
  Submodule.addCommGroup _
theorem smoothTwoForm_covariantDerivative_zero_of_energy_zero (u : smoothTwoForms o)
    (hzero : smoothTwoFormCovariantEnergy u u = 0) (x : M) :
    twoFormFramedCovariantDerivative o u.val ⟨x,o.frame x⟩ = 0 := by
  let := normalizedVolume_isOpenPosMeasure g
  have hc := u.property.covariantPairing_continuous u.property
  have hi := smoothTwoFormCovariantPairing_integrable u u
  have hae : twoFormCovariantPairing o u.val u.val =ᵐ[normalizedVolume g] 0 :=
    (integral_eq_zero_iff_of_nonneg (twoFormCovariantPairing_self_nonneg o u.val) hi).mp hzero
  have heq : twoFormCovariantPairing o u.val u.val = 0 :=
    Measure.eq_of_ae_eq hae hc continuous_const
  have hx := congrFun heq x
  change (1 / 2 : ℝ) * ∑ a, (twoFormFramedCovariantDerivative o u.val ⟨x,o.frame x⟩ a) *
    (twoFormFramedCovariantDerivative o u.val ⟨x,o.frame x⟩ a) = 0 at hx
  ext a
  have hle : (twoFormFramedCovariantDerivative o u.val ⟨x,o.frame x⟩ a) *
      (twoFormFramedCovariantDerivative o u.val ⟨x,o.frame x⟩ a) ≤
      ∑ b, (twoFormFramedCovariantDerivative o u.val ⟨x,o.frame x⟩ b) *
        (twoFormFramedCovariantDerivative o u.val ⟨x,o.frame x⟩ b) :=
    Finset.single_le_sum (fun b _ => mul_self_nonneg _) (Finset.mem_univ a)
  change twoFormFramedCovariantDerivative o u.val ⟨x,o.frame x⟩ a = 0
  nlinarith

end
end PositiveEinsteinFour.Geometry
end


section

/-! A parallel two-form has constant norm on the actual compact connected
manifold. This uses the existing global geodesics, not a holonomy premise. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix MeasureTheory
open scoped Manifold ContDiff _root_.Topology
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem smoothTwoForm_allFrames_covariant_zero (u : smoothTwoForms o)
    (hzero : smoothTwoFormCovariantEnergy u u = 0) (e : FrameBundle g) :
    twoFormFramedCovariantDerivative o u.val e = 0 := by
  have hz := smoothTwoForm_covariantDerivative_zero_of_energy_zero u hzero e.base
  have hpair : twoFormCovariantPairing o u.val u.val e.base = 0 := by
    unfold twoFormCovariantPairing
    rw [hz]
    simp only [frameTensorPairing, Pi.zero_apply, Finset.sum_const_zero, mul_zero]
  rw [twoFormCovariantPairing_eq_frame o u.val u.val e] at hpair
  change (1 / 2 : ℝ) * ∑ a, (twoFormFramedCovariantDerivative o u.val e a) *
    (twoFormFramedCovariantDerivative o u.val e a) = 0 at hpair
  ext a
  have hle : (twoFormFramedCovariantDerivative o u.val e a) *
      (twoFormFramedCovariantDerivative o u.val e a) ≤
      ∑ b, (twoFormFramedCovariantDerivative o u.val e b) *
        (twoFormFramedCovariantDerivative o u.val e b) :=
    Finset.single_le_sum (fun b _ => mul_self_nonneg _) (Finset.mem_univ a)
  change twoFormFramedCovariantDerivative o u.val e a = 0
  nlinarith

omit [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem parallel_twoForm_norm_on_exponential (u : smoothTwoForms o)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o u.val e = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) (v : FourSpace) :
    ‖u.val (frameExponential g o e v)‖ = ‖u.val e.base‖ := by
  by_cases hv : v = 0
  · subst v
    rw [frameExponential_zero]
  have hr : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let w : FourSpace := ‖v‖⁻¹ • v
  have hwn : ‖w‖ = 1 := by
    dsimp [w]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr), inv_mul_cancel₀ hr.ne']
  let Q := directionOrientedMatrix ⟨w,hwn⟩
  let f := e.rotate (orientedToOrthogonal Q)
  have hf : f ∈ o.positive := frameRotate_oriented_positive o e he Q
  have hdir : orthogonalEuclideanIsometry (orientedToOrthogonal Q).val
      (orientedToOrthogonal Q).property (coordinateVector 0) = w := directionRotation_first ⟨w,hwn⟩
  have hexp : frameExponential g o e v = (parallelFrameFlowMap g 0 ‖v‖ f).base := by
    rw [← frameExponential_first_ray g o f hf ‖v‖ hr,
      frameExponential_rotate, map_smul, hdir]
    congr 1
    dsimp [w]
    rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  rw [hexp, parallel_twoForm_norm_along_flow u hz]
  rfl

end
end PositiveEinsteinFour.Geometry
end


end OAI
end


