-- Prove2me | Definitions.Def_OAIQ091C017
-- name    : OAIQ091C017
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T17:24:35.482405+00:00
-- url     : https://prove2.me/theorems/59945147-7300-4928-a899-77bf3663881f
-- title:
--   Definitions bundle OAIQ091C017 of the split of OpenAI, Positively curved Einstein four-manifolds (result family 348)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PositiveEinsteinFour.classification`, `OAI.PositiveEinsteinFour.classificationOn` and `OAI.PositiveEinsteinFour.orientedClassification`, carved from OpenAI's openai/math development (OpenAI, *Positively curved Einstein four-manifolds (result family 348)*, OpenAI Math Release, September 23, 2026, result family 348, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 465 declarations of OpenAI's Lean: 160 definitions, 15 inductive types or structures, 4 instances and 286 theorems. The definitions and types are `OAI.PositiveEinsteinFour.Geometry.ActualJacobiPolarInput`, `OAI.PositiveEinsteinFour.Geometry.ChartUnitTangent`, `OAI.PositiveEinsteinFour.Geometry.ComplexPolarDomain`, `OAI.PositiveEinsteinFour.Geometry.ComplexProjectivePolarData`, `OAI.PositiveEinsteinFour.Geometry.CovariantFieldSmooth`, `OAI.PositiveEinsteinFour.Geometry.DivergenceCokernel`, `OAI.PositiveEinsteinFour.Geometry.FrameOrientation.reversed`, `OAI.PositiveEinsteinFour.Geometry.GurskyLeBrunGapInput`, `OAI.PositiveEinsteinFour.Geometry.HeatCommonEulerMember`, `OAI.PositiveEinsteinFour.Geometry.HeatCommonNormalMember`, `OAI.PositiveEinsteinFour.Geometry.HeatFamilyOneCoefficients`, `OAI.PositiveEinsteinFour.Geometry.HeatFamilySmoothCoefficients`, `OAI.PositiveEinsteinFour.Geometry.HeatNormalBundleExtension`, `OAI.PositiveEinsteinFour.Geometry.HeatNormalBundleExtension.amplitude`, `OAI.PositiveEinsteinFour.Geometry.HeatNormalExtension`, `OAI.PositiveEinsteinFour.Geometry.HeatNormalFrameData`, `OAI.PositiveEinsteinFour.Geometry.HeatNormalOneExtension`, `OAI.PositiveEinsteinFour.Geometry.HeatRadialFrameSpace`, `OAI.PositiveEinsteinFour.Geometry.IsParallelFrameCurveOn`, `OAI.PositiveEinsteinFour.Geometry.KineticLocalFlow`, `OAI.PositiveEinsteinFour.Geometry.NonzeroCotangentChart`, `OAI.PositiveEinsteinFour.Geometry.NormalFrameRotation`, `OAI.PositiveEinsteinFour.Geometry.OrthonormalChartState`, `OAI.PositiveEinsteinFour.Geometry.OrthonormalFrame.scaleBetween`, `OAI.PositiveEinsteinFour.Geometry.ParallelFrameCurveAt`, `OAI.PositiveEinsteinFour.Geometry.ParallelMetricData`, `OAI.PositiveEinsteinFour.Geometry.ParallelMetricData.ofParallelFlows`, `OAI.PositiveEinsteinFour.Geometry.ParallelMetricData.toMetricGreenData`, `OAI.PositiveEinsteinFour.Geometry.ParallelScalarCalculusInput`, `OAI.PositiveEinsteinFour.Geometry.RadialFlowContDiffAt`, `OAI.PositiveEinsteinFour.Geometry.RadialHamiltonianChart`, `OAI.PositiveEinsteinFour.Geometry.ScalarJetL2`, `OAI.PositiveEinsteinFour.Geometry.ScalarL2`, `OAI.PositiveEinsteinFour.Geometry.ScalarParallelData`, `OAI.PositiveEinsteinFour.Geometry.SmoothH1TwoForm`, `OAI.PositiveEinsteinFour.Geometry.SmoothL2TwoForm`, `OAI.PositiveEinsteinFour.Geometry.SmoothScalar`, `OAI.PositiveEinsteinFour.Geometry.TwoFormSmooth`, `OAI.PositiveEinsteinFour.Geometry.UnitTangentBundle`, `OAI.PositiveEinsteinFour.Geometry.actualFrameFlow` and 135 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: [`EinsteinFour_CurvatureTensors02`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/CurvatureTensors02.lean), [`EinsteinFour_GeodesicGeometry04`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/GeodesicGeometry04.lean), [`EinsteinFour_GeodesicGeometry05`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/GeodesicGeometry05.lean), [`EinsteinFour_GeodesicGeometry12`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/GeodesicGeometry12.lean), [`EinsteinFour_GeodesicGeometry13`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/GeodesicGeometry13.lean), [`EinsteinFour_HeatKernels10`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/HeatKernels10.lean), [`EinsteinFour_HodgeTheory08`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/HodgeTheory08.lean), [`EinsteinFour_HodgeTheory09`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/HodgeTheory09.lean), [`EinsteinFour_ScalarRegularity07`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/ScalarRegularity07.lean), [`EinsteinFour_WeylEstimates03`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/WeylEstimates03.lean), [`EinsteinFour_WeylNormal`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/WeylNormal.lean).
--
--   **Imports.** It imports the published bundle `Def_EinsteinFour`; the bundles `OAIQ091C013` and `OAIQ091C014` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ091C037`; the statements `OAI.PositiveEinsteinFour.Geometry.actual_derdzinski_hitchin` and `OAI.PositiveEinsteinFour.Geometry.actual_frameExponential_injOn_sqrt_three`.
-- source:
--   OpenAI, Positively curved Einstein four-manifolds (result family 348), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 348; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Positively-curved-Einstein-four-manifolds-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_EinsteinFour
import Definitions.Def_OAIQ091C013
import Definitions.Def_OAIQ091C014

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylNormal
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instBorelSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instT2SpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Link the normal-tensor calculation to the concrete metric. The classical
curvature decomposition is displayed as an explicit local hypothesis here;
the angular mean identities themselves are proved, not postulated. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory Angular
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

local instance instNormedAddCommGroupMat3_r4e575d_1 : NormedAddCommGroup Mat3 := Matrix.frobeniusNormedAddCommGroup
theorem normalCurvature_eq_of_decomposition
    (g : SmoothMetric M) (c : M) (e : OrthonormalFrame g c)
    (hdecomp : frameCurvature g c e =
      einsteinCurvatureTensor (plusWeyl g c e) (minusWeyl g c e)) (q : Directions) :
    normalCurvature g c e q = 1 + normalDeviation (plusWeyl g c e) (minusWeyl g c e) q := by
  ext i j
  change normalEvaluation q i j (frameCurvature g c e) = _
  rw [hdecomp]
  exact normalEvaluation_einstein (plusWeyl g c e) (minusWeyl g c e) q i j

theorem normalCurvatureDeviation_eq_of_decomposition
    (g : SmoothMetric M) (c : M) (e : OrthonormalFrame g c)
    (hdecomp : frameCurvature g c e =
      einsteinCurvatureTensor (plusWeyl g c e) (minusWeyl g c e)) (q : Directions) :
    normalCurvatureDeviation g c e q =
      normalDeviation (plusWeyl g c e) (minusWeyl g c e) q := by
  rw [normalCurvatureDeviation, normalCurvature_eq_of_decomposition g c e hdecomp]
  abel

end

end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_CurvatureTensors02
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instBorelSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instCompactSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instSecondCountableTopologyOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Angular.coordinateFlip_apply _root_.OAI.PositiveEinsteinFour.Angular.coordinatePermutation_apply _root_.OAI.PositiveEinsteinFour.Angular.pairMix_coordinate _root_.OAI.PositiveEinsteinFour.Angular.planeRotation_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverChart_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverDeck_deck _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverDeck_proj _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverLocal_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverMetric_inner _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_deck_mfderiv _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_projection_mfderiv _root_.OAI.PositiveEinsteinFour.Geometry.orientationFrameClass_proj
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! A four-column Gram--Schmidt normalizer with entrywise smooth dependence
on the positive metric matrix. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators ContDiff

noncomputable section

def gramColumnThree (G : Mat4) : CoordinateColumn :=
  gramRemove G (gramColumnTwo G)
    (gramRemove G (gramColumnOne G) (gramRemove G (gramColumnZero G) (Pi.single 3 1)))

def gramColumn (G : Mat4) (i : Fin 4) : CoordinateColumn :=
  ![gramColumnZero G, gramColumnOne G, gramColumnTwo G, gramColumnThree G] i

/-- The lower-triangular leading coefficient of every residual is one. -/
theorem gramColumn_diagonal (G : Mat4) (i : Fin 4) : gramColumn G i i = 1 := by
  fin_cases i <;> simp [gramColumn, gramColumnZero, gramColumnOne,
    gramColumnTwo, gramColumnThree, gramRemove]

theorem gramColumn_ne_zero (G : Mat4) (i : Fin 4) : gramColumn G i ≠ 0 := by
  intro h
  have hi := gramColumn_diagonal G i
  rw [h] at hi
  norm_num at hi

theorem gramColumn_energy_pos (G : Mat4) (hG : G.PosDef) (i : Fin 4) :
    0 < metricPair G (gramColumn G i) (gramColumn G i) :=
  metricPair_pos G hG _ (gramColumn_ne_zero G i)

theorem metricPair_gramRemove (G : Mat4) (w u v : CoordinateColumn) :
    metricPair G w (gramRemove G u v) = metricPair G w v -
      (metricPair G u v / metricPair G u u) * metricPair G w u := by
  simp only [metricPair, gramRemove, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  repeat' (apply Finset.sum_congr rfl; intro _ _)
  ring

theorem metricPair_gramRemove_self (G : Mat4) (u v : CoordinateColumn)
    (hu : metricPair G u u ≠ 0) : metricPair G u (gramRemove G u v) = 0 := by
  rw [metricPair_gramRemove, div_mul_cancel₀ _ hu, sub_self]

theorem metricPair_gramRemove_orthogonal (G : Mat4) (w u v : CoordinateColumn)
    (hwu : metricPair G w u = 0) :
    metricPair G w (gramRemove G u v) = metricPair G w v := by
  rw [metricPair_gramRemove, hwu, mul_zero, sub_zero]

/-- Orthogonality is proved before normalization, using only the exact
projection formula and positivity of the residual energies. -/
theorem gramColumn_orthogonal (G : Mat4) (hG : G.PosDef)
    (i j : Fin 4) (hij : i ≠ j) : metricPair G (gramColumn G i) (gramColumn G j) = 0 := by
  have hp (i : Fin 4) : metricPair G (gramColumn G i) (gramColumn G i) ≠ 0 :=
    (gramColumn_energy_pos G hG i).ne'
  have h0 : metricPair G (gramColumnZero G) (gramColumnZero G) ≠ 0 := hp 0
  have h1 : metricPair G (gramColumnOne G) (gramColumnOne G) ≠ 0 := hp 1
  have h2 : metricPair G (gramColumnTwo G) (gramColumnTwo G) ≠ 0 := hp 2
  have h01 : metricPair G (gramColumnZero G) (gramColumnOne G) = 0 :=
    metricPair_gramRemove_self G _ _ h0
  have h02 : metricPair G (gramColumnZero G) (gramColumnTwo G) = 0 := by
    rw [gramColumnTwo, metricPair_gramRemove_orthogonal _ _ _ _ h01]
    exact metricPair_gramRemove_self G _ _ h0
  have h12 : metricPair G (gramColumnOne G) (gramColumnTwo G) = 0 :=
    metricPair_gramRemove_self G _ _ h1
  have h03 : metricPair G (gramColumnZero G) (gramColumnThree G) = 0 := by
    rw [gramColumnThree, metricPair_gramRemove_orthogonal _ _ _ _ h02,
      metricPair_gramRemove_orthogonal _ _ _ _ h01]
    exact metricPair_gramRemove_self G _ _ h0
  have h13 : metricPair G (gramColumnOne G) (gramColumnThree G) = 0 := by
    rw [gramColumnThree, metricPair_gramRemove_orthogonal _ _ _ _ h12]
    exact metricPair_gramRemove_self G _ _ h1
  have h23 : metricPair G (gramColumnTwo G) (gramColumnThree G) = 0 :=
    metricPair_gramRemove_self G _ _ h2
  have hs := metricPair_symm G hG.isHermitian
  fin_cases i <;> fin_cases j <;> dsimp only [gramColumn]
  all_goals first
    | exact False.elim (hij rfl)
    | assumption
    | exact (hs _ _).trans h01
    | exact (hs _ _).trans h02
    | exact (hs _ _).trans h03
    | exact (hs _ _).trans h12
    | exact (hs _ _).trans h13
    | exact (hs _ _).trans h23

/-- The inverse square roots of the four residual energies give an
orthonormal frame, with no eigenvector selection. -/
def gramNormalizer (G : Mat4) : Mat4 := fun k i =>
  (Real.sqrt (metricPair G (gramColumn G i) (gramColumn G i)))⁻¹ * gramColumn G i k

theorem gramNormalizer_normalizes (G : Mat4) (hG : G.PosDef) :
    (gramNormalizer G)ᵀ * G * gramNormalizer G = 1 := by
  ext i j
  have hp := gramColumn_energy_pos G hG
  have heq : ((gramNormalizer G)ᵀ * G * gramNormalizer G) i j =
      metricPair G (fun k => gramNormalizer G k i) (fun k => gramNormalizer G k j) := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, metricPair, Finset.sum_mul]
    rw [Finset.sum_comm]
  rw [heq]
  change metricPair G (fun k => _ * gramColumn G i k)
    (fun k => _ * gramColumn G j k) = if i = j then 1 else 0
  rw [metricPair_scaled]
  by_cases hij : i = j
  · subst j
    rw [ite_eq_left rfl]
    have hs : Real.sqrt (metricPair G (gramColumn G i) (gramColumn G i)) ≠ 0 :=
      (Real.sqrt_pos.2 (hp i)).ne'
    have hsq := Real.sq_sqrt (hp i).le
    field_simp
    nlinarith
  · rw [ite_eq_right hij, gramColumn_orthogonal G hG i j hij, mul_zero]

theorem gramRemove_contDiffAt {G : FourSpace → Mat4} {u v : FourSpace → CoordinateColumn}
    {z : FourSpace} (hG : ∀ i j, ContDiffAt ℝ ∞ (fun w => G w i j) z)
    (hu : ∀ i, ContDiffAt ℝ ∞ (fun w => u w i) z)
    (hv : ∀ i, ContDiffAt ℝ ∞ (fun w => v w i) z)
    (hp : metricPair (G z) (u z) (u z) ≠ 0) (i : Fin 4) :
    ContDiffAt ℝ ∞ (fun w => gramRemove (G w) (u w) (v w) i) z := by
  have hc := (metricPair_contDiffAt hG hu hv).div (metricPair_contDiffAt hG hu hu) hp
  exact (hv i).sub (hc.mul (hu i))

theorem gramColumn_contDiffAt {G : FourSpace → Mat4} {z : FourSpace}
    (hG : ∀ i j, ContDiffAt ℝ ∞ (fun w => G w i j) z) (hp : (G z).PosDef)
    (i j : Fin 4) : ContDiffAt ℝ ∞ (fun w => gramColumn (G w) i j) z := by
  have hzero (j : Fin 4) : ContDiffAt ℝ ∞ (fun w => gramColumnZero (G w) j) z :=
    contDiffAt_const
  have hp0 : metricPair (G z) (gramColumnZero (G z)) (gramColumnZero (G z)) ≠ 0 :=
    (gramColumn_energy_pos (G z) hp 0).ne'
  have hone (j : Fin 4) : ContDiffAt ℝ ∞ (fun w => gramColumnOne (G w) j) z :=
    gramRemove_contDiffAt (v := fun _ => Pi.single 1 1) hG hzero
      (fun _ => contDiffAt_const) hp0 j
  have hp1 : metricPair (G z) (gramColumnOne (G z)) (gramColumnOne (G z)) ≠ 0 :=
    (gramColumn_energy_pos (G z) hp 1).ne'
  have htwo (j : Fin 4) : ContDiffAt ℝ ∞ (fun w => gramColumnTwo (G w) j) z := by
    exact gramRemove_contDiffAt hG hone
      (gramRemove_contDiffAt (v := fun _ => Pi.single 2 1) hG hzero
        (fun _ => contDiffAt_const) hp0) hp1 j
  have hp2 : metricPair (G z) (gramColumnTwo (G z)) (gramColumnTwo (G z)) ≠ 0 :=
    (gramColumn_energy_pos (G z) hp 2).ne'
  have hthree (j : Fin 4) : ContDiffAt ℝ ∞ (fun w => gramColumnThree (G w) j) z := by
    exact gramRemove_contDiffAt hG htwo
      (gramRemove_contDiffAt hG hone
        (gramRemove_contDiffAt (v := fun _ => Pi.single 3 1) hG hzero
          (fun _ => contDiffAt_const) hp0) hp1) hp2 j
  fin_cases i
  · exact hzero j
  · exact hone j
  · exact htwo j
  · exact hthree j

theorem gramNormalizer_contDiffAt {G : FourSpace → Mat4} {z : FourSpace}
    (hG : ∀ i j, ContDiffAt ℝ ∞ (fun w => G w i j) z) (hp : (G z).PosDef)
    (i j : Fin 4) : ContDiffAt ℝ ∞ (fun w => gramNormalizer (G w) i j) z := by
  have hc := gramColumn_contDiffAt hG hp j
  have he := metricPair_contDiffAt hG hc hc
  have hpos := gramColumn_energy_pos (G z) hp j
  have hs : ContDiffAt ℝ ∞ (fun w => Real.sqrt
      (metricPair (G w) (gramColumn (G w) j) (gramColumn (G w) j))) z :=
    (Real.contDiffAt_sqrt hpos.ne').comp z he
  exact (hs.inv (Real.sqrt_pos.2 hpos).ne').mul (hc i)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual local orthonormal frames obtained from smooth coordinate vectors
by the explicit four-column normalizer. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Bundle
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def chartGramMatrix (g : SmoothMetric M) (c : M) (S : Mat4) (z : FourSpace) : Mat4 :=
  gramNormalizer (metricInChart g c z) * S

theorem chartGramMatrix_normalizes (g : SmoothMetric M) (c : M)
    (S : Mat4) (hS : Sᵀ * S = 1) (z : ChartTarget c) :
    (chartGramMatrix g c S z)ᵀ * metricInChart g c z * chartGramMatrix g c S z = 1 := by
  have hn := gramNormalizer_normalizes _ (metricInChart_posDef g c z z.property)
  calc
    _ = Sᵀ * ((gramNormalizer (metricInChart g c z))ᵀ * metricInChart g c z *
        gramNormalizer (metricInChart g c z)) * S := by
      simp only [chartGramMatrix, Matrix.transpose_mul, Matrix.mul_assoc]
    _ = 1 := by rw [hn, Matrix.mul_one, hS]

def chartGramFrame (g : SmoothMetric M) (c : M) (S : Mat4) (hS : Sᵀ * S = 1)
    (z : ChartTarget c) : OrthonormalFrame g ((chartAt FourSpace c).symm z) where
  matrix := chartInverseMatrix c z * chartGramMatrix g c S z
  orthonormal := by
    have hm := metricInChart_eq_center_congruence g c z
    rw [← Matrix.mul_assoc] at hm
    calc
      _ = (chartGramMatrix g c S z)ᵀ *
          ((chartInverseMatrix c z)ᵀ * chartMetric g ((chartAt FourSpace c).symm z) *
            chartInverseMatrix c z) * chartGramMatrix g c S z := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = 1 := by
        rw [← hm]
        exact chartGramMatrix_normalizes g c S hS z

def chartGramSection (g : SmoothMetric M) (c : M) (S : Mat4) (hS : Sᵀ * S = 1)
    (z : ChartTarget c) : FrameBundle g :=
  ⟨(chartAt FourSpace c).symm z, chartGramFrame g c S hS z⟩

theorem chartGramMatrix_contDiffAt (g : SmoothMetric M) (c : M) (S : Mat4)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target) (i j : Fin 4) :
    ContDiffAt ℝ ∞ (fun w => chartGramMatrix g c S w i j) z := by
  change ContDiffAt ℝ ∞ (fun w => ∑ k, gramNormalizer (metricInChart g c w) i k * S k j) z
  apply ContDiffAt.sum
  intro k _
  exact (gramNormalizer_contDiffAt (metricInChart_contDiffAt g c z hz)
    (metricInChart_posDef g c z hz) i k).mul contDiffAt_const

theorem chartGramFrame_vector (g : SmoothMetric M) (c : M) (S : Mat4)
    (hS : Sᵀ * S = 1) (z : ChartTarget c) (i : Fin 4) :
    (chartGramFrame g c S hS z).vector i =
      mfderiv I4 I4 (chartAt FourSpace c).symm z
        (WithLp.toLp 2 (fun j => chartGramMatrix g c S z j i)) := by
  change WithLp.toLp 2 (fun j => (chartInverseMatrix c z * chartGramMatrix g c S z) j i) = _
  exact chartInverseMatrix_apply c z (fun j => chartGramMatrix g c S z j i)

theorem continuous_chartGramSection (g : SmoothMetric M) (c : M) (S : Mat4)
    (hS : Sᵀ * S = 1) : Continuous (chartGramSection g c S hS) := by
  have hv (i : Fin 4) : ContDiffOn ℝ ∞
      (fun z => WithLp.toLp 2 (fun j => chartGramMatrix g c S z j i))
      (chartAt FourSpace c).target := by
    apply (contDiffOn_piLp (p := (2 : ENNReal))).mpr
    intro j z hz
    exact (chartGramMatrix_contDiffAt g c S z hz j i).contDiffWithinAt
  have ht (i : Fin 4) := (chart_inverse_moving_vector_smooth c _ (hv i)).continuousOn
  apply continuous_induced_rng.mpr
  have hbase : Continuous (fun z : ChartTarget c => (chartAt FourSpace c).symm z) :=
    (chartAt FourSpace c).continuousOn_symm.domRestrict
  have hvec (i : Fin 4) : Continuous (fun z : ChartTarget c =>
      (⟨(chartAt FourSpace c).symm z, (chartGramFrame g c S hS z).vector i⟩ :
        TangentBundle I4 M)) := by
    apply (ht i).domRestrict.congr
    intro z
    exact congrArg (fun v : TangentSpace I4 ((chartAt FourSpace c).symm z) =>
      (⟨(chartAt FourSpace c).symm z, v⟩ : TangentBundle I4 M))
      (chartGramFrame_vector g c S hS z i).symm
  exact hbase.prodMk (continuous_pi hvec)


def localGramSection (g : SmoothMetric M) (c : M) (S : Mat4) (hS : Sᵀ * S = 1)
    (x : M) : FrameBundle g :=
  open Classical in
  if hx : x ∈ (chartAt FourSpace c).source then
    chartGramSection g c S hS ⟨chartAt FourSpace c x, (chartAt FourSpace c).map_source hx⟩
  else frameAt g x

theorem localGramSection_base (g : SmoothMetric M) (c : M) (S : Mat4)
    (hS : Sᵀ * S = 1) (x : M) : (localGramSection g c S hS x).base = x := by
  classical
  by_cases hx : x ∈ (chartAt FourSpace c).source
  · simp only [localGramSection, dite_eq_left hx, chartGramSection]
    exact (chartAt FourSpace c).left_inv hx
  · simp only [localGramSection, dite_eq_right hx, frameAt]

theorem continuousAt_localGramSection (g : SmoothMetric M) (c : M) (S : Mat4)
    (hS : Sᵀ * S = 1) : ContinuousAt (localGramSection g c S hS) c := by
  classical
  let F : {x : M // x ∈ (chartAt FourSpace c).source} → ChartTarget c := fun x =>
    ⟨chartAt FourSpace c x, (chartAt FourSpace c).map_source x.property⟩
  have hF : Continuous F :=
    ((chartAt FourSpace c).continuousOn.domRestrict).subtype_mk _
  have hcont : ContinuousOn (localGramSection g c S hS) (chartAt FourSpace c).source := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    apply ((continuous_chartGramSection g c S hS).comp hF).congr
    intro x
    change chartGramSection g c S hS ⟨chartAt FourSpace c x,
      (chartAt FourSpace c).map_source x.property⟩ = localGramSection g c S hS x
    simp only [localGramSection, dite_eq_left x.property]
  exact hcont.continuousAt ((chartAt FourSpace c).open_source.mem_nhds
    (mem_chart_source FourSpace c))

/-- A constant orthogonal change makes the local smooth frame positive at
its center; openness of the chosen component then makes it positive nearby. -/
theorem exists_positive_localGramSection (g : SmoothMetric M) (o : FrameOrientation g)
    (c : M) : ∃ S : Mat4, ∃ hS : Sᵀ * S = 1,
      ∀ᶠ x in 𝓝 c, localGramSection g c S hS x ∈ o.positive := by
  classical
  let z : ChartTarget c := ⟨chartAt FourSpace c c,
    (chartAt FourSpace c).map_source (mem_chart_source FourSpace c)⟩
  let e := chartGramFrame g c 1 (by simp) z
  let f := o.frame ((chartAt FourSpace c).symm z)
  let S := e.changeMatrix f
  have hS : Sᵀ * S = 1 := e.changeMatrix_orthogonal f
  have he : chartGramFrame g c S hS z = f := by
    apply frame_eq_of_matrix_eq_p0
    have hm := e.mul_changeMatrix f
    simpa only [e, S, chartGramFrame, chartGramMatrix, Matrix.mul_one,
      Matrix.mul_assoc] using hm
  have hpos : localGramSection g c S hS c ∈ o.positive := by
    change (if hx : c ∈ (chartAt FourSpace c).source then _ else _) ∈ o.positive
    rw [dite_eq_left (mem_chart_source FourSpace c)]
    change (⟨(chartAt FourSpace c).symm z, chartGramFrame g c S hS z⟩ : FrameBundle g) ∈ o.positive
    rw [he]
    exact o.frame_positive _
  refine ⟨S, hS, ?_⟩
  exact (continuousAt_localGramSection g c S hS).preimage_mem_nhds
    (o.clopen.isOpen.mem_nhds hpos)

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylEstimates03
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Jointly continuous orthonormal-frame charts with compact orthogonal
fiber. These charts will give compactness over a compact base. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Bundle Set
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def jointChartGramSection (g : SmoothMetric M) (c : M)
    (p : ChartTarget c × OrthogonalFour) : FrameBundle g :=
  chartGramSection g c p.2.val p.2.property p.1

theorem continuous_jointChartGramSection (g : SmoothMetric M) (c : M) :
    Continuous (jointChartGramSection g c) := by
  have hn (i j : Fin 4) : Continuous (fun z : ChartTarget c =>
      gramNormalizer (metricInChart g c z) i j) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    exact ((gramNormalizer_contDiffAt (metricInChart_contDiffAt g c z z.property)
      (metricInChart_posDef g c z z.property) i j).continuousAt).comp
      continuous_subtype_val.continuousAt
  have hm (i j : Fin 4) : Continuous (fun p : ChartTarget c × OrthogonalFour =>
      chartGramMatrix g c p.2.val p.1 i j) := by
    change Continuous (fun p : ChartTarget c × OrthogonalFour =>
      ∑ k, gramNormalizer (metricInChart g c p.1) i k * p.2.val k j)
    apply continuous_finsetSum
    intro k _
    exact ((hn i k).comp continuous_fst).mul
      ((show Continuous (fun S : Mat4 => S k j) from
        (continuous_apply j).comp (continuous_apply k)).comp
        (continuous_subtype_val.comp continuous_snd))
  have hphi : ContMDiffOn I4 I4 ∞ (chartAt FourSpace c).symm
      (chartAt FourSpace c).target := contMDiffOn_chart_symm
  have ht := (hphi.contMDiffOn_tangentMapWithin (m := ∞) (by simp)
    (chartAt FourSpace c).open_target.uniqueMDiffOn).continuousOn
  have hv (i : Fin 4) : Continuous (fun p : ChartTarget c × OrthogonalFour =>
      (⟨p.1.val, WithLp.toLp 2 (fun j => chartGramMatrix g c p.2.val p.1 j i)⟩ :
        TangentBundle I4 FourSpace)) := by
    have hw : Continuous (fun p : ChartTarget c × OrthogonalFour =>
        WithLp.toLp 2 (fun j => chartGramMatrix g c p.2.val p.1 j i)) :=
      (PiLp.continuous_toLp 2 _).comp (continuous_pi (fun j => hm j i))
    exact (tangentBundleModelSpaceHomeomorph I4).symm.continuous.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk hw)
  have hvec (i : Fin 4) : Continuous (fun p : ChartTarget c × OrthogonalFour =>
      (⟨(jointChartGramSection g c p).base,
        (jointChartGramSection g c p).frame.vector i⟩ : TangentBundle I4 M)) := by
    have hcomp := ht.comp_continuous (hv i) (fun p => p.1.property)
    apply hcomp.congr
    intro p
    change (⟨(chartAt FourSpace c).symm p.1.val,
      mfderivWithin I4 I4 (chartAt FourSpace c).symm (chartAt FourSpace c).target p.1.val
        (WithLp.toLp 2 (fun j => chartGramMatrix g c p.2.val p.1 j i))⟩ :
          TangentBundle I4 M) = _
    rw [mfderivWithin_of_isOpen (chartAt FourSpace c).open_target p.1.property]
    exact congrArg (fun v : TangentSpace I4 ((chartAt FourSpace c).symm p.1.val) =>
      (⟨(chartAt FourSpace c).symm p.1.val, v⟩ : TangentBundle I4 M))
      (chartGramFrame_vector g c p.2.val p.2.property p.1 i).symm
  apply continuous_induced_rng.mpr
  exact (((chartAt FourSpace c).continuousOn_symm.domRestrict).comp continuous_fst).prodMk
    (continuous_pi hvec)

theorem chartGramFrame_surjective (g : SmoothMetric M) (c : M) (z : ChartTarget c)
    (f : OrthonormalFrame g ((chartAt FourSpace c).symm z)) :
    ∃ S : OrthogonalFour, chartGramFrame g c S.val S.property z = f := by
  let e := chartGramFrame g c 1 (by simp) z
  let S : OrthogonalFour := ⟨e.changeMatrix f, e.changeMatrix_orthogonal f⟩
  refine ⟨S, ?_⟩
  have hm : (chartGramFrame g c S.val S.property z).matrix = f.matrix := by
    have he : e.matrix = chartInverseMatrix c z * gramNormalizer (metricInChart g c z) := by
      simp only [e, chartGramFrame, chartGramMatrix, Matrix.mul_one]
    change chartInverseMatrix c z * (gramNormalizer (metricInChart g c z) * S.val) = _
    rw [← Matrix.mul_assoc, ← he]
    exact e.mul_changeMatrix f
  exact frame_eq_of_matrix_eq_p2 _ _ hm

end
end PositiveEinsteinFour.Geometry
end


section

/-! Continuity of actual covariant tensors on the intrinsic orthonormal-frame
bundle, using one fixed tangent-bundle trivialization near each frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Bundle
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem frameChartMatrix_continuousAt (g : SmoothMetric M) (c : M)
    (e : FrameBundle g) (he : e.base ∈ (chartAt FourSpace c).source) (a b : Fin 4) :
    ContinuousAt (fun f => frameChartMatrix g c f a b) e := by
  let V := trivializationAt FourSpace (TangentSpace I4 : M → Type _) c
  have hv : (⟨e.base, e.frame.vector b⟩ : TangentBundle I4 M) ∈ V.source := by
    apply V.mem_source.mpr
    simpa only [V, TangentBundle.trivializationAt_baseSet] using he
  have hvec : Continuous (fun f : FrameBundle g =>
      (⟨f.base, f.frame.vector b⟩ : TangentBundle I4 M)) :=
    (continuous_apply b).comp (continuous_snd.comp (continuous_frameRealization g))
  have htr := V.toOpenPartialHomeomorph.continuousAt hv
  have hm : ContinuousAt (fun f : FrameBundle g =>
      V (⟨f.base, f.frame.vector b⟩ : TangentBundle I4 M)) e :=
    htr.comp (f := fun f : FrameBundle g =>
      (⟨f.base, f.frame.vector b⟩ : TangentBundle I4 M)) hvec.continuousAt
  have hs : ContinuousAt (fun f : FrameBundle g =>
      (V (⟨f.base, f.frame.vector b⟩ : TangentBundle I4 M)).2) e :=
    continuous_snd.continuousAt.comp hm
  exact (EuclideanSpace.proj a : FourSpace →L[ℝ] ℝ).continuous.continuousAt.comp
    (f := fun f : FrameBundle g =>
      (V (⟨f.base, f.frame.vector b⟩ : TangentBundle I4 M)).2) hs

theorem frameChartMatrix_eq (g : SmoothMetric M) (c : M) (e : FrameBundle g) :
    frameChartMatrix g c e =
      chartTransitionMatrix e.base c (chartAt FourSpace e.base e.base) * e.frame.matrix := by
  ext a b
  change (((trivializationAt FourSpace (TangentSpace I4 : M → Type _) c)
    (⟨e.base, e.frame.vector b⟩ : TangentBundle I4 M)).2) a = _
  rw [TangentBundle.trivializationAt_apply]
  simp only [OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm,
    I4, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.id_comp, Function.comp_id, Set.range_id]
  rw [fderivWithin_univ]
  let L : FourSpace →L[ℝ] FourSpace :=
    fderiv ℝ (chartTransition e.base c) (chartAt FourSpace e.base e.base)
  change L (e.frame.vector b) a = _
  have hv : e.frame.vector b = ∑ k, e.frame.matrix k b • coordinateVector k :=
    (sum_coordinateVector (fun k => e.frame.matrix k b)).symm
  rw [hv, map_sum]
  simp only [map_smul, WithLp.ofLp_sum, PiLp.smul_apply, smul_eq_mul, Finset.sum_apply,
    Matrix.mul_apply, chartTransitionMatrix, L]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- A coordinate tensor is evaluated continuously on frames once its local
components are continuous and its chart transition law has been proved. -/
theorem continuous_framedTensor {n : ℕ} (g : SmoothMetric M)
    (T : M → FourSpace → CovariantCoordinates n)
    (hT : ∀ c z, z ∈ (chartAt FourSpace c).target →
      ∀ a, ContinuousAt (fun w => T c w a) z)
    (hchange : ∀ c d z, z ∈ (chartAt FourSpace c).target →
      (chartAt FourSpace c).symm z ∈ (chartAt FourSpace d).source →
      T c z = frameTensor (chartTransitionMatrix c d z) (T d (chartTransition c d z))) :
    Continuous (fun e : FrameBundle g => frameTensor e.frame.matrix
      (T e.base (chartAt FourSpace e.base e.base))) := by
  apply continuous_iff_continuousAt.mpr
  intro e
  let c := e.base
  have he : e.base ∈ (chartAt FourSpace c).source := mem_chart_source FourSpace c
  have hcoord : ContinuousAt (fun f : FrameBundle g => chartAt FourSpace c f.base) e :=
    ((chartAt FourSpace c).continuousAt he).comp (continuous_frameBase g).continuousAt
  have hfixed (a : Fin n → Fin 4) : ContinuousAt
      (fun f : FrameBundle g => frameTensor (frameChartMatrix g c f)
        (T c (chartAt FourSpace c f.base)) a) e := by
    unfold frameTensor
    apply tendsto_finsetSum
    intro b _
    exact (tendsto_finsetProd _ (fun k _ => frameChartMatrix_continuousAt g c e he
      (b k) (a k))).mul ((hT c _ ((chartAt FourSpace c).map_source he) b).comp
        (f := fun f : FrameBundle g => chartAt FourSpace c f.base) hcoord)
  have hfixedAll : ContinuousAt (fun f : FrameBundle g =>
      frameTensor (frameChartMatrix g c f) (T c (chartAt FourSpace c f.base))) e :=
    continuousAt_pi.mpr hfixed
  apply hfixedAll.congr_of_eventuallyEq
  have hnear : ∀ᶠ f : FrameBundle g in 𝓝 e,
      f.base ∈ (chartAt FourSpace c).source :=
    (continuous_frameBase g).continuousAt.eventually
      ((chartAt FourSpace c).open_source.mem_nhds he)
  filter_upwards [hnear] with f hf
  have hcenter : (chartAt FourSpace f.base).symm (chartAt FourSpace f.base f.base) =
      f.base := (chartAt FourSpace f.base).left_inv (mem_chart_source FourSpace f.base)
  have hc := hchange f.base c (chartAt FourSpace f.base f.base)
    (mem_chart_target FourSpace f.base) (by simpa only [hcenter] using hf)
  have hvalue : chartTransition f.base c (chartAt FourSpace f.base f.base) =
      chartAt FourSpace c f.base := by
    rw [chartTransition, (chartAt FourSpace f.base).left_inv
      (mem_chart_source FourSpace f.base)]
  rw [hc, hvalue, ← frameTensor_mul, ← frameChartMatrix_eq]

end
end PositiveEinsteinFour.Geometry
end


section

/-! A measurable positive orthonormal-frame section on a compact oriented
base, assembled from finitely many actual local Gram frames. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set MeasureTheory
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem continuousOn_localGramSection (g : SmoothMetric M) (c : M) (S : Mat4)
    (hS : Sᵀ * S = 1) :
    ContinuousOn (localGramSection g c S hS) (chartAt FourSpace c).source := by
  classical
  let F : {x : M // x ∈ (chartAt FourSpace c).source} → ChartTarget c := fun x =>
    ⟨chartAt FourSpace c x, (chartAt FourSpace c).map_source x.property⟩
  have hF : Continuous F :=
    ((chartAt FourSpace c).continuousOn.domRestrict).subtype_mk _
  apply continuousOn_iff_continuous_domRestrict.mpr
  apply ((continuous_chartGramSection g c S hS).comp hF).congr
  intro x
  change chartGramSection g c S hS ⟨chartAt FourSpace c x,
    (chartAt FourSpace c).map_source x.property⟩ = localGramSection g c S hS x
  simp only [localGramSection, dite_eq_left x.property]

variable [MeasurableSpace M] [BorelSpace M]

theorem exists_measurable_positive_frame [CompactSpace M] [Nonempty M]
    (g : SmoothMetric M) (o : FrameOrientation g) :
    ∃ f : M → FrameBundle g, Measurable f ∧
      ∀ x, (f x).base = x ∧ f x ∈ o.positive := by
  classical
  have hlocal (c : M) : ∃ U : Set M, IsOpen U ∧ c ∈ U ∧
      ∃ f : M → FrameBundle g, Measurable f ∧
        ∀ x ∈ U, (f x).base = x ∧ f x ∈ o.positive := by
    obtain ⟨S, hS, hpositive⟩ := exists_positive_localGramSection g o c
    let V := (chartAt FourSpace c).source
    let f := V.piecewise (localGramSection g c S hS) (fun _ => frameAt g c)
    have hf : Measurable f :=
      (continuousOn_localGramSection g c S hS).measurable_piecewise
        continuousOn_const (chartAt FourSpace c).open_source.measurableSet
    obtain ⟨U, hUV, hUopen, hc⟩ := mem_nhds_iff.mp
      (Filter.inter_mem hpositive (chart_source_mem_nhds FourSpace c))
    refine ⟨U, hUopen, hc, f, hf, ?_⟩
    intro x hx
    have hp := hUV hx
    have he : f x = localGramSection g c S hS x := by
      exact Set.piecewise_eq_of_mem V _ _ hp.2
    rw [he]
    exact ⟨localGramSection_base g c S hS x, hp.1⟩
  choose U hU hc f hf hgood using hlocal
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hU
    (fun x _ => mem_iUnion.mpr ⟨x, hc x⟩)
  have hfinite (s : Finset M) : ∃ F : M → FrameBundle g, Measurable F ∧
      ∀ x ∈ ⋃ c ∈ s, U c, (F x).base = x ∧ F x ∈ o.positive := by
    induction s using Finset.induction_on with
    | empty =>
      obtain ⟨c⟩ := ‹Nonempty M›
      refine ⟨fun _ => frameAt g c, measurable_const, ?_⟩
      simp
    | @insert c s _hcs ih =>
      obtain ⟨F, hF, hFg⟩ := ih
      refine ⟨(U c).piecewise (f c) F, (hf c).piecewise (hU c).measurableSet hF, ?_⟩
      intro x hx
      by_cases hxc : x ∈ U c
      · rw [Set.piecewise_eq_of_mem (U c) _ _ hxc]
        exact hgood c x hxc
      · rw [Set.piecewise_eq_of_notMem (U c) _ _ hxc]
        apply hFg x
        simpa only [Finset.mem_insert, iUnion_iUnion_eq_or_left, mem_union,
          hxc, false_or] using hx
  obtain ⟨F, hF, hFg⟩ := hfinite t
  exact ⟨F, hF, fun x => hFg x (ht (mem_univ x))⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! A compact smooth base has compact orthonormal-frame bundle. The proof
uses finitely many compact coordinate neighborhoods and the compact
orthogonal matrix fiber. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Bundle Set
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem exists_compact_frame_neighborhood (g : SmoothMetric M) (c : M) :
    ∃ U ∈ 𝓝 c, ∃ K : Set (FrameBundle g), IsCompact K ∧
      ∀ e : FrameBundle g, e.base ∈ U → e ∈ K := by
  have hc : chartAt FourSpace c c ∈ (chartAt FourSpace c).target :=
    (chartAt FourSpace c).map_source (mem_chart_source FourSpace c)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    ((chartAt FourSpace c).open_target.mem_nhds hc)
  let B : Set FourSpace := Metric.closedBall (chartAt FourSpace c c) (r / 2)
  have hBtarget : B ⊆ (chartAt FourSpace c).target :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  let C : Set (ChartTarget c) := Subtype.val ⁻¹' B
  have hC : IsCompact C := by
    apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
    have he : Subtype.val '' C = B := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact hw
      · intro hz
        exact ⟨⟨z, hBtarget hz⟩, hz, rfl⟩
    rw [he]
    exact isCompact_closedBall _ _
  let K := jointChartGramSection g c '' (C ×ˢ (univ : Set OrthogonalFour))
  have hK : IsCompact K :=
    (hC.prod isCompact_univ).image (continuous_jointChartGramSection g c)
  refine ⟨(chartAt FourSpace c).symm '' B, ?_, K, hK, ?_⟩
  · have hn := (chartAt FourSpace c).symm.image_mem_nhds hc
      (Metric.closedBall_mem_nhds (chartAt FourSpace c c) (by positivity : 0 < r / 2))
    simpa only [(chartAt FourSpace c).left_inv (mem_chart_source FourSpace c)] using hn
  · intro e he
    obtain ⟨z, hz, hez⟩ := he
    let z' : ChartTarget c := ⟨z, hBtarget hz⟩
    have hex : ∃ S : OrthogonalFour, jointChartGramSection g c (z', S) = e := by
      cases e with
      | mk x f =>
        dsimp only at hez
        subst x
        obtain ⟨S, hS⟩ := chartGramFrame_surjective g c z' f
        exact ⟨S, congrArg (FrameBundle.mk ((chartAt FourSpace c).symm z)) hS⟩
    obtain ⟨S, hS⟩ := hex
    exact ⟨(z', S), ⟨hz, mem_univ S⟩, hS⟩

theorem actual_compactFrameBundle [CompactSpace M] (g : SmoothMetric M) :
    CompactSpace (FrameBundle g) := by
  choose U hU K hK hcover using exists_compact_frame_neighborhood g
  obtain ⟨t, ht⟩ := finite_cover_nhds hU
  apply isCompact_univ_iff.mp
  have hfinite : IsCompact (⋃ c ∈ t, K c) :=
    t.finite_toSet.isCompact_biUnion (fun c _ => hK c)
  have heq : (⋃ c ∈ t, K c) = (univ : Set (FrameBundle g)) := by
    apply univ_subset_iff.mp
    intro e _
    have he : e.base ∈ ⋃ c ∈ t, U c := by rw [ht]; trivial
    obtain ⟨c, hct, hc⟩ := mem_iUnion₂.mp he
    exact mem_iUnion₂.mpr ⟨c, hct, hcover c e hc⟩
  rwa [heq] at hfinite

end
end PositiveEinsteinFour.Geometry
end


section

/-! All four actual Weyl fields used in the parallel-frame Green calculus
are continuous on the intrinsic orthonormal-frame bundle. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix TraceHessian
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem continuous_framedWeylDerivative (g : SmoothMetric M) (k : ℕ) :
    Continuous (fun e : FrameBundle g => frameTensor e.frame.matrix
      (iteratedWeylDerivative g e.base k (chartAt FourSpace e.base e.base))) := by
  apply continuous_framedTensor g (fun c => iteratedWeylDerivative g c k)
  · intro c z hz a
    exact (iteratedWeylDerivative_contDiffAt g c k z hz a).continuousAt
  · intro c d z hz hx
    exact iteratedWeylDerivative_transition g c d k z hz hx

theorem actual_plusWeyl_continuous (g : SmoothMetric M) :
    Continuous (fun e : FrameBundle g => plusWeyl g e.base e.frame) := by
  have h := continuous_blockCoordinates _ (continuous_framedWeylDerivative g 0)
    quaternionMatrix
  apply h.congr
  intro e
  exact frameWeyl_blockCoordinates e.frame

theorem actual_plusWeylGradient_continuous (g : SmoothMetric M) (i : Fin 4) :
    Continuous (fun e : FrameBundle g => plusWeylGradient g e.base e.frame i) := by
  have h := continuous_framedWeylDerivative g 1
  have hs : Continuous (fun e : FrameBundle g => fun a : Fin 4 → Fin 4 =>
      frameTensor e.frame.matrix
        (iteratedWeylDerivative g e.base 1 (chartAt FourSpace e.base e.base))
        (Fin.cons i a)) :=
    continuous_pi (fun a =>
      (show Continuous (fun T : CovariantCoordinates 5 => T (Fin.cons i a)) from
        continuous_apply _).comp h)
  exact continuous_blockCoordinates _ hs quaternionMatrix

theorem actual_plusWeylHessian_continuous (g : SmoothMetric M) (i j : Fin 4) :
    Continuous (fun e : FrameBundle g => plusWeylHessian g e.base e.frame i j) := by
  have h := continuous_framedWeylDerivative g 2
  have hs : Continuous (fun e : FrameBundle g => fun a : Fin 4 → Fin 4 =>
      frameTensor e.frame.matrix
        (iteratedWeylDerivative g e.base 2 (chartAt FourSpace e.base e.base))
        (Fin.cons i (Fin.cons j a))) :=
    continuous_pi (fun a =>
      (show Continuous (fun T : CovariantCoordinates 6 => T (Fin.cons i (Fin.cons j a))) from
        continuous_apply _).comp h)
  exact continuous_blockCoordinates _ hs quaternionMatrix

theorem actual_plusWeylThirdDerivative_continuous (g : SmoothMetric M)
    (i j k : Fin 4) :
    Continuous (fun e : FrameBundle g => plusWeylThirdDerivative g e.base e.frame i j k) := by
  have h := continuous_framedWeylDerivative g 3
  have hs : Continuous (fun e : FrameBundle g => fun a : Fin 4 → Fin 4 =>
      frameTensor e.frame.matrix
        (iteratedWeylDerivative g e.base 3 (chartAt FourSpace e.base e.base))
        (Fin.cons i (Fin.cons j (Fin.cons k a)))) :=
    continuous_pi (fun a =>
      (show Continuous (fun T : CovariantCoordinates 7 =>
        T (Fin.cons i (Fin.cons j (Fin.cons k a)))) from continuous_apply _).comp h)
  exact continuous_blockCoordinates _ hs quaternionMatrix

end
end PositiveEinsteinFour.Geometry
end


section

/-! Primitive parallel-frame ODEs imply differentiation of actual framed
tensors. All coordinate changes are the already proved tensor pullbacks. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

/-- The local velocity and parallel-frame equations in the fixed chart
centered at the current base point. -/
structure ParallelFrameCurveAt (g : SmoothMetric M) (γ : ℝ → FrameBundle g)
    (k : Fin 4) (t : ℝ) : Prop where
  velocity : HasDerivAt
    (fun s => chartAt FourSpace (γ t).base (γ s).base)
    (WithLp.toLp 2 (fun r => frameChartMatrix g (γ t).base (γ t) r k)) t
  parallel : ∀ i j, HasDerivAt
    (fun s => frameChartMatrix g (γ t).base (γ s) i j)
    (-((∑ r, frameChartMatrix g (γ t).base (γ t) r k •
      connectionMatrix g (γ t).base r (chartAt FourSpace (γ t).base (γ t).base)) *
        frameChartMatrix g (γ t).base (γ t)) i j) t

theorem framedTensor_eq_fixedChart {n : ℕ} (g : SmoothMetric M)
    (T : M → FourSpace → CovariantCoordinates n)
    (hchange : ∀ c d z, z ∈ (chartAt FourSpace c).target →
      (chartAt FourSpace c).symm z ∈ (chartAt FourSpace d).source →
      T c z = frameTensor (chartTransitionMatrix c d z) (T d (chartTransition c d z)))
    (c : M) (e : FrameBundle g) (he : e.base ∈ (chartAt FourSpace c).source) :
    frameTensor e.frame.matrix (T e.base (chartAt FourSpace e.base e.base)) =
      frameTensor (frameChartMatrix g c e) (T c (chartAt FourSpace c e.base)) := by
  have hcenter : (chartAt FourSpace e.base).symm (chartAt FourSpace e.base e.base) =
      e.base := (chartAt FourSpace e.base).left_inv (mem_chart_source FourSpace e.base)
  have hc := hchange e.base c (chartAt FourSpace e.base e.base)
    (mem_chart_target FourSpace e.base) (by simpa only [hcenter] using he)
  have hvalue : chartTransition e.base c (chartAt FourSpace e.base e.base) =
      chartAt FourSpace c e.base := by
    rw [chartTransition, (chartAt FourSpace e.base).left_inv
      (mem_chart_source FourSpace e.base)]
  rw [hc, hvalue, ← frameTensor_mul, ← frameChartMatrix_eq]

/-- A chart-covariant tensor differentiates along an actual parallel frame
curve to its framed covariant derivative, with the new direction first. -/
theorem hasDerivAt_framedTensor {n : ℕ} (g : SmoothMetric M)
    (T : M → FourSpace → CovariantCoordinates n)
    (hT : ∀ c z, z ∈ (chartAt FourSpace c).target →
      ∀ a, DifferentiableAt ℝ (fun w => T c w a) z)
    (hchange : ∀ c d z, z ∈ (chartAt FourSpace c).target →
      (chartAt FourSpace c).symm z ∈ (chartAt FourSpace d).source →
      T c z = frameTensor (chartTransitionMatrix c d z) (T d (chartTransition c d z)))
    (hDchange : ∀ c d z, z ∈ (chartAt FourSpace c).target →
      (chartAt FourSpace c).symm z ∈ (chartAt FourSpace d).source →
      covariantDerivative g c (T c) z = frameTensor (chartTransitionMatrix c d z)
        (covariantDerivative g d (T d) (chartTransition c d z)))
    (γ : ℝ → FrameBundle g) (t : ℝ) (k : Fin 4)
    (hγ : ContinuousAt γ t) (hp : ParallelFrameCurveAt g γ k t)
    (a : Fin n → Fin 4) :
    HasDerivAt (fun s => frameTensor (γ s).frame.matrix
      (T (γ s).base (chartAt FourSpace (γ s).base (γ s).base)) a)
      (frameTensor (γ t).frame.matrix
        (covariantDerivative g (γ t).base (T (γ t).base)
          (chartAt FourSpace (γ t).base (γ t).base)) (Fin.cons k a)) t := by
  let c := (γ t).base
  let x (s : ℝ) : FourSpace := chartAt FourSpace c (γ s).base
  let E (s : ℝ) : Mat4 := frameChartMatrix g c (γ s)
  have he : (γ t).base ∈ (chartAt FourSpace c).source := mem_chart_source FourSpace c
  have hz : x t ∈ (chartAt FourSpace c).target := (chartAt FourSpace c).map_source he
  have hd := hasDerivAt_parallel_frameTensor g c x E (T c) t k hp.velocity hp.parallel
    (hT c (x t) hz) a
  have hvalue := framedTensor_eq_fixedChart g (fun c => covariantDerivative g c (T c))
    hDchange c (γ t) he
  have hvalue' := congrFun hvalue (Fin.cons k a)
  change frameTensor (γ t).frame.matrix
    (covariantDerivative g c (T c) (x t)) (Fin.cons k a) =
      frameTensor (E t) (covariantDerivative g c (T c) (x t)) (Fin.cons k a) at hvalue'
  rw [← hvalue'] at hd
  apply hd.congr_of_eventuallyEq
  have hnear : ∀ᶠ s in 𝓝 t, (γ s).base ∈ (chartAt FourSpace c).source :=
    ((continuous_frameBase g).continuousAt.comp hγ).eventually
      ((chartAt FourSpace c).open_source.mem_nhds he)
  filter_upwards [hnear] with s hs
  exact congrFun (framedTensor_eq_fixedChart g T hchange c (γ s) hs) a

end
end PositiveEinsteinFour.Geometry
end


section

/-! Smooth scalar functions and their first three actual covariant derivatives
are continuous on the intrinsic orthonormal-frame bundle. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem continuous_framedScalarDerivative (g : SmoothMetric M) {a : M → ℝ}
    (ha : ContMDiff I4 𝓘(ℝ, ℝ) ∞ a) (k : ℕ) :
    Continuous (fun e : FrameBundle g => frameTensor e.frame.matrix
      (iteratedScalarDerivative g a e.base k (chartAt FourSpace e.base e.base))) := by
  apply continuous_framedTensor g (fun c => iteratedScalarDerivative g a c k)
  · intro c z hz v
    exact (iteratedScalarDerivative_contDiffAt g ha c k z hz v).continuousAt
  · intro c d z hz hx
    exact iteratedScalarDerivative_transition g ha c d k z hz hx

theorem actual_scalarGradient_continuous (g : SmoothMetric M) {a : M → ℝ}
    (ha : ContMDiff I4 𝓘(ℝ, ℝ) ∞ a) (i : Fin 4) :
    Continuous (fun e : FrameBundle g => scalarGradient g a e i) := by
  exact (show Continuous (fun T : CovariantCoordinates 1 => T ![i]) from
    continuous_apply _).comp (continuous_framedScalarDerivative g ha 1)

theorem actual_scalarHessian_continuous (g : SmoothMetric M) {a : M → ℝ}
    (ha : ContMDiff I4 𝓘(ℝ, ℝ) ∞ a) (i j : Fin 4) :
    Continuous (fun e : FrameBundle g => scalarHessian g a e i j) := by
  exact (show Continuous (fun T : CovariantCoordinates 2 => T ![i, j]) from
    continuous_apply _).comp (continuous_framedScalarDerivative g ha 2)

theorem actual_scalarThird_continuous (g : SmoothMetric M) {a : M → ℝ}
    (ha : ContMDiff I4 𝓘(ℝ, ℝ) ∞ a) (i j k : Fin 4) :
    Continuous (fun e : FrameBundle g => scalarThird g a e i j k) := by
  exact (show Continuous (fun T : CovariantCoordinates 3 => T ![i, j, k]) from
    continuous_apply _).comp (continuous_framedScalarDerivative g ha 3)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Smooth two-form fields are defined by their actual coefficients in
local positively oriented orthonormal frames. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

def twoFormChartValue (o : FrameOrientation g) (u : M → TwoFormFour)
    (c : M) (S : Mat4) (hS : Sᵀ * S = 1) (z : FourSpace) : TwoFormFour :=
  open Classical in
  if hz : z ∈ (chartAt FourSpace c).target then
    twoFormFrameValue o u (chartGramSection g c S hS ⟨z, hz⟩) else 0

def TwoFormSmooth (o : FrameOrientation g) (u : M → TwoFormFour) : Prop :=
  ∀ (c : M) (S : Mat4) (hS : Sᵀ * S = 1) (U : Set FourSpace),
    IsOpen U → ∀ hUt : U ⊆ (chartAt FourSpace c).target,
    (∀ z (hz : z ∈ U), chartGramSection g c S hS ⟨z, hUt hz⟩ ∈ o.positive) →
    ContDiffOn ℝ ∞ (twoFormChartValue o u c S hS) U

theorem twoFormChartValue_zero (o : FrameOrientation g) (c : M) (S : Mat4)
    (hS : Sᵀ * S = 1) : twoFormChartValue o (0 : M → TwoFormFour) c S hS = 0 := by
  funext z
  simp [twoFormChartValue, twoFormFrameValue_zero]

theorem twoFormChartValue_add (o : FrameOrientation g) (u v : M → TwoFormFour)
    (c : M) (S : Mat4) (hS : Sᵀ * S = 1) :
    twoFormChartValue o (u + v) c S hS =
      twoFormChartValue o u c S hS + twoFormChartValue o v c S hS := by
  funext z
  by_cases hz : z ∈ (chartAt FourSpace c).target
  · simp only [twoFormChartValue, dite_eq_left hz, Pi.add_apply, twoFormFrameValue_add]
  · simp only [twoFormChartValue, dite_eq_right hz, Pi.add_apply, add_zero]

theorem twoFormChartValue_smul (o : FrameOrientation g) (r : ℝ) (u : M → TwoFormFour)
    (c : M) (S : Mat4) (hS : Sᵀ * S = 1) :
    twoFormChartValue o (r • u) c S hS = r • twoFormChartValue o u c S hS := by
  funext z
  by_cases hz : z ∈ (chartAt FourSpace c).target
  · simp only [twoFormChartValue, dite_eq_left hz, Pi.smul_apply, twoFormFrameValue_smul]
  · simp only [twoFormChartValue, dite_eq_right hz, Pi.smul_apply, smul_zero]

def smoothTwoForms (o : FrameOrientation g) : Submodule ℝ (M → TwoFormFour) where
  carrier := TwoFormSmooth o
  zero_mem' := by
    intro c S hS U _ _ _
    rw [twoFormChartValue_zero]
    exact contDiffOn_const
  add_mem' {u v} hu hv := by
    intro c S hS U hU hUt hp
    rw [twoFormChartValue_add]
    exact (hu c S hS U hU hUt hp).add (hv c S hS U hU hUt hp)
  smul_mem' r u hu := by
    intro c S hS U hU hUt hp
    rw [twoFormChartValue_smul]
    exact (hu c S hS U hU hUt hp).const_smul r

end
end PositiveEinsteinFour.Geometry
end


section

/-! The oriented orthonormal-frame probability, formed from actual normalized
Riemannian volume and Haar probability on the oriented orthogonal fiber. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set MeasureTheory
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M]

def positiveFrameSection (g : SmoothMetric M) (o : FrameOrientation g) :
    M → FrameBundle g := (exists_measurable_positive_frame g o).choose

def orientedFrameParametrization (g : SmoothMetric M) (o : FrameOrientation g)
    (p : M × OrientedOrthogonalFour) : FrameBundle g :=
  (positiveFrameSection g o p.1).rotate (orientedToOrthogonal p.2)

variable [T3Space M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.normalizedVolumeProbability
def canonicalFrameMeasure (g : SmoothMetric M) (o : FrameOrientation g) :
    Measure (FrameBundle g) :=
  Measure.map (orientedFrameParametrization g o)
    ((normalizedVolume g).prod orientedFrameHaar)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual Weyl and scalar parallel differentiation from the coordinate
velocity and Levi-Civita frame ODE. No curvature derivative is an input. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix TraceHessian
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem hasDerivAt_framedWeylDerivative (g : SmoothMetric M)
    (γ : ℝ → FrameBundle g) (t : ℝ) (k : Fin 4)
    (hγ : ContinuousAt γ t) (hp : ParallelFrameCurveAt g γ k t)
    (r : ℕ) (a : Fin (4 + r) → Fin 4) :
    HasDerivAt (fun s => frameTensor (γ s).frame.matrix
      (iteratedWeylDerivative g (γ s).base r
        (chartAt FourSpace (γ s).base (γ s).base)) a)
      (frameTensor (γ t).frame.matrix
        (iteratedWeylDerivative g (γ t).base (r + 1)
          (chartAt FourSpace (γ t).base (γ t).base)) (Fin.cons k a)) t := by
  apply hasDerivAt_framedTensor g (fun c => iteratedWeylDerivative g c r)
  · intro c z hz v
    exact (iteratedWeylDerivative_contDiffAt g c r z hz v).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  · intro c d z hz hx
    exact iteratedWeylDerivative_transition g c d r z hz hx
  · intro c d z hz hx
    exact iteratedWeylDerivative_transition g c d (r + 1) z hz hx
  · exact hγ
  · exact hp

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.parallelFlowNormedRing
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.parallelFlowNormedSpace
local instance parallelFlowNormedAlgebra_r4e575d_1 : NormedAlgebra ℝ Mat3 := Matrix.frobeniusNormedAlgebra
theorem actual_plusWeyl_parallel_derivative (g : SmoothMetric M)
    (γ : ℝ → FrameBundle g) (t : ℝ) (k : Fin 4)
    (hγ : ContinuousAt γ t) (hp : ParallelFrameCurveAt g γ k t) :
    HasDerivAt (fun s => plusWeyl g (γ s).base (γ s).frame)
      (plusWeylGradient g (γ t).base (γ t).frame k) t := by
  have h := hasDerivAt_blockCoordinates
    (fun a => hasDerivAt_framedWeylDerivative g γ t k hγ hp 0 a) quaternionMatrix
  simpa only [iteratedWeylDerivative, frameWeyl_blockCoordinates,
    plusWeylGradient, gradientBlock] using h

theorem actual_plusWeylGradient_parallel_derivative (g : SmoothMetric M)
    (γ : ℝ → FrameBundle g) (t : ℝ) (k j : Fin 4)
    (hγ : ContinuousAt γ t) (hp : ParallelFrameCurveAt g γ k t) :
    HasDerivAt (fun s => plusWeylGradient g (γ s).base (γ s).frame j)
      (plusWeylHessian g (γ t).base (γ t).frame k j) t := by
  exact hasDerivAt_blockCoordinates
    (fun a => hasDerivAt_framedWeylDerivative g γ t k hγ hp 1 (Fin.cons j a))
    quaternionMatrix

theorem actual_plusWeylHessian_parallel_derivative (g : SmoothMetric M)
    (γ : ℝ → FrameBundle g) (t : ℝ) (k i j : Fin 4)
    (hγ : ContinuousAt γ t) (hp : ParallelFrameCurveAt g γ k t) :
    HasDerivAt (fun s => plusWeylHessian g (γ s).base (γ s).frame i j)
      (plusWeylThirdDerivative g (γ t).base (γ t).frame k i j) t := by
  exact hasDerivAt_blockCoordinates
    (fun a => hasDerivAt_framedWeylDerivative g γ t k hγ hp 2
      (Fin.cons i (Fin.cons j a))) quaternionMatrix

theorem hasDerivAt_framedScalarDerivative (g : SmoothMetric M) {a : M → ℝ}
    (ha : ContMDiff I4 𝓘(ℝ, ℝ) ∞ a) (γ : ℝ → FrameBundle g)
    (t : ℝ) (k : Fin 4) (hγ : ContinuousAt γ t)
    (hp : ParallelFrameCurveAt g γ k t) (r : ℕ) (v : Fin r → Fin 4) :
    HasDerivAt (fun s => frameTensor (γ s).frame.matrix
      (iteratedScalarDerivative g a (γ s).base r
        (chartAt FourSpace (γ s).base (γ s).base)) v)
      (frameTensor (γ t).frame.matrix
        (iteratedScalarDerivative g a (γ t).base (r + 1)
          (chartAt FourSpace (γ t).base (γ t).base)) (Fin.cons k v)) t := by
  apply hasDerivAt_framedTensor g (fun c => iteratedScalarDerivative g a c r)
  · intro c z hz v
    exact (iteratedScalarDerivative_contDiffAt g ha c r z hz v).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  · intro c d z hz hx
    exact iteratedScalarDerivative_transition g ha c d r z hz hx
  · intro c d z hz hx
    exact iteratedScalarDerivative_transition g ha c d (r + 1) z hz hx
  · exact hγ
  · exact hp

theorem actual_scalarValue_parallel_derivative (g : SmoothMetric M) {a : M → ℝ}
    (ha : ContMDiff I4 𝓘(ℝ, ℝ) ∞ a) (γ : ℝ → FrameBundle g)
    (t : ℝ) (k : Fin 4) (hγ : ContinuousAt γ t)
    (hp : ParallelFrameCurveAt g γ k t) :
    HasDerivAt (fun s => a (γ s).base) (scalarGradient g a (γ t) k) t := by
  have h := hasDerivAt_framedScalarDerivative g ha γ t k hγ hp 0 ![]
  refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)).congr_deriv ?_
  · beta_reduce
    rw [frameTensor_zero]
    change a (γ s).base = a ((chartAt FourSpace (γ s).base).symm
      (chartAt FourSpace (γ s).base (γ s).base))
    rw [(chartAt FourSpace (γ s).base).left_inv (mem_chart_source FourSpace (γ s).base)]
  · rfl

theorem actual_scalarGradient_parallel_derivative (g : SmoothMetric M) {a : M → ℝ}
    (ha : ContMDiff I4 𝓘(ℝ, ℝ) ∞ a) (γ : ℝ → FrameBundle g)
    (t : ℝ) (k j : Fin 4) (hγ : ContinuousAt γ t)
    (hp : ParallelFrameCurveAt g γ k t) :
    HasDerivAt (fun s => scalarGradient g a (γ s) j)
      (scalarHessian g a (γ t) k j) t := by
  exact hasDerivAt_framedScalarDerivative g ha γ t k hγ hp 1 ![j]

theorem actual_scalarHessian_parallel_derivative (g : SmoothMetric M) {a : M → ℝ}
    (ha : ContMDiff I4 𝓘(ℝ, ℝ) ∞ a) (γ : ℝ → FrameBundle g)
    (t : ℝ) (k i j : Fin 4) (hγ : ContinuousAt γ t)
    (hp : ParallelFrameCurveAt g γ k t) :
    HasDerivAt (fun s => scalarHessian g a (γ s) i j)
      (scalarThird g a (γ t) k i j) t := by
  exact hasDerivAt_framedScalarDerivative g ha γ t k hγ hp 2 ![i, j]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Reflection transforms an actual parallel-frame curve into a parallel
curve with the corresponding reversal of its time parameter. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem frameChartMatrix_reflection (g : SmoothMetric M) (c : M)
    (e : FrameBundle g) (i j : Fin 4) :
    frameChartMatrix g c (frameReflection e) i j =
      orientationSign j * frameChartMatrix g c e i j := by
  rw [frameChartMatrix_eq, frameChartMatrix_eq]
  change (∑ r, chartTransitionMatrix e.base c (chartAt FourSpace e.base e.base) i r *
      e.frame.reflect.matrix r j) = _
  simp only [OrthonormalFrame.reflect_matrix, Matrix.mul_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  ring

/-- The reflected curve follows the same horizontal direction when time
is multiplied by the sign of the reflected frame axis. -/
theorem parallelFrameCurveAt_reflection (g : SmoothMetric M)
    (γ : ℝ → FrameBundle g) (k : Fin 4) (t : ℝ)
    (h : ParallelFrameCurveAt g γ k (orientationSign k * t)) :
    ParallelFrameCurveAt g
      (fun s => frameReflection (γ (orientationSign k * s))) k t := by
  have ht : HasDerivAt (fun s : ℝ => orientationSign k * s) (orientationSign k) t := by
    exact hasDerivAt_const_mul (orientationSign k)
  constructor
  · have hv := h.velocity.scomp t ht
    have he : WithLp.toLp 2 (fun r =>
        frameChartMatrix g (γ (orientationSign k * t)).base
          (frameReflection (γ (orientationSign k * t))) r k) =
        orientationSign k • WithLp.toLp 2 (fun r =>
          frameChartMatrix g (γ (orientationSign k * t)).base
            (γ (orientationSign k * t)) r k) := by
      ext r
      exact frameChartMatrix_reflection g (γ (orientationSign k * t)).base
        (γ (orientationSign k * t)) r k
    change HasDerivAt
      (fun s => chartAt FourSpace (γ (orientationSign k * t)).base
        (γ (orientationSign k * s)).base)
      (WithLp.toLp 2 (fun r => frameChartMatrix g (γ (orientationSign k * t)).base
        (frameReflection (γ (orientationSign k * t))) r k)) t
    rw [he]
    exact hv
  · intro i j
    have hm := ((h.parallel i j).comp t ht).const_mul (orientationSign j)
    change HasDerivAt (fun s =>
      frameChartMatrix g (γ (orientationSign k * t)).base
        (frameReflection (γ (orientationSign k * s))) i j)
      (-((∑ r, frameChartMatrix g (γ (orientationSign k * t)).base
          (frameReflection (γ (orientationSign k * t))) r k •
        connectionMatrix g (γ (orientationSign k * t)).base r
          (chartAt FourSpace (γ (orientationSign k * t)).base
            (γ (orientationSign k * t)).base)) *
        frameChartMatrix g (γ (orientationSign k * t)).base
          (frameReflection (γ (orientationSign k * t)))) i j) t
    have he : frameChartMatrix g (γ (orientationSign k * t)).base
        (frameReflection (γ (orientationSign k * t))) =
        frameChartMatrix g (γ (orientationSign k * t)).base
          (γ (orientationSign k * t)) * frameReflectionMatrix := by
      ext a b
      rw [frameChartMatrix_reflection]
      simp only [frameReflectionMatrix, Matrix.mul_diagonal]
      ring
    rw [he]
    have hcol (r : Fin 4) :
        (frameChartMatrix g (γ (orientationSign k * t)).base
          (γ (orientationSign k * t)) * frameReflectionMatrix) r k =
        orientationSign k * frameChartMatrix g (γ (orientationSign k * t)).base
          (γ (orientationSign k * t)) r k := by
      simp only [frameReflectionMatrix, Matrix.mul_diagonal]
      ring
    simp_rw [hcol]
    change HasDerivAt (fun s =>
      frameChartMatrix g (γ (orientationSign k * t)).base
        (frameReflection (γ (orientationSign k * s))) i j)
      (-((∑ r, (orientationSign k * frameChartMatrix g (γ (orientationSign k * t)).base
          (γ (orientationSign k * t)) r k) •
        connectionMatrix g (γ (orientationSign k * t)).base r
          (chartAt FourSpace (γ (orientationSign k * t)).base
            (γ (orientationSign k * t)).base)) *
        (frameChartMatrix g (γ (orientationSign k * t)).base
          (γ (orientationSign k * t)) * frameReflectionMatrix)) i j) t
    rw [reflection_parallel_rhs
      (frameChartMatrix g (γ (orientationSign k * t)).base (γ (orientationSign k * t)))
      (fun r => connectionMatrix g (γ (orientationSign k * t)).base r
        (chartAt FourSpace (γ (orientationSign k * t)).base
          (γ (orientationSign k * t)).base)) k i j]
    have hfun : (fun s => frameChartMatrix g (γ (orientationSign k * t)).base
        (frameReflection (γ (orientationSign k * s))) i j) =
        (fun s => orientationSign j * frameChartMatrix g (γ (orientationSign k * t)).base
          (γ (orientationSign k * s)) i j) := by
      funext s
      exact frameChartMatrix_reflection _ _ _ _ _
    rw [hfun]
    exact hm

end
end PositiveEinsteinFour.Geometry
end


section

/-! The local horizontal frame vector field is smooth and preserves the
metric Gram matrix. The defining equations are ordinary finite-dimensional
ODEs in one coordinate chart. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

/-- Horizontal motion in the `k`th frame direction in a fixed chart. -/
def parallelFrameVectorField (g : SmoothMetric M) (c : M) (k : Fin 4)
    (p : CoordinateFrameSpace) : CoordinateFrameSpace :=
  (WithLp.toLp 2 (fun r => p.2 r k), -(parallelFrameConnection g c k p * p.2))

theorem parallelFrameVectorField_contDiffAt (g : SmoothMetric M) (c : M)
    (k : Fin 4) (p : CoordinateFrameSpace)
    (hp : p.1 ∈ (chartAt FourSpace c).target) :
    ContDiffAt ℝ ∞ (parallelFrameVectorField g c k) p := by
  have he (a b : Fin 4) : ContDiffAt ℝ ∞
      (fun q : CoordinateFrameSpace => q.2 a b) p := by fun_prop
  have hΓ (a r b : Fin 4) : ContDiffAt ℝ ∞
      (fun q : CoordinateFrameSpace => christoffel g c q.1 a r b) p :=
    (christoffel_contDiffAt g c p.1 hp
      (metricInChart_posDef g c p.1 hp).det_pos.ne' a r b).comp p contDiffAt_fst
  have hv : ContDiffAt ℝ ∞
      (fun q : CoordinateFrameSpace => WithLp.toLp 2 (fun r => q.2 r k)) p := by
    apply (contDiffAt_piLp 2).mpr
    intro r
    exact he r k
  have hE : ContDiffAt ℝ ∞
      (fun q : CoordinateFrameSpace => -(parallelFrameConnection g c k q * q.2)) p := by
    apply contDiffAt_pi.mpr
    intro a
    apply contDiffAt_pi.mpr
    intro b
    change ContDiffAt ℝ ∞ (fun q : CoordinateFrameSpace =>
      -(∑ s, (∑ r, q.2 r k * christoffel g c q.1 a r s) * q.2 s b)) p
    apply ContDiffAt.neg
    apply ContDiffAt.sum
    intro s _
    apply ContDiffAt.mul
    · exact ContDiffAt.sum (fun r _ => (he r k).mul (hΓ a r s))
    · exact he s b
  exact hv.prodMk hE

end
end PositiveEinsteinFour.Geometry
end


section

/-! The horizontal frame equation with a fixed, arbitrary initial direction.
Unlike choosing a unit direction, this equation is smooth at zero velocity. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

abbrev HeatRadialFrameSpace := FourSpace × CoordinateFrameSpace

end
end PositiveEinsteinFour.Geometry
end


section

/-! Local integral curves of the actual horizontal vector field, restricted
to the chart and to the orthonormal-frame equations. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

/-- A matrix normalized by the chart metric gives an actual orthonormal
frame, after applying the inverse-chart tangent map. -/
def chartMatrixFrame (g : SmoothMetric M) (c : M) (z : ChartTarget c)
    (E : Mat4) (hE : Eᵀ * metricInChart g c z * E = 1) :
    OrthonormalFrame g ((chartAt FourSpace c).symm z) where
  matrix := chartInverseMatrix c z * E
  orthonormal := by
    have hm := metricInChart_eq_center_congruence g c z
    rw [← Matrix.mul_assoc] at hm
    calc
      _ = Eᵀ * ((chartInverseMatrix c z)ᵀ *
          chartMetric g ((chartAt FourSpace c).symm z) * chartInverseMatrix c z) * E := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [← hm]; exact hE

end
end PositiveEinsteinFour.Geometry
end


section

/-! Raw parallel-frame calculus supplies the actual Green data. The local
Weyl equation, differential Bianchi and both third-derivative commutators
are proved from the metric, rather than supplied as published inputs. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

/-- Only raw flow, parallel differentiation and normalized
Ricci data remain in the classical frame-calculus input. -/
structure ParallelMetricData (g : SmoothMetric M) (μ : Measure (FrameBundle g)) where
  flow : Fin 4 → FrameFlow g μ
  parallelCurve : ∀ k t e,
    ParallelFrameCurveAt g (fun s => (flow k).map s e) k t
  ricci : ∀ (e : FrameBundle g) j a,
    (∑ i, frameCurvature g e.base e.frame i j a i) = if j = a then 3 else 0

namespace ParallelMetricData

variable {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

theorem continuousWeyl (_d : ParallelMetricData g μ) :
    Continuous (fun e : FrameBundle g => plusWeyl g e.base e.frame) :=
  actual_plusWeyl_continuous g

theorem continuousGradient (_d : ParallelMetricData g μ) (i : Fin 4) :
    Continuous (fun e : FrameBundle g => plusWeylGradient g e.base e.frame i) :=
  actual_plusWeylGradient_continuous g i

theorem continuousHessian (_d : ParallelMetricData g μ) (i j : Fin 4) :
    Continuous (fun e : FrameBundle g => plusWeylHessian g e.base e.frame i j) :=
  actual_plusWeylHessian_continuous g i j

theorem continuousThird (_d : ParallelMetricData g μ) (i j k : Fin 4) :
    Continuous (fun e : FrameBundle g => plusWeylThirdDerivative g e.base e.frame i j k) :=
  actual_plusWeylThirdDerivative_continuous g i j k

theorem curve_continuous (d : ParallelMetricData g μ) (k : Fin 4) (e : FrameBundle g) :
    Continuous (fun s => (d.flow k).map s e) :=
  (d.flow k).continuous.comp (continuous_id.prodMk continuous_const)

theorem derivativeWeyl (d : ParallelMetricData g μ) (k : Fin 4) (t : ℝ)
    (e : FrameBundle g) : HasDerivAt
    (fun s => plusWeyl g ((d.flow k).map s e).base ((d.flow k).map s e).frame)
    (plusWeylGradient g ((d.flow k).map t e).base ((d.flow k).map t e).frame k) t :=
  actual_plusWeyl_parallel_derivative g _ t k (d.curve_continuous k e).continuousAt
    (d.parallelCurve k t e)

theorem derivativeGradient (d : ParallelMetricData g μ) (k j : Fin 4) (t : ℝ)
    (e : FrameBundle g) : HasDerivAt
    (fun s => plusWeylGradient g ((d.flow k).map s e).base ((d.flow k).map s e).frame j)
    (plusWeylHessian g ((d.flow k).map t e).base ((d.flow k).map t e).frame k j) t :=
  actual_plusWeylGradient_parallel_derivative g _ t k j (d.curve_continuous k e).continuousAt
    (d.parallelCurve k t e)

theorem derivativeHessian (d : ParallelMetricData g μ) (k i j : Fin 4) (t : ℝ)
    (e : FrameBundle g) : HasDerivAt
    (fun s => plusWeylHessian g ((d.flow k).map s e).base ((d.flow k).map s e).frame i j)
    (plusWeylThirdDerivative g ((d.flow k).map t e).base ((d.flow k).map t e).frame k i j) t :=
  actual_plusWeylHessian_parallel_derivative g _ t k i j (d.curve_continuous k e).continuousAt
    (d.parallelCurve k t e)

theorem ricciThree (d : ParallelMetricData g μ) : RicciThree g :=
  ricciThree_of_frame_contraction d.ricci

local instance parallelDataNormedRing_r4e575d_1 : NormedRing Mat := Matrix.frobeniusNormedRing
local instance parallelDataNormedSpace_r4e575d_1 : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance parallelDataNormedAlgebra_r4e575d_1 : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
/-- Metric differential identities give the tensor-identity structure. -/
def toMetricGreenData (d : ParallelMetricData g μ) : MetricGreenData g μ where
  flow := d.flow
  weyl := actual_weylCovariantIdentities g d.ricciThree
  continuousWeyl := d.continuousWeyl
  continuousGradient := d.continuousGradient
  continuousHessian := d.continuousHessian
  continuousThird := d.continuousThird
  derivativeWeyl := d.derivativeWeyl
  derivativeGradient := d.derivativeGradient
  derivativeHessian := d.derivativeHessian
  gradientBianchi e r i := actual_plusWeylGradient_bianchi e.frame d.ricciThree r i
  innerCommutator e i k j := actual_plusWeylThird_innerCommutator g d.ricciThree d.flow
    d.derivativeWeyl d.derivativeHessian e i k j
  outerCommutator e i k j := actual_plusWeylThird_outerCommutator e.frame d.ricciThree i k j
  ricci := d.ricci

end ParallelMetricData

end
end PositiveEinsteinFour.Geometry
end


section

/-! The local second-order operator underlying the actual scalar Laplacian.
Its principal coefficient matrix is the smooth positive definite inverse
metric; all lower-order coefficients are the actual Christoffel symbols. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem chartGramMatrix_mul_transpose (g : SmoothMetric M) (c : M)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target) :
    chartGramMatrix g c 1 z * (chartGramMatrix g c 1 z)ᵀ =
      (metricInChart g c z)⁻¹ := by
  let E := chartGramMatrix g c 1 z
  let G := metricInChart g c z
  have hnorm : Eᵀ * G * E = 1 := chartGramMatrix_normalizes g c 1 (by simp) ⟨z, hz⟩
  have hleft : E * (Eᵀ * G) = 1 := mul_eq_one_comm.mp hnorm
  have hG : IsUnit G.det := isUnit_iff_ne_zero.mpr (metricInChart_posDef g c z hz).det_pos.ne'
  calc
    E * Eᵀ = E * Eᵀ * (G * G⁻¹) := by rw [Matrix.mul_nonsing_inv _ hG, mul_one]
    _ = (E * (Eᵀ * G)) * G⁻¹ := by noncomm_ring
    _ = G⁻¹ := by rw [hleft, one_mul]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Uniqueness of the rotation-invariant probability on the actual unit
three-sphere. This identifies the angular measure arising from Euclidean
polar coordinates with the Hausdorff normalization used in the moments. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular MeasureTheory Matrix
open scoped BigOperators

noncomputable section

theorem orientedDirection_mul (P Q : OrientedOrthogonalFour) (q : Directions) :
    orientedDirection (P * Q) q = orientedDirection P (orientedDirection Q q) := by
  apply Subtype.ext
  change Matrix.toEuclideanLin (P.val * Q.val) q.val =
    Matrix.toEuclideanLin P.val (Matrix.toEuclideanLin Q.val q.val)
  change Matrix.toLpLin 2 2 (P.val * Q.val) q.val =
    Matrix.toLpLin 2 2 P.val (Matrix.toLpLin 2 2 Q.val q.val)
  rw [Matrix.toLpLin_mul_same]
  rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual kinetic Hamiltonian has a local flow whose initial-value
Jacobian is one. Both the variational equation and local injectivity are
proved from the vector field, before applying change of variables. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set MeasureTheory
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

/-- A constructed local solution and its first variation. This is output
of the local ODE theorem, not a geometric input. -/
structure KineticLocalFlow (g : SmoothMetric M) (c : M) (p : CotangentCoordinates) where
  radius : ℝ
  radius_pos : 0 < radius
  time : ℝ
  time_pos : 0 < time
  map : CotangentCoordinates × ℝ → CotangentCoordinates
  variation : CotangentCoordinates × ℝ → CotangentCoordinates →L[ℝ] CotangentCoordinates
  continuous_map : ContinuousOn map (Metric.ball p radius ×ˢ Ioo (-time) time)
  continuous_variation : ContinuousOn variation (Metric.ball p radius ×ˢ Ioo (-time) time)
  initial : ∀ q ∈ Metric.ball p radius, map (q, 0) = q
  initial_variation : ∀ q ∈ Metric.ball p radius,
    variation (q, 0) = ContinuousLinearMap.id ℝ CotangentCoordinates
  inside : ∀ q ∈ Metric.ball p radius, ∀ t ∈ Ioo (-time) time,
    (map (q, t)).1 ∈ (chartAt FourSpace c).target
  time_derivative : ∀ q ∈ Metric.ball p radius, ∀ t ∈ Ioo (-time) time,
    HasDerivAt (fun s => map (q, s))
      (cotangentHamiltonianField (kineticHamiltonian g c) (map (q, t))) t
  variation_derivative : ∀ q ∈ Metric.ball p radius, ∀ t ∈ Ioo (-time) time,
    HasDerivAt (fun s => variation (q, s))
      ((fderiv ℝ (cotangentHamiltonianField (kineticHamiltonian g c))
        (map (q, t))).comp (variation (q, t))) t
  joint_derivative : ∀ q ∈ Metric.ball p radius, ∀ t ∈ Ioo (-time) time,
    HasStrictFDerivAt map ((variation (q, t)).coprod
      (ContinuousLinearMap.toSpanSingleton ℝ
        (cotangentHamiltonianField (kineticHamiltonian g c) (map (q, t))))) (q, t)

namespace KineticLocalFlow

variable {g : SmoothMetric M} {c : M} {p : CotangentCoordinates}

theorem initial_derivative (F : KineticLocalFlow g c p)
    (q : CotangentCoordinates) (hq : q ∈ Metric.ball p F.radius)
    (t : ℝ) (ht : t ∈ Ioo (-F.time) F.time) :
    HasFDerivAt (fun x => F.map (x, t)) (F.variation (q, t)) q := by
  have harg : HasFDerivAt (fun x : CotangentCoordinates => (x, t))
      ((ContinuousLinearMap.id ℝ CotangentCoordinates).prod
        (0 : CotangentCoordinates →L[ℝ] ℝ)) q :=
    (hasFDerivAt_id q).prodMk (hasFDerivAt_const t q)
  have h := (F.joint_derivative q hq t ht).hasFDerivAt.comp q
    harg
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | (ext x <;> simp)

end KineticLocalFlow
end
end PositiveEinsteinFour.Geometry
end


section

/-! The opposite Weyl calculus is forced by reflection of the existing
parallel flow. It supplies no additional published tensor identities. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

namespace MetricGreenData

theorem continuousMinusWeyl (d : MetricGreenData g μ) :
    Continuous (fun e : FrameBundle g => minusWeyl g e.base e.frame) := by
  have h := d.continuousWeyl.comp (continuous_frameReflection g)
  simpa only [Function.comp_def, frameReflection, plusWeyl_reflect] using h

theorem continuousMinusGradient (d : MetricGreenData g μ) (i : Fin 4) :
    Continuous (fun e : FrameBundle g => minusWeylGradient g e.base e.frame i) := by
  have h := ((d.continuousGradient i).comp (continuous_frameReflection g)).const_smul
    (orientationSign i)
  have hv (e : FrameBundle g) :
      orientationSign i • plusWeylGradient g (frameReflection e).base (frameReflection e).frame i =
        minusWeylGradient g e.base e.frame i := by
    change orientationSign i • plusWeylGradient g e.base e.frame.reflect i = _
    rw [plusWeylGradient_reflect, smul_smul, ← pow_two, orientationSign_sq, one_smul]
  convert! h using 1
  all_goals try with_reducible_and_instances rfl
  funext e
  exact (hv e).symm

theorem minusWeyl_reflected_flow (d : MetricGreenData g μ)
    (hparallel : ParallelReflection d) (i : Fin 4) (s : ℝ) (e : FrameBundle g) :
    plusWeyl g ((d.flow i).map (orientationSign i * s) (frameReflection e)).base
      ((d.flow i).map (orientationSign i * s) (frameReflection e)).frame =
    minusWeyl g ((d.flow i).map s e).base ((d.flow i).map s e).frame := by
  rw [← hparallel i s e]
  exact plusWeyl_reflect g _ _

theorem minusGradient_reflected_flow (d : MetricGreenData g μ)
    (hparallel : ParallelReflection d) (i : Fin 4) (t : ℝ) (e : FrameBundle g) :
    orientationSign i •
      plusWeylGradient g ((d.flow i).map (orientationSign i * t) (frameReflection e)).base
        ((d.flow i).map (orientationSign i * t) (frameReflection e)).frame i =
    minusWeylGradient g ((d.flow i).map t e).base ((d.flow i).map t e).frame i := by
  rw [← hparallel i t e]
  change orientationSign i • plusWeylGradient g _ ((d.flow i).map t e).frame.reflect i = _
  rw [plusWeylGradient_reflect, smul_smul, ← pow_two, orientationSign_sq, one_smul]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.oppositeParallelDataInstance1
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.oppositeParallelDataInstance2
local instance oppositeParallelDataInstance3_r4e575d_1 : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
theorem derivativeMinusWeyl (d : MetricGreenData g μ) (hparallel : ParallelReflection d)
    (i : Fin 4) (t : ℝ) (e : FrameBundle g) :
    HasDerivAt
      (fun s => minusWeyl g ((d.flow i).map s e).base ((d.flow i).map s e).frame)
      (minusWeylGradient g ((d.flow i).map t e).base ((d.flow i).map t e).frame i) t := by
  have ht : HasDerivAt (fun s : ℝ => orientationSign i * s) (orientationSign i) t := by
    convert! (hasDerivAt_id t).const_mul (orientationSign i) using 1
    all_goals try with_reducible_and_instances rfl
    simp
  have h := (d.derivativeWeyl i (orientationSign i * t) (frameReflection e)).scomp t ht
  change HasDerivAt
    (fun s => plusWeyl g ((d.flow i).map (orientationSign i * s) (frameReflection e)).base
      ((d.flow i).map (orientationSign i * s) (frameReflection e)).frame)
    (orientationSign i •
      plusWeylGradient g ((d.flow i).map (orientationSign i * t) (frameReflection e)).base
        ((d.flow i).map (orientationSign i * t) (frameReflection e)).frame i) t at h
  simp_rw [minusWeyl_reflected_flow d hparallel i] at h
  rw [minusGradient_reflected_flow d hparallel] at h
  exact h

theorem oppositeData (d : MetricGreenData g μ) (hparallel : ParallelReflection d)
    (hRic : RicciThree g) : OppositeWeylData d where
  symmetric e := (actual_weyl_symmetric e.frame).2
  traceFree e := (actual_weyl_traceFree e.frame hRic).2
  continuousWeyl := d.continuousMinusWeyl
  continuousGradient := d.continuousMinusGradient
  derivativeWeyl := d.derivativeMinusWeyl hparallel
  gradientBianchi e r i := actual_minusWeylGradient_bianchi e.frame hRic r i

end MetricGreenData

end
end PositiveEinsteinFour.Geometry
end


section

/-! The normalized coordinate states of the local horizontal ODE are
actual orthonormal frames with their intrinsic tangent-bundle topology. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Bundle
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

abbrev OrthonormalChartState (g : SmoothMetric M) (c : M) :=
  {p : CoordinateFrameSpace // p.1 ∈ (chartAt FourSpace c).target ∧
    p.2ᵀ * metricInChart g c p.1 * p.2 = 1}

def chartFrameStateToBundle (g : SmoothMetric M) (c : M)
    (p : OrthonormalChartState g c) : FrameBundle g :=
  ⟨(chartAt FourSpace c).symm p.val.1,
    chartMatrixFrame g c ⟨p.val.1, p.property.1⟩ p.val.2 p.property.2⟩

theorem frameChartMatrix_apply (g : SmoothMetric M) (c : M)
    (e : FrameBundle g) (he : e.base ∈ (chartAt FourSpace c).source) (a b : Fin 4) :
    frameChartMatrix g c e a b =
      (show FourSpace from mfderiv I4 I4 (chartAt FourSpace c) e.base (e.frame.vector b)) a := by
  rw [mfderiv_chartAt_eq_tangentCoordChange he, tangentCoordChange_def]
  unfold frameChartMatrix
  rw [TangentBundle.trivializationAt_apply]
  simp only [extChartAt, OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm,
    I4, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.id_comp, Function.comp_id, Set.range_id]
  rw [fderivWithin_univ]
  rfl

theorem frameChartMatrix_vector (g : SmoothMetric M) (c : M)
    (e : FrameBundle g) (he : e.base ∈ (chartAt FourSpace c).source) (b : Fin 4) :
    WithLp.toLp 2 (fun a => frameChartMatrix g c e a b) =
      (show FourSpace from mfderiv I4 I4 (chartAt FourSpace c) e.base (e.frame.vector b)) := by
  ext a
  exact frameChartMatrix_apply g c e he a b

omit [IsManifold I4 ∞ M] in
theorem chartTransitionMatrix_mulVec (c d : M) (z : FourSpace)
    (v : Fin 4 → ℝ) :
    WithLp.toLp 2 (chartTransitionMatrix c d z *ᵥ v) =
      fderiv ℝ (chartTransition c d) z (WithLp.toLp 2 v) := by
  rw [← sum_coordinateVector v, map_sum]
  ext a
  simp only [map_smul, WithLp.ofLp_sum, PiLp.smul_apply, smul_eq_mul,
    Finset.sum_apply, Matrix.mulVec, dotProduct, chartTransitionMatrix]
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem frameChartMatrix_change (g : SmoothMetric M) (c d : M)
    (e : FrameBundle g) (hc : e.base ∈ (chartAt FourSpace c).source)
    (hd : e.base ∈ (chartAt FourSpace d).source) :
    chartTransitionMatrix c d (chartAt FourSpace c e.base) * frameChartMatrix g c e =
      frameChartMatrix g d e := by
  have hinv := (chartAt FourSpace c).left_inv hc
  have hJ := chartTransition_fderiv c d (chartAt FourSpace c e.base)
    ((chartAt FourSpace c).map_source hc) (by simpa only [hinv] using hd)
  rw [hinv] at hJ
  have hcomp := (mdifferentiable_chart (I := I4) c).symm_comp_deriv hc
  ext a b
  have heq : WithLp.toLp 2 (fun i =>
      (chartTransitionMatrix c d (chartAt FourSpace c e.base) * frameChartMatrix g c e) i b) =
      WithLp.toLp 2 (fun i => frameChartMatrix g d e i b) := by
    calc
      _ = fderiv ℝ (chartTransition c d) (chartAt FourSpace c e.base)
          (WithLp.toLp 2 (fun i => frameChartMatrix g c e i b)) :=
        chartTransitionMatrix_mulVec c d _ _
      _ = (show FourSpace from mfderiv I4 I4 (chartAt FourSpace d) e.base
          ((mfderiv I4 I4 (chartAt FourSpace c).symm (chartAt FourSpace c e.base))
            (mfderiv I4 I4 (chartAt FourSpace c) e.base (e.frame.vector b)))) := by
        rw [frameChartMatrix_vector g c e hc, hJ]
        rfl
      _ = (show FourSpace from mfderiv I4 I4 (chartAt FourSpace d) e.base (e.frame.vector b)) := by
        exact congrArg (mfderiv I4 I4 (chartAt FourSpace d) e.base)
          (congrArg (fun L => L (e.frame.vector b)) hcomp)
      _ = _ := (frameChartMatrix_vector g d e hd b).symm
  exact congrArg (fun v : FourSpace => v a) heq

theorem chartMatrixFrame_vector (g : SmoothMetric M) (c : M)
    (z : ChartTarget c) (E : Mat4) (hE : Eᵀ * metricInChart g c z * E = 1)
    (i : Fin 4) :
    (chartMatrixFrame g c z E hE).vector i =
      mfderiv I4 I4 (chartAt FourSpace c).symm z
        (WithLp.toLp 2 (fun j => E j i)) := by
  let L : FourSpace →L[ℝ] FourSpace := mfderiv I4 I4 (chartAt FourSpace c).symm z
  change WithLp.toLp 2 (fun j => (chartInverseMatrix c z * E) j i) =
    L (WithLp.toLp 2 (fun j => E j i))
  have hlinear : L (WithLp.toLp 2 (fun j => E j i)) =
      ∑ j, E j i • L (coordinateVector j) := by
    rw [← sum_coordinateVector (fun j => E j i), map_sum]
    apply Finset.sum_congr rfl
    intro j _
    exact map_smul L (E j i) (coordinateVector j)
  rw [hlinear]
  ext j
  simp only [WithLp.ofLp_sum, PiLp.smul_apply, smul_eq_mul,
    Finset.sum_apply, Matrix.mul_apply, chartInverseMatrix, L]
  apply Finset.sum_congr rfl
  intro r _
  exact mul_comm _ _

theorem frameChartMatrix_chartFrameState (g : SmoothMetric M) (c : M)
    (p : OrthonormalChartState g c) :
    frameChartMatrix g c (chartFrameStateToBundle g c p) = p.val.2 := by
  ext a b
  have hsource : (chartFrameStateToBundle g c p).base ∈ (chartAt FourSpace c).source :=
    (chartAt FourSpace c).map_target p.property.1
  rw [frameChartMatrix_apply g c _ hsource]
  change (show FourSpace from mfderiv I4 I4 (chartAt FourSpace c) ((chartAt FourSpace c).symm p.val.1)
    ((chartMatrixFrame g c ⟨p.val.1, p.property.1⟩ p.val.2 p.property.2).vector b)) a = _
  rw [chartMatrixFrame_vector]
  have hi := (mdifferentiable_chart (I := I4) c).comp_symm_deriv p.property.1
  have hv := congrArg (fun L : FourSpace →L[ℝ] FourSpace =>
    L (WithLp.toLp 2 (fun j => p.val.2 j b))) hi
  exact congrArg (fun v : FourSpace => v a) hv

theorem chartFrameState_coordinate (g : SmoothMetric M) (c : M)
    (p : OrthonormalChartState g c) :
    chartAt FourSpace c (chartFrameStateToBundle g c p).base = p.val.1 :=
  (chartAt FourSpace c).right_inv p.property.1

theorem continuous_chartFrameStateToBundle (g : SmoothMetric M) (c : M) :
    Continuous (chartFrameStateToBundle g c) := by
  have hphi : ContMDiffOn I4 I4 ∞ (chartAt FourSpace c).symm
      (chartAt FourSpace c).target := contMDiffOn_chart_symm
  have ht := (hphi.contMDiffOn_tangentMapWithin (m := ∞) (by simp)
    (chartAt FourSpace c).open_target.uniqueMDiffOn).continuousOn
  have hv (i : Fin 4) : Continuous (fun p : OrthonormalChartState g c =>
      (⟨p.val.1, WithLp.toLp 2 (fun j => p.val.2 j i)⟩ :
        TangentBundle I4 FourSpace)) := by
    have hw : Continuous (fun p : OrthonormalChartState g c =>
        WithLp.toLp 2 (fun j => p.val.2 j i)) :=
      (PiLp.continuous_toLp 2 _).comp (continuous_pi (fun j =>
        (continuous_apply i).comp ((continuous_apply j).comp
          (continuous_snd.comp continuous_subtype_val))))
    exact (tangentBundleModelSpaceHomeomorph I4).symm.continuous.comp
      ((continuous_fst.comp continuous_subtype_val).prodMk hw)
  have hvec (i : Fin 4) : Continuous (fun p : OrthonormalChartState g c =>
      (⟨(chartFrameStateToBundle g c p).base,
        (chartFrameStateToBundle g c p).frame.vector i⟩ : TangentBundle I4 M)) := by
    have hcomp := ht.comp_continuous (hv i) (fun p => p.property.1)
    apply hcomp.congr
    intro p
    change (⟨(chartAt FourSpace c).symm p.val.1,
      mfderivWithin I4 I4 (chartAt FourSpace c).symm
        (chartAt FourSpace c).target p.val.1
        (WithLp.toLp 2 (fun j => p.val.2 j i))⟩ : TangentBundle I4 M) = _
    rw [mfderivWithin_of_isOpen (chartAt FourSpace c).open_target p.property.1]
    exact congrArg (fun v : TangentSpace I4 ((chartAt FourSpace c).symm p.val.1) =>
      (⟨(chartAt FourSpace c).symm p.val.1, v⟩ : TangentBundle I4 M))
      (chartMatrixFrame_vector g c ⟨p.val.1, p.property.1⟩ p.val.2 p.property.2 i).symm
  apply continuous_induced_rng.mpr
  have hb : Continuous (fun p : OrthonormalChartState g c =>
      (chartAt FourSpace c).symm p.val.1) :=
    (chartAt FourSpace c).continuousOn_symm.comp_continuous
      (continuous_fst.comp continuous_subtype_val) (fun p => p.property.1)
  exact hb.prodMk (continuous_pi hvec)

theorem frameChartMatrix_normalizes (g : SmoothMetric M) (c : M)
    (e : FrameBundle g) (he : e.base ∈ (chartAt FourSpace c).source) :
    (frameChartMatrix g c e)ᵀ * metricInChart g c (chartAt FourSpace c e.base) *
      frameChartMatrix g c e = 1 := by
  have hcenter := (chartAt FourSpace e.base).left_inv (mem_chart_source FourSpace e.base)
  have hm := metricInChart_transition g e.base c (chartAt FourSpace e.base e.base)
    (mem_chart_target FourSpace e.base) (by simpa only [hcenter] using he)
  have ht : chartTransition e.base c (chartAt FourSpace e.base e.base) =
      chartAt FourSpace c e.base := by
    rw [chartTransition, hcenter]
  rw [ht] at hm
  simp only [frameChartMatrix_eq, Matrix.transpose_mul]
  calc
    _ = e.frame.matrixᵀ *
        ((chartTransitionMatrix e.base c (chartAt FourSpace e.base e.base))ᵀ *
          (metricInChart g c (chartAt FourSpace c e.base) *
            chartTransitionMatrix e.base c (chartAt FourSpace e.base e.base))) *
        e.frame.matrix := by simp only [Matrix.mul_assoc]
    _ = e.frame.matrixᵀ * chartMetric g e.base * e.frame.matrix := by rw [← hm]; rfl
    _ = 1 := e.frame.orthonormal

end
end PositiveEinsteinFour.Geometry
end


section

/-! A common time interval and continuous dependence for nearby initial
states of the actual parallel-frame coordinate ODE. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Metric
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem exists_continuous_local_parallelFrame_flow (g : SmoothMetric M) (c : M)
    (k : Fin 4) (p : CoordinateFrameSpace)
    (hp : p.1 ∈ (chartAt FourSpace c).target) :
    ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ), ∃ α : CoordinateFrameSpace × ℝ → CoordinateFrameSpace,
      ContinuousOn α (closedBall p r ×ˢ Ioo (-ε) ε) ∧
      ∀ q ∈ closedBall p r, α (q, 0) = q ∧
        ∀ t ∈ Ioo (-ε) ε,
          (α (q, t)).1 ∈ (chartAt FourSpace c).target ∧
          HasDerivAt (fun s => α (q, s))
            (parallelFrameVectorField g c k (α (q, t))) t ∧
          (α (q, t)).2ᵀ * metricInChart g c (α (q, t)).1 * (α (q, t)).2 =
            q.2ᵀ * metricInChart g c q.1 * q.2 := by
  have hf : ContDiffAt ℝ 1 (parallelFrameVectorField g c k) p :=
    (parallelFrameVectorField_contDiffAt g c k p hp).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  obtain ⟨ε₀, hε₀, a, r₀, L, K, hr₀, hpl⟩ := IsPicardLindelof.of_contDiffAt_one hf
  obtain ⟨α, hα, hcont⟩ :=
    (hpl 0).exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn
  have hαp : α (p, 0) = p := (hα p (mem_closedBall_self (by positivity))).1
  have hr₀' : 0 < (r₀ : ℝ) := hr₀
  have hdomain : closedBall p (r₀ : ℝ) ×ˢ Icc (0 - ε₀) (0 + ε₀) ∈ 𝓝 (p, (0 : ℝ)) :=
    by
      rw [nhds_prod_eq]
      exact Filter.prod_mem_prod (closedBall_mem_nhds p hr₀')
        (Icc_mem_nhds (by linarith) (by linarith))
  have hnear : ∀ᶠ qt in 𝓝 (p, (0 : ℝ)), (α qt).1 ∈ (chartAt FourSpace c).target :=
    (hcont.continuousAt hdomain).fst.eventually
      ((chartAt FourSpace c).open_target.mem_nhds (by simpa only [hαp] using hp))
  obtain ⟨δ, hδ, hδnear⟩ := Metric.eventually_nhds_iff.mp hnear
  let r : ℝ := min (r₀ : ℝ) (δ / 2)
  let ε : ℝ := min ε₀ (δ / 2)
  have hr : 0 < r := lt_min hr₀' (half_pos hδ)
  have hε : 0 < ε := lt_min hε₀ (half_pos hδ)
  have hsub (q : CoordinateFrameSpace) (hq : q ∈ closedBall p r) :
      q ∈ closedBall p (r₀ : ℝ) := closedBall_subset_closedBall (min_le_left _ _) hq
  have htime {t : ℝ} (ht : t ∈ Ioo (-ε) ε) : t ∈ Ioo (0 - ε₀) (0 + ε₀) := by
    have hle : ε ≤ ε₀ := min_le_left _ _
    constructor <;> linarith [ht.1, ht.2]
  have hinside {q : CoordinateFrameSpace} (hq : q ∈ closedBall p r)
      {t : ℝ} (ht : t ∈ Ioo (-ε) ε) :
      (α (q, t)).1 ∈ (chartAt FourSpace c).target := by
    apply hδnear
    rw [Prod.dist_eq, max_lt_iff]
    constructor
    · have hqr : dist q p ≤ r := hq
      have hrd : r ≤ δ / 2 := min_le_right _ _
      linarith
    · rw [Real.dist_eq, sub_zero, abs_lt]
      have hεd : ε ≤ δ / 2 := min_le_right _ _
      constructor <;> linarith [ht.1, ht.2]
  refine ⟨r, hr, ε, hε, α, hcont.mono ?_, fun q hq => ⟨(hα q (hsub q hq)).1, ?_⟩⟩
  · rintro ⟨q, t⟩ ⟨hq, ht⟩
    exact ⟨hsub q hq, Ioo_subset_Icc_self (htime ht)⟩
  · intro t ht
    have hd {s : ℝ} (hs : s ∈ Ioo (-ε) ε) :
        HasDerivAt (fun u => α (q, u))
          (parallelFrameVectorField g c k (α (q, s))) s :=
      ((hα q (hsub q hq)).2 s (Ioo_subset_Icc_self (htime hs))).hasDerivAt
        (Icc_mem_nhds (htime hs).1 (htime hs).2)
    refine ⟨hinside hq ht, hd ht, ?_⟩
    have hz : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, hε⟩
    have heq := parallelGram_eq_on_interval g c
      (fun s => (α (q, s)).1) (fun s => (α (q, s)).2) k (-ε) ε t 0 ht hz
      (fun s hs => hinside hq hs) (fun s hs => (hd hs).fst)
      (fun s hs i j => hasDerivAt_pi.mp (hasDerivAt_pi.mp (hd hs).snd i) j)
    simpa only [(hα q (hsub q hq)).1] using heq

end
end PositiveEinsteinFour.Geometry
end


section

/-! Uniqueness of the actual horizontal coordinate ODE, locally and on
connected intervals. No a priori uniqueness premise is introduced. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem parallelFrame_solution_unique_near (g : SmoothMetric M) (c : M)
    (k : Fin 4) (α β : ℝ → CoordinateFrameSpace) (t : ℝ)
    (hz : (α t).1 ∈ (chartAt FourSpace c).target)
    (hα : ∀ᶠ s in 𝓝 t, HasDerivAt α (parallelFrameVectorField g c k (α s)) s)
    (hβ : ∀ᶠ s in 𝓝 t, HasDerivAt β (parallelFrameVectorField g c k (β s)) s)
    (heq : α t = β t) : α =ᶠ[𝓝 t] β := by
  have hf : ContDiffAt ℝ 1 (parallelFrameVectorField g c k) (α t) :=
    (parallelFrameVectorField_contDiffAt g c k (α t) hz).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  obtain ⟨K, U, hU, hLip⟩ := hf.exists_lipschitzOnWith
  have haU : ∀ᶠ s in 𝓝 t, α s ∈ U := hα.self_of_nhds.continuousAt.preimage_mem_nhds hU
  have hbU : ∀ᶠ s in 𝓝 t, β s ∈ U :=
    hβ.self_of_nhds.continuousAt.preimage_mem_nhds (by simpa only [← heq] using hU)
  exact ODE_solution_unique_of_eventually
    (Filter.Eventually.of_forall fun _ => hLip) (hα.and haU) (hβ.and hbU) heq

end
end PositiveEinsteinFour.Geometry
end


section

/-! The angular measure in the actual four-dimensional Euclidean polar
decomposition, identified with the spherical measure used by the curvature
averages. No surface-area formula is needed for this identification. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular MeasureTheory MeasureTheory.Measure Set Metric
open scoped Pointwise

noncomputable section

def sphereToDirection : EuclideanUnitSphere ≃ᵢ Directions where
  toFun q := ⟨q.val, by simpa only [mem_sphere, dist_zero_right] using q.property⟩
  invFun q := ⟨q.val, by simpa only [mem_sphere, dist_zero_right] using q.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  isometry_toFun := fun _ _ => rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! The Hessian symmetry and covector commutator for actual smooth scalar
functions, obtained from the same Levi-Civita tensor calculation as the
Weyl identities. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {a : M → ℝ}

theorem scalarCoordinates_contDiffAt (ha : ContMDiff I4 𝓘(ℝ, ℝ) ∞ a)
    (c : M) (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target)
    (v : Fin 0 → Fin 4) :
    ContDiffAt ℝ ∞ (fun w => scalarCoordinates a c w v) z := by
  exact (ha.contMDiffAt.comp z
    (contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas c) hz)).contDiffAt

theorem actual_scalarHessian_symmetric (ha : ContMDiff I4 𝓘(ℝ, ℝ) ∞ a)
    (e : FrameBundle g) (i j : Fin 4) :
    scalarHessian g a e i j = scalarHessian g a e j i := by
  let z : FourSpace := chartAt FourSpace e.base e.base
  have hz : z ∈ (chartAt FourSpace e.base).target :=
    (chartAt FourSpace e.base).map_source (mem_chart_source FourSpace e.base)
  have hdet := (metricInChart_posDef g e.base z hz).det_pos.ne'
  have h := framed_tensor_commutator e.frame.matrix
    (isUnit_iff_ne_zero.mpr e.frame.det_ne_zero)
    (fun p q => coordinateCurvatureMatrix g e.base p q z)
    (scalarCoordinates a e.base z)
    (covariantDerivative g e.base (covariantDerivative g e.base (scalarCoordinates a e.base)) z)
    (covariantDerivative_commutator g e.base (scalarCoordinates a e.base) z hz hdet
      (scalarCoordinates_contDiffAt ha e.base z hz)) i j ![]
  simp only [tensorSlotAction, Fin.sum_univ_zero, neg_zero] at h
  exact sub_eq_zero.mp h

theorem actual_scalarThird_commutator (ha : ContMDiff I4 𝓘(ℝ, ℝ) ∞ a)
    (e : FrameBundle g) (i j k : Fin 4) :
    scalarThird g a e i j k - scalarThird g a e j i k =
      ∑ l, frameCurvature g e.base e.frame i j l k * scalarGradient g a e l := by
  let z : FourSpace := chartAt FourSpace e.base e.base
  let T := covariantDerivative g e.base (scalarCoordinates a e.base)
  have hz : z ∈ (chartAt FourSpace e.base).target :=
    (chartAt FourSpace e.base).map_source (mem_chart_source FourSpace e.base)
  have hdet := (metricInChart_posDef g e.base z hz).det_pos.ne'
  have hT : ∀ v, ContDiffAt ℝ ∞ (fun w => T w v) z :=
    covariantDerivative_contDiffAt g e.base z hz hdet (scalarCoordinates a e.base)
      (scalarCoordinates_contDiffAt ha e.base z hz)
  have h := framed_tensor_commutator e.frame.matrix
    (isUnit_iff_ne_zero.mpr e.frame.det_ne_zero)
    (fun p q => coordinateCurvatureMatrix g e.base p q z)
    (T z) (covariantDerivative g e.base (covariantDerivative g e.base T) z)
    (covariantDerivative_commutator g e.base T z hz hdet hT) i j ![k]
  rw [frame_curvatureEndomorphism] at h
  have he (l : Fin 4) : Function.update (![k] : Fin 1 → Fin 4) 0 l = ![l] := by
    funext t
    fin_cases t
    simp
  change scalarThird g a e i j k - scalarThird g a e j i k =
    -(∑ s : Fin 1, ∑ l, frameCurvature g e.base e.frame i j (![k] s) l *
      frameTensor e.frame.matrix (T z) (Function.update ![k] s l)) at h
  rw [Fin.sum_univ_one] at h
  simp only [Matrix.cons_val_zero, he] at h
  change scalarThird g a e i j k - scalarThird g a e j i k =
    -(∑ l, frameCurvature g e.base e.frame i j k l * scalarGradient g a e l) at h
  rw [h, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro l _
  rw [frameCurvature_last_skew e.frame i j k l]
  ring

/-- Only differentiation along the chosen parallel flow remains input.
Regularity, symmetry and the Ricci commutator follow from the metric. -/
structure ScalarParallelData {μ : MeasureTheory.Measure (FrameBundle g)}
    (d : MetricGreenData g μ) (a : M → ℝ) where
  derivativeValue : ∀ i t e, HasDerivAt (fun s => a ((d.flow i).map s e).base)
    (scalarGradient g a ((d.flow i).map t e) i) t
  derivativeGradient : ∀ i j t e, HasDerivAt
    (fun s => scalarGradient g a ((d.flow i).map s e) j)
    (scalarHessian g a ((d.flow i).map t e) i j) t
  derivativeHessian : ∀ i j k t e, HasDerivAt
    (fun s => scalarHessian g a ((d.flow i).map s e) j k)
    (scalarThird g a ((d.flow i).map t e) i j k) t

theorem ScalarParallelData.toCovariantData {μ : MeasureTheory.Measure (FrameBundle g)}
    {d : MetricGreenData g μ} (s : ScalarParallelData d a)
    (ha : ContMDiff I4 𝓘(ℝ, ℝ) ∞ a) : ScalarCovariantData d a where
  continuousValue := actual_scalarValue_continuous g ha
  continuousGradient := actual_scalarGradient_continuous g ha
  continuousHessian := actual_scalarHessian_continuous g ha
  continuousThird := actual_scalarThird_continuous g ha
  derivativeValue := s.derivativeValue
  derivativeGradient := s.derivativeGradient
  derivativeHessian := s.derivativeHessian
  hessianSymmetric := actual_scalarHessian_symmetric ha
  commutator := actual_scalarThird_commutator ha

def ParallelScalarCalculusInput {μ : MeasureTheory.Measure (FrameBundle g)}
    (d : MetricGreenData g μ) : Prop :=
  ∀ a : M → ℝ, ContMDiff I4 𝓘(ℝ, ℝ) ∞ a → Nonempty (ScalarParallelData d a)

theorem ParallelScalarCalculusInput.toPetersenInput
    {μ : MeasureTheory.Measure (FrameBundle g)} {d : MetricGreenData g μ}
    (h : ParallelScalarCalculusInput d) : PetersenScalarCalculusInput d := by
  intro a ha
  obtain ⟨s⟩ := h a ha
  exact ⟨s.toCovariantData ha⟩

/-- Primitive parallel-frame equations supply the full scalar calculus. -/
theorem ParallelMetricData.scalarCalculus {μ : MeasureTheory.Measure (FrameBundle g)}
    (d : ParallelMetricData g μ) : ParallelScalarCalculusInput d.toMetricGreenData := by
  intro a ha
  refine ⟨{ derivativeValue := ?_, derivativeGradient := ?_, derivativeHessian := ?_ }⟩
  · intro i t e
    exact actual_scalarValue_parallel_derivative g ha _ t i
      (d.curve_continuous i e).continuousAt (d.parallelCurve i t e)
  · intro i j t e
    exact actual_scalarGradient_parallel_derivative g ha _ t i j
      (d.curve_continuous i e).continuousAt (d.parallelCurve i t e)
  · intro i j k t e
    exact actual_scalarHessian_parallel_derivative g ha _ t i j k
      (d.curve_continuous i e).continuousAt (d.parallelCurve i t e)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Coordinate compatibility of the actual two-form covariant derivative. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

theorem chartInverseMatrix_transition (c d : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target)
    (hx : (chartAt FourSpace c).symm z ∈ (chartAt FourSpace d).source) :
    chartInverseMatrix d (chartTransition c d z) * chartTransitionMatrix c d z =
      chartInverseMatrix c z := by
  let B : FourSpace →L[ℝ] FourSpace :=
    mfderiv I4 I4 (chartAt FourSpace d).symm (chartTransition c d z)
  let A : FourSpace →L[ℝ] FourSpace :=
    mfderiv I4 I4 (chartAt FourSpace d) ((chartAt FourSpace c).symm z)
  let C : FourSpace →L[ℝ] FourSpace := mfderiv I4 I4 (chartAt FourSpace c).symm z
  have hBA : B.comp A = ContinuousLinearMap.id ℝ FourSpace :=
    (mdifferentiable_chart (I := I4) d).symm_comp_deriv hx
  have hF : fderiv ℝ (chartTransition c d) z = A.comp C :=
    chartTransition_fderiv c d z hz hx
  have hBC : B.comp (fderiv ℝ (chartTransition c d) z) = C := by
    rw [hF, ← ContinuousLinearMap.comp_assoc, hBA, ContinuousLinearMap.id_comp]
  ext i j
  have hv := congrArg (fun L : FourSpace →L[ℝ] FourSpace => L (coordinateVector j) i) hBC
  have hj : fderiv ℝ (chartTransition c d) z (coordinateVector j) =
      ∑ k, chartTransitionMatrix c d z k j • coordinateVector k :=
    (sum_coordinateVector _).symm
  change B (fderiv ℝ (chartTransition c d) z (coordinateVector j)) i =
    C (coordinateVector j) i at hv
  rw [hj, map_sum] at hv
  simp only [map_smul, WithLp.ofLp_sum, PiLp.smul_apply, smul_eq_mul, Finset.sum_apply] at hv
  change (∑ k, B (coordinateVector k) i * chartTransitionMatrix c d z k j) =
    C (coordinateVector j) i
  simpa only [mul_comm] using hv

end
end PositiveEinsteinFour.Geometry
end


section

/-! C1 regularity of each constructed local kinetic flow follows from its
continuous first variation, without any additional flow regularity input. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem KineticLocalFlow.contDiffAt_slice {g : SmoothMetric M} {c : M}
    {p : CotangentCoordinates} (F : KineticLocalFlow g c p)
    (q : CotangentCoordinates) (hq : q ∈ Metric.ball p F.radius)
    (t : ℝ) (ht : t ∈ Ioo (-F.time) F.time) :
    ContDiffAt ℝ 1 (fun z => F.map (z, t)) q := by
  apply contDiffAt_one_iff.mpr
  refine ⟨fun z => F.variation (z, t), Metric.ball p F.radius,
    Metric.isOpen_ball.mem_nhds hq, ?_, ?_⟩
  · exact F.continuous_variation.comp
      (continuous_id.prodMk continuous_const).continuousOn (fun z hz => ⟨hz, ht⟩)
  · exact fun z hz => F.initial_derivative z hz t ht

end
end PositiveEinsteinFour.Geometry
end


section

/-! The normal curvature field and its derivative are linear contractions
of the two actual Weyl blocks along the first parallel frame direction. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Angular
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : MeasureTheory.Measure (FrameBundle g)}

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.parallelCurvatureCalculusInstance1
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.parallelCurvatureCalculusInstance2
theorem frameCurvatureField_eq_normalDeviation (e : FrameBundle g) (hRic : RicciThree g) :
    frameCurvatureField g e = normalDeviation (plusWeyl g e.base e.frame)
      (minusWeyl g e.base e.frame) firstDirection :=
  normalCurvatureDeviation_eq_of_decomposition g e.base e.frame
    (actual_einstein_decomposition e.frame hRic) firstDirection

namespace MetricGreenData

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.parallelCurvatureCalculusInstance1
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.parallelCurvatureCalculusInstance2
theorem continuousCurvatureField (d : MetricGreenData g μ) (o : OppositeWeylData d)
    (hRic : RicciThree g) : Continuous (frameCurvatureField g) := by
  have h := continuous_normalDeviation_comp d.continuousWeyl o.continuousWeyl firstDirection
  have hf : frameCurvatureField g = fun e => normalDeviation
      (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame) firstDirection :=
    funext (fun e => frameCurvatureField_eq_normalDeviation e hRic)
  rw [hf]
  exact h

theorem continuousCurvatureDerivative (d : MetricGreenData g μ) (o : OppositeWeylData d) :
    Continuous (frameCurvatureDerivative g) := by
  have h := continuous_normalDeviation_comp (d.continuousGradient 0)
    (o.continuousGradient 0) firstDirection
  have hf : frameCurvatureDerivative g = fun e => normalDeviation
      (plusWeylGradient g e.base e.frame 0)
      (minusWeylGradient g e.base e.frame 0) firstDirection :=
    funext (fun e => frameCurvatureDerivative_eq g e)
  rw [hf]
  exact h

theorem derivativeCurvatureField (d : MetricGreenData g μ) (o : OppositeWeylData d)
    (hRic : RicciThree g) (t : ℝ) (e : FrameBundle g) :
    HasDerivAt (fun s => frameCurvatureField g ((d.flow 0).map s e))
      (frameCurvatureDerivative g ((d.flow 0).map t e)) t := by
  have h := hasDerivAt_normalDeviation (d.derivativeWeyl 0 t e)
    (o.derivativeWeyl 0 t e) firstDirection
  have hf : (fun s => frameCurvatureField g ((d.flow 0).map s e)) =
      fun s => normalDeviation (plusWeyl g ((d.flow 0).map s e).base ((d.flow 0).map s e).frame)
        (minusWeyl g ((d.flow 0).map s e).base ((d.flow 0).map s e).frame) firstDirection :=
    funext (fun s => frameCurvatureField_eq_normalDeviation _ hRic)
  rw [hf, frameCurvatureDerivative_eq]
  exact h

end MetricGreenData

end
end PositiveEinsteinFour.Geometry
end


section

/-! The primitive horizontal ODE is invariant under actual coordinate
changes. This uses the proved Christoffel transformation, before any tensor
specialization. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem weighted_chart_connection (g : SmoothMetric M) (c d : M)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target)
    (hd : (chartAt FourSpace c).symm z ∈ (chartAt FourSpace d).source)
    (E : Mat4) (k : Fin 4) :
    chartTransitionMatrix c d z * parallelFrameConnection g c k (z, E) =
      (∑ r, E r k • matrixPartial (chartTransitionMatrix c d) r z) +
      parallelFrameConnection g d k
        (chartTransition c d z, chartTransitionMatrix c d z * E) *
          chartTransitionMatrix c d z := by
  calc
    _ = ∑ r, E r k • (chartTransitionMatrix c d z * connectionMatrix g c r z) := by
      simp only [parallelFrameConnection, Matrix.mul_sum, Matrix.mul_smul]
    _ = ∑ r, E r k • (matrixPartial (chartTransitionMatrix c d) r z +
        weightedConnection (chartTransitionMatrix c d z)
          (fun a => connectionMatrix g d a (chartTransition c d z)) r *
            chartTransitionMatrix c d z) := by
      apply Finset.sum_congr rfl
      intro r _
      rw [chart_connection_intertwining g c d z hz hd r]
      rfl
    _ = _ := by
      simp only [smul_add, Finset.sum_add_distrib]
      congr 1
      calc
        _ = (∑ r, E r k • weightedConnection (chartTransitionMatrix c d z)
            (fun a => connectionMatrix g d a (chartTransition c d z)) r) *
              chartTransitionMatrix c d z := by
          rw [Matrix.sum_mul]
          apply Finset.sum_congr rfl
          intro r _
          exact (Matrix.smul_mul _ _ _).symm
        _ = _ := by rw [weightedConnection_frame]; rfl

theorem hasDerivAt_changedChart_velocity (c d : M)
    (x : ℝ → FourSpace) (E : ℝ → Mat4) (t : ℝ) (k : Fin 4)
    (hz : x t ∈ (chartAt FourSpace c).target)
    (hd : (chartAt FourSpace c).symm (x t) ∈ (chartAt FourSpace d).source)
    (hx : HasDerivAt x (WithLp.toLp 2 (fun r => E t r k)) t) :
    HasDerivAt (fun s => chartTransition c d (x s))
      (WithLp.toLp 2 (fun r => (chartTransitionMatrix c d (x t) * E t) r k)) t := by
  have hF := (chartTransition_contDiffAt c d (x t) hz hd).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have h := hF.hasFDerivAt.comp_hasDerivAt t hx
  have hrate : (fderiv ℝ (chartTransition c d) (x t))
      (WithLp.toLp 2 (fun r => E t r k)) =
      WithLp.toLp 2 (fun r => (chartTransitionMatrix c d (x t) * E t) r k) :=
    (chartTransitionMatrix_mulVec c d (x t) (fun r => E t r k)).symm
  simpa only [Function.comp_def, hrate] using h

theorem hasDerivAt_changedChart_parallel (g : SmoothMetric M) (c d : M)
    (x : ℝ → FourSpace) (E : ℝ → Mat4) (t : ℝ) (k : Fin 4)
    (hz : x t ∈ (chartAt FourSpace c).target)
    (hd : (chartAt FourSpace c).symm (x t) ∈ (chartAt FourSpace d).source)
    (hx : HasDerivAt x (WithLp.toLp 2 (fun r => E t r k)) t)
    (hE : ∀ i j, HasDerivAt (fun s => E s i j)
      (-(parallelFrameConnection g c k (x t, E t) * E t) i j) t)
    (i j : Fin 4) :
    HasDerivAt (fun s => (chartTransitionMatrix c d (x s) * E s) i j)
      (-(parallelFrameConnection g d k
        (chartTransition c d (x t), chartTransitionMatrix c d (x t) * E t) *
          (chartTransitionMatrix c d (x t) * E t)) i j) t := by
  let J := chartTransitionMatrix c d
  let D : Mat4 := ∑ r, E t r k • matrixPartial J r (x t)
  let U : Mat4 := parallelFrameConnection g c k (x t, E t)
  let V : Mat4 := parallelFrameConnection g d k (chartTransition c d (x t), J (x t) * E t)
  have hJ (a b : Fin 4) : HasDerivAt (fun s => J (x s) a b) (D a b) t := by
    have h := hasDerivAt_coordinate_comp hx
      ((chartTransitionMatrix_contDiffAt c d (x t) hz hd a b).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    simpa only [D, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, matrixPartial] using h
  have hp := HasDerivAt.fun_sum (fun a (_ : a ∈ Finset.univ) =>
    (hJ i a).mul (hE a j))
  have hp' : HasDerivAt (fun s => (J (x s) * E s) i j)
      ((D * E t + J (x t) * (-(U * E t))) i j) t := by
    simpa only [U, Matrix.mul_apply, Matrix.add_apply, Matrix.neg_apply,
      Finset.sum_add_distrib, Pi.mul_apply] using hp
  have hc : J (x t) * U = D + V * J (x t) :=
    weighted_chart_connection g c d (x t) hz hd (E t) k
  have hD : D = J (x t) * U - V * J (x t) := (eq_sub_iff_add_eq).mpr hc.symm
  have hrate : D * E t + J (x t) * (-(U * E t)) = -(V * (J (x t) * E t)) := by
    rw [hD]
    noncomm_ring
  rw [hrate] at hp'
  exact hp'

/-- A local solution written in any fixed chart satisfies the centered
primitive equations used by all actual Weyl and scalar derivative theorems. -/
theorem parallelFrameCurveAt_of_fixedChart (g : SmoothMetric M) (c : M)
    (γ : ℝ → FrameBundle g) (t : ℝ) (k : Fin 4)
    (hγ : ContinuousAt γ t) (hc : (γ t).base ∈ (chartAt FourSpace c).source)
    (hx : HasDerivAt (fun s => chartAt FourSpace c (γ s).base)
      (WithLp.toLp 2 (fun r => frameChartMatrix g c (γ t) r k)) t)
    (hE : ∀ i j, HasDerivAt (fun s => frameChartMatrix g c (γ s) i j)
      (-(parallelFrameConnection g c k
        (chartAt FourSpace c (γ t).base, frameChartMatrix g c (γ t)) *
          frameChartMatrix g c (γ t)) i j) t) :
    ParallelFrameCurveAt g γ k t := by
  let d := (γ t).base
  let x (s : ℝ) : FourSpace := chartAt FourSpace c (γ s).base
  let E (s : ℝ) : Mat4 := frameChartMatrix g c (γ s)
  have hd : (γ t).base ∈ (chartAt FourSpace d).source := mem_chart_source FourSpace d
  have hz : x t ∈ (chartAt FourSpace c).target := (chartAt FourSpace c).map_source hc
  have hinv : (chartAt FourSpace c).symm (x t) = (γ t).base :=
    (chartAt FourSpace c).left_inv hc
  have htarget : (chartAt FourSpace c).symm (x t) ∈ (chartAt FourSpace d).source :=
    by rw [hinv]; exact hd
  have hchange : chartTransitionMatrix c d (x t) * E t = frameChartMatrix g d (γ t) :=
    frameChartMatrix_change g c d (γ t) hc hd
  have hvalue : chartTransition c d (x t) = chartAt FourSpace d (γ t).base := by
    change chartAt FourSpace d ((chartAt FourSpace c).symm (x t)) = _
    rw [hinv]
  have hnear : ∀ᶠ s in 𝓝 t,
      (γ s).base ∈ (chartAt FourSpace c).source ∧
      (γ s).base ∈ (chartAt FourSpace d).source :=
    ((continuous_frameBase g).continuousAt.comp hγ).eventually
      (((chartAt FourSpace c).open_source.inter (chartAt FourSpace d).open_source).mem_nhds
        ⟨hc, hd⟩)
  have hy : (fun s => chartAt FourSpace d (γ s).base) =ᶠ[𝓝 t]
      (fun s => chartTransition c d (x s)) := by
    filter_upwards [hnear] with s hs
    change chartAt FourSpace d (γ s).base =
      chartAt FourSpace d ((chartAt FourSpace c).symm (chartAt FourSpace c (γ s).base))
    rw [(chartAt FourSpace c).left_inv hs.1]
  have hF : (fun s => frameChartMatrix g d (γ s)) =ᶠ[𝓝 t]
      (fun s => chartTransitionMatrix c d (x s) * E s) := by
    filter_upwards [hnear] with s hs
    exact (frameChartMatrix_change g c d (γ s) hs.1 hs.2).symm
  constructor
  · have h := hasDerivAt_changedChart_velocity c d x E t k hz htarget hx
    rw [hchange] at h
    exact h.congr_of_eventuallyEq hy
  · intro i j
    have h := hasDerivAt_changedChart_parallel g c d x E t k hz htarget hx hE i j
    rw [hchange, hvalue] at h
    exact h.congr_of_eventuallyEq (hF.mono fun s hs => congrFun (congrFun hs i) j)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The continuous frame-bundle realization of an actual smooth two-form. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem chartInverseMatrix_center (c : M) :
    chartInverseMatrix c (chartAt FourSpace c c) = 1 := by
  have hd : mfderiv I4 I4 (chartAt FourSpace c).symm (chartAt FourSpace c c) =
      ContinuousLinearMap.id ℝ FourSpace := by
    simpa [I4, extChartAt_coe_symm, extChartAt_coe, mfderivWithin_univ] using!
      (mfderivWithin_range_extChartAt_symm (I := I4) (x := c))
  ext i j
  change (show FourSpace from mfderiv I4 I4 (chartAt FourSpace c).symm
    (chartAt FourSpace c c) (coordinateVector j)) i = _
  rw [hd]
  change (coordinateVector j) i = (1 : Mat4) i j
  simp [coordinateVector, Matrix.one_apply]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The Hilbert completion of actual smooth two-form sections with their
intrinsic L2 pairing. The inclusion of pointwise smooth sections is an
injective linear isometry with dense range. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

/- The L2 topology of the completion differs from the pointwise topology
on the smooth function submodule. -/
def SmoothL2TwoForm (o : FrameOrientation g) : Type _ := ↥(smoothTwoForms o)
  deriving AddCommGroup, Module ℝ

instance instCoeSmoothL2TwoFormSubtypeForallTwoFormFourMemSubmoduleRealSmoothTwoForms : Coe (SmoothL2TwoForm o) (smoothTwoForms o) := ⟨id⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! The reconstruction direction of polar volume. It turns the spherical
probability and cubic radial density into actual Euclidean fiber volume,
including the null origin. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal

noncomputable section

def euclideanPolarHomeomorph : ({0}ᶜ : Set FourSpace) ≃ₜ
    Directions × Ioi (0 : ℝ) :=
  (homeomorphUnitSphereProd FourSpace).trans
    (sphereToDirection.toHomeomorph.prodCongr (Homeomorph.refl _))

def euclideanPolarReconstruction (p : Directions × Ioi (0 : ℝ)) : FourSpace :=
  p.2.val • p.1.val

theorem euclideanPolarHomeomorph_symm_coe (p : Directions × Ioi (0 : ℝ)) :
    (euclideanPolarHomeomorph.symm p).val = euclideanPolarReconstruction p := rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! Transfer the derived full Weyl derivative bound through the published
frame disintegration. No integrated Weyl equation is assumed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory Angular
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

theorem BrinKarcherAveraging.integral_of_base_value (hμ : BrinKarcherAveraging g μ)
    (h : FollandMoments) (F : FrameBundle g → ℝ) (A : M → ℝ)
    (hi : Integrable F μ) (ha : Integrable A (normalizedVolume g))
    (hvalue : ∀ e, F e = A e.base) :
    (∫ e, F e ∂μ) = ∫ c, A c ∂normalizedVolume g := by
  let : IsProbabilityMeasure sphereMeasure := h.probability
  apply hμ.fiberFormula _ _ hi ha
  · intro e f hbase _
    rw [hvalue e, hvalue f, hbase]
  · intro c e
    simp_rw [hvalue]
    change (∫ _ : Directions, A c ∂sphereMeasure) = A c
    simp

end
end PositiveEinsteinFour.Geometry
end


section

/-! The total second-variation boundary term is independent of the chart.
The second coordinate jet includes the Hessian of the actual chart change;
the Christoffel transformation cancels exactly that extra term. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def chartTransitionSecondVector (c d : M) (z : FourSpace)
    (y : JacobiCoordinateVector) : JacobiCoordinateVector :=
  jacobiConnection (fun i => matrixPartial (chartTransitionMatrix c d) i z) y *ᵥ y

end
end PositiveEinsteinFour.Geometry
end


section

/-! Intrinsic local horizontal curves obtained from the coordinate ODE. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Bundle
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem frame_eq_of_chart_coordinates (g : SmoothMetric M) (c : M)
    (e f : FrameBundle g) (he : e.base ∈ (chartAt FourSpace c).source)
    (hb : e.base = f.base) (hE : frameChartMatrix g c e = frameChartMatrix g c f) :
    e = f := by
  rcases e with ⟨x, e⟩
  rcases f with ⟨y, f⟩
  dsimp only at hb
  subst y
  have hi := (mdifferentiable_chart (I := I4) c).symm_comp_deriv he
  have hv (j : Fin 4) : e.vector j = f.vector j := by
    have hcol : WithLp.toLp 2 (fun a => frameChartMatrix g c ⟨x, e⟩ a j) =
        WithLp.toLp 2 (fun a => frameChartMatrix g c ⟨x, f⟩ a j) := by rw [hE]
    rw [frameChartMatrix_vector g c ⟨x, e⟩ he,
      frameChartMatrix_vector g c ⟨x, f⟩ he] at hcol
    have h := congrArg (mfderiv I4 I4 (chartAt FourSpace c).symm
      (chartAt FourSpace c x)) hcol
    have hiE := congrArg (fun L => L (e.vector j)) hi
    have hiF := congrArg (fun L => L (f.vector j)) hi
    exact hiE.symm.trans (h.trans hiF)
  have hm : e.matrix = f.matrix := by
    ext i j
    exact congrArg (fun v : FourSpace => v i) (hv j)
  cases e with
  | mk A hA =>
    cases f with
    | mk B hB =>
      dsimp only at hm
      subst B
      rfl

theorem chartFrameStateToBundle_fromFrame (g : SmoothMetric M) (c : M)
    (e : FrameBundle g) (he : e.base ∈ (chartAt FourSpace c).source) :
    chartFrameStateToBundle g c
      ⟨(chartAt FourSpace c e.base, frameChartMatrix g c e),
        (chartAt FourSpace c).map_source he, frameChartMatrix_normalizes g c e he⟩ = e := by
  apply frame_eq_of_chart_coordinates g c
  · change (chartAt FourSpace c).symm (chartAt FourSpace c e.base) ∈ _
    rw [(chartAt FourSpace c).left_inv he]
    exact he
  · exact (chartAt FourSpace c).left_inv he
  · exact frameChartMatrix_chartFrameState g c _

end
end PositiveEinsteinFour.Geometry
end


section

/-! Smooth covariant fields in centered coordinates. This supplies the
one-form fields used by the degree-two de Rham complex. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {n : ℕ}

def covariantFieldCoordinates (T : M → CovariantCoordinates n) (c : M)
    (z : FourSpace) : CovariantCoordinates n :=
  frameTensor (chartInverseMatrix c z) (T ((chartAt FourSpace c).symm z))

def CovariantFieldSmooth (T : M → CovariantCoordinates n) : Prop :=
  ∀ c z, z ∈ (chartAt FourSpace c).target → ∀ a,
    ContDiffAt ℝ ∞ (fun w => covariantFieldCoordinates T c w a) z

theorem covariantFieldCoordinates_transition (T : M → CovariantCoordinates n)
    (c d : M) (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target)
    (hx : (chartAt FourSpace c).symm z ∈ (chartAt FourSpace d).source) :
    covariantFieldCoordinates T c z = frameTensor (chartTransitionMatrix c d z)
      (covariantFieldCoordinates T d (chartTransition c d z)) := by
  unfold covariantFieldCoordinates
  rw [← frameTensor_mul, chartInverseMatrix_transition c d z hz hx]
  have hp : (chartAt FourSpace d).symm (chartTransition c d z) =
      (chartAt FourSpace c).symm z := (chartAt FourSpace d).left_inv hx
  rw [hp]

omit [IsManifold I4 ∞ M] in
theorem covariantFieldCoordinates_add (T U : M → CovariantCoordinates n)
    (c : M) (z : FourSpace) (a : Fin n → Fin 4) :
    covariantFieldCoordinates (T + U) c z a =
      covariantFieldCoordinates T c z a + covariantFieldCoordinates U c z a :=
  frameTensor_add _ _ _ _

omit [IsManifold I4 ∞ M] in
theorem covariantFieldCoordinates_smul (r : ℝ) (T : M → CovariantCoordinates n)
    (c : M) (z : FourSpace) (a : Fin n → Fin 4) :
    covariantFieldCoordinates (r • T) c z a = r * covariantFieldCoordinates T c z a :=
  frameTensor_const_mul _ _ _ _

def smoothCovariantFields (M : Type*) [TopologicalSpace M] [ChartedSpace FourSpace M]
    (n : ℕ) : Submodule ℝ (M → CovariantCoordinates n) where
  carrier := CovariantFieldSmooth
  zero_mem' := by
    intro c z hz a
    have he : (fun w => covariantFieldCoordinates (0 : M → CovariantCoordinates n) c w a) = 0 := by
      funext w
      simp only [covariantFieldCoordinates, Pi.zero_apply, frameTensor, mul_zero,
        Finset.sum_const_zero]
    rw [he]
    exact contDiffAt_const
  add_mem' hT hU := by
    intro c z hz a
    exact ((hT c z hz a).add (hU c z hz a)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun w => covariantFieldCoordinates_add _ _ c w a))
  smul_mem' r T hT := by
    intro c z hz a
    exact ((hT c z hz a).const_smul r).congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun w => covariantFieldCoordinates_smul r T c w a))

end
end PositiveEinsteinFour.Geometry
end


section

/-! Uniqueness of intrinsic parallel-frame curves follows from the actual
coordinate equations, independently of the chart chosen at the comparison point. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def frameCoordinateState (g : SmoothMetric M) (c : M)
    (e : FrameBundle g) : CoordinateFrameSpace :=
  (chartAt FourSpace c e.base, frameChartMatrix g c e)

theorem frameCoordinateState_continuousAt (g : SmoothMetric M) (c : M)
    (e : FrameBundle g) (he : e.base ∈ (chartAt FourSpace c).source) :
    ContinuousAt (frameCoordinateState g c) e := by
  have hb := ((chartAt FourSpace c).continuousAt he).comp
    (continuous_frameBase g).continuousAt
  have hE : ContinuousAt (fun f : FrameBundle g => frameChartMatrix g c f) e :=
    continuousAt_pi.mpr fun a => continuousAt_pi.mpr fun b =>
      frameChartMatrix_continuousAt g c e he a b
  exact hb.prodMk hE

theorem parallelFrameCurveAt_fixedChart (g : SmoothMetric M) (c : M)
    (γ : ℝ → FrameBundle g) (t : ℝ) (k : Fin 4)
    (hγ : ContinuousAt γ t) (hc : (γ t).base ∈ (chartAt FourSpace c).source)
    (hp : ParallelFrameCurveAt g γ k t) :
    HasDerivAt (fun s => frameCoordinateState g c (γ s))
      (parallelFrameVectorField g c k (frameCoordinateState g c (γ t))) t := by
  let d := (γ t).base
  let x (s : ℝ) : FourSpace := chartAt FourSpace d (γ s).base
  let E (s : ℝ) : Mat4 := frameChartMatrix g d (γ s)
  have hd : (γ t).base ∈ (chartAt FourSpace d).source := mem_chart_source FourSpace d
  have hz : x t ∈ (chartAt FourSpace d).target := (chartAt FourSpace d).map_source hd
  have hinv : (chartAt FourSpace d).symm (x t) = (γ t).base :=
    (chartAt FourSpace d).left_inv hd
  have htarget : (chartAt FourSpace d).symm (x t) ∈ (chartAt FourSpace c).source := by
    rw [hinv]
    exact hc
  have hchange : chartTransitionMatrix d c (x t) * E t = frameChartMatrix g c (γ t) :=
    frameChartMatrix_change g d c (γ t) hd hc
  have hvalue : chartTransition d c (x t) = chartAt FourSpace c (γ t).base := by
    change chartAt FourSpace c ((chartAt FourSpace d).symm (x t)) = _
    rw [hinv]
  have hnear : ∀ᶠ s in 𝓝 t,
      (γ s).base ∈ (chartAt FourSpace d).source ∧
      (γ s).base ∈ (chartAt FourSpace c).source :=
    ((continuous_frameBase g).continuousAt.comp hγ).eventually
      (((chartAt FourSpace d).open_source.inter (chartAt FourSpace c).open_source).mem_nhds
        ⟨hd, hc⟩)
  have hy : (fun s => chartAt FourSpace c (γ s).base) =ᶠ[𝓝 t]
      (fun s => chartTransition d c (x s)) := by
    filter_upwards [hnear] with s hs
    change chartAt FourSpace c (γ s).base =
      chartAt FourSpace c ((chartAt FourSpace d).symm (chartAt FourSpace d (γ s).base))
    rw [(chartAt FourSpace d).left_inv hs.1]
  have hF : (fun s => frameChartMatrix g c (γ s)) =ᶠ[𝓝 t]
      (fun s => chartTransitionMatrix d c (x s) * E s) := by
    filter_upwards [hnear] with s hs
    exact (frameChartMatrix_change g d c (γ s) hs.1 hs.2).symm
  have hv := hasDerivAt_changedChart_velocity d c x E t k hz htarget hp.velocity
  rw [hchange] at hv
  have hm (i j : Fin 4) :=
    hasDerivAt_changedChart_parallel g d c x E t k hz htarget hp.velocity hp.parallel i j
  have hm' : HasDerivAt (fun s => frameChartMatrix g c (γ s))
      (-(parallelFrameConnection g c k (frameCoordinateState g c (γ t)) *
        frameChartMatrix g c (γ t))) t := by
    apply hasDerivAt_pi.mpr
    intro i
    apply hasDerivAt_pi.mpr
    intro j
    have hh := hm i j
    rw [hchange, hvalue] at hh
    exact hh.congr_of_eventuallyEq (hF.mono fun s hs => congrFun (congrFun hs i) j)
  exact (hv.congr_of_eventuallyEq hy).prodMk hm'

theorem intrinsic_parallelFrame_unique_near (g : SmoothMetric M)
    (γ η : ℝ → FrameBundle g) (k : Fin 4) (t : ℝ)
    (hγ : ∀ᶠ s in 𝓝 t, ContinuousAt γ s ∧ ParallelFrameCurveAt g γ k s)
    (hη : ∀ᶠ s in 𝓝 t, ContinuousAt η s ∧ ParallelFrameCurveAt g η k s)
    (heq : γ t = η t) : γ =ᶠ[𝓝 t] η := by
  let c := (γ t).base
  have hc : (γ t).base ∈ (chartAt FourSpace c).source := mem_chart_source FourSpace c
  have hγnear := ((continuous_frameBase g).continuousAt.comp hγ.self_of_nhds.1).eventually
    ((chartAt FourSpace c).open_source.mem_nhds hc)
  have hηnear := ((continuous_frameBase g).continuousAt.comp hη.self_of_nhds.1).eventually
    ((chartAt FourSpace c).open_source.mem_nhds (by simpa only [Function.comp_def, ← heq] using hc))
  have hdγ : ∀ᶠ s in 𝓝 t,
      HasDerivAt (fun r => frameCoordinateState g c (γ r))
        (parallelFrameVectorField g c k (frameCoordinateState g c (γ s))) s := by
    filter_upwards [hγ, hγnear] with s hs hc'
    exact parallelFrameCurveAt_fixedChart g c γ s k hs.1 hc' hs.2
  have hdη : ∀ᶠ s in 𝓝 t,
      HasDerivAt (fun r => frameCoordinateState g c (η r))
        (parallelFrameVectorField g c k (frameCoordinateState g c (η s))) s := by
    filter_upwards [hη, hηnear] with s hs hc'
    exact parallelFrameCurveAt_fixedChart g c η s k hs.1 hc' hs.2
  have hu := parallelFrame_solution_unique_near g c k
    (fun r => frameCoordinateState g c (γ r))
    (fun r => frameCoordinateState g c (η r)) t
    ((chartAt FourSpace c).map_source hc) hdγ hdη (by rw [heq])
  filter_upwards [hu, hγnear, hηnear] with s hs hc' hd'
  apply frame_eq_of_chart_coordinates g c (γ s) (η s) hc'
  · apply (chartAt FourSpace c).injOn hc'
      hd'
    exact congrArg Prod.fst hs
  · exact congrArg Prod.snd hs

/-- Two intrinsic horizontal curves with one common value agree throughout
any common open interval. Local uniqueness is transported through a fixed
chart only near each comparison point. -/
theorem intrinsic_parallelFrame_unique_interval [T2Space M]
    (g : SmoothMetric M) (γ η : ℝ → FrameBundle g) (k : Fin 4)
    (a b t : ℝ) (ht : t ∈ Set.Ioo a b)
    (hγc : ContinuousOn γ (Set.Ioo a b))
    (hηc : ContinuousOn η (Set.Ioo a b))
    (hγ : ∀ s ∈ Set.Ioo a b, ParallelFrameCurveAt g γ k s)
    (hη : ∀ s ∈ Set.Ioo a b, ParallelFrameCurveAt g η k s)
    (heq : γ t = η t) : Set.EqOn γ η (Set.Ioo a b) := by
  let I := Set.Ioo a b
  let : PreconnectedSpace I :=
    isPreconnected_iff_preconnectedSpace.mp (convex_Ioo a b).isPreconnected
  let S : Set I := {s | γ s.val = η s.val}
  have hclosed : IsClosed S :=
    isClosed_eq hγc.domRestrict hηc.domRestrict
  have hopen : IsOpen S := by
    apply isOpen_iff_mem_nhds.mpr
    intro s hs
    have hnear : ∀ᶠ r in 𝓝 s.val, r ∈ Set.Ioo a b :=
      isOpen_Ioo.mem_nhds s.property
    have hg : ∀ᶠ r in 𝓝 s.val, ContinuousAt γ r ∧ ParallelFrameCurveAt g γ k r :=
      hnear.mono fun r hr =>
        ⟨hγc.continuousAt (isOpen_Ioo.mem_nhds hr), hγ r hr⟩
    have hh : ∀ᶠ r in 𝓝 s.val, ContinuousAt η r ∧ ParallelFrameCurveAt g η k r :=
      hnear.mono fun r hr =>
        ⟨hηc.continuousAt (isOpen_Ioo.mem_nhds hr), hη r hr⟩
    have hu := intrinsic_parallelFrame_unique_near g γ η k s.val hg hh hs
    exact continuous_subtype_val.continuousAt.preimage_mem_nhds hu
  have hnonempty : S.Nonempty := ⟨⟨t, ht⟩, heq⟩
  have hfull : S = Set.univ := (show IsClopen S from ⟨hclosed, hopen⟩).eq_univ hnonempty
  intro s hs
  have hm : (⟨s, hs⟩ : I) ∈ S := by rw [hfull]; trivial
  exact hm

/-- Global intrinsic parallel curves are determined by their initial frame. -/
theorem intrinsic_parallelFrame_unique_global [T2Space M]
    (g : SmoothMetric M) (γ η : ℝ → FrameBundle g) (k : Fin 4)
    (hγc : Continuous γ) (hηc : Continuous η)
    (hγ : ∀ t, ParallelFrameCurveAt g γ k t)
    (hη : ∀ t, ParallelFrameCurveAt g η k t)
    (heq : γ 0 = η 0) : γ = η := by
  funext t
  let a := |t| + 1
  have ha : 0 < a := by dsimp [a]; positivity
  have h0 : (0 : ℝ) ∈ Set.Ioo (-a) a := ⟨by linarith, ha⟩
  have ht : t ∈ Set.Ioo (-a) a := abs_lt.mp (lt_add_one _)
  exact intrinsic_parallelFrame_unique_interval g γ η k (-a) a 0 h0
    hγc.continuousOn hηc.continuousOn (fun s _ => hγ s) (fun s _ => hη s) heq ht

end
end PositiveEinsteinFour.Geometry
end


section

/-! The existing Levi-Civita coordinate derivative acts on actual smooth
covariant fields; no chart or derivative compatibility is assumed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {n : ℕ}

def covariantFieldDerivative (g : SmoothMetric M) (T : M → CovariantCoordinates n) :
    M → CovariantCoordinates (n + 1) :=
  fun x => covariantDerivative g x (covariantFieldCoordinates T x) (chartAt FourSpace x x)

theorem covariantFieldDerivative_coordinates {T : M → CovariantCoordinates n}
    (hT : CovariantFieldSmooth T) (c : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target) :
    covariantFieldCoordinates (covariantFieldDerivative g T) c z =
      covariantDerivative g c (covariantFieldCoordinates T c) z := by
  let d := (chartAt FourSpace c).symm z
  have hx : (chartAt FourSpace c).symm z ∈ (chartAt FourSpace d).source :=
    mem_chart_source FourSpace d
  have he := covariantDerivative_chart_transition g c d
    (covariantFieldCoordinates T c) (covariantFieldCoordinates T d) z hz hx
    (fun a => (hT d _ ((chartAt FourSpace d).map_source hx) a).differentiableAt (by simp))
    ((chart_overlap_eventually c d z hz hx).mono
      (fun w hw => covariantFieldCoordinates_transition T c d w hw.1 hw.2))
  rw [chartTransitionMatrix_to_center c z hz] at he
  exact he.symm

theorem CovariantFieldSmooth.derivative {T : M → CovariantCoordinates n}
    (hT : CovariantFieldSmooth T) : CovariantFieldSmooth (covariantFieldDerivative g T) := by
  intro c z hz a
  have h := covariantDerivative_contDiffAt g c z hz
    (metricInChart_posDef g c z hz).det_pos.ne' _ (hT c z hz) a
  apply h.congr_of_eventuallyEq
  filter_upwards [(chartAt FourSpace c).open_target.mem_nhds hz] with w hw
  exact congrFun (covariantFieldDerivative_coordinates hT c w hw) a

def covariantFieldFramed (g : SmoothMetric M) (T : M → CovariantCoordinates n)
    (e : FrameBundle g) : CovariantCoordinates n :=
  frameTensor e.frame.matrix (covariantFieldCoordinates T e.base (chartAt FourSpace e.base e.base))

theorem covariantFieldFramed_eq (T : M → CovariantCoordinates n) (e : FrameBundle g) :
    covariantFieldFramed g T e = frameTensor e.frame.matrix (T e.base) := by
  unfold covariantFieldFramed covariantFieldCoordinates
  rw [chartInverseMatrix_center, frameTensor_one,
    (chartAt FourSpace e.base).left_inv (mem_chart_source FourSpace e.base)]

theorem CovariantFieldSmooth.continuous_framed {T : M → CovariantCoordinates n}
    (hT : CovariantFieldSmooth T) : Continuous (covariantFieldFramed g T) := by
  apply continuous_framedTensor g (covariantFieldCoordinates T)
  · intro c z hz a
    exact (hT c z hz a).continuousAt
  · exact covariantFieldCoordinates_transition T

theorem CovariantFieldSmooth.parallel_derivative {T : M → CovariantCoordinates n}
    (hT : CovariantFieldSmooth T) (γ : ℝ → FrameBundle g) (t : ℝ) (i : Fin 4)
    (hγ : ContinuousAt γ t) (hp : ParallelFrameCurveAt g γ i t) (a : Fin n → Fin 4) :
    HasDerivAt (fun s => covariantFieldFramed g T (γ s) a)
      (covariantFieldFramed g (covariantFieldDerivative g T) (γ t) (Fin.cons i a)) t := by
  have h := hasDerivAt_framedTensor g (covariantFieldCoordinates T)
    (fun c z hz a => (hT c z hz a).differentiableAt (by simp))
    (covariantFieldCoordinates_transition T)
    (fun c d z hz hx => covariantDerivative_chart_transition g c d
      (covariantFieldCoordinates T c) (covariantFieldCoordinates T d) z hz hx
      (fun b => (hT d _ ((chartAt FourSpace d).map_source hx) b).differentiableAt (by simp))
      ((chart_overlap_eventually c d z hz hx).mono
        (fun w hw => covariantFieldCoordinates_transition T c d w hw.1 hw.2)))
    γ t i hγ hp a
  refine h.congr_deriv ?_
  · rw [covariantFieldFramed_eq]
    rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! The completion in the actual two-form H1 norm and its bounded map to
L2. Injectivity of the map is not assumed; it requires the weak derivative
closure argument. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

def SmoothH1TwoForm (o : FrameOrientation g) : Type _ := ↥(smoothTwoForms o)
  deriving AddCommGroup, Module ℝ

instance instCoeSmoothH1TwoFormSubtypeForallTwoFormFourMemSubmoduleRealSmoothTwoForms : Coe (SmoothH1TwoForm o) (smoothTwoForms o) := ⟨id⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual curvature commutator for smooth covariant fields. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {n : ℕ}

theorem CovariantFieldSmooth.framed_second {T : M → CovariantCoordinates n}
    (hT : CovariantFieldSmooth T) (e : FrameBundle g) :
    covariantFieldFramed g (covariantFieldDerivative g (covariantFieldDerivative g T)) e =
      frameTensor e.frame.matrix
        (covariantDerivative g e.base
          (covariantDerivative g e.base (covariantFieldCoordinates T e.base))
            (chartAt FourSpace e.base e.base)) := by
  rw [covariantFieldFramed_eq]
  change frameTensor e.frame.matrix
    (covariantDerivative g e.base (covariantFieldCoordinates (covariantFieldDerivative g T) e.base)
      (chartAt FourSpace e.base e.base)) = _
  congr 1
  apply covariantDerivative_congr
  filter_upwards [(chartAt FourSpace e.base).open_target.mem_nhds
    (mem_chart_target FourSpace e.base)] with w hw
  exact covariantFieldDerivative_coordinates hT e.base w hw

theorem CovariantFieldSmooth.framed_commutator {T : M → CovariantCoordinates n}
    (hT : CovariantFieldSmooth T) (e : FrameBundle g) (i j : Fin 4) (a : Fin n → Fin 4) :
    covariantFieldFramed g (covariantFieldDerivative g (covariantFieldDerivative g T)) e
        (Fin.cons i (Fin.cons j a)) -
      covariantFieldFramed g (covariantFieldDerivative g (covariantFieldDerivative g T)) e
        (Fin.cons j (Fin.cons i a)) =
      -tensorSlotAction (curvatureEndomorphism (frameCurvature g e.base e.frame) i j)
        (covariantFieldFramed g T e) a := by
  let c := e.base
  let z := chartAt FourSpace c c
  let X := covariantDerivative g c (covariantDerivative g c (covariantFieldCoordinates T c)) z
  let C := fun p q => coordinateCurvatureMatrix g c p q z
  have hX (p q : Fin 4) (b : Fin n → Fin 4) :
      X (Fin.cons p (Fin.cons q b)) - X (Fin.cons q (Fin.cons p b)) =
        -tensorSlotAction (C p q) (covariantFieldCoordinates T c z) b :=
    covariantDerivative_commutator g c (covariantFieldCoordinates T c) z
      (mem_chart_target FourSpace c) (metricInChart_posDef g c z
        (mem_chart_target FourSpace c)).det_pos.ne' (hT c z (mem_chart_target FourSpace c)) p q b
  have h := framed_tensor_commutator e.frame.matrix
    (isUnit_iff_ne_zero.mpr e.frame.det_ne_zero) C (covariantFieldCoordinates T c z) X hX i j a
  rw [frame_curvatureEndomorphism] at h
  rw [hT.framed_second]
  exact h

end
end PositiveEinsteinFour.Geometry
end


section

/-! The intrinsic squared norm of a smooth covariant field. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {n : ℕ}

def covariantFieldNormSq (g : SmoothMetric M) (T : M → CovariantCoordinates n) (x : M) : ℝ :=
  frameTensorSquareNorm (covariantFieldFramed g T (frameAt g x))

theorem covariantFieldNormSq_eq_frame (T : M → CovariantCoordinates n) (e : FrameBundle g) :
    covariantFieldNormSq g T e.base = frameTensorSquareNorm (covariantFieldFramed g T e) := by
  unfold covariantFieldNormSq
  simp only [covariantFieldFramed_eq]
  exact frameTensor_norm_same_base _ _ _

theorem CovariantFieldSmooth.continuous_normSq {T : M → CovariantCoordinates n}
    (hT : CovariantFieldSmooth T) : Continuous (covariantFieldNormSq g T) := by
  have hnorm : Continuous (fun U : CovariantCoordinates n => frameTensorSquareNorm U) :=
    continuous_finsetSum _ (fun a _ => (continuous_apply a).mul (continuous_apply a))
  have hc := hnorm.comp (hT.continuous_framed (g := g))
  apply continuous_iff_continuousAt.mpr
  intro c
  apply (hc.continuousAt.comp (continuousAt_localGramSection g c 1 (by simp))).congr_of_eventuallyEq
  filter_upwards [] with x
  have he := covariantFieldNormSq_eq_frame T (localGramSection g c 1 (by simp) x)
  rw [localGramSection_base] at he
  exact he

end
end PositiveEinsteinFour.Geometry
end


section

/-! Alternating smooth covariant fields give the existing actual
six-coordinate two-form sections. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

omit [IsManifold I4 ∞ M] in
theorem CovariantTwoFormSkew.coordinates {T : M → CovariantCoordinates 2}
    (hT : CovariantTwoFormSkew T) (c : M) (z : FourSpace) :
    ∀ i j, covariantFieldCoordinates T c z ![j,i] =
      -covariantFieldCoordinates T c z ![i,j] :=
  twoTensor_frame_skew _ _ (hT _)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Locality and time translation for the actual parallel-frame equations.
These are the operations used to extend coordinate solutions. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem parallelFrameCurveAt_congr (g : SmoothMetric M)
    {γ η : ℝ → FrameBundle g} {k : Fin 4} {t : ℝ}
    (h : ParallelFrameCurveAt g γ k t) (heq : γ =ᶠ[𝓝 t] η) :
    ParallelFrameCurveAt g η k t := by
  have ht := heq.self_of_nhds
  constructor
  · have hv := h.velocity.congr_of_eventuallyEq
      (heq.symm.mono fun s hs => congrArg (fun e : FrameBundle g =>
        chartAt FourSpace (γ t).base e.base) hs)
    simpa only [ht] using hv
  · intro i j
    have hm := (h.parallel i j).congr_of_eventuallyEq
      (heq.symm.mono fun s hs => congrArg (fun e : FrameBundle g =>
        frameChartMatrix g (γ t).base e i j) hs)
    simpa only [ht] using hm

theorem parallelFrameCurveAt_comp_add (g : SmoothMetric M)
    (γ : ℝ → FrameBundle g) (k : Fin 4) (t a : ℝ)
    (h : ParallelFrameCurveAt g γ k (t + a)) :
    ParallelFrameCurveAt g (fun s => γ (s + a)) k t := by
  constructor
  · exact h.velocity.comp_add_const t a
  · intro i j
    exact (h.parallel i j).comp_add_const t a

/-- A curve on an open time set is continuous and satisfies the genuine
velocity and Levi-Civita parallel equations there. -/
def IsParallelFrameCurveOn (g : SmoothMetric M) (k : Fin 4)
    (γ : ℝ → FrameBundle g) (s : Set ℝ) : Prop :=
  ContinuousOn γ s ∧ ∀ t ∈ s, ParallelFrameCurveAt g γ k t

theorem IsParallelFrameCurveOn.mono {g : SmoothMetric M} {k : Fin 4}
    {γ : ℝ → FrameBundle g} {s u : Set ℝ}
    (h : IsParallelFrameCurveOn g k γ s) (hu : u ⊆ s) :
    IsParallelFrameCurveOn g k γ u :=
  ⟨h.1.mono hu, fun t ht => h.2 t (hu ht)⟩

theorem IsParallelFrameCurveOn.eqOn_interval [T2Space M]
    {g : SmoothMetric M} {k : Fin 4} {γ η : ℝ → FrameBundle g}
    {a b t : ℝ} (hγ : IsParallelFrameCurveOn g k γ (Set.Ioo a b))
    (hη : IsParallelFrameCurveOn g k η (Set.Ioo a b))
    (ht : t ∈ Set.Ioo a b) (heq : γ t = η t) :
    Set.EqOn γ η (Set.Ioo a b) :=
  intrinsic_parallelFrame_unique_interval g γ η k a b t ht hγ.1 hη.1 hγ.2 hη.2 heq

theorem IsParallelFrameCurveOn.comp_add {g : SmoothMetric M} {k : Fin 4}
    {γ : ℝ → FrameBundle g} {a b : ℝ}
    (h : IsParallelFrameCurveOn g k γ (Set.Ioo a b)) (c : ℝ) :
    IsParallelFrameCurveOn g k (fun t => γ (t + c))
      (Set.Ioo (a - c) (b - c)) := by
  have hmem {t : ℝ} (ht : t ∈ Set.Ioo (a - c) (b - c)) :
      t + c ∈ Set.Ioo a b := by
    constructor <;> linarith [ht.1, ht.2]
  refine ⟨h.1.comp (continuous_id.add continuous_const).continuousOn
    (fun t ht => hmem ht), ?_⟩
  intro t ht
  exact parallelFrameCurveAt_comp_add g γ k t c (h.2 (t + c) (hmem ht))

/-- The two local curves agree on the entire overlap, so choosing the first
one on its interval leaves the second one unchanged on its own interval. -/
theorem parallelFrame_piecewise_eqOn [T2Space M]
    {g : SmoothMetric M} {k : Fin 4} {γ η : ℝ → FrameBundle g}
    {a b c d t : ℝ}
    (hγ : IsParallelFrameCurveOn g k γ (Set.Ioo a b))
    (hη : IsParallelFrameCurveOn g k η (Set.Ioo c d))
    (ht : t ∈ Set.Ioo a b ∩ Set.Ioo c d) (heq : γ t = η t) :
    Set.EqOn ((Set.Ioo a b).piecewise γ η) η (Set.Ioo c d) := by
  classical
  have heqI : Set.EqOn γ η (Set.Ioo (max a c) (min b d)) :=
    (hγ.mono (Set.Ioo_subset_Ioo (le_max_left _ _) (min_le_left _ _))).eqOn_interval
      (hη.mono (Set.Ioo_subset_Ioo (le_max_right _ _) (min_le_right _ _)))
      ⟨max_lt ht.1.1 ht.2.1, lt_min ht.1.2 ht.2.2⟩ heq
  intro s hs
  by_cases hsa : s ∈ Set.Ioo a b
  · rw [Set.piecewise, ite_eq_left hsa]
    exact heqI ⟨max_lt hsa.1 hs.1, lt_min hsa.2 hs.2⟩
  · rw [Set.piecewise, ite_eq_right hsa]

/-- Gluing two overlapping local parallel curves produces a parallel curve
on the union of their time intervals. -/
theorem IsParallelFrameCurveOn.piecewise [T2Space M]
    {g : SmoothMetric M} {k : Fin 4} {γ η : ℝ → FrameBundle g}
    {a b c d t : ℝ}
    (hγ : IsParallelFrameCurveOn g k γ (Set.Ioo a b))
    (hη : IsParallelFrameCurveOn g k η (Set.Ioo c d))
    (ht : t ∈ Set.Ioo a b ∩ Set.Ioo c d) (heq : γ t = η t) :
    IsParallelFrameCurveOn g k ((Set.Ioo a b).piecewise γ η)
      (Set.Ioo a b ∪ Set.Ioo c d) := by
  classical
  have hother := parallelFrame_piecewise_eqOn hγ hη ht heq
  have hlocal (s : ℝ) (hs : s ∈ Set.Ioo a b ∪ Set.Ioo c d) :
      ContinuousAt ((Set.Ioo a b).piecewise γ η) s ∧
        ParallelFrameCurveAt g ((Set.Ioo a b).piecewise γ η) k s := by
    by_cases hsa : s ∈ Set.Ioo a b
    · have hnear : (Set.Ioo a b).piecewise γ η =ᶠ[𝓝 s] γ := by
        filter_upwards [isOpen_Ioo.mem_nhds hsa] with u hu
        rw [Set.piecewise, ite_eq_left hu]
      exact ⟨(hγ.1.continuousAt (isOpen_Ioo.mem_nhds hsa)).congr_of_eventuallyEq hnear,
        parallelFrameCurveAt_congr g (hγ.2 s hsa) hnear.symm⟩
    · have hsc : s ∈ Set.Ioo c d := hs.resolve_left hsa
      have hnear : (Set.Ioo a b).piecewise γ η =ᶠ[𝓝 s] η := by
        filter_upwards [isOpen_Ioo.mem_nhds hsc] with u hu
        exact hother hu
      exact ⟨(hη.1.continuousAt (isOpen_Ioo.mem_nhds hsc)).congr_of_eventuallyEq hnear,
        parallelFrameCurveAt_congr g (hη.2 s hsc) hnear.symm⟩
  exact ⟨fun s hs => (hlocal s hs).1.continuousWithinAt, fun s hs => (hlocal s hs).2⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! Continuous local horizontal flows in the actual frame bundle. The
ambient coordinate ODE preserves its Gram matrix, so its nearby normalized
initial conditions remain actual orthonormal frames. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Metric
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem exists_continuous_local_intrinsic_parallelFrame_flow
    (g : SmoothMetric M) (e : FrameBundle g) (k : Fin 4) :
    ∃ U : Set (FrameBundle g), IsOpen U ∧ e ∈ U ∧
      ∃ ε > (0 : ℝ), ∃ Φ : FrameBundle g × ℝ → FrameBundle g,
        ContinuousOn Φ (U ×ˢ Ioo (-ε) ε) ∧
        ∀ f ∈ U, Φ (f, 0) = f ∧
          ∀ t ∈ Ioo (-ε) ε,
            ParallelFrameCurveAt g (fun s => Φ (f, s)) k t := by
  classical
  let c := e.base
  let q := frameCoordinateState g c
  have he : e.base ∈ (chartAt FourSpace c).source := mem_chart_source FourSpace c
  obtain ⟨r, hr, ε, hε, α, hαc, hα⟩ :=
    exists_continuous_local_parallelFrame_flow g c k (q e)
      ((chartAt FourSpace c).map_source he)
  let U : Set (FrameBundle g) :=
    {f | f.base ∈ (chartAt FourSpace c).source ∧ q f ∈ ball (q e) r}
  have hU : IsOpen U := by
    apply isOpen_iff_mem_nhds.mpr
    intro f hf
    have hs := (continuous_frameBase g).continuousAt.preimage_mem_nhds
      ((chartAt FourSpace c).open_source.mem_nhds hf.1)
    have hq := (frameCoordinateState_continuousAt g c f hf.1).preimage_mem_nhds
      (isOpen_ball.mem_nhds hf.2)
    exact Filter.inter_mem hs hq
  have heU : e ∈ U := ⟨he, mem_ball_self hr⟩
  have hqball {f : FrameBundle g} (hf : f ∈ U) : q f ∈ closedBall (q e) r :=
    ball_subset_closedBall hf.2
  let I := Ioo (-ε) ε
  have hstate (u : U ×ˢ I) :
      (α (q u.val.1, u.val.2)).1 ∈ (chartAt FourSpace c).target ∧
      (α (q u.val.1, u.val.2)).2ᵀ * metricInChart g c (α (q u.val.1, u.val.2)).1 *
        (α (q u.val.1, u.val.2)).2 = 1 := by
    have h := (hα (q u.val.1) (hqball u.property.1)).2 u.val.2 u.property.2
    exact ⟨h.1, h.2.2.trans (frameChartMatrix_normalizes g c u.val.1 u.property.1.1)⟩
  let β : (U ×ˢ I) → OrthonormalChartState g c :=
    fun u => ⟨α (q u.val.1, u.val.2), hstate u⟩
  have hβ : Continuous β := by
    have hqcont : Continuous (fun u : U ×ˢ I => q u.val.1) := by
      apply continuous_iff_continuousAt.mpr
      intro u
      have hp : ContinuousAt (fun v : U ×ˢ I => v.val.1) u :=
        (continuous_fst.comp continuous_subtype_val).continuousAt
      exact (frameCoordinateState_continuousAt g c u.val.1 u.property.1.1).comp
        (x := u) hp
    have htime : Continuous (fun u : U ×ˢ I => u.val.2) :=
      continuous_snd.comp continuous_subtype_val
    apply Continuous.subtype_mk
    exact hαc.comp_continuous (hqcont.prodMk htime)
      (fun u => ⟨hqball u.property.1, u.property.2⟩)
  let Φ : FrameBundle g × ℝ → FrameBundle g := fun u =>
    if hu : u ∈ U ×ˢ I then chartFrameStateToBundle g c (β ⟨u, hu⟩) else u.1
  have hΦeq (u : U ×ˢ I) : Φ u = chartFrameStateToBundle g c (β u) := by
    simp only [Φ, dite_eq_left u.property]
  have hΦc : ContinuousOn Φ (U ×ˢ I) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    exact ((continuous_chartFrameStateToBundle g c).comp hβ).congr
      (fun u => (hΦeq u).symm)
  refine ⟨U, hU, heU, ε, hε, Φ, hΦc, ?_⟩
  intro f hf
  have hz : (0 : ℝ) ∈ I := ⟨by linarith, hε⟩
  refine ⟨?_, ?_⟩
  · rw [hΦeq ⟨(f, 0), hf, hz⟩]
    have hβ0 : β ⟨(f, 0), hf, hz⟩ =
        (⟨q f, (chartAt FourSpace c).map_source hf.1,
          frameChartMatrix_normalizes g c f hf.1⟩ : OrthonormalChartState g c) := by
      apply Subtype.ext
      exact (hα (q f) (hqball hf)).1
    rw [hβ0]
    exact chartFrameStateToBundle_fromFrame g c f hf.1
  · intro t ht
    have hnear : ∀ᶠ s in 𝓝 t, s ∈ I := isOpen_Ioo.mem_nhds ht
    have hx : (fun s => chartAt FourSpace c (Φ (f, s)).base) =ᶠ[𝓝 t]
        (fun s => (α (q f, s)).1) := by
      filter_upwards [hnear] with s hs
      rw [hΦeq ⟨(f, s), hf, hs⟩, chartFrameState_coordinate]
    have hE : (fun s => frameChartMatrix g c (Φ (f, s))) =ᶠ[𝓝 t]
        (fun s => (α (q f, s)).2) := by
      filter_upwards [hnear] with s hs
      rw [hΦeq ⟨(f, s), hf, hs⟩, frameChartMatrix_chartFrameState]
    have hsol := (hα (q f) (hqball hf)).2 t ht
    have hv : HasDerivAt (fun s => (α (q f, s)).1)
        (WithLp.toLp 2 (fun r => (α (q f, t)).2 r k)) t :=
      (ContinuousLinearMap.fst ℝ FourSpace Mat4).hasFDerivAt.comp_hasDerivAt t hsol.2.1
    have hm : HasDerivAt (fun s => (α (q f, s)).2)
        (-(parallelFrameConnection g c k (α (q f, t)) * (α (q f, t)).2)) t :=
      (ContinuousLinearMap.snd ℝ FourSpace Mat4).hasFDerivAt.comp_hasDerivAt t hsol.2.1
    have hvalue : α (q f, t) =
        (chartAt FourSpace c (Φ (f, t)).base, frameChartMatrix g c (Φ (f, t))) :=
      Prod.ext hx.self_of_nhds.symm hE.self_of_nhds.symm
    rw [hvalue] at hv hm
    have hc : ContinuousAt (fun s => Φ (f, s)) t :=
      (hΦc.continuousAt ((hU.prod isOpen_Ioo).mem_nhds ⟨hf, ht⟩)).comp
        (continuous_const.prodMk continuous_id).continuousAt
    apply parallelFrameCurveAt_of_fixedChart g c (fun s => Φ (f, s)) t k hc
    · rw [hΦeq ⟨(f, t), hf, ht⟩]
      exact (chartAt FourSpace c).map_target (hstate ⟨(f, t), hf, ht⟩).1
    · exact hv.congr_of_eventuallyEq hx
    · intro i j
      exact (hasDerivAt_pi.mp (hasDerivAt_pi.mp hm i) j).congr_of_eventuallyEq
        (hE.mono fun s hs => congrFun (congrFun hs i) j)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Characteristic-number and Weyl-gap identities. Gursky--LeBrun, equations (6)--(7), together with the degree
one Bochner vanishing and Hodge decomposition (Petersen §9.1), give the two
integer-count identities. Gursky--LeBrun Theorem 1 gives the two norm gaps.
 -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

def GurskyLeBrunGapInput (g : SmoothMetric M) (orientation : FrameOrientation g) : Prop :=
  ((∃ c, plusNorm orientation c ≠ 0) →
    1 ≤ ∫ c, plusNorm orientation c ^ 2 ∂normalizedVolume g) ∧
  ((∃ c, minusNorm orientation c ≠ 0) →
    1 ≤ ∫ c, minusNorm orientation c ^ 2 ∂normalizedVolume g)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Compactness supplies one common existence time for the actual local
parallel-frame curves. The time comes from a finite cover by the intrinsic
local flow neighborhoods. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem exists_uniform_parallelFrame_time [CompactSpace M]
    (g : SmoothMetric M) (k : Fin 4) :
    ∃ ε > (0 : ℝ), ∀ e : FrameBundle g,
      ∃ γ : ℝ → FrameBundle g, γ 0 = e ∧
        IsParallelFrameCurveOn g k γ (Ioo (-ε) ε) := by
  classical
  let : CompactSpace (FrameBundle g) := actual_compactFrameBundle g
  choose U hU heU ε hε Φ hΦ hcurve using
    (fun e => exists_continuous_local_intrinsic_parallelFrame_flow g e k)
  have hnhds (e : FrameBundle g) : U e ∈ 𝓝 e := (hU e).mem_nhds (heU e)
  obtain ⟨s, hs⟩ := finite_cover_nhds hnhds
  have common (s : Finset (FrameBundle g)) :
      ∃ δ > (0 : ℝ), ∀ e ∈ s, δ ≤ ε e := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, by simp⟩
    | @insert a s ha ih =>
      obtain ⟨δ, hδ, hb⟩ := ih
      refine ⟨min δ (ε a), lt_min hδ (hε a), ?_⟩
      intro e he
      rcases Finset.mem_insert.mp he with rfl | he
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hb e he)
  obtain ⟨δ, hδ, hb⟩ := common s
  refine ⟨δ, hδ, fun e => ?_⟩
  have he : e ∈ ⋃ c ∈ s, U c := by rw [hs]; trivial
  obtain ⟨c, hc, hec⟩ := mem_iUnion₂.mp he
  have ht {t : ℝ} (ht : t ∈ Ioo (-δ) δ) : t ∈ Ioo (-(ε c)) (ε c) := by
    have hd := hb c hc
    constructor <;> linarith [ht.1, ht.2]
  refine ⟨fun t => Φ c (e, t), (hcurve c e hec).1, ?_⟩
  constructor
  · exact (hΦ c).comp (continuous_const.prodMk continuous_id).continuousOn
      (fun t htm => ⟨hec, ht htm⟩)
  · intro t htm
    exact (hcurve c e hec).2 t (ht htm)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Endpoint curves are affine in a common chart.  In any overlapping chart,
their first and second jets are the actual derivatives of the chart change.
Restriction followed by constant extension gives globally continuous jet
functions without requiring a chart change to be regular outside its overlap. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter
open scoped _root_.Topology Manifold ContDiff BigOperators Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]

def endpointChartLine (z : FourSpace) (y : JacobiCoordinateVector) (s : ℝ) : FourSpace :=
  z + s • WithLp.toLp 2 y

def endpointChartPosition (c d : M) (z : FourSpace) (y : JacobiCoordinateVector)
    (s : ℝ) : FourSpace :=
  chartTransition c d (endpointChartLine z y s)

def endpointChartFirst (c d : M) (z : FourSpace) (y : JacobiCoordinateVector)
    (s : ℝ) : FourSpace :=
  WithLp.toLp 2 (chartTransitionMatrix c d (endpointChartLine z y s) *ᵥ y)

def endpointChartSecond (c d : M) (z : FourSpace) (y : JacobiCoordinateVector)
    (s : ℝ) : FourSpace :=
  WithLp.toLp 2 (chartTransitionSecondVector c d (endpointChartLine z y s) y)

@[simp] theorem endpointChartPosition_zero (c d : M) (z : FourSpace)
    (y : JacobiCoordinateVector) : endpointChartPosition c d z y 0 = chartTransition c d z := by
  simp only [endpointChartPosition, endpointChartLine, zero_smul, add_zero]

@[simp] theorem endpointChartFirst_zero (c d : M) (z : FourSpace)
    (y : JacobiCoordinateVector) :
    endpointChartFirst c d z y 0 = WithLp.toLp 2 (chartTransitionMatrix c d z *ᵥ y) := by
  simp only [endpointChartFirst, endpointChartLine, zero_smul, add_zero]

@[simp] theorem endpointChartSecond_zero (c d : M) (z : FourSpace)
    (y : JacobiCoordinateVector) :
    endpointChartSecond c d z y 0 = WithLp.toLp 2 (chartTransitionSecondVector c d z y) := by
  simp only [endpointChartSecond, endpointChartLine, zero_smul, add_zero]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Linearity of the actual exterior derivative on smooth one-forms. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem covariantFieldDerivative_add {n : ℕ} (u v : smoothCovariantFields M n) :
    covariantFieldDerivative g (u + v).val =
      covariantFieldDerivative g u.val + covariantFieldDerivative g v.val := by
  funext x
  have he : covariantFieldCoordinates (u + v).val x =
      fun z => covariantFieldCoordinates u.val x z + covariantFieldCoordinates v.val x z := by
    funext z a
    exact covariantFieldCoordinates_add u.val v.val x z a
  change covariantDerivative g x (covariantFieldCoordinates (u + v).val x) _ = _
  rw [he]
  exact covariantDerivative_add g x _ _ _
    (fun a => (u.property x _ (mem_chart_target FourSpace x) a).differentiableAt (by simp))
    (fun a => (v.property x _ (mem_chart_target FourSpace x) a).differentiableAt (by simp))

theorem covariantFieldDerivative_smul {n : ℕ} (r : ℝ) (u : smoothCovariantFields M n) :
    covariantFieldDerivative g (r • u).val = r • covariantFieldDerivative g u.val := by
  funext x
  have he : covariantFieldCoordinates (r • u).val x =
      fun z => r • covariantFieldCoordinates u.val x z := by
    funext z a
    exact covariantFieldCoordinates_smul r u.val x z a
  change covariantDerivative g x (covariantFieldCoordinates (r • u).val x) _ = _
  rw [he]
  exact covariantDerivative_const_smul g x r _ _

end
end PositiveEinsteinFour.Geometry
end


section

/-! Extension of actual parallel curves by a uniform local existence time. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M]

theorem extend_parallelFrame_interval (g : SmoothMetric M) (k : Fin 4)
    {ε a : ℝ} (hε : 0 < ε) (ha : ε / 2 ≤ a)
    (hlocal : ∀ e : FrameBundle g, ∃ γ : ℝ → FrameBundle g,
      γ 0 = e ∧ IsParallelFrameCurveOn g k γ (Ioo (-ε) ε))
    {γ : ℝ → FrameBundle g} (hγ : IsParallelFrameCurveOn g k γ (Ioo (-a) a)) :
    ∃ δ : ℝ → FrameBundle g, δ 0 = γ 0 ∧
      IsParallelFrameCurveOn g k δ (Ioo (-(a + ε / 2)) (a + ε / 2)) := by
  classical
  let c := a - ε / 4
  have hc : 0 < c := by dsimp [c]; linarith
  have hca : c < a := by dsimp [c]; linarith
  obtain ⟨ηL, hηL0, hηL⟩ := hlocal (γ (-c))
  obtain ⟨ηR, hηR0, hηR⟩ := hlocal (γ c)
  let L : ℝ → FrameBundle g := fun t => ηL (t + c)
  let R : ℝ → FrameBundle g := fun t => ηR (t + -c)
  have hL : IsParallelFrameCurveOn g k L (Ioo (-ε - c) (ε - c)) :=
    hηL.comp_add c
  have hR : IsParallelFrameCurveOn g k R (Ioo (-ε - -c) (ε - -c)) :=
    hηR.comp_add (-c)
  have htL : -c ∈ Ioo (-a) a ∩ Ioo (-ε - c) (ε - c) := by
    constructor <;> constructor <;> linarith
  have heqL : γ (-c) = L (-c) := by simpa only [L, neg_add_cancel] using hηL0.symm
  let ψ : ℝ → FrameBundle g := (Ioo (-a) a).piecewise γ L
  have hψ : IsParallelFrameCurveOn g k ψ (Ioo (-(a + ε / 2)) a) := by
    apply (hγ.piecewise hL htL heqL).mono
    intro t ht
    by_cases hta : -a < t
    · exact Or.inl ⟨hta, ht.2⟩
    · right
      constructor <;> dsimp [c] at * <;> linarith [ht.1, ht.2]
  have hψc : ψ c = γ c := by
    simp only [ψ, Set.piecewise, ite_eq_left (show c ∈ Ioo (-a) a from ⟨by linarith, hca⟩)]
  have htR : c ∈ Ioo (-(a + ε / 2)) a ∩ Ioo (-ε - -c) (ε - -c) := by
    constructor <;> constructor <;> linarith
  have heqR : ψ c = R c := by
    rw [hψc]
    simpa only [R, add_neg_cancel] using hηR0.symm
  let δ : ℝ → FrameBundle g := (Ioo (-(a + ε / 2)) a).piecewise ψ R
  refine ⟨δ, ?_, ?_⟩
  · have ha0 : 0 < a := lt_of_lt_of_le (half_pos hε) ha
    simp only [δ, ψ, Set.piecewise,
      ite_eq_left (show (0 : ℝ) ∈ Ioo (-(a + ε / 2)) a from ⟨by linarith, ha0⟩),
      ite_eq_left (show (0 : ℝ) ∈ Ioo (-a) a from ⟨by linarith, ha0⟩)]
  · apply (hψ.piecewise hR htR heqR).mono
    intro t ht
    by_cases hta : t < a
    · exact Or.inl ⟨ht.1, hta⟩
    · right
      constructor <;> dsimp [c] at * <;> linarith [ht.1, ht.2]

/-- On a compact base, a genuine parallel-frame curve through any prescribed
frame exists on every bounded open time interval. -/
theorem exists_parallelFrame_arbitrary_interval [CompactSpace M]
    (g : SmoothMetric M) (k : Fin 4) (e : FrameBundle g) (a : ℝ) :
    ∃ γ : ℝ → FrameBundle g, γ 0 = e ∧
      IsParallelFrameCurveOn g k γ (Ioo (-a) a) := by
  obtain ⟨ε, hε, hlocal⟩ := exists_uniform_parallelFrame_time g k
  let r (n : ℕ) : ℝ := ((n : ℝ) + 1) * ε / 2
  have hr (n : ℕ) : ε / 2 ≤ r n := by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hmul : 0 ≤ (n : ℝ) * ε := mul_nonneg hn hε.le
    dsimp [r]
    nlinarith
  have hstep (n : ℕ) : r (n + 1) = r n + ε / 2 := by
    simp only [r, Nat.cast_add, Nat.cast_one]
    ring
  have hfam (n : ℕ) : ∃ γ : ℝ → FrameBundle g, γ 0 = e ∧
      IsParallelFrameCurveOn g k γ (Ioo (-(r n)) (r n)) := by
    induction n with
    | zero =>
      obtain ⟨γ, h0, hγ⟩ := hlocal e
      refine ⟨γ, h0, hγ.mono ?_⟩
      apply Ioo_subset_Ioo <;> simp only [r, Nat.cast_zero, zero_add, one_mul] <;> linarith
    | succ n ih =>
      obtain ⟨γ, h0, hγ⟩ := ih
      obtain ⟨δ, hδ0, hδ⟩ := extend_parallelFrame_interval g k hε (hr n) hlocal hγ
      refine ⟨δ, hδ0.trans h0, ?_⟩
      simpa only [hstep n] using hδ
  obtain ⟨n, hn⟩ := exists_nat_gt (a / (ε / 2))
  have hhalf : 0 < ε / 2 := half_pos hε
  have han : a < (n : ℝ) * (ε / 2) := (div_lt_iff₀ hhalf).mp hn
  have har : a < r n := by dsimp [r]; nlinarith
  obtain ⟨γ, h0, hγ⟩ := hfam n
  exact ⟨γ, h0, hγ.mono (Ioo_subset_Ioo (by linarith) har.le)⟩

/-- Compactness and uniqueness extend the actual horizontal ODE for all
real times. Every derivative in the conclusion is still the original
coordinate velocity/parallel equation, not an assumed tensor identity. -/
theorem exists_global_intrinsic_parallelFrame [CompactSpace M]
    (g : SmoothMetric M) (k : Fin 4) (e : FrameBundle g) :
    ∃ Γ : ℝ → FrameBundle g, Γ 0 = e ∧ Continuous Γ ∧
      ∀ t, ParallelFrameCurveAt g Γ k t := by
  classical
  choose γ h0 hγ using exists_parallelFrame_arbitrary_interval g k e
  have compatible {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
      EqOn (γ a) (γ b) (Ioo (-a) a) := by
    apply (hγ a).eqOn_interval ((hγ b).mono (Ioo_subset_Ioo (by linarith) hab))
      (t := 0) ⟨by linarith, ha⟩
    exact (h0 a).trans (h0 b).symm
  let Γ : ℝ → FrameBundle g := fun t => γ (|t| + 1) t
  have hagrees (a : ℝ) (ha : 0 < a) : EqOn Γ (γ a) (Ioo (-a) a) := by
    intro t ht
    have hr : 0 < |t| + 1 := by positivity
    have htr : t ∈ Ioo (-(|t| + 1)) (|t| + 1) := by
      exact abs_lt.mp (lt_add_one _)
    rcases le_total a (|t| + 1) with hle | hle
    · exact (compatible ha hle ht).symm
    · exact compatible hr hle htr
  have hlocal (t : ℝ) : ContinuousAt Γ t ∧ ParallelFrameCurveAt g Γ k t := by
    let a := |t| + 1
    have ha : 0 < a := by dsimp [a]; positivity
    have ht : t ∈ Ioo (-a) a := by
      change t ∈ Ioo (-(|t| + 1)) (|t| + 1)
      exact abs_lt.mp (lt_add_one _)
    have hnear : Γ =ᶠ[𝓝 t] γ a := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
      exact hagrees a ha hs
    exact ⟨((hγ a).1.continuousAt (isOpen_Ioo.mem_nhds ht)).congr_of_eventuallyEq hnear,
      parallelFrameCurveAt_congr g ((hγ a).2 t ht) hnear.symm⟩
  refine ⟨Γ, ?_, continuous_iff_continuousAt.mpr (fun t => (hlocal t).1),
    fun t => (hlocal t).2⟩
  exact h0 (|0| + 1)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The autonomous group law for the actual complete horizontal curves.
Topology and invariant measure are treated separately. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [CompactSpace M]

def parallelFrameFlowMap (g : SmoothMetric M) (k : Fin 4)
    (t : ℝ) (e : FrameBundle g) : FrameBundle g :=
  (Classical.choose (exists_global_intrinsic_parallelFrame g k e)) t

theorem parallelFrameFlowMap_zero (g : SmoothMetric M) (k : Fin 4)
    (e : FrameBundle g) : parallelFrameFlowMap g k 0 e = e :=
  (Classical.choose_spec (exists_global_intrinsic_parallelFrame g k e)).1

theorem parallelFrameFlowMap_curve_continuous (g : SmoothMetric M) (k : Fin 4)
    (e : FrameBundle g) : Continuous (fun t => parallelFrameFlowMap g k t e) :=
  (Classical.choose_spec (exists_global_intrinsic_parallelFrame g k e)).2.1

theorem parallelFrameFlowMap_primitive (g : SmoothMetric M) (k : Fin 4)
    (e : FrameBundle g) (t : ℝ) :
    ParallelFrameCurveAt g (fun s => parallelFrameFlowMap g k s e) k t :=
  (Classical.choose_spec (exists_global_intrinsic_parallelFrame g k e)).2.2 t

theorem parallelFrameFlowMap_add (g : SmoothMetric M) (k : Fin 4)
    (s t : ℝ) (e : FrameBundle g) :
    parallelFrameFlowMap g k (s + t) e =
      parallelFrameFlowMap g k s (parallelFrameFlowMap g k t e) := by
  let γ : ℝ → FrameBundle g := fun u => parallelFrameFlowMap g k (u + t) e
  let η : ℝ → FrameBundle g := fun u =>
    parallelFrameFlowMap g k u (parallelFrameFlowMap g k t e)
  have hγc : Continuous γ :=
    (parallelFrameFlowMap_curve_continuous g k e).comp
      (continuous_id.add continuous_const)
  have hηc : Continuous η :=
    parallelFrameFlowMap_curve_continuous g k (parallelFrameFlowMap g k t e)
  have hγ (u : ℝ) : ParallelFrameCurveAt g γ k u :=
    parallelFrameCurveAt_comp_add g (fun v => parallelFrameFlowMap g k v e) k u t
      (parallelFrameFlowMap_primitive g k e (u + t))
  have hη (u : ℝ) : ParallelFrameCurveAt g η k u :=
    parallelFrameFlowMap_primitive g k (parallelFrameFlowMap g k t e) u
  have h0 : γ 0 = η 0 := by simp only [γ, η, zero_add, parallelFrameFlowMap_zero]
  exact congrFun (intrinsic_parallelFrame_unique_global g γ η k hγc hηc hγ hη h0) s

theorem parallelFrameFlowMap_neg_left (g : SmoothMetric M) (k : Fin 4)
    (t : ℝ) (e : FrameBundle g) :
    parallelFrameFlowMap g k (-t) (parallelFrameFlowMap g k t e) = e := by
  rw [← parallelFrameFlowMap_add, neg_add_cancel, parallelFrameFlowMap_zero]

theorem parallelFrameFlowMap_neg_right (g : SmoothMetric M) (k : Fin 4)
    (t : ℝ) (e : FrameBundle g) :
    parallelFrameFlowMap g k t (parallelFrameFlowMap g k (-t) e) = e := by
  rw [← parallelFrameFlowMap_add, add_neg_cancel, parallelFrameFlowMap_zero]

/-- The inverse at time `t` is the actual horizontal curve at time `-t`. -/
def parallelFrameEquiv (g : SmoothMetric M) (k : Fin 4) (t : ℝ) :
    FrameBundle g ≃ FrameBundle g where
  toFun := parallelFrameFlowMap g k t
  invFun := parallelFrameFlowMap g k (-t)
  left_inv := parallelFrameFlowMap_neg_left g k t
  right_inv := parallelFrameFlowMap_neg_right g k t

end
end PositiveEinsteinFour.Geometry
end


section

/-! Classical geometric hypotheses for the canonical frame measure, with
averaging, positive support and orientation preservation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M]

/-- Normalized Ricci curvature supplies the contraction field of the
parallel-frame calculus. -/
def ParallelMetricData.ofParallelFlows (g : SmoothMetric M)
    (μ : Measure (FrameBundle g)) (flow : Fin 4 → FrameFlow g μ)
    (hcurve : ∀ k t e, ParallelFrameCurveAt g (fun s => (flow k).map s e) k t)
    (hRic : RicciThree g) : ParallelMetricData g μ where
  flow := flow
  parallelCurve := hcurve
  ricci e j a := by
    rw [frameCurvature_ricci]
    change (e.frame.matrixᵀ * chartRicci g e.base * e.frame.matrix) j a = _
    rw [hRic e.base, mul_smul_comm, smul_mul_assoc, e.frame.orthonormal]
    simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
      mul_ite, mul_one, mul_zero]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Joint continuity of the actual complete horizontal flow. Local Picard
flows agree by uniqueness; compactness gives a common time for continuous
slices, and the proved group law extends this to every real time. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [CompactSpace M]

theorem parallelFrameFlowMap_eq_local (g : SmoothMetric M) (k : Fin 4)
    {U : Set (FrameBundle g)} {ε : ℝ} (hε : 0 < ε)
    {Φ : FrameBundle g × ℝ → FrameBundle g}
    (hΦ : ContinuousOn Φ (U ×ˢ Ioo (-ε) ε))
    (hcurve : ∀ f ∈ U, Φ (f, 0) = f ∧ ∀ t ∈ Ioo (-ε) ε,
      ParallelFrameCurveAt g (fun s => Φ (f, s)) k t)
    {f : FrameBundle g} (hf : f ∈ U) {t : ℝ} (ht : t ∈ Ioo (-ε) ε) :
    parallelFrameFlowMap g k t f = Φ (f, t) := by
  have hz : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, hε⟩
  have hglobal : IsParallelFrameCurveOn g k
      (fun s => parallelFrameFlowMap g k s f) (Ioo (-ε) ε) :=
    ⟨(parallelFrameFlowMap_curve_continuous g k f).continuousOn,
      fun s _ => parallelFrameFlowMap_primitive g k f s⟩
  have hlocal : IsParallelFrameCurveOn g k (fun s => Φ (f, s)) (Ioo (-ε) ε) :=
    ⟨hΦ.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun s hs => ⟨hf, hs⟩), (hcurve f hf).2⟩
  exact hglobal.eqOn_interval hlocal hz
    ((parallelFrameFlowMap_zero g k f).trans (hcurve f hf).1.symm) ht

theorem parallelFrameFlowMap_continuousAt_zero (g : SmoothMetric M) (k : Fin 4)
    (e : FrameBundle g) :
    ContinuousAt (fun p : ℝ × FrameBundle g => parallelFrameFlowMap g k p.1 p.2)
      (0, e) := by
  obtain ⟨U, hU, heU, ε, hε, Φ, hΦ, hcurve⟩ :=
    exists_continuous_local_intrinsic_parallelFrame_flow g e k
  have hz : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, hε⟩
  have hc : ContinuousAt (fun p : ℝ × FrameBundle g => Φ (p.2, p.1)) (0, e) :=
    (hΦ.continuousAt ((hU.prod isOpen_Ioo).mem_nhds ⟨heU, hz⟩)).comp
      (continuous_snd.prodMk continuous_fst).continuousAt
  apply hc.congr_of_eventuallyEq
  have hn : Ioo (-ε) ε ×ˢ U ∈ 𝓝 ((0 : ℝ), e) :=
    (isOpen_Ioo.prod hU).mem_nhds ⟨hz, heU⟩
  filter_upwards [hn] with p hp
  exact parallelFrameFlowMap_eq_local g k hε hΦ hcurve hp.2 hp.1

theorem parallelFrameFlowMap_uniform_continuous_time
    (g : SmoothMetric M) (k : Fin 4) :
    ∃ δ > (0 : ℝ), ∀ t : ℝ, |t| < δ → Continuous (parallelFrameFlowMap g k t) := by
  classical
  let : CompactSpace (FrameBundle g) := actual_compactFrameBundle g
  choose U hU heU ε hε Φ hΦ hcurve using
    (fun e => exists_continuous_local_intrinsic_parallelFrame_flow g e k)
  obtain ⟨s, hs⟩ := finite_cover_nhds
    (fun e : FrameBundle g => (hU e).mem_nhds (heU e))
  have common (s : Finset (FrameBundle g)) :
      ∃ δ > (0 : ℝ), ∀ e ∈ s, δ ≤ ε e := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, by simp⟩
    | @insert a s ha ih =>
      obtain ⟨δ, hδ, hb⟩ := ih
      refine ⟨min δ (ε a), lt_min hδ (hε a), ?_⟩
      intro e he
      rcases Finset.mem_insert.mp he with rfl | he
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hb e he)
  obtain ⟨δ, hδ, hb⟩ := common s
  refine ⟨δ, hδ, fun t ht => continuous_iff_continuousAt.mpr fun e => ?_⟩
  have he : e ∈ ⋃ c ∈ s, U c := by rw [hs]; trivial
  obtain ⟨c, hc, hec⟩ := mem_iUnion₂.mp he
  have htc : t ∈ Ioo (-(ε c)) (ε c) := by
    have hbound := hb c hc
    rcases abs_lt.mp ht with ⟨hl, hr⟩
    constructor <;> linarith
  have hlocal : ContinuousAt (fun f : FrameBundle g => Φ c (f, t)) e :=
    ((hΦ c).continuousAt (((hU c).prod isOpen_Ioo).mem_nhds ⟨hec, htc⟩)).comp
      (continuous_id.prodMk continuous_const).continuousAt
  apply hlocal.congr_of_eventuallyEq
  filter_upwards [(hU c).mem_nhds hec] with f hf
  exact parallelFrameFlowMap_eq_local g k (hε c) (hΦ c) (hcurve c) hf htc

theorem parallelFrameFlowMap_continuous_slice (g : SmoothMetric M) (k : Fin 4)
    (t : ℝ) : Continuous (parallelFrameFlowMap g k t) := by
  obtain ⟨δ, hδ, hlocal⟩ := parallelFrameFlowMap_uniform_continuous_time g k
  obtain ⟨n, hn⟩ := exists_nat_gt (|t| / δ)
  have hn0 : 0 < (n : ℝ) := lt_of_le_of_lt (div_nonneg (abs_nonneg t) hδ.le) hn
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hn0
  have hstep : |t / (n : ℝ)| < δ := by
    rw [abs_div, abs_of_pos hn0, div_lt_iff₀ hn0]
    have hm := (div_lt_iff₀ hδ).mp hn
    nlinarith
  have hcont (m : ℕ) : Continuous (parallelFrameFlowMap g k ((m : ℝ) * (t / n))) := by
    induction m with
    | zero =>
      simp only [Nat.cast_zero, zero_mul]
      have hId : parallelFrameFlowMap g k 0 = id :=
        funext (parallelFrameFlowMap_zero g k)
      rw [hId]
      exact continuous_id
    | succ m ih =>
      have heq : (fun e : FrameBundle g =>
          parallelFrameFlowMap g k (((m + 1 : ℕ) : ℝ) * (t / n)) e) =
          (fun e => parallelFrameFlowMap g k ((m : ℝ) * (t / n))
            (parallelFrameFlowMap g k (t / n) e)) := by
        funext e
        rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, parallelFrameFlowMap_add]
      change Continuous (fun e : FrameBundle g =>
        parallelFrameFlowMap g k (((m + 1 : ℕ) : ℝ) * (t / n)) e)
      rw [heq]
      exact ih.comp (hlocal (t / n) hstep)
  have hnval : (n : ℝ) * (t / n) = t := by field_simp [hnne]
  simpa only [hnval] using hcont n

theorem parallelFrameFlowMap_continuous (g : SmoothMetric M) (k : Fin 4) :
    Continuous (fun p : ℝ × FrameBundle g => parallelFrameFlowMap g k p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  have hshift : ContinuousAt (fun q : ℝ × FrameBundle g => (q.1 - p.1, q.2)) p :=
    (continuous_fst.sub continuous_const).continuousAt.prodMk continuous_snd.continuousAt
  have hzero : ContinuousAt (fun q : ℝ × FrameBundle g =>
      parallelFrameFlowMap g k (q.1 - p.1) q.2) p := by
    have hz : ContinuousAt (fun q : ℝ × FrameBundle g =>
        parallelFrameFlowMap g k q.1 q.2) (p.1 - p.1, p.2) := by
      simpa only [sub_self] using parallelFrameFlowMap_continuousAt_zero g k p.2
    exact hz.comp (x := p) hshift
  have h := (parallelFrameFlowMap_continuous_slice g k p.1).continuousAt.comp hzero
  apply h.congr
  filter_upwards [] with q
  change parallelFrameFlowMap g k p.1
    (parallelFrameFlowMap g k (q.1 - p.1) q.2) = parallelFrameFlowMap g k q.1 q.2
  rw [← parallelFrameFlowMap_add, add_sub_cancel]

/-- The actual parallel flow gives homeomorphisms, with inverse at negative time. -/
def parallelFrameHomeomorph (g : SmoothMetric M) (k : Fin 4) (t : ℝ) :
    FrameBundle g ≃ₜ FrameBundle g where
  toEquiv := parallelFrameEquiv g k t
  continuous_toFun := parallelFrameFlowMap_continuous_slice g k t
  continuous_invFun := parallelFrameFlowMap_continuous_slice g k (-t)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Reflection equivariance of the constructed complete parallel-frame flow.
The identity follows from the primitive coordinate ODE and intrinsic uniqueness;
it does not use a measure-preservation assumption. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [CompactSpace M]

theorem parallelFrameFlowMap_reflection (g : SmoothMetric M) (k : Fin 4)
    (t : ℝ) (e : FrameBundle g) :
    frameReflection (parallelFrameFlowMap g k t e) =
      parallelFrameFlowMap g k (orientationSign k * t) (frameReflection e) := by
  let γ : ℝ → FrameBundle g := fun s =>
    frameReflection (parallelFrameFlowMap g k (orientationSign k * s) e)
  let η : ℝ → FrameBundle g := fun s =>
    parallelFrameFlowMap g k s (frameReflection e)
  have hγc : Continuous γ :=
    (continuous_frameReflection g).comp
      ((parallelFrameFlowMap_curve_continuous g k e).comp
        (continuous_const.mul continuous_id))
  have hηc : Continuous η :=
    parallelFrameFlowMap_curve_continuous g k (frameReflection e)
  have hγ (s : ℝ) : ParallelFrameCurveAt g γ k s :=
    parallelFrameCurveAt_reflection g (fun u => parallelFrameFlowMap g k u e) k s
      (parallelFrameFlowMap_primitive g k e (orientationSign k * s))
  have hη (s : ℝ) : ParallelFrameCurveAt g η k s :=
    parallelFrameFlowMap_primitive g k (frameReflection e) s
  have h0 : γ 0 = η 0 := by
    simp only [γ, η, mul_zero, parallelFrameFlowMap_zero]
  have heq := intrinsic_parallelFrame_unique_global g γ η k hγc hηc hγ hη h0
  have hsign : orientationSign k * (orientationSign k * t) = t := by
    rw [← mul_assoc, ← pow_two, orientationSign_sq, one_mul]
  simpa only [γ, η, hsign] using congrFun heq (orientationSign k * t)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Rotating the normal frame while fixing its distinguished direction
commutes with the actual horizontal flow. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem frameChartMatrix_rotate (g : SmoothMetric M) (c : M)
    (e : FrameBundle g) (Q : OrthogonalFour) :
    frameChartMatrix g c (e.rotate Q) = frameChartMatrix g c e * Q.val := by
  rw [frameChartMatrix_eq, frameChartMatrix_eq]
  change chartTransitionMatrix e.base c (chartAt FourSpace e.base e.base) *
      (e.frame.matrix * Q.val) =
    (chartTransitionMatrix e.base c (chartAt FourSpace e.base e.base) *
      e.frame.matrix) * Q.val
  exact (Matrix.mul_assoc _ _ _).symm

theorem rotated_column (E : Mat4) (Q : OrthogonalFour) (k : Fin 4)
    (hQ : ∀ r, Q.val r k = (1 : Mat4) r k) (i : Fin 4) :
    (E * Q.val) i k = E i k := by
  simp only [Matrix.mul_apply, hQ, Matrix.one_apply]
  simp

theorem parallelFrameCurveAt_rotate (g : SmoothMetric M)
    (γ : ℝ → FrameBundle g) (k : Fin 4) (Q : OrthogonalFour)
    (hQ : ∀ r, Q.val r k = (1 : Mat4) r k) (t : ℝ)
    (h : ParallelFrameCurveAt g γ k t) :
    ParallelFrameCurveAt g (fun s => (γ s).rotate Q) k t := by
  let c := (γ t).base
  let E (s : ℝ) := frameChartMatrix g c (γ s)
  let C : Mat4 := ∑ r, E t r k • connectionMatrix g c r
    (chartAt FourSpace c (γ t).base)
  have hcol (r : Fin 4) : frameChartMatrix g c ((γ t).rotate Q) r k = E t r k := by
    rw [frameChartMatrix_rotate]
    exact rotated_column (E t) Q k hQ r
  constructor
  · have he : WithLp.toLp 2 (fun r => frameChartMatrix g c ((γ t).rotate Q) r k) =
        WithLp.toLp 2 (fun r => E t r k) := by
      ext r
      exact hcol r
    change HasDerivAt (fun s => chartAt FourSpace c (γ s).base)
      (WithLp.toLp 2 (fun r => frameChartMatrix g c ((γ t).rotate Q) r k)) t
    rw [he]
    exact h.velocity
  · intro i j
    have hs := HasDerivAt.fun_sum (fun a (_ : a ∈ Finset.univ) =>
      (h.parallel i a).mul_const (Q.val a j))
    have hp : HasDerivAt (fun s => (E s * Q.val) i j)
        ((-(C * E t) * Q.val) i j) t := by
      simpa only [E, C, Matrix.mul_apply, Matrix.neg_apply] using hs
    have he : (-((∑ r, frameChartMatrix g c ((γ t).rotate Q) r k •
        connectionMatrix g c r (chartAt FourSpace c (γ t).base)) *
          frameChartMatrix g c ((γ t).rotate Q)) i j) =
        (-(C * E t) * Q.val) i j := by
      simp_rw [hcol]
      rw [frameChartMatrix_rotate]
      change (-(C * (E t * Q.val))) i j = (-(C * E t) * Q.val) i j
      rw [Matrix.neg_mul, Matrix.mul_assoc]
    change HasDerivAt (fun s => frameChartMatrix g c ((γ s).rotate Q) i j)
      (-((∑ r, frameChartMatrix g c ((γ t).rotate Q) r k •
        connectionMatrix g c r (chartAt FourSpace c (γ t).base)) *
          frameChartMatrix g c ((γ t).rotate Q)) i j) t
    rw [he]
    have hf : (fun s => frameChartMatrix g c ((γ s).rotate Q) i j) =
        fun s => (E s * Q.val) i j := by
      funext s
      exact congrFun (congrFun (frameChartMatrix_rotate g c (γ s) Q) i) j
    rw [hf]
    exact hp

theorem parallelFrameFlowMap_rotate [T2Space M] [CompactSpace M]
    (g : SmoothMetric M) (k : Fin 4) (Q : OrthogonalFour)
    (hQ : ∀ r, Q.val r k = (1 : Mat4) r k) (t : ℝ) (e : FrameBundle g) :
    (parallelFrameFlowMap g k t e).rotate Q =
      parallelFrameFlowMap g k t (e.rotate Q) := by
  let γ : ℝ → FrameBundle g := fun s => (parallelFrameFlowMap g k s e).rotate Q
  let η : ℝ → FrameBundle g := fun s => parallelFrameFlowMap g k s (e.rotate Q)
  have hγc : Continuous γ := (continuous_frameRotate g).comp
    ((parallelFrameFlowMap_curve_continuous g k e).prodMk continuous_const)
  have hηc : Continuous η := parallelFrameFlowMap_curve_continuous g k (e.rotate Q)
  have hγ (s : ℝ) : ParallelFrameCurveAt g γ k s :=
    parallelFrameCurveAt_rotate g (fun u => parallelFrameFlowMap g k u e) k Q hQ s
      (parallelFrameFlowMap_primitive g k e s)
  have hη (s : ℝ) : ParallelFrameCurveAt g η k s :=
    parallelFrameFlowMap_primitive g k (e.rotate Q) s
  have h0 : γ 0 = η 0 := by simp only [γ, η, parallelFrameFlowMap_zero]
  exact congrFun (intrinsic_parallelFrame_unique_global g γ η k hγc hηc hγ hη h0) t

end
end PositiveEinsteinFour.Geometry
end


section

/-! Strict positivity of the Einstein constant from the concrete sectional
curvature predicate. No Ricci-positivity hypothesis is retained. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {c : M}

theorem OrthonormalFrame.map_coordinateVector (e : OrthonormalFrame g c) (i : Fin 4) :
    e.map (coordinateVector i) = e.vector i := by
  ext a
  simp [OrthonormalFrame.map_apply, coordinateVector]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Positive constant multiplication of an actual smooth Riemannian metric.
The constructor and chart-tensor identities discharge the local part of the
classical scaling input. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bornology
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def rescaleMetric (g : SmoothMetric M) (c : ℝ) (hc : 0 < c) : SmoothMetric M where
  inner x := c • g.inner x
  symm x v w := by
    change c * g.inner x v w = c * g.inner x w v
    rw [g.symm]
  pos x v hv := by
    change 0 < c * g.inner x v v
    exact mul_pos hc (g.pos x v hv)
  isVonNBounded x := by
    let r := Real.sqrt c
    have hr : r ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hc)
    have hb := (g.isVonNBounded x).image
      (r⁻¹ • ContinuousLinearMap.id ℝ (TangentSpace I4 x))
    apply hb.subset
    intro v hv
    refine ⟨r • v, ?_, ?_⟩
    · change g.inner x (r • v) (r • v) < 1
      simp only [map_smul, _root_.smul_apply, smul_eq_mul]
      rw [← mul_assoc, ← pow_two, Real.sq_sqrt hc.le]
      exact hv
    · simp [smul_smul, hr]
  contMDiff := g.contMDiff.const_smul_section

@[simp] theorem rescaleMetric_inner (g : SmoothMetric M) (c : ℝ) (hc : 0 < c)
    (x : M) (v w : TangentSpace I4 x) :
    (rescaleMetric g c hc).inner x v w = c * g.inner x v w := rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! The compact group of oriented normal-frame rotations. Its elements
fix the first frame direction, so its action commutes with the actual
first parallel flow. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular Matrix MeasureTheory Set
open scoped BigOperators Manifold ContDiff

noncomputable section

theorem orientedDirection_one (q : Directions) : orientedDirection 1 q = q := by
  apply Subtype.ext
  ext i
  change (∑ j, (1 : Mat4) i j * q.val j) = q.val i
  simp [Matrix.one_apply]

def normalRotationSubgroup : Subgroup OrientedOrthogonalFour where
  carrier := {Q | orientedDirection Q firstDirection = firstDirection}
  one_mem' := orientedDirection_one _
  mul_mem' := by
    intro P Q hP hQ
    change orientedDirection (P * Q) firstDirection = firstDirection
    rw [orientedDirection_mul, hQ, hP]
  inv_mem' := by
    intro Q hQ
    have h := congrArg (orientedDirection Q⁻¹) hQ
    rw [← orientedDirection_mul, inv_mul_cancel, orientedDirection_one] at h
    exact h.symm

abbrev NormalFrameRotation := normalRotationSubgroup

theorem normalFrameRotation_column (Q : NormalFrameRotation) (i : Fin 4) :
    Q.val.val i 0 = (1 : Mat4) i 0 := by
  have h := congrArg (fun q : Directions => q.val i) Q.property
  change (∑ j, Q.val.val i j * firstDirection.val j) = firstDirection.val i at h
  simpa only [firstDirection_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true, Matrix.one_apply] using h

theorem mem_normalRotationSubgroup_of_column (Q : OrientedOrthogonalFour)
    (hQ : ∀ i, Q.val i 0 = (1 : Mat4) i 0) : Q ∈ normalRotationSubgroup := by
  apply Subtype.ext
  ext i
  change (∑ j, Q.val i j * firstDirection.val j) = firstDirection.val i
  simp only [firstDirection_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true, hQ, Matrix.one_apply]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def normalFrameRotate {g : SmoothMetric M} (e : FrameBundle g)
    (Q : NormalFrameRotation) : FrameBundle g :=
  e.rotate (orientedToOrthogonal Q.val)

def normalFrameChange {g : SmoothMetric M} {c : M}
    (e f : OrthonormalFrame g c) (hdet : 0 < e.matrix.det * f.matrix.det)
    (hfirst : e.vector 0 = f.vector 0) : NormalFrameRotation :=
  ⟨orientedFrameChange e f hdet, mem_normalRotationSubgroup_of_column _
    (fun i => e.changeMatrix_first f hfirst i)⟩

theorem normalFrameRotate_change {g : SmoothMetric M} {c : M}
    (e f : OrthonormalFrame g c) (hdet : 0 < e.matrix.det * f.matrix.det)
    (hfirst : e.vector 0 = f.vector 0) :
    normalFrameRotate (⟨c, e⟩ : FrameBundle g) (normalFrameChange e f hdet hfirst) =
      (⟨c, f⟩ : FrameBundle g) :=
  orientedFrameMap_change e f hdet

theorem normalFrameRotate_first {g : SmoothMetric M} (e : FrameBundle g)
    (Q : NormalFrameRotation) : (normalFrameRotate e Q).frame.vector 0 = e.frame.vector 0 := by
  change (e.frame.rotate (orientedToOrthogonal Q.val)).vector 0 = e.frame.vector 0
  rw [OrthonormalFrame.rotate_vector]
  simp only [orientedToOrthogonal, normalFrameRotation_column, Matrix.one_apply,
    ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]

theorem parallelFrameFlowMap_normalFrameRotate [T2Space M] [CompactSpace M]
    (g : SmoothMetric M) (t : ℝ) (e : FrameBundle g) (Q : NormalFrameRotation) :
    normalFrameRotate (parallelFrameFlowMap g 0 t e) Q =
      parallelFrameFlowMap g 0 t (normalFrameRotate e Q) :=
  parallelFrameFlowMap_rotate g 0 (orientedToOrthogonal Q.val)
    (normalFrameRotation_column Q) t e

/-- The transported base point and first vector are independent of the
chosen positive normal frame. This gives the descent of the constructed
frame flow to geodesic data. -/
theorem parallelFrameFlowMap_same_first [T2Space M] [CompactSpace M]
    (g : SmoothMetric M) {c : M} (e f : OrthonormalFrame g c)
    (hdet : 0 < e.matrix.det * f.matrix.det) (hfirst : e.vector 0 = f.vector 0)
    (t : ℝ) :
    (parallelFrameFlowMap g 0 t ⟨c, e⟩).base =
        (parallelFrameFlowMap g 0 t ⟨c, f⟩).base ∧
      (parallelFrameFlowMap g 0 t ⟨c, e⟩).frame.vector 0 =
        (parallelFrameFlowMap g 0 t ⟨c, f⟩).frame.vector 0 := by
  let Q := normalFrameChange e f hdet hfirst
  have heq : normalFrameRotate (parallelFrameFlowMap g 0 t ⟨c, e⟩) Q =
      parallelFrameFlowMap g 0 t ⟨c, f⟩ := by
    rw [parallelFrameFlowMap_normalFrameRotate]
    change parallelFrameFlowMap g 0 t
      (normalFrameRotate ⟨c, e⟩ (normalFrameChange e f hdet hfirst)) = _
    rw [normalFrameRotate_change]
  constructor
  · have h := congrArg (fun a : FrameBundle g => a.base) heq
    exact h
  · have h := congrArg (fun a : FrameBundle g => a.frame.vector 0) heq
    rw [normalFrameRotate_first] at h
    exact h

end
end PositiveEinsteinFour.Geometry
end


section

/-! Complete horizontal curves give parallel-frame calculus. Preservation of
the specified measure is the Brin--Karcher hypothesis, Section 1, p. 275. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

def actualFrameFlow (g : SmoothMetric M) (μ : Measure (FrameBundle g))
    (hpres : ∀ k t, MeasurePreserving (parallelFrameFlowMap g k t) μ μ)
    (k : Fin 4) : FrameFlow g μ where
  map t := (parallelFrameHomeomorph g k t).toMeasurableEquiv
  continuous := parallelFrameFlowMap_continuous g k
  preserves := hpres k

@[simp] theorem actualFrameFlow_apply (g : SmoothMetric M)
    (μ : Measure (FrameBundle g))
    (hpres : ∀ k t, MeasurePreserving (parallelFrameFlowMap g k t) μ μ)
    (k : Fin 4) (t : ℝ) (e : FrameBundle g) :
    (actualFrameFlow g μ hpres k).map t e = parallelFrameFlowMap g k t e := rfl

def actualParallelMetricData (g : SmoothMetric M) (μ : Measure (FrameBundle g))
    (hpres : ∀ k t, MeasurePreserving (parallelFrameFlowMap g k t) μ μ)
    (hRic : RicciThree g) : ParallelMetricData g μ :=
  ParallelMetricData.ofParallelFlows g μ (actualFrameFlow g μ hpres)
    (fun k t e => parallelFrameFlowMap_primitive g k e t) hRic

theorem actualParallelMetricData_reflection (g : SmoothMetric M)
    (μ : Measure (FrameBundle g))
    (hpres : ∀ k t, MeasurePreserving (parallelFrameFlowMap g k t) μ μ)
    (hRic : RicciThree g) :
    ParallelReflection (actualParallelMetricData g μ hpres hRic).toMetricGreenData :=
  parallelFrameFlowMap_reflection g

end
end PositiveEinsteinFour.Geometry
end


section

/-! Intrinsic unit tangent vectors and the actual first-vector projection
from oriented frames. Every unit vector has a positive orthonormal
completion, constructed with the explicit quaternionic completion. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Angular Bundle MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem OrthonormalFrame.inner_map_self {g : SmoothMetric M} {c : M}
    (e : OrthonormalFrame g c) (v : FourSpace) :
    g.inner c (e.map v) (e.map v) = ‖v‖ ^ 2 := by
  rw [← chartMetric_pairing]
  change (e.matrix *ᵥ WithLp.ofLp v) ⬝ᵥ
    (chartMetric g c *ᵥ (e.matrix *ᵥ WithLp.ofLp v)) = _
  rw [Matrix.mulVec_mulVec, dotProduct_comm, Matrix.dotProduct_mulVec,
    ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, ← Matrix.mul_assoc,
    e.orthonormal, Matrix.one_mulVec, EuclideanSpace.real_norm_sq_eq]
  simp only [dotProduct, pow_two]

theorem OrthonormalFrame.inner_vector_self {g : SmoothMetric M} {c : M}
    (e : OrthonormalFrame g c) (i : Fin 4) :
    g.inner c (e.vector i) (e.vector i) = 1 := by
  rw [← e.map_coordinateVector i, e.inner_map_self]
  simp [coordinateVector]

structure UnitTangentBundle (g : SmoothMetric M) where
  base : M
  vector : TangentSpace I4 base
  unit : g.inner base vector vector = 1

theorem unitTangent_ext {g : SmoothMetric M} {u v : UnitTangentBundle g}
    (hbase : u.base = v.base) (hvector : u.vector = v.vector) : u = v := by
  cases u with
  | mk x a ha =>
    cases v with
    | mk y b hb =>
      dsimp at hbase hvector
      subst y
      subst b
      rfl

def unitTangentRealization {g : SmoothMetric M} (u : UnitTangentBundle g) :
    TangentBundle I4 M := ⟨u.base, u.vector⟩

instance instTopologicalSpaceUnitTangentBundle (g : SmoothMetric M) : TopologicalSpace (UnitTangentBundle g) :=
  TopologicalSpace.induced unitTangentRealization inferInstance

theorem unitTangentRealization_injective (g : SmoothMetric M) :
    Function.Injective (unitTangentRealization : UnitTangentBundle g → TangentBundle I4 M) := by
  rintro ⟨x, v, hv⟩ ⟨y, w, hw⟩ h
  have hxy : x = y := congrArg Bundle.TotalSpace.proj h
  subst y
  have hvw : v = w := TotalSpace.mk_injective x h
  subst w
  rfl

def unitTangentOfFrame {g : SmoothMetric M} (e : FrameBundle g) : UnitTangentBundle g :=
  ⟨e.base, e.frame.vector 0, e.frame.inner_vector_self 0⟩

theorem continuous_unitTangentOfFrame (g : SmoothMetric M) :
    Continuous (unitTangentOfFrame : FrameBundle g → UnitTangentBundle g) := by
  apply continuous_induced_rng.mpr
  exact (continuous_apply 0).comp (continuous_snd.comp (continuous_frameRealization g))

/-- Every intrinsic unit tangent vector admits an oriented orthonormal
completion, so the first-vector projection loses only the normal frame. -/
theorem exists_positive_unitTangent_frame (g : SmoothMetric M) (o : FrameOrientation g)
    (u : UnitTangentBundle g) :
    ∃ e : FrameBundle g, e ∈ o.positive ∧ unitTangentOfFrame e = u := by
  let e := o.frame u.base
  obtain ⟨v, hv⟩ := (LinearMap.surjective_of_injective e.map_injective) u.vector
  have hn : ‖v‖ = 1 := by
    have h := e.inner_map_self v
    rw [hv, u.unit] at h
    nlinarith [norm_nonneg v]
  let q : Directions := ⟨v, hn⟩
  let f := (⟨u.base, e⟩ : FrameBundle g).rotate
    (orientedToOrthogonal (directionOrientedMatrix q))
  refine ⟨f, frameRotate_oriented_positive o _ (o.frame_positive _) _, ?_⟩
  apply unitTangentRealization_injective g
  change (⟨u.base, (e.turn q).vector 0⟩ : TangentBundle I4 M) = ⟨u.base, u.vector⟩
  exact congrArg (fun w : TangentSpace I4 u.base =>
    (⟨u.base, w⟩ : TangentBundle I4 M)) ((e.turn_first q).trans hv)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual Jacobi equation along the constructed parallel-frame flow.
Existence and the compact-interval bounds are derived from the metric
curvature and the linear ODE theorem, with no Jacobi-existence input. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory Jacobi Set
open scoped Manifold ContDiff _root_.Topology NNReal Matrix.Norms.L2Operator

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

def jacobiZeroData (g : SmoothMetric M) (hRic : RicciThree g) :
    ParallelMetricData g (0 : Measure (FrameBundle g)) :=
  actualParallelMetricData g 0 (fun k t =>
    ⟨(parallelFrameHomeomorph g k t).continuous.measurable, by simp⟩) hRic

def actualJacobiCurvature (g : SmoothMetric M) (e : FrameBundle g)
    (s : ℝ) : NormalMatrix :=
  1 + frameCurvatureField g (parallelFrameFlowMap g 0 s e)

def actualJacobiCurvatureDerivative (g : SmoothMetric M) (e : FrameBundle g)
    (s : ℝ) : NormalMatrix :=
  frameCurvatureDerivative g (parallelFrameFlowMap g 0 s e)

theorem actual_frameCurvature_continuous (g : SmoothMetric M) (hRic : RicciThree g) :
    Continuous (frameCurvatureField g) := by
  let d := (jacobiZeroData g hRic).toMetricGreenData
  exact d.continuousCurvatureField
    (d.oppositeData (actualParallelMetricData_reflection g 0 _ hRic) hRic) hRic

theorem actual_frameCurvatureDerivative_continuous (g : SmoothMetric M)
    (hRic : RicciThree g) : Continuous (frameCurvatureDerivative g) := by
  let d := (jacobiZeroData g hRic).toMetricGreenData
  exact d.continuousCurvatureDerivative
    (d.oppositeData (actualParallelMetricData_reflection g 0 _ hRic) hRic)

theorem actualJacobiCurvature_continuous (g : SmoothMetric M) (hRic : RicciThree g)
    (e : FrameBundle g) : Continuous (actualJacobiCurvature g e) :=
  continuous_const.add ((actual_frameCurvature_continuous g hRic).comp
    ((parallelFrameFlowMap_continuous g 0).comp
      (continuous_id.prodMk continuous_const)))

theorem actualJacobiCurvatureDerivative_continuous (g : SmoothMetric M)
    (hRic : RicciThree g) (e : FrameBundle g) :
    Continuous (actualJacobiCurvatureDerivative g e) :=
  (actual_frameCurvatureDerivative_continuous g hRic).comp
    ((parallelFrameFlowMap_continuous g 0).comp
      (continuous_id.prodMk continuous_const))

theorem actualJacobiCurvature_hasDerivAt (g : SmoothMetric M) (hRic : RicciThree g)
    (e : FrameBundle g) (s : ℝ) :
    HasDerivAt (actualJacobiCurvature g e) (actualJacobiCurvatureDerivative g e s) s := by
  let d := (jacobiZeroData g hRic).toMetricGreenData
  have hd := d.derivativeCurvatureField
    (d.oppositeData (actualParallelMetricData_reflection g 0 _ hRic) hRic) hRic s e
  have hC : HasDerivAt
      (fun r => frameCurvatureField g (parallelFrameFlowMap g 0 r e))
      (frameCurvatureDerivative g (parallelFrameFlowMap g 0 s e)) s := by
    apply hasDerivAt_iff_tendsto_slope.mpr
    exact hd.tendsto_slope
  exact hC.const_add 1

theorem actualJacobiCurvature_symmetric (g : SmoothMetric M) (e : FrameBundle g)
    (s : ℝ) : (actualJacobiCurvature g e s)ᵀ = actualJacobiCurvature g e s :=
  frameJacobiMatrix_symmetric _

theorem actualJacobiCurvature_bounded (g : SmoothMetric M) (hRic : RicciThree g) :
    ∃ K : ℝ≥0, ∀ e : FrameBundle g, ∀ s : ℝ, ‖actualJacobiCurvature g e s‖ ≤ K := by
  let : CompactSpace (FrameBundle g) := actual_compactFrameBundle g
  have hC : Continuous (fun e : FrameBundle g => (1 : NormalMatrix) + frameCurvatureField g e) :=
    continuous_const.add (actual_frameCurvature_continuous g hRic)
  obtain ⟨K, hK⟩ := isCompact_univ.exists_bound_of_continuousOn hC.continuousOn
  refine ⟨⟨max 0 K, le_max_left _ _⟩, fun e s => ?_⟩
  exact (hK (parallelFrameFlowMap g 0 s e) (mem_univ _)).trans (le_max_right _ _)

theorem exists_actualJacobiSolution (g : SmoothMetric M) (hRic : RicciThree g)
    (e : FrameBundle g) : Nonempty (MatrixJacobiSolution (actualJacobiCurvature g e)) := by
  obtain ⟨K, hK⟩ := actualJacobiCurvature_bounded g hRic
  exact exists_matrixJacobiSolution _ (actualJacobiCurvature_continuous g hRic e) K (hK e)

def actualJacobiSolution (g : SmoothMetric M) (hRic : RicciThree g)
    (e : FrameBundle g) : MatrixJacobiSolution (actualJacobiCurvature g e) :=
  Classical.choice (exists_actualJacobiSolution g hRic e)

theorem exists_actualRegularJacobi (g : SmoothMetric M) (hRic : RicciThree g)
    (e : FrameBundle g) (t : ℝ) :
    ∃ q : RegularJacobi t, q.R = actualJacobiCurvature g e ∧
      q.J = (actualJacobiSolution g hRic e).J ∧ q.V = (actualJacobiSolution g hRic e).V :=
  (actualJacobiSolution g hRic e).exists_regular
    (actualJacobiCurvatureDerivative g e) (actualJacobiCurvature_continuous g hRic e)
    (actualJacobiCurvatureDerivative_continuous g hRic e)
    (actualJacobiCurvature_hasDerivAt g hRic e) (actualJacobiCurvature_symmetric g e) t

def actualRegularJacobi (g : SmoothMetric M) (hRic : RicciThree g)
    (e : FrameBundle g) (t : ℝ) : RegularJacobi t :=
  Classical.choose (exists_actualRegularJacobi g hRic e t)

end
end PositiveEinsteinFour.Geometry
end


section

/-! A positive scalar change of metric transports the actual clopen
orientation of the orthonormal frame bundle. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

/-- Scale frame vectors when the metric matrices have the inverse square relation. -/
def OrthonormalFrame.scaleBetween {g h : SmoothMetric M} {x : M}
    (e : OrthonormalFrame g x) (a : ℝ)
    (ha : (a ^ 2) • chartMetric h x = chartMetric g x) : OrthonormalFrame h x where
  matrix := a • e.matrix
  orthonormal := by rw [frame_scaling_identity, ha, e.orthonormal]

@[simp] theorem OrthonormalFrame.scaleBetween_vector {g h : SmoothMetric M} {x : M}
    (e : OrthonormalFrame g x) (a : ℝ)
    (ha : (a ^ 2) • chartMetric h x = chartMetric g x) (i : Fin 4) :
    (e.scaleBetween a ha).vector i = a • e.vector i := by
  ext j
  rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! The canonical unit tangent measure is normalized base volume times
spherical probability in every measurable positive reference frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular Matrix MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

local instance instIsProbabilityMeasureDirectionsSphereMeasure_2_r4e575d_1 : IsProbabilityMeasure sphereMeasure := actual_sphereMeasure_probability
def unitTangentTurn (e : FrameBundle g) (q : Directions) : UnitTangentBundle g :=
  unitTangentOfFrame (e.rotate (orientedToOrthogonal (directionOrientedMatrix q)))

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual first frame flow descends to intrinsic unit tangent vectors.
The definition is independent of the chosen positive normal frame, and
inherits the identity and group law from the constructed complete curves. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [CompactSpace M]

theorem parallelFrameFlowMap_positive (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (he : e ∈ o.positive) (t : ℝ) :
    parallelFrameFlowMap g 0 t e ∈ o.positive := by
  have h := o.mem_iff_of_continuous_curve (fun s => parallelFrameFlowMap g 0 s e)
    (parallelFrameFlowMap_curve_continuous g 0 e) t 0
  rw [parallelFrameFlowMap_zero] at h
  exact h.mpr he

theorem unitTangentOfFrame_flow_eq (g : SmoothMetric M) (o : FrameOrientation g)
    (e f : FrameBundle g) (he : e ∈ o.positive) (hf : f ∈ o.positive)
    (heq : unitTangentOfFrame e = unitTangentOfFrame f) (t : ℝ) :
    unitTangentOfFrame (parallelFrameFlowMap g 0 t e) =
      unitTangentOfFrame (parallelFrameFlowMap g 0 t f) := by
  cases e with
  | mk x E =>
    cases f with
    | mk y F =>
      have hxy : x = y := congrArg (fun u : UnitTangentBundle g => u.base) heq
      subst y
      have hfirst : E.vector 0 = F.vector 0 :=
        congrArg (fun u : UnitTangentBundle g => u.vector) heq
      have hdet := (o.compatible x E F he).mp hf
      have h := parallelFrameFlowMap_same_first g E F hdet hfirst t
      exact unitTangent_ext h.1 h.2

def unitTangentFrame (g : SmoothMetric M) (o : FrameOrientation g)
    (u : UnitTangentBundle g) : FrameBundle g :=
  Classical.choose (exists_positive_unitTangent_frame g o u)

omit [T2Space M] [CompactSpace M] in
theorem unitTangentFrame_positive (g : SmoothMetric M) (o : FrameOrientation g)
    (u : UnitTangentBundle g) : unitTangentFrame g o u ∈ o.positive :=
  (Classical.choose_spec (exists_positive_unitTangent_frame g o u)).1

omit [T2Space M] [CompactSpace M] in
theorem unitTangentOfFrame_lift (g : SmoothMetric M) (o : FrameOrientation g)
    (u : UnitTangentBundle g) : unitTangentOfFrame (unitTangentFrame g o u) = u :=
  (Classical.choose_spec (exists_positive_unitTangent_frame g o u)).2

def unitTangentFlowMap (g : SmoothMetric M) (o : FrameOrientation g)
    (t : ℝ) (u : UnitTangentBundle g) : UnitTangentBundle g :=
  unitTangentOfFrame (parallelFrameFlowMap g 0 t (unitTangentFrame g o u))

theorem unitTangentFlowMap_of_frame (g : SmoothMetric M) (o : FrameOrientation g)
    (t : ℝ) (e : FrameBundle g) (he : e ∈ o.positive) :
    unitTangentFlowMap g o t (unitTangentOfFrame e) =
      unitTangentOfFrame (parallelFrameFlowMap g 0 t e) :=
  unitTangentOfFrame_flow_eq g o _ e (unitTangentFrame_positive g o _) he
    (unitTangentOfFrame_lift g o _) t

theorem unitTangentFlowMap_zero (g : SmoothMetric M) (o : FrameOrientation g)
    (u : UnitTangentBundle g) : unitTangentFlowMap g o 0 u = u := by
  rw [unitTangentFlowMap, parallelFrameFlowMap_zero, unitTangentOfFrame_lift]

theorem unitTangentFlowMap_add (g : SmoothMetric M) (o : FrameOrientation g)
    (s t : ℝ) (u : UnitTangentBundle g) :
    unitTangentFlowMap g o (s + t) u =
      unitTangentFlowMap g o s (unitTangentFlowMap g o t u) := by
  let e := unitTangentFrame g o u
  have he : e ∈ o.positive := unitTangentFrame_positive g o u
  have h := unitTangentFlowMap_of_frame g o s (parallelFrameFlowMap g 0 t e)
    (parallelFrameFlowMap_positive g o e he t)
  calc
    _ = unitTangentOfFrame (parallelFrameFlowMap g 0 s (parallelFrameFlowMap g 0 t e)) := by
      rw [unitTangentFlowMap, parallelFrameFlowMap_add]
    _ = _ := h.symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! The positive-frame projection is a compact quotient. Consequently
the descended complete geodesic flow is jointly continuous, without a
continuous global choice of normal frames. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bundle Set
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M]

theorem tangentBundle_t2 : T2Space (TangentBundle I4 M) := by
  apply t2Space_iff_disjoint_nhds.mpr
  intro x y hne
  by_cases hbase : x.proj = y.proj
  · let e := trivializationAt FourSpace (TangentSpace I4 : M → Type _) x.proj
    have hx : x ∈ e.source := e.mem_source.mpr
      (mem_baseSet_trivializationAt FourSpace (TangentSpace I4) x.proj)
    have hy : y ∈ e.source := e.mem_source.mpr (by
      rw [← hbase]
      exact mem_baseSet_trivializationAt FourSpace (TangentSpace I4) x.proj)
    have hxy : e x ≠ e y := fun heq => hne (e.toOpenPartialHomeomorph.injOn hx hy heq)
    exact (e.toOpenPartialHomeomorph.continuousAt hx).disjoint
      (disjoint_nhds_nhds.mpr hxy) (e.toOpenPartialHomeomorph.continuousAt hy)
  · exact (FiberBundle.continuous_proj FourSpace (TangentSpace I4)).continuousAt.disjoint
      (disjoint_nhds_nhds.mpr hbase)
      (FiberBundle.continuous_proj FourSpace (TangentSpace I4)).continuousAt

omit [T2Space M] in
theorem isEmbedding_unitTangentRealization (g : SmoothMetric M) :
    Topology.IsEmbedding (unitTangentRealization : UnitTangentBundle g → TangentBundle I4 M) where
  eq_induced := rfl
  injective := unitTangentRealization_injective g

instance instT2SpaceUnitTangentBundle (g : SmoothMetric M) : T2Space (UnitTangentBundle g) := by
  let : T2Space (TangentBundle I4 M) := tangentBundle_t2
  exact (isEmbedding_unitTangentRealization g).t2Space

variable [CompactSpace M]

def positiveFirstProjection (g : SmoothMetric M) (o : FrameOrientation g)
    (e : o.positive) : UnitTangentBundle g := unitTangentOfFrame e.val

omit [T2Space M] [CompactSpace M] in
theorem positiveFirstProjection_surjective (g : SmoothMetric M) (o : FrameOrientation g) :
    Function.Surjective (positiveFirstProjection g o) := by
  intro u
  obtain ⟨e, he, hu⟩ := exists_positive_unitTangent_frame g o u
  exact ⟨⟨e, he⟩, hu⟩

theorem positiveFirstProjection_quotient (g : SmoothMetric M) (o : FrameOrientation g) :
    Topology.IsQuotientMap (positiveFirstProjection g o) := by
  let : CompactSpace (FrameBundle g) := actual_compactFrameBundle g
  let : CompactSpace o.positive :=
    isCompact_iff_compactSpace.mp o.clopen.isClosed.isCompact
  have hc : Continuous (positiveFirstProjection g o) :=
    (continuous_unitTangentOfFrame g).comp continuous_subtype_val
  exact hc.isClosedMap.isQuotientMap hc (positiveFirstProjection_surjective g o)

theorem unitTangentFlowMap_continuous (g : SmoothMetric M) (o : FrameOrientation g) :
    Continuous (fun p : ℝ × UnitTangentBundle g => unitTangentFlowMap g o p.1 p.2) := by
  apply (positiveFirstProjection_quotient g o).continuous_lift_prod_right
  have hc : Continuous (fun p : ℝ × o.positive =>
      unitTangentOfFrame (parallelFrameFlowMap g 0 p.1 p.2.val)) :=
    (continuous_unitTangentOfFrame g).comp ((parallelFrameFlowMap_continuous g 0).comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))
  convert hc using 1
  all_goals try with_reducible_and_instances rfl
  funext p
  exact unitTangentFlowMap_of_frame g o p.1 p.2.val p.2.property

end
end PositiveEinsteinFour.Geometry
end


section

/-! Restrict the actual unit tangent probability to one base chart and
compute its spherical fibers in the smooth local Gram section. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular Matrix MeasureTheory Set Bundle
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

local instance instIsProbabilityMeasureDirectionsSphereMeasure_4_r4e575d_1 : IsProbabilityMeasure sphereMeasure := actual_sphereMeasure_probability
theorem continuous_unitTangentBase (g : SmoothMetric M) :
    Continuous (UnitTangentBundle.base : UnitTangentBundle g → M) := by
  have hr : Continuous (unitTangentRealization : UnitTangentBundle g → TangentBundle I4 M) :=
    continuous_induced_dom
  exact (FiberBundle.continuous_proj FourSpace (TangentSpace I4)).comp hr

end
end PositiveEinsteinFour.Geometry
end


section

/-! Cotangent coordinates of intrinsic unit tangent vectors. Lowering the
scaled tangent vector has an explicit inverse away from zero momentum. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Bundle
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

abbrev ChartUnitTangent (g : SmoothMetric M) (c : M) :=
  {u : UnitTangentBundle g // u.base ∈ (chartAt FourSpace c).source}

abbrev NonzeroCotangentChart (c : M) :=
  {p : CotangentCoordinates // p.1 ∈ (chartAt FourSpace c).target ∧ p.2 ≠ 0}

def tangentInnerForm (g : SmoothMetric M) (x : M) :
    FourSpace →L[ℝ] FourSpace →L[ℝ] ℝ := g.inner x

def unitTangentVector {g : SmoothMetric M} (u : UnitTangentBundle g) : FourSpace := u.vector

theorem tangentInnerForm_pos (g : SmoothMetric M) (x : M) (v : FourSpace) (hv : v ≠ 0) :
    0 < tangentInnerForm g x v v := g.pos x v hv

theorem tangentInnerForm_unit (g : SmoothMetric M) (u : UnitTangentBundle g) :
    tangentInnerForm g u.base (unitTangentVector u) (unitTangentVector u) = 1 := u.unit

def chartForwardOperator (c x : M) : FourSpace →L[ℝ] FourSpace :=
  mfderiv I4 I4 (chartAt FourSpace c) x

def chartBackwardOperator (c : M) (z : FourSpace) : FourSpace →L[ℝ] FourSpace :=
  mfderiv I4 I4 (chartAt FourSpace c).symm z

theorem chartBackward_forward (c x : M) (hx : x ∈ (chartAt FourSpace c).source) :
    (chartBackwardOperator c (chartAt FourSpace c x)).comp (chartForwardOperator c x) =
      ContinuousLinearMap.id ℝ FourSpace :=
  (mdifferentiable_chart (I := I4) c).symm_comp_deriv hx

theorem chartForward_backward (c : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target) :
    (chartForwardOperator c ((chartAt FourSpace c).symm z)).comp (chartBackwardOperator c z) =
      ContinuousLinearMap.id ℝ FourSpace :=
  (mdifferentiable_chart (I := I4) c).comp_symm_deriv hz

def unitChartVelocity (c : M) {g : SmoothMetric M}
    (u : UnitTangentBundle g) : FourSpace :=
  ((trivializationAt FourSpace (TangentSpace I4 : M → Type _) c)
    (unitTangentRealization u)).2

theorem unitChartVelocity_eq_derivative (c : M) {g : SmoothMetric M}
    (u : UnitTangentBundle g) (hu : u.base ∈ (chartAt FourSpace c).source) :
    unitChartVelocity c u = chartForwardOperator c u.base (unitTangentVector u) := by
  unfold chartForwardOperator
  rw [mfderiv_chartAt_eq_tangentCoordChange hu, tangentCoordChange_def]
  unfold unitChartVelocity
  rw [TangentBundle.trivializationAt_apply]
  simp only [extChartAt, OpenPartialHomeomorph.extend_coe,
    OpenPartialHomeomorph.extend_coe_symm, I4, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, Function.id_comp, Function.comp_id, Set.range_id]
  simp only [fderivWithin_univ, unitTangentRealization, unitTangentVector]

theorem unitChartVelocity_continuousAt (c : M) {g : SmoothMetric M}
    (u : UnitTangentBundle g) (hu : u.base ∈ (chartAt FourSpace c).source) :
    ContinuousAt (unitChartVelocity c) u := by
  let V := trivializationAt FourSpace (TangentSpace I4 : M → Type _) c
  have hv : unitTangentRealization u ∈ V.source := by
    apply V.mem_source.mpr
    simpa only [V, TangentBundle.trivializationAt_baseSet, unitTangentRealization] using hu
  have hreal : Continuous (unitTangentRealization : UnitTangentBundle g → TangentBundle I4 M) :=
    continuous_induced_dom
  exact ((V.toOpenPartialHomeomorph.continuousAt hv).comp hreal.continuousAt).snd

def unitCotangentState (g : SmoothMetric M) (c : M)
    (r : ℝ) (u : UnitTangentBundle g) : CotangentCoordinates :=
  (chartAt FourSpace c u.base, r • WithLp.toLp 2
    (metricInChart g c (chartAt FourSpace c u.base) *ᵥ WithLp.ofLp (unitChartVelocity c u)))

theorem unitCotangentState_continuousAt (g : SmoothMetric M) (c : M)
    (r : ℝ) (u : UnitTangentBundle g)
    (hu : u.base ∈ (chartAt FourSpace c).source) :
    ContinuousAt (fun p : ℝ × UnitTangentBundle g => unitCotangentState g c p.1 p.2)
      (r, u) := by
  have hb : Continuous (fun u : UnitTangentBundle g => u.base) :=
    (FiberBundle.continuous_proj FourSpace (TangentSpace I4)).comp
      (show Continuous (unitTangentRealization : UnitTangentBundle g → TangentBundle I4 M) from
        continuous_induced_dom)
  have hx := ((chartAt FourSpace c).continuousAt hu).comp hb.continuousAt
  have hG (i j : Fin 4) : ContinuousAt
      (fun u : UnitTangentBundle g => metricInChart g c (chartAt FourSpace c u.base) i j) u :=
    (metricInChart_contDiffAt g c _ ((chartAt FourSpace c).map_source hu) i j).continuousAt.comp
      (f := fun u : UnitTangentBundle g => chartAt FourSpace c u.base) hx
  have hv := unitChartVelocity_continuousAt c u hu
  have hp : ContinuousAt (fun u : UnitTangentBundle g => WithLp.toLp 2
      (metricInChart g c (chartAt FourSpace c u.base) *ᵥ WithLp.ofLp (unitChartVelocity c u))) u := by
    apply (PiLp.continuous_toLp 2 _).continuousAt.comp
    apply continuousAt_pi.mpr
    intro i
    change ContinuousAt (fun y : UnitTangentBundle g =>
      ∑ j, metricInChart g c (chartAt FourSpace c y.base) i j * unitChartVelocity c y j) u
    exact tendsto_finsetSum _ (fun j _ => (hG i j).mul
      ((PiLp.continuous_apply 2 _ j).continuousAt.comp hv))
  have hx' : ContinuousAt (fun p : ℝ × UnitTangentBundle g =>
      chartAt FourSpace c p.2.base) (r, u) := by
    have hb' : Continuous (fun p : ℝ × UnitTangentBundle g => p.2.base) :=
      hb.comp continuous_snd
    exact ((chartAt FourSpace c).continuousAt hu).comp
      (f := fun p : ℝ × UnitTangentBundle g => p.2.base) hb'.continuousAt
  have hp' : ContinuousAt (fun p : ℝ × UnitTangentBundle g => WithLp.toLp 2
      (metricInChart g c (chartAt FourSpace c p.2.base) *ᵥ
        WithLp.ofLp (unitChartVelocity c p.2))) (r, u) :=
    ContinuousAt.comp (x := (r, u))
      (g := fun v : UnitTangentBundle g => WithLp.toLp 2
        (metricInChart g c (chartAt FourSpace c v.base) *ᵥ WithLp.ofLp (unitChartVelocity c v)))
      (f := fun p : ℝ × UnitTangentBundle g => p.2) hp continuous_snd.continuousAt
  exact hx'.prodMk (continuous_fst.continuousAt.smul hp')

def raisedChartVelocity (g : SmoothMetric M) (c : M)
    (p : CotangentCoordinates) : FourSpace :=
  WithLp.toLp 2 ((metricInChart g c p.1)⁻¹ *ᵥ WithLp.ofLp p.2)

def raisedChartVector (g : SmoothMetric M) (c : M)
    (p : CotangentCoordinates) : FourSpace :=
  chartBackwardOperator c p.1 (raisedChartVelocity g c p)

def momentumRadius (g : SmoothMetric M) (c : M) (p : CotangentCoordinates) : ℝ :=
  Real.sqrt (tangentInnerForm g ((chartAt FourSpace c).symm p.1)
    (raisedChartVector g c p) (raisedChartVector g c p))

theorem raisedChartVelocity_lower (g : SmoothMetric M) (c : M)
    (p : CotangentCoordinates) (hp : p.1 ∈ (chartAt FourSpace c).target) :
    metricInChart g c p.1 *ᵥ WithLp.ofLp (raisedChartVelocity g c p) = WithLp.ofLp p.2 := by
  change metricInChart g c p.1 *ᵥ ((metricInChart g c p.1)⁻¹ *ᵥ WithLp.ofLp p.2) = _
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
    (isUnit_iff_ne_zero.mpr (metricInChart_posDef g c p.1 hp).det_pos.ne'), Matrix.one_mulVec]

theorem momentumRadius_pos (g : SmoothMetric M) (c : M)
    (p : NonzeroCotangentChart c) : 0 < momentumRadius g c p := by
  apply Real.sqrt_pos.mpr
  apply tangentInnerForm_pos
  intro hv
  have hw : raisedChartVelocity g c p = 0 := by
    apply chart_inverse_derivative_injective c p.val.1 p.property.1
    change chartBackwardOperator c p.val.1 _ = chartBackwardOperator c p.val.1 0
    simpa only [raisedChartVector, map_zero] using hv
  have hp := raisedChartVelocity_lower g c p p.property.1
  rw [hw] at hp
  have hp0 : p.val.2 = 0 := by
    apply WithLp.ofLp_injective
    simpa using hp.symm
  exact p.property.2 hp0

theorem momentumRadius_sq (g : SmoothMetric M) (c : M)
    (p : NonzeroCotangentChart c) : momentumRadius g c p ^ 2 =
      tangentInnerForm g ((chartAt FourSpace c).symm p.val.1)
        (raisedChartVector g c p) (raisedChartVector g c p) := by
  apply Real.sq_sqrt
  exact (tangentInnerForm_pos g _ _ (by
    intro hv
    have hw : raisedChartVelocity g c p = 0 := by
      apply chart_inverse_derivative_injective c p.val.1 p.property.1
      change chartBackwardOperator c p.val.1 _ = chartBackwardOperator c p.val.1 0
      simpa only [raisedChartVector, map_zero] using hv
    have hp := raisedChartVelocity_lower g c p p.property.1
    rw [hw] at hp
    apply p.property.2
    apply WithLp.ofLp_injective
    simpa using hp.symm)).le

def unitTangentFromMomentum (g : SmoothMetric M) (c : M)
    (p : NonzeroCotangentChart c) : ChartUnitTangent g c := by
  let r := momentumRadius g c p
  have hr : r ≠ 0 := (momentumRadius_pos g c p).ne'
  refine ⟨⟨(chartAt FourSpace c).symm p.val.1,
    r⁻¹ • raisedChartVector g c p, ?_⟩, (chartAt FourSpace c).map_target p.property.1⟩
  change tangentInnerForm g ((chartAt FourSpace c).symm p.val.1)
    (r⁻¹ • raisedChartVector g c p) (r⁻¹ • raisedChartVector g c p) = 1
  simp only [map_smul, _root_.smul_apply, smul_eq_mul]
  rw [← momentumRadius_sq g c p]
  change r⁻¹ * (r⁻¹ * r ^ 2) = 1
  field_simp [hr]

theorem unitChartVelocity_fromMomentum (g : SmoothMetric M) (c : M)
    (p : NonzeroCotangentChart c) :
    unitChartVelocity c (unitTangentFromMomentum g c p).val =
      (momentumRadius g c p)⁻¹ • raisedChartVelocity g c p := by
  rw [unitChartVelocity_eq_derivative c _ (unitTangentFromMomentum g c p).property]
  change (chartForwardOperator c ((chartAt FourSpace c).symm p.val.1))
    ((momentumRadius g c p)⁻¹ • raisedChartVector g c p) = _
  rw [map_smul]
  apply congrArg ((momentumRadius g c p)⁻¹ • ·)
  exact congrArg (fun L : FourSpace →L[ℝ] FourSpace => L (raisedChartVelocity g c p))
    (chartForward_backward c p.val.1 p.property.1)

/-- The normalized inverse recovers every nonzero cotangent momentum. -/
theorem unitCotangentState_fromMomentum (g : SmoothMetric M) (c : M)
    (p : NonzeroCotangentChart c) :
    unitCotangentState g c (momentumRadius g c p) (unitTangentFromMomentum g c p).val = p.val := by
  apply Prod.ext
  · exact (chartAt FourSpace c).right_inv p.property.1
  change momentumRadius g c p • WithLp.toLp 2
    (metricInChart g c (chartAt FourSpace c ((chartAt FourSpace c).symm p.val.1)) *ᵥ
      WithLp.ofLp (unitChartVelocity c (unitTangentFromMomentum g c p).val)) = p.val.2
  rw [(chartAt FourSpace c).right_inv p.property.1,
    unitChartVelocity_fromMomentum, WithLp.ofLp_smul, Matrix.mulVec_smul,
    raisedChartVelocity_lower g c p p.property.1]
  change momentumRadius g c p • ((momentumRadius g c p)⁻¹ • p.val.2) = p.val.2
  rw [smul_smul, mul_inv_cancel₀ (momentumRadius_pos g c p).ne', one_smul]

theorem raisedChartVelocity_unitCotangentState (g : SmoothMetric M) (c : M)
    (r : ℝ) (u : UnitTangentBundle g)
    (hu : u.base ∈ (chartAt FourSpace c).source) :
    raisedChartVelocity g c (unitCotangentState g c r u) = r • unitChartVelocity c u := by
  change WithLp.toLp 2 ((metricInChart g c (chartAt FourSpace c u.base))⁻¹ *ᵥ
    WithLp.ofLp (r • WithLp.toLp 2 (metricInChart g c (chartAt FourSpace c u.base) *ᵥ
      WithLp.ofLp (unitChartVelocity c u)))) = _
  rw [WithLp.ofLp_smul, WithLp.ofLp_toLp, Matrix.mulVec_smul,
    Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _
      (isUnit_iff_ne_zero.mpr (metricInChart_posDef g c _
        ((chartAt FourSpace c).map_source hu)).det_pos.ne'), Matrix.one_mulVec]
  rfl

theorem raisedChartVector_unitCotangentState (g : SmoothMetric M) (c : M)
    (r : ℝ) (u : UnitTangentBundle g)
    (hu : u.base ∈ (chartAt FourSpace c).source) :
    raisedChartVector g c (unitCotangentState g c r u) =
      r • unitTangentVector u := by
  change (chartBackwardOperator c (chartAt FourSpace c u.base))
    (raisedChartVelocity g c (unitCotangentState g c r u)) = _
  rw [raisedChartVelocity_unitCotangentState g c r u hu, map_smul,
    unitChartVelocity_eq_derivative c u hu]
  apply congrArg (r • ·)
  exact congrArg (fun L : FourSpace →L[ℝ] FourSpace => L (unitTangentVector u))
    (chartBackward_forward c u.base hu)

theorem momentumRadius_unitCotangentState (g : SmoothMetric M) (c : M)
    (r : ℝ) (hr : 0 < r) (u : UnitTangentBundle g)
    (hu : u.base ∈ (chartAt FourSpace c).source) :
    momentumRadius g c (unitCotangentState g c r u) = r := by
  unfold momentumRadius
  rw [raisedChartVector_unitCotangentState g c r u hu]
  change Real.sqrt (tangentInnerForm g ((chartAt FourSpace c).symm (chartAt FourSpace c u.base))
    (r • unitTangentVector u) (r • unitTangentVector u)) = r
  rw [(chartAt FourSpace c).left_inv hu]
  simp only [map_smul, _root_.smul_apply, smul_eq_mul, tangentInnerForm_unit, mul_one]
  rw [← pow_two, Real.sqrt_sq_eq_abs, abs_of_pos hr]

theorem unitCotangentState_momentum_ne_zero (g : SmoothMetric M) (c : M)
    (r : ℝ) (hr : 0 < r) (u : UnitTangentBundle g)
    (hu : u.base ∈ (chartAt FourSpace c).source) :
    (unitCotangentState g c r u).2 ≠ 0 := by
  intro hzero
  have hv : raisedChartVector g c (unitCotangentState g c r u) = 0 := by
    unfold raisedChartVector raisedChartVelocity
    rw [hzero]
    simp
  have hrad : momentumRadius g c (unitCotangentState g c r u) = 0 := by
    simp [momentumRadius, hv]
  rw [momentumRadius_unitCotangentState g c r hr u hu] at hrad
  exact hr.ne' hrad

def unitTangentCotangentTo (g : SmoothMetric M) (c : M)
    (p : PositiveRadius × ChartUnitTangent g c) : NonzeroCotangentChart c :=
  ⟨unitCotangentState g c p.1.val p.2.val,
    (chartAt FourSpace c).map_source p.2.property,
    unitCotangentState_momentum_ne_zero g c p.1.val p.1.property p.2.val p.2.property⟩

def unitTangentCotangentFrom (g : SmoothMetric M) (c : M)
    (p : NonzeroCotangentChart c) : PositiveRadius × ChartUnitTangent g c :=
  (⟨momentumRadius g c p, momentumRadius_pos g c p⟩, unitTangentFromMomentum g c p)

theorem unitTangentCotangentTo_from (g : SmoothMetric M) (c : M)
    (p : NonzeroCotangentChart c) :
    unitTangentCotangentTo g c (unitTangentCotangentFrom g c p) = p := by
  apply Subtype.ext
  exact unitCotangentState_fromMomentum g c p

theorem unitTangentCotangentFrom_to (g : SmoothMetric M) (c : M)
    (p : PositiveRadius × ChartUnitTangent g c) :
    unitTangentCotangentFrom g c (unitTangentCotangentTo g c p) = p := by
  apply Prod.ext
  · apply Subtype.ext
    exact momentumRadius_unitCotangentState g c p.1.val p.1.property p.2.val p.2.property
  · apply Subtype.ext
    apply unitTangent_ext
    · exact (chartAt FourSpace c).left_inv p.2.property
    · change (momentumRadius g c (unitCotangentState g c p.1.val p.2.val))⁻¹ •
        raisedChartVector g c (unitCotangentState g c p.1.val p.2.val) =
          unitTangentVector p.2.val
      rw [momentumRadius_unitCotangentState g c p.1.val p.1.property p.2.val p.2.property,
        raisedChartVector_unitCotangentState g c p.1.val p.2.val p.2.property,
        smul_smul, inv_mul_cancel₀ p.1.property.ne', one_smul]

/-- Actual radial unit tangent coordinates and nonzero cotangent coordinates
in a fixed manifold chart are mutually inverse. -/
def unitTangentCotangentEquiv (g : SmoothMetric M) (c : M) :
    (PositiveRadius × ChartUnitTangent g c) ≃ NonzeroCotangentChart c where
  toFun := unitTangentCotangentTo g c
  invFun := unitTangentCotangentFrom g c
  left_inv := unitTangentCotangentFrom_to g c
  right_inv := unitTangentCotangentTo_from g c

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual nonzero cotangent chart is a homeomorphism. Continuity of
its inverse follows from the inverse chart's tangent map and normalization. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Bundle
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem continuous_raisedChartVelocity (g : SmoothMetric M) (c : M) :
    Continuous (fun p : NonzeroCotangentChart c => raisedChartVelocity g c p.val) := by
  have hi (i j : Fin 4) : Continuous (fun p : NonzeroCotangentChart c =>
      (metricInChart g c p.val.1)⁻¹ i j) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    exact (metricInChart_inv_contDiffAt g c p.val.1 p.property.1
      (metricInChart_posDef g c p.val.1 p.property.1).det_pos.ne' i j).continuousAt.comp
      (f := fun q : NonzeroCotangentChart c => q.val.1)
      (continuous_fst.comp continuous_subtype_val).continuousAt
  change Continuous (fun p : NonzeroCotangentChart c => WithLp.toLp 2
    (fun i => ∑ j, (metricInChart g c p.val.1)⁻¹ i j * p.val.2 j))
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  apply continuous_finsetSum
  intro j _
  exact (hi i j).mul ((PiLp.continuous_apply 2 _ j).comp
    (continuous_snd.comp continuous_subtype_val))

theorem momentumRadius_eq_sqrt (g : SmoothMetric M) (c : M) (p : CotangentCoordinates) :
    momentumRadius g c p = Real.sqrt (WithLp.ofLp (raisedChartVelocity g c p) ⬝ᵥ
      (metricInChart g c p.1 *ᵥ WithLp.ofLp (raisedChartVelocity g c p))) := by
  rw [metricInChart_pairing]
  rfl

theorem continuous_momentumRadius (g : SmoothMetric M) (c : M) :
    Continuous (fun p : NonzeroCotangentChart c => momentumRadius g c p.val) := by
  have hG (i j : Fin 4) : Continuous (fun p : NonzeroCotangentChart c =>
      metricInChart g c p.val.1 i j) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    exact (metricInChart_contDiffAt g c p.val.1 p.property.1 i j).continuousAt.comp
      (f := fun q : NonzeroCotangentChart c => q.val.1)
      (continuous_fst.comp continuous_subtype_val).continuousAt
  have hv (i : Fin 4) : Continuous (fun p : NonzeroCotangentChart c =>
      raisedChartVelocity g c p.val i) :=
    (PiLp.continuous_apply 2 _ i).comp (continuous_raisedChartVelocity g c)
  have hq : Continuous (fun p : NonzeroCotangentChart c =>
      ∑ i, raisedChartVelocity g c p.val i *
        (∑ j, metricInChart g c p.val.1 i j * raisedChartVelocity g c p.val j)) := by
    apply continuous_finsetSum
    intro i _
    exact (hv i).mul (continuous_finsetSum _ (fun j _ => (hG i j).mul (hv j)))
  simpa only [momentumRadius_eq_sqrt, dotProduct, Matrix.mulVec] using hq.sqrt

theorem continuous_unitTangentFromMomentum (g : SmoothMetric M) (c : M) :
    Continuous (unitTangentFromMomentum g c) := by
  have hv : Continuous (fun p : NonzeroCotangentChart c =>
      (momentumRadius g c p.val)⁻¹ • raisedChartVelocity g c p.val) :=
    ((continuous_momentumRadius g c).inv₀
      (fun p => (momentumRadius_pos g c p).ne')).smul
      (continuous_raisedChartVelocity g c)
  have hinput : Continuous (fun p : NonzeroCotangentChart c =>
      (⟨p.val.1, (momentumRadius g c p.val)⁻¹ • raisedChartVelocity g c p.val⟩ :
        TangentBundle I4 FourSpace)) :=
    (tangentBundleModelSpaceHomeomorph I4).symm.continuous.comp
      ((continuous_fst.comp continuous_subtype_val).prodMk hv)
  have hphi : ContMDiffOn I4 I4 ∞ (chartAt FourSpace c).symm
      (chartAt FourSpace c).target := contMDiffOn_chart_symm
  have ht := (hphi.contMDiffOn_tangentMapWithin (m := ∞) (by simp)
    (chartAt FourSpace c).open_target.uniqueMDiffOn).continuousOn
  have hcomp := ht.comp_continuous hinput (fun p => p.property.1)
  have hreal : Continuous (fun p : NonzeroCotangentChart c =>
      unitTangentRealization (unitTangentFromMomentum g c p).val) := by
    apply hcomp.congr
    intro p
    change (⟨(chartAt FourSpace c).symm p.val.1,
      mfderivWithin I4 I4 (chartAt FourSpace c).symm (chartAt FourSpace c).target p.val.1
        ((momentumRadius g c p.val)⁻¹ • raisedChartVelocity g c p.val)⟩ :
          TangentBundle I4 M) = _
    rw [mfderivWithin_of_isOpen (chartAt FourSpace c).open_target p.property.1]
    change (⟨(chartAt FourSpace c).symm p.val.1,
      chartBackwardOperator c p.val.1
        ((momentumRadius g c p.val)⁻¹ • raisedChartVelocity g c p.val)⟩ :
          TangentBundle I4 M) = _
    exact congrArg (fun v : FourSpace =>
      (⟨(chartAt FourSpace c).symm p.val.1, v⟩ : TangentBundle I4 M))
      (map_smul (chartBackwardOperator c p.val.1) (momentumRadius g c p.val)⁻¹
        (raisedChartVelocity g c p.val))
  apply continuous_induced_rng.mpr
  exact continuous_induced_rng.mpr hreal

theorem continuous_unitTangentCotangentTo (g : SmoothMetric M) (c : M) :
    Continuous (unitTangentCotangentTo g c) := by
  apply continuous_induced_rng.mpr
  apply continuous_iff_continuousAt.mpr
  intro p
  exact (unitCotangentState_continuousAt g c p.1.val p.2.val p.2.property).comp
    (f := fun q : PositiveRadius × ChartUnitTangent g c => (q.1.val, q.2.val))
    (((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd)).continuousAt)

theorem continuous_unitTangentCotangentFrom (g : SmoothMetric M) (c : M) :
    Continuous (unitTangentCotangentFrom g c) :=
  ((continuous_momentumRadius g c).subtype_mk (fun p => momentumRadius_pos g c p)).prodMk
    (continuous_unitTangentFromMomentum g c)

def unitTangentCotangentHomeomorph (g : SmoothMetric M) (c : M) :
    (PositiveRadius × ChartUnitTangent g c) ≃ₜ NonzeroCotangentChart c where
  toEquiv := unitTangentCotangentEquiv g c
  continuous_toFun := continuous_unitTangentCotangentTo g c
  continuous_invFun := continuous_unitTangentCotangentFrom g c

end
end PositiveEinsteinFour.Geometry
end

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeodesicGeometry04
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Exact unit-speed length and endpoint distance bounds for the actual
complete geodesics, including their intrinsic unit-tangent formulation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bundle Set MeasureTheory
open scoped Manifold ContDiff ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [CompactSpace M]

def unitGeodesic (g : SmoothMetric M) (o : FrameOrientation g)
    (u : UnitTangentBundle g) (t : ℝ) : M := (unitTangentFlowMap g o t u).base

end
end PositiveEinsteinFour.Geometry
end


section

/-! The positive radial extension of the actual unit-speed geodesic flow.
Its ambient measure preservation suffices for every unit-speed frame flow,
by continuity across energy shells and normal-frame averaging. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TopologicalSpace
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [CompactSpace M]

/-- Radius is constant and multiplies the time of the unit-speed flow. -/
def unitTangentRadialFlow (g : SmoothMetric M) (o : FrameOrientation g) (t : ℝ)
    (p : PositiveRadius × UnitTangentBundle g) : PositiveRadius × UnitTangentBundle g :=
  (p.1, unitTangentFlowMap g o (p.1.val * t) p.2)

theorem unitTangentRadialFlow_continuous (g : SmoothMetric M) (o : FrameOrientation g)
    (t : ℝ) : Continuous (unitTangentRadialFlow g o t) :=
  continuous_fst.prodMk ((unitTangentFlowMap_continuous g o).comp
    (((continuous_subtype_val.comp continuous_fst).mul_const t).prodMk continuous_snd))

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual exponential in an orthonormal frame, constructed from the
complete unit-speed geodesics. The zero vector is included continuously,
using the proved metric length bound. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular Bundle Filter Set
open scoped Manifold ContDiff _root_.Topology ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [CompactSpace M]

def frameExponentialNonzero (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (v : ({0}ᶜ : Set FourSpace)) : M :=
  unitGeodesic g o (unitTangentTurn e (euclideanPolarHomeomorph v).1)
    (euclideanPolarHomeomorph v).2.val

def frameExponential (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) : FourSpace → M :=
  Function.extend (Subtype.val : ({0}ᶜ : Set FourSpace) → FourSpace)
    (frameExponentialNonzero g o e) (fun _ => e.base)

theorem frameExponential_nonzero (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (v : ({0}ᶜ : Set FourSpace)) :
    frameExponential g o e v.val = frameExponentialNonzero g o e v :=
  Subtype.val_injective.extend_apply _ _ v

theorem frameExponential_radial (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (q : Directions) (r : PositiveRadius) :
    frameExponential g o e (r.val • q.val) = unitGeodesic g o (unitTangentTurn e q) r.val := by
  let p : Directions × PositiveRadius := (q, r)
  have hv := frameExponential_nonzero g o e (euclideanPolarHomeomorph.symm p)
  simpa only [euclideanPolarHomeomorph_symm_coe, euclideanPolarReconstruction,
    frameExponentialNonzero, Homeomorph.apply_symm_apply] using hv

end
end PositiveEinsteinFour.Geometry
end


section

/-! Intrinsic radial geodesic motion, in each local cotangent chart, is
the constructed kinetic Hamiltonian flow. No continuous frame choice is
needed: uniqueness allows an arbitrary positive frame at the initial point. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [CompactSpace M]

def unitRadialCotangentState (g : SmoothMetric M) (c : M)
    (p : PositiveRadius × UnitTangentBundle g) : CotangentCoordinates :=
  unitCotangentState g c p.1.val p.2

end
end PositiveEinsteinFour.Geometry
end


section

/-! The radial exponential is the actual local kinetic endpoint map near
zero. A common coordinate interval works for every unit direction. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular Matrix Bundle Filter Set
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

/-- Lowering the initial frame vector in a fixed coordinate chart. -/
def frameMomentumMap (g : SmoothMetric M) (c : M) (e : FrameBundle g) :
    FourSpace →L[ℝ] FourSpace :=
  (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ)
    (metricInChart g c (chartAt FourSpace c e.base))).comp
      ((chartForwardOperator c e.base).comp e.frame.map.toContinuousLinearMap)

theorem unitCotangentState_turn (g : SmoothMetric M) (c : M) (e : FrameBundle g)
    (he : e.base ∈ (chartAt FourSpace c).source) (r : ℝ) (q : Directions) :
    unitCotangentState g c r (unitTangentTurn e q) =
      (chartAt FourSpace c e.base, frameMomentumMap g c e (r • q.val)) := by
  have hv : (unitTangentTurn e q).vector = e.frame.map q.val := e.frame.turn_first q
  rw [unitCotangentState, unitChartVelocity_eq_derivative c _ he]
  change (_, r • WithLp.toLp 2 (_ *ᵥ WithLp.ofLp
    (chartForwardOperator c e.base (unitTangentTurn e q).vector))) = _
  rw [hv]
  simp only [frameMomentumMap, map_smul, ContinuousLinearMap.comp_apply,
    LinearMap.coe_toContinuousLinearMap']
  rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! Compact invariant radius slabs. A finite collection of the constructed
Hamiltonian charts provides one positive time valid throughout each slab. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [CompactSpace M]

/-- Data produced by the local Hamiltonian theorem, retaining the actual
coordinate map and the common interval of agreement with radial motion. -/
structure RadialHamiltonianChart (g : SmoothMetric M) (o : FrameOrientation g) where
  anchor : PositiveRadius × UnitTangentBundle g
  center : M
  domain : Set (PositiveRadius × UnitTangentBundle g)
  image : Set CotangentCoordinates
  flow : KineticLocalFlow g center (unitRadialCotangentState g center anchor)
  open_domain : IsOpen domain
  anchor_mem : anchor ∈ domain
  open_image : IsOpen image
  image_eq : image = unitRadialCotangentState g center '' domain
  image_subset_ball : image ⊆ Metric.ball (unitRadialCotangentState g center anchor) flow.radius
  image_in_chart : ∀ z ∈ image, z.1 ∈ (chartAt FourSpace center).target ∧ z.2 ≠ 0
  trajectory_in_chart : ∀ q ∈ domain, ∀ t ∈ Ioo (-flow.time) flow.time,
    (unitTangentRadialFlow g o t q).2.base ∈ (chartAt FourSpace center).source
  conjugacy : ∀ q ∈ domain, EqOn
    (fun t => flow.map (unitRadialCotangentState g center q, t))
    (fun t => unitRadialCotangentState g center (unitTangentRadialFlow g o t q))
    (Ioo (-flow.time) flow.time)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Measurable extensions of the actual radial cotangent chart and its
inverse. The extensions agree with the homeomorphism on its genuine domain;
the arbitrary value outside that domain is used only for measurability. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def cotangentRadialInverseOn (g : SmoothMetric M) (c : M)
    (z : NonzeroCotangentChart c) : PositiveRadius × UnitTangentBundle g :=
  let p := (unitTangentCotangentHomeomorph g c).symm z
  (p.1, p.2.val)

theorem continuous_cotangentRadialInverseOn (g : SmoothMetric M) (c : M) :
    Continuous (cotangentRadialInverseOn g c) :=
  ((unitTangentCotangentHomeomorph g c).symm.continuous.fst).prodMk
    (continuous_subtype_val.comp
      (unitTangentCotangentHomeomorph g c).symm.continuous.snd)

def cotangentRadialRetraction (g : SmoothMetric M) (c : M) :
    CotangentCoordinates → PositiveRadius × UnitTangentBundle g :=
  Function.extend (Subtype.val : NonzeroCotangentChart c → CotangentCoordinates)
    (cotangentRadialInverseOn g c)
    (fun _ => (⟨1, by norm_num⟩, unitTangentOfFrame (frameAt g c)))

theorem cotangentRadialRetraction_on (g : SmoothMetric M) (c : M)
    (z : NonzeroCotangentChart c) :
    cotangentRadialRetraction g c z.val = cotangentRadialInverseOn g c z := by
  exact Subtype.val_injective.extend_apply _ _ z

theorem cotangentRadialRetraction_source (g : SmoothMetric M) (c : M)
    (z : CotangentCoordinates)
    (hz : z.1 ∈ (chartAt FourSpace c).target ∧ z.2 ≠ 0) :
    (cotangentRadialRetraction g c z).2.base ∈ (chartAt FourSpace c).source := by
  rw [cotangentRadialRetraction_on g c (⟨z, hz⟩ : NonzeroCotangentChart c)]
  exact ((unitTangentCotangentHomeomorph g c).symm
    (⟨z, hz⟩ : NonzeroCotangentChart c)).2.property

/-- The measurable inverse recovers the original intrinsic radial state. -/
theorem cotangentRadialRetraction_state (g : SmoothMetric M) (c : M)
    (p : PositiveRadius × UnitTangentBundle g)
    (hp : p.2.base ∈ (chartAt FourSpace c).source) :
    cotangentRadialRetraction g c (unitRadialCotangentState g c p) = p := by
  let a : PositiveRadius × ChartUnitTangent g c := (p.1, ⟨p.2, hp⟩)
  let H := unitTangentCotangentHomeomorph g c
  calc
    cotangentRadialRetraction g c (unitRadialCotangentState g c p) =
        cotangentRadialInverseOn g c (H a) :=
      cotangentRadialRetraction_on g c (H a)
    _ = p := by
      change ((H.symm (H a)).1, (H.symm (H a)).2.val) = p
      rw [H.symm_apply_apply]

/-- On the nonzero cotangent chart, the extension's inverse is also a right inverse. -/
theorem unitRadialCotangentState_retraction (g : SmoothMetric M) (c : M)
    (z : CotangentCoordinates)
    (hz : z.1 ∈ (chartAt FourSpace c).target ∧ z.2 ≠ 0) :
    unitRadialCotangentState g c (cotangentRadialRetraction g c z) = z := by
  let q : NonzeroCotangentChart c := ⟨z, hz⟩
  let H := unitTangentCotangentHomeomorph g c
  rw [cotangentRadialRetraction_on g c q]
  exact congrArg Subtype.val (H.apply_symm_apply q)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Technical measure reductions for the actual radial flow. Local image
identities on a compact slab give every time on that slab; a countable
exhaustion then gives the ambient measure. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [CompactSpace M]

theorem unitTangentRadialFlow_zero (g : SmoothMetric M) (o : FrameOrientation g)
    (p : PositiveRadius × UnitTangentBundle g) : unitTangentRadialFlow g o 0 p = p := by
  apply Prod.ext
  · rfl
  · change unitTangentFlowMap g o (p.1.val * 0) p.2 = p.2
    rw [mul_zero, unitTangentFlowMap_zero]

theorem unitTangentRadialFlow_add (g : SmoothMetric M) (o : FrameOrientation g)
    (s t : ℝ) (p : PositiveRadius × UnitTangentBundle g) :
    unitTangentRadialFlow g o (s + t) p =
      unitTangentRadialFlow g o s (unitTangentRadialFlow g o t p) := by
  apply Prod.ext
  · rfl
  · change unitTangentFlowMap g o (p.1.val * (s + t)) p.2 =
      unitTangentFlowMap g o (p.1.val * s)
        (unitTangentFlowMap g o (p.1.val * t) p.2)
    rw [mul_add, unitTangentFlowMap_add]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Smooth coordinate changes for the actual cotangent states used by the
radial geodesic flow. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def cotangentChartTransition (g : SmoothMetric M) (c d : M)
    (p : CotangentCoordinates) : CotangentCoordinates :=
  (chartTransition c d p.1,
    WithLp.toLp 2 (metricInChart g d (chartTransition c d p.1) *ᵥ
      (chartTransitionMatrix c d p.1 *ᵥ
        ((metricInChart g c p.1)⁻¹ *ᵥ WithLp.ofLp p.2))))

theorem cotangentChartTransition_contDiffAt (g : SmoothMetric M) (c d : M)
    (p : CotangentCoordinates) (hp : p.1 ∈ (chartAt FourSpace c).target)
    (hd : (chartAt FourSpace c).symm p.1 ∈ (chartAt FourSpace d).source) :
    ContDiffAt ℝ ∞ (cotangentChartTransition g c d) p := by
  have hφ : ContDiffAt ℝ ∞ (fun q : CotangentCoordinates => chartTransition c d q.1) p :=
    (chartTransition_contDiffAt c d p.1 hp hd).comp p contDiffAt_fst
  have hout : chartTransition c d p.1 ∈ (chartAt FourSpace d).target :=
    (chartAt FourSpace d).map_source hd
  have hG (i j : Fin 4) : ContDiffAt ℝ ∞
      (fun q : CotangentCoordinates => metricInChart g d (chartTransition c d q.1) i j) p :=
    by
      have hOuter : ContDiffAt ℝ ∞ (fun z : FourSpace => metricInChart g d z i j)
          (chartTransition c d p.1) := metricInChart_contDiffAt g d _ hout i j
      exact hOuter.comp p hφ
  have hD (i j : Fin 4) : ContDiffAt ℝ ∞
      (fun q : CotangentCoordinates => chartTransitionMatrix c d q.1 i j) p :=
    (chartTransitionMatrix_contDiffAt c d p.1 hp hd i j).comp p contDiffAt_fst
  have hInv (i j : Fin 4) : ContDiffAt ℝ ∞
      (fun q : CotangentCoordinates => (metricInChart g c q.1)⁻¹ i j) p :=
    (metricInChart_inv_contDiffAt g c p.1 hp
      (metricInChart_posDef g c p.1 hp).det_pos.ne' i j).comp p contDiffAt_fst
  have hP (i : Fin 4) : ContDiffAt ℝ ∞ (fun q : CotangentCoordinates => q.2 i) p := by
    fun_prop
  apply hφ.prodMk
  apply (contDiffAt_piLp 2).mpr
  intro i
  change ContDiffAt ℝ ∞ (fun q : CotangentCoordinates =>
    ∑ j, metricInChart g d (chartTransition c d q.1) i j *
      ∑ k, chartTransitionMatrix c d q.1 j k *
        ∑ l, (metricInChart g c q.1)⁻¹ k l * q.2 l) p
  apply ContDiffAt.sum
  intro j _
  apply (hG i j).mul
  apply ContDiffAt.sum
  intro k _
  apply (hD j k).mul
  exact ContDiffAt.sum (fun l _ => (hInv k l).mul (hP l))

theorem unitChartVelocity_change (g : SmoothMetric M) (o : FrameOrientation g)
    (c d : M) (u : UnitTangentBundle g)
    (hc : u.base ∈ (chartAt FourSpace c).source)
    (hd : u.base ∈ (chartAt FourSpace d).source) :
    unitChartVelocity d u = WithLp.toLp 2
      (chartTransitionMatrix c d (chartAt FourSpace c u.base) *ᵥ
        WithLp.ofLp (unitChartVelocity c u)) := by
  obtain ⟨e, _he, hue⟩ := exists_positive_unitTangent_frame g o u
  have hb : e.base = u.base := congrArg UnitTangentBundle.base hue
  have hce : e.base ∈ (chartAt FourSpace c).source := by rwa [hb]
  have hde : e.base ∈ (chartAt FourSpace d).source := by rwa [hb]
  have hm := frameChartMatrix_change g c d e hce hde
  rw [← hue]
  change WithLp.toLp 2 (fun i => frameChartMatrix g d e i 0) =
    WithLp.toLp 2 (chartTransitionMatrix c d (chartAt FourSpace c e.base) *ᵥ
      (fun i => frameChartMatrix g c e i 0))
  ext i
  exact (congrFun (congrFun hm i) 0).symm

theorem cotangentChartTransition_unitState (g : SmoothMetric M) (o : FrameOrientation g)
    (c d : M) (r : ℝ) (u : UnitTangentBundle g)
    (hc : u.base ∈ (chartAt FourSpace c).source)
    (hd : u.base ∈ (chartAt FourSpace d).source) :
    cotangentChartTransition g c d (unitCotangentState g c r u) =
      unitCotangentState g d r u := by
  have hφ : chartTransition c d (chartAt FourSpace c u.base) = chartAt FourSpace d u.base := by
    rw [chartTransition, (chartAt FourSpace c).left_inv hc]
  have hv : chartTransitionMatrix c d (chartAt FourSpace c u.base) *ᵥ
      WithLp.ofLp (unitChartVelocity c u) = WithLp.ofLp (unitChartVelocity d u) := by
    exact congrArg WithLp.ofLp (unitChartVelocity_change g o c d u hc hd).symm
  have hraise := congrArg WithLp.ofLp (raisedChartVelocity_unitCotangentState g c r u hc)
  apply Prod.ext
  · exact hφ
  · change WithLp.toLp 2
        (metricInChart g d (chartTransition c d (chartAt FourSpace c u.base)) *ᵥ
          (chartTransitionMatrix c d (chartAt FourSpace c u.base) *ᵥ
            WithLp.ofLp (raisedChartVelocity g c (unitCotangentState g c r u)))) = _
    rw [hraise, WithLp.ofLp_smul, Matrix.mulVec_smul, hv, hφ, Matrix.mulVec_smul]
    rfl

theorem cotangentChartTransition_radialState (g : SmoothMetric M) (o : FrameOrientation g)
    (c d : M) (p : PositiveRadius × UnitTangentBundle g)
    (hc : p.2.base ∈ (chartAt FourSpace c).source)
    (hd : p.2.base ∈ (chartAt FourSpace d).source) :
    cotangentChartTransition g c d (unitRadialCotangentState g c p) =
      unitRadialCotangentState g d p :=
  cotangentChartTransition_unitState g o c d p.1.val p.2 hc hd

theorem cotangentChartTransition_retraction (g : SmoothMetric M) (o : FrameOrientation g)
    (c d : M) (z : CotangentCoordinates)
    (hz : z.1 ∈ (chartAt FourSpace c).target ∧ z.2 ≠ 0)
    (hd : (cotangentRadialRetraction g c z).2.base ∈ (chartAt FourSpace d).source) :
    cotangentChartTransition g c d z =
      unitRadialCotangentState g d (cotangentRadialRetraction g c z) := by
  have h := cotangentChartTransition_radialState g o c d (cotangentRadialRetraction g c z)
    (cotangentRadialRetraction_source g c z hz) hd
  rwa [unitRadialCotangentState_retraction g c z hz] at h

end
end PositiveEinsteinFour.Geometry
end


section

/-! Local coordinate expressions of the actual radial flow. Coordinate
composition is proved from the intrinsic group law and actual chart inverses. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Filter Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem cotangentRadialRetraction_continuousAt (g : SmoothMetric M) (c : M)
    (z : CotangentCoordinates)
    (hz : z.1 ∈ (chartAt FourSpace c).target ∧ z.2 ≠ 0) :
    ContinuousAt (cotangentRadialRetraction g c) z := by
  let S : Set CotangentCoordinates := {q | q.1 ∈ (chartAt FourSpace c).target ∧ q.2 ≠ 0}
  have hS : IsOpen S :=
    ((chartAt FourSpace c).open_target.preimage continuous_fst).inter
      (isOpen_compl_singleton.preimage continuous_snd)
  have hc : Continuous (fun q : NonzeroCotangentChart c => cotangentRadialRetraction g c q.val) :=
    (continuous_cotangentRadialInverseOn g c).congr
      (fun q => (cotangentRadialRetraction_on g c q).symm)
  have hcont : ContinuousOn (cotangentRadialRetraction g c) S :=
    continuousOn_iff_continuous_domRestrict.mpr hc
  exact (hcont z hz).continuousAt (hS.mem_nhds hz)

variable [T2Space M] [CompactSpace M]

def radialCoordinateFlow (g : SmoothMetric M) (o : FrameOrientation g)
    (c d : M) (t : ℝ) (z : CotangentCoordinates) : CotangentCoordinates :=
  unitRadialCotangentState g d (unitTangentRadialFlow g o t (cotangentRadialRetraction g c z))

theorem radialCoordinateFlow_at_state (g : SmoothMetric M) (o : FrameOrientation g)
    (c d : M) (t : ℝ) (p : PositiveRadius × UnitTangentBundle g)
    (hc : p.2.base ∈ (chartAt FourSpace c).source) :
    radialCoordinateFlow g o c d t (unitRadialCotangentState g c p) =
      unitRadialCotangentState g d (unitTangentRadialFlow g o t p) := by
  rw [radialCoordinateFlow, cotangentRadialRetraction_state g c p hc]

/-- The intrinsic group law becomes coordinate composition on a genuine
neighborhood of the starting cotangent state. -/
theorem radialCoordinateFlow_add_eventually (g : SmoothMetric M) (o : FrameOrientation g)
    (c m d : M) (s t : ℝ) (p : PositiveRadius × UnitTangentBundle g)
    (hc : p.2.base ∈ (chartAt FourSpace c).source)
    (hm : (unitTangentRadialFlow g o t p).2.base ∈ (chartAt FourSpace m).source) :
    radialCoordinateFlow g o c d (s + t) =ᶠ[𝓝 (unitRadialCotangentState g c p)]
      (radialCoordinateFlow g o m d s ∘ radialCoordinateFlow g o c m t) := by
  have hz : (unitRadialCotangentState g c p).1 ∈ (chartAt FourSpace c).target ∧
      (unitRadialCotangentState g c p).2 ≠ 0 :=
    ⟨(chartAt FourSpace c).map_source hc,
      unitCotangentState_momentum_ne_zero g c p.1.val p.1.property p.2 hc⟩
  have hr := cotangentRadialRetraction_continuousAt g c _ hz
  have hb : ContinuousAt (fun z : CotangentCoordinates =>
      (unitTangentRadialFlow g o t (cotangentRadialRetraction g c z)).2.base)
      (unitRadialCotangentState g c p) :=
    (continuous_unitTangentBase g).continuousAt.comp
      (continuous_snd.continuousAt.comp ((unitTangentRadialFlow_continuous g o t).continuousAt.comp hr))
  have hm' : (unitTangentRadialFlow g o t (cotangentRadialRetraction g c
      (unitRadialCotangentState g c p))).2.base ∈ (chartAt FourSpace m).source := by
    simpa only [cotangentRadialRetraction_state g c p hc] using hm
  filter_upwards [hb.preimage_mem_nhds ((chartAt FourSpace m).open_source.mem_nhds hm')] with z hz'
  change unitRadialCotangentState g d
      (unitTangentRadialFlow g o (s + t) (cotangentRadialRetraction g c z)) =
    unitRadialCotangentState g d (unitTangentRadialFlow g o s
      (cotangentRadialRetraction g m (unitRadialCotangentState g m
        (unitTangentRadialFlow g o t (cotangentRadialRetraction g c z)))))
  rw [cotangentRadialRetraction_state g m _ hz', unitTangentRadialFlow_add]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Continuous differentiability of the actual radial flow is local in cotangent charts
and is stable under its intrinsic time-composition law. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Filter Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [CompactSpace M]

def RadialFlowContDiffAt (g : SmoothMetric M) (o : FrameOrientation g)
    (t : ℝ) (p : PositiveRadius × UnitTangentBundle g) : Prop :=
  ∀ c d : M, p.2.base ∈ (chartAt FourSpace c).source →
    (unitTangentRadialFlow g o t p).2.base ∈ (chartAt FourSpace d).source →
    ContDiffAt ℝ 1 (radialCoordinateFlow g o c d t) (unitRadialCotangentState g c p)

omit [T2Space M] [CompactSpace M] in
theorem radial_state_domain_nhds (g : SmoothMetric M) (c : M)
    (p : PositiveRadius × UnitTangentBundle g)
    (hc : p.2.base ∈ (chartAt FourSpace c).source) :
    {z : CotangentCoordinates | z.1 ∈ (chartAt FourSpace c).target ∧ z.2 ≠ 0} ∈
      𝓝 (unitRadialCotangentState g c p) := by
  apply (((chartAt FourSpace c).open_target.preimage continuous_fst).inter
    (isOpen_compl_singleton.preimage continuous_snd)).mem_nhds
  exact ⟨(chartAt FourSpace c).map_source hc,
    unitCotangentState_momentum_ne_zero g c p.1.val p.1.property p.2 hc⟩

theorem RadialFlowContDiffAt.add (g : SmoothMetric M) (o : FrameOrientation g)
    (s t : ℝ) (p : PositiveRadius × UnitTangentBundle g)
    (hs : RadialFlowContDiffAt g o s (unitTangentRadialFlow g o t p))
    (ht : RadialFlowContDiffAt g o t p) : RadialFlowContDiffAt g o (s + t) p := by
  intro c d hc hd
  let m := (unitTangentRadialFlow g o t p).2.base
  have hm : (unitTangentRadialFlow g o t p).2.base ∈ (chartAt FourSpace m).source :=
    mem_chart_source FourSpace m
  have hmid := ht c m hc hm
  have hout := hs m d hm (by simpa only [← unitTangentRadialFlow_add] using hd)
  have hout' : ContDiffAt ℝ 1 (radialCoordinateFlow g o m d s)
      (radialCoordinateFlow g o c m t (unitRadialCotangentState g c p)) := by
    simpa only [radialCoordinateFlow_at_state g o c m t p hc] using hout
  exact (hout'.comp (unitRadialCotangentState g c p) hmid).congr_of_eventuallyEq
    (radialCoordinateFlow_add_eventually g o c m d s t p hc hm)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Continuous differentiability of the actual exponential in coordinate
charts, including the zero vector. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular Filter Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [CompactSpace M]

theorem radialCoordinateFlow_frame_endpoint (g : SmoothMetric M) (o : FrameOrientation g)
    (c d : M) (e : FrameBundle g) (he : e.base ∈ (chartAt FourSpace c).source)
    (v : FourSpace) (hv : v ≠ 0) :
    (radialCoordinateFlow g o c d 1
      (chartAt FourSpace c e.base, frameMomentumMap g c e v)).1 =
      chartAt FourSpace d (frameExponential g o e v) := by
  let w : ({0}ᶜ : Set FourSpace) := ⟨v, hv⟩
  let q := (euclideanPolarHomeomorph w).1
  let r := (euclideanPolarHomeomorph w).2
  have hvr : r.val • q.val = v :=
    congrArg Subtype.val (euclideanPolarHomeomorph.symm_apply_apply w)
  have hstate : unitRadialCotangentState g c (r, unitTangentTurn e q) =
      (chartAt FourSpace c e.base, frameMomentumMap g c e v) := by
    change unitCotangentState g c r.val (unitTangentTurn e q) = _
    rw [unitCotangentState_turn g c e he, hvr]
  rw [← hstate, radialCoordinateFlow_at_state g o c d 1 _ he]
  change chartAt FourSpace d (unitTangentFlowMap g o (r.val * 1) (unitTangentTurn e q)).base = _
  rw [mul_one, ← hvr, frameExponential_radial]
  rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual scalar first jet and its Dirichlet pairing.  The Hilbert space
below is the closure of smooth first jets, with the value coordinate retained;
no solvability or elliptic estimate is built into its definition. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

/-- Smooth real scalar functions, with their pointwise vector-space structure. -/
def smoothScalarModule (M : Type*) [TopologicalSpace M] [ChartedSpace FourSpace M] :
    Submodule ℝ (M → ℝ) where
  carrier := {a | ContMDiff I4 𝓘(ℝ, ℝ) ∞ a}
  zero_mem' := contMDiff_const
  add_mem' := fun ha hb => ha.add hb
  smul_mem' := fun c a ha => by
    change ContMDiff I4 𝓘(ℝ, ℝ) ∞ (c • a)
    simpa only [Pi.smul_apply, smul_eq_mul] using! contMDiff_const.mul ha

abbrev SmoothScalar := ↥(smoothScalarModule M)

theorem smoothScalarData {μ : Measure (FrameBundle g)}
    (d : ParallelMetricData g μ) (a : SmoothScalar (M := M)) :
    ScalarCovariantData d.toMetricGreenData a :=
  Classical.choice (d.scalarCalculus.toPetersenInput a a.property)

/-- Viewing a smooth scalar on the orthonormal frame bundle. -/
def smoothScalarValue (g : SmoothMetric M) :
    SmoothScalar (M := M) →ₗ[ℝ] C(FrameBundle g, ℝ) where
  toFun a := ⟨fun e => a.val e.base, actual_scalarValue_continuous g a.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Each actual frame component of the scalar differential is linear. -/
def smoothScalarGradient {μ : Measure (FrameBundle g)}
    (d : ParallelMetricData g μ) (i : Fin 4) :
    SmoothScalar (M := M) →ₗ[ℝ] C(FrameBundle g, ℝ) where
  toFun a := ⟨fun e => scalarGradient g a e i,
    actual_scalarGradient_continuous g a.property i⟩
  map_add' a b := by
    ext e
    obtain ⟨f, hf⟩ := ((d.toMetricGreenData.flow i).map 0).surjective e
    change (d.toMetricGreenData.flow i).map 0 f = e at hf
    have h := ((smoothScalarData d (a + b)).derivativeValue i 0 f).unique
      (((smoothScalarData d a).derivativeValue i 0 f).add
        ((smoothScalarData d b).derivativeValue i 0 f))
    simpa only [hf] using! h
  map_smul' c a := by
    ext e
    obtain ⟨f, hf⟩ := ((d.toMetricGreenData.flow i).map 0).surjective e
    change (d.toMetricGreenData.flow i).map 0 f = e at hf
    have h := ((smoothScalarData d (c • a)).derivativeValue i 0 f).unique
      (((smoothScalarData d a).derivativeValue i 0 f).const_mul c)
    simpa only [hf, Pi.smul_apply, smul_eq_mul] using! h

variable {μ : Measure (FrameBundle g)} [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]

abbrev ScalarL2 (g : SmoothMetric M) (μ : Measure (FrameBundle g)) := Lp ℝ 2 μ

def smoothScalarValueL2 (g : SmoothMetric M) (μ : Measure (FrameBundle g))
    [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ] :
    SmoothScalar (M := M) →ₗ[ℝ] ScalarL2 g μ :=
  (ContinuousMap.toLp 2 μ ℝ).toLinearMap.comp (smoothScalarValue g)

def smoothScalarGradientL2 (d : ParallelMetricData g μ) (i : Fin 4) :
    SmoothScalar (M := M) →ₗ[ℝ] ScalarL2 g μ :=
  (ContinuousMap.toLp 2 μ ℝ).toLinearMap.comp (smoothScalarGradient d i)

/-- The value and four derivative coordinates, in a genuine Hilbert product. -/
abbrev ScalarJetL2 (g : SmoothMetric M) (μ : Measure (FrameBundle g)) :=
  PiLp 2 (fun _ : Option (Fin 4) => ScalarL2 g μ)

def smoothScalarFirstJet (d : ParallelMetricData g μ) :
    SmoothScalar (M := M) →ₗ[ℝ] ScalarJetL2 g μ :=
  (WithLp.linearEquiv 2 ℝ (Option (Fin 4) → ScalarL2 g μ)).symm.toLinearMap.comp
    (LinearMap.pi fun j => match j with
      | none => smoothScalarValueL2 g μ
      | some i => smoothScalarGradientL2 d i)

/-- Intrinsic first-order Sobolev space generated by actual smooth scalars. -/
def scalarH1 (d : ParallelMetricData g μ) : Submodule ℝ (ScalarJetL2 g μ) :=
  (LinearMap.range (smoothScalarFirstJet d)).topologicalClosure

def scalarH1Value (d : ParallelMetricData g μ) : scalarH1 d →L[ℝ] ScalarL2 g μ :=
  (PiLp.proj 2 (fun _ : Option (Fin 4) => ScalarL2 g μ) none).comp (scalarH1 d).subtypeL

def scalarH1Gradient (d : ParallelMetricData g μ) (i : Fin 4) :
    scalarH1 d →L[ℝ] ScalarL2 g μ :=
  (PiLp.proj 2 (fun _ : Option (Fin 4) => ScalarL2 g μ) (some i)).comp (scalarH1 d).subtypeL

def smoothScalarToH1 (d : ParallelMetricData g μ) (a : SmoothScalar (M := M)) :
    scalarH1 d :=
  ⟨smoothScalarFirstJet d a, Submodule.le_topologicalClosure _ ⟨a, rfl⟩⟩

@[simp] theorem scalarH1Value_smooth (d : ParallelMetricData g μ)
    (a : SmoothScalar (M := M)) :
    scalarH1Value d (smoothScalarToH1 d a) = smoothScalarValueL2 g μ a := rfl

@[simp] theorem scalarH1Gradient_smooth (d : ParallelMetricData g μ)
    (a : SmoothScalar (M := M)) (i : Fin 4) :
    scalarH1Gradient d i (smoothScalarToH1 d a) = smoothScalarGradientL2 d i a := rfl

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

def ActualJacobiPolarInput (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) : Prop :=
  volumeRatio g ≤ (3 * Real.pi / 4) *
    ((∫ u in (0 : ℝ)..(5 / 8), ∫ e,
        (actualRegularJacobi g hRic e (Real.pi * u)).truncatedDensity
          ∂canonicalFrameMeasure g o) +
      ∫ u in (5 / 8 : ℝ)..1, ∫ e,
        (actualRegularJacobi g hRic e (Real.pi * u)).truncatedDensity
          ∂canonicalFrameMeasure g o)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The continuous mean and its kernel on the actual scalar first-jet
completion.  Mean subtraction changes only the value coordinate. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

section FirstJet

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

/-- A constant as an actual smooth scalar function. -/
def smoothScalarConst (c : ℝ) : SmoothScalar (M := M) :=
  ⟨fun _ => c, contMDiff_const⟩

theorem smoothScalarGradient_const (d : ParallelMetricData g μ) (i : Fin 4) (c : ℝ) :
    smoothScalarGradient d i (smoothScalarConst c) = 0 := by
  ext e
  obtain ⟨f, hf⟩ := ((d.toMetricGreenData.flow i).map 0).surjective e
  change (d.toMetricGreenData.flow i).map 0 f = e at hf
  let s := Classical.choice (d.scalarCalculus.toPetersenInput
    (smoothScalarConst (M := M) c) (smoothScalarConst (M := M) c).property)
  have h := (s.derivativeValue i 0 f).unique (hasDerivAt_const 0 c)
  simpa only [hf] using! h

variable [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]

/-- The constant one in scalar `L²`. -/
def scalarL2One (g : SmoothMetric M) (μ : Measure (FrameBundle g))
    [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ] : ScalarL2 g μ :=
  smoothScalarValueL2 g μ (smoothScalarConst 1)

/-- The genuine constant first jet, with zero derivative coordinates. -/
def scalarH1One (d : ParallelMetricData g μ) : scalarH1 d :=
  smoothScalarToH1 d (smoothScalarConst 1)

@[simp] theorem scalarH1Value_one (d : ParallelMetricData g μ) :
    scalarH1Value d (scalarH1One d) = scalarL2One g μ := rfl

@[simp] theorem scalarH1Gradient_one (d : ParallelMetricData g μ) (i : Fin 4) :
    scalarH1Gradient d i (scalarH1One d) = 0 := by
  change smoothScalarGradientL2 d i (smoothScalarConst 1) = 0
  simp only [smoothScalarGradientL2, LinearMap.comp_apply,
    smoothScalarGradient_const, map_zero]

/-- Integration of the value coordinate, represented by inner product with
the constant one and hence continuous on the actual `H¹` completion. -/
def scalarH1Mean (d : ParallelMetricData g μ) : scalarH1 d →L[ℝ] ℝ :=
  (innerSL ℝ (scalarL2One g μ)).comp (scalarH1Value d)

theorem scalarH1Mean_smooth (d : ParallelMetricData g μ) (a : SmoothScalar (M := M)) :
    scalarH1Mean d (smoothScalarToH1 d a) = ∫ e, a.val e.base ∂μ := by
  change inner ℝ (ContinuousMap.toLp 2 μ ℝ
    (smoothScalarValue g (smoothScalarConst 1)))
    (ContinuousMap.toLp 2 μ ℝ (smoothScalarValue g a)) = _
  rw [ContinuousMap.inner_toLp]
  simp only [conj_trivial]
  change (∫ e, a.val e.base * (1 : ℝ) ∂μ) = _
  simp only [mul_one]

/-- The closed subspace on which the actual value coordinate has mean zero. -/
def scalarH1MeanZero (d : ParallelMetricData g μ) : Submodule ℝ (scalarH1 d) :=
  (scalarH1Mean d).ker

@[simp] theorem mem_scalarH1MeanZero (d : ParallelMetricData g μ) (u : scalarH1 d) :
    u ∈ scalarH1MeanZero d ↔ scalarH1Mean d u = 0 := Iff.rfl

/-- Subtract the constant jet with coefficient equal to the scalar mean. -/
def scalarH1SubtractMean (d : ParallelMetricData g μ) : scalarH1 d →L[ℝ] scalarH1 d :=
  ContinuousLinearMap.id ℝ _ - (scalarH1Mean d).smulRight (scalarH1One d)

theorem scalarH1SubtractMean_apply (d : ParallelMetricData g μ) (u : scalarH1 d) :
    scalarH1SubtractMean d u = u - scalarH1Mean d u • scalarH1One d := rfl

@[simp] theorem scalarH1Gradient_subtractMean (d : ParallelMetricData g μ)
    (u : scalarH1 d) (i : Fin 4) :
    scalarH1Gradient d i (scalarH1SubtractMean d u) = scalarH1Gradient d i u := by
  rw [scalarH1SubtractMean_apply, map_sub, map_smul]
  simp only [scalarH1Gradient_one, smul_zero, sub_zero]

variable [IsProbabilityMeasure μ]

@[simp] theorem scalarH1Mean_one (d : ParallelMetricData g μ) :
    scalarH1Mean d (scalarH1One d) = 1 := by
  rw [scalarH1One, scalarH1Mean_smooth]
  simp only [smoothScalarConst, integral_const, probReal_univ, one_smul]

@[simp] theorem scalarH1Mean_subtractMean (d : ParallelMetricData g μ) (u : scalarH1 d) :
    scalarH1Mean d (scalarH1SubtractMean d u) = 0 := by
  rw [scalarH1SubtractMean_apply, map_sub, map_smul]
  simp only [scalarH1Mean_one, smul_eq_mul, mul_one, sub_self]

@[simp] theorem scalarH1SubtractMean_idempotent (d : ParallelMetricData g μ)
    (u : scalarH1 d) :
    scalarH1SubtractMean d (scalarH1SubtractMean d u) = scalarH1SubtractMean d u := by
  rw [scalarH1SubtractMean_apply, scalarH1Mean_subtractMean, zero_smul, sub_zero]

/-- Subtracting the actual integral preserves smoothness. -/
def smoothScalarSubtractMean (a : SmoothScalar (M := M)) : SmoothScalar (M := M) :=
  a - (∫ e, a.val e.base ∂μ) • smoothScalarConst 1

omit [IsProbabilityMeasure μ] in
theorem smoothScalarSubtractMean_toH1 (d : ParallelMetricData g μ)
    (a : SmoothScalar (M := M)) :
    smoothScalarToH1 d (smoothScalarSubtractMean (μ := μ) a) =
      scalarH1SubtractMean d (smoothScalarToH1 d a) := by
  rw [scalarH1SubtractMean_apply, scalarH1Mean_smooth]
  apply Subtype.ext
  change smoothScalarFirstJet d (a - (∫ e, a.val e.base ∂μ) • smoothScalarConst 1) = _
  rw [map_sub, map_smul]
  rfl

omit [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ] [IsProbabilityMeasure μ] in
@[simp] theorem smoothScalarGradient_subtractMean (d : ParallelMetricData g μ)
    (a : SmoothScalar (M := M)) (i : Fin 4) :
    smoothScalarGradient d i (smoothScalarSubtractMean (μ := μ) a) =
      smoothScalarGradient d i a := by
  unfold smoothScalarSubtractMean
  rw [map_sub, map_smul, smoothScalarGradient_const, smul_zero, sub_zero]

omit [IsProbabilityMeasure μ] in
@[simp] theorem smoothScalarGradientL2_subtractMean (d : ParallelMetricData g μ)
    (a : SmoothScalar (M := M)) (i : Fin 4) :
    smoothScalarGradientL2 d i (smoothScalarSubtractMean (μ := μ) a) =
      smoothScalarGradientL2 d i a := by
  rw [← scalarH1Gradient_smooth, smoothScalarSubtractMean_toH1,
    scalarH1Gradient_subtractMean, scalarH1Gradient_smooth]

end FirstJet

end
end PositiveEinsteinFour.Geometry
end


section

/-! Contraction of a smooth third-order tensor by the actual inverse metric. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff

noncomputable section

def covariantMetricTraceThree (G : Mat4) (T : CovariantCoordinates 3) : CovariantCoordinates 1 :=
  fun v => -(∑ a, ∑ b, G a b * T (Fin.cons a (Fin.cons b v)))

theorem covariantMetricTraceThree_frame (E : Mat4) (T : CovariantCoordinates 3) :
    twoFormCodiffTensor (frameTensor E T) =
      frameTensor E (covariantMetricTraceThree (E * Eᵀ) T) := by
  funext v
  have hp : (∑ i, frameTensor E T (Fin.cons i (Fin.cons i v))) =
      frameTensor E (fun w => ∑ a, ∑ b, (E * Eᵀ) a b * T (Fin.cons a (Fin.cons b w))) v := by
    simp only [frameTensor_cons]
    rw [Finset.sum_comm]
    calc
      (∑ a, ∑ i, E a i * ∑ b, E b i * frameTensor E
          (fun w => T (Fin.cons a (Fin.cons b w))) v) =
          ∑ a, ∑ b, (∑ i, E a i * E b i) * frameTensor E
            (fun w => T (Fin.cons a (Fin.cons b w))) v := by
        apply Finset.sum_congr rfl
        intro a _
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro b _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by
        symm
        rw [frameTensor_sum]
        apply Finset.sum_congr rfl
        intro a _
        rw [frameTensor_sum]
        apply Finset.sum_congr rfl
        intro b _
        rw [frameTensor_const_mul]
        rfl
  have hi (i : Fin 4) : ![i,i,v 0] = Fin.cons i (Fin.cons i v) := by
    ext a
    fin_cases a <;> rfl
  change -(∑ i, frameTensor E T ![i,i,v 0]) = _
  simp_rw [hi]
  rw [hp]
  exact (frameTensor_neg E _ v).symm

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {n : ℕ}

def covariantMetricTraceField (g : SmoothMetric M) (T : M → CovariantCoordinates 3) :
    M → CovariantCoordinates 1 :=
  fun x => covariantMetricTraceThree (chartMetric g x)⁻¹ (T x)

theorem covariantMetricTraceField_framed (T : M → CovariantCoordinates 3) (e : FrameBundle g) :
    covariantFieldFramed g (covariantMetricTraceField g T) e =
      twoFormCodiffTensor (covariantFieldFramed g T e) := by
  simp only [covariantFieldFramed_eq]
  rw [covariantMetricTraceThree_frame, e.frame.matrix_mul_transpose]
  rfl

theorem covariantFieldFramed_chart (T : M → CovariantCoordinates n)
    (c : M) (S : Mat4) (hS : Sᵀ * S = 1) (z : ChartTarget c) :
    covariantFieldFramed g T (chartGramSection g c S hS z) =
      frameTensor (chartGramMatrix g c S z) (covariantFieldCoordinates T c z) := by
  rw [covariantFieldFramed_eq]
  change frameTensor (chartInverseMatrix c z * chartGramMatrix g c S z) (T _) = _
  rw [frameTensor_mul]
  rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! Reversing the actual frame orientation exchanges the two Weyl norms.
The plus-block Sobolev argument therefore proves both norm gaps, without
assuming reflection preservation of a fixed oriented frame measure. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped BigOperators Manifold ContDiff

noncomputable section

theorem frameReflectionMatrix_det : frameReflectionMatrix.det = -1 := by
  norm_num [frameReflectionMatrix, Matrix.det_diagonal, Fin.prod_univ_succ, orientationSign]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

theorem OrthonormalFrame.reflect_det {c : M} (e : OrthonormalFrame g c) :
    e.reflect.matrix.det = -e.matrix.det := by
  change (e.matrix * frameReflectionMatrix).det = _
  rw [Matrix.det_mul, frameReflectionMatrix_det, mul_neg_one]

/-- The opposite orientation is the pullback of the original orientation
through the concrete single-axis reflection. -/
def FrameOrientation.reversed (o : FrameOrientation g) : FrameOrientation g where
  positive := frameReflection ⁻¹' o.positive
  clopen := o.clopen.preimage (continuous_frameReflection g)
  nonempty_fiber c := by
    refine ⟨(o.frame c).reflect, ?_⟩
    change (⟨c, (o.frame c).reflect.reflect⟩ : FrameBundle g) ∈ o.positive
    rw [OrthonormalFrame.reflect_reflect]
    exact o.frame_positive c
  compatible c e f he := by
    change (⟨c, e.reflect⟩ : FrameBundle g) ∈ o.positive at he
    change (⟨c, f.reflect⟩ : FrameBundle g) ∈ o.positive ↔ _
    simpa only [OrthonormalFrame.reflect_det, neg_mul_neg] using
      o.compatible c e.reflect f.reflect he

end
end PositiveEinsteinFour.Geometry
end


section

/-! The scalar Sobolev energy as a genuine Hilbert norm.  Only the four
first-derivative coordinates are rescaled; the value coordinate is unchanged. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Function
open scoped Manifold ContDiff BigOperators

noncomputable section

def scalarJetWeight : Option (Fin 4) → ℝ
  | none => 1
  | some _ => Real.sqrt (1 / 2)

theorem scalarJetWeight_ne_zero (j : Option (Fin 4)) : scalarJetWeight j ≠ 0 := by
  cases j with
  | none => norm_num [scalarJetWeight]
  | some i => exact ne_of_gt (Real.sqrt_pos.2 (by norm_num))

def scalarWeightEquiv (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (j : Option (Fin 4)) : E ≃L[ℝ] E where
  toFun u := scalarJetWeight j • u
  invFun u := (scalarJetWeight j)⁻¹ • u
  left_inv u := inv_smul_smul₀ (scalarJetWeight_ne_zero j) u
  right_inv u := smul_inv_smul₀ (scalarJetWeight_ne_zero j) u
  map_add' u v := smul_add _ _ _
  map_smul' r u := by simp only [RingHom.id_apply, smul_smul]; rw [mul_comm]
  continuous_toFun := continuous_const_smul _
  continuous_invFun := continuous_const_smul _

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
  [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]

/-- Invertible diagonal rescaling of the actual scalar first jet. -/
def scalarWeightedJetEquiv (g : SmoothMetric M) (μ : Measure (FrameBundle g)) :
    ScalarJetL2 g μ ≃L[ℝ] ScalarJetL2 g μ :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Option (Fin 4) => ScalarL2 g μ)).trans
    ((ContinuousLinearEquiv.piCongrRight fun j => scalarWeightEquiv (ScalarL2 g μ) j).trans
      (PiLp.continuousLinearEquiv 2 ℝ
        (fun _ : Option (Fin 4) => ScalarL2 g μ)).symm)

omit [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ] in
@[simp] theorem scalarWeightedJetEquiv_none (u : ScalarJetL2 g μ) :
    scalarWeightedJetEquiv g μ u none = u none := by
  change (1 : ℝ) • u none = u none
  exact one_smul _ _

omit [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ] in
@[simp] theorem scalarWeightedJetEquiv_some (u : ScalarJetL2 g μ) (i : Fin 4) :
    scalarWeightedJetEquiv g μ u (some i) = Real.sqrt (1 / 2) • u (some i) := rfl

/-- The closed image of actual smooth first jets, with the Sobolev energy norm. -/
def scalarWeightedH1 (d : ParallelMetricData g μ) : Submodule ℝ (ScalarJetL2 g μ) :=
  (scalarH1 d).map (scalarWeightedJetEquiv g μ).toLinearMap

/-- The weighted energy space is continuously linearly equivalent to actual H¹. -/
def scalarWeightedH1Equiv (d : ParallelMetricData g μ) :
    scalarH1 d ≃L[ℝ] scalarWeightedH1 d :=
  (scalarWeightedJetEquiv g μ).submoduleMap (scalarH1 d)

/-- Continuous recovery of the original first jet, including its value. -/
def scalarWeightedH1ToH1 (d : ParallelMetricData g μ) :
    scalarWeightedH1 d →L[ℝ] scalarH1 d :=
  (scalarWeightedH1Equiv d).symm.toContinuousLinearMap

@[simp] theorem scalarWeightedH1ToH1_equiv (d : ParallelMetricData g μ) (u : scalarH1 d) :
    scalarWeightedH1ToH1 d (scalarWeightedH1Equiv d u) = u :=
  (scalarWeightedH1Equiv d).symm_apply_apply u

/-- A smooth function, regarded as an element of the weighted Hilbert space. -/
def smoothScalarToWeightedH1 (d : ParallelMetricData g μ) :
    SmoothScalar (M := M) →ₗ[ℝ] scalarWeightedH1 d where
  toFun a := scalarWeightedH1Equiv d (smoothScalarToH1 d a)
  map_add' a b := by
    rw [← map_add]
    congr 1
    exact Subtype.ext ((smoothScalarFirstJet d).map_add a b)
  map_smul' r a := by
    rw [← map_smul]
    congr 1
    exact Subtype.ext ((smoothScalarFirstJet d).map_smul r a)

@[simp] theorem scalarWeightedH1ToH1_smooth (d : ParallelMetricData g μ)
    (a : SmoothScalar (M := M)) :
    scalarWeightedH1ToH1 d (smoothScalarToWeightedH1 d a) = smoothScalarToH1 d a :=
  scalarWeightedH1ToH1_equiv d _

end
end PositiveEinsteinFour.Geometry
end


section

/-! The divergence of an actual smooth one-form is a smooth scalar. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

def oneFormDivergence (g : SmoothMetric M) (u : smoothCovariantFields M 1) (x : M) : ℝ :=
  ∑ i, ∑ j, (chartMetric g x)⁻¹ i j * covariantFieldDerivative g u.val x ![i,j]

theorem oneFormDivergence_eq_frame (u : smoothCovariantFields M 1) (e : FrameBundle g) :
    oneFormDivergence g u e.base =
      ∑ i, covariantFieldFramed g (covariantFieldDerivative g u.val) e ![i,i] := by
  simp only [oneFormDivergence, covariantFieldFramed_eq]
  rw [frameTensor_trace_two, e.frame.matrix_mul_transpose]

theorem oneFormDivergence_coordinates (u : smoothCovariantFields M 1)
    (c : M) (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target) :
    oneFormDivergence g u ((chartAt FourSpace c).symm z) =
      ∑ i, ∑ j, (metricInChart g c z)⁻¹ i j *
        covariantFieldCoordinates (covariantFieldDerivative g u.val) c z ![i,j] := by
  have h := oneFormDivergence_eq_frame u (chartGramSection g c 1 (by simp) ⟨z,hz⟩)
  simp_rw [covariantFieldFramed_chart] at h
  rw [frameTensor_trace_two, chartGramMatrix_mul_transpose g c z hz] at h
  exact h

theorem oneFormDivergence_smooth (u : smoothCovariantFields M 1) :
    ContMDiff I4 𝓘(ℝ, ℝ) ∞ (oneFormDivergence g u) := by
  intro c
  have hz := mem_chart_target FourSpace c
  have hchart : ContDiffAt ℝ ∞ (fun z => ∑ i, ∑ j, (metricInChart g c z)⁻¹ i j *
      covariantFieldCoordinates (covariantFieldDerivative g u.val) c z ![i,j])
      (chartAt FourSpace c c) := by
    apply ContDiffAt.sum
    intro i _
    apply ContDiffAt.sum
    intro j _
    exact (metricInChart_inv_contDiffAt g c _ hz
      (metricInChart_posDef g c _ hz).det_pos.ne' i j).mul
        (u.property.derivative (g := g) c _ hz ![i,j])
  have h := hchart.contMDiffAt.comp c
    (contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas c)
      (mem_chart_source FourSpace c))
  apply h.congr_of_eventuallyEq
  filter_upwards [(chartAt FourSpace c).open_source.mem_nhds
    (mem_chart_source FourSpace c)] with x hx
  have he := oneFormDivergence_coordinates (g := g) u c (chartAt FourSpace c x)
    ((chartAt FourSpace c).map_source hx)
  simpa only [Function.comp_apply, (chartAt FourSpace c).left_inv hx] using he

def smoothOneFormDivergence (g : SmoothMetric M) : smoothCovariantFields M 1 →ₗ[ℝ] SmoothScalar (M := M) where
  toFun u := ⟨oneFormDivergence g u, oneFormDivergence_smooth u⟩
  map_add' u v := by
    apply Subtype.ext
    funext x
    have hd := congrFun (covariantFieldDerivative_add (g := g) u v) x
    change (∑ i, ∑ j, (chartMetric g x)⁻¹ i j *
      covariantFieldDerivative g (u + v).val x ![i,j]) = _
    rw [hd]
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    rfl
  map_smul' r u := by
    apply Subtype.ext
    funext x
    have hd := congrFun (covariantFieldDerivative_smul (g := g) r u) x
    change (∑ i, ∑ j, (chartMetric g x)⁻¹ i j *
      covariantFieldDerivative g (r • u).val x ![i,j]) =
        r * (∑ i, ∑ j, (chartMetric g x)⁻¹ i j * covariantFieldDerivative g u.val x ![i,j])
    rw [hd]
    simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm _ r, ← Finset.mul_sum]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Inverse-metric contraction preserves actual smooth covariant fields. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

theorem covariantMetricTraceField_coordinates (T : M → CovariantCoordinates 3)
    (c : M) (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target) :
    covariantFieldCoordinates (covariantMetricTraceField g T) c z =
      covariantMetricTraceThree (metricInChart g c z)⁻¹ (covariantFieldCoordinates T c z) := by
  have h := covariantMetricTraceField_framed T (chartGramSection g c 1 (by simp) ⟨z,hz⟩)
  rw [covariantFieldFramed_chart, covariantFieldFramed_chart,
    covariantMetricTraceThree_frame, chartGramMatrix_mul_transpose g c z hz] at h
  have hi := congrArg (frameTensor ((chartGramMatrix g c 1 z)ᵀ * metricInChart g c z)) h
  simp only [← frameTensor_mul] at hi
  rw [mul_eq_one_comm.mp (chartGramMatrix_normalizes g c 1 (by simp) ⟨z,hz⟩),
    frameTensor_one, frameTensor_one] at hi
  exact hi

theorem CovariantFieldSmooth.metricTrace {T : M → CovariantCoordinates 3}
    (hT : CovariantFieldSmooth T) : CovariantFieldSmooth (covariantMetricTraceField g T) := by
  intro c z hz a
  have hs : ContDiffAt ℝ ∞ (fun w =>
      covariantMetricTraceThree (metricInChart g c w)⁻¹ (covariantFieldCoordinates T c w) a) z := by
    apply ContDiffAt.neg
    apply ContDiffAt.sum
    intro i _
    apply ContDiffAt.sum
    intro j _
    exact (metricInChart_inv_contDiffAt g c z hz
      (metricInChart_posDef g c z hz).det_pos.ne' i j).mul
      (hT c z hz (Fin.cons i (Fin.cons j a)))
  apply hs.congr_of_eventuallyEq
  filter_upwards [(chartAt FourSpace c).open_target.mem_nhds hz] with w hw
  exact congrFun (covariantMetricTraceField_coordinates T c w hw) a

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual pulled-back frame connection has zero radial contraction.
The connection uses the differential of the constructed frame and the
Levi-Civita connection of its base map. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Metric
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def heatNormalFrameConnection (g : SmoothMetric M) (c : M)
    (P : FourSpace → CoordinateFrameSpace) (i : Fin 4) (x : FourSpace) : Mat4 :=
  (P x).2⁻¹ * ((fderiv ℝ P x (coordinateVector i)).2 +
    (∑ r : Fin 4, (fderiv ℝ P x (coordinateVector i)).1 r •
      connectionMatrix g c r (P x).1) * (P x).2)

end
end PositiveEinsteinFour.Geometry
end

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeodesicGeometry05
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The concrete normal-frame data used by the two-form heat construction.
Every field is obtained from the actual radial frame flow. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Metric
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [CompactSpace M]

structure HeatNormalFrameData (g : SmoothMetric M) (o : FrameOrientation g)
    (c : M) (e : FrameBundle g) where
  point : FourSpace → CoordinateFrameSpace
  regular : ContDiffAt ℝ 12 point 0
  initial : point 0 = frameCoordinateState g c e
  radius : ℝ
  radius_pos : 0 < radius
  exponential : ∀ x ∈ ball 0 radius,
    (point x).1 = chartAt FourSpace c (frameExponential g o e x)
  in_chart : ∀ x ∈ ball 0 radius, (point x).1 ∈ (chartAt FourSpace c).target
  orthonormal : ∀ x ∈ ball 0 radius,
    (point x).2ᵀ * metricInChart g c (point x).1 * (point x).2 = 1
  differentiable : ∀ x ∈ ball 0 radius, DifferentiableAt ℝ point x
  radial_connection : ∀ x ∈ ball 0 radius,
    (∑ i : Fin 4, x i • heatNormalFrameConnection g c point i x) = 0
  connection_regular : ∀ i j k : Fin 4,
    ContDiffAt ℝ 11 (fun x => heatNormalFrameConnection g c point i x j k) 0

end
end PositiveEinsteinFour.Geometry
end


section

/-! Coordinate differentiation of the base map and frame matrix in the
normal-frame construction. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem heatLinearForm_coordinate_expansion (L : FourSpace →L[ℝ] ℝ) (v : FourSpace) :
    L v = ∑ i : Fin 4, v i * L (coordinateVector i) := by
  have hv : (∑ i : Fin 4, v i • coordinateVector i) = v :=
    sum_coordinateVector (WithLp.ofLp v)
  calc
    L v = L (∑ i : Fin 4, v i • coordinateVector i) := congrArg L hv.symm
    _ = _ := by rw [map_sum]; simp only [map_smul, smul_eq_mul]

theorem heatFrame_matrixPartial (P : FourSpace → CoordinateFrameSpace) (x : FourSpace)
    (hP : DifferentiableAt ℝ P x) (i : Fin 4) :
    matrixPartial (fun y => (P y).2) i x = (fderiv ℝ P x (coordinateVector i)).2 := by
  ext j k
  let π₁ : Mat4 →L[ℝ] (Fin 4 → ℝ) := ContinuousLinearMap.proj j
  let π₂ : (Fin 4 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj k
  let π : Mat4 →L[ℝ] ℝ := π₂.comp π₁
  have h := π.hasFDerivAt.comp x hP.hasFDerivAt.snd
  have he := congrArg (fun L : FourSpace →L[ℝ] ℝ => L (coordinateVector i)) h.fderiv
  exact he

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem heatFrame_metricPartial (g : SmoothMetric M) (c : M)
    (P : FourSpace → CoordinateFrameSpace) (x : FourSpace)
    (hP : DifferentiableAt ℝ P x) (hx : (P x).1 ∈ (chartAt FourSpace c).target)
    (i : Fin 4) :
    matrixPartial (fun y => metricInChart g c (P y).1) i x =
      (∑ r : Fin 4, (fderiv ℝ P x (coordinateVector i)).1 r •
        connectionMatrix g c r (P x).1)ᵀ * metricInChart g c (P x).1 +
      metricInChart g c (P x).1 *
        (∑ r : Fin 4, (fderiv ℝ P x (coordinateVector i)).1 r •
          connectionMatrix g c r (P x).1) := by
  let v := (fderiv ℝ P x (coordinateVector i)).1
  rw [← parallelFrame_metric_rate g c (P x).1 hx v]
  ext j k
  have hg := ((metricInChart_contDiffAt g c (P x).1 hx j k).differentiableAt
    (by first | simp | exact_mod_cast le_top)).hasFDerivAt
  have h := hg.comp x hP.hasFDerivAt.fst
  have he := congrArg (fun L : FourSpace →L[ℝ] ℝ => L (coordinateVector i)) h.fderiv
  change partialDeriv (fun y => metricInChart g c (P y).1 j k) i x = _
  rw [show partialDeriv (fun y => metricInChart g c (P y).1 j k) i x =
      fderiv ℝ (fun z => metricInChart g c z j k) (P x).1 v from he]
  rw [heatLinearForm_coordinate_expansion]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, matrixPartial, partialDeriv]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Metric compatibility of the actual radially parallel frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Metric
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem heatNormalFrameConnection_skew (g : SmoothMetric M) (c : M)
    (P : FourSpace → CoordinateFrameSpace) (x : FourSpace)
    (hP : DifferentiableAt ℝ P x) (hx : (P x).1 ∈ (chartAt FourSpace c).target)
    (hn : ∀ᶠ y in 𝓝 x, (P y).2ᵀ * metricInChart g c (P y).1 * (P y).2 = 1)
    (i : Fin 4) :
    (heatNormalFrameConnection g c P i x)ᵀ = -heatNormalFrameConnection g c P i x := by
  let E := fun y => (P y).2
  let H := fun y => metricInChart g c (P y).1
  have hE (r s : Fin 4) : DifferentiableAt ℝ (fun y => E y r s) x :=
    differentiableAt_pi.mp (differentiableAt_pi.mp hP.snd r) s
  have hH (r s : Fin 4) : DifferentiableAt ℝ (fun y => H y r s) x := by
    exact ((metricInChart_contDiffAt g c (P x).1 hx r s).differentiableAt
      (by first | simp | exact_mod_cast le_top)).comp x hP.fst
  have hn0 : (E x)ᵀ * H x * E x = 1 := hn.self_of_nhds
  have hdet : (E x).det ≠ 0 := by
    intro hz
    have hh := congrArg Matrix.det hn0
    simp only [Matrix.det_mul, Matrix.det_transpose, hz, zero_mul, Matrix.det_one] at hh
    norm_num at hh
  have heq : (fun y => (E y)ᵀ * (H y * E y)) =ᶠ[𝓝 x] fun _ => 1 := by
    filter_upwards [hn] with y hy
    simpa only [Matrix.mul_assoc] using hy
  have hzero : matrixPartial (fun y => (E y)ᵀ * (H y * E y)) i x = 0 := by
    rw [matrixPartial_congr heq]
    ext r s
    change fderiv ℝ (fun _ : FourSpace => (1 : Mat4) r s) x (coordinateVector i) = 0
    exact congrArg (fun L : FourSpace →L[ℝ] ℝ => L (coordinateVector i))
      (fderiv_const_apply (𝕜 := ℝ) (x := x) ((1 : Mat4) r s))
  have hd := matrixPartial_congruence E H x hE hH i
  rw [hzero] at hd
  have hmatrix : matrixPartial E i x = (fderiv ℝ P x (coordinateVector i)).2 :=
    heatFrame_matrixPartial P x hP i
  have hmetric := heatFrame_metricPartial g c P x hP hx i
  change matrixPartial H i x = _ at hmetric
  rw [hmatrix, hmetric] at hd
  have hc := pulledConnection_metric_compatibility (H x) (E x)
    (fderiv ℝ P x (coordinateVector i)).2
    (∑ r : Fin 4, (fderiv ℝ P x (coordinateVector i)).1 r •
      connectionMatrix g c r (P x).1) (isUnit_iff_ne_zero.mpr hdet)
  rw [hn0, Matrix.mul_one, Matrix.one_mul] at hc
  apply eq_neg_of_add_eq_zero_left
  exact hc.trans hd.symm

variable [T2Space M] [CompactSpace M]

theorem HeatNormalFrameData.connection_skew {g : SmoothMetric M} {o : FrameOrientation g}
    {c : M} {e : FrameBundle g} (D : HeatNormalFrameData g o c e)
    (x : FourSpace) (hx : x ∈ ball 0 D.radius) (i : Fin 4) :
    (heatNormalFrameConnection g c D.point i x)ᵀ =
      -heatNormalFrameConnection g c D.point i x := by
  apply heatNormalFrameConnection_skew g c D.point x (D.differentiable x hx) (D.in_chart x hx)
  filter_upwards [isOpen_ball.mem_nhds hx] with y hy
  exact D.orthonormal y hy

end
end PositiveEinsteinFour.Geometry
end


section

/-! The six-dimensional action of the actual normal-frame connection. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

def heatTwoFormConnectionMatrix (B : Mat4) : Matrix (Fin 6) (Fin 6) ℝ :=
  fun k l => twoFormSkewAction (twoFormExtract B) (EuclideanSpace.basisFun (Fin 6) ℝ l) k

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def heatTwoFormConnection (g : SmoothMetric M) (c : M)
    (P : FourSpace → CoordinateFrameSpace) (i : Fin 4) (x : FourSpace) :
    Matrix (Fin 6) (Fin 6) ℝ :=
  heatTwoFormConnectionMatrix (heatNormalFrameConnection g c P i x)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual Weitzenböck curvature potential in the normal frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def heatNormalFrameCurvature (g : SmoothMetric M) (c : M)
    (P : FourSpace → CoordinateFrameSpace) (x : FourSpace) : CovariantCoordinates 4 :=
  frameTensor (P x).2 (curvatureCoordinates g c (P x).1)

def heatNormalPotential (g : SmoothMetric M) (c : M)
    (P : FourSpace → CoordinateFrameSpace) (x : FourSpace) : TwoFormMatrix :=
  twoFormPotentialMatrix (heatNormalFrameCurvature g c P x)

end
end PositiveEinsteinFour.Geometry
end


section

/-! A continuous intrinsic Jacobian density for the actual exponential.
Its expression in any output chart is the metric density times the
absolute coordinate determinant. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Bundle Set
open scoped Manifold ContDiff _root_.Topology BigOperators

noncomputable section

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

def frameExponentialGram (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (v : FourSpace) : Mat4 := fun i j =>
  g.inner (frameExponential g o e v)
    (mfderiv I4 I4 (frameExponential g o e) v (coordinateVector i))
    (mfderiv I4 I4 (frameExponential g o e) v (coordinateVector j))

def frameExponentialJacobian (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (v : FourSpace) : ℝ := Real.sqrt (frameExponentialGram g o e v).det

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarRegularity07
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.heatSignedTraceENorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Nondivergence form of a local scalar Laplace-type operator applied to
the actual Gaussian ansatz. The coefficients here are their values at the
point of evaluation; no equation or geometric coefficient identity is assumed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped BigOperators ContDiff

noncomputable section

def fourHeatLocalOperator (a : Matrix (Fin 4) (Fin 4) ℝ) (b : Fin 4 → ℝ)
    (c : ℝ) (u : FourSpace → ℝ) (x : FourSpace) : ℝ :=
  -(∑ i : Fin 4, ∑ j : Fin 4, a i j * partialDeriv (partialDeriv u i) j x) +
    (∑ i : Fin 4, b i * partialDeriv u i x) + c * u x

end
end PositiveEinsteinFour.Geometry
end


section

/-! The radial identity for the actual exponential pullback metric,
and the resulting cancellation of the Gaussian eikonal defect. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular Matrix
open scoped Manifold ContDiff _root_.Topology InnerProductSpace BigOperators

noncomputable section

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

abbrev heatNormalMetric (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (v : FourSpace) : Mat4 :=
  frameExponentialGram g o e v

end
end PositiveEinsteinFour.Geometry
end


section

/-! The local six-component heat operator in a radial frame. The additional
first-order Gaussian term vanishes by the radial connection identity. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators ContDiff

noncomputable section

def fourHeatBundleFirst (B : Fin 4 → HeatMat6) (u : FourSpace → Fin 6 → ℝ)
    (x : FourSpace) (k : Fin 6) : ℝ :=
  ∑ i : Fin 4, ∑ l : Fin 6, B i k l * partialDeriv (fun y => u y l) i x

def fourHeatBundleZero (C : HeatMat6) (u : FourSpace → Fin 6 → ℝ)
    (x : FourSpace) (k : Fin 6) : ℝ := ∑ l : Fin 6, C k l * u x l

def fourHeatBundleOperator (a : Mat4) (b : Fin 4 → ℝ)
    (B : Fin 4 → HeatMat6) (C : HeatMat6) (u : FourSpace → Fin 6 → ℝ)
    (x : FourSpace) (k : Fin 6) : ℝ :=
  fourHeatLocalOperator a b 0 (fun y => u y k) x +
    fourHeatBundleFirst B u x k + fourHeatBundleZero C u x k

end
end PositiveEinsteinFour.Geometry
end


section

/-! The leading scalar heat transport equation in density divergence form. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter
open scoped _root_.Topology BigOperators

noncomputable section

def fourHeatDensityDrift (a : FourSpace → Mat4) (J : FourSpace → ℝ)
    (x : FourSpace) (j : Fin 4) : ℝ :=
  -((∑ i : Fin 4, partialDeriv (fun y => a y i j) i x) +
    (J x)⁻¹ * ∑ i : Fin 4, a x i j * partialDeriv J i x)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The regular radial integral used to construct successive heat
coefficients, including at the origin. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Filter Metric
open scoped ContDiff _root_.Topology Interval

noncomputable section

def fourHeatRadialAverage (m : ℕ) (f : FourSpace → ℝ) (x : FourSpace) : ℝ :=
  ∫ s : ℝ in 0..1, s ^ m * f (s • x)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Lower-order coefficients contributed by the normal-frame connection. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

def fourHeatConnectionFirst (a : Mat4) (A : Fin 4 → HeatMat6) (i : Fin 4) : HeatMat6 :=
  (-2 : ℝ) • ∑ j : Fin 4, a i j • A j

def fourHeatConnectionZero (a : Mat4) (b : Fin 4 → ℝ)
    (A : Fin 4 → FourSpace → HeatMat6) (V : HeatMat6) (x : FourSpace) : HeatMat6 :=
  V + (∑ i : Fin 4, b i • A i x) -
    ∑ i : Fin 4, ∑ j : Fin 4, a i j •
      ((Matrix.of fun k l => partialDeriv (fun y => A i y k l) j x) + A j x * A i x)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Lower-order coefficients contributed by the normal-frame connection. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

def fourHeatOneConnectionFirst (a : Mat4) (A : Fin 4 → Mat4) (i : Fin 4) : Mat4 :=
  (-2 : ℝ) • ∑ j : Fin 4, a i j • A j

def fourHeatOneConnectionZero (a : Mat4) (b : Fin 4 → ℝ)
    (A : Fin 4 → FourSpace → Mat4) (V : Mat4) (x : FourSpace) : Mat4 :=
  V + (∑ i : Fin 4, b i • A i x) -
    ∑ i : Fin 4, ∑ j : Fin 4, a i j •
      ((Matrix.of fun k l => partialDeriv (fun y => A i y k l) j x) + A j x * A i x)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual normal-coordinate density and its leading scalar heat
amplitude. Their normalization is obtained from the differential of the
geometric exponential at zero. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter Set Metric
open scoped Manifold ContDiff _root_.Topology

noncomputable section

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

def heatNormalLeadingAmplitude (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (v : FourSpace) : ℝ :=
  (Real.sqrt (frameExponentialJacobian g o e v))⁻¹

end
end PositiveEinsteinFour.Geometry
end


section

/-! Solving the inhomogeneous radial transport equation by the actual
integral with a nonvanishing leading amplitude. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped ContDiff

noncomputable section

def fourHeatWeightedRadialAverage (m : ℕ) (U F : FourSpace → ℝ) (x : FourSpace) : ℝ :=
  U x * fourHeatRadialAverage m (fun y => F y / U y) x

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual normalized leading scalar amplitude solves its transport
equation on a normal-coordinate ball. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter Metric
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

abbrev heatNormalDrift (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (x : FourSpace) : Fin 4 → ℝ :=
  fourHeatDensityDrift (fun y => (heatNormalMetric g o e y)⁻¹)
    (frameExponentialJacobian g o e) x

end
end PositiveEinsteinFour.Geometry
end


section

/-! The scalar heat coefficients are actual integrals. Their finite
regularity and transport equations follow from the radial integral solver. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped ContDiff

noncomputable section

def fourHeatCoefficient (a : FourSpace → Mat4) (b : FourSpace → Fin 4 → ℝ)
    (c U : FourSpace → ℝ) : ℕ → FourSpace → ℝ
  | 0 => U
  | m + 1 => fourHeatWeightedRadialAverage m U
      (fun x => -fourHeatLocalOperator (a x) (b x) (c x) (fourHeatCoefficient a b c U m) x)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual finite smooth extensions of the normal-coordinate coefficients.
They agree with the geometric operator near the center. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter Metric
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

structure HeatNormalExtension (n : ℕ) (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) where
  a : FourSpace → Mat4
  b : FourSpace → Fin 4 → ℝ
  U : FourSpace → ℝ
  a_regular : ∀ i j, ContDiff ℝ n (fun x => a x i j)
  b_regular : ∀ i, ContDiff ℝ n (fun x => b x i)
  U_regular : ContDiff ℝ n U
  U_pos : ∀ x, 0 < U x
  a_near : a =ᶠ[𝓝 0] (fun x => (heatNormalMetric g o e x)⁻¹)
  b_near : b =ᶠ[𝓝 0] heatNormalDrift g o e
  U_near : U =ᶠ[𝓝 0] heatNormalLeadingAmplitude g o e

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual finite-regularity coefficients of the two-form operator in
normal coordinates and the radially parallel frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Metric
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

def heatNormalBundleFirst {g : SmoothMetric M} {o : FrameOrientation g}
    {c : M} {e : FrameBundle g} (D : HeatNormalFrameData g o c e)
    (x : FourSpace) (i : Fin 4) : HeatMat6 :=
  fourHeatConnectionFirst (heatNormalMetric g o e x)⁻¹
    (fun j => heatTwoFormConnection g c D.point j x) i

def heatNormalBundleZero {g : SmoothMetric M} {o : FrameOrientation g}
    {c : M} {e : FrameBundle g} (D : HeatNormalFrameData g o c e)
    (x : FourSpace) : HeatMat6 :=
  fourHeatConnectionZero (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x)
    (heatTwoFormConnection g c D.point) (heatNormalPotential g c D.point x) x

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual finite-regularity coefficients of the one-form operator in
normal coordinates and the radially parallel frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Metric
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

def heatNormalOneFirst {g : SmoothMetric M} {o : FrameOrientation g}
    {c : M} {e : FrameBundle g} (D : HeatNormalFrameData g o c e)
    (x : FourSpace) (i : Fin 4) : Mat4 :=
  fourHeatOneConnectionFirst (heatNormalMetric g o e x)⁻¹
    (fun j => heatNormalFrameConnection g c D.point j x) i

def heatNormalOneZero {g : SmoothMetric M} {o : FrameOrientation g}
    {c : M} {e : FrameBundle g} (D : HeatNormalFrameData g o c e)
    (x : FourSpace) : Mat4 :=
  fourHeatOneConnectionZero (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x)
    (heatNormalFrameConnection g c D.point) (((3 : ℝ) • (1 : Mat4))) x

end
end PositiveEinsteinFour.Geometry
end


section

/-! One global finite-smooth family extends all actual normal
coefficients near a given frame, with a positive leading amplitude. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

structure HeatFamilySmoothCoefficients where
  a : HeatRadialFrameSpace → Mat4
  b : HeatRadialFrameSpace → Fin 4 → ℝ
  B : HeatRadialFrameSpace → Fin 4 → HeatMat6
  C : HeatRadialFrameSpace → HeatMat6
  U : HeatRadialFrameSpace → ℝ
  a_regular : ∀ i j, ContDiff ℝ 10 (fun z => a z i j)
  b_regular : ∀ i, ContDiff ℝ 10 (fun z => b z i)
  B_regular : ∀ i k l, ContDiff ℝ 10 (fun z => B z i k l)
  C_regular : ∀ k l, ContDiff ℝ 10 (fun z => C z k l)
  U_regular : ContDiff ℝ 10 U
  U_pos : ∀ z, 0 < U z

end
end PositiveEinsteinFour.Geometry
end


section

/-! Finite smooth extensions of the actual normal-frame bundle coefficients. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

structure HeatNormalBundleExtension {g : SmoothMetric M} {o : FrameOrientation g}
    {c : M} {e : FrameBundle g} (D : HeatNormalFrameData g o c e) where
  base : HeatNormalExtension 10 g o e
  B : FourSpace → Fin 4 → HeatMat6
  C : FourSpace → HeatMat6
  B_regular : ∀ i k l, ContDiff ℝ 10 (fun x => B x i k l)
  C_regular : ∀ k l, ContDiff ℝ 10 (fun x => C x k l)
  B_near : B =ᶠ[𝓝 0] heatNormalBundleFirst D
  C_near : C =ᶠ[𝓝 0] heatNormalBundleZero D

end
end PositiveEinsteinFour.Geometry
end


section

/-! Finite smooth extensions of the actual normal-frame bundle coefficients. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

structure HeatNormalOneExtension {g : SmoothMetric M} {o : FrameOrientation g}
    {c : M} {e : FrameBundle g} (D : HeatNormalFrameData g o c e) where
  base : HeatNormalExtension 10 g o e
  B : FourSpace → Fin 4 → Mat4
  C : FourSpace → Mat4
  B_regular : ∀ i k l, ContDiff ℝ 10 (fun x => B x i k l)
  C_regular : ∀ k l, ContDiff ℝ 10 (fun x => C x k l)
  B_near : B =ᶠ[𝓝 0] heatNormalOneFirst D
  C_near : C =ᶠ[𝓝 0] heatNormalOneZero D

end
end PositiveEinsteinFour.Geometry
end


section

/-! Successive matrix heat amplitudes are actual radial integrals of the
preceding amplitude under the six-component differential operator. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped BigOperators ContDiff

noncomputable section

def fourHeatBundleCoefficient (a : FourSpace → Mat4) (b : FourSpace → Fin 4 → ℝ)
    (B : FourSpace → Fin 4 → HeatMat6) (C : FourSpace → HeatMat6) (U : FourSpace → ℝ) :
    ℕ → FourSpace → HeatMat6
  | 0 => fun x k l => U x * (if k = l then 1 else 0)
  | m + 1 => fun x k l => fourHeatWeightedRadialAverage m U
      (fun y => -fourHeatBundleOperator (a y) (b y) (B y) (C y)
        (fun z q => fourHeatBundleCoefficient a b B C U m z q l) y k) x

end
end PositiveEinsteinFour.Geometry
end


section

/-! The first four actual normal-frame matrix heat amplitudes and their
transport equations. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter Metric
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

def HeatNormalBundleExtension.amplitude {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g} {D : HeatNormalFrameData g o c e}
    (E : HeatNormalBundleExtension D) : ℕ → FourSpace → HeatMat6 :=
  fourHeatBundleCoefficient E.base.a E.base.b E.B E.C E.base.U

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HodgeTheory08
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Joint C4 one-form amplitudes with the center and frame retained. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour
open scoped ContDiff BigOperators Matrix.Norms.Elementwise
noncomputable section

structure HeatFamilyOneCoefficients where
  base : HeatFamilySmoothCoefficients
  B : HeatRadialFrameSpace → Fin 4 → Mat4
  C : HeatRadialFrameSpace → Mat4
  B_regular : ∀ i k l, ContDiff ℝ 10 (fun z => B z i k l)
  C_regular : ∀ k l, ContDiff ℝ 10 (fun z => C z k l)


end
end PositiveEinsteinFour.Geometry
end


section

/-! A common chart, coefficient extension and actual operator agreement
for every frame in one neighborhood. These are constructed geometric data. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter Metric
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

structure HeatCommonNormalMember (g : SmoothMetric M) (o : FrameOrientation g) (c : M)
    (E : HeatFamilySmoothCoefficients) (r : ℝ) (e : FrameBundle g) where
  frameData : HeatNormalFrameData g o c e
  extension : HeatNormalBundleExtension frameData
  chart : OpenPartialHomeomorph FourSpace M
  radius_le : r ≤ frameData.radius
  point_regular : ∀ x ∈ ball (0 : FourSpace) r, ContDiffAt ℝ 2 frameData.point x
  metric_pos : ∀ x ∈ ball (0 : FourSpace) r, 0 < (heatNormalMetric g o e x).det
  ball_source : ball 0 r ⊆ chart.source
  exponential : EqOn chart (frameExponential g o e) chart.source
  target_chart : chart.target ⊆ (chartAt FourSpace c).source
  inverse_regular : ContMDiffOn I4 I4 4 chart.symm chart.target
  a_family : extension.base.a = fun x => E.a (x, frameCoordinateState g c e)
  b_family : extension.base.b = fun x => E.b (x, frameCoordinateState g c e)
  B_family : extension.B = fun x => E.B (x, frameCoordinateState g c e)
  C_family : extension.C = fun x => E.C (x, frameCoordinateState g c e)
  U_family : extension.base.U = fun x => E.U (x, frameCoordinateState g c e)
  actual : ∀ x ∈ ball (0 : FourSpace) r,
    extension.base.a x = (heatNormalMetric g o e x)⁻¹ ∧
    extension.base.b x = heatNormalDrift g o e x ∧
    extension.B x = heatNormalBundleFirst frameData x ∧
    extension.C x = heatNormalBundleZero frameData x ∧
    extension.base.U x = heatNormalLeadingAmplitude g o e x

end
end PositiveEinsteinFour.Geometry
end


section

/-! One common actual normal family for all three Euler heat degrees. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Set Filter Metric
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

structure HeatCommonEulerMember (g : SmoothMetric M) (o : FrameOrientation g) (c : M)
    (F : HeatFamilyOneCoefficients) (r : ℝ) (e : FrameBundle g) where
  normal : HeatCommonNormalMember g o c F.base r e
  one : HeatNormalOneExtension normal.frameData
  one_base : one.base = normal.extension.base
  point_regular_four : ∀ x ∈ ball (0 : FourSpace) r, ContDiffAt ℝ 4 normal.frameData.point x
  one_B_family : one.B = fun x => F.B (x, frameCoordinateState g c e)
  one_C_family : one.C = fun x => F.C (x, frameCoordinateState g c e)
  one_actual : ∀ x ∈ ball (0 : FourSpace) r,
    one.B x = heatNormalOneFirst normal.frameData x ∧
    one.C x = heatNormalOneZero normal.frameData x

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HodgeTheory09
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The cokernel of actual smooth divergence is measured exactly by the
scalar integral. No upper-degree index identity is assumed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M}

local instance divergenceMeanCompactFrames_r4e575d_1 : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g
abbrev DivergenceCokernel (g : SmoothMetric M) :=
  SmoothScalar (M := M) ⧸ (LinearMap.range (smoothOneFormDivergence g))

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

/-! Every actual member has the regularity and operator identities needed
for Green's formula throughout its common ball. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter Metric
open scoped BigOperators ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M}
  {E : HeatFamilySmoothCoefficients} {r : ℝ} {e : FrameBundle g}

theorem HeatCommonNormalMember.exponential_source (N : HeatCommonNormalMember g o c E r e)
    (x : FourSpace) (hx : x ∈ ball 0 r) :
    frameExponential g o e x ∈ (chartAt FourSpace c).source := by
  rw [← N.exponential (N.ball_source hx)]
  exact N.target_chart (N.chart.map_source (N.ball_source hx))

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

/-! Explicit polar coordinates on the actual round four-sphere. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Set
open scoped BigOperators
noncomputable section

def roundPolarVector (t : ℝ) (q : Directions) : EuclideanSpace ℝ (Fin 5) :=
  WithLp.toLp 2 (Fin.cons (Real.cos t) (fun i => Real.sin t * q.val i))

theorem roundPolarVector_norm (t : ℝ) (q : Directions) : ‖roundPolarVector t q‖ = 1 := by
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]
  change (Real.cos t) ^ 2 + (∑ i : Fin 4, (Real.sin t * q.val i) ^ 2) = 1 ^ 2
  have hq : (∑ i : Fin 4, (q.val i) ^ 2) = 1 := by
    rw [← EuclideanSpace.real_norm_sq_eq, q.property]
    norm_num
  simp_rw [mul_pow]
  rw [← Finset.mul_sum, hq, mul_one]
  nlinarith [Real.sin_sq_add_cos_sq t]

def roundPolarPoint (t : ℝ) (q : Directions) : RoundSphere4 :=
  ⟨roundPolarVector t q, roundPolarVector_norm t q⟩

@[simp] theorem roundPolarPoint_first (t : ℝ) (q : Directions) :
    (roundPolarPoint t q).val 0 = Real.cos t := rfl

@[simp] theorem roundPolarPoint_tail (t : ℝ) (q : Directions) (i : Fin 4) :
    (roundPolarPoint t q).val i.succ = Real.sin t * q.val i := rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! The differential of the standard sphere exponential away from zero,
with the radial norm derivative justified from its squared norm. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Filter Set
open scoped _root_.Topology InnerProductSpace
noncomputable section

def roundSphereLinearInclusion : (ℝ × FourSpace) →L[ℝ] EuclideanSpace ℝ (Fin 5) where
  toFun p := WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2))
  map_add' p q := by
    ext i
    refine Fin.cases ?_ (fun i => ?_) i <;> rfl
  map_smul' a p := by
    ext i
    refine Fin.cases ?_ (fun i => ?_) i <;> rfl
  cont := by fun_prop

@[simp] theorem roundSphereLinearInclusion_first (p : ℝ × FourSpace) :
    roundSphereLinearInclusion p 0 = p.1 := rfl

@[simp] theorem roundSphereLinearInclusion_tail (p : ℝ × FourSpace) (i : Fin 4) :
    roundSphereLinearInclusion p i.succ = p.2 i := rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! The real orthonormal coordinates adapted to a parallel self-dual form
are the usual two complex coordinates. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix
open scoped BigOperators
noncomputable section

def complexCoordinatesLinear : FourSpace ≃ₗ[ℝ] EuclideanSpace ℂ (Fin 2) where
  toFun x := WithLp.toLp 2 ![⟨x 0,x 1⟩, ⟨x 2,x 3⟩]
  invFun z := WithLp.toLp 2 ![(z 0).re,(z 0).im,(z 1).re,(z 1).im]
  left_inv x := by ext i; fin_cases i <;> rfl
  right_inv z := by ext i; fin_cases i <;> rfl
  map_add' x y := by ext i; fin_cases i <;> rfl
  map_smul' r x := by
    ext i
    fin_cases i <;> apply Complex.ext <;> simp

theorem complexCoordinatesLinear_norm (x : FourSpace) :
    ‖complexCoordinatesLinear x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp [complexCoordinatesLinear, Fin.sum_univ_succ, Complex.sq_norm, Complex.normSq_apply]
  ring

def complexCoordinates : FourSpace ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin 2) :=
  { complexCoordinatesLinear with norm_map' := complexCoordinatesLinear_norm }

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeodesicGeometry13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The explicit projective polar points at the Ricci-three scale. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi
open scoped BigOperators
noncomputable section

def complexPolarLift (t : ℝ) (q : Directions) : CP2Vector :=
  WithLp.toLp 2 ![(Real.cos (t / Real.sqrt 2) : ℂ),
    (Real.sin (t / Real.sqrt 2) : ℂ) * complexCoordinates q.val 0,
    (Real.sin (t / Real.sqrt 2) : ℂ) * complexCoordinates q.val 1]

theorem complexPolarLift_norm (t : ℝ) (q : Directions) : ‖complexPolarLift t q‖ = 1 := by
  have hq : ‖complexCoordinates q.val 0‖ ^ 2 + ‖complexCoordinates q.val 1‖ ^ 2 = 1 := by
    calc
      _ = ‖complexCoordinates q.val‖ ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
      _ = 1 := by rw [complexCoordinates.norm_map, q.property]; norm_num
  have hn : ‖complexPolarLift t q‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
    change ‖(Real.cos (t / Real.sqrt 2) : ℂ)‖ ^ 2 +
      ‖(Real.sin (t / Real.sqrt 2) : ℂ) * complexCoordinates q.val 0‖ ^ 2 +
      ‖(Real.sin (t / Real.sqrt 2) : ℂ) * complexCoordinates q.val 1‖ ^ 2 = 1
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    nlinarith [Real.sin_sq_add_cos_sq (t / Real.sqrt 2),
      congrArg (fun r => Real.sin (t / Real.sqrt 2) ^ 2 * r) hq]
  nlinarith [norm_nonneg (complexPolarLift t q)]

theorem complexPolarLift_ne_zero (t : ℝ) (q : Directions) : complexPolarLift t q ≠ 0 := by
  intro h
  have hn := complexPolarLift_norm t q
  rw [h, norm_zero] at hn
  exact zero_ne_one hn

def complexProjectivePolar (t : ℝ) (q : Directions) : ComplexProjective2 :=
  Projectivization.mk ℂ (complexPolarLift t q) (complexPolarLift_ne_zero t q)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual exponential factors through the projective polar quotient.
The resulting map is surjective. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set
open scoped Manifold ContDiff
noncomputable section

structure ComplexProjectivePolarData (p : ComplexProjective2) where
  time : ℝ
  time_mem : time ∈ Icc (0 : ℝ) complexJacobiRadius
  direction : Directions
  point_eq : complexProjectivePolar time direction = p

end
end PositiveEinsteinFour.Geometry
end


section

/-! The compact polar parametrization is a genuine quotient onto CP2. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set
noncomputable section
attribute [local instance] complexProjectiveTopology complexProjective_t2Space

abbrev ComplexPolarDomain := Icc (0 : ℝ) complexJacobiRadius × Directions

end
end PositiveEinsteinFour.Geometry
end


end OAI
end


