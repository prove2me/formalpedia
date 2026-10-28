-- Prove2me | Definitions.Def_OAIQ059C006
-- name    : OAIQ059C006
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T21:49:25.249917+00:00
-- url     : https://prove2.me/theorems/2fb8db53-7c06-403b-aa12-38964140bcd2
-- title:
--   Definitions bundle OAIQ059C006 of the split of OpenAI, Nonuniqueness for bounded measurable scalar conductivities in three dimensions (result family 365)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ScalarConductivity.main_nonuniqueness`, carved from OpenAI's openai/math development (OpenAI, *Nonuniqueness for bounded measurable scalar conductivities in three dimensions (result family 365)*, OpenAI Math Release, September 23, 2026, result family 365, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 235 declarations of OpenAI's Lean: 79 definitions and 156 theorems. The definitions and types are `OAI.ScalarConductivity.PhysicalFiniteEndingData.cartesianTensor`, `OAI.ScalarConductivity.PhysicalFiniteEndingData.correctedEndJet`, `OAI.ScalarConductivity.PhysicalFiniteEndingData.endRepresentative`, `OAI.ScalarConductivity.PhysicalFiniteEndingData.terminalProfile`, `OAI.ScalarConductivity.PhysicalFiniteEndingData.terminalProfileChild`, `OAI.ScalarConductivity.PhysicalFiniteEndingData.terminalProfileParent`, `OAI.ScalarConductivity.PhysicalFiniteEndingData.terminalValue`, `OAI.ScalarConductivity.PhysicalFiniteEndingData.traces`, `OAI.ScalarConductivity.RectFootprint.average`, `OAI.ScalarConductivity.VanishingCorrectionRegion.piola`, `OAI.ScalarConductivity.allVoltageGradients`, `OAI.ScalarConductivity.attachedCollarTensor`, `OAI.ScalarConductivity.attachedEndFlatCLM`, `OAI.ScalarConductivity.attachedEndGradientCLM`, `OAI.ScalarConductivity.attachedEndGradientL`, `OAI.ScalarConductivity.attachedEndPoissonField`, `OAI.ScalarConductivity.attachedEndPoissonJet`, `OAI.ScalarConductivity.attachedFaceTensorList`, `OAI.ScalarConductivity.attachedFlatTestCovector`, `OAI.ScalarConductivity.attachedPatchTensor`, `OAI.ScalarConductivity.attachedPeriodicField`, `OAI.ScalarConductivity.attachedPeriodicFlux`, `OAI.ScalarConductivity.attachedPeriodicFluxFace`, `OAI.ScalarConductivity.attachedPhysicalFlatTensor`, `OAI.ScalarConductivity.attachedPhysicalJet`, `OAI.ScalarConductivity.boxAverage`, `OAI.ScalarConductivity.branchCorrection`, `OAI.ScalarConductivity.branchFluxCorrection`, `OAI.ScalarConductivity.branchSplicedField`, `OAI.ScalarConductivity.branchSplicedFlux`, `OAI.ScalarConductivity.centralAmbientEnergy`, `OAI.ScalarConductivity.centralAmbientQ`, `OAI.ScalarConductivity.centralAnchorAverage`, `OAI.ScalarConductivity.centralCoercivityConstant`, `OAI.ScalarConductivity.centralFullJetCLM`, `OAI.ScalarConductivity.centralInteriorCompletion`, `OAI.ScalarConductivity.centralInteriorComponentCLM`, `OAI.ScalarConductivity.centralInteriorJetCLM`, `OAI.ScalarConductivity.centralJoinChildCutoff`, `OAI.ScalarConductivity.centralJoinPartition` and 39 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `Conductivity_Branching_AttachedCutLayer`, `Conductivity_Branching_AttachedEndGradientL2`, `Conductivity_Branching_AttachedEndL2`, `Conductivity_Branching_AttachedEndLayer`, `Conductivity_Branching_AttachedEndLinear`, `Conductivity_Branching_AttachedFlatTransport`, `Conductivity_Branching_BranchFiniteEnding`, `Conductivity_Branching_CentralJoinCover`, `Conductivity_Branching_ChildCentralL2`, `Conductivity_Branching_ChildLocalizedJet`, `Conductivity_Branching_CollarMeasureTransport`, `Conductivity_Branching_FlatEndingSplice`, `Conductivity_Branching_ParentCentralL2`, `Conductivity_Branching_ParentLocalizedJet`, `Conductivity_Branching_PhysicalBlockRepresentative`, `Conductivity_Branching_PhysicalFiniteEndingData`, `Conductivity_Branching_PhysicalRankTransport`, `Conductivity_Branching_SmoothFamilyCorrectionTransport`, `Conductivity_Flux_AttachedEndDifferential`, `Conductivity_Flux_CentralDistributionLaplacian`, `Conductivity_Flux_CollarCartesianDifferential`, `Conductivity_Flux_PhysicalEndDifferential`, `Conductivity_Flux_PhysicalTensorPatch`, `Conductivity_Flux_VariableBlockTensor`, `Conductivity_Flux_VoltageFluxConstraints`, `Conductivity_Fourier_AttachedEndPoisson`, `Conductivity_Fourier_AttachedPeriodicFlux`, `Conductivity_Fourier_EndPoissonDifferential`, `Conductivity_Fourier_EndPoissonJets`, `Conductivity_Fourier_EndPoissonRepresentative`, `Conductivity_Fourier_PoissonTraceRate`, `Conductivity_Fourier_TorusPoissonContinuous`, `Conductivity_Geometry_AffineBoxPoincare`, `Conductivity_Geometry_BoxCoordinateBridge`, `Conductivity_Geometry_CollarAE`, `Conductivity_Geometry_CollarLocalInverse`, `Conductivity_Geometry_CollarReverseBound`, `Conductivity_Geometry_ParametricCorrectionRegionPiola`, `Conductivity_Geometry_PhysicalCollarRegularity`, `Conductivity_Geometry_PhysicalEndRegions`, `Conductivity_Geometry_RectanglePoincare`, `Conductivity_Geometry_SmoothCollarRate`, `Conductivity_Geometry_SmoothCollarTrace`, `Conductivity_Geometry_TorusAffineField`, `Conductivity_Sobolev_AttachedEndMatchedH1`, `Conductivity_Sobolev_CentralNeighborhoodCompletion`, `Conductivity_Sobolev_CentralPhysicalRegion`, `Conductivity_Sobolev_CentralPhysicalVariational`, `Conductivity_Sobolev_ChildCompletionJoin`, `Conductivity_Sobolev_ChildH10Transport`, `Conductivity_Sobolev_ChildH1Pullback`, `Conductivity_Sobolev_CollarLpPullback`, `Conductivity_Sobolev_CutAttachedEndH1`, `Conductivity_Sobolev_FiniteEndPhysicalH1`, `Conductivity_Sobolev_LocalJoinedH1`, `Conductivity_Sobolev_LocalPhysicalCorrectionBound`, `Conductivity_Sobolev_OriginalSmoothMultiplier`, `Conductivity_Sobolev_ParentCompletionJoin`, `Conductivity_Sobolev_VoltageJetCompletion`, `Conductivity_Sources_CentralWeightedVariational`, `Conductivity_Sources_ParametricPullback`, `Conductivity_Variational_CentralAnchor`, `Conductivity_Variational_CentralCoercivitySmooth`, `Conductivity_Variational_CentralCorrectedRepresentative`, `Conductivity_Variational_CentralEnergySpace`, `Conductivity_Variational_CentralLocalAgreement`, `Conductivity_Variational_CompletePhysicalAttachment`, `Conductivity_Variational_FieldVectorCLM`, `Conductivity_Variational_LocalBoundedPiolaCorrection`, `Conductivity_Variational_PhysicalStripIntegral`, `Conductivity_Variational_PhysicalTerminalBands`, `Conductivity_Variational_PhysicalTestEnergy`, `Conductivity_Variational_WholeBallJetFormula`, `Conductivity_Walls_WallSideMoments`.
--
--   **Imports.** It imports the published bundle `Def_Conductivity`; the bundles `OAIQ059C003` and `OAIQ059C004` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ059C008`; the statements `OAI.ScalarConductivity.PhysicalFiniteEndingData.corrected_block_smooth_green`, `OAI.ScalarConductivity.PhysicalFiniteEndingData.corrected_pair_representative`, `OAI.ScalarConductivity.PhysicalFiniteEndingData.endRepresentative_regular`, `OAI.ScalarConductivity.attachedPeriodicFlux_smooth_green`, `OAI.ScalarConductivity.complete_physical_attachment`, `OAI.ScalarConductivity.fullAttachedEnd_smooth_green_neg` and `OAI.ScalarConductivity.fullAttachedEnd_smooth_green_pos`; the proofs of `OAI.ScalarConductivity.PhysicalFiniteEndingData.corrected_pair_representative`, `OAI.ScalarConductivity.attachedPeriodicFlux_smooth_green`, `OAI.ScalarConductivity.central_pair_regular_exists` and `OAI.ScalarConductivity.complete_physical_attachment`.
-- source:
--   OpenAI, Nonuniqueness for bounded measurable scalar conductivities in three dimensions (result family 365), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 365; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-for-Bounded-Measurable-Scalar-Conductivities-in-Three-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_Conductivity
import Definitions.Def_OAIQ059C003
import Definitions.Def_OAIQ059C004

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_AffineBoxPoincare
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace _root_.OAI.ScalarConductivity.centralMeasure_finite _root_.OAI.ScalarConductivity.instCoeFunSubtypeForallBox3RealMemSubmoduleCentralSmoothFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory

def boxAverage (a r : Box3) (f : Box3 → ℝ) : ℝ :=
  unitCubeAverage (fun z => f (boxRescale a r z))

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_RectanglePoincare
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace _root_.OAI.ScalarConductivity.centralMeasure_finite _root_.OAI.ScalarConductivity.instCoeFunSubtypeForallBox3RealMemSubmoduleCentralSmoothFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory

def RectFootprint.average (Q : RectFootprint) (lo hi : ℝ) (f : Box3 → ℝ) : ℝ :=
  boxAverage ((Q.xl,Q.yl),lo) ((Q.xu-Q.xl,Q.yu-Q.yl),hi-lo) f

open Set MeasureTheory

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_CentralAnchor
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace _root_.OAI.ScalarConductivity.centralMeasure_finite _root_.OAI.ScalarConductivity.instCoeFunSubtypeForallBox3RealMemSubmoduleCentralSmoothFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory

def centralAnchorAverage (n : ℕ) (f : Box3 → ℝ) : ℝ :=
  (centralAnchorData n).1.average (centralAnchorData n).2.1 (centralAnchorData n).2.2 f

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_EndPoissonJets
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace _root_.OAI.ScalarConductivity.spectralTraceGraph_realInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity

section
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal

def endPoissonSequence (s : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (R : ℝ) (hR : 0 ≤ R) (f : spectralTraceGraph (torusRate s)) (j : Fin 4) :
    lp (fun _ : TorusModes => FiniteAxisL2 R) 2 :=
  ⟨fun h => finiteDecayLp (torusRate s h) R (endModeCoefficient s h (f.val 0 h) j),by
    have hu := (lp.memℓp (f.val 0)).summable (by norm_num : 0 < (2:ℝ≥0∞).toReal)
    simp only [ENNReal.toReal_ofNat,Real.rpow_two] at hu
    have hw : Summable (fun h => torusRate s h*‖f.val 0 h‖^2) :=
      (spectralTraceGraph_exists_iff (fun h => Real.sqrt_nonneg _) (f.val 0)).mp ⟨f,rfl⟩
    apply (memℓp_gen_iff (by norm_num : 0 < (2:ℝ≥0∞).toReal)).mpr
    simp only [ENNReal.toReal_ofNat,Real.rpow_two]
    fin_cases j
    · exact (hu.mul_left R).of_nonneg_of_le (fun h => sq_nonneg _)
        (fun h => finiteDecayLp_norm_sq (Real.sqrt_nonneg _) hR (f.val 0 h))
    · exact (hw.div_const 2).of_nonneg_of_le (fun h => sq_nonneg _)
        (fun h => finiteDecayLp_axial_bound (torusRate s h) R (Real.sqrt_nonneg _) (f.val 0 h))
    · exact (hw.mul_left 2).of_nonneg_of_le (fun h => sq_nonneg _)
        (fun h => by simpa [endModeCoefficient,mul_assoc] using finiteDecayLp_angular_bound s hs R h 0 (f.val 0 h))
    · exact (hw.mul_left 2).of_nonneg_of_le (fun h => sq_nonneg _)
        (fun h => by simpa [endModeCoefficient,mul_assoc] using finiteDecayLp_angular_bound s hs R h 1 (f.val 0 h))⟩

local instance instMeasureSpaceUnitAddCircle_solutions_6_r070ee7_1 : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
def endPoissonJet (s : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (R : ℝ) (hR : 0 ≤ R) (f : spectralTraceGraph (torusRate s)) : FiniteCylinderJets R :=
  WithLp.toLp 2 (fun j => cylinderFourier (FiniteAxisMeasure R) (endPoissonSequence s hs R hR f j))

def endPoissonModeJet (s : Fin 3 → ℝ) (R : ℝ) (h : TorusModes) (a : ℂ) : FiniteCylinderJets R :=
  WithLp.toLp 2 (fun j => cylinderMode (FiniteAxisMeasure R) h
    (finiteDecayLp (torusRate s h) R (endModeCoefficient s h a j)))

lemma endPoissonJet_component_hasSum (s : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (R : ℝ) (hR : 0 ≤ R) (f : spectralTraceGraph (torusRate s)) (j : Fin 4) :
    HasSum (fun h => endPoissonModeJet s R h (f.val 0 h) j) (endPoissonJet s hs R hR f j) :=
  cylinderFourier_hasSum (FiniteAxisMeasure R) (endPoissonSequence s hs R hR f j)

end

open Set MeasureTheory Filter Topology
open scoped ENNReal

lemma endModeCoefficient_add (s : Fin 3 → ℝ) (h : TorusModes) (a b : ℂ) (j : Fin 4) :
    endModeCoefficient s h (a+b) j=endModeCoefficient s h a j+endModeCoefficient s h b j := by
  fin_cases j <;> simp [endModeCoefficient,mul_add]

lemma endModeCoefficient_smul (s : Fin 3 → ℝ) (h : TorusModes) (c a : ℂ) (j : Fin 4) :
    endModeCoefficient s h (c*a) j=c*endModeCoefficient s h a j := by
  fin_cases j <;> dsimp [endModeCoefficient] <;> ring

variable (s : Fin 3 → ℝ)
  (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
  (R : ℝ) (hR : 0 ≤ R)

lemma endPoissonSequence_add (f g : spectralTraceGraph (torusRate s)) (j : Fin 4) :
    endPoissonSequence s hs R hR (f+g) j=
      endPoissonSequence s hs R hR f j+endPoissonSequence s hs R hR g j := by
  apply lp.ext
  funext h
  change finiteDecayLp _ _ (endModeCoefficient s h (f.val 0 h+g.val 0 h) j)=_
  rw [endModeCoefficient_add,finiteDecayLp_add]
  rfl

lemma endPoissonSequence_smul (c : ℂ) (f : spectralTraceGraph (torusRate s)) (j : Fin 4) :
    endPoissonSequence s hs R hR (c•f) j=c•endPoissonSequence s hs R hR f j := by
  apply lp.ext
  funext h
  change finiteDecayLp _ _ (endModeCoefficient s h (c*f.val 0 h) j)=_
  rw [endModeCoefficient_smul,finiteDecayLp_smul]
  rfl

lemma endPoissonJet_add (f g : spectralTraceGraph (torusRate s)) :
    endPoissonJet s hs R hR (f+g)=endPoissonJet s hs R hR f+endPoissonJet s hs R hR g := by
  apply PiLp.ext
  intro j
  change cylinderFourier _ (endPoissonSequence _ _ _ _ (f+g) j)=_
  rw [endPoissonSequence_add,map_add]
  rfl

lemma endPoissonJet_smul (c : ℂ) (f : spectralTraceGraph (torusRate s)) :
    endPoissonJet s hs R hR (c•f)=c•endPoissonJet s hs R hR f := by
  apply PiLp.ext
  intro j
  change cylinderFourier _ (endPoissonSequence _ _ _ _ (c•f) j)=_
  rw [endPoissonSequence_smul,map_smul]
  rfl

lemma endPoissonJet_component_norm_sq (f : spectralTraceGraph (torusRate s)) (j : Fin 4) :
    ‖endPoissonJet s hs R hR f j‖^2=
      ∑' h,‖finiteDecayLp (torusRate s h) R (endModeCoefficient s h (f.val 0 h) j)‖^2 :=
  cylinderFourier_norm_sq _ _

lemma endPoissonJet_component_bound (f : spectralTraceGraph (torusRate s)) :
    ‖endPoissonJet s hs R hR f 0‖^2 ≤ R*‖f.val 0‖^2 ∧
    ‖endPoissonJet s hs R hR f 1‖^2 ≤ ‖f.val 1‖^2/2 ∧
    ‖endPoissonJet s hs R hR f 2‖^2 ≤ 2*‖f.val 1‖^2 ∧
    ‖endPoissonJet s hs R hR f 3‖^2 ≤ 2*‖f.val 1‖^2 := by
  have hu := (lp.memℓp (f.val 0)).summable (by norm_num : 0<(2:ℝ≥0∞).toReal)
  simp only [ENNReal.toReal_ofNat,Real.rpow_two] at hu
  have hw : Summable (fun h => torusRate s h*‖f.val 0 h‖^2) :=
    (spectralTraceGraph_exists_iff (fun h => Real.sqrt_nonneg _) (f.val 0)).mp ⟨f,rfl⟩
  have huEq : ‖f.val 0‖^2=∑' h,‖f.val 0 h‖^2 := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
      lp.norm_rpow_eq_tsum (by norm_num : 0<(2:ℝ≥0∞).toReal) (f.val 0)
  have hwEq := spectralGraph_weight_norm_sq (torusRate s) (fun h => Real.sqrt_nonneg _) f
  have hj (j : Fin 4) : Summable (fun h =>
      ‖finiteDecayLp (torusRate s h) R (endModeCoefficient s h (f.val 0 h) j)‖^2) := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two,endPoissonSequence] using
      (lp.memℓp (endPoissonSequence s hs R hR f j)).summable
        (by norm_num : 0<(2:ℝ≥0∞).toReal)
  refine ⟨?_,?_,?_,?_⟩
  · rw [endPoissonJet_component_norm_sq,huEq,←tsum_mul_left]
    exact (hj 0).tsum_le_tsum (fun h => finiteDecayLp_norm_sq (Real.sqrt_nonneg _) hR (f.val 0 h))
      (hu.mul_left R)
  · rw [endPoissonJet_component_norm_sq,hwEq,←tsum_div_const]
    exact (hj 1).tsum_le_tsum (fun h => finiteDecayLp_axial_bound _ _ (Real.sqrt_nonneg _) (f.val 0 h))
      (hw.div_const 2)
  · rw [endPoissonJet_component_norm_sq,hwEq,←tsum_mul_left]
    exact (hj 2).tsum_le_tsum (fun h => by
      simpa [endModeCoefficient,mul_assoc] using finiteDecayLp_angular_bound s hs R h 0 (f.val 0 h))
      (hw.mul_left 2)
  · rw [endPoissonJet_component_norm_sq,hwEq,←tsum_mul_left]
    exact (hj 3).tsum_le_tsum (fun h => by
      simpa [endModeCoefficient,mul_assoc] using finiteDecayLp_angular_bound s hs R h 1 (f.val 0 h))
      (hw.mul_left 2)

lemma endPoissonJet_norm_sq_le (f : spectralTraceGraph (torusRate s)) :
    ‖endPoissonJet s hs R hR f‖^2 ≤ (R+5)*‖f‖^2 := by
  obtain ⟨h0,h1,h2,h3⟩ := endPoissonJet_component_bound s hs R hR f
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [Fin.sum_univ_four]
  rw [spectralGraph_norm_sq]
  nlinarith [sq_nonneg ‖f.val 0‖,sq_nonneg ‖f.val 1‖,mul_nonneg hR (sq_nonneg ‖f.val 1‖)]

lemma endPoissonJet_norm_le (f : spectralTraceGraph (torusRate s)) :
    ‖endPoissonJet s hs R hR f‖ ≤ (R+6)*‖f‖ := by
  have hn := endPoissonJet_norm_sq_le s hs R hR f
  have hb : R+5 ≤ (R+6)^2 := by nlinarith [sq_nonneg R]
  have hh := mul_le_mul_of_nonneg_right hb (sq_nonneg ‖f‖)
  nlinarith [norm_nonneg (endPoissonJet s hs R hR f),norm_nonneg f,
    mul_nonneg (show 0 ≤ R+6 by linarith) (norm_nonneg f)]

def endPoissonCLM : spectralTraceGraph (torusRate s) →L[ℂ] FiniteCylinderJets R :=
  ({ toFun := fun f => endPoissonJet s hs R hR f
     map_add' := endPoissonJet_add s hs R hR
     map_smul' := endPoissonJet_smul s hs R hR } :
    spectralTraceGraph (torusRate s) →ₗ[ℂ] FiniteCylinderJets R).mkContinuous (R+6)
    (endPoissonJet_norm_le s hs R hR)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_CollarReverseBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped NNReal ENNReal

lemma sourceExtended_jacobian_upper (i j : Fin 4) {l r : ℝ}
    (hl : -(1:ℝ)/100≤l) (hr : r≤1/100)
    {x : Fin 3 → ℝ} (hx : x∈sourceExtendedBox l r) :
    abs ((sourceCollarDerivative i j x).det)≤2 := by
  obtain ⟨ht,ha,hb⟩ := mem_sourceExtendedBox.mp hx
  have ht' : x 0∈Icc (-(1:ℝ)/100) (1/100) := ⟨hl.trans ht.1,ht.2.trans hr⟩
  have hR := sourceCollarRadius_extended j ht' hb
  rw [sourceCollarDerivative_det,abs_mul,abs_mul,abs_mul]
  rw [abs_neg,abs_of_pos (show 0 < sourceLength by norm_num [sourceLength]),
    abs_of_nonneg (show 0≤ sourceCollarRadius j (x 0) (x 2) by linarith [hR.1]),
    abs_of_pos (show 0 < sourceRadialWidth by norm_num [sourceRadialWidth,sourceHole]),
    abs_of_nonneg (show 0≤1-x 0 by linarith [ht'.2])]
  have hh := mul_le_mul hR.2 (show 1-x 0≤101/100 by linarith [ht'.1])
    (by linarith [ht'.2] : 0≤1-x 0) (by norm_num : (0:ℝ)≤2)
  norm_num [sourceLength,sourceRadialWidth,sourceHole]
  nlinarith

theorem sourceExtended_integral_upper {g : (Fin 3 → ℝ) → ℝ}
    (hg : Continuous g) (hn : ∀ y,0≤g y) (i j : Fin 4) {l r : ℝ}
    (hl : -(1:ℝ)/100≤l) (hr : r≤1/100) :
    (∫ y in sourceCollarPiece i j '' sourceExtendedBox l r,g y)≤
      2*(∫ x in sourceExtendedBox l r,g (sourceCollarPiece i j x)) := by
  rw [sourceExtended_integral i j hl hr,←integral_const_mul]
  apply setIntegral_mono_on
  · have hc : Continuous (fun x : Fin 3 → ℝ => abs ((sourceCollarDerivative i j x).det)) := by
      simp_rw [sourceCollarDerivative_det]
      unfold sourceCollarRadius squareFace
      fun_prop
    exact (hc.mul (hg.comp (sourceCollarPiece_contDiff i j).continuous)).continuousOn.integrableOn_compact isCompact_Icc
  · exact (continuous_const.mul (hg.comp (sourceCollarPiece_contDiff i j).continuous)).continuousOn.integrableOn_compact isCompact_Icc
  · exact measurableSet_Icc
  · intro x hx
    exact mul_le_mul_of_nonneg_right (sourceExtended_jacobian_upper i j hl hr hx) (hn _)

theorem integral_sourceAngular_lower {f : (Fin 3 → ℝ) → ℝ}
    (hf : Continuous f) (hn : ∀ z,0≤f z) (t : ℝ) :
    (faceRayDensityLower 1*faceRayDensityLower sourceRadialWidth)*
        (∑ i : Fin 4,∑ j : Fin 4,∫ a in (-1:ℝ)..1,∫ b in (-1:ℝ)..1,
          f (sourceCollarPiece i j ![t,a,b])) ≤
      ∫ x : UnitAddTorus (Fin 2),f (sourceAngularCollar t x) := by
  have hw : 0 < sourceRadialWidth := by norm_num [sourceRadialWidth,sourceHole]
  have hk₀ := (faceRayDensityLower_pos (w:=1) (by norm_num)).le
  have hk₁ := (faceRayDensityLower_pos hw).le
  rw [integral_unitTorus_faces (F:=fun x => f (sourceAngularCollar t x))
    (w₀:=1) (w₁:=sourceRadialWidth) (by norm_num) hw
    (hf.comp (continuous_sourceAngularCollar t)),Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  rw [←intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on (by norm_num)
  · exact (continuous_const.mul (continuous_parametric_unitInterval
      (f:=fun a b => f (sourceCollarPiece i j ![t,a,b]))
      (hf.comp (sourceAngularFace_continuous t i j)))).intervalIntegrable _ _
  · exact ((continuous_parametric_unitInterval
      (continuous_torusFaceTerm 1 sourceRadialWidth
        (hf.comp (continuous_sourceAngularCollar t)) i j)).mul
      (continuous_faceRayDensity 1 i)).intervalIntegrable _ _
  · intro a ha
    have hinner : faceRayDensityLower sourceRadialWidth*
        (∫ b in (-1:ℝ)..1,f (sourceCollarPiece i j ![t,a,b])) ≤
        ∫ b in (-1:ℝ)..1,
          torusFaceTerm 1 sourceRadialWidth (fun x => f (sourceAngularCollar t x)) i j a b := by
      rw [←intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_mono_on (by norm_num)
      · exact (continuous_const.mul ((hf.comp (sourceAngularFace_continuous t i j)).comp
          (continuous_const.prodMk continuous_id))).intervalIntegrable _ _
      · exact ((continuous_torusFaceTerm 1 sourceRadialWidth
          (hf.comp (continuous_sourceAngularCollar t)) i j).comp
          (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
      · intro b hb
        dsimp only [torusFaceTerm]
        rw [sourceAngular_face t a b i j (abs_le.mpr ha) (abs_le.mpr hb),mul_comm]
        exact mul_le_mul_of_nonneg_left (faceRayDensity_lower hw j (abs_le.mpr hb)) (hn _)
    have hnint : 0≤ ∫ b in (-1:ℝ)..1,f (sourceCollarPiece i j ![t,a,b]) :=
      intervalIntegral.integral_nonneg (by norm_num) (fun _ _ => hn _)
    calc
      _ = (faceRayDensityLower sourceRadialWidth*
          (∫ b in (-1:ℝ)..1,f (sourceCollarPiece i j ![t,a,b])))*faceRayDensityLower 1 := by ring
      _ ≤ _ := mul_le_mul hinner (faceRayDensity_lower (by norm_num) i (abs_le.mpr ha))
        hk₀ ((mul_nonneg hk₁ hnint).trans hinner)

theorem sourceAngular_volume_reverse {g : (Fin 3 → ℝ) → ℝ}
    (hg : Continuous g) (hn : ∀ y,0≤g y) {l r : ℝ}
    (hlr : l ≤ r) (hl : -(1:ℝ)/100≤l) (hr : r≤1/100) :
    (∑ i : Fin 4,∑ j : Fin 4,∫ y in sourceCollarPiece i j '' sourceExtendedBox l r,g y)≤
      (2/(faceRayDensityLower 1*faceRayDensityLower sourceRadialWidth))*
        (∫ t in l..r,∫ x : UnitAddTorus (Fin 2),g (sourceAngularCollar t x)) := by
  let k := faceRayDensityLower 1*faceRayDensityLower sourceRadialWidth
  have hk : 0<k := mul_pos (faceRayDensityLower_pos (by norm_num))
    (faceRayDensityLower_pos (by norm_num [sourceRadialWidth,sourceHole]))
  have hcont : Continuous (fun t : ℝ => ∫ x : UnitAddTorus (Fin 2),g (sourceAngularCollar t x)) := by
    have hcs : Continuous (fun p : ℝ×UnitAddTorus (Fin 2) => sourceAngularCollar p.1 p.2) := by
      simpa only [zero_add] using continuous_sourceAngular 0
    have hh := continuous_parametric_integral_of_continuous (μ:=volume)
      (f:=fun t (x : UnitAddTorus (Fin 2)) => g (sourceAngularCollar t x))
      (hg.comp hcs) (s:=univ) isCompact_univ
    simpa using hh
  have hsum : Continuous (fun t : ℝ => ∑ i : Fin 4,∑ j : Fin 4,
      ∫ a in (-1:ℝ)..1,∫ b in (-1:ℝ)..1,g (sourceCollarPiece i j ![t,a,b])) :=
    continuous_finsetSum _ (fun i _ => continuous_finsetSum _ (fun j _ => continuous_collarFace_integral hg i j))
  have Hint : k*(∑ i : Fin 4,∑ j : Fin 4,
      ∫ x in sourceExtendedBox l r,g (sourceCollarPiece i j x))≤
      ∫ t in l..r,∫ x : UnitAddTorus (Fin 2),g (sourceAngularCollar t x) := by
    have hh := intervalIntegral.integral_mono_on (μ:=volume) hlr
      ((continuous_const.mul hsum).intervalIntegrable l r)
      (hcont.intervalIntegrable l r) (fun t _ => integral_sourceAngular_lower hg hn t)
    simp only [Pi.mul_apply] at hh
    rw [intervalIntegral.integral_const_mul] at hh
    convert hh using 2
    all_goals try with_reducible_and_instances rfl
    rw [intervalIntegral.integral_finsetSum (fun i _ =>
      (continuous_finsetSum _ (fun j _ => continuous_collarFace_integral hg i j)).intervalIntegrable l r)]
    apply Finset.sum_congr rfl
    intro i _
    rw [intervalIntegral.integral_finsetSum (fun j _ => (continuous_collarFace_integral hg i j).intervalIntegrable l r)]
    apply Finset.sum_congr rfl
    intro j _
    exact integral_sourceExtendedBox (hg.comp (sourceCollarPiece_contDiff i j).continuous) hlr
  calc
    _ ≤ ∑ i : Fin 4,∑ j : Fin 4,2*(∫ x in sourceExtendedBox l r,g (sourceCollarPiece i j x)) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact sourceExtended_integral_upper hg hn i j hl hr
    _ = (2/k)*(k*(∑ i : Fin 4,∑ j : Fin 4,
        ∫ x in sourceExtendedBox l r,g (sourceCollarPiece i j x))) := by
      simp_rw [←Finset.mul_sum]
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left Hint (by positivity)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_CollarMeasureTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped NNReal ENNReal

lemma continuous_uncurry_sourceAngularCollar : Continuous (Function.uncurry sourceAngularCollar) := by
  change Continuous (fun z : ℝ×UnitAddTorus (Fin 2) => sourceAngularCollar z.1 z.2)
  simpa only [zero_add] using continuous_sourceAngular 0

lemma integral_sourceAngularCollarMeasure {f : (Fin 3 → ℝ) → ℝ}
    (hf : Continuous f) {l r : ℝ} (hlr : l ≤ r) :
    (∫ x,f x ∂sourceAngularCollarMeasure l r)=
      ∫ t in l..r,∫ θ : UnitAddTorus (Fin 2),f (sourceAngularCollar t θ) := by
  unfold sourceAngularCollarMeasure
  rw [integral_map continuous_uncurry_sourceAngularCollar.aemeasurable hf.aestronglyMeasurable]
  have hi : Integrable (fun p : ℝ×UnitAddTorus (Fin 2) => f (sourceAngularCollar p.1 p.2))
      ((volume.restrict (Ioc l r)).prod volume) := by
    have hh := (hf.comp continuous_uncurry_sourceAngularCollar).continuousOn.integrableOn_compact (μ:=volume)
      ((isCompact_Icc : IsCompact (Icc l r)).prod (isCompact_univ : IsCompact (univ : Set (UnitAddTorus (Fin 2)))))
    have hh' := hh.mono_set (prod_mono Ioc_subset_Icc_self Subset.rfl)
    simpa only [Function.comp_def,Function.uncurry_def,IntegrableOn,Measure.volume_eq_prod,←Measure.prod_restrict,Measure.restrict_univ] using hh'
  simp only [Function.uncurry]
  rw [integral_prod _ hi,intervalIntegral.integral_of_le hlr]

theorem sourcePhysicalCollarMeasure_le {l r : ℝ}
    (hlr : l ≤ r) (hl : -(1:ℝ)/100≤l) (hr : r≤1/100) :
    sourcePhysicalCollarMeasure l r ≤
      ENNReal.ofReal (2/(faceRayDensityLower 1*faceRayDensityLower sourceRadialWidth)) •
        sourceAngularCollarMeasure l r := by
  have : IsFiniteMeasure
      (ENNReal.ofReal (2/(faceRayDensityLower 1*faceRayDensityLower sourceRadialWidth)) •
        sourceAngularCollarMeasure l r) :=
    ⟨by
      rw [Measure.smul_apply]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)⟩
  apply finiteMeasure_le_of_nonneg_compact_integrals
  intro f hf hcomp hn
  rw [integral_sourcePhysicalCollarMeasure hf,integral_smul_measure,
    ENNReal.toReal_ofReal (by
      have h0 := faceRayDensityLower_pos (w:=1) (by norm_num)
      have h1 := faceRayDensityLower_pos (w:=sourceRadialWidth)
        (by norm_num [sourceRadialWidth,sourceHole])
      positivity),integral_sourceAngularCollarMeasure hf hlr]
  exact sourceAngular_volume_reverse hf hn hlr hl hr

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_CollarLpPullback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped NNReal ENNReal

lemma sourcePhysicalCoordinates_measurePreserving {l r : ℝ}
    (hl : -(1:ℝ)/100≤l) (hr : r≤1/100) :
    MeasurePreserving sourcePhysicalCoordinates (sourceAngularCollarMeasure l r)
      (sourceCylinderMeasure l r) := by
  refine ⟨measurable_sourcePhysicalCoordinates,?_⟩
  unfold sourceAngularCollarMeasure
  rw [←sourceCylinderMeasure_eq]
  rw [Measure.map_map measurable_sourcePhysicalCoordinates continuous_uncurry_sourceAngularCollar.measurable]
  have he : sourcePhysicalCoordinates ∘ Function.uncurry sourceAngularCollar=ᵐ[sourceCylinderMeasure l r] id := by
    have ht : ∀ᵐ z∂sourceCylinderMeasure l r,z.1∈Ioc l r :=
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioc)
    filter_upwards [ht] with z hz
    exact sourcePhysicalCoordinates_angular ⟨hl.trans hz.1.le,hz.2.trans hr⟩ z.2
  rw [Measure.map_congr he,Measure.map_id]

def sourceCollarPullback {l r : ℝ} (hlr : l ≤ r)
    (hl : -(1:ℝ)/100≤l) (hr : r≤1/100) :
    Lp ℂ 2 (sourceCylinderMeasure l r) →L[ℝ]
      Lp ℂ 2 (sourcePhysicalCollarMeasure l r) :=
  (Lp.LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top (sourcePhysicalCollarMeasure_le hlr hl hr)).comp
    (Lp.compMeasurePreservingₗᵢ ℝ sourcePhysicalCoordinates
      (sourcePhysicalCoordinates_measurePreserving hl hr)).toContinuousLinearMap

lemma sourceCollarPullback_ae {l r : ℝ} (hlr : l ≤ r)
    (hl : -(1:ℝ)/100≤l) (hr : r≤1/100) (f : Lp ℂ 2 (sourceCylinderMeasure l r)) :
    sourceCollarPullback hlr hl hr f=ᵐ[sourcePhysicalCollarMeasure l r]
      f ∘ sourcePhysicalCoordinates := by
  have h0 := Lp.coeFn_LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top
    (sourcePhysicalCollarMeasure_le hlr hl hr)
    ((Lp.compMeasurePreservingₗᵢ ℝ sourcePhysicalCoordinates
      (sourcePhysicalCoordinates_measurePreserving hl hr)) f)
  have h1 := Lp.coeFn_compMeasurePreserving f (sourcePhysicalCoordinates_measurePreserving hl hr)
  exact h0.trans ((Measure.absolutelyContinuous_of_le_smul
    (sourcePhysicalCollarMeasure_le hlr hl hr)).ae_eq h1)

lemma sourceCollarPullback_ae_of_ae {l r : ℝ} (hlr : l ≤ r)
    (hl : -(1:ℝ)/100≤l) (hr : r≤1/100) (f : Lp ℂ 2 (sourceCylinderMeasure l r))
    {g : (ℝ×UnitAddTorus (Fin 2)) → ℂ} (hg : f=ᵐ[sourceCylinderMeasure l r] g) :
    sourceCollarPullback hlr hl hr f=ᵐ[sourcePhysicalCollarMeasure l r]
      g ∘ sourcePhysicalCoordinates := by
  apply (sourceCollarPullback_ae hlr hl hr f).trans
  exact (Measure.absolutelyContinuous_of_le_smul (sourcePhysicalCollarMeasure_le hlr hl hr)).ae_eq
    ((sourcePhysicalCoordinates_measurePreserving hl hr).quasiMeasurePreserving.ae_eq_comp hg)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_EndPoissonRepresentative
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace _root_.OAI.ScalarConductivity.spectralTraceGraph_realInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity

section
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal

attribute [local instance] OAI.ScalarConductivity.instMeasureSpaceUnitAddCircle_solutions_7
local instance instIsProbabilityMeasureUnitAddCircleVolume_solutions_7_r070ee7_1 : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
lemma endPoissonModeJet_ae (s : Fin 3 → ℝ) (R : ℝ) (h : TorusModes) (a : ℂ) (j : Fin 4) :
    endPoissonModeJet s R h a j=ᵐ[(FiniteAxisMeasure R).prod volume]
      endPoissonModeField s h a j := by
  have h1 := (Measure.quasiMeasurePreserving_fst
    (μ := FiniteAxisMeasure R) (ν := (volume : Measure (UnitAddTorus (Fin 2))))).ae
    (finiteDecayLp_ae (torusRate s h) R (endModeCoefficient s h a j))
  have h2 := (Measure.quasiMeasurePreserving_snd
    (μ := FiniteAxisMeasure R) (ν := (volume : Measure (UnitAddTorus (Fin 2))))).ae (coeFn_mFourierLp 2 h)
  filter_upwards [cylinderTensor_ae
    (finiteDecayLp (torusRate s h) R (endModeCoefficient s h a j)) (mFourierLp 2 h),h1,h2]
      with z hz h1 h2
  change cylinderTensor _ _ z=_
  rw [hz,h1,h2]
  rfl

lemma endModeCoefficient_norm_bound (s : Fin 3 → ℝ) (h : TorusModes) (a : ℂ) (j : Fin 4) :
    ‖endModeCoefficient s h a j‖ ≤ (1+torusRate s h+torusSize h)*‖a‖ := by
  have hm : 0≤torusRate s h := Real.sqrt_nonneg _
  have hsize := torusSize_nonneg h
  fin_cases j
  · change ‖a‖≤_
    nlinarith [mul_nonneg hm (norm_nonneg a),mul_nonneg hsize (norm_nonneg a)]
  · change ‖-(torusRate s h:ℂ)*a‖≤_
    rw [norm_mul,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hm]
    exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg a)
  · change ‖Complex.I*(h 0:ℂ)*a‖≤_
    rw [norm_mul,norm_mul,Complex.norm_I,one_mul]
    have he : ‖(h 0:ℂ)‖=|(h 0:ℝ)| := by simp
    rw [he]
    have hh : |(h 0:ℝ)|≤torusSize h := le_add_of_nonneg_right (abs_nonneg _)
    exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg a)
  · change ‖Complex.I*(h 1:ℂ)*a‖≤_
    rw [norm_mul,norm_mul,Complex.norm_I,one_mul]
    have he : ‖(h 1:ℂ)‖=|(h 1:ℝ)| := by simp
    rw [he]
    have hh : |(h 1:ℝ)|≤torusSize h := le_add_of_nonneg_left (abs_nonneg _)
    exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg a)

lemma endPoissonField_hasSum (s : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (f : spectralTraceGraph (torusRate s)) (j : Fin 4)
    {z : ℝ × UnitAddTorus (Fin 2)} (hz : 0<z.1) :
    HasSum (fun h => endPoissonModeField s h (f.val 0 h) j z) (endPoissonField s f j z) := by
  apply Summable.hasSum
  apply Summable.of_norm
  have hb : Summable (fun h => ‖f.val 0‖*((1+torusRate s h+torusSize h)*
      Real.exp (-z.1*torusRate s h))) := by
    have h0 := torusRate_exp_summable hs hz
    have h1 := flatMode_derivative_summable hs 1 hz
    simpa only [pow_one,add_mul,one_mul,add_assoc] using (h0.add h1).mul_left ‖f.val 0‖
  apply hb.of_nonneg_of_le (fun h => norm_nonneg _) (fun h => ?_)
  have hc := endModeCoefficient_norm_bound s h (f.val 0 h) j
  have ha := lp.norm_apply_le_norm (by norm_num : (2:ℝ≥0∞)≠0) (f.val 0) h
  have hp : 0≤1+torusRate s h+torusSize h := by
    have hm : 0≤torusRate s h := Real.sqrt_nonneg _
    linarith [torusSize_nonneg h]
  have hc' := hc.trans (mul_le_mul_of_nonneg_left ha hp)
  have hm : ‖mFourier h z.2‖≤1 := by simpa only [mFourier_norm] using (mFourier h).norm_coe_le_norm z.2
  unfold endPoissonModeField
  rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ (Real.exp (-torusRate s h*z.1)*((1+torusRate s h+torusSize h)*‖f.val 0‖))*1 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hc' (Real.exp_nonneg _)) hm (norm_nonneg _)
        (mul_nonneg (Real.exp_nonneg _) (mul_nonneg hp (norm_nonneg _)))
    _ = _ := by rw [show -torusRate s h*z.1= -z.1*torusRate s h by ring]; ring

theorem endPoissonJet_ae (s : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (R : ℝ) (hR : 0≤R) (f : spectralTraceGraph (torusRate s)) (j : Fin 4) :
    endPoissonJet s hs R hR f j=ᵐ[(FiniteAxisMeasure R).prod volume] endPoissonField s f j := by
  apply lp_hasSum_ae_unique (endPoissonJet_component_hasSum s hs R hR f j)
    (fun h => endPoissonModeJet_ae s R h (f.val 0 h) j)
  have ht : ∀ᵐ t∂FiniteAxisMeasure R,0<t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht using ht.1
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae ht] with z hz
  exact endPoissonField_hasSum s hs f j hz

end

open Set MeasureTheory Filter Topology UnitAddTorus
open scoped NNReal ENNReal

lemma continuous_endPoissonModeField (s : Fin 3 → ℝ) (h : TorusModes)
    (a : ℂ) (j : Fin 4) : Continuous (endPoissonModeField s h a j) := by
  unfold endPoissonModeField
  fun_prop

lemma measurable_endPoissonField (s : Fin 3 → ℝ)
    (f : spectralTraceGraph (torusRate s)) (j : Fin 4) : Measurable (endPoissonField s f j) := by
  exact Measurable.tsum (fun h => (continuous_endPoissonModeField s h (f.val 0 h) j).measurable)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_TorusPoissonContinuous
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity

section
open MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal

attribute [local instance] OAI.ScalarConductivity.torusPoissonContinuousMeasureSpace
attribute [local instance] OAI.ScalarConductivity.torusPoissonContinuousProbabilityMeasure
theorem torusPoissonContinuous_toLp {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ, (1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {t : ℝ} (ht : 0<t) (f : TorusL2) :
    (torusPoissonContinuous s t f).toLp 2 volume ℂ=torusPoissonFlow s t f := by
  have hsum := (poisson_series_norm_summable hs ht f).of_norm.hasSum
  have hm := (ContinuousMap.toLp 2 volume ℂ).hasSum hsum
  have he := hasSum_mFourier_series_L2 (torusPoissonFlow s t f)
  simp only [torusPoissonFlow_coeff,abs_of_pos ht] at he
  apply hm.unique
  convert! he using 1
  all_goals try with_reducible_and_instances rfl

lemma torusPoissonContinuous_apply {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ, (1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {t : ℝ} (ht : 0<t) (f : TorusL2) (x : UnitAddTorus (Fin 2)) :
    torusPoissonContinuous s t f x=
      ∑' h, (Real.exp (-torusRate s h*t):ℂ)*mFourierCoeff f h*mFourier h x := by
  exact ((ContinuousMap.evalCLM ℂ x).hasSum
    (poisson_series_norm_summable hs ht f).of_norm.hasSum).tsum_eq.symm

end

open MeasureTheory Filter Topology UnitAddTorus Real Set
open scoped ENNReal

local instance torusAnglesMeasureSpace_r070ee7_1 : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
lemma torusRealContinuation_eq {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ, (1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (f : TorusL2) {x : Fin 3 → ℝ} (hx : 0<x 0) :
    torusRealContinuation s f x=
      flatFourier s (fun h => (mFourierCoeff f h).re) (fun _ => 0) x+
      flatFourier s (fun h => (mFourierCoeff f h).im) (fun _ => Real.pi/2) x := by
  have hre (h) : |(mFourierCoeff f h).re|≤‖f‖ :=
    (Complex.abs_re_le_norm _).trans (torusFourierCoeff_bound f h)
  have him (h) : |(mFourierCoeff f h).im|≤‖f‖ :=
    (Complex.abs_im_le_norm _).trans (torusFourierCoeff_bound f h)
  have hc := (ContinuousMap.evalCLM ℂ (torusAngles x)).hasSum
    (poisson_series_norm_summable hs hx f).of_norm.hasSum
  have hr := Complex.reCLM.hasSum hc
  change HasSum (fun h => ((exp (-torusRate s h*x 0):ℂ)*mFourierCoeff f h*mFourier h (torusAngles x)).re)
    (torusRealContinuation s f x) at hr
  rw [←hr.tsum_eq]
  unfold flatFourier
  rw [←(flatFourier_summable hs hre hx).tsum_add (flatFourier_summable hs him hx)]
  apply tsum_congr
  intro h
  rw [mFourier_torusAngles,complex_mode_real]
  simp only [flatPhaseMode,add_zero]

lemma torusRealContinuation_smooth {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ, (1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (f : TorusL2) :
    ContDiffOn ℝ (↑(⊤:ℕ∞)) (torusRealContinuation s f) {x | 0<x 0} := by
  have hre (h) : |(mFourierCoeff f h).re|≤‖f‖ :=
    (Complex.abs_re_le_norm _).trans (torusFourierCoeff_bound f h)
  have him (h) : |(mFourierCoeff f h).im|≤‖f‖ :=
    (Complex.abs_im_le_norm _).trans (torusFourierCoeff_bound f h)
  exact ((flatFourier_smooth hs hre).add (flatFourier_smooth hs him)).congr
    (fun x hx => torusRealContinuation_eq hs f hx)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_EndPoissonDifferential
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace _root_.OAI.ScalarConductivity.spectralTraceGraph_realInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus

lemma endFlatMode_eq (s : Fin 3 → ℝ) (h : TorusModes) (a : ℂ) (x : Fin 3 → ℝ) :
    endFlatMode s h a x=endPoissonModeField s h a 0 (x 0,torusAngles x) := by
  rw [endFlatMode,endFrequency_apply,Complex.exp_add,←Complex.ofReal_exp]
  rw [endPoissonModeField,mFourier_torusAngles]
  change a*((Real.exp (-(torusRate s h*x 0)):ℂ)*_) =
    (Real.exp (-torusRate s h*x 0):ℂ)*a*_
  rw [neg_mul]
  ring

lemma endFlatPoisson_eq (s : Fin 3 → ℝ) (f : spectralTraceGraph (torusRate s))
    (x : Fin 3 → ℝ) :
    endFlatPoisson s f x=endPoissonField s f 0 (x 0,torusAngles x) := by
  exact tsum_congr (fun h => endFlatMode_eq s h (f.val 0 h) x)

theorem endFlatPoisson_hasFDeriv (s : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (f : spectralTraceGraph (torusRate s)) {x : Fin 3 → ℝ} (hx : 0<x 0) :
    HasFDerivAt (endFlatPoisson s f)
      (∑' h,endFlatMode s h (f.val 0 h) x • endFrequency s h) x := by
  have hu : Summable (fun h => ‖f.val 0‖*((torusRate s h+torusSize h)*
      Real.exp (-(x 0/2)*torusRate s h))) := by
    simpa only [pow_one] using
      (flatMode_derivative_summable hs 1 (show 0<x 0/2 by linarith)).mul_left ‖f.val 0‖
  exact hasFDerivAt_tsum_of_isPreconnected hu (axial_halfspace_open (x 0/2))
    (axial_halfspace_connected (x 0/2))
    (fun h y _ => endFlatMode_hasFDeriv s h (f.val 0 h) y)
    (fun h y hy => endFlatMode_derivative_bound s h
      (lp.norm_apply_le_norm (by norm_num) (f.val 0) h) hy.le)
    (show x 0/2<x 0 by linarith)
    (by simpa only [endFlatMode_eq] using (endPoissonField_hasSum s hs f 0 (z:=(x 0,torusAngles x)) hx).summable)
    (show x 0/2<x 0 by linarith)

lemma endFlatMode_axis (s : Fin 3 → ℝ) (h : TorusModes) (a : ℂ)
    (x : Fin 3 → ℝ) (j : Fin 3) :
    (endFlatMode s h a x • endFrequency s h) (Pi.single j 1)=
      endPoissonModeField s h a j.succ (x 0,torusAngles x) := by
  rw [smul_apply,smul_eq_mul,endFlatMode_eq]
  fin_cases j <;> simp [endFrequency,endPoissonModeField,endModeCoefficient] <;> ring

lemma endFlatPoisson_derivative_axis (s : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (f : spectralTraceGraph (torusRate s)) {x : Fin 3 → ℝ} (hx : 0<x 0) (j : Fin 3) :
    fderiv ℝ (endFlatPoisson s f) x (Pi.single j 1)=
      endPoissonField s f j.succ (x 0,torusAngles x) := by
  calc
    _ = (∑' h,endFlatMode s h (f.val 0 h) x • endFrequency s h) (Pi.single j 1) :=
      congrArg (fun L : (Fin 3 → ℝ) →L[ℝ] ℂ => L (Pi.single j 1))
        (endFlatPoisson_hasFDeriv s hs f hx).fderiv
    _ = ∑' h,(endFlatMode s h (f.val 0 h) x • endFrequency s h) (Pi.single j 1) :=
      (ContinuousLinearMap.apply ℝ ℂ (Pi.single j 1)).map_tsum
        (endFlatPoisson_derivative_summable s hs f hx)
    _ = _ := tsum_congr (fun h => endFlatMode_axis s h (f.val 0 h) x j)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_CollarCartesianDifferential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus Matrix
open scoped Matrix.Norms.Elementwise

lemma sourceCartesianGradient_chain (i j : Fin 4) {x : Fin 3 → ℝ}
    (hx : x∈sourceExtendedBox (-(1:ℝ)/100) (1/100)) (v : Fin 3 → ℝ) :
    (sourceCollarJacobian i j x)ᵀ *ᵥ (sourceCartesianGradientMatrix i j x *ᵥ v)=
      sourceFaceAngleMatrix i j x *ᵥ v := by
  rw [sourceCartesianGradientMatrix,←Matrix.mulVec_mulVec,Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (by
      rw [Matrix.det_transpose]
      exact sourceCollarJacobian_extended_ne_zero i j hx)),Matrix.one_mulVec]

lemma sourceCartesianGradient_uniform_bound : ∃ C : ℝ,0<C ∧
    ∀ (i j : Fin 4) (x : Fin 3 → ℝ),x∈sourceExtendedBox (-(1:ℝ)/100) (1/100) →
      ∀ a b : Fin 3,|sourceCartesianGradientMatrix i j x a b|≤C := by
  have hb (i j : Fin 4) : ∃ C : ℝ,∀ x∈sourceExtendedBox (-(1:ℝ)/100) (1/100),
      ‖sourceCartesianGradientMatrix i j x‖≤C :=
    (isCompact_Icc : IsCompact (sourceExtendedBox (-(1:ℝ)/100) (1/100))).exists_bound_of_continuousOn
      (continuousOn_sourceCartesianGradientMatrix i j)
  choose C hC using hb
  refine ⟨1+∑ i : Fin 4,∑ j : Fin 4,|C i j|,by positivity,?_⟩
  intro i j x hx a b
  have hentry : |sourceCartesianGradientMatrix i j x a b|≤C i j := by
    simpa only [Real.norm_eq_abs] using
      (norm_le_pi_norm (sourceCartesianGradientMatrix i j x a) b).trans
        ((norm_le_pi_norm (sourceCartesianGradientMatrix i j x) a).trans (hC i j x hx))
  have hsum : |C i j|≤∑ i : Fin 4,∑ j : Fin 4,|C i j| :=
    (Finset.single_le_sum (fun k _ => abs_nonneg (C i k)) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (fun k _ => Finset.sum_nonneg (fun l _ => abs_nonneg (C k l)))
        (Finset.mem_univ i))
  linarith [le_abs_self (C i j)]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_CollarLocalInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix

def sourceCollarTangentEquiv (i j : Fin 4) (x : Fin 3 → ℝ)
    (hx : x∈sourceExtendedBox (-(1:ℝ)/100) (1/100)) :
    (Fin 3 → ℝ) ≃L[ℝ] (Fin 3 → ℝ) :=
  (LinearMap.equivOfDetNeZero (Matrix.toLin' (sourceCollarJacobian i j x))
    (by rw [LinearMap.det_toLin']; exact sourceCollarJacobian_extended_ne_zero i j hx)).toContinuousLinearEquiv

lemma sourceCollarPiece_hasStrictFDeriv (i j : Fin 4) (x : Fin 3 → ℝ)
    (hx : x∈sourceExtendedBox (-(1:ℝ)/100) (1/100)) :
    HasStrictFDerivAt (sourceCollarPiece i j) (sourceCollarTangentEquiv i j x hx).toContinuousLinearMap
      x := by
  have hf := (sourceCollarPiece_contDiff i j).hasStrictFDerivAt (x:=x) (by simp)
  rw [(sourceCollarPiece_hasFDeriv i j x).fderiv] at hf
  exact hf

lemma sourceCollarInverse_eventually_left (i j : Fin 4) {x : Fin 3 → ℝ}
    (hx : x∈sourceCollarOpenBox) :
    ∀ᶠ y in 𝓝 x,sourceCollarInverse i j (sourceCollarPiece i j y)=y := by
  filter_upwards [isOpen_sourceCollarOpenBox.mem_nhds hx] with y hy
  exact sourceCollarInverse_left_pos i j
    (lt_of_lt_of_le (by norm_num : (0:ℝ)<1/50)
      (sourceCollarRadius_extended j ⟨hy.1.1.le,hy.1.2.le⟩ hy.2.2.le).1)
    (by linarith [hy.1.2]) hy.2.1.le hy.2.2.le

lemma sourceCollarInverse_hasStrictFDeriv (i j : Fin 4) {x : Fin 3 → ℝ}
    (hx : x∈sourceCollarOpenBox) :
    HasStrictFDerivAt (sourceCollarInverse i j)
      (sourceCollarTangentEquiv i j x (sourceCollarOpenBox_subset hx)).symm.toContinuousLinearMap
      (sourceCollarPiece i j x) :=
  (sourceCollarPiece_hasStrictFDeriv i j x (sourceCollarOpenBox_subset hx)).to_local_left_inverse
    (sourceCollarInverse_eventually_left i j hx)

lemma sourceCollarPiece_map_nhds (i j : Fin 4) {x : Fin 3 → ℝ}
    (hx : x∈sourceCollarOpenBox) :
    Filter.map (sourceCollarPiece i j) (𝓝 x)=𝓝 (sourceCollarPiece i j x) :=
  (sourceCollarPiece_hasStrictFDeriv i j x (sourceCollarOpenBox_subset hx)).map_nhds_eq_of_equiv

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_PhysicalEndDifferential
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace _root_.OAI.ScalarConductivity.spectralTraceGraph_realInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus Matrix

lemma sourceCollarInverse_point (i j : Fin 4) {x : Fin 3 → ℝ}
    (hx : x∈sourceCollarOpenBox) : sourceCollarInverse i j (sourceCollarPiece i j x)=x :=
  (sourceCollarInverse_eventually_left i j hx).self_of_nhds

lemma endFlatPoisson_realCLM_apply (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    (f : spectralTraceGraph (torusRate s)) {x : Fin 3 → ℝ} (hx : 0<x 0) (v : Fin 3 → ℝ) :
    (fderiv ℝ (endFlatPoisson s f) x v).re=
      (fun k : Fin 3 => (endPoissonField s f k.succ (x 0,torusAngles x)).re) ⬝ᵥ v := by
  change (Complex.reCLM.comp (fderiv ℝ (endFlatPoisson s f) x)) v=_
  rw [realCLM_apply_basis]
  apply congrArg (fun g : Fin 3 → ℝ => g ⬝ᵥ v)
  funext k
  exact congrArg Complex.re (endFlatPoisson_derivative_axis s hs f hx k)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_AttachedEndPoisson
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace _root_.OAI.ScalarConductivity.spectralTraceGraph_realInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus Matrix

def attachedEndPoissonField (s : Fin 3 → ℝ) (f : spectralTraceGraph (torusRate s))
    (a b : ℝ) (j : Fin 4) (y : Fin 3 → ℝ) : ℂ :=
  endPoissonField s f j (a*(sourceCollarTime y-b),sourcePhysicalAngles y)

lemma measurable_attachedEndPoissonField (s : Fin 3 → ℝ)
    (f : spectralTraceGraph (torusRate s)) (a b : ℝ) (j : Fin 4) :
    Measurable (attachedEndPoissonField s f a b j) := by
  apply (measurable_endPoissonField s f j).comp
  exact (measurable_const.mul (measurable_sourcePhysicalCoordinates.fst.sub measurable_const)).prodMk
    measurable_sourcePhysicalAngles

lemma attachedEndPoissonField_angular (s : Fin 3 → ℝ)
    (f : spectralTraceGraph (torusRate s)) (a b : ℝ) (j : Fin 4)
    {t : ℝ} (ht : t∈Icc (-(1:ℝ)/100) (1/100)) (θ : UnitAddTorus (Fin 2)) :
    attachedEndPoissonField s f a b j (sourceAngularCollar t θ)=
      endPoissonField s f j (a*(t-b),θ) := by
  simp only [attachedEndPoissonField,sourceAngular_time ht,sourcePhysicalAngles_angular ht]

lemma attachedEndPoissonField_piece (s : Fin 3 → ℝ)
    (f : spectralTraceGraph (torusRate s)) (a b : ℝ) (i j : Fin 4) {x : Fin 3 → ℝ}
    (hx : x∈sourceExtendedBox (-(1:ℝ)/100) (1/100)) :
    attachedEndPoissonField s f a b 0 (sourceCollarPiece i j x)=
      endFlatPoisson s f (endAxialAffine a b (sourceFaceAngles i j x)) := by
  obtain ⟨ht,ha,hb⟩ := mem_sourceExtendedBox.mp hx
  rw [←sourceFaceAngles_physical i j ha hb,attachedEndPoissonField_angular s f a b 0 ht,
    endFlatPoisson_eq,torusAngles_endAxialAffine]
  rfl

lemma attachedEndPoissonField_local_eq (s : Fin 3 → ℝ)
    (f : spectralTraceGraph (torusRate s)) (a b : ℝ) (i j : Fin 4) {x : Fin 3 → ℝ}
    (hx : x∈sourceCollarOpenBox) :
    attachedEndPoissonField s f a b 0 =ᶠ[𝓝 (sourceCollarPiece i j x)]
      (fun y => endFlatPoisson s f (endAxialAffine a b (sourceFaceAngles i j (sourceCollarInverse i j y)))) := by
  change ∀ᶠ y in 𝓝 (sourceCollarPiece i j x),attachedEndPoissonField s f a b 0 y=
    endFlatPoisson s f (endAxialAffine a b (sourceFaceAngles i j (sourceCollarInverse i j y)))
  rw [←sourceCollarPiece_map_nhds i j hx,Filter.eventually_map]
  filter_upwards [isOpen_sourceCollarOpenBox.mem_nhds hx,
    sourceCollarInverse_eventually_left i j hx] with y hy hi
  rw [hi]
  exact attachedEndPoissonField_piece s f a b i j (sourceCollarOpenBox_subset hy)

theorem attachedEndPoissonField_hasFDeriv (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    (f : spectralTraceGraph (torusRate s)) (a b : ℝ) (i j : Fin 4) {x : Fin 3 → ℝ}
    (hx : x∈sourceCollarOpenBox) (ht : 0<a*(x 0-b)) :
    HasFDerivAt (attachedEndPoissonField s f a b 0)
      ((fderiv ℝ (endFlatPoisson s f) (endAxialAffine a b (sourceFaceAngles i j x))).comp
        (((Matrix.toLin' (endAxialMatrix a)).toContinuousLinearMap).comp
          (((Matrix.toLin' (sourceFaceAngleMatrix i j x)).toContinuousLinearMap).comp
            (sourceCollarTangentEquiv i j x (sourceCollarOpenBox_subset hx)).symm.toContinuousLinearMap)))
      (sourceCollarPiece i j x) := by
  have he := sourceCollarInverse_point i j hx
  have h1 := (sourceCollarInverse_hasStrictFDeriv i j hx).hasFDerivAt
  have h2 := (sourceFaceAngles_hasFDeriv i j (sourceCollarInverse i j (sourceCollarPiece i j x))).comp
    (sourceCollarPiece i j x) h1
  rw [he] at h2
  have h3a : HasFDerivAt (endAxialAffine a b)
      (Matrix.toLin' (endAxialMatrix a)).toContinuousLinearMap
      (sourceFaceAngles i j (sourceCollarInverse i j (sourceCollarPiece i j x))) := by
    simpa only [he] using endAxialAffine_hasFDeriv a b (sourceFaceAngles i j x)
  have h3 := h3a.comp (sourceCollarPiece i j x) h2
  have hd := (endFlatPoisson_hasFDeriv s hs f (x:=endAxialAffine a b (sourceFaceAngles i j x)) ht).differentiableAt.hasFDerivAt
  have hda : HasFDerivAt (endFlatPoisson s f)
      (fderiv ℝ (endFlatPoisson s f) (endAxialAffine a b (sourceFaceAngles i j x)))
      (endAxialAffine a b (sourceFaceAngles i j (sourceCollarInverse i j (sourceCollarPiece i j x)))) := by
    simpa only [he] using hd
  have h3' := hda.comp (sourceCollarPiece i j x) h3
  exact h3'.congr_of_eventuallyEq (attachedEndPoissonField_local_eq s f a b i j hx)

lemma attachedEndPoissonField_eq_continuation (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    (f : spectralTraceGraph (torusRate s)) (a b : ℝ) {y : Fin 3 → ℝ}
    (hy : 0<a*(sourceCollarTime y-b)) {x : Fin 3 → ℝ}
    (hx : x 0=a*(sourceCollarTime y-b)) (hθ : torusAngles x=sourcePhysicalAngles y) :
    (attachedEndPoissonField s f a b 0 y).re=
      torusRealContinuation s ((mFourierBasis (d:=Fin 2)).repr.symm (f.val 0)) x := by
  unfold torusRealContinuation
  rw [hx,hθ,torusPoissonContinuous_apply hs hy]
  unfold attachedEndPoissonField endPoissonField
  apply congrArg Complex.re
  apply tsum_congr
  intro h
  have hc : mFourierCoeff (((mFourierBasis (d:=Fin 2)).repr.symm (f.val 0)):TorusL2) h=f.val 0 h := by
    rw [←mFourierBasis_repr,LinearIsometryEquiv.apply_symm_apply]
  simp only [endPoissonModeField,endModeCoefficient,hc,Matrix.cons_val_zero]

theorem attachedEndPoissonField_localLip (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    (f : spectralTraceGraph (torusRate s)) (a b : ℝ) {x : Fin 3 → ℝ}
    (ht : 0<a*(sourceCollarTime x-b)) (hx : ∀ i,sourceComplexDirections x i≠0) :
    LocalLipAt (fun y => (attachedEndPoissonField s f a b 0 y).re) x := by
  have hflat := (localLipAt_of_contDiffAt ((endAxialAffine_contDiff a b).of_le
    (show (1:WithTop ℕ∞)≤↑(⊤:ℕ∞) by simp)).contDiffAt).comp (sourceLocalFlat_localLip hx)
  have hc := (torusRealContinuation_smooth hs ((mFourierBasis (d:=Fin 2)).repr.symm (f.val 0))).of_le
    (show (1:WithTop ℕ∞)≤↑(⊤:ℕ∞) by simp)
  have hc' := hc.contDiffAt ((axial_halfspace_open 0).mem_nhds
    (show 0<(endAxialAffine a b (sourceLocalFlat x x)) 0 from ht))
  apply ((localLipAt_of_contDiffAt hc').comp (f:=endAxialAffine a b ∘ sourceLocalFlat x) hflat).congr
  have htime : ∀ᶠ y in 𝓝 x,0<a*(sourceCollarTime y-b) :=
    (continuous_const.mul (locallyLipschitz_sourceCollarTime.continuous.sub continuous_const)).continuousAt
      (Ioi_mem_nhds ht)
  have hdirs : ∀ᶠ y in 𝓝 x,∀ i,sourceComplexDirections y i≠0 := by
    rw [eventually_all]
    intro i
    exact (locallyLipschitz_sourceDirection i).continuous.continuousAt (isOpen_ne.mem_nhds (hx i))
  filter_upwards [htime,hdirs] with y hyt hyd
  exact (attachedEndPoissonField_eq_continuation s hs f a b hyt rfl
    ((torusAngles_endAxialAffine a b _).trans (sourceLocalFlat_angles hx hyd))).symm

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_AttachedEndL2
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace _root_.OAI.ScalarConductivity.spectralTraceGraph_realInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal

def attachedEndPoissonJet (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    (f : spectralTraceGraph (torusRate s)) {a b l r R : ℝ}
    (ha : a≠0) (hR : 0≤R) (hlr : l ≤ r) (hl : -(1:ℝ)/100≤l) (hr : r≤1/100)
    (hT : ∀ t∈Icc l r,affineEndTime a b t∈Icc 0 R) (j : Fin 4) :
    Lp ℂ 2 (sourcePhysicalCollarMeasure l r) :=
  sourceCollarPullback hlr hl hr (affineEndPullback ha hT (endPoissonJet s hs R hR f j))

lemma attachedEndPoissonJet_ae (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    (f : spectralTraceGraph (torusRate s)) {a b l r R : ℝ}
    (ha : a≠0) (hR : 0≤R) (hlr : l ≤ r) (hl : -(1:ℝ)/100≤l) (hr : r≤1/100)
    (hT : ∀ t∈Icc l r,affineEndTime a b t∈Icc 0 R) (j : Fin 4) :
    attachedEndPoissonJet s hs f ha hR hlr hl hr hT j=ᵐ[sourcePhysicalCollarMeasure l r]
      attachedEndPoissonField s f a b j := by
  have he : affineEndPullback ha hT (endPoissonJet s hs R hR f j)=ᵐ[sourceCylinderMeasure l r]
      endPoissonField s f j ∘ affineEndCoordinates a b :=
    affineEndPullback_ae_of_ae ha hT _ (endPoissonJet_ae s hs R hR f j)
  have hp := sourceCollarPullback_ae_of_ae hlr hl hr _ he
  change sourceCollarPullback hlr hl hr (affineEndPullback ha hT (endPoissonJet s hs R hR f j))=ᵐ[sourcePhysicalCollarMeasure l r] _
  exact hp

lemma attachedEndPoissonField_memLp (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    (f : spectralTraceGraph (torusRate s)) {a b l r R : ℝ}
    (ha : a≠0) (hR : 0≤R) (hlr : l ≤ r) (hl : -(1:ℝ)/100≤l) (hr : r≤1/100)
    (hT : ∀ t∈Icc l r,affineEndTime a b t∈Icc 0 R) (j : Fin 4) :
    MemLp (attachedEndPoissonField s f a b j) 2
      (volume.restrict (sourceClosedCollarBand l r)) :=
  sourceClosedCollarBand_memLp hl hr
    ((memLp_congr_ae (attachedEndPoissonJet_ae s hs f ha hR hlr hl hr hT j)).mp
      (Lp.memLp (attachedEndPoissonJet s hs f ha hR hlr hl hr hT j)))

lemma attachedEndPoissonField_angular_memLp (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    (f : spectralTraceGraph (torusRate s)) {a b l r R : ℝ}
    (ha : a≠0) (hR : 0≤R) (hl : -(1:ℝ)/100≤l) (hr : r≤1/100)
    (hT : ∀ t∈Icc l r,affineEndTime a b t∈Icc 0 R) (j : Fin 4) :
    MemLp (fun z : ℝ×UnitAddTorus (Fin 2) => attachedEndPoissonField s f a b j
      (sourceAngularCollar z.1 z.2)) 2 ((volume.restrict (Ioc l r)).prod volume) := by
  rw [←sourceCylinderMeasure_eq]
  have h : MemLp (endPoissonField s f j ∘ affineEndCoordinates a b) 2 (sourceCylinderMeasure l r) :=
    (memLp_congr_ae (affineEndPullback_ae_of_ae ha hT _
    (endPoissonJet_ae s hs R hR f j))).mp (Lp.memLp (affineEndPullback ha hT
      (endPoissonJet s hs R hR f j)))
  apply (memLp_congr_ae _).mp h
  have ht : ∀ᵐ z∂sourceCylinderMeasure l r,z.1∈Ioc l r :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioc)
  filter_upwards [ht] with z hz
  exact (attachedEndPoissonField_angular s f a b j ⟨hl.trans hz.1.le,hz.2.trans hr⟩ z.2).symm

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_PoissonTraceRate
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace _root_.OAI.ScalarConductivity.spectralTraceGraph_realInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity

open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal

attribute [local instance] OAI.ScalarConductivity.instMeasureSpaceUnitAddCircle_solutions_8
attribute [local instance] OAI.ScalarConductivity.instIsProbabilityMeasureUnitAddCircleVolume_solutions_8
lemma torusPoissonContinuous_trace_sq {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {t : ℝ} (ht : 0<t) (f : C(UnitAddTorus (Fin 2),ℂ))
    (g : SpectralL2 TorusModes)
    (hg : ∀ h,g h=(torusRate s h:ℂ)*mFourierCoeff (f.toLp 2 volume ℂ) h) :
    (∫ θ,‖torusPoissonContinuous s t (f.toLp 2 volume ℂ) θ-f θ‖^2)≤t^2*‖g‖^2 := by
  change (∫ θ,‖(torusPoissonContinuous s t (f.toLp 2 volume ℂ)-f) θ‖^2)≤_
  rw [continuousMap_L2_sq,map_sub,torusPoissonContinuous_toLp hs ht]
  have hh := torusPoissonFlow_trace_rate s ht.le (f.toLp 2 volume ℂ) g hg
  nlinarith [norm_nonneg (torusPoissonFlow s t (f.toLp 2 volume ℂ)-f.toLp 2 volume ℂ),
    mul_nonneg ht.le (norm_nonneg g)]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_SmoothCollarRate
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace _root_.OAI.ScalarConductivity.spectralTraceGraph_realInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal NNReal

lemma sourceAngular_time_displacement (t b : ℝ) (θ : UnitAddTorus (Fin 2)) :
    ‖sourceAngularCollar t θ-sourceAngularCollar b θ‖≤8*|t-b| := by
  rw [show sourceAngularCollar t θ=sourceAngularCollar b θ+(t-b) • sourceAngularVelocity θ by
    simpa only [add_sub_cancel] using sourceAngular_affine b (t-b) θ,add_sub_cancel_left,norm_smul,
    Real.norm_eq_abs]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left (sourceAngularVelocity_norm θ) (abs_nonneg (t-b))

lemma smooth_sourceCollar_value_displacement {q : (Fin 3 → ℝ) → ℝ} {K : ℝ≥0}
    (hK : LipschitzOnWith K q (sourceClosedCollarBand (-(1:ℝ)/100) (1/100)))
    {t b : ℝ} (ht : t∈Icc (-(1:ℝ)/100) (1/100)) (hb : b∈Icc (-(1:ℝ)/100) (1/100))
    (θ : UnitAddTorus (Fin 2)) :
    |q (sourceAngularCollar t θ)-q (sourceAngularCollar b θ)|≤8*(K:ℝ)*|t-b| := by
  have ht' : sourceAngularCollar t θ∈sourceClosedCollarBand (-(1:ℝ)/100) (1/100) := by
    change sourceCollarTime (sourceAngularCollar t θ)∈Icc (-(1:ℝ)/100) (1/100)
    rw [sourceAngular_time ht]; exact ht
  have hb' : sourceAngularCollar b θ∈sourceClosedCollarBand (-(1:ℝ)/100) (1/100) := by
    change sourceCollarTime (sourceAngularCollar b θ)∈Icc (-(1:ℝ)/100) (1/100)
    rw [sourceAngular_time hb]; exact hb
  have H := (hK.dist_le_mul _ ht' _ hb').trans
    (mul_le_mul_of_nonneg_left (sourceAngular_time_displacement t b θ) K.coe_nonneg)
  simpa only [Real.dist_eq,dist_eq_norm,Real.norm_eq_abs,mul_assoc,mul_left_comm] using H

attribute [local instance] OAI.ScalarConductivity.smoothCollarRateMeasureSpace
attribute [local instance] OAI.ScalarConductivity.smoothCollarRateProbabilityMeasure
lemma endPoissonField_eq_traceFlow {s : Fin 3 → ℝ}
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    (f : spectralTraceGraph (torusRate s)) (q : C(UnitAddTorus (Fin 2),ℂ))
    (hq : ∀ h,f.val 0 h=mFourierCoeff q h) {t : ℝ} (ht : 0<t) (θ : UnitAddTorus (Fin 2)) :
    endPoissonField s f 0 (t,θ)=torusPoissonContinuous s t (q.toLp 2 volume ℂ) θ := by
  rw [torusPoissonContinuous_apply hs ht]
  unfold endPoissonField
  apply tsum_congr
  intro h
  simp only [endPoissonModeField,endModeCoefficient,Matrix.cons_val_zero,hq,mFourierCoeff_toLp]

lemma smooth_attachedEnd_fiber_rate {s : Fin 3 → ℝ}
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    (f : spectralTraceGraph (torusRate s)) {q : (Fin 3 → ℝ) → ℝ}
    (hq : ContDiff ℝ (↑(⊤:ℕ∞)) q) {K : ℝ≥0}
    (hK : LipschitzOnWith K q (sourceClosedCollarBand (-(1:ℝ)/100) (1/100)))
    {a b t : ℝ} (hb : b∈Icc (-(1:ℝ)/100) (1/100)) (ht : t∈Icc (-(1:ℝ)/100) (1/100))
    (hpos : 0<a*(t-b)) (htrace : ∀ h,f.val 0 h=mFourierCoeff
      (fun θ => (q (sourceAngularCollar b θ):ℂ)) h)
    (g : SpectralL2 TorusModes) (hg : ∀ h,g h=(torusRate s h:ℂ)*f.val 0 h) :
    (∫ θ,((attachedEndPoissonField s f a b 0 (sourceAngularCollar t θ)).re-
      q (sourceAngularCollar t θ))^2)≤(2*a^2*‖g‖^2+2*(8*(K:ℝ))^2)*(t-b)^2 := by
  let Q : C(UnitAddTorus (Fin 2),ℂ) := ⟨fun θ => (q (sourceAngularCollar b θ):ℂ),
    Complex.continuous_ofReal.comp (hq.continuous.comp (continuous_sourceAngularCollar b))⟩
  let P := torusPoissonContinuous s (a*(t-b)) (Q.toLp 2 volume ℂ)
  have he (θ : UnitAddTorus (Fin 2)) :
      attachedEndPoissonField s f a b 0 (sourceAngularCollar t θ)=P θ :=
    (attachedEndPoissonField_angular s f a b 0 ht θ).trans
      (endPoissonField_eq_traceFlow hs f Q htrace hpos θ)
  have hP : Continuous (fun θ => (P θ).re-q (sourceAngularCollar t θ)) :=
    (Complex.continuous_re.comp P.continuous).sub (hq.continuous.comp (continuous_sourceAngularCollar t))
  simp_rw [he]
  have hbound (θ : UnitAddTorus (Fin 2)) :
      ((P θ).re-q (sourceAngularCollar t θ))^2≤
      2*‖P θ-Q θ‖^2+2*(8*(K:ℝ)*|t-b|)^2 := by
    have hp := Complex.abs_re_le_norm (P θ-Q θ)
    have hq' := smooth_sourceCollar_value_displacement hK ht hb θ
    have hq'' : |q (sourceAngularCollar b θ)-q (sourceAngularCollar t θ)|≤8*(K:ℝ)*|t-b| := by
      rwa [abs_sub_comm] at hq'
    have h1 := pow_le_pow_left₀ (abs_nonneg _) hp 2
    have h2 := pow_le_pow_left₀ (abs_nonneg _) hq'' 2
    simp only [sq_abs,Complex.sub_re,Complex.ofReal_re,Q,ContinuousMap.coe_mk] at h1 h2
    dsimp only [Q,ContinuousMap.coe_mk]
    nlinarith [sq_nonneg ((P θ).re-q (sourceAngularCollar b θ)-
      (q (sourceAngularCollar b θ)-q (sourceAngularCollar t θ)))]
  have hpint : Integrable (fun θ => ‖P θ-Q θ‖^2) :=
    (((P.continuous.sub Q.continuous).norm).pow 2).integrable_of_hasCompactSupport (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (subset_univ _))
  have hfin : Integrable (fun θ => ((P θ).re-q (sourceAngularCollar t θ))^2) :=
    (hP.pow 2).integrable_of_hasCompactSupport (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (subset_univ _))
  have H := integral_mono hfin ((hpint.const_mul 2).add (integrable_const _)) hbound
  simp only [Pi.add_apply] at H
  rw [integral_add (hpint.const_mul 2) (integrable_const _),integral_const_mul,integral_const] at H
  have hrate : (∫ θ,‖P θ-Q θ‖^2)≤(a*(t-b))^2*‖g‖^2 :=
    torusPoissonContinuous_trace_sq hs hpos Q g (fun h => by rw [hg,mFourierCoeff_toLp,htrace]; rfl)
  simp only [probReal_univ,one_smul] at H
  calc
    _ ≤ 2*((a*(t-b))^2*‖g‖^2)+2*(8*(K:ℝ)*|t-b|)^2 := by linarith
    _ = _ := by rw [mul_pow,mul_pow,sq_abs]; ring

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_PhysicalStripIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal

lemma sourceClosedBand_sq_integral_le {u : (Fin 3 → ℝ) → ℝ}
    (hu : Measurable u) {l r M : ℝ} (hlr : l ≤ r)
    (hl : -(1:ℝ)/100≤l) (hr : r≤1/100)
    (hi : Integrable (fun z : ℝ×UnitAddTorus (Fin 2) => u (sourceAngularCollar z.1 z.2)^2)
      ((volume.restrict (Ioc l r)).prod volume))
    (hb : ∀ᵐ t∂volume.restrict (Ioc l r),(∫ θ,u (sourceAngularCollar t θ)^2)≤M) :
    (∫ y in sourceClosedCollarBand l r,u y^2)≤ sourceCollarVolumeConstant*(r-l)*M := by
  have he : Integrable (fun y => u y^2) (sourceAngularCollarMeasure l r) := by
    unfold sourceAngularCollarMeasure
    exact (integrable_map_measure (hu.pow_const 2).aestronglyMeasurable
      continuous_uncurry_sourceAngularCollar.aemeasurable).mpr hi
  have hc : Integrable (fun y => u y^2)
      (ENNReal.ofReal sourceCollarVolumeConstant • sourceAngularCollarMeasure l r) :=
    he.smul_measure ENNReal.ofReal_ne_top
  have hle : volume.restrict (sourceClosedCollarBand l r)≤
      ENNReal.ofReal sourceCollarVolumeConstant • sourceAngularCollarMeasure l r :=
    (sourceClosedCollarBand_measure_le hl hr).trans (sourcePhysicalCollarMeasure_le hlr hl hr)
  have H := integral_mono_measure hle (Eventually.of_forall (fun y => sq_nonneg (u y))) hc
  rw [integral_smul_measure,ENNReal.toReal_ofReal sourceCollarVolumeConstant_pos.le] at H
  have hmap : (∫ y,u y^2 ∂sourceAngularCollarMeasure l r)=
      ∫ t in Ioc l r,∫ θ,u (sourceAngularCollar t θ)^2 := by
    unfold sourceAngularCollarMeasure
    rw [integral_map continuous_uncurry_sourceAngularCollar.aemeasurable
      (hu.pow_const 2).aestronglyMeasurable]
    exact integral_prod _ hi
  rw [hmap] at H
  have hb' : (∫ t in Ioc l r,∫ θ,u (sourceAngularCollar t θ)^2)≤(r-l)*M := by
    have hh := integral_mono_ae hi.integral_prod_left (integrable_const M) hb
    simpa only [integral_const,Measure.real,Measure.restrict_apply_univ,Real.volume_Ioc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hlr),smul_eq_mul] using hh
  simpa only [smul_eq_mul,mul_assoc] using H.trans
    (mul_le_mul_of_nonneg_left hb' sourceCollarVolumeConstant_pos.le)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_AttachedEndLayer
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace _root_.OAI.ScalarConductivity.spectralTraceGraph_realInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal NNReal

lemma continuous_angular_memLp {q : (Fin 3 → ℝ) → ℝ} (hq : Continuous q)
    {l r : ℝ} (hl : -(1:ℝ)/100≤l) (hr : r≤1/100) :
    MemLp (fun z : ℝ×UnitAddTorus (Fin 2) => q (sourceAngularCollar z.1 z.2)) 2
      ((volume.restrict (Ioc l r)).prod volume) := by
  obtain ⟨M,hM⟩ := (isCompact_sourceClosedCollarBand (le_refl (-(1:ℝ)/100))
    (le_refl ((1:ℝ)/100))).exists_bound_of_continuousOn hq.continuousOn
  apply MemLp.of_bound (hq.comp continuous_uncurry_sourceAngularCollar).aestronglyMeasurable M
  have ht : ∀ᵐ z : ℝ×UnitAddTorus (Fin 2)∂(volume.restrict (Ioc l r)).prod volume,z.1∈Ioc l r :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioc)
  filter_upwards [ht] with z hz
  apply hM
  change sourceCollarTime (sourceAngularCollar z.1 z.2)∈Icc (-(1:ℝ)/100) (1/100)
  rw [sourceAngular_time ⟨hl.trans hz.1.le,hz.2.trans hr⟩]
  exact ⟨hl.trans hz.1.le,hz.2.trans hr⟩

lemma smooth_attachedEnd_fiber_rate_volume {s : Fin 3 → ℝ}
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    (f : spectralTraceGraph (torusRate s)) {q : (Fin 3 → ℝ) → ℝ}
    (hq : ContDiff ℝ (↑(⊤:ℕ∞)) q) {K : ℝ≥0}
    (hK : LipschitzOnWith K q (sourceClosedCollarBand (-(1:ℝ)/100) (1/100)))
    {a b t : ℝ} (hb : b∈Icc (-(1:ℝ)/100) (1/100)) (ht : t∈Icc (-(1:ℝ)/100) (1/100))
    (hpos : 0<a*(t-b)) (htrace : ∀ h,f.val 0 h=mFourierCoeff
      (fun θ => (q (sourceAngularCollar b θ):ℂ)) h)
    (g : SpectralL2 TorusModes) (hg : ∀ h,g h=(torusRate s h:ℂ)*f.val 0 h) :
    (∫ θ,((attachedEndPoissonField s f a b 0 (sourceAngularCollar t θ)).re-
      q (sourceAngularCollar t θ))^2)≤(2*a^2*‖g‖^2+2*(8*(K:ℝ))^2)*(t-b)^2 := by
  rw [unitTorus_volume_eq_normalized]
  exact smooth_attachedEnd_fiber_rate hs f hq hK hb ht hpos htrace g hg

lemma smooth_attachedEnd_band_rate {s : Fin 3 → ℝ}
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    (f : spectralTraceGraph (torusRate s)) {q : (Fin 3 → ℝ) → ℝ}
    (hq : ContDiff ℝ (↑(⊤:ℕ∞)) q) {K : ℝ≥0}
    (hK : LipschitzOnWith K q (sourceClosedCollarBand (-(1:ℝ)/100) (1/100)))
    {a b l r R d : ℝ} (ha : a≠0) (hR : 0≤R) (_ : 0≤d)
    (hb : b∈Icc (-(1:ℝ)/100) (1/100)) (hlr : l ≤ r)
    (hl : -(1:ℝ)/100≤l) (hr : r≤1/100)
    (hT : ∀ t∈Icc l r,affineEndTime a b t∈Icc 0 R)
    (hnear : ∀ t∈Icc l r,|t-b|≤d)
    (htrace : ∀ h,f.val 0 h=mFourierCoeff (fun θ => (q (sourceAngularCollar b θ):ℂ)) h)
    (g : SpectralL2 TorusModes) (hg : ∀ h,g h=(torusRate s h:ℂ)*f.val 0 h) :
    (∫ y in sourceClosedCollarBand l r,((attachedEndPoissonField s f a b 0 y).re-q y)^2)≤
      sourceCollarVolumeConstant*(r-l)*((2*a^2*‖g‖^2+2*(8*(K:ℝ))^2)*d^2) := by
  apply sourceClosedBand_sq_integral_le
    ((Complex.measurable_re.comp (measurable_attachedEndPoissonField s f a b 0)).sub hq.continuous.measurable)
    hlr hl hr
  · exact ((attachedEndPoissonField_angular_memLp s hs f ha hR hl hr hT 0).re.sub
      (continuous_angular_memLp hq.continuous hl hr)).integrable_sq
  have ht : ∀ᵐ t∂volume.restrict (Ioc l r),t≠b := by
    apply ae_restrict_of_ae
    rw [ae_iff]
    simpa only [not_not,Set.ofPred_eq_eq_singleton] using (measure_singleton b : volume ({b}:Set ℝ)=0)
  filter_upwards [ae_restrict_mem measurableSet_Ioc,ht] with t ht hne
  have htb : t-b≠0 := sub_ne_zero.mpr hne
  have hpos : 0<a*(t-b) := lt_of_le_of_ne (hT t ⟨ht.1.le,ht.2⟩).1 (Ne.symm (mul_ne_zero ha htb))
  apply (smooth_attachedEnd_fiber_rate_volume hs f hq hK hb ⟨hl.trans ht.1.le,ht.2.trans hr⟩
    hpos htrace g hg).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hnear t ⟨ht.1.le,ht.2⟩) 2

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_AttachedCutLayer
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace _root_.OAI.ScalarConductivity.spectralTraceGraph_realInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped NNReal

lemma smooth_attachedEnd_cut_layer_rate {s : Fin 3 → ℝ}
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    (f : spectralTraceGraph (torusRate s)) {q χ : (Fin 3 → ℝ) → ℝ}
    (hq : ContDiff ℝ (↑(⊤:ℕ∞)) q) (hχ : ∀ x,|χ x|≤1) {K : ℝ≥0}
    (hK : LipschitzOnWith K q (sourceClosedCollarBand (-(1:ℝ)/100) (1/100)))
    {a b η : ℝ} (ha : a≠0) (hη : 0<η) (hl : -(1:ℝ)/100≤b-η) (hr : b+η≤1/100)
    (htrace : ∀ h,f.val 0 h=mFourierCoeff (fun θ => (q (sourceAngularCollar b θ):ℂ)) h)
    (g : SpectralL2 TorusModes) (hg : ∀ h,g h=(torusRate s h:ℂ)*f.val 0 h)
    (hu : MemLp (cutMatchedValue (fun x => a*(sourceCollarTime x-b)) χ
      (fun x => (attachedEndPoissonField s f a b 0 x).re-q x)) 2 volume)
    {ε : ℝ} (hε : 0<ε) (hεη : ε≤|a| *η) :
    (∫ x in {x | 0<a*(sourceCollarTime x-b) ∧ a*(sourceCollarTime x-b)≤ε},
      (cutMatchedValue (fun x => a*(sourceCollarTime x-b)) χ
        (fun x => (attachedEndPoissonField s f a b 0 x).re-q x) x)^2)≤
      (sourceCollarVolumeConstant*(2*a^2*‖g‖^2+2*(8*(K:ℝ))^2)/|a|^3)*ε^3 := by
  let l := min b (b+ε/a)
  let r := max b (b+ε/a)
  obtain ⟨hlen,hleft,hright,hiff,hnear⟩ := affine_layer_interval (b:=b) ha hε.le
  have heη : ε/|a|≤η := (div_le_iff₀ (abs_pos.mpr ha)).mpr (by simpa [mul_comm] using hεη)
  have hl' : -(1:ℝ)/100≤l := hl.trans (by dsimp [l]; linarith)
  have hr' : r≤(1:ℝ)/100 := (by dsimp [r]; linarith : r≤b+η).trans hr
  have hb : b∈Icc (-(1:ℝ)/100) (1/100) := ⟨by linarith,by linarith⟩
  have hT : ∀ t∈Icc l r,affineEndTime a b t∈Icc 0 ε := fun t ht => (hiff t).mp ht
  have hp := ((attachedEndPoissonField_memLp s hs f ha hε.le (min_le_max) hl' hr' hT 0).re.sub
    (continuous_sourceBand_memLp hq.continuous hl' hr')).integrable_sq
  have hup := hu.integrable_sq
  calc
    _ ≤ ∫ x in sourceClosedCollarBand l r,
        (cutMatchedValue (fun x => a*(sourceCollarTime x-b)) χ
          (fun x => (attachedEndPoissonField s f a b 0 x).re-q x) x)^2 := by
      apply setIntegral_mono_set hup.integrableOn
        (Eventually.of_forall (fun x => sq_nonneg _))
      exact Eventually.of_forall (fun x hx => (hiff _).mpr ⟨hx.1.le,hx.2⟩)
    _ ≤ ∫ x in sourceClosedCollarBand l r,((attachedEndPoissonField s f a b 0 x).re-q x)^2 := by
      apply integral_mono_ae hup.integrableOn hp
      apply Eventually.of_forall
      intro x
      by_cases ht : 0<a*(sourceCollarTime x-b)
      · simp only [cutMatchedValue,ht,ite_eq_left,mul_pow]
        have hsq : (χ x)^2≤1 := by
          simpa only [sq_abs,one_pow] using (pow_le_pow_left₀ (abs_nonneg (χ x)) (hχ x) 2)
        simpa only [one_mul,Pi.sub_apply,RCLike.re_to_complex] using mul_le_mul_of_nonneg_right hsq
          (sq_nonneg ((attachedEndPoissonField s f a b 0 x).re-q x))
      · simp only [cutMatchedValue,ht,ite_false,zero_pow,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true]
        positivity
    _ ≤ sourceCollarVolumeConstant*(r-l)*((2*a^2*‖g‖^2+2*(8*(K:ℝ))^2)*(ε/|a|)^2) :=
      smooth_attachedEnd_band_rate hs f hq hK ha hε.le (by positivity) hb min_le_max hl' hr' hT hnear htrace g hg
    _ = _ := by
      change sourceCollarVolumeConstant*(max b (b+ε/a)-min b (b+ε/a))*_= _
      rw [hlen]
      ring

lemma smooth_attachedEnd_cut_thin {s : Fin 3 → ℝ}
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    (f : spectralTraceGraph (torusRate s)) {q χ : (Fin 3 → ℝ) → ℝ}
    (hq : ContDiff ℝ (↑(⊤:ℕ∞)) q) (hχ : ∀ x,|χ x|≤1)
    {a b η : ℝ} (ha : a≠0) (hη : 0<η) (hl : -(1:ℝ)/100≤b-η) (hr : b+η≤1/100)
    (htrace : ∀ h,f.val 0 h=mFourierCoeff (fun θ => (q (sourceAngularCollar b θ):ℂ)) h)
    (g : SpectralL2 TorusModes) (hg : ∀ h,g h=(torusRate s h:ℂ)*f.val 0 h)
    (hu : MemLp (cutMatchedValue (fun x => a*(sourceCollarTime x-b)) χ
      (fun x => (attachedEndPoissonField s f a b 0 x).re-q x)) 2 volume) :
    Tendsto (fun n : ℕ => ((n:ℝ)+1)^2*
      ∫ x in {x | 0<a*(sourceCollarTime x-b) ∧ ((n:ℝ)+1)*(a*(sourceCollarTime x-b))≤2},
      (cutMatchedValue (fun x => a*(sourceCollarTime x-b)) χ
        (fun x => (attachedEndPoissonField s f a b 0 x).re-q x) x)^2) atTop (𝓝 0) := by
  obtain ⟨K,hK⟩ := smooth_sourceCollar_lipschitz hq
  apply seamLayer_scaled_tendsto_of_cubic_pi (mul_pos (abs_pos.mpr ha) hη)
  intro ε hε hεη
  exact smooth_attachedEnd_cut_layer_rate hs f hq hχ hK ha hη hl hr htrace g hg hu hε hεη

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_CollarAE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma sourceCollar_frontier_null (i j : Fin 4) :
    volume (sourceCollarPiece i j '' frontier (sourceExtendedBox (-(1:ℝ)/100) (1/100)))=0 := by
  let B := sourceExtendedBox (-(1:ℝ)/100) (1/100)
  have hB : IsClosed B := isClosed_Icc
  have hs : frontier B⊆B := hB.frontier_subset
  have hzero : volume (frontier B)=0 := (convex_Icc _ _).addHaar_frontier volume
  have H := measure_image_le_det volume isClosed_frontier.measurableSet
    (fun x hx => (sourceCollarPiece_contDiff i j).differentiable (by simp) x)
    ((sourceExtendedBox_injOn i j (by rfl) (by rfl)).mono hs)
    (C:=2) (fun x hx => by
      rw [(sourceCollarPiece_hasFDeriv i j x).fderiv]
      exact sourceExtended_jacobian_upper i j (by rfl) (by rfl) (hs hx))
  have H' : volume (sourceCollarPiece i j '' frontier B) ≤ 0 := by
    simpa only [hzero,mul_zero] using H
  exact le_antisymm H' bot_le

lemma sourceCollar_open_charts_ae : ∀ᵐ y : Fin 3 → ℝ,
    y∈sourceClosedCollarBand (-(1:ℝ)/100) (1/100) →
      ∃ i j : Fin 4,∃ x∈sourceCollarOpenBox,sourceCollarPiece i j x=y := by
  let N := ⋃ i : Fin 4,⋃ j : Fin 4,sourceCollarPiece i j ''
    frontier (sourceExtendedBox (-(1:ℝ)/100) (1/100))
  have hN : volume N=0 := measure_iUnion_null (fun i =>
    measure_iUnion_null (fun j => sourceCollar_frontier_null i j))
  have hn : ∀ᵐ y : Fin 3 → ℝ,y∉N := by
    rw [ae_iff]
    simpa only [not_not,Set.ofPred_mem_eq] using hN
  filter_upwards [hn] with y hy ht
  rw [sourceClosedCollarBand_eq _ _ (by rfl) (by rfl)] at ht
  obtain ⟨i,hi⟩ := mem_iUnion.mp ht
  obtain ⟨j,x,hx,he⟩ := mem_iUnion.mp hi
  refine ⟨i,j,x,?_,he⟩
  rw [sourceCollarOpenBox_eq_interior]
  by_contra hn
  apply hy
  exact mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨j,⟨x,
    ⟨subset_closure hx,hn⟩,he⟩⟩⟩

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_AttachedEndDifferential
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace _root_.OAI.ScalarConductivity.spectralTraceGraph_realInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus Matrix

theorem attachedEndPoisson_real_fderiv (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    (f : spectralTraceGraph (torusRate s)) (a b : ℝ) (i j : Fin 4) {x : Fin 3 → ℝ}
    (hx : x∈sourceCollarOpenBox) (ht : 0<a*(x 0-b)) (v : Fin 3 → ℝ) :
    fderiv ℝ (fun y => (attachedEndPoissonField s f a b 0 y).re) (sourceCollarPiece i j x) v=
      (sourceCartesianGradientMatrix i j x *ᵥ (endAxialMatrix a *ᵥ
        (fun k : Fin 3 => (attachedEndPoissonField s f a b k.succ (sourceCollarPiece i j x)).re))) ⬝ᵥ v := by
  let E := sourceCollarTangentEquiv i j x (sourceCollarOpenBox_subset hx)
  let z := endAxialAffine a b (sourceFaceAngles i j x)
  let r : Fin 3 → ℝ := fun k => (endPoissonField s f k.succ (z 0,torusAngles z)).re
  let w := E.symm v
  have hw : sourceCollarJacobian i j x *ᵥ w=v := E.apply_symm_apply v
  have hd : (sourceFaceAngleMatrix i j x)ᵀ=sourceFaceAngleMatrix i j x := Matrix.diagonal_transpose _
  have ha : (endAxialMatrix a)ᵀ=endAxialMatrix a := Matrix.diagonal_transpose _
  have hp := Complex.reCLM.hasFDerivAt.comp (sourceCollarPiece i j x)
    (attachedEndPoissonField_hasFDeriv s hs f a b i j hx ht)
  have hr : r=fun k : Fin 3 => (attachedEndPoissonField s f a b k.succ (sourceCollarPiece i j x)).re := by
    funext k
    obtain ⟨htx,hi,hj⟩ := mem_sourceExtendedBox.mp (sourceCollarOpenBox_subset hx)
    dsimp only [r,z]
    rw [←sourceFaceAngles_physical i j hi hj,attachedEndPoissonField_angular s f a b k.succ htx,
      torusAngles_endAxialAffine]
    rfl
  calc
    _ = (fderiv ℝ (endFlatPoisson s f) z
        (endAxialMatrix a *ᵥ (sourceFaceAngleMatrix i j x *ᵥ w))).re :=
      congrArg (fun L : (Fin 3 → ℝ) →L[ℝ] ℝ => L v) hp.fderiv
    _ = r ⬝ᵥ (endAxialMatrix a *ᵥ (sourceFaceAngleMatrix i j x *ᵥ w)) :=
      endFlatPoisson_realCLM_apply s hs f (x:=z) ht _
    _ = (sourceFaceAngleMatrix i j x *ᵥ w) ⬝ᵥ (endAxialMatrix a *ᵥ r) := by
      simpa only [ha] using Matrix.dotProduct_transpose_mulVec (endAxialMatrix a) r (sourceFaceAngleMatrix i j x *ᵥ w)
    _ = w ⬝ᵥ (sourceFaceAngleMatrix i j x *ᵥ (endAxialMatrix a *ᵥ r)) := by
      rw [dotProduct_comm (sourceFaceAngleMatrix i j x *ᵥ w) (endAxialMatrix a *ᵥ r)]
      simpa only [hd] using Matrix.dotProduct_transpose_mulVec (sourceFaceAngleMatrix i j x) (endAxialMatrix a *ᵥ r) w
    _ = w ⬝ᵥ ((sourceCollarJacobian i j x)ᵀ *ᵥ
        (sourceCartesianGradientMatrix i j x *ᵥ (endAxialMatrix a *ᵥ r))) := by
      rw [sourceCartesianGradient_chain i j (sourceCollarOpenBox_subset hx)]
    _ = (sourceCartesianGradientMatrix i j x *ᵥ (endAxialMatrix a *ᵥ r)) ⬝ᵥ
        (sourceCollarJacobian i j x *ᵥ w) := Matrix.dotProduct_transpose_mulVec _ _ _
    _ = _ := by rw [hw,hr]

lemma attachedEndPoisson_real_differentiable_ae (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    (f : spectralTraceGraph (torusRate s)) (a b : ℝ) :
    ∀ᵐ y : Fin 3 → ℝ,y∈sourceClosedCollarBand (-(1:ℝ)/100) (1/100) →
      0<a*(sourceCollarTime y-b) → DifferentiableAt ℝ (fun y => (attachedEndPoissonField s f a b 0 y).re) y := by
  filter_upwards [sourceCollar_open_charts_ae] with y hy hb ht
  obtain ⟨i,j,x,hx,rfl⟩ := hy hb
  rw [sourceCollarPiece_time_open hx] at ht
  exact (Complex.reCLM.hasFDerivAt.comp _ (attachedEndPoissonField_hasFDeriv s hs f a b i j hx ht)).differentiableAt

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_AttachedEndGradientL2
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace _root_.OAI.ScalarConductivity.spectralTraceGraph_realInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus Matrix
open scoped ENNReal

lemma sourceCollarTime_level_null {b : ℝ} (hb : b∈Icc (-(1:ℝ)/100) (1/100)) :
    volume {y : Fin 3 → ℝ | sourceCollarTime y=b}=0 := by
  have hle := (sourceClosedCollarBand_measure_le hb.1 hb.2).trans
    (sourcePhysicalCollarMeasure_le (le_refl b) hb.1 hb.2)
  rw [sourceAngularCollarMeasure_self,smul_zero] at hle
  have he := Measure.le_iff.mp hle univ MeasurableSet.univ
  have hs : sourceClosedCollarBand b b={y : Fin 3 → ℝ | sourceCollarTime y=b} := by
    ext y; simp [sourceClosedCollarBand]
  simp only [Measure.restrict_apply_univ,Measure.coe_zero,Pi.zero_apply,hs] at he
  exact le_antisymm he bot_le

lemma sourceColevel_ae_ne {b : ℝ} (hb : b∈Icc (-(1:ℝ)/100) (1/100)) :
    ∀ᵐ y : Fin 3 → ℝ,sourceCollarTime y≠b := by
  rw [ae_iff]
  simpa only [not_not] using sourceCollarTime_level_null hb

lemma attachedEndPoisson_grad_bound (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    (f : spectralTraceGraph (torusRate s)) (a b : ℝ) :
    ∃ C : ℝ,0<C ∧ ∀ k : Fin 3,∀ᵐ y : Fin 3 → ℝ,
      y∈sourceClosedCollarBand (-(1:ℝ)/100) (1/100) → 0<a*(sourceCollarTime y-b) →
      |fderiv ℝ (fun y => (attachedEndPoissonField s f a b 0 y).re) y (Pi.single k 1)|≤
        C*∑ d : Fin 3,‖attachedEndPoissonField s f a b d.succ y‖ := by
  obtain ⟨C,hC,hbound⟩ := sourceCartesianGradient_uniform_bound
  refine ⟨C*(|a|+1),mul_pos hC (by positivity),?_⟩
  intro k
  filter_upwards [sourceCollar_open_charts_ae] with y hy hb ht
  obtain ⟨i,j,x,hx,rfl⟩ := hy hb
  rw [sourceCollarPiece_time_open hx] at ht
  rw [attachedEndPoisson_real_fderiv s hs f a b i j hx ht,dotProduct_single,mul_one]
  rw [Matrix.mulVec]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d _
  rw [abs_mul,endAxialMatrix,Matrix.mulVec_diagonal,abs_mul]
  have hd : |![a,1,1] d|≤|a|+1 := by
    fin_cases d
    · change |a|≤|a|+1; linarith
    · change |(1:ℝ)|≤|a|+1; rw [abs_one]; linarith [abs_nonneg a]
    · change |(1:ℝ)|≤|a|+1; rw [abs_one]; linarith [abs_nonneg a]
  have he := Complex.abs_re_le_norm (attachedEndPoissonField s f a b d.succ (sourceCollarPiece i j x))
  calc
    _ ≤ C*((|a|+1)*‖attachedEndPoissonField s f a b d.succ (sourceCollarPiece i j x)‖) :=
      mul_le_mul (hbound i j x (sourceCollarOpenBox_subset hx) k d)
        (mul_le_mul hd he (abs_nonneg _) (by positivity)) (by positivity) hC.le
    _ = _ := by ring

lemma attachedEndPoisson_grad_memLp (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    (f : spectralTraceGraph (torusRate s)) {a b l r R : ℝ}
    (ha : a≠0) (hR : 0≤R) (hb : b∈Icc (-(1:ℝ)/100) (1/100))
    (hlr : l ≤ r) (hl : -(1:ℝ)/100≤l) (hr : r≤1/100)
    (hT : ∀ t∈Icc l r,affineEndTime a b t∈Icc 0 R) (k : Fin 3) :
    MemLp (fun y => fderiv ℝ (fun y => (attachedEndPoissonField s f a b 0 y).re) y (Pi.single k 1))
      2 (volume.restrict (sourceClosedCollarBand l r)) := by
  obtain ⟨C,hC,hbound⟩ := attachedEndPoisson_grad_bound s hs f a b
  have hjet (d : Fin 3) := (attachedEndPoissonField_memLp s hs f ha hR hlr hl hr hT d.succ).norm
  have hsum : MemLp (fun y => C*∑ d : Fin 3,‖attachedEndPoissonField s f a b d.succ y‖) 2
      (volume.restrict (sourceClosedCollarBand l r)) :=
    (memLp_finsetSum Finset.univ (fun d _ => hjet d)).const_mul C
  apply hsum.mono' (measurable_fderiv_apply_const ℝ _ _).aestronglyMeasurable
  have hband : MeasurableSet (sourceClosedCollarBand l r) :=
    measurableSet_Icc.preimage measurable_sourcePhysicalCoordinates.fst
  filter_upwards [ae_restrict_mem hband,ae_restrict_of_ae (hbound k),
    ae_restrict_of_ae (sourceColevel_ae_ne hb)] with y hy hbd hne
  rw [Real.norm_eq_abs]
  exact hbd ⟨hl.trans hy.1,hy.2.trans hr⟩
    (lt_of_le_of_ne (hT _ hy).1 (Ne.symm (mul_ne_zero ha (sub_ne_zero.mpr hne))))

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_AttachedEndLinear
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace _root_.OAI.ScalarConductivity.spectralTraceGraph_realInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory Filter Topology
open scoped ENNReal

lemma endPoissonField_add_pos (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    (f g : spectralTraceGraph (torusRate s)) (j : Fin 4)
    {z : ℝ×UnitAddTorus (Fin 2)} (hz : 0<z.1) :
    endPoissonField s (f+g) j z=endPoissonField s f j z+endPoissonField s g j z := by
  have h := (endPoissonField_hasSum s hs f j hz).add (endPoissonField_hasSum s hs g j hz)
  apply (endPoissonField_hasSum s hs (f+g) j hz).unique
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext h
  change endPoissonModeField s h ((f.val 0 h)+(g.val 0 h)) j z=_
  simp [endPoissonModeField,endModeCoefficient_add,mul_add,add_mul]

lemma endPoissonField_rsmul_pos (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    (c : ℝ) (f : spectralTraceGraph (torusRate s)) (j : Fin 4)
    {z : ℝ×UnitAddTorus (Fin 2)} (hz : 0<z.1) :
    endPoissonField s (c•f) j z=c • endPoissonField s f j z := by
  have h := (endPoissonField_hasSum s hs f j hz).const_smul c
  apply (endPoissonField_hasSum s hs (c•f) j hz).unique
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext h
  change endPoissonModeField s h ((c:ℂ)*f.val 0 h) j z=c • _
  simp only [endPoissonModeField,endModeCoefficient_smul,Complex.real_smul]
  ring

def attachedEndFlatCLM (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    {a b l r R : ℝ} (ha : a≠0) (hR : 0≤R) (hlr : l ≤ r)
    (hl : -(1:ℝ)/100≤l) (hr : r≤1/100)
    (hT : ∀ t∈Icc l r,affineEndTime a b t∈Icc 0 R) (j : Fin 4) :
    spectralTraceGraph (torusRate s) →L[ℝ] Lp ℂ 2 (volume.restrict (sourceClosedCollarBand l r)) :=
  (Lp.LpToLpOfMeasureLeSMul (c:=1) (by simp)
    (by simpa only [one_smul] using sourceClosedCollarBand_measure_le hl hr)).comp
    ((sourceCollarPullback hlr hl hr).comp ((affineEndPullback ha hT).comp
      (((PiLp.proj 2 (fun _ : Fin 4 => Lp ℂ 2 (sourceCylinderMeasure 0 R)) (𝕜:=ℂ) j).restrictScalars ℝ).comp ((endPoissonCLM s hs R hR).restrictScalars ℝ))))

lemma attachedEndFlatCLM_ae (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    (f : spectralTraceGraph (torusRate s)) {a b l r R : ℝ}
    (ha : a≠0) (hR : 0≤R) (hlr : l ≤ r) (hl : -(1:ℝ)/100≤l) (hr : r≤1/100)
    (hT : ∀ t∈Icc l r,affineEndTime a b t∈Icc 0 R) (j : Fin 4) :
    attachedEndFlatCLM s hs ha hR hlr hl hr hT j f=ᵐ[volume.restrict (sourceClosedCollarBand l r)]
      attachedEndPoissonField s f a b j := by
  apply (Lp.coeFn_LpToLpOfMeasureLeSMul (c:=1) (by simp)
    (by simpa only [one_smul] using sourceClosedCollarBand_measure_le hl hr) _).trans
  exact (Measure.absolutelyContinuous_of_le (sourceClosedCollarBand_measure_le hl hr)).ae_eq
    (attachedEndPoissonJet_ae s hs f ha hR hlr hl hr hT j)

lemma attachedEndPoisson_real_fderiv_add_ae (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    (f g : spectralTraceGraph (torusRate s)) (a b : ℝ) :
    ∀ᵐ y : Fin 3 → ℝ,y∈sourceClosedCollarBand (-(1:ℝ)/100) (1/100) →
      0<a*(sourceCollarTime y-b) →
      fderiv ℝ (fun y => (attachedEndPoissonField s (f+g) a b 0 y).re) y=
        fderiv ℝ (fun y => (attachedEndPoissonField s f a b 0 y).re) y+
        fderiv ℝ (fun y => (attachedEndPoissonField s g a b 0 y).re) y := by
  filter_upwards [attachedEndPoisson_real_differentiable_ae s hs f a b,
    attachedEndPoisson_real_differentiable_ae s hs g a b] with y hf hg hy ht
  have he : (fun y => (attachedEndPoissonField s (f+g) a b 0 y).re)=ᶠ[𝓝 y]
      (fun y => (attachedEndPoissonField s f a b 0 y).re+(attachedEndPoissonField s g a b 0 y).re) := by
    filter_upwards [((attachedEndTime_lipschitz a b).choose_spec.continuous.continuousAt).eventually
      (lt_mem_nhds ht)] with z hz
    change (endPoissonField s (f+g) 0 _).re=_
    rw [endPoissonField_add_pos s hs f g 0 hz]
    rfl
  rw [he.fderiv_eq]
  exact fderiv_fun_add (hf hy ht) (hg hy ht)

lemma attachedEndPoisson_real_fderiv_rsmul_ae (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    (c : ℝ) (f : spectralTraceGraph (torusRate s)) (a b : ℝ) :
    ∀ᵐ y : Fin 3 → ℝ,y∈sourceClosedCollarBand (-(1:ℝ)/100) (1/100) →
      0<a*(sourceCollarTime y-b) →
      fderiv ℝ (fun y => (attachedEndPoissonField s (c•f) a b 0 y).re) y=
        c • fderiv ℝ (fun y => (attachedEndPoissonField s f a b 0 y).re) y := by
  filter_upwards [attachedEndPoisson_real_differentiable_ae s hs f a b] with y hf hy ht
  have he : (fun y => (attachedEndPoissonField s (c•f) a b 0 y).re)=ᶠ[𝓝 y]
      (fun y => c*(attachedEndPoissonField s f a b 0 y).re) := by
    filter_upwards [((attachedEndTime_lipschitz a b).choose_spec.continuous.continuousAt).eventually
      (lt_mem_nhds ht)] with z hz
    change (endPoissonField s (c•f) 0 _).re=_
    rw [endPoissonField_rsmul_pos s hs c f 0 hz]
    simp [attachedEndPoissonField]
  rw [he.fderiv_eq]
  exact fderiv_const_mul (hf hy ht) c

lemma attachedEndPoisson_grad_bound_uniform (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    (a b : ℝ) :
    ∃ C : ℝ,0<C ∧ ∀ (f : spectralTraceGraph (torusRate s)) (k : Fin 3),∀ᵐ y : Fin 3 → ℝ,
      y∈sourceClosedCollarBand (-(1:ℝ)/100) (1/100) → 0<a*(sourceCollarTime y-b) →
      |fderiv ℝ (fun y => (attachedEndPoissonField s f a b 0 y).re) y (Pi.single k 1)|≤
        C*∑ d : Fin 3,‖attachedEndPoissonField s f a b d.succ y‖ := by
  obtain ⟨C,hC,hbound⟩ := sourceCartesianGradient_uniform_bound
  refine ⟨C*(|a|+1),mul_pos hC (by positivity),?_⟩
  intro f k
  filter_upwards [sourceCollar_open_charts_ae] with y hy hb ht
  obtain ⟨i,j,x,hx,rfl⟩ := hy hb
  rw [sourceCollarPiece_time_open hx] at ht
  rw [attachedEndPoisson_real_fderiv s hs f a b i j hx ht,dotProduct_single,mul_one]
  rw [Matrix.mulVec]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d _
  rw [abs_mul,endAxialMatrix,Matrix.mulVec_diagonal,abs_mul]
  have hd : |![a,1,1] d|≤|a|+1 := by
    fin_cases d
    · change |a|≤|a|+1; linarith
    · change |(1:ℝ)|≤|a|+1; rw [abs_one]; linarith [abs_nonneg a]
    · change |(1:ℝ)|≤|a|+1; rw [abs_one]; linarith [abs_nonneg a]
  have he := Complex.abs_re_le_norm (attachedEndPoissonField s f a b d.succ (sourceCollarPiece i j x))
  calc
    _ ≤ C*((|a|+1)*‖attachedEndPoissonField s f a b d.succ (sourceCollarPiece i j x)‖) :=
      mul_le_mul (hbound i j x (sourceCollarOpenBox_subset hx) k d)
        (mul_le_mul hd he (abs_nonneg _) (by positivity)) (by positivity) hC.le
    _ = _ := by ring

variable (s : Fin 3 → ℝ)
  (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
  {a b l r R : ℝ} (ha : a≠0) (hR : 0≤R)
  (hb : b∈Icc (-(1:ℝ)/100) (1/100)) (hlr : l ≤ r)
  (hl : -(1:ℝ)/100≤l) (hr : r≤1/100)
  (hT : ∀ t∈Icc l r,affineEndTime a b t∈Icc 0 R)

include ha hb hl hr hT in
lemma attachedEndBand_positive_ae :
    ∀ᵐ y∂volume.restrict (sourceClosedCollarBand l r),
      y∈sourceClosedCollarBand (-(1:ℝ)/100) (1/100) ∧ 0<a*(sourceCollarTime y-b) := by
  filter_upwards [ae_restrict_mem ((isCompact_sourceClosedCollarBand hl hr).measurableSet),
    ae_restrict_of_ae (sourceColevel_ae_ne hb)] with y hy hne
  exact ⟨⟨hl.trans hy.1,hy.2.trans hr⟩,
    lt_of_le_of_ne (hT _ hy).1 (Ne.symm (mul_ne_zero ha (sub_ne_zero.mpr hne)))⟩

def attachedEndGradientL (k : Fin 3) :
    spectralTraceGraph (torusRate s) →ₗ[ℝ] Lp ℝ 2 (volume.restrict (sourceClosedCollarBand l r)) where
  toFun f := (attachedEndPoisson_grad_memLp s hs f ha hR hb hlr hl hr hT k).toLp _
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(attachedEndPoisson_grad_memLp s hs (f+g) ha hR hb hlr hl hr hT k).coeFn_toLp,
      (attachedEndPoisson_grad_memLp s hs f ha hR hb hlr hl hr hT k).coeFn_toLp,
      (attachedEndPoisson_grad_memLp s hs g ha hR hb hlr hl hr hT k).coeFn_toLp,
      Lp.coeFn_add ((attachedEndPoisson_grad_memLp s hs f ha hR hb hlr hl hr hT k).toLp _)
        ((attachedEndPoisson_grad_memLp s hs g ha hR hb hlr hl hr hT k).toLp _),
      ae_restrict_of_ae (attachedEndPoisson_real_fderiv_add_ae s hs f g a b),
      attachedEndBand_positive_ae ha hb hl hr hT] with x hfg hf hg he hd hx
    rw [hfg,he]
    simp only [Pi.add_apply,hf,hg,hd hx.1 hx.2]
    rfl
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [(attachedEndPoisson_grad_memLp s hs (c•f) ha hR hb hlr hl hr hT k).coeFn_toLp,
      (attachedEndPoisson_grad_memLp s hs f ha hR hb hlr hl hr hT k).coeFn_toLp,
      Lp.coeFn_smul c ((attachedEndPoisson_grad_memLp s hs f ha hR hb hlr hl hr hT k).toLp _),
      ae_restrict_of_ae (attachedEndPoisson_real_fderiv_rsmul_ae s hs c f a b),
      attachedEndBand_positive_ae ha hb hl hr hT] with x hcf hf he hd hx
    change _ = (c • _ : Lp ℝ 2 (volume.restrict (sourceClosedCollarBand l r))) x
    rw [hcf,he]
    simp only [Pi.smul_apply,hf,hd hx.1 hx.2]
    rfl

lemma attachedEndGradientL_ae (k : Fin 3) (f : spectralTraceGraph (torusRate s)) :
    attachedEndGradientL s hs ha hR hb hlr hl hr hT k f=ᵐ[volume.restrict (sourceClosedCollarBand l r)]
      (fun y => fderiv ℝ (fun y => (attachedEndPoissonField s f a b 0 y).re) y (Pi.single k 1)) :=
  (attachedEndPoisson_grad_memLp s hs f ha hR hb hlr hl hr hT k).coeFn_toLp

lemma attachedEndGradientL_bound (k : Fin 3) :
    ∃ C : ℝ,∀ f,‖attachedEndGradientL s hs ha hR hb hlr hl hr hT k f‖≤C*‖f‖ := by
  obtain ⟨C,hC,hbound⟩ := attachedEndPoisson_grad_bound_uniform s hs a b
  refine ⟨C*∑ d : Fin 3,‖attachedEndFlatCLM s hs ha hR hlr hl hr hT d.succ‖,fun f => ?_⟩
  have h : ‖attachedEndGradientL s hs ha hR hb hlr hl hr hT k f‖≤
      C*∑ d : Fin 3,‖attachedEndFlatCLM s hs ha hR hlr hl hr hT d.succ f‖ := by
    apply lp_norm_le_sum_norm_of_ae hC.le
    filter_upwards [attachedEndGradientL_ae s hs ha hR hb hlr hl hr hT k f,
      ae_all_iff.mpr (fun d : Fin 3 => attachedEndFlatCLM_ae s hs f ha hR hlr hl hr hT d.succ),
      ae_restrict_of_ae (hbound f k),attachedEndBand_positive_ae ha hb hl hr hT] with x hx hj hb hxpos
    rw [hx,Real.norm_eq_abs]
    simp only [hj]
    exact hb hxpos.1 hxpos.2
  calc
    _ ≤ C*∑ d : Fin 3,‖attachedEndFlatCLM s hs ha hR hlr hl hr hT d.succ f‖ := h
    _ ≤ C*∑ d : Fin 3,‖attachedEndFlatCLM s hs ha hR hlr hl hr hT d.succ‖*‖f‖ :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun d _ => ContinuousLinearMap.le_opNorm _ _)) hC.le
    _ = _ := by rw [← Finset.sum_mul]; ring

def attachedEndGradientCLM (k : Fin 3) :
    spectralTraceGraph (torusRate s) →L[ℝ] Lp ℝ 2 (volume.restrict (sourceClosedCollarBand l r)) :=
  (attachedEndGradientL s hs ha hR hb hlr hl hr hT k).mkContinuousOfExistsBound
    (attachedEndGradientL_bound s hs ha hR hb hlr hl hr hT k)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_CentralEnergySpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity

section
open Set MeasureTheory
open scoped ENNReal

def centralAmbientQ (s : Fin 3 → ℝ) : CentralAmbient s →L[ℝ] CentralAmbient s :=
  ContinuousLinearMap.id ℝ _-(centralAmbientM s).smulRight (centralAmbientOne s)

end

open Set MeasureTheory

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_CentralCoercivitySmooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory

def centralAmbientEnergy (s : Fin 3 → ℝ) (u : CentralAmbient s) : ℝ :=
  ‖centralAmbientD s u‖^2+
    ∑ i : Fin 3,‖spectralGraphWeight (torusRate s) (centralAmbientT s i u)‖^2

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_CentralPhysicalVariational
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory

def centralCoercivityConstant (s : Fin 3 → ℝ) : ℝ :=
  1+‖centralAmbientQ s‖^2*centralCoercivityBase

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_CentralWeightedVariational
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace _root_.OAI.ScalarConductivity.spectralTraceGraph_realInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory

variable {V G : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G]

def centralWeightedForm {ι : Type*} (κ : ℝ) (w : ι → ℝ) (D : V →L[ℝ] G)
    (T : Fin 3 → V →L[ℝ] spectralTraceGraph w) : V →L[ℝ] V →L[ℝ] ℝ :=
  (((innerSL ℝ).comp D).flip.comp D).flip + κ • ∑ i : Fin 3,
    (((innerSL ℝ).comp ((spectralGraphWeight w).comp (T i))).flip.comp
      ((spectralGraphWeight w).comp (T i))).flip

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_AttachedEndMatchedH1
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace _root_.OAI.ScalarConductivity.spectralTraceGraph_realInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped NNReal

theorem smooth_attachedEnd_matched_H1 {s : Fin 3 → ℝ}
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    (f : spectralTraceGraph (torusRate s)) {q χ : (Fin 3 → ℝ) → ℝ}
    (hq : ContDiff ℝ (↑(⊤:ℕ∞)) q) (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ)
    (hc : HasCompactSupport χ) (hχb : ∀ x,|χ x|≤1)
    {a b η : ℝ} (ha : a≠0) (hη : 0<η) (hl : -(1:ℝ)/100≤b-η) (hr : b+η≤1/100)
    (hχs : tsupport χ⊆sourceClosedCollarBand (b-η) (b+η))
    (htrace : ∀ h,f.val 0 h=mFourierCoeff (fun θ => (q (sourceAngularCollar b θ):ℂ)) h)
    (g : SpectralL2 TorusModes) (hg : ∀ h,g h=(torusRate s h:ℂ)*f.val 0 h) :
    ∃ w : H1,w∈H10 ∧ (∀ᵐ x∂ballMeasure,
      weakValue w x=cutMatchedValue (fun y => a*(sourceCollarTime y-b)) χ
        (fun y => (attachedEndPoissonField s f a b 0 y).re-q y) (WithLp.ofLp x) ∧
      ∀ i,weakGradient w x i=cutMatchedGradient (fun y => a*(sourceCollarTime y-b)) χ
        (fun y => (attachedEndPoissonField s f a b 0 y).re-q y)
        (fun y => fderiv ℝ (fun y => (attachedEndPoissonField s f a b 0 y).re) y-fderiv ℝ q y)
        i (WithLp.ofLp x)) := by
  let τ : (Fin 3 → ℝ) → ℝ := fun y => a*(sourceCollarTime y-b)
  let p : (Fin 3 → ℝ) → ℝ := fun y => (attachedEndPoissonField s f a b 0 y).re-q y
  let F : (Fin 3 → ℝ) → (Fin 3 → ℝ) →L[ℝ] ℝ :=
    fun y => fderiv ℝ (fun y => (attachedEndPoissonField s f a b 0 y).re) y-fderiv ℝ q y
  let R := |a| *η
  let l := min b (b+R/a)
  let r := max b (b+R/a)
  let D := sourceClosedCollarBand l r
  have hR : 0≤R := (mul_pos (abs_pos.mpr ha) hη).le
  have hdiv : R/|a|=η := by dsimp [R]; field_simp
  obtain ⟨hlen,hleft,hright,hiff,hnear⟩ := affine_layer_interval (b:=b) ha hR
  have hl' : -(1:ℝ)/100≤l := by dsimp only [l]; rw [hdiv] at hleft; linarith
  have hr' : r≤(1:ℝ)/100 := by dsimp only [r]; rw [hdiv] at hright; linarith
  have hb : b∈Icc (-(1:ℝ)/100) (1/100) := ⟨by linarith,by linarith⟩
  have hT : ∀ t∈Icc l r,affineEndTime a b t∈Icc 0 R := fun t ht => (hiff t).mp ht
  have hD : MeasurableSet D := (isCompact_sourceClosedCollarBand hl' hr').measurableSet
  have hDfull : D⊆sourceClosedCollarBand (-(1:ℝ)/100) (1/100) :=
    fun y hy => ⟨hl'.trans hy.1,hy.2.trans hr'⟩
  have hχfull : tsupport χ⊆sourceClosedCollarBand (-(1:ℝ)/100) (1/100) :=
    fun y hy => ⟨hl.trans (hχs hy).1,(hχs hy).2.trans hr⟩
  have htD : ∀ y∈tsupport χ,0<τ y → y∈D := by
    intro y hy ht
    apply (hiff _).mpr
    have hbound : |sourceCollarTime y-b|≤η := by
      apply abs_le.mpr
      constructor <;> linarith [(hχs hy).1,(hχs hy).2]
    refine ⟨ht.le,?_⟩
    calc
      a*(sourceCollarTime y-b) ≤ |a*(sourceCollarTime y-b)| := le_abs_self _
      _ = |a| *|sourceCollarTime y-b| := abs_mul _ _
      _ ≤ R := mul_le_mul_of_nonneg_left hbound (abs_nonneg a)
  have hp : MemLp p 2 (volume.restrict D) :=
    (attachedEndPoissonField_memLp s hs f ha hR min_le_max hl' hr' hT 0).re.sub
      (continuous_sourceBand_memLp hq.continuous hl' hr')
  obtain ⟨K,hK⟩ := attachedEndTime_lipschitz a b
  have hu := cutMatchedValue_memLp hK.continuous hχ.continuous hc hD hp htD
  apply localized_matched_seam_H1_pi hK hχ hc hD hp htD _ F _ _ (by norm_num : (5:ℝ)/2<3)
    (fun y hy => sourceBand_euclidean_bound (hχfull hy))
    (smooth_attachedEnd_cut_thin hs f hq hχb ha hη hl hr htrace g hg hu)
  · intro y hy ht
    exact (attachedEndPoissonField_localLip s hs f a b ht
      (sourceDirections_ne_zero_on_band (hχfull hy))).sub
      (localLipAt_of_contDiffAt (hq.of_le (by simp)).contDiffAt)
  · intro i
    exact (attachedEndPoisson_grad_memLp s hs f ha hR hb min_le_max hl' hr' hT i).sub
      (continuous_sourceBand_memLp ((hq.continuous_fderiv (by simp)).clm_apply continuous_const) hl' hr')
  · filter_upwards [ae_restrict_of_ae (attachedEndPoisson_real_differentiable_ae s hs f a b),
      ae_restrict_mem hD] with y hy hyD ht
    exact (hy (hDfull hyD) ht).hasFDerivAt.sub
      ((hq.differentiable (by simp)) y).hasFDerivAt

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_SmoothCollarTrace
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace _root_.OAI.ScalarConductivity.spectralTraceGraph_realInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal

theorem smoothCollarTrace_matched_H1 {s : Fin 3 → ℝ}
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    {q χ : (Fin 3 → ℝ) → ℝ}
    (hq : ContDiff ℝ (↑(⊤:ℕ∞)) q) (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ)
    (hc : HasCompactSupport χ) (hχb : ∀ x,|χ x|≤1)
    {a b η : ℝ} (ha : a≠0) (hη : 0<η) (hl : -(1:ℝ)/100≤b-η) (hr : b+η≤1/100)
    (hχs : tsupport χ⊆sourceClosedCollarBand (b-η) (b+η)) :
    let f := smoothCollarTrace s b hq
    ∃ w : H1,w∈H10 ∧ (∀ᵐ x∂ballMeasure,
      weakValue w x=cutMatchedValue (fun y => a*(sourceCollarTime y-b)) χ
        (fun y => (attachedEndPoissonField s f a b 0 y).re-q y) (WithLp.ofLp x) ∧
      ∀ i,weakGradient w x i=cutMatchedGradient (fun y => a*(sourceCollarTime y-b)) χ
        (fun y => (attachedEndPoissonField s f a b 0 y).re-q y)
        (fun y => fderiv ℝ (fun y => (attachedEndPoissonField s f a b 0 y).re) y-fderiv ℝ q y)
        i (WithLp.ofLp x)) := by
  exact smooth_attachedEnd_matched_H1 hs _ hq hχ hc hχb ha hη hl hr hχs
    (smoothCollarTrace_fst s b hq)
    ⟨_,smoothCollarTrace_rate_memℓp s b hq⟩ (fun _ => rfl)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_ParentCentralL2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory Filter Topology

def parentCentralComponentCLM (s : Fin 3 → ℝ) (i : Fin 4) :
    CentralAmbient s →L[ℝ] Lp ℝ 2 (volume : Measure (Fin 3 → ℝ)) :=
  (lpZeroExtensionCLM parentBand_measurable).comp
    ((lpRestrictionCLM (sourceClosedCollarBand centralThickness (2*centralThickness))).comp
      (centralPhysicalWholeCLM.comp (centralAmbientComponent s i)))

lemma parentCentralComponentCLM_smooth_ae (s : Fin 3 → ℝ) (f : centralSmoothFunctions) (i : Fin 4) :
    parentCentralComponentCLM s i (centralEmbedL s f)=ᵐ[volume]
      (sourceClosedCollarBand centralThickness (2*centralThickness)).indicator
        (fun y => centralJetField f i (sourcePairCoordinates y)) := by
  have hr := lpRestrictionCLM_ae (sourceClosedCollarBand centralThickness (2*centralThickness))
    (centralPhysicalWholeCLM (centralSmoothJet f i))
  have he := hr.trans (ae_restrict_of_ae (centralPhysicalWholeCLM_smooth_ae f i))
  have hb : (lpRestrictionCLM (sourceClosedCollarBand centralThickness (2*centralThickness))
      (centralPhysicalWholeCLM (centralSmoothJet f i)))=ᵐ[volume.restrict
      (sourceClosedCollarBand centralThickness (2*centralThickness))]
      (fun y => centralJetField f i (sourcePairCoordinates y)) := by
    filter_upwards [he,ae_restrict_mem parentBand_measurable] with y hy hb
    rw [hy,indicator_of_mem (show y∈centralPhysical from parentBand_central hb)]
  exact lpZeroExtensionCLM_ae_of_ae parentBand_measurable _ hb

variable (s : Fin 3 → ℝ)
  (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
  {a : ℝ} (ha : a<0)

def parentEndValueCLM : spectralTraceGraph (torusRate s) →L[ℝ]
    Lp ℝ 2 (volume : Measure (Fin 3 → ℝ)) :=
  (lpZeroExtensionCLM parentEndBand_measurable).comp
    ((Complex.reCLM.compLpL 2 (volume.restrict (sourceClosedCollarBand 0 centralThickness))).comp
      (attachedEndFlatCLM s hs ha.ne (show 0≤-a*centralThickness by
        exact mul_nonneg (neg_nonneg.mpr ha.le) (by norm_num [centralThickness]))
        (by norm_num [centralThickness]) (by norm_num) (by norm_num [centralThickness])
        (parentEndTime_mem ha) 0))

def parentEndGradientCLM (i : Fin 3) : spectralTraceGraph (torusRate s) →L[ℝ]
    Lp ℝ 2 (volume : Measure (Fin 3 → ℝ)) :=
  (lpZeroExtensionCLM parentEndBand_measurable).comp
    (attachedEndGradientCLM s hs ha.ne (show 0≤-a*centralThickness by
        exact mul_nonneg (neg_nonneg.mpr ha.le) (by norm_num [centralThickness]))
      (by norm_num [centralThickness]) (by norm_num [centralThickness])
      (by norm_num) (by norm_num [centralThickness]) (parentEndTime_mem ha) i)

lemma parentEndValueCLM_ae (f : spectralTraceGraph (torusRate s)) :
    parentEndValueCLM s hs ha f=ᵐ[volume]
      (sourceClosedCollarBand 0 centralThickness).indicator
        (fun y => (attachedEndPoissonField s f a centralThickness 0 y).re) := by
  apply lpZeroExtensionCLM_ae_of_ae parentEndBand_measurable
  have he := attachedEndFlatCLM_ae s hs f ha.ne
    (show 0≤-a*centralThickness by exact mul_nonneg (neg_nonneg.mpr ha.le) (by norm_num [centralThickness]))
    (show (0:ℝ) ≤ centralThickness by norm_num [centralThickness]) (by norm_num) (by norm_num [centralThickness])
    (parentEndTime_mem ha) 0
  apply (Complex.reCLM.coeFn_compLpL _).trans
  filter_upwards [he] with y hy
  exact congrArg Complex.re hy

lemma parentEndGradientCLM_ae (f : spectralTraceGraph (torusRate s)) (i : Fin 3) :
    parentEndGradientCLM s hs ha i f=ᵐ[volume]
      (sourceClosedCollarBand 0 centralThickness).indicator
        (fun y => fderiv ℝ (fun y => (attachedEndPoissonField s f a centralThickness 0 y).re) y (Pi.single i 1)) := by
  apply lpZeroExtensionCLM_ae_of_ae parentEndBand_measurable
  exact attachedEndGradientL_ae s hs ha.ne
    (show 0≤-a*centralThickness by exact mul_nonneg (neg_nonneg.mpr ha.le) (by norm_num [centralThickness]))
    (by norm_num [centralThickness]) (by norm_num [centralThickness])
    (by norm_num) (by norm_num [centralThickness]) (parentEndTime_mem ha) i f

def parentJoinedComponentCLM (i : Fin 4) : CentralAmbient s →L[ℝ]
    Lp ℝ 2 (volume : Measure (Fin 3 → ℝ)) :=
  parentCentralComponentCLM s i+
    ((Fin.cases (parentEndValueCLM s hs ha) (parentEndGradientCLM s hs ha) :
      Fin 4 → spectralTraceGraph (torusRate s) →L[ℝ] Lp ℝ 2 (volume : Measure (Fin 3 → ℝ))) i).comp (centralAmbientT s 0)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_LocalJoinedH1
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace _root_.OAI.ScalarConductivity.spectralTraceGraph_realInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma compact_smooth_pi_H1 {q : (Fin 3 → ℝ) → ℝ}
    (hq : ContDiff ℝ (↑(⊤:ℕ∞)) q) (hc : HasCompactSupport q)
    {R : ℝ} (hR : R<3) (hs : ∀ x∈tsupport q,‖WithLp.toLp 2 x‖≤R) :
    ∃ w : H1,w∈H10 ∧ (∀ᵐ x∂ballMeasure,
      weakValue w x=q (WithLp.ofLp x) ∧ ∀ i,
      weakGradient w x i=fderiv ℝ q (WithLp.ofLp x) (Pi.single i 1)) := by
  let E : R3 ≃L[ℝ] (Fin 3 → ℝ) := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)
  have hd : ContDiff ℝ (↑(⊤:ℕ∞)) (q ∘ E) := hq.comp E.contDiff
  refine ⟨smoothH1 (q ∘ E) hd,smoothH1_mem_H10 _ hd ?_ ?_,?_⟩
  · exact hc.comp_homeomorph E.toHomeomorph
  · intro x hx
    have hh : tsupport (q ∘ E)⊆E ⁻¹' tsupport q :=
      closure_minimal (fun y hy => subset_tsupport q hy) ((isClosed_tsupport q).preimage E.continuous)
    have hx' : E x∈tsupport q := hh hx
    have hnorm := (hs (E x) hx').trans_lt hR
    have he : WithLp.toLp 2 (E x)=x := rfl
    rw [he] at hnorm
    simpa only [ball,Metric.mem_ball,dist_zero_right] using hnorm
  · filter_upwards [smoothH1_value (q ∘ E) hd,smoothH1_gradient (q ∘ E) hd] with x hx hg
    refine ⟨hx,fun i => ?_⟩
    rw [hg]
    exact gradient_of_pi_function q x i ((hq.differentiable (by simp)) _)

theorem smoothCollarTrace_localJoined_H1 {s : Fin 3 → ℝ}
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    {q χ : (Fin 3 → ℝ) → ℝ}
    (hq : ContDiff ℝ (↑(⊤:ℕ∞)) q) (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ)
    (hc : HasCompactSupport χ) (hχb : ∀ x,|χ x|≤1)
    {a b η : ℝ} (ha : a≠0) (hη : 0<η) (hl : -(1:ℝ)/100≤b-η) (hr : b+η≤1/100)
    (hχs : tsupport χ⊆sourceClosedCollarBand (b-η) (b+η)) :
    let p := fun y => (attachedEndPoissonField s (smoothCollarTrace s b hq) a b 0 y).re
    ∃ w : H1,w∈H10 ∧ (∀ᵐ x∂ballMeasure,
      weakValue w x=localJoinedValue (fun y => a*(sourceCollarTime y-b)) χ q p (WithLp.ofLp x) ∧
      ∀ i,weakGradient w x i=localJoinedGradient (fun y => a*(sourceCollarTime y-b)) χ q p i (WithLp.ofLp x)) := by
  obtain ⟨w,hw,hwe⟩ := smoothCollarTrace_matched_H1 hs hq hχ hc hχb ha hη hl hr hχs
  obtain ⟨z,hz,hze⟩ := compact_smooth_pi_H1 (hχ.mul hq) (hc.mul_right (f':=q))
    (by norm_num : (5:ℝ)/2<3) (fun x hx => sourceBand_euclidean_bound
      (show x∈sourceClosedCollarBand (-(1:ℝ)/100) (1/100) from
        ⟨hl.trans (hχs (tsupport_mul_subset_left hx)).1,
          (hχs (tsupport_mul_subset_left hx)).2.trans hr⟩))
  refine ⟨w+z,H10.add_mem hw hz,?_⟩
  filter_upwards [hwe,hze,weakValue_add w z,weakGradient_add w z] with x hx hz hv hg
  refine ⟨?_,fun i => ?_⟩
  · rw [hv]
    change weakValue w x+weakValue z x=_
    rw [hx.1,hz.1]
    dsimp only [Pi.add_apply,localJoinedValue,cutMatchedValue]
    split_ifs <;> ring
  · rw [hg]
    change weakGradient w x i+weakGradient z x i=_
    rw [hx.2 i,hz.2 i]
    change _+fderiv ℝ (χ*q) (WithLp.ofLp x) (Pi.single i 1)=_
    rw [fderiv_mul ((hχ.differentiable (by simp)) _) ((hq.differentiable (by simp)) _)]
    simp only [cutMatchedGradient,localJoinedGradient,sub_apply,
      add_apply,smul_apply,smul_eq_mul]
    split_ifs <;> ring

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_ParentLocalizedJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity

section
open Set MeasureTheory Filter Topology

variable (s : Fin 3 → ℝ)
  (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
  {a : ℝ} (ha : a<0)
  {χ : (Fin 3 → ℝ) → ℝ} (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ) (hc : HasCompactSupport χ)

def parentLocalComponentCLM (i : Fin 4) : CentralAmbient s →L[ℝ]
    Lp ℝ 2 (volume : Measure (Fin 3 → ℝ)) :=
  Fin.cases ((compactMultiplierCLM hχ.continuous hc).comp (parentJoinedComponentCLM s hs ha 0))
    (fun j => ((compactMultiplierCLM ((hχ.continuous_fderiv (by simp)).clm_apply continuous_const)
        (hc.fderiv_apply ℝ (Pi.single j 1))).comp (parentJoinedComponentCLM s hs ha 0))+
      ((compactMultiplierCLM hχ.continuous hc).comp (parentJoinedComponentCLM s hs ha j.succ))) i

def parentLocalJetCLM : CentralAmbient s →L[ℝ] JetSpace :=
  physicalFourJetCLM.comp (ContinuousLinearMap.pi (parentLocalComponentCLM s hs ha hχ hc))

end

open Set MeasureTheory Filter Topology

variable (s : Fin 3 → ℝ)
  (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
  {a : ℝ} (ha : a<0)
  {χ : (Fin 3 → ℝ) → ℝ} (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ) (hc : HasCompactSupport χ)
  (hχs : tsupport χ⊆sourceClosedCollarBand 0 (2*centralThickness))

lemma parentJoinedComponentCLM_smooth_value (f : centralSmoothFunctions) :
    parentJoinedComponentCLM s hs ha 0 (centralEmbedL s f)=ᵐ[volume] (fun y =>
      (sourceClosedCollarBand centralThickness (2*centralThickness)).indicator
        (fun y => f (sourcePairCoordinates y)) y+
      (sourceClosedCollarBand 0 centralThickness).indicator
        (fun y => (attachedEndPoissonField s (centralSmoothTrace s f 0) a centralThickness 0 y).re) y) := by
  apply (Lp.coeFn_add _ _).trans
  filter_upwards [parentCentralComponentCLM_smooth_ae s f 0,parentEndValueCLM_ae s hs ha (centralSmoothTrace s f 0)] with y hy hz
  change (parentCentralComponentCLM s 0 (centralEmbedL s f)) y+
    (parentEndValueCLM s hs ha (centralSmoothTrace s f 0)) y=_
  rw [hy,hz]
  rfl

lemma parentJoinedComponentCLM_smooth_gradient (f : centralSmoothFunctions) (i : Fin 3) :
    parentJoinedComponentCLM s hs ha i.succ (centralEmbedL s f)=ᵐ[volume] (fun y =>
      (sourceClosedCollarBand centralThickness (2*centralThickness)).indicator
        (fun y => fderiv ℝ (fun y => f (sourcePairCoordinates y)) y (Pi.single i 1)) y+
      (sourceClosedCollarBand 0 centralThickness).indicator
        (fun y => fderiv ℝ (fun y => (attachedEndPoissonField s (centralSmoothTrace s f 0) a centralThickness 0 y).re) y (Pi.single i 1)) y) := by
  apply (Lp.coeFn_add _ _).trans
  filter_upwards [parentCentralComponentCLM_smooth_ae s f i.succ,parentEndGradientCLM_ae s hs ha (centralSmoothTrace s f 0) i] with y hy hz
  change (parentCentralComponentCLM s i.succ (centralEmbedL s f)) y+
    (parentEndGradientCLM s hs ha i (centralSmoothTrace s f 0)) y=_
  rw [hy,hz]
  simp only [central_parent_partial]

include hχs in
lemma parentLocalComponentCLM_smooth_value (f : centralSmoothFunctions) :
    parentLocalComponentCLM s hs ha hχ hc 0 (centralEmbedL s f)=ᵐ[volume]
      localJoinedValue (fun y => a*(sourceCollarTime y-centralThickness)) χ
        (fun y => f (sourcePairCoordinates y))
        (fun y => (attachedEndPoissonField s (centralSmoothTrace s f 0) a centralThickness 0 y).re) := by
  have he := compactMultiplierCLM_ae hχ.continuous hc (parentJoinedComponentCLM s hs ha 0 (centralEmbedL s f))
  filter_upwards [he,parentJoinedComponentCLM_smooth_value s hs ha f,
    sourceColevel_ae_ne (show centralThickness∈Icc (-(1:ℝ)/100) (1/100) by norm_num [centralThickness])] with y hy hv hn
  simp only [parentLocalComponentCLM, Fin.cases_zero, ContinuousLinearMap.comp_apply, localJoinedValue]
  rw [hy,hv]
  by_cases hys : y∈tsupport χ
  · rw [parent_band_indicator_join ha y (hχs hys) hn]
  · rw [image_eq_zero_of_notMem_tsupport hys]
    simp

include hχs in
lemma parentLocalComponentCLM_smooth_gradient (f : centralSmoothFunctions) (i : Fin 3) :
    parentLocalComponentCLM s hs ha hχ hc i.succ (centralEmbedL s f)=ᵐ[volume]
      localJoinedGradient (fun y => a*(sourceCollarTime y-centralThickness)) χ
        (fun y => f (sourcePairCoordinates y))
        (fun y => (attachedEndPoissonField s (centralSmoothTrace s f 0) a centralThickness 0 y).re) i := by
  have he₀ := compactMultiplierCLM_ae ((hχ.continuous_fderiv (by simp)).clm_apply continuous_const)
    (hc.fderiv_apply ℝ (Pi.single i 1)) (parentJoinedComponentCLM s hs ha 0 (centralEmbedL s f))
  have he₁ := compactMultiplierCLM_ae hχ.continuous hc (parentJoinedComponentCLM s hs ha i.succ (centralEmbedL s f))
  apply (Lp.coeFn_add _ _).trans
  filter_upwards [he₀,he₁,parentJoinedComponentCLM_smooth_value s hs ha f,
    parentJoinedComponentCLM_smooth_gradient s hs ha f i,
    sourceColevel_ae_ne (show centralThickness∈Icc (-(1:ℝ)/100) (1/100) by norm_num [centralThickness])] with y h₀ h₁ hv hg hn
  change (compactMultiplierCLM ((hχ.continuous_fderiv (by simp)).clm_apply continuous_const)
    (hc.fderiv_apply ℝ (Pi.single i 1)) (parentJoinedComponentCLM s hs ha 0 (centralEmbedL s f))) y+
      (compactMultiplierCLM hχ.continuous hc (parentJoinedComponentCLM s hs ha i.succ (centralEmbedL s f))) y=_
  rw [h₀,h₁,hv,hg]
  simp only [localJoinedGradient]
  by_cases hys : y∈tsupport χ
  · rw [parent_band_indicator_join ha y (hχs hys) hn,
      parent_band_indicator_join ha y (hχs hys) hn]
  · rw [image_eq_zero_of_notMem_tsupport hys,fderiv_of_notMem_tsupport ℝ hys]
    simp

include hχs in
lemma parentLocalJetCLM_smooth_ae (f : centralSmoothFunctions) :
    parentLocalJetCLM s hs ha hχ hc (centralEmbedL s f)=ᵐ[ballMeasure] (fun x =>
      WithLp.toLp 2 (Fin.cases
        (localJoinedValue (fun y => a*(sourceCollarTime y-centralThickness)) χ
          (fun y => f (sourcePairCoordinates y))
          (fun y => (attachedEndPoissonField s (centralSmoothTrace s f 0) a centralThickness 0 y).re) (WithLp.ofLp x))
        (fun i => localJoinedGradient (fun y => a*(sourceCollarTime y-centralThickness)) χ
          (fun y => f (sourcePairCoordinates y))
          (fun y => (attachedEndPoissonField s (centralSmoothTrace s f 0) a centralThickness 0 y).re) i (WithLp.ofLp x)))) := by
  have h₀ := ae_restrict_of_ae (s:=ball) ((PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae_eq_comp
    (parentLocalComponentCLM_smooth_value s hs ha hχ hc hχs f))
  have h₁ (i : Fin 3) := ae_restrict_of_ae (s:=ball) ((PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae_eq_comp
    (parentLocalComponentCLM_smooth_gradient s hs ha hχ hc hχs f i))
  apply (physicalFourJetCLM_ae (fun i => parentLocalComponentCLM s hs ha hχ hc i (centralEmbedL s f))).trans
  filter_upwards [h₀,ae_all_iff.mpr h₁] with x hv hg
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hv
  · exact hg j

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_ParentCompletionJoin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity

section
open Set MeasureTheory Filter Topology

variable (s : Fin 3 → ℝ)
  (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
  {a : ℝ} (ha : a<0)
  {χ : (Fin 3 → ℝ) → ℝ} (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ) (hc : HasCompactSupport χ)
  (hχb : ∀ x,|χ x|≤1)
  (hχs : tsupport χ⊆sourceClosedCollarBand 0 (2*centralThickness))

include hχb hχs in
lemma parentLocalJetCLM_smooth_H10 (f : centralSmoothFunctions) :
    parentLocalJetCLM s hs ha hχ hc (centralEmbedL s f)∈zeroTraceAmbient := by
  have hq := (central_smooth f).comp sourcePairCLE.contDiff
  obtain ⟨w,hw,hwe⟩ := smoothCollarTrace_localJoined_H1 hs hq hχ hc hχb ha.ne
    (show (0:ℝ) < centralThickness by norm_num [centralThickness])
    (show -(1:ℝ)/100 ≤ centralThickness-centralThickness by norm_num)
    (show centralThickness+centralThickness≤(1:ℝ)/100 by norm_num [centralThickness])
    (by simpa only [sub_self,two_mul] using hχs)
  dsimp only at hwe
  rw [central_parent_trace_eq s f] at hwe
  have he : parentLocalJetCLM s hs ha hχ hc (centralEmbedL s f)=w.val := by
    apply Lp.ext
    filter_upwards [parentLocalJetCLM_smooth_ae s hs ha hχ hc hχs f,hwe] with x hx hwx
    rw [hx]
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hwx.1.symm
    · exact (hwx.2 j).symm
  rw [he]
  exact hw

include hχb hχs in

theorem parentLocalJetCLM_central_H10 (u : centralEnergySpace s) :
    parentLocalJetCLM s hs ha hχ hc u.val∈zeroTraceAmbient := by
  let T := (zeroTraceAmbient.comap (parentLocalJetCLM s hs ha hχ hc).toLinearMap)
  have ht : IsClosed (T : Set (CentralAmbient s)) :=
    (Submodule.isClosed_topologicalClosure (Submodule.span ℝ compactSmoothJets)).preimage
      (parentLocalJetCLM s hs ha hχ hc).continuous
  have hr : LinearMap.range (centralEmbedL s)≤T := by
    rintro z ⟨f,rfl⟩
    exact parentLocalJetCLM_smooth_H10 s hs ha hχ hc hχb hχs f
  exact (Submodule.topologicalClosure_minimal _ hr ht) u.property

def parentCompletionJoin : centralEnergySpace s →L[ℝ] H1 :=
  ((parentLocalJetCLM s hs ha hχ hc).comp (centralEnergySpace s).subtypeL).codRestrict H1Space
    (fun u => zeroTraceAmbient_le_H1Space (parentLocalJetCLM_central_H10 s hs ha hχ hc hχb hχs u))

end

open Set MeasureTheory Filter Topology
open scoped ENNReal

variable {X Y E : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure X} {ν : Measure Y} (e : X ≃ᵐ Y) {c : ℝ≥0∞}
  (hc : c≠∞) (hmap : Measure.map e μ ≤ c • ν)

lemma sourceChildCoordinates_quasi (σ : ℝ) :
    Measure.QuasiMeasurePreserving (sourceChildCoordinates σ) volume volume := by
  refine ⟨(sourceChildHomeomorph σ).measurable,?_⟩
  rw [sourceChildCoordinates_map_volume]
  exact Measure.smul_absolutelyContinuous

def sourceChildPullbackCLM (σ : ℝ) : Lp E 2 (volume : Measure (Fin 3 → ℝ)) →L[ℝ]
    Lp E 2 (volume : Measure (Fin 3 → ℝ)) :=
  lpBoundedPullbackCLM (sourceChildHomeomorph σ).toMeasurableEquiv ENNReal.ofReal_ne_top
    (le_of_eq (sourceChildCoordinates_map_volume σ))

lemma sourceChildPullbackCLM_ae (σ : ℝ) (f : Lp E 2 (volume : Measure (Fin 3 → ℝ))) :
    sourceChildPullbackCLM σ f=ᵐ[volume] (fun y => f (sourceChildCoordinates σ y)) :=
  lpBoundedPullbackCLM_ae _ _ _ f

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_ChildCentralL2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory Filter Topology

def childCentralRawComponentCLM (s : Fin 3 → ℝ) (k : Fin 2) (i : Fin 4) :
    CentralAmbient s →L[ℝ] Lp ℝ 2 (volume : Measure (Fin 3 → ℝ)) :=
  (lpZeroExtensionCLM childCentralBand_measurable).comp
    ((lpRestrictionCLM (sourceClosedCollarBand (-2*centralThickness) (-centralThickness))).comp
      ((sourceChildPullbackCLM (actualChildSign k)).comp
        (centralPhysicalWholeCLM.comp (centralAmbientComponent s i))))

lemma childCentralRawComponentCLM_smooth_ae (s : Fin 3 → ℝ) (k : Fin 2)
    (f : centralSmoothFunctions) (i : Fin 4) :
    childCentralRawComponentCLM s k i (centralEmbedL s f)=ᵐ[volume]
      (sourceClosedCollarBand (-2*centralThickness) (-centralThickness)).indicator
        (fun y => centralJetField f i (sourcePairCoordinates (sourceChildCoordinates (actualChildSign k) y))) := by
  have hp := (sourceChildPullbackCLM_ae (actualChildSign k) (centralPhysicalWholeCLM (centralSmoothJet f i))).trans
    ((sourceChildCoordinates_quasi (actualChildSign k)).ae_eq_comp (centralPhysicalWholeCLM_smooth_ae f i))
  have hr := (lpRestrictionCLM_ae (sourceClosedCollarBand (-2*centralThickness) (-centralThickness))
    (sourceChildPullbackCLM (actualChildSign k) (centralPhysicalWholeCLM (centralSmoothJet f i)))).trans
      (ae_restrict_of_ae hp)
  apply lpZeroExtensionCLM_ae_of_ae childCentralBand_measurable
  filter_upwards [hr,ae_restrict_mem childCentralBand_measurable] with y hy hb
  change (lpRestrictionCLM (sourceClosedCollarBand (-2*centralThickness) (-centralThickness))
    (sourceChildPullbackCLM (actualChildSign k) (centralPhysicalWholeCLM (centralSmoothJet f i)))) y=_
  rw [hy,Function.comp_apply,indicator_of_mem (show sourceChildCoordinates (actualChildSign k) y∈centralPhysical from childBand_central k hb)]

def childCentralComponentCLM (s : Fin 3 → ℝ) (k : Fin 2) (i : Fin 4) :
    CentralAmbient s →L[ℝ] Lp ℝ 2 (volume : Measure (Fin 3 → ℝ)) :=
  Fin.cases (childCentralRawComponentCLM s k 0)
    (fun j => sourceScale • childCentralRawComponentCLM s k (childAxis j).succ) i

lemma childCentralComponentCLM_smooth_value (s : Fin 3 → ℝ) (k : Fin 2) (f : centralSmoothFunctions) :
    childCentralComponentCLM s k 0 (centralEmbedL s f)=ᵐ[volume]
      (sourceClosedCollarBand (-2*centralThickness) (-centralThickness)).indicator
        (fun y => f (sourcePairCoordinates (sourceChildCoordinates (actualChildSign k) y))) :=
  childCentralRawComponentCLM_smooth_ae s k f 0

lemma childCentralComponentCLM_smooth_gradient (s : Fin 3 → ℝ) (k : Fin 2)
    (f : centralSmoothFunctions) (i : Fin 3) :
    childCentralComponentCLM s k i.succ (centralEmbedL s f)=ᵐ[volume]
      (sourceClosedCollarBand (-2*centralThickness) (-centralThickness)).indicator
        (fun y => fderiv ℝ (fun y => f (sourcePairCoordinates (sourceChildCoordinates (actualChildSign k) y))) y (Pi.single i 1)) := by
  apply (Lp.coeFn_smul sourceScale (childCentralRawComponentCLM s k (childAxis i).succ (centralEmbedL s f))).trans
  filter_upwards [childCentralRawComponentCLM_smooth_ae s k f (childAxis i).succ] with y hy
  change sourceScale*_=_
  rw [hy]
  by_cases hb : y∈sourceClosedCollarBand (-2*centralThickness) (-centralThickness)
  · simp only [indicator_of_mem hb,central_child_partial]
  · simp only [indicator_of_notMem hb,mul_zero]

variable (s : Fin 3 → ℝ)
  (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
  {a : ℝ} (ha : 0<a)

def childEndValueCLM : spectralTraceGraph (torusRate s) →L[ℝ]
    Lp ℝ 2 (volume : Measure (Fin 3 → ℝ)) :=
  (lpZeroExtensionCLM childEndBand_measurable).comp
    ((Complex.reCLM.compLpL 2 (volume.restrict (sourceClosedCollarBand (-centralThickness) 0))).comp
      (attachedEndFlatCLM s hs ha.ne' (show 0≤a*centralThickness by
        exact mul_nonneg ha.le (by norm_num [centralThickness]))
        (by norm_num [centralThickness]) (by norm_num [centralThickness]) (by norm_num)
        (childEndTime_mem ha) 0))

def childEndGradientCLM (i : Fin 3) : spectralTraceGraph (torusRate s) →L[ℝ]
    Lp ℝ 2 (volume : Measure (Fin 3 → ℝ)) :=
  (lpZeroExtensionCLM childEndBand_measurable).comp
    (attachedEndGradientCLM s hs ha.ne' (show 0≤a*centralThickness by
        exact mul_nonneg ha.le (by norm_num [centralThickness]))
      (by norm_num [centralThickness]) (by norm_num [centralThickness])
      (by norm_num [centralThickness]) (by norm_num) (childEndTime_mem ha) i)

lemma childEndValueCLM_ae (f : spectralTraceGraph (torusRate s)) :
    childEndValueCLM s hs ha f=ᵐ[volume]
      (sourceClosedCollarBand (-centralThickness) 0).indicator
        (fun y => (attachedEndPoissonField s f a (-centralThickness) 0 y).re) := by
  apply lpZeroExtensionCLM_ae_of_ae childEndBand_measurable
  have he := attachedEndFlatCLM_ae s hs f ha.ne'
    (show 0≤a*centralThickness by exact mul_nonneg ha.le (by norm_num [centralThickness]))
    (show -centralThickness≤(0:ℝ) by norm_num [centralThickness]) (by norm_num [centralThickness]) (by norm_num)
    (childEndTime_mem ha) 0
  apply (Complex.reCLM.coeFn_compLpL _).trans
  filter_upwards [he] with y hy
  exact congrArg Complex.re hy

lemma childEndGradientCLM_ae (f : spectralTraceGraph (torusRate s)) (i : Fin 3) :
    childEndGradientCLM s hs ha i f=ᵐ[volume]
      (sourceClosedCollarBand (-centralThickness) 0).indicator
        (fun y => fderiv ℝ (fun y => (attachedEndPoissonField s f a (-centralThickness) 0 y).re) y (Pi.single i 1)) := by
  apply lpZeroExtensionCLM_ae_of_ae childEndBand_measurable
  exact attachedEndGradientL_ae s hs ha.ne'
    (show 0≤a*centralThickness by exact mul_nonneg ha.le (by norm_num [centralThickness]))
    (by norm_num [centralThickness]) (by norm_num [centralThickness])
    (by norm_num [centralThickness]) (by norm_num) (childEndTime_mem ha) i f

def childJoinedComponentCLM (k : Fin 2) (i : Fin 4) : CentralAmbient s →L[ℝ]
    Lp ℝ 2 (volume : Measure (Fin 3 → ℝ)) :=
  childCentralComponentCLM s k i+
    ((Fin.cases (childEndValueCLM s hs ha) (childEndGradientCLM s hs ha) :
      Fin 4 → spectralTraceGraph (torusRate s) →L[ℝ] Lp ℝ 2 (volume : Measure (Fin 3 → ℝ))) i).comp (centralAmbientT s k.succ)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_CentralPhysicalRegion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma centralParent_time_iff (y : Fin 3 → ℝ) :
    centralThickness ≤ sourceCollarTime y ↔
      centralParentFootprint (sourcePairCoordinates y).1 ∧ |y 2| ≤ centralHeight := by
  rw [sourceCollarTime_ge_iff]
  have hL : 0 < sourceLength := by norm_num [sourceLength]
  simp only [sourceRadial,max_le_iff,le_max_iff,centralParentFootprint,sourcePairCoordinates,
    centralHeight,centralOuterX,centralInnerX,centralOuterY,centralInnerY]
  rw [div_le_iff₀ hL,le_div_iff₀ hL]
  constructor
  · rintro ⟨hz,hi,ho⟩
    exact ⟨⟨by nlinarith [ho.1],ho.2,hi.imp (fun h => by nlinarith [h]) id⟩,hz⟩
  · rintro ⟨⟨hx,hy,hi⟩,hz⟩
    exact ⟨hz,hi.imp (fun h => by nlinarith [h]) id,⟨by nlinarith [hx],hy⟩⟩

theorem centralPhysical_time_iff (y : Fin 3 → ℝ) :
    y∈centralPhysical ↔ centralThickness ≤ sourceCollarTime y ∧
      (∀ k : Fin 2,sourceCollarTime ((sourceChildHomeomorph (actualChildSign k)).symm y) ≤  -centralThickness) := by
  simp only [centralParent_time_iff,centralChild_time_iff,centralPhysical,mem_preimage,
    centralClosed,mem_ofPred_eq,sourcePairCoordinates,actualChildSign,Fin.forall_fin_two,
    ite_true,Fin.isValue,one_ne_zero,ite_false]
  tauto

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_CentralJoinCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma centralPhysical_subset_ball {y : Fin 3 → ℝ} (hy : y∈centralPhysical) :
    WithLp.toLp 2 y∈ball := by
  have hp := (centralParent_time_iff y).mp ((centralPhysical_time_iff y).mp hy).1
  have ho : WithLp.toLp 2 y∈sourceOuterBox := by
    change |y 0| ≤ sourceLength ∧ |y 1| ≤ 1 ∧ |y 2| ≤ 1
    rcases hp with ⟨⟨hx,hy,_⟩,hz⟩
    dsimp [sourcePairCoordinates] at hx hy
    norm_num [centralOuterX,centralOuterY,centralHeight,sourceLength,sourceRadialWidth,
      sourceHole,centralThickness] at hx hy hz ⊢
    exact ⟨by linarith,by linarith,by linarith⟩
  have hn := sourceBox_norm_bound ho
  simpa only [ball,Metric.mem_ball,dist_zero_right] using
    hn.trans (by norm_num : (5:ℝ)/2<3)

lemma centralPhysical_mem_interior_of_strict {y : Fin 3 → ℝ}
    (hp : centralThickness < sourceCollarTime y)
    (hc : ∀ k : Fin 2,sourceCollarTime ((sourceChildHomeomorph (actualChildSign k)).symm y)< -centralThickness) :
    y∈interior centralPhysical := by
  have ht := locallyLipschitz_sourceCollarTime.continuous
  have hp' : ∀ᶠ z in 𝓝 y,centralThickness < sourceCollarTime z :=
    ht.continuousAt (Ioi_mem_nhds hp)
  have hc' (k : Fin 2) : ∀ᶠ z in 𝓝 y,sourceCollarTime ((sourceChildHomeomorph (actualChildSign k)).symm z)< -centralThickness :=
    (ht.comp (sourceChildHomeomorph (actualChildSign k)).symm.continuous).continuousAt (Iio_mem_nhds (hc k))
  apply mem_interior_iff_mem_nhds.mpr
  filter_upwards [hp',eventually_all.mpr hc'] with z hpz hcz
  exact (centralPhysical_time_iff z).mpr ⟨hpz.le,fun k => (hcz k).le⟩

lemma centralJoinOpen_covers : centralPhysical⊆⋃ i,centralJoinOpen i := by
  intro y hy
  obtain ⟨hp,hc⟩ := (centralPhysical_time_iff y).mp hy
  by_cases hpe : sourceCollarTime y=centralThickness
  · apply mem_iUnion.mpr
    refine ⟨1,?_⟩
    change sourceCollarTime y∈Ioo 0 (2*centralThickness)
    rw [hpe]
    norm_num [centralThickness]
  by_cases hce : ∃ k : Fin 2,sourceCollarTime ((sourceChildHomeomorph (actualChildSign k)).symm y)= -centralThickness
  · obtain ⟨k,hk⟩ := hce
    apply mem_iUnion.mpr
    fin_cases k
    · refine ⟨2,?_⟩
      change sourceCollarTime ((sourceChildHomeomorph 1).symm y)∈Ioo (-2*centralThickness) 0
      norm_num [actualChildSign] at hk
      rw [hk]
      norm_num [centralThickness]
    · refine ⟨3,?_⟩
      change sourceCollarTime ((sourceChildHomeomorph (-1)).symm y)∈Ioo (-2*centralThickness) 0
      norm_num [actualChildSign] at hk
      rw [hk]
      norm_num [centralThickness]
  · exact mem_iUnion.mpr ⟨0,centralPhysical_mem_interior_of_strict
      (lt_of_le_of_ne hp (Ne.symm hpe)) (fun k => lt_of_le_of_ne (hc k) (fun he => hce ⟨k,he⟩))⟩

theorem exists_centralJoinPartition_neighborhood :
    ∃ ρ : SmoothPartitionOfUnity (Fin 4) (modelWithCornersSelf ℝ (Fin 3 → ℝ))
        (Fin 3 → ℝ) centralPhysical,ρ.IsSubordinate centralJoinOpen ∧
      ∀ y∈centralPhysical,(fun z => ∑ i : Fin 4,ρ i z)=ᶠ[𝓝 y] (fun _ => (1:ℝ)) := by
  obtain ⟨K,hK,hKc,hCK,hKU⟩ := exists_compact_closed_between centralPhysical_compact
    (isOpen_iUnion centralJoinOpen_isOpen) centralJoinOpen_covers
  obtain ⟨g,hg⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (modelWithCornersSelf ℝ (Fin 3 → ℝ)) hKc centralJoinOpen centralJoinOpen_isOpen hKU
  let ρ : SmoothPartitionOfUnity (Fin 4) (modelWithCornersSelf ℝ (Fin 3 → ℝ))
      (Fin 3 → ℝ) centralPhysical :=
    { toFun := g.toFun
      locallyFinite' := g.locallyFinite'
      nonneg' := g.nonneg'
      sum_eq_one' := fun y hy => g.sum_eq_one (interior_subset (hCK hy))
      sum_le_one' := g.sum_le_one' }
  refine ⟨ρ,hg,fun y hy => ?_⟩
  filter_upwards [mem_interior_iff_mem_nhds.mp (hCK hy)] with z hz
  change ∑ i : Fin 4,g i z=1
  simpa only [finsum_eq_sum_of_fintype] using g.sum_eq_one hz

def centralJoinPartition : SmoothPartitionOfUnity (Fin 4)
    (modelWithCornersSelf ℝ (Fin 3 → ℝ)) (Fin 3 → ℝ) centralPhysical :=
  Classical.choose exists_centralJoinPartition_neighborhood

lemma centralJoinPartition_subordinate : centralJoinPartition.IsSubordinate centralJoinOpen :=
  (Classical.choose_spec exists_centralJoinPartition_neighborhood).1

lemma centralJoinPartition_smooth (i : Fin 4) : ContDiff ℝ (↑(⊤:ℕ∞)) (centralJoinPartition i) :=
  (centralJoinPartition i).contMDiff.contDiff

lemma centralJoinPartition_bound (i : Fin 4) (y : Fin 3 → ℝ) : |centralJoinPartition i y| ≤ 1 := by
  rw [abs_of_nonneg (centralJoinPartition.nonneg i y)]
  exact centralJoinPartition.le_one i y

lemma centralJoinPartition_interior_support : tsupport (centralJoinPartition 0)⊆centralPhysical :=
  (centralJoinPartition_subordinate 0).trans interior_subset

lemma centralJoinPartition_interior_compact : HasCompactSupport (centralJoinPartition 0) :=
  centralPhysical_compact.of_isClosed_subset (isClosed_tsupport _) centralJoinPartition_interior_support

lemma centralJoinPartition_parent_support :
    tsupport (centralJoinPartition 1)⊆sourceClosedCollarBand 0 (2*centralThickness) := by
  intro y hy
  have ht := centralJoinPartition_subordinate 1 hy
  change sourceCollarTime y∈Ioo 0 (2*centralThickness) at ht
  exact ⟨ht.1.le,ht.2.le⟩

lemma centralJoinPartition_parent_compact : HasCompactSupport (centralJoinPartition 1) :=
  (isCompact_sourceClosedCollarBand (by norm_num) (by norm_num [centralThickness])).of_isClosed_subset
    (isClosed_tsupport _) centralJoinPartition_parent_support

def centralJoinChildCutoff (k : Fin 2) (y : Fin 3 → ℝ) : ℝ :=
  centralJoinPartition (centralChildPatch k) (sourceChildCoordinates (actualChildSign k) y)

lemma centralJoinChildCutoff_smooth (k : Fin 2) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (centralJoinChildCutoff k) :=
  (centralJoinPartition_smooth _).comp (sourceChildCoordinates_contDiff _)

lemma centralJoinChildCutoff_bound (k : Fin 2) (y : Fin 3 → ℝ) : |centralJoinChildCutoff k y| ≤ 1 :=
  centralJoinPartition_bound _ _

lemma centralJoinChildCutoff_support (k : Fin 2) :
    tsupport (centralJoinChildCutoff k)⊆sourceClosedCollarBand (-2*centralThickness) 0 := by
  intro y hy
  have ht : sourceChildCoordinates (actualChildSign k) y∈tsupport (centralJoinPartition (centralChildPatch k)) :=
    tsupport_comp_subset_preimage (centralJoinPartition (centralChildPatch k))
      (sourceChildCoordinates_contDiff _).continuous hy
  have hp := centralJoinPartition_subordinate (centralChildPatch k) ht
  have he : centralJoinOpen (centralChildPatch k)=
      (fun z => sourceCollarTime ((sourceChildHomeomorph (actualChildSign k)).symm z)) ⁻¹' Ioo (-2*centralThickness) 0 := by
    fin_cases k <;> norm_num [centralJoinOpen,centralChildPatch,actualChildSign]
  rw [he] at hp
  change sourceCollarTime ((sourceChildHomeomorph (actualChildSign k)).symm
    ((sourceChildHomeomorph (actualChildSign k)) y))∈Ioo (-2*centralThickness) 0 at hp
  rw [Homeomorph.symm_apply_apply] at hp
  exact ⟨hp.1.le,hp.2.le⟩

lemma centralJoinChildCutoff_compact (k : Fin 2) : HasCompactSupport (centralJoinChildCutoff k) :=
  (isCompact_sourceClosedCollarBand (by norm_num [centralThickness]) (by norm_num)).of_isClosed_subset
    (isClosed_tsupport _) (centralJoinChildCutoff_support k)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_ChildLocalizedJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity

section
open Set MeasureTheory Filter Topology

variable (s : Fin 3 → ℝ)
  (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
  {a : ℝ} (ha : 0<a)
  (k : Fin 2)
  {χ : (Fin 3 → ℝ) → ℝ} (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ) (hc : HasCompactSupport χ)

def childLocalComponentCLM (i : Fin 4) : CentralAmbient s →L[ℝ]
    Lp ℝ 2 (volume : Measure (Fin 3 → ℝ)) :=
  Fin.cases ((compactMultiplierCLM hχ.continuous hc).comp (childJoinedComponentCLM s hs ha k 0))
    (fun j => ((compactMultiplierCLM ((hχ.continuous_fderiv (by simp)).clm_apply continuous_const)
        (hc.fderiv_apply ℝ (Pi.single j 1))).comp (childJoinedComponentCLM s hs ha k 0))+
      ((compactMultiplierCLM hχ.continuous hc).comp (childJoinedComponentCLM s hs ha k j.succ))) i

def childLocalJetCLM : CentralAmbient s →L[ℝ] JetSpace :=
  physicalFourJetCLM.comp (ContinuousLinearMap.pi (childLocalComponentCLM s hs ha k hχ hc))

end

open Set MeasureTheory Filter Topology

variable (s : Fin 3 → ℝ)
  (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
  {a : ℝ} (ha : 0<a)
  (k : Fin 2)
  {χ : (Fin 3 → ℝ) → ℝ} (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ) (hc : HasCompactSupport χ)
  (hχs : tsupport χ⊆sourceClosedCollarBand (-2*centralThickness) 0)

lemma childJoinedComponentCLM_smooth_value (f : centralSmoothFunctions) :
    childJoinedComponentCLM s hs ha k 0 (centralEmbedL s f)=ᵐ[volume] (fun y =>
      (sourceClosedCollarBand (-2*centralThickness) (-centralThickness)).indicator
        (fun y => f (sourcePairCoordinates (sourceChildCoordinates (actualChildSign k) y))) y+
      (sourceClosedCollarBand (-centralThickness) 0).indicator
        (fun y => (attachedEndPoissonField s (centralSmoothTrace s f k.succ) a (-centralThickness) 0 y).re) y) := by
  apply (Lp.coeFn_add _ _).trans
  filter_upwards [childCentralComponentCLM_smooth_value s k f,childEndValueCLM_ae s hs ha (centralSmoothTrace s f k.succ)] with y hy hz
  change (childCentralComponentCLM s k 0 (centralEmbedL s f)) y+
    (childEndValueCLM s hs ha (centralSmoothTrace s f k.succ)) y=_
  rw [hy,hz]

lemma childJoinedComponentCLM_smooth_gradient (f : centralSmoothFunctions) (i : Fin 3) :
    childJoinedComponentCLM s hs ha k i.succ (centralEmbedL s f)=ᵐ[volume] (fun y =>
      (sourceClosedCollarBand (-2*centralThickness) (-centralThickness)).indicator
        (fun y => fderiv ℝ (fun y => f (sourcePairCoordinates (sourceChildCoordinates (actualChildSign k) y))) y (Pi.single i 1)) y+
      (sourceClosedCollarBand (-centralThickness) 0).indicator
        (fun y => fderiv ℝ (fun y => (attachedEndPoissonField s (centralSmoothTrace s f k.succ) a (-centralThickness) 0 y).re) y (Pi.single i 1)) y) := by
  apply (Lp.coeFn_add _ _).trans
  filter_upwards [childCentralComponentCLM_smooth_gradient s k f i,childEndGradientCLM_ae s hs ha (centralSmoothTrace s f k.succ) i] with y hy hz
  change (childCentralComponentCLM s k i.succ (centralEmbedL s f)) y+
    (childEndGradientCLM s hs ha i (centralSmoothTrace s f k.succ)) y=_
  rw [hy,hz]

include hχs in
lemma childLocalComponentCLM_smooth_value (f : centralSmoothFunctions) :
    childLocalComponentCLM s hs ha k hχ hc 0 (centralEmbedL s f)=ᵐ[volume]
      localJoinedValue (fun y => a*(sourceCollarTime y-(-centralThickness))) χ
        (fun y => f (sourcePairCoordinates (sourceChildCoordinates (actualChildSign k) y)))
        (fun y => (attachedEndPoissonField s (centralSmoothTrace s f k.succ) a (-centralThickness) 0 y).re) := by
  have he := compactMultiplierCLM_ae hχ.continuous hc (childJoinedComponentCLM s hs ha k 0 (centralEmbedL s f))
  filter_upwards [he,childJoinedComponentCLM_smooth_value s hs ha k f,
    sourceColevel_ae_ne (show -centralThickness∈Icc (-(1:ℝ)/100) (1/100) by norm_num [centralThickness])] with y hy hv hn
  simp only [childLocalComponentCLM, Fin.cases_zero, ContinuousLinearMap.comp_apply, localJoinedValue]
  rw [hy,hv]
  by_cases hys : y∈tsupport χ
  · rw [child_band_indicator_join ha y (hχs hys) hn]
  · rw [image_eq_zero_of_notMem_tsupport hys]
    simp

include hχs in
lemma childLocalComponentCLM_smooth_gradient (f : centralSmoothFunctions) (i : Fin 3) :
    childLocalComponentCLM s hs ha k hχ hc i.succ (centralEmbedL s f)=ᵐ[volume]
      localJoinedGradient (fun y => a*(sourceCollarTime y-(-centralThickness))) χ
        (fun y => f (sourcePairCoordinates (sourceChildCoordinates (actualChildSign k) y)))
        (fun y => (attachedEndPoissonField s (centralSmoothTrace s f k.succ) a (-centralThickness) 0 y).re) i := by
  have he₀ := compactMultiplierCLM_ae ((hχ.continuous_fderiv (by simp)).clm_apply continuous_const)
    (hc.fderiv_apply ℝ (Pi.single i 1)) (childJoinedComponentCLM s hs ha k 0 (centralEmbedL s f))
  have he₁ := compactMultiplierCLM_ae hχ.continuous hc (childJoinedComponentCLM s hs ha k i.succ (centralEmbedL s f))
  apply (Lp.coeFn_add _ _).trans
  filter_upwards [he₀,he₁,childJoinedComponentCLM_smooth_value s hs ha k f,
    childJoinedComponentCLM_smooth_gradient s hs ha k f i,
    sourceColevel_ae_ne (show -centralThickness∈Icc (-(1:ℝ)/100) (1/100) by norm_num [centralThickness])] with y h₀ h₁ hv hg hn
  change (compactMultiplierCLM ((hχ.continuous_fderiv (by simp)).clm_apply continuous_const)
    (hc.fderiv_apply ℝ (Pi.single i 1)) (childJoinedComponentCLM s hs ha k 0 (centralEmbedL s f))) y+
      (compactMultiplierCLM hχ.continuous hc (childJoinedComponentCLM s hs ha k i.succ (centralEmbedL s f))) y=_
  rw [h₀,h₁,hv,hg]
  simp only [localJoinedGradient]
  by_cases hys : y∈tsupport χ
  · rw [child_band_indicator_join ha y (hχs hys) hn,
      child_band_indicator_join ha y (hχs hys) hn]
  · rw [image_eq_zero_of_notMem_tsupport hys,fderiv_of_notMem_tsupport ℝ hys]
    simp

include hχs in
lemma childLocalJetCLM_smooth_ae (f : centralSmoothFunctions) :
    childLocalJetCLM s hs ha k hχ hc (centralEmbedL s f)=ᵐ[ballMeasure] (fun x =>
      WithLp.toLp 2 (Fin.cases
        (localJoinedValue (fun y => a*(sourceCollarTime y-(-centralThickness))) χ
          (fun y => f (sourcePairCoordinates (sourceChildCoordinates (actualChildSign k) y)))
          (fun y => (attachedEndPoissonField s (centralSmoothTrace s f k.succ) a (-centralThickness) 0 y).re) (WithLp.ofLp x))
        (fun i => localJoinedGradient (fun y => a*(sourceCollarTime y-(-centralThickness))) χ
          (fun y => f (sourcePairCoordinates (sourceChildCoordinates (actualChildSign k) y)))
          (fun y => (attachedEndPoissonField s (centralSmoothTrace s f k.succ) a (-centralThickness) 0 y).re) i (WithLp.ofLp x)))) := by
  have h₀ := ae_restrict_of_ae (s:=ball) ((PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae_eq_comp
    (childLocalComponentCLM_smooth_value s hs ha k hχ hc hχs f))
  have h₁ (i : Fin 3) := ae_restrict_of_ae (s:=ball) ((PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae_eq_comp
    (childLocalComponentCLM_smooth_gradient s hs ha k hχ hc hχs f i))
  apply (physicalFourJetCLM_ae (fun i => childLocalComponentCLM s hs ha k hχ hc i (centralEmbedL s f))).trans
  filter_upwards [h₀,ae_all_iff.mpr h₁] with x hv hg
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hv
  · exact hg j

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_ChildCompletionJoin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

variable (s : Fin 3 → ℝ)
  (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
  {a : ℝ} (ha : 0<a)
  (k : Fin 2)
  {χ : (Fin 3 → ℝ) → ℝ} (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ) (hc : HasCompactSupport χ)
  (hχb : ∀ x,|χ x|≤1)
  (hχs : tsupport χ⊆sourceClosedCollarBand (-2*centralThickness) 0)

include hχb hχs in
lemma childLocalJetCLM_smooth_H10 (f : centralSmoothFunctions) :
    childLocalJetCLM s hs ha k hχ hc (centralEmbedL s f)∈zeroTraceAmbient := by
  have hq := ((central_smooth f).comp sourcePairCLE.contDiff).comp (sourceChildCoordinates_contDiff (actualChildSign k))
  obtain ⟨w,hw,hwe⟩ := smoothCollarTrace_localJoined_H1 hs hq hχ hc hχb ha.ne'
    (show (0:ℝ) < centralThickness by norm_num [centralThickness])
    (show -(1:ℝ)/100≤(-centralThickness)-centralThickness by norm_num [centralThickness])
    (show (-centralThickness)+centralThickness≤(1:ℝ)/100 by norm_num [centralThickness])
    (by
      convert hχs using 1
      all_goals try with_reducible_and_instances rfl
      congr 1 <;> ring)
  dsimp only at hwe
  rw [central_child_trace_eq s k f] at hwe
  have he : childLocalJetCLM s hs ha k hχ hc (centralEmbedL s f)=w.val := by
    apply Lp.ext
    filter_upwards [childLocalJetCLM_smooth_ae s hs ha k hχ hc hχs f,hwe] with x hx hwx
    rw [hx]
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hwx.1.symm
    · exact (hwx.2 j).symm
  rw [he]
  exact hw

include hχb hχs in

theorem childLocalJetCLM_central_H10 (u : centralEnergySpace s) :
    childLocalJetCLM s hs ha k hχ hc u.val∈zeroTraceAmbient := by
  let T := (zeroTraceAmbient.comap (childLocalJetCLM s hs ha k hχ hc).toLinearMap)
  have ht : IsClosed (T : Set (CentralAmbient s)) :=
    (Submodule.isClosed_topologicalClosure (Submodule.span ℝ compactSmoothJets)).preimage
      (childLocalJetCLM s hs ha k hχ hc).continuous
  have hr : LinearMap.range (centralEmbedL s)≤T := by
    rintro z ⟨f,rfl⟩
    exact childLocalJetCLM_smooth_H10 s hs ha k hχ hc hχb hχs f
  exact (Submodule.topologicalClosure_minimal _ hr ht) u.property

def childCompletionJoin : centralEnergySpace s →L[ℝ] H1 :=
  ((childLocalJetCLM s hs ha k hχ hc).comp (centralEnergySpace s).subtypeL).codRestrict H1Space
    (fun u => zeroTraceAmbient_le_H1Space (childLocalJetCLM_central_H10 s hs ha k hχ hc hχb hχs u))

lemma childCompletionJoin_mem_H10 (u : centralEnergySpace s) :
    childCompletionJoin s hs ha k hχ hc hχb hχs u∈H10 :=
  childLocalJetCLM_central_H10 s hs ha k hχ hc hχb hχs u

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_ChildH10Transport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity

section
open Set MeasureTheory Filter Topology

open Set MeasureTheory Filter Topology

variable (s : Fin 3 → ℝ)
  (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
  {a : ℝ} (ha : 0<a) (k : Fin 2)
  {χ : (Fin 3 → ℝ) → ℝ} (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ) (hc : HasCompactSupport χ)
  (hχb : ∀ x,|χ x|≤1)
  (hχs : tsupport χ⊆sourceClosedCollarBand (-2*centralThickness) 0)

def physicalChildCompletionJoin : centralEnergySpace s →L[ℝ] H1 :=
  (childH10Transport k).comp
    ((childCompletionJoin s hs ha k hχ hc hχb hχs).codRestrict H10
      (childCompletionJoin_mem_H10 s hs ha k hχ hc hχb hχs))

end

open Set MeasureTheory Filter Topology

variable (s : Fin 3 → ℝ)
  {χ : (Fin 3 → ℝ) → ℝ} (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ) (hc : HasCompactSupport χ)

def centralInteriorComponentCLM (i : Fin 4) : CentralAmbient s →L[ℝ]
    Lp ℝ 2 (volume : Measure (Fin 3 → ℝ)) :=
  Fin.cases ((compactMultiplierCLM hχ.continuous hc).comp
      (centralPhysicalWholeCLM.comp (centralAmbientComponent s 0)))
    (fun j => ((compactMultiplierCLM ((hχ.continuous_fderiv (by simp)).clm_apply continuous_const)
        (hc.fderiv_apply ℝ (Pi.single j 1))).comp
          (centralPhysicalWholeCLM.comp (centralAmbientComponent s 0)))+
      ((compactMultiplierCLM hχ.continuous hc).comp
        (centralPhysicalWholeCLM.comp (centralAmbientComponent s j.succ)))) i

def centralInteriorJetCLM : CentralAmbient s →L[ℝ] JetSpace :=
  physicalFourJetCLM.comp (ContinuousLinearMap.pi (centralInteriorComponentCLM s hχ hc))

lemma centralInteriorComponentCLM_smooth_value
    (hχs : tsupport χ⊆centralPhysical) (f : centralSmoothFunctions) :
    centralInteriorComponentCLM s hχ hc 0 (centralEmbedL s f)=ᵐ[volume]
      (fun y => χ y*f (sourcePairCoordinates y)) := by
  have he := compactMultiplierCLM_ae hχ.continuous hc
    (centralPhysicalWholeCLM (centralSmoothJet f 0))
  filter_upwards [he,centralPhysicalWholeCLM_smooth_ae f 0] with y hy hv
  change (compactMultiplierCLM hχ.continuous hc
    (centralPhysicalWholeCLM (centralSmoothJet f 0))) y=_
  rw [hy,hv]
  by_cases hs : y∈tsupport χ
  · rw [indicator_of_mem (hχs hs)]
    rfl
  · rw [image_eq_zero_of_notMem_tsupport hs]
    simp

lemma centralInteriorComponentCLM_smooth_gradient
    (hχs : tsupport χ⊆centralPhysical) (f : centralSmoothFunctions) (i : Fin 3) :
    centralInteriorComponentCLM s hχ hc i.succ (centralEmbedL s f)=ᵐ[volume]
      (fun y => fderiv ℝ (fun y => χ y*f (sourcePairCoordinates y)) y (Pi.single i 1)) := by
  have hq : ContDiff ℝ (↑(⊤:ℕ∞)) (fun y => f (sourcePairCoordinates y)) :=
    (central_smooth f).comp sourcePairCLE.contDiff
  have he₀ := compactMultiplierCLM_ae ((hχ.continuous_fderiv (by simp)).clm_apply continuous_const)
    (hc.fderiv_apply ℝ (Pi.single i 1)) (centralPhysicalWholeCLM (centralSmoothJet f 0))
  have he₁ := compactMultiplierCLM_ae hχ.continuous hc (centralPhysicalWholeCLM (centralSmoothJet f i.succ))
  apply (Lp.coeFn_add _ _).trans
  filter_upwards [he₀,he₁,centralPhysicalWholeCLM_smooth_ae f 0,
    centralPhysicalWholeCLM_smooth_ae f i.succ] with y h₀ h₁ hv hg
  change (compactMultiplierCLM ((hχ.continuous_fderiv (by simp)).clm_apply continuous_const)
      (hc.fderiv_apply ℝ (Pi.single i 1)) (centralPhysicalWholeCLM (centralSmoothJet f 0))) y+
    (compactMultiplierCLM hχ.continuous hc (centralPhysicalWholeCLM (centralSmoothJet f i.succ))) y=_
  rw [h₀,h₁,hv,hg]
  change _=fderiv ℝ (χ*(fun y => f (sourcePairCoordinates y))) y (Pi.single i 1)
  rw [fderiv_mul ((hχ.differentiable (by simp)) _) ((hq.differentiable (by simp)) _)]
  simp only [add_apply,smul_apply,smul_eq_mul]
  by_cases hs : y∈tsupport χ
  · rw [indicator_of_mem (hχs hs),indicator_of_mem (hχs hs),central_parent_partial]
    change fderiv ℝ χ y (Pi.single i 1)*f (sourcePairCoordinates y)+χ y*_ =
      χ y*_+f (sourcePairCoordinates y)*fderiv ℝ χ y (Pi.single i 1)
    ring
  · rw [image_eq_zero_of_notMem_tsupport hs,fderiv_of_notMem_tsupport ℝ hs]
    simp

lemma centralInteriorJetCLM_smooth_H10
    (hχs : tsupport χ⊆centralPhysical)
    (hχB : ∀ y∈tsupport χ,WithLp.toLp 2 y∈ball) (f : centralSmoothFunctions) :
    centralInteriorJetCLM s hχ hc (centralEmbedL s f)∈zeroTraceAmbient := by
  let q := fun y => χ y*f (sourcePairCoordinates y)
  let E : R3 ≃L[ℝ] (Fin 3 → ℝ) := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)
  have hq : ContDiff ℝ (↑(⊤:ℕ∞)) q := hχ.mul ((central_smooth f).comp sourcePairCLE.contDiff)
  have hqe : ContDiff ℝ (↑(⊤:ℕ∞)) (q ∘ E) := hq.comp E.contDiff
  have ht : tsupport (q ∘ E)⊆E ⁻¹' tsupport χ :=
    closure_minimal (fun y hy => subset_tsupport χ (fun hc => hy (by simp [q,hc])))
      ((isClosed_tsupport χ).preimage E.continuous)
  have htB : tsupport (q ∘ E)⊆ball := fun x hx => hχB (E x) (ht hx)
  have hmem := smoothH1_mem_H10 (q ∘ E) hqe ((hc.mul_right (f':=fun y => f (sourcePairCoordinates y))).comp_homeomorph E.toHomeomorph) htB
  have he : centralInteriorJetCLM s hχ hc (centralEmbedL s f)=(smoothH1 (q ∘ E) hqe).val := by
    apply Lp.ext
    have ha₀ := ae_restrict_of_ae (s:=ball) ((PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae_eq_comp
      (centralInteriorComponentCLM_smooth_value s hχ hc hχs f))
    have ha₁ (i : Fin 3) := ae_restrict_of_ae (s:=ball) ((PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae_eq_comp
      (centralInteriorComponentCLM_smooth_gradient s hχ hc hχs f i))
    filter_upwards [physicalFourJetCLM_ae (fun i => centralInteriorComponentCLM s hχ hc i (centralEmbedL s f)),
      ha₀,ae_all_iff.mpr ha₁,(smoothJet_memLp hqe).coeFn_toLp] with x hj hv hg hs
    change (smoothH1 (q ∘ E) hqe).val x=smoothJet (q ∘ E) x at hs
    rw [hs]
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact (congrArg (fun z : JetFiber => z 0) hj).trans hv
    · exact (congrArg (fun z : JetFiber => z j.succ) hj).trans
        ((hg j).trans (gradient_of_pi_function q x j ((hq.differentiable (by simp)) _)).symm)
  rw [he]
  exact hmem

theorem centralInteriorJetCLM_central_H10
    (hχs : tsupport χ⊆centralPhysical)
    (hχB : ∀ y∈tsupport χ,WithLp.toLp 2 y∈ball) (u : centralEnergySpace s) :
    centralInteriorJetCLM s hχ hc u.val∈zeroTraceAmbient := by
  let T := zeroTraceAmbient.comap (centralInteriorJetCLM s hχ hc).toLinearMap
  have ht : IsClosed (T : Set (CentralAmbient s)) :=
    (Submodule.isClosed_topologicalClosure (Submodule.span ℝ compactSmoothJets)).preimage
      (centralInteriorJetCLM s hχ hc).continuous
  have hr : LinearMap.range (centralEmbedL s)≤T := by
    rintro z ⟨f,rfl⟩
    exact centralInteriorJetCLM_smooth_H10 s hχ hc hχs hχB f
  exact (Submodule.topologicalClosure_minimal _ hr ht) u.property

def centralInteriorCompletion (hχs : tsupport χ⊆centralPhysical)
    (hχB : ∀ y∈tsupport χ,WithLp.toLp 2 y∈ball) : centralEnergySpace s →L[ℝ] H1 :=
  ((centralInteriorJetCLM s hχ hc).comp (centralEnergySpace s).subtypeL).codRestrict H1Space
    (fun u => zeroTraceAmbient_le_H1Space (centralInteriorJetCLM_central_H10 s hχ hc hχs hχB u))

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_WholeBallJetFormula
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology
open scoped Classical

lemma ballWholePiComponentCLM_ae_of_ae (i : Fin 4) (z : JetSpace)
    (f : (Fin 3 → ℝ) → JetFiber)
    (he : z=ᵐ[ballMeasure] (fun x => f (WithLp.ofLp x))) :
    ballWholePiComponentCLM i z=ᵐ[volume]
      (fun y => if WithLp.toLp 2 y∈ball then f y i else 0) := by
  filter_upwards [ballWholePiComponentCLM_ae i z,ballWholePiJetCLM_ae_of_ae z f he] with y hi hy
  rw [hi,hy]
  split_ifs <;> rfl

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_CentralNeighborhoodCompletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

variable (s : Fin 3 → ℝ)
  (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
  {a : Fin 3 → ℝ} (ha₀ : a 0<0) (ha : ∀ k : Fin 2,0<a k.succ)

def centralNeighborhoodCompletion : centralEnergySpace s →L[ℝ] H1 :=
  centralInteriorCompletion s (centralJoinPartition_smooth 0)
    centralJoinPartition_interior_compact centralJoinPartition_interior_support
    (fun _ hy => centralPhysical_subset_ball (centralJoinPartition_interior_support hy))+
  parentCompletionJoin s hs ha₀ (centralJoinPartition_smooth 1)
    centralJoinPartition_parent_compact (centralJoinPartition_bound 1)
    centralJoinPartition_parent_support+
  ∑ k : Fin 2,physicalChildCompletionJoin s hs (ha k) k (centralJoinChildCutoff_smooth k)
    (centralJoinChildCutoff_compact k) (centralJoinChildCutoff_bound k) (centralJoinChildCutoff_support k)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_CentralLocalAgreement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity

open Set MeasureTheory Filter Topology

open Set MeasureTheory Filter Topology

variable (s : Fin 3 → ℝ)
  (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
  {a : Fin 3 → ℝ} (ha₀ : a 0<0) (ha : ∀ k : Fin 2,0<a k.succ)

def centralNeighborhoodRawCLM : CentralAmbient s →L[ℝ] JetSpace :=
  centralInteriorJetCLM s (centralJoinPartition_smooth 0) centralJoinPartition_interior_compact+
  parentLocalJetCLM s hs ha₀ (centralJoinPartition_smooth 1) centralJoinPartition_parent_compact+
  ((childTransportJetCLM 0).comp (childLocalJetCLM s hs (ha 0) 0
      (centralJoinChildCutoff_smooth 0) (centralJoinChildCutoff_compact 0))+
    (childTransportJetCLM 1).comp (childLocalJetCLM s hs (ha 1) 1
      (centralJoinChildCutoff_smooth 1) (centralJoinChildCutoff_compact 1)))

def centralFullJetCLM : CentralAmbient s →L[ℝ] JetSpace :=
  physicalFourJetCLM.comp (ContinuousLinearMap.pi (fun i =>
    centralPhysicalWholeCLM.comp (centralAmbientComponent s i)))

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_AttachedFlatTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

def attachedPhysicalFlatTensor (s : Fin 3 → ℝ) (a : ℝ) (i j : Fin 4)
    (y : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  attachedFlatTensor s a i j (sourceCollarInverse i j y)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_PhysicalTensorPatch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

def attachedPatchTensor (s : Fin 3 → ℝ) (a : ℝ) (i j : Fin 4)
    (y : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  by classical exact if y∈sourceFlatPatch i j then attachedPhysicalFlatTensor s a i j y else 1

end ScalarConductivity

end


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

def attachedFaceTensorList (s : Fin 3 → ℝ) (a : ℝ) (ks : List (Fin 4 × Fin 4))
    (y : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ := by
  classical
  exact ks.foldr (fun k A => if y∈sourceFlatPatch k.1 k.2 then
    attachedPatchTensor s a k.1 k.2 y else A) 1

def attachedCollarTensor (s : Fin 3 → ℝ) (a : ℝ) :
    (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ :=
  attachedFaceTensorList s a (Finset.univ : Finset (Fin 4 × Fin 4)).toList

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_CutAttachedEndH1
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace _root_.OAI.ScalarConductivity.spectralTraceGraph_realInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace ScalarConductivity
open Set MeasureTheory Filter Topology

def fullAttachedEndValue (s : Fin 3 → ℝ) (f : spectralTraceGraph (torusRate s))
    (a b κ : ℝ) (y : Fin 3 → ℝ) : ℝ :=
  (attachedEndPoissonField s f a b 0 y).re+κ*(a*(sourceCollarTime y-b))

def fullAttachedEndGradient (s : Fin 3 → ℝ) (f : spectralTraceGraph (torusRate s))
    (a b κ : ℝ) (y : Fin 3 → ℝ) (i : Fin 3) : ℝ :=
  fderiv ℝ (fun y => (attachedEndPoissonField s f a b 0 y).re) y (Pi.single i 1)+
    κ*fderiv ℝ (fun y => a*(sourceCollarTime y-b)) y (Pi.single i 1)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_PhysicalTestEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

def attachedFlatTestCovector (φ : (Fin 3 → ℝ) → ℝ) (a : ℝ)
    (i j : Fin 4) (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  (attachedCartesianMatrix a i j x)⁻¹ *ᵥ physicalTestCovector φ (sourceCollarPiece i j x)

end ScalarConductivity

end


end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_BoxCoordinateBridge
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace _root_.OAI.ScalarConductivity.centralMeasure_finite _root_.OAI.ScalarConductivity.instCoeFunSubtypeForallBox3RealMemSubmoduleCentralSmoothFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory

lemma boxCoordinates_apply (x : Coord3) : boxCoordinates x=((x 0,x 1),x 2) := rfl
lemma boxCoordinates_symm_apply (p : Box3) : boxCoordinates.symm p=![p.1.1,p.1.2,p.2] := rfl

lemma boxCoordinates_fderiv (f : Box3 → ℝ) (hf : Differentiable ℝ f)
    (x v : Coord3) :
    fderiv ℝ (f∘boxCoordinates) x v=fderiv ℝ f (boxCoordinates x) (boxCoordinates v) := by
  rw [fderiv_comp x (hf _) boxCoordinates.differentiableAt]
  have he : fderiv ℝ (fun x => boxCoordinates x) x=boxCoordinates.toContinuousLinearMap :=
    boxCoordinates.toContinuousLinearMap.hasFDerivAt.fderiv
  rw [he]
  rfl

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_LocalPhysicalCorrectionBound
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace _root_.OAI.ScalarConductivity.centralMeasure_finite _root_.OAI.ScalarConductivity.instCoeFunSubtypeForallBox3RealMemSubmoduleCentralSmoothFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise

def closedCorrectionBox (a b : Coord3) : Set Coord3 :=
  boxCoordinates ⁻¹' ((Icc (a 0) (b 0) ×ˢ Icc (a 1) (b 1)) ×ˢ Icc (a 2) (b 2))

lemma closedCorrectionBox_compact (a b : Coord3) : IsCompact (closedCorrectionBox a b) := by
  have hc : IsCompact ((Icc (a 0) (b 0) ×ˢ Icc (a 1) (b 1)) ×ˢ Icc (a 2) (b 2)) :=
    (isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc
  convert hc.image boxCoordinates.symm.continuous using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  constructor
  · intro hx
    exact ⟨boxCoordinates x,hx,boxCoordinates.symm_apply_apply x⟩
  · rintro ⟨p,hp,rfl⟩
    simpa only [closedCorrectionBox,mem_preimage,boxCoordinates.apply_symm_apply] using hp

lemma boxCoordinates_symm_norm_le : ‖boxCoordinates.symm.toContinuousLinearMap‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro p
  simp only [one_mul]
  apply pi_norm_le_iff_of_nonneg (norm_nonneg p) |>.mpr
  intro i
  fin_cases i
  · exact (norm_fst_le p.1).trans (norm_fst_le p)
  · exact (norm_snd_le p.1).trans (norm_fst_le p)
  · exact norm_snd_le p

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_SmoothFamilyCorrectionTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

namespace SmoothVanishingPairFamily
omit [FiniteDimensional ℝ P]
variable {p : P} {W V : Set Coord3} {r s : Fin 2 → P×Coord3 → ℝ}
lemma supported (hr : SmoothVanishingPairFamily p W r) (q : P) :
    PairSupported (fun j x => r j (q,x)) W := by
  obtain ⟨_,_,K,_,hKW,hs⟩ := hr
  exact (hs q).mono hKW
end SmoothVanishingPairFamily

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Walls_WallSideMoments
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace _root_.OAI.ScalarConductivity.centralMeasure_finite _root_.OAI.ScalarConductivity.instCoeFunSubtypeForallBox3RealMemSubmoduleCentralSmoothFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Matrix MeasureTheory Filter Topology

lemma boxCoordinates_positive_integral (f : Coord3 → ℝ) :
    (∫ x in {x : Coord3 | 0<x 2},f x)=
      ∫ p in (univ : Set (ℝ×ℝ))×ˢIoi (0:ℝ),f (boxCoordinates.symm p) := by
  let U : Set Box3 := (univ : Set (ℝ×ℝ))×ˢIoi (0:ℝ)
  let S : Set Coord3 := {x | 0<x 2}
  have he : (fun x => U.indicator (fun p => f (boxCoordinates.symm p)) (boxCoordinates x))=S.indicator f := by
    funext x
    by_cases hx : 0<x 2
    · have hU : boxCoordinates x∈U := ⟨mem_univ _,hx⟩
      rw [indicator_of_mem hU,indicator_of_mem (show x∈{x : Coord3 | 0<x 2} from hx),boxCoordinates.symm_apply_apply]
    · have hU : boxCoordinates x∉U := fun hh => hx hh.2
      rw [indicator_of_notMem hU,indicator_of_notMem (show x∉{x : Coord3 | 0<x 2} from hx)]
  have hh := boxCoordinates_integral (U.indicator (fun p => f (boxCoordinates.symm p)))
  rw [he,integral_indicator (isOpen_lt continuous_const (continuous_apply 2)).measurableSet,
    integral_indicator (MeasurableSet.univ.prod measurableSet_Ioi)] at hh
  exact hh

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_ParametricPullback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem exists_parametric_source_pullback
    (Y : OpenPartialHomeomorph (P×Coord3) (P×Coord3))
    (hY : ∀ q x,(Y (q,x)).1=q)
    (hsm : ContDiff ℝ (↑(⊤:ℕ∞)) Y)
    (hinv : ContDiffOn ℝ (↑(⊤:ℕ∞)) Y.symm Y.target)
    (p : P) {V : Set P} {O W K : Set Coord3}
    (hV : IsOpen V) (hp : p∈V) (hVb : Bornology.IsBounded V)
    (hO : IsOpen O) (hOb : Bornology.IsBounded O)
    (hK : IsCompact K) (hKO : K⊆O) (hVO : V×ˢO⊆Y.target)
    (hW : ∀ q∈V,W⊆(fiberSlice Y hY q).symm '' K)
    {r : Fin 2 → P×Coord3 → ℝ} (hr : SmoothVanishingPairFamily p W r) :
    ∃ R : Fin 2 → P×Coord3 → ℝ,SmoothVanishingPairFamily p O R ∧
      ∀ᶠ q in 𝓝 p,(fun j x => R j (q,x))=(fun j => localPiolaSource (fiberSlice Y hY q) (fun x => r j (q,x))) := by
  obtain ⟨χ,hχ,hχc,hχs,_,hχone⟩ := exists_smooth_core_cutoff
    (isCompact_singleton.prod hK) (hV.prod hO) (hVb.prod hOb)
    (prod_mono (singleton_subset_iff.mpr hp) hKO)
  let w : P×Coord3 → ℝ := fun q => inverseSourceWeight (fiberSlice Y hY q.1).symm q.2
  have hw := parametric_inverseSourceWeight_smooth Y hY hsm hinv
  let g (j : Fin 2) : P×Coord3 → ℝ := fun q => w q*r j (q.1,(Y.symm q).2)
  have hg (j) : ContDiffOn ℝ (↑(⊤:ℕ∞)) (g j) Y.target :=
    hw.mul ((hr.1 j).contDiffOn.comp (contDiff_fst.contDiffOn.prodMk
      (contDiff_snd.contDiffOn.comp hinv (fun _ _ => mem_univ _))) (fun _ _ => mem_univ _))
  let R : Fin 2 → P×Coord3 → ℝ := fun j q => χ q*g j q
  have hR (j) : ContDiff ℝ (↑(⊤:ℕ∞)) (R j) :=
    smooth_mul_of_support_in_open Y.open_target (hg j) hχ (hχs.trans hVO)
  have hRq (q : P) (j) : tsupport (fun x => R j (q,x))⊆Prod.snd '' tsupport χ := by
    intro x hx
    have hc : (q,x)∈tsupport χ := (tsupport_comp_subset_preimage χ (continuous_const.prodMk continuous_id))
      (tsupport_mul_subset_left hx)
    exact ⟨(q,x),hc,rfl⟩
  refine ⟨R,⟨hR,fun j x => by simp only [R,g,hr.2.1 j _,mul_zero],
    Prod.snd '' tsupport χ,hχc.image continuous_snd,
    fun x hx => by rcases hx with ⟨z,hz,rfl⟩; exact (hχs hz).2,
    hRq⟩,?_⟩
  have hχnear : ∀ᶠ q in 𝓝 p,∀ x∈K,χ (q,x)=1 := by
    apply hK.eventually_forall_of_forall_eventually
    intro x hx
    exact hχone (p,x) ⟨mem_singleton p,hx⟩
  filter_upwards [hV.mem_nhds hp,hχnear] with q hq hone
  funext j x
  let X := (fiberSlice Y hY q).symm
  have hXs : K⊆X.source := fun y hy => hVO ⟨hq,hKO hy⟩
  have hs : tsupport (fun x => r j (q,x))⊆X '' K := (hr.supported q j).trans (hW q hq)
  have hpr : tsupport (localPiolaSource X.symm (fun x => r j (q,x)))⊆K :=
    localPiolaSource_inverse_support X _ (hr.compact q j).2 hXs hs
  by_cases hx : (q,x)∈Y.target
  · have he : localPiolaSource (fiberSlice Y hY q) (fun y => r j (q,y)) x=g j (q,x) := by
      simp only [localPiolaSource,ite_eq_left (show x∈(fiberSlice Y hY q).target from hx)]
      rfl
    rw [he]
    by_cases hxK : x∈K
    · simp only [R,hone x hxK,one_mul]
    · have hz : g j (q,x)=0 := he.symm.trans (image_eq_zero_of_notMem_tsupport (fun h => hxK (hpr h)))
      simp only [R,hz,mul_zero]
  · have hc : χ (q,x)=0 := image_eq_zero_of_notMem_tsupport (fun hh => hx (hVO (hχs hh)))
    simp only [R,hc,zero_mul,localPiolaSource,ite_eq_right (show x∉(fiberSlice Y hY q).target from hx)]

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_LocalBoundedPiolaCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

theorem physicalSourceMoment_piola_local
    (X : OpenPartialHomeomorph Coord3 Coord3)
    (hX : ContDiffOn ℝ (↑(⊤:ℕ∞)) X X.source)
    (hXi : ContDiffOn ℝ (↑(⊤:ℕ∞)) X.symm X.target)
    {u v : Coord3 → Fin 2 → ℝ} (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u)
    (hv : ContDiff ℝ (↑(⊤:ℕ∞)) v)
    {U : Set Coord3} (hU : U⊆X.source) (hpot : EqOn u (v∘X.symm) (X '' U))
    {r : PhysicalSourcePair} (hr : CompactSmoothPair r) (hs : PairSupported r U) :
    physicalSourceMoment u (fun j => localPiolaSource X (r j))=physicalSourceMoment v r := by
  have hss (j) := (hs j).trans hU
  have hd := hX.differentiableOn (by simp)
  have hdi := hXi.differentiableOn (by simp)
  have hpr : CompactSmoothPair (fun j => localPiolaSource X (r j)) := fun j =>
    ⟨localPiolaSource_smooth X hX hXi (r j) (hr j).1 (hr j).2 (hss j),
      (localPiolaSource_compact X (r j) (hr j).2 (hss j)).1⟩
  have he (j) (φ : Coord3 → ℝ) := localPiolaSource_pairing volume X hd
    (fun _ hx => local_fderiv_det_ne_zero X hd hdi hx) (r j) ((subset_tsupport _).trans (hss j)) φ
  have ht (i j : Fin 2) : (∫ y,u y i*localPiolaSource X (r j) y)=(∫ x,v x i*r j x) := by
    rw [he]
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases hx : x∈U
    · rw [hpot (mem_image_of_mem X hx),Function.comp_apply,X.left_inv (hU hx)]
    · rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hs j h)),mul_zero,mul_zero]
  ext i
  fin_cases i
  · change (∫ y,localPiolaSource X (r 0) y)=(∫ x,r 0 x)
    simpa only [one_mul] using he 0 (fun _ => 1)
  · change (∫ y,localPiolaSource X (r 1) y)=(∫ x,r 1 x)
    simpa only [one_mul] using he 1 (fun _ => 1)
  · change (∫ y,u y 1*localPiolaSource X (r 0) y-u y 0*localPiolaSource X (r 1) y)=
      ∫ x,v x 1*r 0 x-v x 0*r 1 x
    have hi (w : Coord3 → Fin 2 → ℝ) (hw : Continuous w) (s : PhysicalSourcePair)
        (hs : CompactSmoothPair s) (i j : Fin 2) : Integrable (fun x => w x i*s j x) :=
      ((continuous_apply i|>.comp hw).mul (hs j).1.continuous).integrable_of_hasCompactSupport (hs j).2.mul_left
    rw [integral_sub (hi u hu.continuous _ hpr 1 0) (hi u hu.continuous _ hpr 0 1),ht,ht,
      integral_sub (hi v hv.continuous r hr 1 0) (hi v hv.continuous r hr 0 1)]

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_ParametricCorrectionRegionPiola
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

def VanishingCorrectionRegion.piola
    {u v : P×Coord3 → Fin 2 → ℝ}
    (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u) (hv : ContDiff ℝ (↑(⊤:ℕ∞)) v) (p : P)
    (Y : OpenPartialHomeomorph (P×Coord3) (P×Coord3))
    (hY : ∀ q x,(Y (q,x)).1=q)
    (hsm : ContDiff ℝ (↑(⊤:ℕ∞)) Y)
    (hinv : ContDiffOn ℝ (↑(⊤:ℕ∞)) Y.symm Y.target)
    {V : Set P} (hV : IsOpen V) (hp : p∈V) (hVb : Bornology.IsBounded V)
    {A U W K : Set Coord3} (hA : IsOpen A) (B : VanishingCorrectionRegion v p A)
    (hK : IsCompact K) (hKB : K⊆B.region) (hVA : V×ˢA⊆Y.target)
    (hW : ∀ q∈V,W⊆(fiberSlice Y hY q).symm '' K)
    (hWo : IsOpen W) (hWn : W.Nonempty) (hWb : Bornology.IsBounded W) (hWU : W⊆U)
    (himage : ∀ q∈V,(fiberSlice Y hY q).symm '' A⊆U)
    (hpot : ∀ q∈V,∀ y∈A,u (q,(fiberSlice Y hY q).symm y)=v (q,y))
    {C : ℝ} (hC : 0<C)
    (hbound : ∀ q∈V,∀ y∈A,
      let X := (fiberSlice Y hY q).symm
      9*|(fderiv ℝ X y).det|⁻¹*‖operatorMatrix (fderiv ℝ X y)‖*
        ‖operatorMatrix (fderiv ℝ X y)‖≤C) :
    VanishingCorrectionRegion u p U := by
  refine ⟨W,hWo,hWn,hWU,hWb,?_⟩
  intro r hr ε hε
  obtain ⟨R,hR,hRe⟩ := exists_parametric_source_pullback Y hY hsm hinv p hV hp hVb
    B.region_open B.region_bounded hK hKB (fun z hz => hVA ⟨hz.1,B.region_subset hz.2⟩) hW hr
  have hsolve := B.solve R hR (ε/C) (div_pos hε hC)
  filter_upwards [hRe,hsolve,hV.mem_nhds hp] with q he solve hq hm
  let X := (fiberSlice Y hY q).symm
  have hX : ContDiffOn ℝ (↑(⊤:ℕ∞)) X X.source := (fiberSlice_smooth Y hY hsm hinv q).2
  have hXi : ContDiffOn ℝ (↑(⊤:ℕ∞)) X.symm X.target :=
    (fiberSlice_smooth Y hY hsm hinv q).1.contDiffOn
  have hAs : A⊆X.source := fun y hy => hVA ⟨hq,hy⟩
  have huq : ContDiff ℝ (↑(⊤:ℕ∞)) (fun y => u (q,y)) := hu.comp (contDiff_const.prodMk contDiff_id)
  have hvq : ContDiff ℝ (↑(⊤:ℕ∞)) (fun y => v (q,y)) := hv.comp (contDiff_const.prodMk contDiff_id)
  have hps : EqOn (fun y => u (q,y)) ((fun y => v (q,y))∘X.symm) (X '' A) := by
    rintro _ ⟨y,hy,rfl⟩
    change u (q,X y)=v (q,X.symm (X y))
    rw [X.left_inv (hAs hy)]
    exact hpot q hq y hy
  have hrX (j) : tsupport (fun y => r j (q,y))⊆X.target :=
    (hr.supported q j).trans ((hW q hq).trans (by
      rintro _ ⟨y,hy,rfl⟩
      exact X.map_source (hAs (B.region_subset (hKB hy)))))
  have hre : (fun j => localPiolaSource X (fun y => R j (q,y)))=(fun j y => r j (q,y)) := by
    funext j
    rw [congrFun he j]
    exact localPiolaSource_inverse X (hX.differentiableOn (by simp))
      (hXi.differentiableOn (by simp)) _ ((subset_tsupport _).trans (hrX j))
  have hRs : PairSupported (fun j y => R j (q,y)) A := (hR.supported q).mono B.region_subset
  have hRm : physicalSourceMoment (fun y => v (q,y)) (fun j y => R j (q,y))=0 := by
    have hh := physicalSourceMoment_piola_local X hX hXi huq hvq hAs hps (hR.compact q) hRs
    rw [hre,hm] at hh
    exact hh.symm
  have hh := (solve hRm).piola_local X hX hXi huq hvq hA hAs hps hC.le
    (hbound q hq) (hR.compact q) hRs
  rw [hre,mul_div_cancel₀ ε hC.ne'] at hh
  exact hh.region_mono (himage q hq)

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_TorusAffineField
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix UnitAddTorus

def torusAffineField (s : Fin 3 → ℝ) (κ : ℝ) (f : TorusL2) (x : Coord3) : ℝ :=
  κ*x 0+torusRealContinuation s f x

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_FieldVectorCLM
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set
namespace ScalarConductivity
open Matrix Set MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise ENNReal

lemma voltageGradient_add {u v : Coord3 → Fin 2 → ℝ} {x : Coord3}
    (hu : DifferentiableAt ℝ u x) (hv : DifferentiableAt ℝ v x) :
    voltageGradient (fun y => u y+v y) x = voltageGradient u x+voltageGradient v x := by
  change gradientVectorCLM (fderiv ℝ (u+v) x) = _
  rw [fderiv_add hu hv,map_add]
  rfl

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_VoltageFluxConstraints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open MeasureTheory Set Filter Topology Matrix
open scoped ENNReal Matrix.Norms.Elementwise

def smoothVoltageGradients (μ : Measure Coord3) (U : Set Coord3) :
    Set (Lp FieldVector 2 (μ.restrict U)) :=
  {z | ∃ (v : Coord3 → Fin 2 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) v ∧
    ∃ (hg : MemLp (voltageGradient v) 2 (μ.restrict U)), z = hg.toLp _}

def allVoltageGradients (μ : Measure Coord3) (U : Set Coord3) :
    Submodule ℝ (Lp FieldVector 2 (μ.restrict U)) :=
  (Submodule.span ℝ (smoothVoltageGradients μ U)).topologicalClosure

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_VoltageJetCompletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

def compactVoltageJets (μ : Measure Coord3) (U : Set Coord3) : Set (VoltageJetSpace μ U) :=
  {z | ∃ (v : Coord3 → Fin 2 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) v ∧
    HasCompactSupport v ∧ tsupport v ⊆ U ∧
    ∃ (hm : MemLp v 2 (μ.restrict U)) (hg : MemLp (voltageGradient v) 2 (μ.restrict U)),
      z = (hm.toLp _,hg.toLp _)}

lemma compactVoltageJets_add (μ : Measure Coord3) (U : Set Coord3)
    {z w : VoltageJetSpace μ U} (hz : z ∈ compactVoltageJets μ U)
    (hw : w ∈ compactVoltageJets μ U) : z+w ∈ compactVoltageJets μ U := by
  obtain ⟨v,hv,hvc,hvs,hvm,hvg,rfl⟩ := hz
  obtain ⟨f,hf,hfc,hfs,hfm,hfg,rfl⟩ := hw
  have he : voltageGradient (v+f) = voltageGradient v+voltageGradient f :=
    funext fun x => voltageGradient_add (hv.differentiable (by simp) x) (hf.differentiable (by simp) x)
  have hmg : MemLp (voltageGradient (v+f)) 2 (μ.restrict U) := by rw [he]; exact hvg.add hfg
  refine ⟨v+f,hv.add hf,hvc.add hfc,(tsupport_add v f).trans (union_subset hvs hfs),
    hvm.add hfm,hmg,?_⟩
  apply Prod.ext
  · exact (MemLp.toLp_add hvm hfm).symm
  · change hvg.toLp _ + hfg.toLp _ = hmg.toLp _
    rw [← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (Eventually.of_forall fun x => congrFun he x |>.symm)

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_CentralDistributionLaplacian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

def centralSmoothPartial (f : centralSmoothFunctions) (i : Fin 3) : centralSmoothFunctions :=
  ⟨cubePartial f (centralDirection i),cubePartial_smooth (central_smooth f) _⟩

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_BranchFiniteEnding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix UnitAddTorus
open scoped Matrix.Norms.Elementwise

variable {s : Fin 3 → ℝ} {f : Fin 2 → TorusL2} (i : Fin 3)
  (z : TorusEndingData s (branchNormalize i f))

def branchCorrection (j : Fin 2) : Coord3 → ℝ :=
  torusEndingCorrection z.d z.e (fun x => (branchFinitePair i z).v x j)
    (torusAffineField s (centralBasisSlopes j i) (f j))

def branchFluxCorrection (j : Fin 2) : Coord3 → Coord3 :=
  torusEndingFluxCorrection z.d z.e (fun x => ((branchFinitePair i z).G x).col j)
    (flatModeFlux s (torusAffineField s (centralBasisSlopes j i) (f j)))

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_FlatEndingSplice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix UnitAddTorus
open scoped Matrix.Norms.Elementwise

variable {s : Fin 3 → ℝ} {f : Fin 2 → TorusL2} (i : Fin 3)
  (z : TorusEndingData s (branchNormalize i f))

def branchSplicedField (j : Fin 2) (x : Coord3) : ℝ :=
  torusAffineField s (centralBasisSlopes j i) (f j) x+branchCorrection i z j x

def branchSplicedFlux (j : Fin 2) (x : Coord3) : Coord3 :=
  flatModeFlux s (torusAffineField s (centralBasisSlopes j i) (f j)) x+
    branchFluxCorrection i z j x

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_PhysicalEndRegions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma physicalChildEnd_far_parent (k : Fin 2) {y : Fin 3 → ℝ}
    (hy : y∈sourceClosedCollarBand (-centralThickness) 0) :
    2*centralThickness ≤ sourceCollarTime (sourceChildCoordinates (actualChildSign k) y) := by
  obtain ⟨h₀,h₁,h₂⟩ := sourceSmallBand_bounds hy
  have hsign : |actualChildSign k|=1 := by fin_cases k <;> norm_num [actualChildSign]
  have ha : |actualChildSign k*sourceOffset|=sourceOffset := by
    rw [abs_mul,hsign,one_mul]; norm_num [sourceOffset]
  have hu := abs_add_le (sourceScale*y 1) (actualChildSign k*sourceOffset)
  rw [abs_mul,abs_of_pos (show 0 < sourceScale by norm_num [sourceScale]),ha] at hu
  have hl := abs_add_le (-sourceScale*y 1) (sourceScale*y 1+actualChildSign k*sourceOffset)
  have he : -sourceScale*y 1+(sourceScale*y 1+actualChildSign k*sourceOffset)=
    actualChildSign k*sourceOffset := by ring
  rw [he,ha,abs_mul,abs_neg,abs_of_pos (show 0 < sourceScale by norm_num [sourceScale])] at hl
  apply (sourceCollarTime_ge_iff _ _).mpr
  change |sourceScale*y 2|≤_ ∧ _≤ max (|sourceScale*y 1+actualChildSign k*sourceOffset|/sourceLength)
    (|sourceScale*y 0|) ∧ max (|sourceScale*y 1+actualChildSign k*sourceOffset|/sourceLength)
      (|sourceScale*y 0|)≤_
  simp only [abs_mul,abs_of_pos (show 0 < sourceScale by norm_num [sourceScale])]
  constructor
  · norm_num [sourceScale,centralThickness]; linarith
  · constructor
    · apply le_trans _ (le_max_left _ _)
      norm_num [sourceHole,sourceRadialWidth,sourceLength,sourceScale,sourceOffset,centralThickness] at *
      linarith
    · apply max_le
      · norm_num [sourceHole,sourceRadialWidth,sourceLength,sourceScale,sourceOffset,centralThickness] at *
        linarith
      · norm_num [sourceHole,sourceRadialWidth,sourceLength,sourceScale,sourceOffset,centralThickness] at *
        linarith

lemma physicalEndRegion_parent_child_disjoint (k : Fin 2) :
    Disjoint (physicalEndRegion 0) (physicalEndRegion k.succ) := by
  apply disjoint_left.mpr
  intro y hp hc
  have hh := physicalChildEnd_far_parent k hc
  have he : sourceChildCoordinates (actualChildSign k)
      ((sourceChildHomeomorph (actualChildSign k)).symm y)=y :=
    (sourceChildHomeomorph (actualChildSign k)).apply_symm_apply y
  rw [he] at hh
  change sourceCollarTime y∈Icc 0 centralThickness at hp
  norm_num [centralThickness] at hp hh
  linarith [hp.2]

lemma physicalEndRegion_pairwise_disjoint : Pairwise (fun i j => Disjoint (physicalEndRegion i) (physicalEndRegion j)) := by
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals first | exact (hij rfl).elim | exact physicalEndRegion_parent_child_disjoint 0 |
    exact physicalEndRegion_parent_child_disjoint 1 |
    exact (physicalEndRegion_parent_child_disjoint 0).symm |
    exact (physicalEndRegion_parent_child_disjoint 1).symm |
    exact physicalEndRegion_children_disjoint | exact physicalEndRegion_children_disjoint.symm

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_PhysicalCollarRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

def variableFaceField (u : Coord3 → Fin 2 → ℝ) (a b : ℝ) (i j : Fin 4) : Coord3 → Fin 2 → ℝ :=
  fun y => u (flatEndCoordinates a b (sourceFaceAngles i j (sourceCollarInverse i j y)))

def variableCollarField (u : Coord3 → Fin 2 → ℝ) (a b : ℝ) : Coord3 → Fin 2 → ℝ :=
  sourceFacePaste (variableFaceField u a b) 0

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_FiniteEndPhysicalH1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix

def attachedPeriodicField (f : Coord3 → ℝ) (a b : ℝ) : Coord3 → ℝ :=
  physicalPeriodicField (fun x => f (flatEndCoordinates a b x))

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_PhysicalRankTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory

def periodicCorrectionJet (f : Coord3 → ℝ) (a : ℝ) (i : Fin 3) (x : R3) : JetFiber :=
  Fin.cases
    (physicalJet (attachedPeriodicField f a centralThickness (WithLp.ofLp x))
      (fun j => lineDeriv ℝ (attachedPeriodicField f a centralThickness)
        (WithLp.ofLp x) (Pi.single j 1)))
    (fun k => physicalJet
      (attachedPeriodicField f a (-centralThickness)
        ((sourceChildHomeomorph (actualChildSign k)).symm (WithLp.ofLp x)))
      (fun j => sourceScale⁻¹*lineDeriv ℝ (attachedPeriodicField f a (-centralThickness))
        ((sourceChildHomeomorph (actualChildSign k)).symm (WithLp.ofLp x))
        (Pi.single (childAxis j) 1))) i

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_CompletePhysicalAttachment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

def attachedPhysicalJet (s a κ : Fin 3 → ℝ) (p : centralEnergySpace s)
    (i : Fin 3) (x : R3) : JetFiber :=
  Fin.cases
    (physicalJet (fullAttachedEndValue s (centralT s 0 p) (a 0) centralThickness
      (κ 0) (WithLp.ofLp x))
      (fullAttachedEndGradient s (centralT s 0 p) (a 0) centralThickness
        (κ 0) (WithLp.ofLp x)))
    (fun k => physicalJet
      (fullAttachedEndValue s (centralT s k.succ p) (a k.succ) (-centralThickness)
        (κ k.succ) ((sourceChildHomeomorph (actualChildSign k)).symm (WithLp.ofLp x)))
      (fun j => sourceScale⁻¹*fullAttachedEndGradient s (centralT s k.succ p)
        (a k.succ) (-centralThickness) (κ k.succ)
        ((sourceChildHomeomorph (actualChildSign k)).symm (WithLp.ofLp x)) (childAxis j))) i

end ScalarConductivity
end

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_PhysicalFiniteEndingData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix UnitAddTorus

namespace PhysicalFiniteEndingData
variable {s : Fin 3 → ℝ} (z : PhysicalFiniteEndingData s)

def traces (i : Fin 3) (j : Fin 2) : TorusL2 := torusSpectralSynthesis s (centralT s i (z.p j))

def correctedEndJet (j : Fin 2) (i : Fin 3) (x : R3) : JetFiber :=
  attachedPhysicalJet s z.compression (centralBasisSlopes j) (z.p j) i x+
    periodicCorrectionJet (branchCorrection i (z.ending i) j) (z.compression i) i x

end PhysicalFiniteEndingData
end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_VariableBlockTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise ENNReal

lemma variableBlockTensor_local_list (K : Fin 3 → Coord3 → Mat3) (a : Fin 3 → ℝ) (is : List (Fin 3))
    (i : Fin 3) (hi : i∈is) {y : Fin 3 → ℝ} (hy : y∈physicalEndRegion i) :
    variableBlockTensorList K a is y=variableEndTensor K a i y := by
  classical
  induction is with
  | nil => simp at hi
  | cons j is ih =>
    rw [variableBlockTensorList_cons]
    by_cases he : j=i
    · subst j; simp only [ite_eq_left hy]
    · have hn : y∉physicalEndRegion j := fun hj =>
        (disjoint_left.mp (physicalEndRegion_pairwise_disjoint he) hj hy)
      rw [ite_eq_right hn]
      exact ih ((List.mem_cons.mp hi).resolve_left (Ne.symm he))

lemma variableBlockTensor_local (K : Fin 3 → Coord3 → Mat3) (a : Fin 3 → ℝ) (i : Fin 3)
    {y : Fin 3 → ℝ} (hy : y∈physicalEndRegion i) :
    variableBlockTensor K a y=variableEndTensor K a i y :=
  variableBlockTensor_local_list K a _ i (by simp) hy

attribute [local instance] OAI.ScalarConductivity.variableBlockTensorMeasurableSpace
attribute [local instance] OAI.ScalarConductivity.variableBlockTensorBorelSpace
theorem variableBlockTensor_properties (K : Fin 3 → Coord3 → Mat3) (a : Fin 3 → ℝ)
    (hK : ∀ i,Measurable (K i) ∧ (∀ x,(K i x).IsSymm) ∧
      ∃ c C : ℝ,0 < c ∧ c≤C ∧ ∀ x v,c*(v ⬝ᵥ v)≤v ⬝ᵥ(K i x*ᵥv) ∧ v ⬝ᵥ(K i x*ᵥv)≤C*(v ⬝ᵥ v))
    (ha : ∀ i,a i≠0) :
    Measurable (variableBlockTensor K a) ∧
      MemLp (variableBlockTensor K a) ∞ (volume : Measure (Fin 3 → ℝ)) ∧
      (∀ y,(variableBlockTensor K a y).IsSymm) ∧
      (∃ c C : ℝ,0 < c ∧ c<C ∧ ∀ y (v : Fin 3 → ℝ),
        c*‖v‖^2 ≤ v ⬝ᵥ (variableBlockTensor K a y*ᵥv) ∧
          v ⬝ᵥ (variableBlockTensor K a y*ᵥv) ≤ C*‖v‖^2) ∧
      (∀ i y,y∈physicalEndRegion i → variableBlockTensor K a y=variableEndTensor K a i y) ∧
      (∀ y,(∀ i,y∉physicalEndRegion i) → variableBlockTensor K a y=1) := by
  let : TopologicalSpace.PseudoMetrizableSpace (Matrix (Fin 3) (Fin 3) ℝ) :=
    inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin 3 → Fin 3 → ℝ))
  let : SecondCountableTopology (Matrix (Fin 3) (Fin 3) ℝ) :=
    inferInstanceAs (SecondCountableTopology (Fin 3 → Fin 3 → ℝ))
  have h := variableBlockTensorList_properties K a hK ha
    (Finset.univ : Finset (Fin 3)).toList
  obtain ⟨B,hB,hbound⟩ := h.2.2.2
  exact ⟨h.1,memLp_top_of_bound h.1.aestronglyMeasurable B (ae_of_all _ hbound),
    h.2.1,h.2.2.1,fun i y hy => variableBlockTensor_local K a i hy,
    fun y hy => variableBlockTensorList_outside K a _ (fun i _ => hy i)⟩

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_AttachedPeriodicFlux
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory UnitAddTorus Matrix
open scoped ENNReal

def attachedPeriodicFluxFace (F : Coord3 → Coord3) (a b : ℝ) (i j : Fin 4)
    (y : Coord3) : Coord3 :=
  let x := sourceCollarInverse i j y
  (|a| *sourceFlatDensity i j x) • ((attachedCartesianMatrix a i j x)⁻¹ᵀ*ᵥ
    F (flatEndCoordinates a b (sourceFaceAngles i j x)))

def attachedPeriodicFlux (F : Coord3 → Coord3) (a b : ℝ) : Coord3 → Coord3 :=
  sourceFacePaste (attachedPeriodicFluxFace F a b) 0

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_CentralCorrectedRepresentative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise

namespace PhysicalFiniteEndingData
variable {s : Fin 3 → ℝ} (z : PhysicalFiniteEndingData s)

def endRepresentative (i : Fin 3) : Coord3 → Fin 2 → ℝ :=
  Fin.cases (variableCollarField (fun y j => branchSplicedField 0 (z.ending 0) j y)
    (z.compression 0) centralThickness)
    (fun k => fun y => variableCollarField (fun y j => branchSplicedField k.succ (z.ending k.succ) j y)
      (z.compression k.succ) (-centralThickness) ((sourceChildHomeomorph (actualChildSign k)).symm y)) i

end PhysicalFiniteEndingData
end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_PhysicalBlockRepresentative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise

namespace PhysicalFiniteEndingData
variable {s : Fin 3 → ℝ} (z : PhysicalFiniteEndingData s)

local instance physicalBlockRepresentativeMeasurableSpace_r070ee7_1 : MeasurableSpace Mat3 := inferInstanceAs (MeasurableSpace (Fin 3 → Fin 3 → ℝ))
def cartesianTensor
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (y : Coord3) : Symmetric3 :=
  ⟨variableBlockTensor z.flatTensor z.compression y,
    (variableBlockTensor_properties z.flatTensor z.compression (z.flatTensor_properties hs) z.compression_ne).2.2.1 y⟩

end PhysicalFiniteEndingData
end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_ChildH1Pullback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology
attribute [local instance] Classical.propDecidable

def childPullbackComponentCLM (k : Fin 2) (i : Fin 4) : JetSpace →L[ℝ] Lp ℝ 2 (volume : Measure Coord3) :=
  Fin.cases ((sourceChildPullbackCLM (actualChildSign k)).comp (ballWholePiComponentCLM 0))
    (fun j => sourceScale • ((sourceChildPullbackCLM (actualChildSign k)).comp
      (ballWholePiComponentCLM (childAxis j).succ))) i

def childPullbackJetCLM (k : Fin 2) : JetSpace →L[ℝ] JetSpace :=
  physicalFourJetCLM.comp (ContinuousLinearMap.pi (childPullbackComponentCLM k))

lemma childPullbackComponentCLM_ae (k : Fin 2) (z : JetSpace) (i : Fin 4) :
    childPullbackComponentCLM k i z=ᵐ[volume] fun y => Fin.cases
      (if WithLp.toLp 2 (sourceChildCoordinates (actualChildSign k) y)∈ball then
        z (WithLp.toLp 2 (sourceChildCoordinates (actualChildSign k) y)) 0 else 0)
      (fun j => sourceScale*(if WithLp.toLp 2 (sourceChildCoordinates (actualChildSign k) y)∈ball then
        z (WithLp.toLp 2 (sourceChildCoordinates (actualChildSign k) y)) (childAxis j).succ else 0)) i := by
  have he (i : Fin 4) := ballWholePiComponentCLM_ae_of_ae i z
    (fun y => z (WithLp.toLp 2 y)) (by filter_upwards [] with x; rfl)
  have hp (i : Fin 4) := (sourceChildPullbackCLM_ae (actualChildSign k) (ballWholePiComponentCLM i z)).trans
    ((sourceChildCoordinates_quasi _).ae_eq_comp (he i))
  refine Fin.cases (hp 0) (fun j => ?_) i
  apply (Lp.coeFn_smul _ _).trans
  filter_upwards [hp (childAxis j).succ] with y hy
  exact congrArg (fun t : ℝ => sourceScale*t) hy

lemma childPullbackJetCLM_ae (k : Fin 2) (z : JetSpace) :
    childPullbackJetCLM k z=ᵐ[ballMeasure] fun x => WithLp.toLp 2 (Fin.cases
      (z (sourceChildEuclidean (actualChildSign k) x) 0)
      (fun j => sourceScale*z (sourceChildEuclidean (actualChildSign k) x) (childAxis j).succ)) := by
  have hi (i : Fin 4) := ae_restrict_of_ae (s:=ball) ((PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae_eq_comp
    (childPullbackComponentCLM_ae k z i))
  filter_upwards [physicalFourJetCLM_ae (fun i => childPullbackComponentCLM k i z),ae_all_iff.mpr hi,
    ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx hi hxb
  change physicalFourJetCLM (fun i => childPullbackComponentCLM k i z) x=_
  rw [hx]
  have hb : sourceChildEuclidean (actualChildSign k) x∈ball := sourceChildEuclidean_ball k ⟨x,hxb,rfl⟩
  ext i
  have hh := hi i
  change childPullbackComponentCLM k i z (WithLp.ofLp x)=Fin.cases
    (if sourceChildEuclidean (actualChildSign k) x∈ball then z (sourceChildEuclidean (actualChildSign k) x) 0 else 0)
    (fun j => sourceScale*(if sourceChildEuclidean (actualChildSign k) x∈ball then
      z (sourceChildEuclidean (actualChildSign k) x) (childAxis j).succ else 0)) i at hh
  simpa only [ite_eq_left hb] using hh

lemma sourceChildEuclidean_quasi (σ : ℝ) :
    Measure.QuasiMeasurePreserving (sourceChildEuclidean σ) volume volume :=
  (PiLp.volume_preserving_toLp (Fin 3)).quasiMeasurePreserving.comp
    ((sourceChildCoordinates_quasi σ).comp (PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving)

lemma sourceChildEuclidean_ball_quasi (k : Fin 2) :
    Measure.QuasiMeasurePreserving (sourceChildEuclidean (actualChildSign k)) ballMeasure ballMeasure := by
  exact (sourceChildEuclidean_quasi _).restrict fun x hx => sourceChildEuclidean_ball k ⟨x,hx,rfl⟩

lemma childPullbackJetCLM_smooth (k : Fin 2) (f : R3 → ℝ) (hf : ContDiff ℝ (↑(⊤:ℕ∞)) f) :
    childPullbackJetCLM k (smoothH1 f hf).val=
      (smoothH1 (f ∘ sourceChildEuclidean (actualChildSign k)) (hf.comp (sourceChildEuclidean_contDiff _))).val := by
  apply Lp.ext
  have hh := (sourceChildEuclidean_ball_quasi k).ae_eq_comp (smoothJet_memLp hf).coeFn_toLp
  filter_upwards [childPullbackJetCLM_ae k (smoothH1 f hf).val,hh,
    (smoothJet_memLp (hf.comp (sourceChildEuclidean_contDiff (actualChildSign k)))).coeFn_toLp] with x hx hh hg
  change (smoothH1 (f ∘ sourceChildEuclidean (actualChildSign k)) (hf.comp (sourceChildEuclidean_contDiff _))).val x=_ at hg
  rw [hx,hg]
  ext i
  cases i using Fin.cases with
  | zero =>
    change (smoothH1 f hf).val (sourceChildEuclidean (actualChildSign k) x) 0=f (sourceChildEuclidean (actualChildSign k) x)
    exact congrArg (fun v : JetFiber => v 0) hh
  | succ j =>
    change sourceScale*(smoothH1 f hf).val (sourceChildEuclidean (actualChildSign k) x) (childAxis j).succ=_
    change (smoothH1 f hf).val (sourceChildEuclidean (actualChildSign k) x)=_ at hh
    rw [hh]
    exact (sourceChildEuclidean_gradient _ hf x j).symm

lemma childPullbackJetCLM_H1 (k : Fin 2) {z : JetSpace} (hz : z∈H1Space) :
    childPullbackJetCLM k z∈H1Space := by
  let T := H1Space.comap (childPullbackJetCLM k).toLinearMap
  have ht : IsClosed (T : Set JetSpace) := H1_isClosed.preimage (childPullbackJetCLM k).continuous
  have hs : Submodule.span ℝ smoothJets≤T := by
    apply Submodule.span_le.mpr
    rintro z ⟨f,hf,hm,rfl⟩
    have he : hm.toLp (smoothJet f)=(smoothH1 f hf).val := by
      apply Lp.ext; exact hm.coeFn_toLp.trans (smoothJet_memLp hf).coeFn_toLp.symm
    change childPullbackJetCLM k (hm.toLp (smoothJet f))∈H1Space
    rw [he,childPullbackJetCLM_smooth k f hf]
    exact (smoothH1 _ _).property
  exact (Submodule.topologicalClosure_minimal _ hs ht) hz

def childH1Pullback (k : Fin 2) : H1 →L[ℝ] H1 :=
  ((childPullbackJetCLM k).comp H1Space.subtypeL).codRestrict H1Space
    (fun u => childPullbackJetCLM_H1 k u.property)

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_PhysicalTerminalBands
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix UnitAddTorus

namespace PhysicalFiniteEndingData
variable {s : Fin 3 → ℝ} (z : PhysicalFiniteEndingData s)

def terminalValue (i : Fin 3) (j : Fin 2) : ℝ :=
  centralBasisSlopes j i*((z.ending i).R+1)+(mFourierCoeff (z.traces i j) 0).re

end PhysicalFiniteEndingData
end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_OriginalSmoothMultiplier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix UnitAddTorus

namespace PhysicalFiniteEndingData
variable {s : Fin 3 → ℝ} (z : PhysicalFiniteEndingData s)

def terminalProfileParent (η : ℝ) (j : Fin 2) (y : Coord3) : ℝ :=
  centralBasisSlopes j 0*z.compression 0*max (terminalTime 0 y) 0*
    (1-Real.smoothTransition (terminalTime 0 y/η-1))

def terminalProfileChild (η : ℝ) (j : Fin 2) (k : Fin 2) (y : Coord3) : ℝ :=
  (z.terminalValue k.succ j-z.terminalValue 0 j+
    centralBasisSlopes j k.succ*z.compression k.succ*min (terminalTime k.succ y) 0)*
    Real.smoothTransition (terminalTime k.succ y/η+2)

def terminalProfile (η : ℝ) (j : Fin 2) (y : Coord3) : ℝ :=
  z.terminalProfileParent η j y+∑ k : Fin 2,z.terminalProfileChild η j k y

end PhysicalFiniteEndingData
end ScalarConductivity

end
end

end OAI
end


