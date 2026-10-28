-- Prove2me | Definitions.Def_OAIQ059C007
-- name    : OAIQ059C007
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T21:43:41.336726+00:00
-- url     : https://prove2.me/theorems/4babeb5c-1a05-4053-86c5-d10d7c5fcd1f
-- title:
--   Definitions bundle OAIQ059C007 of the split of OpenAI, Nonuniqueness for bounded measurable scalar conductivities in three dimensions (result family 365)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ScalarConductivity.main_nonuniqueness`, carved from OpenAI's openai/math development (OpenAI, *Nonuniqueness for bounded measurable scalar conductivities in three dimensions (result family 365)*, OpenAI Math Release, September 23, 2026, result family 365, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 155 declarations of OpenAI's Lean: 69 definitions, 1 instance and 85 theorems. The definitions and types are `OAI.ScalarConductivity.coordDyadicBump`, `OAI.ScalarConductivity.coordMollify`, `OAI.ScalarConductivity.crossingPotential`, `OAI.ScalarConductivity.cylinderFluxLp`, `OAI.ScalarConductivity.cylinderFluxPairL`, `OAI.ScalarConductivity.cylinderFourierEquiv`, `OAI.ScalarConductivity.cylinderJetMode`, `OAI.ScalarConductivity.cylinderPolynomialGraphL`, `OAI.ScalarConductivity.cylinderPolynomialJetL`, `OAI.ScalarConductivity.cylinderSlopeJet`, `OAI.ScalarConductivity.cylinderSobolevGraph`, `OAI.ScalarConductivity.cylinderTerminalFlux`, `OAI.ScalarConductivity.delayedEndingPotential`, `OAI.ScalarConductivity.delayedEndingSymmetricTensor`, `OAI.ScalarConductivity.delayedEndingTensor`, `OAI.ScalarConductivity.delayedEndingValue`, `OAI.ScalarConductivity.delayedPairFlux`, `OAI.ScalarConductivity.endingJoinMiddleTensor`, `OAI.ScalarConductivity.endingJoinSymmetricTensor`, `OAI.ScalarConductivity.endingJoinTensor`, `OAI.ScalarConductivity.finiteEndingSymmetricTensor`, `OAI.ScalarConductivity.finiteUpdatePairs`, `OAI.ScalarConductivity.flatCrossFlux`, `OAI.ScalarConductivity.flatSmoothMode`, `OAI.ScalarConductivity.fourierMatchingPair`, `OAI.ScalarConductivity.fourierMatchingResidual`, `OAI.ScalarConductivity.fullEndFlatCovector`, `OAI.ScalarConductivity.gradientCoordinateConstant`, `OAI.ScalarConductivity.joinedFlux`, `OAI.ScalarConductivity.localizedTwoFlux`, `OAI.ScalarConductivity.matchedEndingPair`, `OAI.ScalarConductivity.originalMulH1CLM`, `OAI.ScalarConductivity.originalPairVoltageJet`, `OAI.ScalarConductivity.originalVoltageJetCLM`, `OAI.ScalarConductivity.physicalBlockRegion`, `OAI.ScalarConductivity.physicalComplexTraceCLM`, `OAI.ScalarConductivity.physicalRealTraceCLM`, `OAI.ScalarConductivity.physicalSmoothOuterTrace`, `OAI.ScalarConductivity.physicalTerminalFluxCLM`, `OAI.ScalarConductivity.smoothCylinderModeJet` and 29 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `Conductivity_Branching_AlignedEndingRegularity`, `Conductivity_Branching_DelayedEndingRegularity`, `Conductivity_Branching_EndingJoinElliptic`, `Conductivity_Branching_FiniteEndingRegularity`, `Conductivity_Branching_MatchedEndingRegularity`, `Conductivity_Branching_MeasurableDisjointGluing`, `Conductivity_Branching_PhysicalBlockEnergy`, `Conductivity_Branching_PhysicalTraceTransport`, `Conductivity_Flux_AttachedPhysicalSmoothGreen`, `Conductivity_Flux_AxialFluxBlend`, `Conductivity_Flux_CubeWeakDivergence`, `Conductivity_Flux_CylinderCompletedGreen`, `Conductivity_Flux_CylinderSlopeGreen`, `Conductivity_Flux_DelayedPairFlux`, `Conductivity_Flux_LocalizedTwoFlux`, `Conductivity_Flux_PhysicalAttachedGreen`, `Conductivity_Flux_PotentialCurl`, `Conductivity_Flux_TorusCylinderGreenReal`, `Conductivity_Flux_TorusFluxDecay`, `Conductivity_Fourier_AngularInverseTensor`, `Conductivity_Fourier_CylinderFourierComplete`, `Conductivity_Fourier_CylinderModeGreen`, `Conductivity_Fourier_EndingJoinMiddleModel`, `Conductivity_Fourier_FourierMatchingInterpolation`, `Conductivity_Fourier_TorusSmoothModeJet`, `Conductivity_Geometry_CylinderJetOrthogonal`, `Conductivity_Geometry_CylinderPolynomial`, `Conductivity_Geometry_ParametricPotentialCoordinates`, `Conductivity_Geometry_RegularPotentialCoordinates`, `Conductivity_Geometry_TorusDirectionalDerivative`, `Conductivity_Scalarization_DenseClosureApprox`, `Conductivity_Scalarization_EndingJoinConstitution`, `Conductivity_Sobolev_CylinderSobolevGraph`, `Conductivity_Sobolev_OriginalMultiplierOperator`, `Conductivity_Sobolev_OriginalPairVoltage`, `Conductivity_Sobolev_OriginalSmoothMultiplier`, `Conductivity_Sobolev_ParentFullEndH1`, `Conductivity_Sobolev_SobolevChain`, `Conductivity_Sobolev_VoltageH1Completion`, `Conductivity_Sobolev_VoltageJetCompletion`, `Conductivity_Sobolev_VoltageOriginalH10`, `Conductivity_Sobolev_WallParticular`, `Conductivity_Sobolev_WallParticularFamily`, `Conductivity_Sobolev_WallParticularFinish`, `Conductivity_Sources_AngularCoefficient`, `Conductivity_Sources_AngularJet`, `Conductivity_Sources_BranchCombine`, `Conductivity_Sources_EndPointEnergy`, `Conductivity_Sources_FluxCylinder`, `Conductivity_Sources_ParametricSymmetricSources`, `Conductivity_Sources_PhysicalC1Pullback`, `Conductivity_Sources_SymmetricCutoffSources`, `Conductivity_Sources_WordTrace`, `Conductivity_Variational_C1VoltageApproximation`, `Conductivity_Variational_CompactRegularC0`, `Conductivity_Variational_CompactRegularCorrection`, `Conductivity_Variational_MetricControlledPiola`, `Conductivity_Variational_OriginalVoltageRestriction`, `Conductivity_Variational_ParametricMomentSmall`, `Conductivity_Variational_ParametricSpatialDerivative`, `Conductivity_Variational_PhysicalOpenVoltage`, `Conductivity_Variational_PhysicalRealTrace`, `Conductivity_Variational_VoltageBoundaryTrace`, `Conductivity_Variational_VoltagePoincare`, `Conductivity_Walls_CriticalWall`, `Conductivity_Walls_CriticalWallHomogeneous`, `Conductivity_Walls_CriticalWallResidual`, `Conductivity_Walls_CriticalWallTensor`, `Conductivity_Walls_EndingJoinCutoff`, `Conductivity_Walls_ParametricWallAmplitude`, `Conductivity_Walls_ParametricWallOperators`, `Conductivity_Walls_ParametricWallTensors`, `Conductivity_Walls_WallHalfspaceIntegral`, `Conductivity_Walls_WallSideMoments`, `Conductivity_Walls_WallTransferParametric`, `Conductivity_Walls_WallVanishingMomentCoefficients`.
--
--   **Imports.** It imports the published bundle `Def_Conductivity`; the bundles `OAIQ059C003`, `OAIQ059C004` and `OAIQ059C005` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ059C008`; the statements `OAI.ScalarConductivity.PhysicalFiniteEndingData.corrected_block_smooth_green`, `OAI.ScalarConductivity.PhysicalFiniteEndingData.corrected_pair_representative`, `OAI.ScalarConductivity.endingJoin_constitution_ae`, `OAI.ScalarConductivity.fourierMatchingFamily_correction`, `OAI.ScalarConductivity.fullAttachedEnd_smooth_green_neg`, `OAI.ScalarConductivity.fullAttachedEnd_smooth_green_pos`, `OAI.ScalarConductivity.matchedEnding_regularRegion_ae` and `OAI.ScalarConductivity.matchedEnding_weak_equation`; the proofs of `OAI.ScalarConductivity.PhysicalFiniteEndingData.corrected_pair_representative`, `OAI.ScalarConductivity.attachedPeriodicFlux_smooth_green`, `OAI.ScalarConductivity.endingJoin_constitution_ae`, `OAI.ScalarConductivity.exists_local_split_on_subpatch_retained`, `OAI.ScalarConductivity.fine_global_scalar_tensor_approximation`, `OAI.ScalarConductivity.matchedEnding_weak_equation` and `OAI.ScalarConductivity.physicalFiniteEndingData_nonempty`.
-- source:
--   OpenAI, Nonuniqueness for bounded measurable scalar conductivities in three dimensions (result family 365), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 365; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-for-Bounded-Measurable-Scalar-Conductivities-in-Three-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_Conductivity
import Definitions.Def_OAIQ059C003
import Definitions.Def_OAIQ059C004
import Definitions.Def_OAIQ059C005

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_LocalizedTwoFlux
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ScalarConductivity
open Filter Topology

def localizedTwoFlux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : Fin 3 → E) (χ : SmoothScalar E) (L : E →L[ℝ] ℝ)
    (H₁ H₂ : SmoothScalar ℝ) (α p q r k : ℝ) : Fin 5 → SmoothScalar E :=
  α • airyFlux v (localizedSecondPotential χ L H₂ k) +
    transverseFlux v (p • localizedFirstPotential χ L H₁ k)
      (q • localizedFirstPotential χ L H₁ k)
      (r • localizedFirstPotential χ L H₁ k)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_PotentialCurl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory

def crossingPotential (L : ℝ) (a b i j : Fin 3) (x : Coord3) : ℝ :=
  wedgePotential 0 a (fun y => deriv (crossingFirst L) (y 0)*sin (y a)) i j x +
  wedgePotential 0 b (fun y => (deriv (crossingSecond L) (y 0)/2)*sin (2*y b)) i j x +
  wedgePotential a b (angularStream (crossingResidualFirst L) (crossingResidualSecond L) a b) i j x

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_WallParticular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma wallParticularNumerator_smooth [ProperSpace E] (d : E) {v r₁ r₂ : E × ℝ → ℝ}
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v) (h₁ : ContDiff ℝ (↑(⊤ : ℕ∞)) r₁)
    (h₂ : ContDiff ℝ (↑(⊤ : ℕ∞)) r₂) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (wallParticularNumerator d v r₁ r₂) := by
  exact (wallPrimitive_smooth (h₂.sub (wallAlong_smooth d
    ((wallPrimitive_smooth h₁).mul (wallDerivative_smooth hv))))).sub
      ((wallPrimitive_smooth h₁).mul (wallAlong_smooth d hv))

theorem wall_particular_flux_equations [ProperSpace E] (d : E) {v r₁ r₂ : E × ℝ → ℝ}
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v) (h₁ : ContDiff ℝ (↑(⊤ : ℕ∞)) r₁)
    (h₂ : ContDiff ℝ (↑(⊤ : ℕ∞)) r₂) (p : E × ℝ) :
    wallDerivative (wallPrimitive r₁) p=r₁ p ∧
    wallAlong d (fun q => wallPrimitive r₁ q*wallDerivative v q) p+
      wallDerivative (fun q => wallPrimitive r₁ q*wallAlong d v q+
        wallParticularNumerator d v r₁ r₂ q) p=r₂ p := by
  refine ⟨wallDerivative_primitive h₁ p,?_⟩
  let B : E × ℝ → ℝ := fun q =>
    r₂ q-wallAlong d (fun q => wallPrimitive r₁ q*wallDerivative v q) q
  have hB : ContDiff ℝ (↑(⊤ : ℕ∞)) B := h₂.sub (wallAlong_smooth d
    ((wallPrimitive_smooth h₁).mul (wallDerivative_smooth hv)))
  have he : (fun q => wallPrimitive r₁ q*wallAlong d v q+
      wallParticularNumerator d v r₁ r₂ q)=wallPrimitive B := by
    funext q; simp only [wallParticularNumerator,B]; ring
  rw [he,wallDerivative_primitive hB]
  dsimp [B]; ring

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_CylinderModeGreen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus

local instance cylinderModeGreenMeasureSpace_r244364_1 : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
def smoothCylinderModeJet {q : ℝ → ℂ} (hq : ContDiff ℝ (↑(⊤:ℕ∞)) q)
    (R : ℝ) (k : TorusModes) : FiniteCylinderJets R :=
  WithLp.toLp 2 ![cylinderMode (FiniteAxisMeasure R) k (smoothFiniteAxisLp hq.continuous R),
    cylinderMode (FiniteAxisMeasure R) k (smoothFiniteAxisLp (hq.continuous_deriv (by simp)) R),
    cylinderMode (FiniteAxisMeasure R) k ((Complex.I*(k 0:ℂ))•smoothFiniteAxisLp hq.continuous R),
    cylinderMode (FiniteAxisMeasure R) k ((Complex.I*(k 1:ℂ))•smoothFiniteAxisLp hq.continuous R)]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_CylinderJetOrthogonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory Filter Topology

def cylinderJetMode (R : ℝ) (h : TorusModes) :
    FiniteAxisJets R →ₗᵢ[ℂ] FiniteCylinderJets R where
  toFun q := WithLp.toLp 2 (fun j => cylinderMode (FiniteAxisMeasure R) h (q j))
  map_add' q r := by
    apply PiLp.ext
    intro j
    exact map_add (cylinderMode (FiniteAxisMeasure R) h) (q j) (r j)
  map_smul' c q := by
    apply PiLp.ext
    intro j
    exact map_smul (cylinderMode (FiniteAxisMeasure R) h) c (q j)
  norm_map' q := by
    have he : ‖WithLp.toLp 2 (fun j => cylinderMode (FiniteAxisMeasure R) h (q j))‖^2=‖q‖^2 := by
      simp only [PiLp.norm_sq_eq_of_L2,LinearIsometry.norm_map]
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp he

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_CylinderPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory Filter Topology

def cylinderPolynomialJetL (R : ℝ) : (TorusModes →₀ smoothComplexAxis) →ₗ[ℂ] FiniteCylinderJets R :=
  Finsupp.lsum ℂ (fun h => (cylinderJetMode R h).toLinearMap.comp (smoothAxisModeJetL R h))

open Set MeasureTheory Filter Topology
open scoped ENNReal

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_CylinderSobolevGraph
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace _root_.OAI.ScalarConductivity.spectralTraceGraph_realInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

def cylinderPolynomialGraphL (s : Fin 3 → ℝ) (R : ℝ) :
    (TorusModes →₀ smoothComplexAxis) →ₗ[ℂ] CylinderTraceAmbient s R :=
  (cylinderPolynomialJetL R).prod
    ((cylinderPolynomialTraceL s 0).prod (cylinderPolynomialTraceL s R))

def cylinderSobolevGraph (s : Fin 3 → ℝ) (R : ℝ) : Submodule ℂ (CylinderTraceAmbient s R) :=
  (LinearMap.range (cylinderPolynomialGraphL s R)).topologicalClosure

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_CylinderCompletedGreen
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace _root_.OAI.ScalarConductivity.spectralTraceGraph_realInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

def spectralEndWeight (s : Fin 3 → ℝ) (R : ℝ) (f : spectralTraceGraph (torusRate s)) :
    SpectralL2 TorusModes :=
  sequenceMultiplier (fun h => (Real.exp (-torusRate s h*|R|):ℂ)) 1
    zero_le_one (poissonMultiplier_bound s R) (f.val 1)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_CylinderSlopeGreen
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace _root_.OAI.ScalarConductivity.spectralTraceGraph_realInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

def cylinderSlopeJet (r R : ℝ) : FiniteCylinderJets R :=
  smoothCylinderModeJet (complex_linear_axis_smooth r) R 0

end ScalarConductivity



namespace ScalarConductivity
open Set MeasureTheory Filter Topology

def cylinderTerminalFlux (s : Fin 3 → ℝ) (r R : ℝ)
    (f g : spectralTraceGraph (torusRate s)) : ℝ :=
  r*spectralGraphMean (torusRate s) g-(spectralWeightedPairL s (spectralEndWeight s R f) g).re

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_SobolevChain
attribute [-instance] _root_.OAI.ScalarConductivity.bumpProbability_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

variable {g dg : ℝ → ℝ} (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g) (hdg : Continuous dg)
  (hderiv : ∀ r, HasDerivAt g (dg r) r) {C : ℝ} (hC : 0≤C)
  (hgb : ∀ r, ‖g r‖≤C*‖r‖) (hdgb : ∀ r, ‖dg r‖≤C)

include hderiv

def sobolevChain (u : H1) : H1 :=
  ⟨sobolevChainLp hg hdg hC hgb hdgb u.val,
    sobolevChainLp_preserves_H1 hg hdg hderiv hC hgb hdgb u.property⟩

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_ParentFullEndH1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix

def fullEndFlatCovector (s : Fin 3 → ℝ) (f : spectralTraceGraph (torusRate s))
    (κ : ℝ) (t : ℝ) (θ : (Fin 2 → UnitAddCircle)) : Fin 3 → ℝ :=
  (fun k => (endPoissonField s f k.succ (t,θ)).re)+κ • Pi.single 0 1

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_CompactRegularCorrection
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace _root_.OAI.ScalarConductivity.centralMeasure_finite _root_.OAI.ScalarConductivity.instCoeFunSubtypeForallBox3RealMemSubmoduleCentralSmoothFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma cube_coordinate_divergence_moment {F₁ F₂ F₃ r : Box3 → ℝ}
    (h₁ : ContDiff ℝ (↑(⊤ : ℕ∞)) F₁) (h₂ : ContDiff ℝ (↑(⊤ : ℕ∞)) F₂)
    (h₃ : ContDiff ℝ (↑(⊤ : ℕ∞)) F₃)
    (hs₁ : HasCompactSupport F₁) (hs₂ : HasCompactSupport F₂) (hs₃ : HasCompactSupport F₃)
    (hd : ∀ p, cubePartial F₁ ((1,0),0) p+cubePartial F₂ ((0,1),0) p+
      cubePartial F₃ ((0,0),1) p=r p)
    {f : Box3 → ℝ} (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) :
    (∫ p,f p*r p)= -(∫ p,cubePartial f ((1,0),0) p*F₁ p)-
      (∫ p,cubePartial f ((0,1),0) p*F₂ p)-(∫ p,cubePartial f ((0,0),1) p*F₃ p) := by
  have he : (fun p => f p*r p)=(fun p => f p*cubePartial F₁ ((1,0),0) p+
      f p*cubePartial F₂ ((0,1),0) p+f p*cubePartial F₃ ((0,0),1) p) := by
    funext p; rw [←hd p]; ring
  have hi₁ : Integrable (fun p => f p*cubePartial F₁ ((1,0),0) p) := (hf.continuous.mul (continuous_cubePartial h₁ ((1,0),0))).integrable_of_hasCompactSupport (μ := volume)
    (cubePartial_compact hs₁ _).mul_left
  have hi₂ : Integrable (fun p => f p*cubePartial F₂ ((0,1),0) p) := (hf.continuous.mul (continuous_cubePartial h₂ ((0,1),0))).integrable_of_hasCompactSupport (μ := volume)
    (cubePartial_compact hs₂ _).mul_left
  have hi₃ : Integrable (fun p => f p*cubePartial F₃ ((0,0),1) p) := (hf.continuous.mul (continuous_cubePartial h₃ ((0,0),1))).integrable_of_hasCompactSupport (μ := volume)
    (cubePartial_compact hs₃ _).mul_left
  have hi₁₂ : Integrable (fun p => f p*cubePartial F₁ ((1,0),0) p+f p*cubePartial F₂ ((0,1),0) p) := hi₁.add hi₂
  rw [he,integral_add hi₁₂ hi₃,integral_add hi₁ hi₂,
    cube_integration_by_parts hf h₁ hs₁,cube_integration_by_parts hf h₂ hs₂,
    cube_integration_by_parts hf h₃ hs₃]
  ring

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_CubeWeakDivergence
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace _root_.OAI.ScalarConductivity.centralMeasure_finite _root_.OAI.ScalarConductivity.instCoeFunSubtypeForallBox3RealMemSubmoduleCentralSmoothFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory

theorem cube_weak_divergence {F₁ F₂ F₃ r : Box3 → ℝ}
    (h₁ : ContDiff ℝ (↑(⊤ : ℕ∞)) F₁) (h₂ : ContDiff ℝ (↑(⊤ : ℕ∞)) F₂)
    (h₃ : ContDiff ℝ (↑(⊤ : ℕ∞)) F₃)
    (hs₁ : HasCompactSupport F₁) (hs₂ : HasCompactSupport F₂) (hs₃ : HasCompactSupport F₃)
    (hd : ∀ p,cubePartial F₁ ((1,0),0) p+cubePartial F₂ ((0,1),0) p+
      cubePartial F₃ ((0,0),1) p=r p)
    (φ : Box3 → ℝ) (hφ : ContDiff ℝ (↑(⊤ : ℕ∞)) φ) :
    (∫ p,fderiv ℝ φ p ((F₁ p,F₂ p),F₃ p))=-(∫ p,φ p*r p) := by
  have hi₁ : Integrable (fun p => cubePartial φ ((1,0),0) p*F₁ p) :=
    ((cubePartial_smooth hφ _).continuous.mul h₁.continuous).integrable_of_hasCompactSupport hs₁.mul_left
  have hi₂ : Integrable (fun p => cubePartial φ ((0,1),0) p*F₂ p) :=
    ((cubePartial_smooth hφ _).continuous.mul h₂.continuous).integrable_of_hasCompactSupport hs₂.mul_left
  have hi₃ : Integrable (fun p => cubePartial φ ((0,0),1) p*F₃ p) :=
    ((cubePartial_smooth hφ _).continuous.mul h₃.continuous).integrable_of_hasCompactSupport hs₃.mul_left
  simp_rw [cube_fderiv_expansion]
  have hi₁₂ : Integrable (fun p => cubePartial φ ((1,0),0) p*F₁ p+cubePartial φ ((0,1),0) p*F₂ p) := hi₁.add hi₂
  rw [integral_add hi₁₂ hi₃,integral_add hi₁ hi₂]
  linarith [cube_coordinate_divergence_moment h₁ h₂ h₃ hs₁ hs₂ hs₃ hd hφ]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_RegularPotentialCoordinates
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace _root_.OAI.ScalarConductivity.centralMeasure_finite _root_.OAI.ScalarConductivity.instCoeFunSubtypeForallBox3RealMemSubmoduleCentralSmoothFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise

lemma correctionBox_isOpen (a b : Coord3) : IsOpen (correctionBox a b) :=
  ((isOpen_Ioo.prod isOpen_Ioo).prod isOpen_Ioo).preimage boxCoordinates.continuous

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_SymmetricCutoffSources
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

theorem symmetric_cutoff_sources
    (H : Coord3 → Mat3) (hH : ContDiff ℝ (↑(⊤ : ℕ∞)) H) (hs : HasCompactSupport H)
    (hsy : ∀ x,(H x).IsSymm)
    (u : Coord3 → Fin 2 → ℝ) (hu : ContDiff ℝ (↑(⊤ : ℕ∞)) u) :
    (∀ j,ContDiff ℝ (↑(⊤ : ℕ∞)) (symmetricSource H u j)) ∧
    (∀ j,HasCompactSupport (symmetricSource H u j)) ∧
    (∀ j (ψ : Coord3 → ℝ),ContDiff ℝ (↑(⊤ : ℕ∞)) ψ →
      (∫ x,fderiv ℝ ψ x ((H x*gradientColumns (fderiv ℝ u x)).col j))=
        -(∫ x,ψ x*symmetricSource H u j x)) ∧
    (∫ x,symmetricSource H u 0 x)=0 ∧ (∫ x,symmetricSource H u 1 x)=0 ∧
    (∫ x,u x 1*symmetricSource H u 0 x-u x 0*symmetricSource H u 1 x)=0 := by
  have hr (j : Fin 2) : ContDiff ℝ (↑(⊤ : ℕ∞)) (symmetricSource H u j) :=
    coordinateDivergence_smooth (symmetricFlux_smooth hH hu j)
  have hsr (j : Fin 2) : HasCompactSupport (symmetricSource H u j) :=
    coordinateDivergence_compact (symmetricFlux_compact hs u j)
  have hw (j : Fin 2) (ψ : Coord3 → ℝ) (hψ : ContDiff ℝ (↑(⊤ : ℕ∞)) ψ) :
      (∫ x,fderiv ℝ ψ x ((H x*gradientColumns (fderiv ℝ u x)).col j))=
        -(∫ x,ψ x*symmetricSource H u j x) :=
    coordinateDivergence_weak (symmetricFlux_smooth hH hu j) (symmetricFlux_compact hs u j) ψ hψ
  exact ⟨hr,hsr,hw,compact_symmetric_source_moments u hu H hsy _ hr hsr hw⟩

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_ParametricPotentialCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem exists_parametric_potential_coordinates
    {u : P×Coord3 → Fin 2 → ℝ} (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u)
    (p : P) (x : Coord3) (hD : Function.Surjective (fderiv ℝ (fun y => u (p,y)) x))
    {U : Set (P×Coord3)} (hU : IsOpen U) (hpx : (p,x)∈U) :
    ∃ Y : OpenPartialHomeomorph (P×Coord3) (P×Coord3),
      (p,x)∈Y.source ∧ Y.source⊆U ∧
      (∀ q y,(Y (q,y)).1=q) ∧
      (∀ q y,coordinatePair (Y (q,y)).2=u (q,y)) ∧
      ContDiff ℝ (↑(⊤:ℕ∞)) Y ∧ ContDiffOn ℝ (↑(⊤:ℕ∞)) Y.symm Y.target := by
  let D := fderiv ℝ (fun y => u (p,y)) x
  obtain ⟨Q,hQ⟩ := ContinuousLinearMap.HasRightInverse.of_surjective_of_finiteDimensional hD
  let L := potentialCompletionEquiv D hD
  let φ : P×Coord3 → Coord3 := fun q => L (completedPotential (fun y => u (q.1,y)) D Q q.2)
  have hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ :=
    L.contDiff.comp (((Q.contDiff.comp hu).add contDiff_snd).sub (Q.contDiff.comp (D.contDiff.comp contDiff_snd)))
  have hup : ContDiff ℝ (↑(⊤:ℕ∞)) (fun y => u (p,y)) :=
    hu.comp (contDiff_const.prodMk contDiff_id)
  have hφd : fderiv ℝ (fun y => φ (p,y)) x=(L : Coord3 →L[ℝ] Coord3) := by
    have hh := L.hasFDerivAt.comp x (completedPotential_derivative
      ((hup.differentiable (by simp) x).hasFDerivAt) Q)
    simpa only [φ,D,Function.comp_def,ContinuousLinearMap.comp_id] using hh.fderiv
  obtain ⟨Y,hp,hsub,he,hY,hYi⟩ := exists_parametric_diffeomorph hφ p x L hφd hU hpx
  refine ⟨Y,hp,hsub,fun q y => by rw [he],?_,hY,hYi⟩
  intro q y
  rw [he]
  exact (potentialCompletionEquiv_pairing D hD _).trans
    (completedPotential_pairing (fun y => u (q,y)) D Q hQ y)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_PhysicalC1Pullback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise

lemma inverseSourceWeight_smooth
    (X : OpenPartialHomeomorph Coord3 Coord3)
    (hX : ContDiffOn ℝ (↑(⊤:ℕ∞)) X X.source)
    (hXi : ContDiffOn ℝ (↑(⊤:ℕ∞)) X.symm X.target) :
    ContDiffOn ℝ (↑(⊤:ℕ∞)) (inverseSourceWeight X) X.source := by
  apply X.open_source.contDiffOn_iff.mpr
  intro x hx
  have hxs := hX.contDiffAt (X.open_source.mem_nhds hx)
  have hxis := hXi.contDiffAt (X.open_target.mem_nhds (X.map_source hx))
  have hd : ContDiffAt ℝ (↑(⊤:ℕ∞)) (fun y => fderiv ℝ X.symm (X y)) x :=
    (hxis.fderiv_right (by trivial)).comp x hxs
  have hd0 := local_fderiv_det_ne_zero X.symm (hXi.differentiableOn (by simp))
    (hX.differentiableOn (by simp)) (X.map_source hx)
  exact ((((contDiff_clm_det (E := Coord3) (↑(⊤:ℕ∞))).contDiffAt.comp x hd).abs hd0).inv
    (abs_ne_zero.mpr hd0))

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_ParametricSpatialDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace ScalarConductivity
open Set Filter Topology Matrix
open scoped Matrix.Norms.Elementwise

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

omit [FiniteDimensional ℝ P] in
theorem parametric_chart_compact_bounds
    (Y : OpenPartialHomeomorph (P×Coord3) (P×Coord3))
    (hY : ∀ p x,(Y (p,x)).1=p)
    (hsm : ContDiff ℝ (↑(⊤:ℕ∞)) Y)
    (hinv : ContDiffOn ℝ (↑(⊤:ℕ∞)) Y.symm Y.target)
    {K : Set (P×Coord3)} (hK : IsCompact K) (hKs : K⊆Y.target) :
    ∃ B : ℝ,0<B ∧ ∀ q∈K,
      let X := (fiberSlice Y hY q.1).symm
      |inverseSourceWeight X q.2|≤B ∧
      ‖fderiv ℝ (inverseSourceWeight X) q.2‖≤B ∧
      ‖fderiv ℝ X q.2‖≤B ∧
      9*|(fderiv ℝ X q.2).det|⁻¹*‖operatorMatrix (fderiv ℝ X q.2)‖*
        ‖operatorMatrix (fderiv ℝ X q.2)‖≤B := by
  let f : P×Coord3 → Coord3 := fun q => (Y.symm q).2
  let w : P×Coord3 → ℝ := fun q => inverseSourceWeight (fiberSlice Y hY q.1).symm q.2
  let D := spatialFDeriv f
  let g : P×Coord3 → ℝ := fun q =>
    9*|(D q).det|⁻¹*‖operatorMatrix (D q)‖*‖operatorMatrix (D q)‖
  have hf : ContDiffOn ℝ (↑(⊤:ℕ∞)) f Y.target :=
    contDiff_snd.contDiffOn.comp hinv (fun _ _ => mem_univ _)
  have hD := spatialFDeriv_smoothOn Y.open_target hf
  have hw := parametric_inverseSourceWeight_smooth Y hY hsm hinv
  have hdw := spatialFDeriv_smoothOn Y.open_target hw
  have hg : ContinuousOn g Y.target := by
    intro q hq
    have hd := hD.contDiffAt (Y.open_target.mem_nhds hq)
    have hm := (operatorMatrix_contDiff (m := Fin 3) (n := Fin 3)).contDiffAt.comp q hd
    have hne : (D q).det≠0 := by
      obtain ⟨hs,hi⟩ := fiberSlice_smooth Y hY hsm hinv q.1
      exact local_fderiv_det_ne_zero (fiberSlice Y hY q.1).symm
        (hi.differentiableOn (by simp)) (hs.differentiable (by simp)).differentiableOn hq
    have ht := ((contDiff_clm_det (E := Coord3) (↑(⊤:ℕ∞))).contDiffAt.comp q hd).abs hne
    exact (((continuousAt_const.mul ((ht.inv (abs_ne_zero.mpr hne)).continuousAt)).mul
      hm.continuousAt.norm).mul hm.continuousAt.norm).continuousWithinAt
  obtain ⟨A,hA⟩ := (hK.image_of_continuousOn (hw.continuousOn.mono hKs)).isBounded.exists_norm_le
  obtain ⟨B,hB⟩ := (hK.image_of_continuousOn (hdw.continuousOn.mono hKs)).isBounded.exists_norm_le
  obtain ⟨C,hC⟩ := (hK.image_of_continuousOn (hD.continuousOn.mono hKs)).isBounded.exists_norm_le
  obtain ⟨T,hT⟩ := (hK.image_of_continuousOn (hg.mono hKs)).isBounded.exists_norm_le
  refine ⟨|A|+|B|+|C|+|T|+1,by positivity,fun q hq => ⟨?_,?_,?_,?_⟩⟩
  · exact (hA _ (mem_image_of_mem _ hq)).trans (by linarith [le_abs_self A,abs_nonneg B,abs_nonneg C,abs_nonneg T])
  · exact (hB _ (mem_image_of_mem _ hq)).trans (by linarith [le_abs_self B,abs_nonneg A,abs_nonneg C,abs_nonneg T])
  · exact (hC _ (mem_image_of_mem _ hq)).trans (by linarith [le_abs_self C,abs_nonneg A,abs_nonneg B,abs_nonneg T])
  · exact (le_abs_self _).trans ((hT _ (mem_image_of_mem _ hq)).trans
      (by linarith [le_abs_self T,abs_nonneg A,abs_nonneg B,abs_nonneg C]))

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Walls_CriticalWallTensor
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace _root_.OAI.ScalarConductivity.centralMeasure_finite _root_.OAI.ScalarConductivity.instCoeFunSubtypeForallBox3RealMemSubmoduleCentralSmoothFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

def wallCoordinatePair (v : Box3 → ℝ) (x : Coord3) : Fin 2 → ℝ :=
  ![x 0,v (boxCoordinates x)]

lemma wallCoordinatePair_smooth {v : Box3 → ℝ}
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (wallCoordinatePair v) := by
  apply contDiff_pi.mpr
  intro j
  fin_cases j
  · exact contDiff_apply ℝ ℝ (0 : Fin 3)
  · exact hv.comp boxCoordinates.contDiff

def wallMatrix (A B : Box3 → ℝ) (x : Coord3) : Mat3 :=
  !![0,0,A (boxCoordinates x);0,0,0;A (boxCoordinates x),0,B (boxCoordinates x)]

lemma wallMatrix_symmetric (A B : Box3 → ℝ) (x : Coord3) :
    (wallMatrix A B x).IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

lemma wallMatrix_smooth {A B : Box3 → ℝ}
    (hA : ContDiff ℝ (↑(⊤ : ℕ∞)) A) (hB : ContDiff ℝ (↑(⊤ : ℕ∞)) B) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (wallMatrix A B) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  fin_cases i <;> fin_cases j
  all_goals first | exact contDiff_const | exact hA.comp boxCoordinates.contDiff |
    exact hB.comp boxCoordinates.contDiff

end ScalarConductivity

end


noncomputable section
namespace ScalarConductivity
open Set Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

lemma wallMatrix_tsupport {A B : Box3 → ℝ} {K : Set Box3}
    (hA : tsupport A⊆K) (hB : tsupport B⊆K) :
    tsupport (wallMatrix A B)⊆boxCoordinates ⁻¹' K := by
  apply matrix_tsupport_subset (wallMatrix A B)
  intro i j
  fin_cases i <;> fin_cases j
  all_goals first
    | exact (tsupport_comp_subset_preimage A boxCoordinates.continuous).trans (preimage_mono hA)
    | exact (tsupport_comp_subset_preimage B boxCoordinates.continuous).trans (preimage_mono hB)
    | simp [wallMatrix]

lemma wallMatrix_compact {A B : Box3 → ℝ}
    (hA : HasCompactSupport A) (hB : HasCompactSupport B) :
    HasCompactSupport (wallMatrix A B) := by
  apply matrix_hasCompactSupport (wallMatrix A B)
  intro i j
  fin_cases i <;> fin_cases j
  all_goals first
    | exact hA.comp_homeomorph boxCoordinates.toHomeomorph
    | exact hB.comp_homeomorph boxCoordinates.toHomeomorph
    | exact HasCompactSupport.zero

def wallParticularTensor (χ v r₁ r₂ : Box3 → ℝ) : Coord3 → Mat3 :=
  wallMatrix (fun p => χ p*wallPrimitive r₁ p)
    (fun p => χ p*(wallQuotient (wallParticularNumerator (1,0) v r₁ r₂) p/wallQuotient (wallDerivative v) p))

lemma wallParticularTensor_smooth {χ v r₁ r₂ : Box3 → ℝ}
    (hχ : ContDiff ℝ (↑(⊤ : ℕ∞)) χ) (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v)
    (h₁ : ContDiff ℝ (↑(⊤ : ℕ∞)) r₁) (h₂ : ContDiff ℝ (↑(⊤ : ℕ∞)) r₂)
    (hne : ∀ p∈tsupport χ,wallQuotient (wallDerivative v) p≠0) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (wallParticularTensor χ v r₁ r₂) :=
  wallMatrix_smooth (hχ.mul (wallPrimitive_smooth h₁))
    (smooth_wall_cutoff_ratio hχ (wallParticularNumerator_smooth (1,0) hv h₁ h₂)
      (wallDerivative_smooth hv) hne)

lemma wallParticularTensor_compact {χ v r₁ r₂ : Box3 → ℝ} (hs : HasCompactSupport χ) :
    HasCompactSupport (wallParticularTensor χ v r₁ r₂) ∧
      tsupport (wallParticularTensor χ v r₁ r₂)⊆boxCoordinates ⁻¹' tsupport χ :=
  ⟨wallMatrix_compact hs.mul_right hs.mul_right,
    wallMatrix_tsupport tsupport_mul_subset_left tsupport_mul_subset_left⟩

theorem wallParticularTensor_weak_moments {χ v r₁ r₂ : Box3 → ℝ}
    (hχ : ContDiff ℝ (↑(⊤ : ℕ∞)) χ) (hs : HasCompactSupport χ)
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v)
    (h₁ : ContDiff ℝ (↑(⊤ : ℕ∞)) r₁) (h₂ : ContDiff ℝ (↑(⊤ : ℕ∞)) r₂)
    (hne : ∀ p∈tsupport χ,wallQuotient (wallDerivative v) p≠0) :
    let H := wallParticularTensor χ v r₁ r₂
    let u := wallCoordinatePair v
    (∀ j,ContDiff ℝ (↑(⊤ : ℕ∞)) (symmetricSource H u j)) ∧
    (∀ j,HasCompactSupport (symmetricSource H u j)) ∧
    (∀ j (ψ : Coord3 → ℝ),ContDiff ℝ (↑(⊤ : ℕ∞)) ψ →
      (∫ x,fderiv ℝ ψ x ((H x*gradientColumns (fderiv ℝ u x)).col j))=
        -(∫ x,ψ x*symmetricSource H u j x)) ∧
    (∫ x,symmetricSource H u 0 x)=0 ∧ (∫ x,symmetricSource H u 1 x)=0 ∧
    (∫ x,u x 1*symmetricSource H u 0 x-u x 0*symmetricSource H u 1 x)=0 :=
  symmetric_cutoff_sources _ (wallParticularTensor_smooth hχ hv h₁ h₂ hne)
    (wallParticularTensor_compact hs).1 (wallMatrix_symmetric _ _) _ (wallCoordinatePair_smooth hv)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_ParametricSymmetricSources
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace _root_.OAI.ScalarConductivity.centralMeasure_finite _root_.OAI.ScalarConductivity.instCoeFunSubtypeForallBox3RealMemSubmoduleCentralSmoothFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

lemma symmetricSource_parametric_smoothOn {H : P×Coord3 → Mat3} {u : P×Coord3 → Fin 2 → ℝ}
    {V : Set (P×Coord3)} (hV : IsOpen V) (hH : ContDiffOn ℝ (↑(⊤:ℕ∞)) H V)
    (hu : ContDiffOn ℝ (↑(⊤:ℕ∞)) u V) (j : Fin 2) :
    ContDiffOn ℝ (↑(⊤:ℕ∞)) (fun q => symmetricSource (fun x => H (q.1,x)) (fun x => u (q.1,x)) j q.2) V := by
  apply coordinateDivergence_parametric_smoothOn hV
    (f:=fun q : P×Coord3 => (H q*gradientColumns (fderiv ℝ (fun x => u (q.1,x)) q.2)).col j)
  have hg := gradientColumns_parametric_smoothOn hV hu
  apply contDiffOn_pi.mpr
  intro i
  change ContDiffOn ℝ (↑(⊤:ℕ∞)) (fun q => ∑ k, H q i k *
    gradientColumns (fderiv ℝ (fun x => u (q.1,x)) q.2) k j) V
  apply ContDiffOn.sum
  intro k _
  exact (contDiffOn_pi.mp (contDiffOn_pi.mp hH i) k).mul
    (contDiffOn_pi.mp (contDiffOn_pi.mp hg k) j)

lemma wallCoordinatePair_parametric_smooth {v : P×Box3 → ℝ}
    (hv : ContDiff ℝ (↑(⊤:ℕ∞)) v) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (fun q : P×Coord3 => wallCoordinatePair (fun y => v (q.1,y)) q.2) := by
  apply contDiff_pi.mpr
  intro j
  fin_cases j
  · exact (contDiff_apply ℝ ℝ (0:Fin 3)).comp contDiff_snd
  · exact hv.comp (contDiff_fst.prodMk (boxCoordinates.contDiff.comp contDiff_snd))

lemma wallMatrix_parametric_smoothOn {A B : P×Box3 → ℝ} {V : Set P}
    (hA : ContDiffOn ℝ (↑(⊤:ℕ∞)) A (V×ˢuniv))
    (hB : ContDiffOn ℝ (↑(⊤:ℕ∞)) B (V×ˢuniv)) :
    ContDiffOn ℝ (↑(⊤:ℕ∞)) (fun q : P×Coord3 =>
      wallMatrix (fun y => A (q.1,y)) (fun y => B (q.1,y)) q.2) (V×ˢuniv) := by
  have hm : ContDiff ℝ (↑(⊤:ℕ∞)) (fun q : P×Coord3 => (q.1,boxCoordinates q.2)) :=
    contDiff_fst.prodMk (boxCoordinates.contDiff.comp contDiff_snd)
  have hmap : MapsTo (fun q : P×Coord3 => (q.1,boxCoordinates q.2)) (V×ˢuniv) (V×ˢuniv) :=
    fun q hq => ⟨hq.1,mem_univ _⟩
  apply contDiffOn_pi.mpr
  intro i
  apply contDiffOn_pi.mpr
  intro j
  fin_cases i <;> fin_cases j
  all_goals first | exact contDiffOn_const | exact hA.comp hm.contDiffOn hmap |
    exact hB.comp hm.contDiffOn hmap

end ScalarConductivity

end


end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Walls_WallHalfspaceIntegral
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace _root_.OAI.ScalarConductivity.centralMeasure_finite _root_.OAI.ScalarConductivity.instCoeFunSubtypeForallBox3RealMemSubmoduleCentralSmoothFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

theorem wall_halfspace_flux {f g : Box3 → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g)
    (hsf : HasCompactSupport f) (hsg : HasCompactSupport g) (d : ℝ×ℝ) :
    (∫ p in (Set.univ : Set (ℝ×ℝ)) ×ˢ Ioi (0:ℝ),
      wallAlong d f p+wallDerivative g p)= -(∫ q : ℝ×ℝ,g (q,0)) := by
  have hif : Integrable (wallAlong d f) :=
    (wallAlong_smooth d hf).continuous.integrable_of_hasCompactSupport (hsf.fderiv_apply ℝ (d,0))
  have hig : Integrable (wallDerivative g) :=
    (wallDerivative_smooth hg).continuous.integrable_of_hasCompactSupport (hsg.fderiv_apply ℝ (0,1))
  have hm : (volume : Measure Box3).restrict ((Set.univ : Set (ℝ×ℝ)) ×ˢ Ioi (0:ℝ))=
      (volume : Measure (ℝ×ℝ)).prod ((volume : Measure ℝ).restrict (Ioi 0)) := by
    change ((volume : Measure (ℝ×ℝ)).prod (volume : Measure ℝ)).restrict _=_
    rw [←Measure.prod_restrict,Measure.restrict_univ]
  rw [integral_add hif.integrableOn hig.integrableOn]
  have hfzero : (∫ p in (Set.univ : Set (ℝ×ℝ)) ×ˢ Ioi (0:ℝ),wallAlong d f p)=0 := by
    rw [hm,integral_prod_symm]
    · simp_rw [wallAlong_integral_slice hf hsf d,integral_zero]
    · rw [←hm]; exact hif.integrableOn
  rw [hfzero,zero_add,hm,integral_prod]
  · simp_rw [wallDerivative_slice (hg.differentiable (by simp))]
    have he (q : ℝ×ℝ) : (∫ z in Ioi (0:ℝ),deriv (fun t => g (q,t)) z)= -g (q,0) :=
      HasCompactSupport.integral_Ioi_deriv_eq
        ((hg.of_le (by simp)).comp (contDiff_const.prodMk contDiff_id))
        (hasCompactSupport_prodMkLeft hsg q) 0
    simp_rw [he,integral_neg]
  · rw [←hm]; exact hig.integrableOn

end ScalarConductivity



namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma wallAlong_sCoordinate (p : Box3) : wallAlong (1,0) (fun q : Box3 => q.1.1) p=1 := by
  exact cubePartial_fst_fst ((1,0),0) p

lemma wallDerivative_sCoordinate (p : Box3) : wallDerivative (fun q : Box3 => q.1.1) p=0 := by
  exact cubePartial_fst_fst ((0,0),1) p

lemma wall_torque_divergence {A B v : Box3 → ℝ}
    (hA : ContDiff ℝ (↑(⊤ : ℕ∞)) A) (hB : ContDiff ℝ (↑(⊤ : ℕ∞)) B)
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v) (p : Box3) :
    v p*wallDerivative A p-p.1.1*(wallAlong (1,0) (fun q => A q*wallDerivative v q) p+
      wallDerivative (fun q => A q*wallAlong (1,0) v q+B q*wallDerivative v q) p)=
    wallAlong (1,0) (fun q => -q.1.1*(A q*wallDerivative v q)) p+
      wallDerivative (fun q => v q*A q-q.1.1*(A q*wallAlong (1,0) v q+B q*wallDerivative v q)) p := by
  let F := fun q => A q*wallDerivative v q
  let G := fun q => A q*wallAlong (1,0) v q+B q*wallDerivative v q
  have hF := (hA.mul (wallDerivative_smooth hv)).differentiable (by simp)
  have hG := ((hA.mul (wallAlong_smooth (1,0) hv)).add (hB.mul (wallDerivative_smooth hv))).differentiable (by simp)
  have hs : Differentiable ℝ (fun q : Box3 => q.1.1) := differentiable_fst.comp differentiable_fst
  have hAd := hA.differentiable (by simp)
  have hvd := hv.differentiable (by simp)
  change v p*wallDerivative A p-p.1.1*(wallAlong (1,0) F p+wallDerivative G p)=
    wallAlong (1,0) (fun q => -q.1.1*F q) p+
      wallDerivative (fun q => v q*A q-q.1.1*G q) p
  rw [wallAlong_mul (f := fun q : Box3 => -q.1.1) (g := F) (1,0) hs.neg hF,wallAlong_neg,wallAlong_sCoordinate,
    wallDerivative_sub (f := fun q => v q*A q) (g := fun q => q.1.1*G q) (hvd.mul hAd) (hs.mul hG),wallDerivative_mul hvd hAd,
    wallDerivative_mul (f := fun q : Box3 => q.1.1) (g := G) hs hG,wallDerivative_sCoordinate]
  dsimp [F]
  ring

theorem wall_matrix_halfspace_moments {A B v : Box3 → ℝ}
    (hA : ContDiff ℝ (↑(⊤ : ℕ∞)) A) (hB : ContDiff ℝ (↑(⊤ : ℕ∞)) B)
    (hsA : HasCompactSupport A) (hsB : HasCompactSupport B)
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v) (hz : ∀ q,wallDerivative v (q,0)=0) :
    let U := (Set.univ : Set (ℝ×ℝ)) ×ˢ Ioi (0:ℝ)
    let r₁ := wallDerivative A
    let r₂ := fun p => wallAlong (1,0) (fun q => A q*wallDerivative v q) p+
      wallDerivative (fun q => A q*wallAlong (1,0) v q+B q*wallDerivative v q) p
    (∫ p in U,r₁ p)= -(∫ q : ℝ×ℝ,A (q,0)) ∧
    (∫ p in U,r₂ p)= -(∫ q : ℝ×ℝ,A (q,0)*wallAlong (1,0) v (q,0)) ∧
    (∫ p in U,v p*r₁ p-p.1.1*r₂ p)=
      -(∫ q : ℝ×ℝ,A (q,0)*(v (q,0)-q.1*wallAlong (1,0) v (q,0))) := by
  dsimp only
  have hF := hA.mul (wallDerivative_smooth hv)
  have hG := (hA.mul (wallAlong_smooth (1,0) hv)).add (hB.mul (wallDerivative_smooth hv))
  have hsF : HasCompactSupport (fun q => A q*wallDerivative v q) := hsA.mul_right
  have hsG : HasCompactSupport (fun q => A q*wallAlong (1,0) v q+B q*wallDerivative v q) :=
    hsA.mul_right.add hsB.mul_right
  have hs : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun q : Box3 => q.1.1) := contDiff_fst.comp contDiff_fst
  refine ⟨?_,?_,?_⟩
  · have hh := wall_halfspace_flux (f := fun _ : Box3 => 0) contDiff_const hA HasCompactSupport.zero hsA (1,0)
    simpa [wallAlong] using hh
  · have hh := wall_halfspace_flux hF hG hsF hsG (1,0)
    simpa only [hz,mul_zero,add_zero] using hh
  · have hh := wall_halfspace_flux
      (hs.neg.mul hF) ((hv.mul hA).sub (hs.mul hG))
      hsF.mul_left (hsA.mul_left.sub hsG.mul_left) (1,0)
    simp_rw [←wall_torque_divergence hA hB hv] at hh
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    apply integral_congr_ae
    filter_upwards [] with q
    simp only [hz,mul_zero,add_zero]
    ring

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Walls_CriticalWallHomogeneous
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace _root_.OAI.ScalarConductivity.centralMeasure_finite _root_.OAI.ScalarConductivity.instCoeFunSubtypeForallBox3RealMemSubmoduleCentralSmoothFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

def wallHomogeneousTensor (χ v : Box3 → ℝ) (a : (ℝ×ℝ) → ℝ) : Coord3 → Mat3 :=
  wallMatrix (fun p => χ p*a p.1)
    (fun p => χ p*(wallQuotient (wallHomogeneousNumerator (1,0) v a) p/wallQuotient (wallDerivative v) p))

lemma wallHomogeneousTensor_smooth {χ v : Box3 → ℝ} {a : (ℝ×ℝ) → ℝ}
    (hχ : ContDiff ℝ (↑(⊤ : ℕ∞)) χ) (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v)
    (ha : ContDiff ℝ (↑(⊤ : ℕ∞)) a)
    (hne : ∀ p∈tsupport χ,wallQuotient (wallDerivative v) p≠0) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (wallHomogeneousTensor χ v a) :=
  wallMatrix_smooth (hχ.mul (ha.comp contDiff_fst))
    (smooth_wall_cutoff_ratio hχ (wallHomogeneousNumerator_smooth (1,0) hv ha)
      (wallDerivative_smooth hv) hne)

lemma wallHomogeneousTensor_compact {χ v : Box3 → ℝ} {a : (ℝ×ℝ) → ℝ} (hs : HasCompactSupport χ) :
    HasCompactSupport (wallHomogeneousTensor χ v a) ∧
      tsupport (wallHomogeneousTensor χ v a)⊆boxCoordinates ⁻¹' tsupport χ :=
  ⟨wallMatrix_compact hs.mul_right hs.mul_right,
    wallMatrix_tsupport tsupport_mul_subset_left tsupport_mul_subset_left⟩

end ScalarConductivity

end


end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Walls_CriticalWall
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace _root_.OAI.ScalarConductivity.centralMeasure_finite _root_.OAI.ScalarConductivity.instCoeFunSubtypeForallBox3RealMemSubmoduleCentralSmoothFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix Filter Topology

lemma wallHomogeneousTensor_tsupport_surface {χ v : Box3 → ℝ} {a : (ℝ×ℝ) → ℝ}
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v) (ha : ContDiff ℝ (↑(⊤ : ℕ∞)) a) :
    tsupport (wallHomogeneousTensor χ v a)⊆(fun x : Coord3 => (boxCoordinates x).1) ⁻¹' tsupport a := by
  apply closure_minimal _ ((isClosed_tsupport a).preimage (continuous_fst.comp boxCoordinates.continuous))
  intro x hx
  by_contra hn
  have ha₀ : a (boxCoordinates x).1=0 := image_eq_zero_of_notMem_tsupport hn
  have hq := wallHomogeneousQuotient_zero_off_surface hv ha hn
  apply hx
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [wallHomogeneousTensor,wallMatrix,ha₀,hq]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Walls_CriticalWallResidual
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace _root_.OAI.ScalarConductivity.centralMeasure_finite _root_.OAI.ScalarConductivity.instCoeFunSubtypeForallBox3RealMemSubmoduleCentralSmoothFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix Filter Topology

lemma wallParticularTensor_tsupport_surface {K : Set (ℝ×ℝ)} (hK : IsClosed K)
    {χ v r₁ r₂ : Box3 → ℝ}
    (hr₁ : tsupport r₁⊆Prod.fst ⁻¹' K) (hr₂ : tsupport r₂⊆Prod.fst ⁻¹' K) :
    tsupport (wallParticularTensor χ v r₁ r₂)⊆
      (fun x : Coord3 => (boxCoordinates x).1) ⁻¹' K := by
  have hA := wallPrimitive_tsupport_surface hK hr₁
  have hd : tsupport (wallAlong (1,0) (fun p => wallPrimitive r₁ p*wallDerivative v p))⊆
      Prod.fst ⁻¹' K :=
    (tsupport_fderiv_apply_subset ℝ ((1,0),0)).trans (tsupport_mul_subset_left.trans hA)
  have hG : tsupport (wallParticularNumerator (1,0) v r₁ r₂)⊆Prod.fst ⁻¹' K := by
    apply (tsupport_sub _ _).trans
    apply union_subset
    · exact wallPrimitive_tsupport_surface hK ((tsupport_sub _ _).trans (union_subset hr₂ hd))
    · exact tsupport_mul_subset_left.trans hA
  have hQ := wallQuotient_tsupport_surface hK hG
  apply closure_minimal _ (hK.preimage (continuous_fst.comp boxCoordinates.continuous))
  intro x hx
  by_contra hn
  have ha₀ : wallPrimitive r₁ (boxCoordinates x)=0 :=
    image_eq_zero_of_notMem_tsupport (fun hh => hn (hA hh))
  have hq₀ : wallQuotient (wallParticularNumerator (1,0) v r₁ r₂) (boxCoordinates x)=0 :=
    image_eq_zero_of_notMem_tsupport (fun hh => hn (hQ hh))
  apply hx
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [wallParticularTensor,wallMatrix,ha₀,hq₀]

def wallParticularResidual (χ v r₁ r₂ : Box3 → ℝ) (j : Fin 2) (x : Coord3) : ℝ :=
  ![r₁ (boxCoordinates x),r₂ (boxCoordinates x)] j-
    symmetricSource (wallParticularTensor χ v r₁ r₂) (wallCoordinatePair v) j x

end ScalarConductivity



namespace ScalarConductivity
open Set MeasureTheory Matrix Filter Topology

theorem wallParticularResidual_moments {χ v r₁ r₂ : Box3 → ℝ}
    (hχ : ContDiff ℝ (↑(⊤ : ℕ∞)) χ) (hsχ : HasCompactSupport χ)
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v)
    (h₁ : ContDiff ℝ (↑(⊤ : ℕ∞)) r₁) (h₂ : ContDiff ℝ (↑(⊤ : ℕ∞)) r₂)
    (hs₁ : HasCompactSupport r₁) (hs₂ : HasCompactSupport r₂)
    (hne : ∀ p∈tsupport χ,wallQuotient (wallDerivative v) p≠0) :
    let R := wallParticularResidual χ v r₁ r₂
    let u := wallCoordinatePair v
    (∀ j,ContDiff ℝ (↑(⊤ : ℕ∞)) (R j)) ∧
    (∀ j,HasCompactSupport (R j)) ∧
    (∫ x,R 0 x)=(∫ x : Coord3,r₁ (boxCoordinates x)) ∧
    (∫ x,R 1 x)=(∫ x : Coord3,r₂ (boxCoordinates x)) ∧
    (∫ x,u x 1*R 0 x-u x 0*R 1 x)=
      (∫ x : Coord3,u x 1*r₁ (boxCoordinates x)-u x 0*r₂ (boxCoordinates x)) := by
  dsimp only
  let H := wallParticularTensor χ v r₁ r₂
  let u := wallCoordinatePair v
  obtain ⟨hsm,hcmp,_,hm₁,hm₂,hm₃⟩ := wallParticularTensor_weak_moments hχ hsχ hv h₁ h₂ hne
  have hr₁ : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => r₁ (boxCoordinates x)) := h₁.comp boxCoordinates.contDiff
  have hr₂ : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => r₂ (boxCoordinates x)) := h₂.comp boxCoordinates.contDiff
  have hs₁' : HasCompactSupport (fun x => r₁ (boxCoordinates x)) :=
    hs₁.comp_homeomorph boxCoordinates.toHomeomorph
  have hs₂' : HasCompactSupport (fun x => r₂ (boxCoordinates x)) :=
    hs₂.comp_homeomorph boxCoordinates.toHomeomorph
  have hu : ContDiff ℝ (↑(⊤ : ℕ∞)) u := wallCoordinatePair_smooth hv
  have hu₀ := contDiff_pi.mp hu 0
  have hu₁ := contDiff_pi.mp hu 1
  have hI₁ := hr₁.continuous.integrable_of_hasCompactSupport (μ:=volume) hs₁'
  have hI₂ := hr₂.continuous.integrable_of_hasCompactSupport (μ:=volume) hs₂'
  have hS₁ := (hsm 0).continuous.integrable_of_hasCompactSupport (μ:=volume) (hcmp 0)
  have hS₂ := (hsm 1).continuous.integrable_of_hasCompactSupport (μ:=volume) (hcmp 1)
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro j
    fin_cases j
    · exact hr₁.sub (hsm 0)
    · exact hr₂.sub (hsm 1)
  · intro j
    fin_cases j
    · exact hs₁'.sub (hcmp 0)
    · exact hs₂'.sub (hcmp 1)
  · change (∫ x,r₁ (boxCoordinates x)-symmetricSource H u 0 x)=_
    rw [integral_sub hI₁ hS₁,hm₁,sub_zero]
  · change (∫ x,r₂ (boxCoordinates x)-symmetricSource H u 1 x)=_
    rw [integral_sub hI₂ hS₂,hm₂,sub_zero]
  · have hI : Integrable (fun x => u x 1*r₁ (boxCoordinates x)-u x 0*r₂ (boxCoordinates x)) :=
      ((hu₁.mul hr₁).continuous.integrable_of_hasCompactSupport hs₁'.mul_left).sub
        ((hu₀.mul hr₂).continuous.integrable_of_hasCompactSupport hs₂'.mul_left)
    have hS : Integrable (fun x => u x 1*symmetricSource H u 0 x-u x 0*symmetricSource H u 1 x) :=
      ((hu₁.mul (hsm 0)).continuous.integrable_of_hasCompactSupport (hcmp 0).mul_left).sub
        ((hu₀.mul (hsm 1)).continuous.integrable_of_hasCompactSupport (hcmp 1).mul_left)
    have he : (fun x => u x 1*wallParticularResidual χ v r₁ r₂ 0 x-
        u x 0*wallParticularResidual χ v r₁ r₂ 1 x)=
        fun x => (u x 1*r₁ (boxCoordinates x)-u x 0*r₂ (boxCoordinates x))-
          (u x 1*symmetricSource H u 0 x-u x 0*symmetricSource H u 1 x) := by
      funext x
      simp only [wallParticularResidual,Matrix.cons_val_zero,Matrix.cons_val_one]
      ring
    change (∫ x,u x 1*wallParticularResidual χ v r₁ r₂ 0 x-
      u x 0*wallParticularResidual χ v r₁ r₂ 1 x)=_
    rw [he,integral_sub hI hS,hm₃,sub_zero]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Walls_ParametricWallOperators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise
variable {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [ProperSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

lemma wallQuotient_parametric_smooth {f : P×(E×ℝ) → ℝ}
    (hf : ContDiff ℝ (↑(⊤:ℕ∞)) f) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (fun q : P×(E×ℝ) => wallQuotient (fun x => f (q.1,x)) q.2) := by
  apply contDiff_compact_integral (μ:=volume) (K:=Icc (0:ℝ) 1)
    (F:=fun z : (P×(E×ℝ))×ℝ => wallDerivative (fun x => f (z.1.1,x))
      (z.1.2.1,z.2*z.1.2.2)) _ isCompact_Icc
  exact (wallDerivative_parametric_smooth hf).comp
    (contDiff_fst.fst.prodMk (contDiff_fst.snd.fst.prodMk
      (contDiff_snd.mul contDiff_fst.snd.snd)))

lemma wallParticularNumerator_parametric_smooth (d : E) {v r₁ r₂ : P×(E×ℝ) → ℝ}
    (hv : ContDiff ℝ (↑(⊤:ℕ∞)) v) (h₁ : ContDiff ℝ (↑(⊤:ℕ∞)) r₁)
    (h₂ : ContDiff ℝ (↑(⊤:ℕ∞)) r₂) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (fun q : P×(E×ℝ) =>
      wallParticularNumerator d (fun x => v (q.1,x)) (fun x => r₁ (q.1,x)) (fun x => r₂ (q.1,x)) q.2) := by
  exact (wallPrimitive_parametric_smooth (h₂.sub (wallAlong_parametric_smooth d
    ((wallPrimitive_parametric_smooth h₁).mul (wallDerivative_parametric_smooth hv))))).sub
    ((wallPrimitive_parametric_smooth h₁).mul (wallAlong_parametric_smooth d hv))

omit [ProperSpace P] [ProperSpace E] in
lemma wallHomogeneousNumerator_parametric_smooth (d : E) {v : P×(E×ℝ) → ℝ} {a : P×E → ℝ}
    (hv : ContDiff ℝ (↑(⊤:ℕ∞)) v) (ha : ContDiff ℝ (↑(⊤:ℕ∞)) a) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (fun q : P×(E×ℝ) =>
      wallHomogeneousNumerator d (fun x => v (q.1,x)) (fun x => a (q.1,x)) q.2) := by
  have hA : ContDiff ℝ (↑(⊤:ℕ∞)) (fun q : P×(E×ℝ) => a (q.1,q.2.1)) :=
    ha.comp (contDiff_fst.prodMk contDiff_snd.fst)
  have hm : ContDiff ℝ (↑(⊤:ℕ∞)) (fun q : P×(E×ℝ) => (q.1,(q.2.1,(0:ℝ)))) :=
    contDiff_fst.prodMk (contDiff_snd.fst.prodMk contDiff_const)
  have hs := wallAlong_parametric_smooth d hv
  exact ((contDiff_const.mul hA).mul (hs.sub (hs.comp hm))).sub
    ((wallAlong_parametric_smooth d hA).mul (hv.sub (hv.comp hm)))

lemma parametric_smooth_wall_cutoff_ratio {χ : E×ℝ → ℝ} {f g : P×(E×ℝ) → ℝ}
    (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ) (hf : ContDiff ℝ (↑(⊤:ℕ∞)) f)
    (hg : ContDiff ℝ (↑(⊤:ℕ∞)) g) {V : Set P} (hV : IsOpen V)
    (hne : ∀ p∈V,∀ x∈tsupport χ,wallQuotient (fun y => g (p,y)) x≠0) :
    ContDiffOn ℝ (↑(⊤:ℕ∞)) (fun q : P×(E×ℝ) =>
      χ q.2*(wallQuotient (fun x => f (q.1,x)) q.2 / wallQuotient (fun x => g (q.1,x)) q.2))
      (V×ˢuniv) := by
  apply (hV.prod isOpen_univ).contDiffOn_iff.mpr
  intro q hq
  by_cases hx : q.2∈tsupport χ
  · exact (hχ.comp contDiff_snd).contDiffAt.mul
      ((wallQuotient_parametric_smooth hf).contDiffAt.div
        (wallQuotient_parametric_smooth hg).contDiffAt (hne q.1 hq.1 q.2 hx))
  · apply (show ContDiffAt ℝ (↑(⊤:ℕ∞)) (fun _ : P×(E×ℝ) => (0:ℝ)) q from
      contDiffAt_const).congr_of_eventuallyEq
    have he := continuous_snd.continuousAt.eventually (notMem_tsupport_iff_eventuallyEq.mp hx)
    filter_upwards [he] with z hz
    change χ z.2=0 at hz
    simp only [hz,zero_mul]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Walls_ParametricWallTensors
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace _root_.OAI.ScalarConductivity.centralMeasure_finite _root_.OAI.ScalarConductivity.instCoeFunSubtypeForallBox3RealMemSubmoduleCentralSmoothFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [ProperSpace P]

lemma wallParticularTensor_parametric_smoothOn {χ : Box3 → ℝ}
    {v r₁ r₂ : P×Box3 → ℝ} (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ)
    (hv : ContDiff ℝ (↑(⊤:ℕ∞)) v) (h₁ : ContDiff ℝ (↑(⊤:ℕ∞)) r₁)
    (h₂ : ContDiff ℝ (↑(⊤:ℕ∞)) r₂) {V : Set P} (hV : IsOpen V)
    (hne : ∀ p∈V,∀ x∈tsupport χ,
      wallQuotient (wallDerivative (fun y => v (p,y))) x≠0) :
    ContDiffOn ℝ (↑(⊤:ℕ∞)) (fun q : P×Coord3 =>
      wallParticularTensor χ (fun y => v (q.1,y)) (fun y => r₁ (q.1,y)) (fun y => r₂ (q.1,y)) q.2)
      (V×ˢuniv) := by
  unfold wallParticularTensor
  apply wallMatrix_parametric_smoothOn
    (A:=fun q : P×Box3 => χ q.2*wallPrimitive (fun y => r₁ (q.1,y)) q.2)
    (B:=fun q : P×Box3 => χ q.2*(wallQuotient
      (wallParticularNumerator (1,0) (fun y => v (q.1,y)) (fun y => r₁ (q.1,y))
        (fun y => r₂ (q.1,y))) q.2 / wallQuotient (wallDerivative (fun y => v (q.1,y))) q.2))
  · exact ((hχ.comp contDiff_snd).mul (wallPrimitive_parametric_smooth h₁)).contDiffOn
  · exact parametric_smooth_wall_cutoff_ratio hχ
      (wallParticularNumerator_parametric_smooth (1,0) hv h₁ h₂)
      (wallDerivative_parametric_smooth hv) hV hne

lemma wallHomogeneousTensor_parametric_smoothOn {χ : Box3 → ℝ}
    {v : P×Box3 → ℝ} {a : P×(ℝ×ℝ) → ℝ} (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ)
    (hv : ContDiff ℝ (↑(⊤:ℕ∞)) v) (ha : ContDiff ℝ (↑(⊤:ℕ∞)) a)
    {V : Set P} (hV : IsOpen V)
    (hne : ∀ p∈V,∀ x∈tsupport χ,
      wallQuotient (wallDerivative (fun y => v (p,y))) x≠0) :
    ContDiffOn ℝ (↑(⊤:ℕ∞)) (fun q : P×Coord3 =>
      wallHomogeneousTensor χ (fun y => v (q.1,y)) (fun y => a (q.1,y)) q.2) (V×ˢuniv) := by
  unfold wallHomogeneousTensor
  apply wallMatrix_parametric_smoothOn
    (A:=fun q : P×Box3 => χ q.2*a (q.1,q.2.1))
    (B:=fun q : P×Box3 => χ q.2*(wallQuotient
      (wallHomogeneousNumerator (1,0) (fun y => v (q.1,y)) (fun y => a (q.1,y))) q.2 /
        wallQuotient (wallDerivative (fun y => v (q.1,y))) q.2))
  · exact ((hχ.comp contDiff_snd).mul
      (ha.comp (contDiff_fst.prodMk contDiff_snd.fst))).contDiffOn
  · exact parametric_smooth_wall_cutoff_ratio hχ (wallHomogeneousNumerator_parametric_smooth (1,0) hv ha)
      (wallDerivative_parametric_smooth hv) hV hne

lemma wallParticularTensor_zero (χ v : Box3 → ℝ) :
    wallParticularTensor χ v (fun _ => 0) (fun _ => 0)=0 := by
  have hP : wallPrimitive (fun _ : Box3 => (0:ℝ))=fun _ => 0 := by
    funext x; simp [wallPrimitive]
  have hG : wallParticularNumerator (1,0) v (fun _ => 0) (fun _ => 0)=fun _ => 0 := by
    funext x
    simp [wallParticularNumerator,hP,wallAlong]
  funext x
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [wallParticularTensor,wallMatrix,hP,hG,wallQuotient,wallDerivative]

lemma wallHomogeneousTensor_zero (χ v : Box3 → ℝ) :
    wallHomogeneousTensor χ v (fun _ => 0)=0 := by
  have hG : wallHomogeneousNumerator (1,0) v (fun _ => 0)=fun _ => 0 := by
    funext x; simp [wallHomogeneousNumerator,wallAlong]
  funext x
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [wallHomogeneousTensor,wallMatrix,hG,wallQuotient,wallDerivative]

lemma wallParticularResidual_parametric_smoothOn {χ : Box3 → ℝ}
    {v r₁ r₂ : P×Box3 → ℝ} (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ)
    (hv : ContDiff ℝ (↑(⊤:ℕ∞)) v) (h₁ : ContDiff ℝ (↑(⊤:ℕ∞)) r₁)
    (h₂ : ContDiff ℝ (↑(⊤:ℕ∞)) r₂) {V : Set P} (hV : IsOpen V)
    (hne : ∀ p∈V,∀ x∈tsupport χ,
      wallQuotient (wallDerivative (fun y => v (p,y))) x≠0) (j : Fin 2) :
    ContDiffOn ℝ (↑(⊤:ℕ∞)) (fun q : P×Coord3 =>
      wallParticularResidual χ (fun y => v (q.1,y)) (fun y => r₁ (q.1,y)) (fun y => r₂ (q.1,y)) j q.2)
      (V×ˢuniv) := by
  have hs := symmetricSource_parametric_smoothOn (hV.prod isOpen_univ)
    (wallParticularTensor_parametric_smoothOn hχ hv h₁ h₂ hV hne)
    (wallCoordinatePair_parametric_smooth hv).contDiffOn j
  have hm : ContDiff ℝ (↑(⊤:ℕ∞)) (fun q : P×Coord3 => (q.1,boxCoordinates q.2)) :=
    contDiff_fst.prodMk (boxCoordinates.contDiff.comp contDiff_snd)
  fin_cases j
  · exact (h₁.comp hm).contDiffOn.sub hs
  · exact (h₂.comp hm).contDiffOn.sub hs

end ScalarConductivity

end


noncomputable section
namespace ScalarConductivity
open Set Matrix MeasureTheory Filter Topology

lemma wallPositiveCut_indicator {δ : ℝ} (hδ : 0<δ) {f : Coord3 → ℝ}
    (hs : ∀ x∈tsupport f,δ≤|x 2|) :
    wallPositiveCut δ f={x : Coord3 | 0<x 2}.indicator f := by
  funext x
  by_cases hx : 0<x 2
  · rw [indicator_of_mem (show x∈{x : Coord3 | 0<x 2} from hx)]
    by_cases hf : f x=0
    · simp [wallPositiveCut,hf]
    · have hbound := hs x (subset_tsupport f hf)
      rw [abs_of_pos hx] at hbound
      simp only [wallPositiveCut,Real.smoothTransition.one_of_one_le ((le_div_iff₀ hδ).mpr (by simpa using hbound)),one_mul]
  · rw [indicator_of_notMem (show x∉{x : Coord3 | 0<x 2} from hx)]
    exact mul_eq_zero_of_left (Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (le_of_not_gt hx) hδ.le)) _

lemma wallPositiveCut_tsupport {δ : ℝ} (hδ : 0<δ) {f : Coord3 → ℝ}
    (hs : ∀ x∈tsupport f,δ≤|x 2|) :
    tsupport (wallPositiveCut δ f)⊆tsupport f∩{x : Coord3 | δ≤x 2} := by
  apply subset_inter tsupport_mul_subset_right
  apply closure_minimal _ (isClosed_le continuous_const (continuous_apply 2))
  intro x hx
  have hf : f x≠0 := fun hh => hx (by simp [hh])
  have hp : 0<x 2 := by
    by_contra hn
    apply hx
    exact mul_eq_zero_of_left (Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) hδ.le)) _
  change δ≤x 2
  simpa only [abs_of_pos hp] using hs x (subset_tsupport f hf)

lemma wallNegativeCut_tsupport {δ : ℝ} (hδ : 0<δ) {f : Coord3 → ℝ}
    (hs : ∀ x∈tsupport f,δ≤|x 2|) :
    tsupport (fun x => f x-wallPositiveCut δ f x)⊆tsupport f∩{x : Coord3 | x 2≤ -δ} := by
  apply subset_inter
  · exact (tsupport_sub _ _).trans (union_subset Subset.rfl tsupport_mul_subset_right)
  · apply closure_minimal _ (isClosed_le (continuous_apply 2) continuous_const)
    intro x hx
    have hf : f x≠0 := fun hh => hx (by simp [wallPositiveCut,hh])
    have hn : x 2≤0 := by
      by_contra hn
      have hp : 0<x 2 := lt_of_not_ge hn
      have he := congrFun (wallPositiveCut_indicator hδ hs) x
      rw [indicator_of_mem (show x∈{x : Coord3 | 0<x 2} from hp)] at he
      exact hx (by change f x-wallPositiveCut δ f x=0; rw [he,sub_self])
    have hh := hs x (subset_tsupport f hf)
    rw [abs_of_nonpos hn] at hh
    change x 2≤ -δ
    linarith

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_FiniteEndingRegularity
attribute [-instance] _root_.OAI.ScalarConductivity.instMeasurableSpaceSymmetric3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

def finiteEndingSymmetricTensor (a J L K : ℝ) (x : Coord3) : Symmetric3 :=
  ⟨finiteEndingTensor a J L K x,finiteEndingTensor_symm a J L K x⟩

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_AlignedEndingRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix

def delayedEndingValue (lam k J L K R : ℝ) (x : Coord3) : ℝ :=
  exp (-lam*R)*alignedEndingValue lam k J L K (x-Pi.single 0 R)

def matchedEndingPair (u : Coord3 → Fin 2 → ℝ) (lam k J L K : ℝ) (x : Coord3) : Fin 2 → ℝ :=
  if x 0<13/2 then u x else ![x 0,delayedEndingValue lam k J L K 7 x]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_DelayedEndingRegularity
attribute [-instance] _root_.OAI.ScalarConductivity.instMeasurableSpaceSymmetric3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

def delayedEndingSymmetricTensor (lam k J L K R : ℝ) (x : Coord3) : Symmetric3 :=
  alignedEndingSymmetricTensor lam k J L K (x-Pi.single 0 R)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_AxialFluxBlend
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix

def delayedEndingTensor (lam k J L K R : ℝ) (x : Coord3) : Mat3 :=
  alignedEndingTensor lam k J L K (x-Pi.single 0 R)

def delayedEndingPotential (lam k J L K R : ℝ) (i j : Fin 3) (x : Coord3) : ℝ :=
  exp (-lam*R)*alignedEndingPotential lam k J L K i j (x-Pi.single 0 R)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_CompactRegularC0
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace _root_.OAI.ScalarConductivity.centralMeasure_finite _root_.OAI.ScalarConductivity.instCoeFunSubtypeForallBox3RealMemSubmoduleCentralSmoothFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

theorem compact_regular_box_correction_C0 {a b c d : Fin 3 → ℝ}
    (hab : ∀ i,a i<b i) (hca : ∀ i,c i<a i) (hbd : ∀ i,b i<d i) :
    ∃ L : ℝ,0<L ∧ ∀ (r₁ r₂ : Box3 → ℝ),
      ContDiff ℝ (↑(⊤ : ℕ∞)) r₁ → ContDiff ℝ (↑(⊤ : ℕ∞)) r₂ →
      HasCompactSupport r₁ → HasCompactSupport r₂ →
      tsupport r₁⊆(Ioo (a 0) (b 0) ×ˢ Ioo (a 1) (b 1)) ×ˢ Ioo (a 2) (b 2) →
      tsupport r₂⊆(Ioo (a 0) (b 0) ×ˢ Ioo (a 1) (b 1)) ×ˢ Ioo (a 2) (b 2) →
      (∫ p,r₁ p)=0 → (∫ p,r₂ p)=0 →
      (∫ p,p.1.2*r₁ p-p.1.1*r₂ p)=0 → ∀ M : ℝ,0≤M →
      UniformC1Bound r₁ M → UniformC1Bound r₂ M →
    ∃ H : Fin 3 → Fin 3 → Box3 → ℝ,
      (∀ i j, ContDiff ℝ (↑(⊤ : ℕ∞)) (H i j)) ∧
      (∀ i j, HasCompactSupport (H i j)) ∧
      (∀ i j, tsupport (H i j)⊆(Icc (c 0) (d 0) ×ˢ Icc (c 1) (d 1)) ×ˢ Icc (c 2) (d 2)) ∧
      (∀ i j p,H i j p=H j i p) ∧
      (∀ p,cubePartial (H 0 0) ((1,0),0) p+cubePartial (H 1 0) ((0,1),0) p+
        cubePartial (H 2 0) ((0,0),1) p=r₁ p) ∧
      (∀ p,cubePartial (H 0 1) ((1,0),0) p+cubePartial (H 1 1) ((0,1),0) p+
        cubePartial (H 2 1) ((0,0),1) p=r₂ p) ∧
      (∀ i j p,|H i j p|≤L*M) := by
  have hcd : ∀ i,c i<d i := fun i => (hca i).trans ((hab i).trans (hbd i))
  obtain ⟨D₀,hD₀,solve₀⟩ := compact_box_divergence_C1 hab
  obtain ⟨D₁,hD₁,solve₁⟩ := compact_box_divergence_C1 hcd
  let L := D₀+2*D₁*D₀
  refine ⟨L,by dsimp [L]; positivity,?_⟩
  intro r₁ r₂ hr₁ hr₂ hs₁ hs₂ hv₁ hv₂ hz₁ hz₂ ht M hM hb₁ hb₂
  obtain ⟨F₁,F₂,F₃,hF₁,hF₂,hF₃,hsF₁,hsF₂,hsF₃,hdF,htF,hbF₁,hbF₂,hbF₃⟩ := solve₀ r₁ hr₁ hs₁ hv₁ hz₁ M hM hb₁
  obtain ⟨G₁,G₂,G₃,hG₁,hG₂,hG₃,hsG₁,hsG₂,hsG₃,hdG,htG,hbG₁,hbG₂,hbG₃⟩ := solve₀ r₂ hr₂ hs₂ hv₂ hz₂ M hM hb₂
  have hf₁ : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun p : Box3 => p.1.1) := contDiff_fst.comp contDiff_fst
  have hf₂ : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun p : Box3 => p.1.2) := contDiff_snd.comp contDiff_fst
  have hIF := cube_coordinate_divergence_moment hF₁ hF₂ hF₃ hsF₁ hsF₂ hsF₃ hdF hf₂
  have hIG := cube_coordinate_divergence_moment hG₁ hG₂ hG₃ hsG₁ hsG₂ hsG₃ hdG hf₁
  simp only [cubePartial_fst_fst,cubePartial_snd_fst,zero_mul,one_mul,integral_zero,neg_zero,
    sub_zero,zero_sub] at hIF hIG
  have hi₁ : Integrable (fun p : Box3 => p.1.2*r₁ p) := (hf₂.continuous.mul hr₁.continuous).integrable_of_hasCompactSupport (μ := volume) hs₁.mul_left
  have hi₂ : Integrable (fun p : Box3 => p.1.1*r₂ p) := (hf₁.continuous.mul hr₂.continuous).integrable_of_hasCompactSupport (μ := volume) hs₂.mul_left
  have hzq : (∫ p,F₂ p-G₁ p)=0 := by
    rw [integral_sub (hF₂.continuous.integrable_of_hasCompactSupport hsF₂)
      (hG₁.continuous.integrable_of_hasCompactSupport hsG₁)]
    rw [integral_sub hi₁ hi₂,hIF,hIG] at ht
    linarith
  let U := (Icc (c 0) (d 0) ×ˢ Icc (c 1) (d 1)) ×ˢ Icc (c 2) (d 2)
  let V := (Ioo (c 0) (d 0) ×ˢ Ioo (c 1) (d 1)) ×ˢ Ioo (c 2) (d 2)
  have hinner : (Icc (a 0) (b 0) ×ˢ Icc (a 1) (b 1)) ×ˢ Icc (a 2) (b 2) ⊆ V := by
    intro p hp
    exact ⟨⟨⟨(hca 0).trans_le hp.1.1.1,hp.1.1.2.trans_lt (hbd 0)⟩,
      ⟨(hca 1).trans_le hp.1.2.1,hp.1.2.2.trans_lt (hbd 1)⟩⟩,
      ⟨(hca 2).trans_le hp.2.1,hp.2.2.trans_lt (hbd 2)⟩⟩
  have hVU : V⊆U := fun _ hp =>
    ⟨⟨Ioo_subset_Icc_self hp.1.1,Ioo_subset_Icc_self hp.1.2⟩,Ioo_subset_Icc_self hp.2⟩
  have htFV := htF.trans hinner
  have htGV := htG.trans hinner
  have htF₁ : tsupport F₁⊆U := ((subset_union_left.trans subset_union_left).trans htFV).trans hVU
  have htF₂ : tsupport F₂⊆U := ((subset_union_right.trans subset_union_left).trans htFV).trans hVU
  have htF₃ : tsupport F₃⊆U := (subset_union_right.trans htFV).trans hVU
  have htG₁ : tsupport G₁⊆U := ((subset_union_left.trans subset_union_left).trans htGV).trans hVU
  have htG₂ : tsupport G₂⊆U := ((subset_union_right.trans subset_union_left).trans htGV).trans hVU
  have htG₃ : tsupport G₃⊆U := (subset_union_right.trans htGV).trans hVU
  have htq : tsupport (fun p => F₂ p-G₁ p)⊆V :=
    (tsupport_sub _ _).trans (union_subset
      ((subset_union_right.trans subset_union_left).trans htFV)
      ((subset_union_left.trans subset_union_left).trans htGV))
  have hbq : UniformC1Bound (fun p => F₂ p-G₁ p) (2*D₀*M) := by
    convert hbF₂.sub (hF₂.differentiable (by simp)) (hG₁.differentiable (by simp)) hbG₁ using 1
    all_goals try with_reducible_and_instances rfl
    ring
  obtain ⟨h₁,h₂,h₃,hh₁,hh₂,hh₃,hsh₁,hsh₂,hsh₃,hdh,hth,hbh₁,hbh₂,hbh₃⟩ :=
    solve₁ (fun p => F₂ p-G₁ p) (hF₂.sub hG₁) (hsF₂.sub hsG₁) htq hzq
      (2*D₀*M) (by positivity) hbq
  have hth₁ : tsupport h₁⊆U := (subset_union_left.trans subset_union_left).trans hth
  have hth₂ : tsupport h₂⊆U := (subset_union_right.trans subset_union_left).trans hth
  have hth₃ : tsupport h₃⊆U := subset_union_right.trans hth
  let A := fun p => F₁ p+cubePartial h₁ ((0,1),0) p
  let B := fun p => G₁ p+cubePartial h₂ ((0,1),0) p
  let C := fun p => F₃ p+cubePartial h₃ ((0,1),0) p
  let D := fun p => G₂ p-cubePartial h₂ ((1,0),0) p
  let H : Fin 3 → Fin 3 → Box3 → ℝ := ![![A,B,C],![B,D,G₃],![C,G₃,fun _ => 0]]
  have hA := hF₁.add (cubePartial_smooth hh₁ ((0,1),0))
  have hB := hG₁.add (cubePartial_smooth hh₂ ((0,1),0))
  have hC := hF₃.add (cubePartial_smooth hh₃ ((0,1),0))
  have hD := hG₂.sub (cubePartial_smooth hh₂ ((1,0),0))
  have hsA := hsF₁.add (cubePartial_compact hsh₁ ((0,1),0))
  have hsB := hsG₁.add (cubePartial_compact hsh₂ ((0,1),0))
  have hsC := hsF₃.add (cubePartial_compact hsh₃ ((0,1),0))
  have hsD := hsG₂.sub (cubePartial_compact hsh₂ ((1,0),0))
  have hB' : B=(fun p => F₂ p-cubePartial h₁ ((1,0),0) p-cubePartial h₃ ((0,0),1) p) := by
    funext p
    change G₁ p+cubePartial h₂ ((0,1),0) p=_
    linarith [hdh p]
  have htA : tsupport A⊆U := (tsupport_add _ _).trans
    (union_subset htF₁ ((cubePartial_tsupport _).trans hth₁))
  have htB : tsupport B⊆U := (tsupport_add _ _).trans
    (union_subset htG₁ ((cubePartial_tsupport _).trans hth₂))
  have htC : tsupport C⊆U := (tsupport_add _ _).trans
    (union_subset htF₃ ((cubePartial_tsupport _).trans hth₃))
  have htD : tsupport D⊆U := (tsupport_sub _ _).trans
    (union_subset htG₂ ((cubePartial_tsupport _).trans hth₂))
  have ht0 : tsupport (fun _ : Box3 => (0:ℝ))⊆U := by simp
  refine ⟨H,?_,?_,?_,?_,?_,?_,?_⟩
  · intro i j; fin_cases i <;> fin_cases j
    all_goals first | exact hA | exact hB | exact hC | exact hD | exact hG₃ | exact contDiff_const
  · intro i j; fin_cases i <;> fin_cases j
    all_goals first | exact hsA | exact hsB | exact hsC | exact hsD | exact hsG₃ | exact HasCompactSupport.zero
  · intro i j; fin_cases i <;> fin_cases j
    all_goals first | exact htA | exact htB | exact htC | exact htD | exact htG₃ | exact ht0
  · intro i j p; fin_cases i <;> fin_cases j <;> rfl
  · intro p
    change cubePartial A ((1,0),0) p+cubePartial B ((0,1),0) p+cubePartial C ((0,0),1) p=r₁ p
    rw [hB']
    change cubePartial (fun p => F₁ p+cubePartial h₁ ((0,1),0) p) ((1,0),0) p+
      cubePartial (fun p => F₂ p-cubePartial h₁ ((1,0),0) p-cubePartial h₃ ((0,0),1) p) ((0,1),0) p+
      cubePartial (fun p => F₃ p+cubePartial h₃ ((0,1),0) p) ((0,0),1) p=r₁ p
    rw [cubePartial_add (hF₁.differentiable (by simp)) ((cubePartial_smooth hh₁ _).differentiable (by simp)),
      cubePartial_sub ((hF₂.sub (cubePartial_smooth hh₁ _)).differentiable (by simp))
        ((cubePartial_smooth hh₃ _).differentiable (by simp)),
      cubePartial_sub (hF₂.differentiable (by simp)) ((cubePartial_smooth hh₁ _).differentiable (by simp)),
      cubePartial_add (hF₃.differentiable (by simp)) ((cubePartial_smooth hh₃ _).differentiable (by simp)),
      cubePartial_commute hh₁ ((0,1),0) ((1,0),0),cubePartial_commute hh₃ ((0,1),0) ((0,0),1)]
    linarith [hdF p]
  · intro p
    change cubePartial B ((1,0),0) p+cubePartial D ((0,1),0) p+cubePartial G₃ ((0,0),1) p=r₂ p
    change cubePartial (fun p => G₁ p+cubePartial h₂ ((0,1),0) p) ((1,0),0) p+
      cubePartial (fun p => G₂ p-cubePartial h₂ ((1,0),0) p) ((0,1),0) p+
      cubePartial G₃ ((0,0),1) p=r₂ p
    rw [cubePartial_add (hG₁.differentiable (by simp)) ((cubePartial_smooth hh₂ _).differentiable (by simp)),
      cubePartial_sub (hG₂.differentiable (by simp)) ((cubePartial_smooth hh₂ _).differentiable (by simp)),
      cubePartial_commute hh₂ ((0,1),0) ((1,0),0)]
    linarith [hdG p]

  · have hcomb (f g : Box3 → ℝ) (hf : UniformC1Bound f (D₀*M))
        (hg : UniformC1Bound g (D₁*(2*D₀*M))) (v : Box3) (hv : ‖v‖≤1) (p : Box3) :
        |f p+cubePartial g v p|≤L*M ∧ |f p-cubePartial g v p|≤L*M := by
      have hd := cubePartial_bound_of_C1 hg hv p
      have he : D₀*M+D₁*(2*D₀*M)=L*M := by dsimp [L]; ring
      exact ⟨(abs_add_le _ _).trans ((add_le_add (hf p).1 hd).trans_eq he),
        (abs_sub _ _).trans ((add_le_add (hf p).1 hd).trans_eq he)⟩
    have hA₀ (p : Box3) : |A p|≤L*M := (hcomb F₁ h₁ hbF₁ hbh₁ ((0,1),0) (by simp [Prod.norm_def]) p).1
    have hB₀ (p : Box3) : |B p|≤L*M := (hcomb G₁ h₂ hbG₁ hbh₂ ((0,1),0) (by simp [Prod.norm_def]) p).1
    have hC₀ (p : Box3) : |C p|≤L*M := (hcomb F₃ h₃ hbF₃ hbh₃ ((0,1),0) (by simp [Prod.norm_def]) p).1
    have hD₀' (p : Box3) : |D p|≤L*M := (hcomb G₂ h₂ hbG₂ hbh₂ ((1,0),0) (by simp [Prod.norm_def]) p).2
    have hG₀ (p : Box3) : |G₃ p|≤L*M := (hbG₃ p).1.trans
      (mul_le_mul_of_nonneg_right (by dsimp [L]; exact le_add_of_nonneg_right (by positivity)) hM)
    intro i j p
    fin_cases i <;> fin_cases j
    all_goals first | exact hA₀ p | exact hB₀ p | exact hC₀ p | exact hD₀' p | exact hG₀ p | skip
    change |(0:ℝ)|≤L*M
    rw [abs_zero]
    dsimp [L]
    positivity

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_MetricControlledPiola
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

theorem localPiolaSource_inverse_C1_of_bounds
    (X : OpenPartialHomeomorph Coord3 Coord3)
    (hX : ContDiffOn ℝ (↑(⊤:ℕ∞)) X X.source)
    (hXi : ContDiffOn ℝ (↑(⊤:ℕ∞)) X.symm X.target)
    {K : Set Coord3} (hKs : K⊆X.source) {B : ℝ} (hB : 0<B)
    (hwb : ∀ x∈K,|inverseSourceWeight X x|≤B ∧ ‖fderiv ℝ (inverseSourceWeight X) x‖≤B)
    (hDX : ∀ x∈K,‖fderiv ℝ X x‖≤B)
    (r : Coord3 → ℝ) (hr : ContDiff ℝ (↑(⊤:ℕ∞)) r)
    (hc : HasCompactSupport r) (hs : tsupport r⊆X '' K)
    (M : ℝ) (hM : 0≤M) (hb : UniformC1Bound r M) :
    UniformC1Bound (localPiolaSource X.symm r) (B*(B+1)*M) := by
  let w := inverseSourceWeight X
  have hw := inverseSourceWeight_smooth X hX hXi
  let p := localPiolaSource X.symm r
  have hps : tsupport p⊆K := localPiolaSource_inverse_support X r hc hKs hs
  intro x
  change |p x|≤B*(B+1)*M ∧ ‖fderiv ℝ p x‖≤B*(B+1)*M
  by_cases hx : x∈K
  · have hxs := hX.contDiffAt (X.open_source.mem_nhds (hKs hx))
    have hws := hw.contDiffAt (X.open_source.mem_nhds (hKs hx))
    have he : p=ᶠ[𝓝 x] (fun y => w y*r (X y)) := by
      filter_upwards [X.open_source.mem_nhds (hKs hx)] with y hy
      simp [p,localPiolaSource,hy,w,inverseSourceWeight]
    have hrc : DifferentiableAt ℝ (fun y => r (X y)) x :=
      (hr.differentiable (by simp) (X x)).comp x (hxs.differentiableAt (by simp))
    refine ⟨?_,?_⟩
    · rw [he.eq_of_nhds,abs_mul]
      exact (mul_le_mul (hwb x hx).1 (hb (X x)).1 (abs_nonneg _) hB.le).trans
        (by nlinarith [mul_nonneg hB.le hM,sq_nonneg B])
    · rw [he.fderiv_eq,fderiv_fun_mul (hws.differentiableAt (by simp)) hrc]
      have hchain := ((hr.differentiable (by simp) (X x)).hasFDerivAt.comp x
        (hxs.differentiableAt (by simp)).hasFDerivAt).fderiv
      have hcomp : ‖fderiv ℝ (fun y => r (X y)) x‖≤M*B := by
        change ‖fderiv ℝ (r ∘ X) x‖≤_
        rw [hchain]
        exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul (hb (X x)).2 (hDX x hx) (norm_nonneg _) hM)
      calc
        _ ≤ ‖w x • fderiv ℝ (fun y => r (X y)) x‖+‖r (X x) • fderiv ℝ w x‖ := norm_add_le _ _
        _ = |w x| *‖fderiv ℝ (fun y => r (X y)) x‖+|r (X x)| *‖fderiv ℝ w x‖ := by
          simp only [norm_smul,Real.norm_eq_abs]
        _ ≤ B*(M*B)+M*B := add_le_add
          (mul_le_mul (hwb x hx).1 hcomp (norm_nonneg _) hB.le)
          (mul_le_mul (hb (X x)).1 (hwb x hx).2 (norm_nonneg _) hM)
        _ = _ := by ring
  · have hn : x∉tsupport p := fun h => hx (hps h)
    rw [image_eq_zero_of_notMem_tsupport hn,fderiv_of_notMem_tsupport ℝ hn,abs_zero,norm_zero]
    exact ⟨by positivity,by positivity⟩

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Walls_WallSideMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix Filter Topology
open scoped Matrix.Norms.Elementwise

lemma symmetricSource_compactSmoothPair {H : Coord3 → Mat3} {u : Coord3 → Fin 2 → ℝ}
    (hH : ContDiff ℝ (↑(⊤:ℕ∞)) H) (hc : HasCompactSupport H)
    (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u) : CompactSmoothPair (symmetricSource H u) :=
  fun j => ⟨coordinateDivergence_smooth (symmetricFlux_smooth hH hu j),
    coordinateDivergence_compact (symmetricFlux_compact hc u j)⟩

lemma physicalSourceMoment_symmetricSource {H : Coord3 → Mat3} {u : Coord3 → Fin 2 → ℝ}
    (hH : ContDiff ℝ (↑(⊤:ℕ∞)) H) (hc : HasCompactSupport H)
    (hsy : ∀ x,(H x).IsSymm) (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u) :
    physicalSourceMoment u (symmetricSource H u)=0 := by
  have hh := (symmetric_cutoff_sources H hH hc hsy u hu).2.2.2
  ext i
  fin_cases i
  · exact hh.1
  · exact hh.2.1
  · exact hh.2.2

lemma wallPositiveCut_sub (δ : ℝ) (f g : Coord3 → ℝ) :
    wallPositiveCut δ (f-g)=wallPositiveCut δ f-wallPositiveCut δ g := by
  funext x
  simp only [wallPositiveCut,Pi.sub_apply,mul_sub]

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_WallParticularFamily
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace _root_.OAI.ScalarConductivity.centralMeasure_finite _root_.OAI.ScalarConductivity.instCoeFunSubtypeForallBox3RealMemSubmoduleCentralSmoothFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Matrix Filter Topology
open scoped Matrix.Norms.Elementwise
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

def wallInputPair (r : Fin 2 → P×Box3 → ℝ) (p : P) : PhysicalSourcePair :=
  fun j x => r j (p,boxCoordinates x)

def wallParticularFamily (χ : Box3 → ℝ) (v : P×Box3 → ℝ)
    (r : Fin 2 → P×Box3 → ℝ) (q : P×Coord3) : Mat3 :=
  wallParticularTensor χ (fun y => v (q.1,y))
    (fun y => r 0 (q.1,y)) (fun y => r 1 (q.1,y)) q.2

def wallResidualFamily (χ : Box3 → ℝ) (v : P×Box3 → ℝ)
    (r : Fin 2 → P×Box3 → ℝ) (j : Fin 2) (q : P×Coord3) : ℝ :=
  wallParticularResidual χ (fun y => v (q.1,y))
    (fun y => r 0 (q.1,y)) (fun y => r 1 (q.1,y)) j q.2

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] in
lemma wallResidualFamily_eq (χ : Box3 → ℝ) (v : P×Box3 → ℝ)
    (r : Fin 2 → P×Box3 → ℝ) (p : P) :
    (fun j x => wallResidualFamily χ v r j (p,x))=
      wallInputPair r p-symmetricSource (fun x => wallParticularFamily χ v r (p,x))
        (wallCoordinatePair (fun y => v (p,y))) := by
  ext j x
  fin_cases j <;> rfl

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] in
lemma wallResidualFamily_zero {χ : Box3 → ℝ} {v : P×Box3 → ℝ}
    {r : Fin 2 → P×Box3 → ℝ} {p : P} (hz : ∀ j y,r j (p,y)=0) (j x) :
    wallResidualFamily χ v r j (p,x)=0 := by
  have he (j) : (fun y => r j (p,y))=fun _ => 0 := funext (hz j)
  dsimp [wallResidualFamily,wallParticularResidual]
  rw [he 0,he 1,wallParticularTensor_zero,symmetricSource_zero]
  fin_cases j <;> simp [hz]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] in
lemma wallParticularFamily_zero {χ : Box3 → ℝ} {v : P×Box3 → ℝ}
    {r : Fin 2 → P×Box3 → ℝ} {p : P} (hz : ∀ j y,r j (p,y)=0) (x) :
    wallParticularFamily χ v r (p,x)=0 := by
  have he (j) : (fun y => r j (p,y))=fun _ => 0 := funext (hz j)
  dsimp [wallParticularFamily]
  rw [he 0,he 1,wallParticularTensor_zero]
  rfl

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] in
lemma wallResidualFamily_tsupport {χ : Box3 → ℝ} {v : P×Box3 → ℝ}
    {r : Fin 2 → P×Box3 → ℝ} {S : Set Box3} {p : P}
    (hχc : HasCompactSupport χ) (hs : ∀ j,tsupport (fun y => r j (p,y))⊆S) (j : Fin 2) :
    tsupport (fun x => wallResidualFamily χ v r j (p,x))⊆boxCoordinates ⁻¹' (S∪tsupport χ) := by
  have he := congrFun (wallResidualFamily_eq χ v r p) j
  rw [he]
  apply (tsupport_sub _ _).trans
  apply union_subset
  · exact (tsupport_comp_subset_preimage (fun y => r j (p,y)) boxCoordinates.continuous).trans
      ((preimage_mono (hs j)).trans (preimage_mono subset_union_left))
  · exact (symmetricSource_tsupport _ _ j).trans
      ((wallParticularTensor_compact (χ:=χ) (v:=fun y => v (p,y))
        (r₁:=fun y => r 0 (p,y)) (r₂:=fun y => r 1 (p,y))
        hχc).2.trans (preimage_mono subset_union_right))

lemma wallParticularFamily_smoothOn {χ : Box3 → ℝ} {v : P×Box3 → ℝ}
    {r : Fin 2 → P×Box3 → ℝ} (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ)
    (hv : ContDiff ℝ (↑(⊤:ℕ∞)) v) (hr : ∀ j,ContDiff ℝ (↑(⊤:ℕ∞)) (r j))
    {V : Set P} (hV : IsOpen V)
    (hne : ∀ p∈V,∀ x∈tsupport χ,wallQuotient (wallDerivative (fun y => v (p,y))) x≠0) :
    ContDiffOn ℝ (↑(⊤:ℕ∞)) (wallParticularFamily χ v r) (V×ˢuniv) :=
  wallParticularTensor_parametric_smoothOn hχ hv (hr 0) (hr 1) hV hne

lemma wallResidualFamily_smoothOn {χ : Box3 → ℝ} {v : P×Box3 → ℝ}
    {r : Fin 2 → P×Box3 → ℝ} (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ)
    (hv : ContDiff ℝ (↑(⊤:ℕ∞)) v) (hr : ∀ j,ContDiff ℝ (↑(⊤:ℕ∞)) (r j))
    {V : Set P} (hV : IsOpen V)
    (hne : ∀ p∈V,∀ x∈tsupport χ,wallQuotient (wallDerivative (fun y => v (p,y))) x≠0) (j) :
    ContDiffOn ℝ (↑(⊤:ℕ∞)) (wallResidualFamily χ v r j) (V×ˢuniv) :=
  wallParticularResidual_parametric_smoothOn hχ hv (hr 0) (hr 1) hV hne j

lemma wallParticularFamily_small {χ : Box3 → ℝ} {v : P×Box3 → ℝ}
    {r : Fin 2 → P×Box3 → ℝ} (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ)
    (hχc : HasCompactSupport χ) (hv : ContDiff ℝ (↑(⊤:ℕ∞)) v)
    (hr : ∀ j,ContDiff ℝ (↑(⊤:ℕ∞)) (r j)) {p : P} {V : Set P}
    (hV : IsOpen V) (hp : p∈V)
    (hne : ∀ p∈V,∀ x∈tsupport χ,wallQuotient (wallDerivative (fun y => v (p,y))) x≠0)
    (hz : ∀ j y,r j (p,y)=0) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ q in 𝓝 p,∀ x,‖wallParticularFamily χ v r (q,x)‖≤ε := by
  apply compact_parametric_norm_small_global (f:=wallParticularFamily χ v r) (p:=p)
    (boxCoordinates.toHomeomorph.isCompact_preimage.mpr hχc)
  · intro x _
    exact ((wallParticularFamily_smoothOn hχ hv hr hV hne).contDiffAt
      ((hV.prod isOpen_univ).mem_nhds ⟨hp,mem_univ x⟩)).continuousAt
  · exact wallParticularFamily_zero hz
  · apply Eventually.of_forall
    intro q
    exact (wallParticularTensor_compact (χ:=χ) (v:=fun y => v (q,y))
      (r₁:=fun y => r 0 (q,y)) (r₂:=fun y => r 1 (q,y)) hχc).2
  · exact hε

omit [FiniteDimensional ℝ P] in
lemma wallResidualFamily_moment {χ : Box3 → ℝ} {v : P×Box3 → ℝ}
    {r : Fin 2 → P×Box3 → ℝ} (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ)
    (hχc : HasCompactSupport χ) (hv : ContDiff ℝ (↑(⊤:ℕ∞)) v)
    (hr : ∀ j,ContDiff ℝ (↑(⊤:ℕ∞)) (r j)) {p : P}
    (hrs : ∀ j,HasCompactSupport (fun y => r j (p,y)))
    (hne : ∀ x∈tsupport χ,wallQuotient (wallDerivative (fun y => v (p,y))) x≠0) :
    physicalSourceMoment (wallCoordinatePair (fun y => v (p,y)))
      (fun j x => wallResidualFamily χ v r j (p,x))=
    physicalSourceMoment (wallCoordinatePair (fun y => v (p,y))) (wallInputPair r p) := by
  have hvp : ContDiff ℝ (↑(⊤:ℕ∞)) (fun y => v (p,y)) := hv.comp (contDiff_const.prodMk contDiff_id)
  have hrp (j) : ContDiff ℝ (↑(⊤:ℕ∞)) (fun y => r j (p,y)) := (hr j).comp (contDiff_const.prodMk contDiff_id)
  have hh := wallParticularResidual_moments hχ hχc hvp (hrp 0) (hrp 1) (hrs 0) (hrs 1) hne
  ext i
  fin_cases i
  · exact hh.2.2.1
  · exact hh.2.2.2.1
  · exact hh.2.2.2.2

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_WallParticularFinish
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
open scoped Matrix.Norms.Elementwise
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

omit [FiniteDimensional ℝ P] in
lemma wall_particular_family_finishes
    {χ : Box3 → ℝ} {v : P×Box3 → ℝ} {r : Fin 2 → P×Box3 → ℝ}
    (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ) (hχc : HasCompactSupport χ)
    (hv : ContDiff ℝ (↑(⊤:ℕ∞)) v) (hr : ∀ j,ContDiff ℝ (↑(⊤:ℕ∞)) (r j))
    (q : P) {U : Set Coord3} (hχU : boxCoordinates ⁻¹' tsupport χ⊆U)
    (hrs : ∀ j,HasCompactSupport (fun y => r j (q,y)))
    (hne : ∀ z∈tsupport χ,wallQuotient (wallDerivative (fun y => v (q,y))) z≠0)
    (hm : physicalSourceMoment (wallCoordinatePair (fun y => v (q,y))) (wallInputPair r q)=0)
    {ε : ℝ} (small : ∀ x,‖wallParticularFamily χ v r (q,x)‖≤ε/2)
    (solve : physicalSourceMoment (wallCoordinatePair (fun y => v (q,y)))
        (fun j x => wallResidualFamily χ v r j (q,x))=0 →
      BoundedPhysicallyCorrectable (wallCoordinatePair (fun y => v (q,y))) U
        (fun j x => wallResidualFamily χ v r j (q,x)) (ε/2)) :
    BoundedPhysicallyCorrectable (wallCoordinatePair (fun y => v (q,y))) U (wallInputPair r q) ε := by
  have hvq : ContDiff ℝ (↑(⊤:ℕ∞)) (fun y => v (q,y)) := hv.comp (contDiff_const.prodMk contDiff_id)
  have hrq (j) : ContDiff ℝ (↑(⊤:ℕ∞)) (fun y => r j (q,y)) := (hr j).comp (contDiff_const.prodMk contDiff_id)
  have hRm := (wallResidualFamily_moment hχ hχc hv hr hrs hne).trans hm
  let H : Coord3 → Mat3 := fun x => wallParticularFamily χ v r (q,x)
  have hHs : ContDiff ℝ (↑(⊤:ℕ∞)) H := by
    change ContDiff ℝ (↑(⊤:ℕ∞)) (wallParticularTensor χ (fun y => v (q,y))
      (fun y => r 0 (q,y)) (fun y => r 1 (q,y)))
    exact wallParticularTensor_smooth hχ hvq (hrq 0) (hrq 1) hne
  have hc := wallParticularTensor_compact (χ:=χ) (v:=fun y => v (q,y))
    (r₁:=fun y => r 0 (q,y)) (r₂:=fun y => r 1 (q,y)) hχc
  have hHsolve : BoundedPhysicallyCorrectable (wallCoordinatePair (fun y => v (q,y))) U
      (symmetricSource H (wallCoordinatePair (fun y => v (q,y)))) (ε/2) :=
    ⟨H,hHs,hc.1,hc.2.trans hχU,by
      unfold H wallParticularFamily wallParticularTensor
      intro x
      exact wallMatrix_symmetric _ _ x,fun _ => rfl,small⟩
  have hh := hHsolve.add (wallCoordinatePair_smooth hvq) (solve hRm)
  rw [wallResidualFamily_eq,add_sub_cancel] at hh
  convert hh using 1 <;> first | rfl | ring

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_ParametricMomentSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix Filter Topology

lemma physicalSourceMoment_family_tendsto_zero {P : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    {u : P×Coord3 → Fin 2 → ℝ} (hu : Continuous u)
    {r : Fin 2 → P×Coord3 → ℝ} {p : P} {V : Set P}
    (hV : IsOpen V) (hp : p∈V)
    (hr : ∀ j,ContDiffOn ℝ (↑(⊤:ℕ∞)) (r j) (V×ˢuniv))
    {K : Set Coord3} (hK : IsCompact K)
    (hs : ∀ᶠ q in 𝓝 p,PairSupported (fun j x => r j (q,x)) K)
    (hz : ∀ j x,r j (p,x)=0) :
    Tendsto (fun q => physicalSourceMoment (fun x => u (q,x)) (fun j x => r j (q,x)))
      (𝓝 p) (𝓝 0) := by
  have hcont (j x) : ContinuousAt (r j) (p,x) :=
    ((hr j).contDiffAt ((hV.prod isOpen_univ).mem_nhds ⟨hp,mem_univ x⟩)).continuousAt
  have hc : ∀ᶠ q in 𝓝 p,∀ j,Continuous (fun x => r j (q,x)) := by
    filter_upwards [hV.mem_nhds hp] with q hq j
    exact (hr j).continuousOn.comp_continuous (continuous_const.prodMk continuous_id)
      (fun x => ⟨hq,mem_univ x⟩)
  apply tendsto_pi_nhds.mpr
  intro i
  fin_cases i
  · exact compact_supported_integral_tendsto_zero hK (hcont 0) (hz 0)
      (hc.mono (fun q hh => hh 0)) (hs.mono (fun q hh => hh 0))
  · exact compact_supported_integral_tendsto_zero hK (hcont 1) (hz 1)
      (hc.mono (fun q hh => hh 1)) (hs.mono (fun q hh => hh 1))
  · apply compact_supported_integral_tendsto_zero hK
      (f:=fun q => u q 1*r 0 q-u q 0*r 1 q)
    · intro x
      exact (((continuous_apply 1).comp hu).continuousAt.mul (hcont 0 x)).sub
        (((continuous_apply 0).comp hu).continuousAt.mul (hcont 1 x))
    · intro x; simp only [hz,mul_zero,sub_zero]
    · filter_upwards [hc] with q hq
      exact (((continuous_apply 1).comp (hu.comp (continuous_const.prodMk continuous_id))).mul (hq 0)).sub
        (((continuous_apply 0).comp (hu.comp (continuous_const.prodMk continuous_id))).mul (hq 1))
    · filter_upwards [hs] with q hq
      exact (tsupport_sub _ _).trans (union_subset
        (tsupport_mul_subset_right.trans (hq 0)) (tsupport_mul_subset_right.trans (hq 1)))

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Walls_ParametricWallAmplitude
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace _root_.OAI.ScalarConductivity.centralMeasure_finite _root_.OAI.ScalarConductivity.instCoeFunSubtypeForallBox3RealMemSubmoduleCentralSmoothFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Matrix Filter Topology
open scoped Matrix.Norms.Elementwise

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

def wallTransferFamily (χ : Box3 → ℝ) (v : P×Box3 → ℝ)
    (θ η : ℝ → ℝ) (σ lam : ℝ) (q : (P×Coord3)×Coord3) : Mat3 :=
  wallHomogeneousTensor χ (fun y => v (q.1.1,y))
    (wallMomentAmplitude θ η σ lam q.1.2) q.2

lemma wallTransferFamily_smoothOn {χ : Box3 → ℝ} {v : P×Box3 → ℝ}
    {θ η : ℝ → ℝ} (σ lam : ℝ)
    (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ) (hv : ContDiff ℝ (↑(⊤:ℕ∞)) v)
    (hθ : ContDiff ℝ (↑(⊤:ℕ∞)) θ) (hη : ContDiff ℝ (↑(⊤:ℕ∞)) η)
    {V : Set P} (hV : IsOpen V)
    (hne : ∀ p∈V,∀ x∈tsupport χ,wallQuotient (wallDerivative (fun y => v (p,y))) x≠0) :
    ContDiffOn ℝ (↑(⊤:ℕ∞)) (wallTransferFamily χ v θ η σ lam) ((V×ˢuniv)×ˢuniv) := by
  exact wallHomogeneousTensor_parametric_smoothOn hχ
    (hv.comp (contDiff_fst.fst.prodMk contDiff_snd))
    ((wallMomentAmplitude_parametric_smooth σ lam hθ hη).comp
      (contDiff_fst.snd.prodMk contDiff_snd))
    (hV.prod isOpen_univ) (fun p hp => hne p.1 hp.1)

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] in
lemma wallTransferFamily_zero (χ : Box3 → ℝ) (v : P×Box3 → ℝ)
    (θ η : ℝ → ℝ) (σ lam : ℝ) (p : P) (x : Coord3) :
    wallTransferFamily χ v θ η σ lam ((p,0),x)=0 := by
  dsimp [wallTransferFamily]
  rw [wallMomentAmplitude_zero]
  change wallHomogeneousTensor χ (fun y => v (p,y)) (fun _ => 0) x=0
  rw [wallHomogeneousTensor_zero]
  rfl

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Walls_WallTransferParametric
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace _root_.OAI.ScalarConductivity.centralMeasure_finite _root_.OAI.ScalarConductivity.instCoeFunSubtypeForallBox3RealMemSubmoduleCentralSmoothFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Matrix Filter Topology
open scoped Matrix.Norms.Elementwise
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

def wallTransferSource (χ : Box3 → ℝ) (v : P×Box3 → ℝ)
    (θ η : ℝ → ℝ) (σ lam : ℝ) (j : Fin 2) (q : (P×Coord3)×Coord3) : ℝ :=
  symmetricSource (fun x => wallTransferFamily χ v θ η σ lam (q.1,x))
    (wallCoordinatePair (fun y => v (q.1.1,y))) j q.2

lemma wallTransferSource_smoothOn {χ : Box3 → ℝ} {v : P×Box3 → ℝ}
    {θ η : ℝ → ℝ} (σ lam : ℝ)
    (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ) (hv : ContDiff ℝ (↑(⊤:ℕ∞)) v)
    (hθ : ContDiff ℝ (↑(⊤:ℕ∞)) θ) (hη : ContDiff ℝ (↑(⊤:ℕ∞)) η)
    {V : Set P} (hV : IsOpen V)
    (hne : ∀ p∈V,∀ x∈tsupport χ,wallQuotient (wallDerivative (fun y => v (p,y))) x≠0) (j) :
    ContDiffOn ℝ (↑(⊤:ℕ∞)) (wallTransferSource χ v θ η σ lam j) ((V×ˢuniv)×ˢuniv) :=
  symmetricSource_parametric_smoothOn
    (H:=wallTransferFamily χ v θ η σ lam)
    (u:=fun q : (P×Coord3)×Coord3 => wallCoordinatePair (fun y => v (q.1.1,y)) q.2)
    ((hV.prod isOpen_univ).prod isOpen_univ)
    (wallTransferFamily_smoothOn σ lam hχ hv hθ hη hV hne)
    ((wallCoordinatePair_parametric_smooth hv).comp
      (contDiff_fst.fst.prodMk contDiff_snd)).contDiffOn j

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] in
lemma wallTransferSource_zero (χ : Box3 → ℝ) (v : P×Box3 → ℝ)
    (θ η : ℝ → ℝ) (σ lam : ℝ) (p : P) (j : Fin 2) (x : Coord3) :
    wallTransferSource χ v θ η σ lam j ((p,0),x)=0 := by
  have he : (fun x => wallTransferFamily χ v θ η σ lam ((p,0),x))=0 :=
    funext (wallTransferFamily_zero χ v θ η σ lam p)
  dsimp only [wallTransferSource]
  rw [he,symmetricSource_zero]
  rfl

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] in
lemma wallTransferSource_tsupport {χ : Box3 → ℝ} (hχc : HasCompactSupport χ)
    (v : P×Box3 → ℝ) (θ η : ℝ → ℝ) (σ lam : ℝ) (q : P×Coord3) (j) :
    tsupport (fun x => wallTransferSource χ v θ η σ lam j (q,x))⊆boxCoordinates ⁻¹' tsupport χ :=
  (symmetricSource_tsupport (fun x => wallTransferFamily χ v θ η σ lam (q,x))
    (wallCoordinatePair (fun y => v (q.1,y))) j).trans
      (wallHomogeneousTensor_compact (χ:=χ) (v:=fun y => v (q.1,y))
        (a:=wallMomentAmplitude θ η σ lam q.2) hχc).2

lemma wallTransferFamily_small {χ : Box3 → ℝ} {v : P×Box3 → ℝ}
    {θ η : ℝ → ℝ} (σ lam : ℝ)
    (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ) (hχc : HasCompactSupport χ)
    (hv : ContDiff ℝ (↑(⊤:ℕ∞)) v)
    (hθ : ContDiff ℝ (↑(⊤:ℕ∞)) θ) (hη : ContDiff ℝ (↑(⊤:ℕ∞)) η)
    {p : P} {V : Set P} (hV : IsOpen V) (hp : p∈V)
    (hne : ∀ p∈V,∀ x∈tsupport χ,wallQuotient (wallDerivative (fun y => v (p,y))) x≠0)
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ q in 𝓝 (p,(0:Coord3)),∀ x,‖wallTransferFamily χ v θ η σ lam (q,x)‖≤ε := by
  apply compact_parametric_norm_small_global (f:=wallTransferFamily χ v θ η σ lam) (p:=(p,(0:Coord3)))
    (boxCoordinates.toHomeomorph.isCompact_preimage.mpr hχc)
  · intro x _
    exact ((wallTransferFamily_smoothOn σ lam hχ hv hθ hη hV hne).contDiffAt
      (((hV.prod isOpen_univ).prod isOpen_univ).mem_nhds ⟨⟨hp,mem_univ 0⟩,mem_univ x⟩)).continuousAt
  · exact wallTransferFamily_zero χ v θ η σ lam p
  · apply Eventually.of_forall
    intro q
    exact (wallHomogeneousTensor_compact (χ:=χ) (v:=fun y => v (q.1,y))
      (a:=wallMomentAmplitude θ η σ lam q.2) hχc).2
  · exact hε

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Walls_WallVanishingMomentCoefficients
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
open scoped Matrix.Norms.Elementwise
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

lemma wall_vanishing_moment_coefficients
    {v : P×Box3 → ℝ} (hv : ContDiff ℝ (↑(⊤:ℕ∞)) v) (p : P)
    {l t a b σ lam : ℝ} (hlt : l<t) (hab : a<b) (hσ : σ≠0) (hlam : lam≠0)
    (hlim : ∀ z : ℝ×ℝ,v (p,(z,0))=σ*Real.exp (-lam*z.1))
    {V : Set P} (hV : IsOpen V) (hp : p∈V)
    {r : Fin 2 → P×Coord3 → ℝ}
    (hr : ∀ j,ContDiffOn ℝ (↑(⊤:ℕ∞)) (r j) (V×ˢuniv))
    {K : Set Coord3} (hK : IsCompact K)
    (hs : ∀ᶠ q in 𝓝 p,PairSupported (fun j x => r j (q,x)) K)
    (hrz : ∀ j x,r j (p,x)=0) (δ : ℝ) :
    ∃ θ η : ℝ → ℝ, ContDiff ℝ (↑(⊤:ℕ∞)) θ ∧ ContDiff ℝ (↑(⊤:ℕ∞)) η ∧
      HasCompactSupport θ ∧ HasCompactSupport η ∧ tsupport θ⊆Icc l t ∧ tsupport η⊆Ioo a b ∧
      ∃ c : P → Coord3,Tendsto c (𝓝 p) (𝓝 0) ∧ ∀ᶠ q in 𝓝 p,∀ i,
        (∫ z,wallMomentAmplitude θ η σ lam (c q) z*wallActualMoment (fun y => v (q,y)) z i)=
        -physicalSourceMoment (wallCoordinatePair (fun y => v (q,y)))
          (fun j => wallPositiveCut δ (fun x => r j (q,x))) i := by
  have hvq (q : P) : ContDiff ℝ (↑(⊤:ℕ∞)) (fun y => v (q,y)) :=
    hv.comp (contDiff_const.prodMk contDiff_id)
  obtain ⟨θ,η,hθ,hη,hθc,hηc,hθs,hηs,C,hC,hinv⟩ :=
    actual_wall_moment_uniform_inverse (v:=fun q y => v (q,y)) (p₀:=p) hlt hab hσ hlam
      (hvq p) hv.continuous (wallAlong_parametric_smooth (1,0) hv).continuous hlim
  let u : P×Coord3 → Fin 2 → ℝ := fun q => wallCoordinatePair (fun y => v (q.1,y)) q.2
  have hu : ContDiff ℝ (↑(⊤:ℕ∞)) u := wallCoordinatePair_parametric_smooth hv
  let rp : Fin 2 → P×Coord3 → ℝ := fun j q => wallPositiveCut δ (fun x => r j (q.1,x)) q.2
  have hrp (j) : ContDiffOn ℝ (↑(⊤:ℕ∞)) (rp j) (V×ˢuniv) :=
    ((Real.smoothTransition.contDiff.comp
      (((contDiff_apply ℝ ℝ (2:Fin 3)).comp contDiff_snd).div_const δ)).contDiffOn).mul (hr j)
  let m : P → Coord3 := fun q => physicalSourceMoment (fun x => u (q,x)) (fun j x => rp j (q,x))
  have hm : Tendsto m (𝓝 p) (𝓝 0) := physicalSourceMoment_family_tendsto_zero hu.continuous hV hp
    hrp hK (hs.mono (fun q hq => hq.wallPositiveCut δ))
    (fun j x => by simp [rp,wallPositiveCut,hrz])
  have hchoose : ∀ᶠ q in 𝓝 p,∃ c : Coord3,‖c‖≤C*‖m q‖ ∧
      (∀ i,(∫ z,wallMomentAmplitude θ η σ lam c z*wallActualMoment (fun y => v (q,y)) z i)= -m q i) := by
    filter_upwards [hinv] with q hq
    obtain ⟨c,hcb,_,_,_,hcm⟩ := hq (-m q)
    refine ⟨c,?_,hcm⟩
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg hC.le (norm_nonneg _))).mpr
    intro i
    simpa only [norm_neg] using hcb i
  obtain ⟨c,hc,hcm⟩ := exists_vanishing_moment_selection hm hchoose
  exact ⟨θ,η,hθ,hη,hθc,hηc,hθs,hηs,c,hc,hcm⟩

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_TorusFluxDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix

def flatCrossFlux (s : Fin 3→ℝ) (f g : Coord3→ℝ) (x : Coord3) : Coord3 :=
  g x • flatModeFlux s f x-f x • flatModeFlux s g x

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Walls_EndingJoinCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix

def endingJoinTensor (D : Coord3 → Mat3) (lam k J L K : ℝ) (x : Coord3) : Mat3 :=
  (1-endingJoinCutoff (x 0)) • D x+endingJoinCutoff (x 0) • delayedEndingTensor lam k J L K 7 x

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_EndingJoinElliptic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix

lemma endingJoinTensor_symm {D : Coord3 → Mat3} (hD : ∀ x,(D x).IsSymm) (lam k J L K : ℝ) (x : Coord3) :
    (endingJoinTensor D lam k J L K x).IsSymm :=
  ((hD x).smul _).add ((alignedEndingTensor_symm _ _ _ _ _ _).smul _)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_FourierMatchingInterpolation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix

def fourierMatchingPair (s : Fin 3 → ℝ) (k : ℤ) (f g : ℝ×Coord3 → ℝ)
    (z : ℝ×Coord3) : Fin 2 → ℝ :=
  ![z.2 0+fourierMatchingCutoff (z.2 0)*f z,
    flatPhaseMode s ![0,k] 0 z.2+fourierMatchingCutoff (z.2 0)*g z]

end ScalarConductivity



namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

def fourierMatchingResidual (s : Fin 3 → ℝ) (k : ℤ) (f g : ℝ×Coord3 → ℝ)
    (j : Fin 2) (z : ℝ×Coord3) : ℝ :=
  -fourierResidualCutoff (z.2 0)*symmetricSource (fun _ => flatBackgroundTensor s)
    (fun x => fourierMatchingPair s k f g (z.1,x)) j z.2

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_EndingJoinMiddleModel
attribute [-instance] _root_.OAI.ScalarConductivity.instMeasurableSpaceSymmetric3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

def endingJoinMiddleTensor (s : Fin 3 → ℝ) (lam k J : ℝ) (x : Coord3) : Symmetric3 :=
  ⟨(1-endingJoinCutoff (x 0)) • flatBackgroundTensor s+
    endingJoinCutoff (x 0) • delayedInitialTensor lam k J 7 x,
    ((flatBackgroundTensor_symm s).smul _).add ((delayedInitialTensor_symm _ _ _ _ _).smul _)⟩

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_MatchedEndingRegularity
attribute [-instance] _root_.OAI.ScalarConductivity.instMeasurableSpaceSymmetric3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

def endingJoinSymmetricTensor (D : Coord3 → Mat3) (hD : ∀ x,(D x).IsSymm)
    (lam k J L K : ℝ) (x : Coord3) : Symmetric3 :=
  ⟨endingJoinTensor D lam k J L K x,endingJoinTensor_symm hD _ _ _ _ _ x⟩

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_MeasurableDisjointGluing
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
open scoped Matrix.Norms.Elementwise

instance instBorelSpaceSymmetric3 : BorelSpace Symmetric3 := ⟨rfl⟩

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_PhysicalBlockEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

def physicalBlockRegion : Set (Fin 3 → ℝ) :=
  centralPhysical ∪ ⋃ i : Fin 3,physicalEndRegion i

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_CylinderFourierComplete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal

attribute [local instance] OAI.ScalarConductivity.cylinderFourierCompleteMeasureSpace
attribute [local instance] OAI.ScalarConductivity.cylinderFourierCompleteProbabilityMeasure
lemma cylinderMode_inner_coefficient {μ : Measure ℝ} [SFinite μ]
    (F : CylinderL2 μ) (h : TorusModes) (f : Lp ℂ 2 μ) :
    inner ℂ (cylinderMode μ h f) F = inner ℂ f (cylinderCoefficientLp F h) := by
  have hae : (fun z : ℝ × UnitAddTorus (Fin 2) =>
      inner ℂ ((cylinderMode μ h f) z) (F z)) =ᵐ[μ.prod volume]
      fun z => (starRingEnd ℂ) (f z.1) * (mFourier (-h) z.2 * F z) := by
    filter_upwards [cylinderTensor_ae f (mFourierLp 2 h),
      Measure.quasiMeasurePreserving_snd.ae (coeFn_mFourierLp 2 h)] with z hz he
    change inner ℂ ((cylinderTensor f (mFourierLp 2 h)) z) (F z) = _
    rw [hz,he]
    simp only [RCLike.inner_apply,map_mul,mFourier_neg]
    ring
  have hI := (L2.integrable_inner (cylinderMode μ h f) F).congr hae
  rw [L2.inner_def,L2.inner_def,integral_congr_ae hae,integral_prod _ hI]
  apply integral_congr_ae
  filter_upwards [cylinderCoefficientLp_ae F h] with t ht
  rw [ht,integral_const_mul]
  simp only [cylinderCoefficient,mFourierCoeff,smul_eq_mul,RCLike.inner_apply]
  ring

lemma cylinderModes_total {μ : Measure ℝ} [SFinite μ] (F : CylinderL2 μ)
    (hF : ∀ (h : TorusModes) (f : Lp ℂ 2 μ), inner ℂ (cylinderMode μ h f) F = 0) :
    F = 0 := by
  have hc (h : TorusModes) : cylinderCoefficientLp F h = 0 := by
    apply (inner_self_eq_zero (𝕜:=ℂ)).mp
    exact (cylinderMode_inner_coefficient F h (cylinderCoefficientLp F h)).symm.trans
      (hF h (cylinderCoefficientLp F h))
  have hac (h : TorusModes) : cylinderCoefficient F h =ᵐ[μ] 0 := by
    exact (cylinderCoefficientLp_ae F h).symm.trans (by rw [hc h]; exact Lp.coeFn_zero _ _ _)
  have haslice : ∀ᵐ t ∂μ, ∀ᵐ θ ∂(volume : Measure (UnitAddTorus (Fin 2))), F (t,θ) = 0 := by
    filter_upwards [cylinderL2_slice_memLp F, ae_all_iff.mpr hac] with t ht hct
    let g : TorusL2 := ht.toLp (fun θ => F (t,θ))
    have hcg (h : TorusModes) : mFourierCoeff g h = 0 := by
      calc
        mFourierCoeff g h = cylinderCoefficient F h t := by
          unfold mFourierCoeff cylinderCoefficient
          apply integral_congr_ae
          filter_upwards [ht.coeFn_toLp] with θ hθ
          rw [hθ]
        _ = 0 := hct h
    have hg : g = 0 := by
      apply mFourierBasis.repr.injective
      rw [map_zero]
      ext h
      simpa only [mFourierBasis_repr,lp.coeFn_zero,Pi.zero_apply] using hcg h
    have hg' : g =ᵐ[volume] (0 : UnitAddTorus (Fin 2) → ℂ) := by
      rw [hg]
      exact Lp.coeFn_zero _ _ _
    exact ht.coeFn_toLp.symm.trans hg'
  have hn : ‖F‖^2 = 0 := by
    rw [complexLp_norm_sq,integral_prod _ ((Lp.memLp F).integrable_norm_pow (by decide : (2:ℕ)≠0))]
    apply integral_eq_zero_of_ae
    filter_upwards [haslice] with t ht
    apply integral_eq_zero_of_ae
    filter_upwards [ht] with θ hθ
    simp only [hθ,norm_zero,zero_pow (by decide : (2:ℕ)≠0),Pi.zero_apply]
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hn)

theorem cylinderFourier_surjective (μ : Measure ℝ) [SFinite μ] :
    Function.Surjective (cylinderFourier μ) := by
  classical
  let L := (cylinderFourier μ).toContinuousLinearMap
  let K := L.range
  have hclosed : IsClosed (K : Set (CylinderL2 μ)) :=
    (cylinderFourier μ).isometry.isClosedEmbedding.isClosed_range
  let : CompleteSpace K := hclosed.completeSpace_coe
  have horth : Kᗮ = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro F hF
    change F = 0
    apply cylinderModes_total F
    intro h f
    apply hF
    exact ⟨lp.single 2 h f,(cylinderMode_orthogonal μ).linearIsometry_apply_single f⟩
  have htop : K = ⊤ := (Submodule.orthogonal_eq_bot_iff).mp horth
  intro F
  have hF : F∈K := by rw [htop]; trivial
  exact hF

def cylinderFourierEquiv (μ : Measure ℝ) [SFinite μ] :
    lp (fun _ : TorusModes => Lp ℂ 2 μ) 2 ≃ₗᵢ[ℂ] CylinderL2 μ :=
  LinearIsometryEquiv.ofSurjective (cylinderFourier μ) (cylinderFourier_surjective μ)

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_TorusDirectionalDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal NNReal

lemma measurable_torusRealRepresentative : Measurable torusRealRepresentative :=
  measurable_subtype_coe.comp (measurableEquivPiIoc (fun _ : Fin 2 => (0:ℝ))).measurable

lemma torusRealLift_lipschitz (f : C(UnitAddTorus (Fin 2),ℂ)) (K : ℝ≥0)
    (hLip : ∀ j t θ, ‖f (θ+torusCoordinateShift j t)-f θ‖≤(K:ℝ)*|t|) :
    LipschitzWith (2*K) (fun x : TorusRealPlane => f (torusRealProjection x)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have he : torusRealProjection x=(torusRealProjection y+torusCoordinateShift 0 (x 0-y 0))+
      torusCoordinateShift 1 (x 1-y 1) := by
    ext j
    fin_cases j <;> simp [torusRealProjection,torusCoordinateShift]
  have hx (j : Fin 2) : |x j-y j|≤dist x y := by
    simpa only [Real.dist_eq] using dist_le_pi_dist x y j
  calc
    dist (f (torusRealProjection x)) (f (torusRealProjection y)) ≤
        dist (f (torusRealProjection x))
          (f (torusRealProjection y+torusCoordinateShift 0 (x 0-y 0)))+
        dist (f (torusRealProjection y+torusCoordinateShift 0 (x 0-y 0)))
          (f (torusRealProjection y)) := dist_triangle _ _ _
    _≤(K:ℝ)*|x 1-y 1|+(K:ℝ)*|x 0-y 0| := by
      apply add_le_add
      · rw [dist_eq_norm,he]
        exact hLip 1 _ _
      · rw [dist_eq_norm]
        exact hLip 0 _ _
    _≤((2*K:ℝ≥0):ℝ)*dist x y := by
      push_cast
      nlinarith [mul_le_mul_of_nonneg_left (hx 0) K.coe_nonneg,
        mul_le_mul_of_nonneg_left (hx 1) K.coe_nonneg]

def torusDirectionalDerivative (f : UnitAddTorus (Fin 2) → ℂ) (j : Fin 2)
    (θ : UnitAddTorus (Fin 2)) : ℂ :=
  lineDeriv ℝ (fun x => f (torusRealProjection x)) (torusRealRepresentative θ) (Pi.single j 1)

lemma torusDirectionalDerivative_norm (f : C(UnitAddTorus (Fin 2),ℂ)) (K : ℝ≥0)
    (hLip : ∀ j t θ, ‖f (θ+torusCoordinateShift j t)-f θ‖≤(K:ℝ)*|t|)
    (j : Fin 2) (θ : UnitAddTorus (Fin 2)) :
    ‖torusDirectionalDerivative f j θ‖≤2*K := by
  have h := norm_lineDeriv_le_of_lipschitz ℝ (torusRealLift_lipschitz f K hLip)
    (x₀:=torusRealRepresentative θ) (v:=Pi.single j 1)
  simpa only [torusDirectionalDerivative,NNReal.coe_mul,NNReal.coe_ofNat,
    Pi.norm_single,norm_one,mul_one] using h

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_AngularCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal

attribute [local instance] OAI.ScalarConductivity.angularCoefficientMeasureSpace
attribute [local instance] OAI.ScalarConductivity.angularCoefficientProbabilityMeasure
lemma sourceAngularCoefficient_smooth {f : (Fin 3 → ℝ) → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (a b : ℝ) (h : TorusModes) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (sourceAngularCoefficient f a b h) := by
  let F : ℝ × ((Fin 4 → ℝ) × ℂ) → ℂ := fun z =>
    z.2.2 * (f (sourceAngularPolynomial (a*z.1+b) z.2.1) : ℂ)
  have hF : ContDiff ℝ (↑(⊤ : ℕ∞)) F := by
    apply ContDiff.mul (contDiff_snd.comp contDiff_snd)
    exact Complex.ofRealCLM.contDiff.comp (hf.comp
      (contDiff_sourceAngularPolynomial_joint.comp
        ((contDiff_const.mul contDiff_fst |>.add contDiff_const).prodMk
          (contDiff_fst.comp contDiff_snd))))
  have hr : Continuous (fun θ : UnitAddTorus (Fin 2) =>
      (sourceRayCoordinates θ,mFourier (-h) θ)) :=
    continuous_sourceRayCoordinates.prodMk (mFourier (-h)).continuous
  exact contDiff_compact_parameter hF hr

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_AngularJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal NNReal

lemma measurable_torusDirectionalDerivative_joint
    {f : ℝ × UnitAddTorus (Fin 2) → ℂ} (hf : Continuous f) (j : Fin 2) :
    Measurable (fun z : ℝ × UnitAddTorus (Fin 2) =>
      torusDirectionalDerivative (fun θ => f (z.1,θ)) j z.2) := by
  let F : ℝ × TorusRealPlane → ℂ := fun z => f (z.1,torusRealProjection z.2)
  have hc : Continuous F := hf.comp
    (continuous_fst.prodMk (continuous_torusRealProjection.comp continuous_snd))
  have hm := (measurable_lineDeriv (𝕜:=ℝ) hc (v:=(0,Pi.single j 1))).comp
    (measurable_fst.prodMk (measurable_torusRealRepresentative.comp measurable_snd))
  convert hm using 1
  all_goals try with_reducible_and_instances rfl
  funext z
  unfold torusDirectionalDerivative lineDeriv
  congr 2
  ext t
  simp [F]

theorem sourceAngularTest_lipschitz {f : (Fin 3 → ℝ) → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (a b R : ℝ) :
    ∃ K : ℝ≥0, ∀ t∈Icc (0:ℝ) R, ∀ j u θ,
      ‖sourceAngularTest f a b (t,θ+torusCoordinateShift j u)-
        sourceAngularTest f a b (t,θ)‖≤(K:ℝ)*|u| := by
  let G : ℝ × (Fin 4 → ℝ) → ℂ := fun z =>
    (f (sourceAngularPolynomial (a*z.1+b) z.2) : ℂ)
  have hG : ContDiff ℝ (↑(⊤ : ℕ∞)) G :=
    Complex.ofRealCLM.contDiff.comp (hf.comp
      (contDiff_sourceAngularPolynomial_joint.comp
        ((contDiff_const.mul contDiff_fst |>.add contDiff_const).prodMk contDiff_snd)))
  obtain ⟨K,hK⟩ := hG.contDiffOn.exists_lipschitzOnWith (by simp)
    ((convex_Icc (0:ℝ) R).prod (convex_Icc _ _))
    (isCompact_Icc.prod (isCompact_Icc (a:=(fun _ : Fin 4 => (-2:ℝ))) (b:=fun _ => (2:ℝ))))
  refine ⟨K*⟨sourceRayConstant,sourceRayConstant_nonneg⟩,?_⟩
  intro t ht j u θ
  have hh := hK.dist_le_mul (t,sourceRayCoordinates (θ+torusCoordinateShift j u))
    ⟨ht,sourceRayCoordinates_mem _⟩ (t,sourceRayCoordinates θ) ⟨ht,sourceRayCoordinates_mem _⟩
  rw [Prod.dist_eq,dist_self,max_eq_right (dist_nonneg),dist_eq_norm,dist_eq_norm] at hh
  apply hh.trans
  change _ ≤ (K:ℝ)*sourceRayConstant*|u|
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left (sourceRayCoordinates_difference j u θ) K.coe_nonneg

def sourceAngularJet (f : (Fin 3 → ℝ) → ℝ) (a b : ℝ)
    (j : Fin 4) (z : ℝ × UnitAddTorus (Fin 2)) : ℂ :=
  ![sourceAngularTest f a b z,sourceAngularAxial f a b z.1 z.2,
    torusDirectionalDerivative (fun θ => sourceAngularTest f a b (z.1,θ)) 0 z.2/(2*Real.pi),
    torusDirectionalDerivative (fun θ => sourceAngularTest f a b (z.1,θ)) 1 z.2/(2*Real.pi)] j

end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal NNReal

attribute [local instance] OAI.ScalarConductivity.angularJetFiniteCylinderMeasureSpace
attribute [local instance] OAI.ScalarConductivity.angularJetFiniteCylinderProbabilityMeasure
lemma sourceAngularJet_memLp {f : (Fin 3 → ℝ) → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (a b R : ℝ) (j : Fin 4) :
    MemLp (sourceAngularJet f a b j) 2 ((FiniteAxisMeasure R).prod volume) := by
  obtain ⟨K,hK⟩ := sourceAngularTest_lipschitz hf a b R
  have hang (k : Fin 2) : MemLp (fun z : ℝ × UnitAddTorus (Fin 2) =>
      torusDirectionalDerivative (fun θ => sourceAngularTest f a b (z.1,θ)) k z.2/(2*Real.pi))
        2 ((FiniteAxisMeasure R).prod volume) := by
    apply MemLp.of_bound
      (((measurable_torusDirectionalDerivative_joint (continuous_sourceAngularTest hf a b) k).div_const _).aestronglyMeasurable) ((2:ℝ)*K/‖(2*Real.pi:ℂ)‖)
    filter_upwards [finiteCylinder_ae_mem R] with z hz
    rw [norm_div]
    apply div_le_div_of_nonneg_right _ (norm_nonneg _)
    exact torusDirectionalDerivative_norm
      ⟨fun θ => sourceAngularTest f a b (z.1,θ),
        (continuous_sourceAngularTest hf a b).comp (continuous_const.prodMk continuous_id)⟩
      K (hK z.1 hz) k z.2
  fin_cases j
  · exact continuous_memLp_finiteCylinder (continuous_sourceAngularTest hf a b) R
  · exact continuous_memLp_finiteCylinder (continuous_sourceAngularAxial hf a b) R
  · exact hang 0
  · exact hang 1

def sourceAngularLpJet {f : (Fin 3 → ℝ) → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (a b R : ℝ) : FiniteCylinderJets R :=
  WithLp.toLp 2 (fun j => (sourceAngularJet_memLp hf a b R j).toLp _)

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_EndPointEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus Matrix
open scoped ENNReal

def sourceEndSmoothDensity (s : Fin 3 → ℝ) (f : spectralTraceGraph (torusRate s))
    (κ a b : ℝ) (φ : (Fin 3 → ℝ) → ℝ) (z : ℝ × UnitAddTorus (Fin 2)) : ℝ :=
  fullEndFlatCovector s f κ z.1 z.2 ⬝ᵥ
    (flatCylinderMatrix s*ᵥ(fun k : Fin 3 => (sourceAngularJet φ a b k.succ z).re))

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_AttachedPhysicalSmoothGreen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix

def physicalSmoothOuterTrace {φ : (Fin 3 → ℝ) → ℝ} (s : Fin 3 → ℝ)
    (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) (i : Fin 3) : spectralTraceGraph (torusRate s) :=
  Fin.cases (smoothCollarTrace s 0 hφ)
    (fun k => smoothCollarTrace s 0 (hφ.comp (sourceChildCoordinates_contDiff (actualChildSign k)))) i

end ScalarConductivity



end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_TorusSmoothModeJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory UnitAddTorus
open scoped ENNReal

def flatSmoothMode (q : ℝ → ℂ) (h : TorusModes) (x : Coord3) : ℂ :=
  q (x 0)*Complex.exp (angularFrequency h x)

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_DelayedPairFlux
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix Real

def delayedPairFlux (lam k J L K R : ℝ) (j : Fin 2) (x : Coord3) : Coord3 :=
  if j=0 then Pi.single 0 1 else potentialCurl (delayedEndingPotential lam k J L K R) x

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Scalarization_EndingJoinConstitution
attribute [-instance] _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix

def joinedFlux (D : Coord3 → Mat3) (u : Coord3 → Fin 2 → ℝ) (lam k J L K : ℝ) (j : Fin 2) : Coord3 → Coord3 :=
  axialFluxBlend endingJoinCutoff (matchingFlux D u j) (delayedPairFlux lam k J L K 7 j)

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Scalarization_DenseClosureApprox
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open MeasureTheory Set Filter Topology TopologicalSpace
open scoped ENNReal

def finiteUpdatePairs
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    (U : Set Coord3) (u : Coord3 → Fin 2 → ℝ) (A : Coord3 → Symmetric3)
    (hE : MemLp (voltageGradient u) 2 (μ.restrict U))
    (hF : MemLp (voltageFlux u A) 2 (μ.restrict U)) (a b : ℝ) :
    Set (Lp FieldVector 2 (μ.restrict U) × Lp FieldVector 2 (μ.restrict U)) :=
  {Z | ∃ R : CompactGlobalUpdate μ U u A,
    μ (U \ regularRegion (fun x => u x+R.du x) R.tensor U) = 0 ∧
    (∀ᵐ x ∂μ, x ∈ U → R.tensor x ∈ matrixFiniteLaminate a b) ∧
    Z = R.fieldPair μ hE hF}

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_VoltagePoincare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open MeasureTheory Set Filter Topology Matrix
open scoped ENNReal NNReal

lemma gradientVectorCLM_injective : Function.Injective gradientVectorCLM := by
  intro D E h
  have hm : gradientColumns D = gradientColumns E := by
    ext i j
    exact congrArg (fun v : FieldVector => v (i,j)) h
  ext v j
  have h := congrArg (fun M : Matrix (Fin 3) (Fin 2) ℝ => (Mᵀ *ᵥ v) j) hm
  simpa only [gradientColumns_apply] using h

lemma exists_gradientCoordinateConstant :
    ∃ K : ℝ≥0, 0 < K ∧ ∀ D : Coord3 →L[ℝ] (Fin 2 → ℝ),
      ‖D‖ ≤ K * ‖gradientVectorCLM D‖ := by
  obtain ⟨K,hK,hbound⟩ := gradientVectorCLM.toLinearMap.injective_iff_antilipschitz.mp
    gradientVectorCLM_injective
  refine ⟨K,hK,fun D => ?_⟩
  simpa only [dist_zero_right,map_zero,ContinuousLinearMap.coe_coe] using hbound.le_mul_dist D 0

def gradientCoordinateConstant : ℝ≥0 := exists_gradientCoordinateConstant.choose

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

lemma voltageGradient_zero : voltageGradient (0 : Coord3 → Fin 2 → ℝ) = 0 := by
  funext x
  change gradientVectorCLM (fderiv ℝ (0 : Coord3 → Fin 2 → ℝ) x) = 0
  simp only [fderiv_zero,Pi.zero_apply,map_zero]

lemma voltageGradient_smul (c : ℝ) {v : Coord3 → Fin 2 → ℝ} (hv : Differentiable ℝ v) :
    voltageGradient (c • v) = c • voltageGradient v := by
  funext x
  simp only [voltageGradient,fderiv_const_smul (hv x),map_smul,Pi.smul_apply]

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_VoltageH1Completion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open MeasureTheory Set Filter Topology TopologicalSpace Matrix
open scoped ENNReal Matrix.Norms.Elementwise

def smoothVoltageJets (μ : Measure Coord3) (U : Set Coord3) : Set (VoltageJetSpace μ U) :=
  {z | ∃ (v : Coord3 → Fin 2 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) v ∧
    ∃ (hm : MemLp v 2 (μ.restrict U)) (hg : MemLp (voltageGradient v) 2 (μ.restrict U)),
      z = (hm.toLp _,hg.toLp _)}

def voltageH1Jets (μ : Measure Coord3) (U : Set Coord3) :
    Submodule ℝ (VoltageJetSpace μ U) :=
  (Submodule.span ℝ (smoothVoltageJets μ U)).topologicalClosure

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_C1VoltageApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology TopologicalSpace MeasureTheory Matrix
open scoped ENNReal Convolution

def coordDyadicBump (n : ℕ) : CoordBump where
  rIn := (1/2:ℝ)^(n+1)
  rOut := (1/2:ℝ)^n
  rIn_pos := by positivity
  rIn_lt_rOut := by
    rw [pow_succ]
    have h : 0<(1/2:ℝ)^n := by positivity
    linarith

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]

def coordMollify (φ : CoordBump) (f : Coord3 → F) : Coord3 → F :=
  (φ.normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ,volume] f

omit [CompleteSpace F] [MeasurableSpace F] [BorelSpace F] in
lemma coordMollify_smooth (φ : CoordBump) {f : Coord3 → F} (hf : Continuous f) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (coordMollify φ f) :=
  φ.hasCompactSupport_normed.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    φ.contDiff_normed hf.locallyIntegrable

omit [CompleteSpace F] in
lemma coordMollify_memLp (φ : CoordBump) {f : Coord3 → F} (hf : Continuous f)
    {U : Set Coord3} (hUb : Bornology.IsBounded U) (hUm : MeasurableSet U) :
    MemLp (coordMollify φ f) 2 (volume.restrict U) :=
  continuous_memLp_bounded_coord (coordMollify_smooth φ hf).continuous hUb hUm

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_AngularInverseTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix Real
open scoped Matrix.Norms.Elementwise

def undoAngularValue (A : Matrix (Fin 2) (Fin 2) ℤ) (θ : Fin 2 → ℝ)
    (d lam : ℝ) (v : Coord3 → Fin 2 → ℝ) (x : Coord3) : Fin 2 → ℝ :=
  ![sqrt (angularNormalization A)*v (undoAngularPoint A θ d x) 0+d,
    exp (-lam*d)*v (undoAngularPoint A θ d x) 1]

def undoAngularTensor (A : Matrix (Fin 2) (Fin 2) ℤ) (θ : Fin 2 → ℝ)
    (d : ℝ) (E : Coord3 → Mat3) (x : Coord3) : Mat3 :=
  (angularNormalization A)⁻¹ •
    (angularLiftMatrix A*E (undoAngularPoint A θ d x)*(angularLiftMatrix A)ᵀ)

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_TorusCylinderGreenReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory UnitAddTorus
open scoped ENNReal

variable {F : Coord3 → Coord3}

attribute [local instance] OAI.ScalarConductivity.torusCylinderGreenRealFluxMeasureSpaceUnitAddCircle
def cylinderFluxLp (hF : Continuous F) (hp : AngularPeriodic (2*Real.pi) F)
    (R : ℝ) (j : Fin 3) : CylinderL2 (FiniteAxisMeasure R) :=
  (continuous_memLp_finiteCylinder (continuous_torusFluxComponent hF hp j) R).toLp _

def cylinderFluxPairL (hF : Continuous F) (hp : AngularPeriodic (2*Real.pi) F)
    (R : ℝ) : FiniteCylinderJets R →L[ℂ] ℂ :=
  ∑ j : Fin 3,(innerSL ℂ (cylinderFluxLp hF hp R j)).comp
    (PiLp.proj 2 (fun _ : Fin 4 => CylinderL2 (FiniteAxisMeasure R)) j.succ)

attribute [local instance] OAI.ScalarConductivity.torusCylinderGreenRealFluxIsProbabilityMeasure
def torusFluxLp (hF : Continuous F) (hp : AngularPeriodic (2*Real.pi) F) (t : ℝ) : TorusL2 :=
  ContinuousMap.toLp 2 volume ℂ ⟨fun θ => (torusPeriodicDescent F (t,θ) 0:ℂ),
    (continuous_torusFluxComponent hF hp 0).comp (continuous_const.prodMk continuous_id)⟩

def torusFluxPairL (hF : Continuous F) (hp : AngularPeriodic (2*Real.pi) F)
    (s : Fin 3 → ℝ) (t : ℝ) : spectralTraceGraph (torusRate s) →L[ℂ] ℂ :=
  (innerSL ℂ (torusFluxLp hF hp t)).comp (torusSpectralSynthesis s)

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_PhysicalAttachedGreen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix

def physicalTerminalFluxCLM (s a κ : Fin 3 → ℝ) (ha : ∀ i,a i≠0)
    (f : Fin 3 → spectralTraceGraph (torusRate s)) : H1 →L[ℝ] ℝ :=
  angularArea • ∑ i : Fin 3,
    (terminalFluxL2CLM s (κ i) (physicalEndLength_pos a ha i) (f i)).comp (physicalOuterTraceCLM i)

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_FluxCylinder
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

def sourceFluxDensity (F : Coord3 → Coord3) (a b : ℝ) (φ : Coord3 → ℝ)
    (z : ℝ × UnitAddTorus (Fin 2)) : ℝ :=
  torusPeriodicDescent F z ⬝ᵥ(fun j : Fin 3 => (sourceAngularJet φ a b j.succ z).re)

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_VoltageOriginalH10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology
open scoped ENNReal Classical

def voltageComponentJetCLM (μ : Measure Coord3) (U : Set Coord3) (j : Fin 2) :
    VoltageJetSpace μ U →L[ℝ] Lp JetFiber 2 (μ.restrict U) :=
  ((voltageValueComponentJet j).compLpL 2 (μ.restrict U)).comp
    (ContinuousLinearMap.fst ℝ _ _)+
  ((voltageGradientComponentJet j).compLpL 2 (μ.restrict U)).comp
    (ContinuousLinearMap.snd ℝ _ _)

def voltageOriginalJetCLM {U : Set Coord3} (hU : MeasurableSet U) (j : Fin 2) :
    VoltageJetSpace volume U →L[ℝ] JetSpace :=
  (lpRestrictionCLM ball).comp
    (((Lp.compMeasurePreservingₗᵢ ℝ
      (WithLp.ofLp : R3 → Coord3)
      (PiLp.volume_preserving_ofLp (Fin 3))).toContinuousLinearMap).comp
      ((lpZeroExtensionCLM hU).comp (voltageComponentJetCLM volume U j)))

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_OriginalVoltageRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology
open scoped ENNReal Classical

def originalVoltageJetCLM (U : Set Coord3) (j : Fin 2) :
    JetSpace →L[ℝ] VoltageJetSpace volume U :=
  (((originalVoltageValue j).compLpL 2 (volume.restrict U)).prod
    ((originalVoltageGradient j).compLpL 2 (volume.restrict U))).comp
      (originalCartesianJetCLM U)

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_OriginalPairVoltage
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

def originalPairVoltageJet (U : Set Coord3) (w : Fin 2 → H1) : VoltageJetSpace volume U :=
  originalVoltageJetCLM U 0 (w 0).val + originalVoltageJetCLM U 1 (w 1).val

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_PhysicalOpenVoltage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise ENNReal

lemma physicalOpenBlock_open : IsOpen physicalOpenBlock :=
  sourceOpenBlock_isOpen.preimage
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.continuous

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_VoltageBoundaryTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology
open scoped ENNReal

def voltageOriginalProjectedH1 {U : Set Coord3} (hU : MeasurableSet U) (j : Fin 2) :
    VoltageJetSpace volume U →L[ℝ] H1 :=
  H1Space.orthogonalProjectionOnto.comp (voltageOriginalJetCLM hU j)

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_PhysicalRealTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal NNReal

attribute [local instance] OAI.ScalarConductivity.physicalRealTraceMeasureSpaceUnitAddCircle
def physicalComplexTraceCLM (i : Fin 3) : H1 →L[ℝ] TorusL2 :=
  (((mFourierBasis (d:=Fin 2)).repr.symm.toContinuousLinearEquiv.toContinuousLinearMap).restrictScalars ℝ).comp
    (physicalOuterTraceCLM i)

local instance physicalRealTraceIsProbabilityMeasure_r244364_1 : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
def physicalRealTraceCLM (i : Fin 3) : H1 →L[ℝ] Lp ℝ 2 (volume : Measure (UnitAddTorus (Fin 2))) :=
  (Complex.reCLM.compLpL 2 volume).comp (physicalComplexTraceCLM i)

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_PhysicalTraceTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus

def sourceMeanCLM (i : Fin 3) : H1 →L[ℝ] ℝ :=
  (Complex.reCLM.comp ((lp.evalCLM ℂ (fun _ : TorusModes => ℂ) 2 0).restrictScalars ℝ)).comp
    (physicalOuterTraceCLM i)

end ScalarConductivity

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
open Set MeasureTheory Filter Topology

variable {χ : R3 → ℝ} (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ) (hc : HasCompactSupport χ)

lemma originalMulJetCLM_smooth {f : R3 → ℝ} (hf : ContDiff ℝ (↑(⊤:ℕ∞)) f) :
    originalMulJetCLM hχ hc (smoothH1 f hf)=(smoothH1 (χ*f) (hχ.mul hf)).val := by
  apply Lp.ext
  filter_upwards [originalMulJetCLM_ae hχ hc (smoothH1 f hf),smoothH1_value f hf,smoothH1_gradient f hf,
    (smoothJet_memLp (hχ.mul hf)).coeFn_toLp] with x hm hv hg hs
  change (smoothH1 (χ*f) (hχ.mul hf)).val x=smoothJet (χ*f) x at hs
  rw [hm,hs]
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · change χ x*weakValue (smoothH1 f hf) x=χ x*f x
    rw [hv]
  · change fderiv ℝ χ x (EuclideanSpace.single j 1)*weakValue (smoothH1 f hf) x+
      χ x*weakGradient (smoothH1 f hf) x j=gradient (χ*f) x j
    rw [hv,hg]
    have hj (g : R3 → ℝ) : gradient g x j=fderiv ℝ g x (EuclideanSpace.single j 1) := by
      have h : inner ℝ (EuclideanSpace.single j 1) (gradient g x)=
          (starRingEnd ℝ) (fderiv ℝ g x (EuclideanSpace.single j 1)) := inner_gradient_right
      simpa only [EuclideanSpace.inner_single_left,RCLike.conj_to_real,one_mul] using h
    rw [hj,hj,fderiv_mul (hχ.differentiable (by simp) x) (hf.differentiable (by simp) x)]
    simp only [add_apply,smul_apply,smul_eq_mul]
    ring

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_OriginalMultiplierOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

variable {χ : R3 → ℝ} (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ) (hc : HasCompactSupport χ)

lemma originalMulJetCLM_mem_H1 (u : H1) : originalMulJetCLM hχ hc u∈H1Space := by
  have hclosed : IsClosed {u : H1 | originalMulJetCLM hχ hc u∈H1Space} :=
    H1_isClosed.preimage (originalMulJetCLM hχ hc).continuous
  apply (closure_minimal (s:={u : H1 | u.val∈smoothJets}) ?_ hclosed) (smoothH1_dense u)
  rintro v ⟨f,hf,hm,he⟩
  have hv : v=smoothH1 f hf := Subtype.ext he
  change originalMulJetCLM hχ hc v∈H1Space
  rw [hv,originalMulJetCLM_smooth]
  exact (smoothH1 (χ*f) (hχ.mul hf)).property

def originalMulH1CLM : H1 →L[ℝ] H1 :=
  (originalMulJetCLM hχ hc).codRestrict H1Space (originalMulJetCLM_mem_H1 hχ hc)

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_BranchCombine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity

section
open Set MeasureTheory Filter Topology
attribute [local instance] Classical.propDecidable

def sourceBranchCombine (α β : ℝ) (v w : H10) : H10 :=
  α • childZeroTransport 0 v+β • childZeroTransport 1 w

end

open Set MeasureTheory Filter Topology

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_WordTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus

lemma sourceWordMap_contDiff (ν : SourceWord) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (sourceWordMap ν : R3 → R3) := by
  induction ν with
  | nil => exact contDiff_id
  | cons k ν ih => exact (sourceChildEuclidean_contDiff _).comp ih

def sourceWordBoundary (ν : SourceWord) (θ : UnitAddTorus (Fin 2)) : R3 :=
  sourceWordMap ν (WithLp.toLp 2 (physicalOuterBoundary 0 θ))

end ScalarConductivity

end
end

end OAI
end


