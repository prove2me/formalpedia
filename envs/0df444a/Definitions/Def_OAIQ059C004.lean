-- Prove2me | Definitions.Def_OAIQ059C004
-- name    : OAIQ059C004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T21:36:02.465461+00:00
-- url     : https://prove2.me/theorems/b8b7a419-c8d5-48c6-b131-f08cab20bcda
-- title:
--   Definitions bundle OAIQ059C004 of the split of OpenAI, Nonuniqueness for bounded measurable scalar conductivities in three dimensions (result family 365)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ScalarConductivity.main_nonuniqueness`, carved from OpenAI's openai/math development (OpenAI, *Nonuniqueness for bounded measurable scalar conductivities in three dimensions (result family 365)*, OpenAI Math Release, September 23, 2026, result family 365, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 344 declarations of OpenAI's Lean: 121 definitions, 4 instances and 219 theorems. The definitions and types are `OAI.ScalarConductivity.PhysicalFiniteEndingData.terminalBase`, `OAI.ScalarConductivity.PhysicalFiniteEndingData.terminalCore`, `OAI.ScalarConductivity.PhysicalFiniteEndingData.terminalTime`, `OAI.ScalarConductivity.RectFootprint.poincareConstant`, `OAI.ScalarConductivity.SmoothFluxIntegrable`, `OAI.ScalarConductivity.SmoothLipZero.onH1`, `OAI.ScalarConductivity.SmoothLipZero.onLp`, `OAI.ScalarConductivity.VoltageJetSpace`, `OAI.ScalarConductivity.WeakFiniteTensorPair.projectFirst`, `OAI.ScalarConductivity.WeakFiniteTensorPair.scaleTensor`, `OAI.ScalarConductivity.WeakFiniteTensorPair.undoAngular`, `OAI.ScalarConductivity.affineFourierField`, `OAI.ScalarConductivity.airyFlux`, `OAI.ScalarConductivity.alignedEndingPotential`, `OAI.ScalarConductivity.alignedEndingSymmetricTensor`, `OAI.ScalarConductivity.alignedEndingTensor`, `OAI.ScalarConductivity.alignedEndingValue`, `OAI.ScalarConductivity.angularCutoff`, `OAI.ScalarConductivity.angularFrequency`, `OAI.ScalarConductivity.angularLiftMatrix`, `OAI.ScalarConductivity.angularPeriodize`, `OAI.ScalarConductivity.angularRealTranslation`, `OAI.ScalarConductivity.angularStream`, `OAI.ScalarConductivity.axialFluxBlend`, `OAI.ScalarConductivity.axialPair`, `OAI.ScalarConductivity.axialZeroExtension`, `OAI.ScalarConductivity.boxRescale`, `OAI.ScalarConductivity.cascadeBaseStream`, `OAI.ScalarConductivity.cascadeCenter`, `OAI.ScalarConductivity.cascadeCrossStream`, `OAI.ScalarConductivity.cascadeFlux`, `OAI.ScalarConductivity.cascadeIndex`, `OAI.ScalarConductivity.cascadeMother`, `OAI.ScalarConductivity.cascadePotential`, `OAI.ScalarConductivity.cascadePotentialMother`, `OAI.ScalarConductivity.cascadePotentialTerm`, `OAI.ScalarConductivity.cascadeStageTensor`, `OAI.ScalarConductivity.cascadeSymmetricTensor`, `OAI.ScalarConductivity.cascadeTensor`, `OAI.ScalarConductivity.cascadeTerm` and 81 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `Conductivity_Branching_AlignedEndingRegularity`, `Conductivity_Branching_AttachedCutLayer`, `Conductivity_Branching_AttachedEndGradientL2`, `Conductivity_Branching_CascadeCoefficient`, `Conductivity_Branching_CascadeGeometry`, `Conductivity_Branching_CascadeRankPieces`, `Conductivity_Branching_CascadeStreams`, `Conductivity_Branching_CentralChildCollar`, `Conductivity_Branching_CentralJoinCover`, `Conductivity_Branching_ChildCentralL2`, `Conductivity_Branching_ChildJetScaling`, `Conductivity_Branching_ChildLocalizedJet`, `Conductivity_Branching_ChildTransportFormula`, `Conductivity_Branching_CollarMeasureTransport`, `Conductivity_Branching_Ending`, `Conductivity_Branching_EndingCoordinateTransport`, `Conductivity_Branching_ParentCentralL2`, `Conductivity_Branching_ParentLocalizedJet`, `Conductivity_Branching_TorusEndingCorrection`, `Conductivity_Flux_AntisymmetricFlux`, `Conductivity_Flux_AttachedEndDifferential`, `Conductivity_Flux_AxialFluxBlend`, `Conductivity_Flux_CascadeFluxLocal`, `Conductivity_Flux_CascadeTensorBounds`, `Conductivity_Flux_CentralDistribution`, `Conductivity_Flux_CentralDistributionLaplacian`, `Conductivity_Flux_CompactBoxDivergence`, `Conductivity_Flux_CompactBoxDivergenceC1`, `Conductivity_Flux_CompactFluxDivergence`, `Conductivity_Flux_CubeWeakDivergence`, `Conductivity_Flux_FiberDivergenceC1`, `Conductivity_Flux_LinearTensorEllipticity`, `Conductivity_Flux_SmoothFluxIntegrable`, `Conductivity_Flux_TorusCylinderGreenReal`, `Conductivity_Flux_TwoFluxDivergence`, `Conductivity_Fourier_AffineFourierField`, `Conductivity_Fourier_AngularInverseTensor`, `Conductivity_Fourier_AngularPeriodization`, `Conductivity_Fourier_AngularPhaseTranslation`, `Conductivity_Fourier_AttachedEndPoisson`, `Conductivity_Fourier_CollarAngularInverse`, `Conductivity_Fourier_CompactifiedFourierTail`, `Conductivity_Fourier_CylinderFourier`, `Conductivity_Fourier_EndPoissonDifferential`, `Conductivity_Fourier_EndPoissonJets`, `Conductivity_Fourier_FlatFourierFlux`, `Conductivity_Fourier_GeneralModeFiniteEndNormal`, `Conductivity_Fourier_PoissonTraceRate`, `Conductivity_Fourier_PureMode`, `Conductivity_Fourier_TorusFlatMode`, `Conductivity_Fourier_TorusFourierSmooth`, `Conductivity_Fourier_TorusPeriodicDescent`, `Conductivity_Fourier_TorusPoissonContinuous`, `Conductivity_Fourier_TorusPoissonFlow`, `Conductivity_Fourier_TorusSmoothModeJet`, `Conductivity_Fourier_UndoAngularWeakPair`, `Conductivity_Geometry_AffineBoxPoincare`, `Conductivity_Geometry_CollarAE`, `Conductivity_Geometry_CollarInteriorFacts`, `Conductivity_Geometry_CollarLip`, `Conductivity_Geometry_CollarLocalInverse`, `Conductivity_Geometry_ExtendedCollar`, `Conductivity_Geometry_ParametricPotentialCoordinates`, `Conductivity_Geometry_PhysicalBoxCorrection`, `Conductivity_Geometry_PhysicalCollarBand`, `Conductivity_Geometry_PhysicalCollarTrace`, `Conductivity_Geometry_RectanglePoincare`, `Conductivity_Geometry_SmoothCollarRate`, `Conductivity_Geometry_SmoothCollarTrace`, `Conductivity_Geometry_TorusDirectionalDerivative`, `Conductivity_Geometry_TorusExponential`, `Conductivity_Scalarization_ConcreteFluxScalarization`, `Conductivity_Sobolev_AxialExtension`, `Conductivity_Sobolev_AxialPairRank`, `Conductivity_Sobolev_CentralPhysicalEnergy`, `Conductivity_Sobolev_CentralPhysicalRegion`, `Conductivity_Sobolev_CentralPhysicalTrace`, `Conductivity_Sobolev_CentralPoincare`, `Conductivity_Sobolev_ChildH1Pullback`, `Conductivity_Sobolev_CollarLpPullback`, `Conductivity_Sobolev_MatchedSeamH1`, `Conductivity_Sobolev_NonlinearLp`, `Conductivity_Sobolev_SobolevChain`, `Conductivity_Sobolev_SobolevSmoothOperations`, `Conductivity_Sobolev_SobolevSmoothTests`, `Conductivity_Sobolev_SobolevTraceChain`, `Conductivity_Sobolev_VoltageJetCompletion`, `Conductivity_Sobolev_WallParticular`, `Conductivity_Sources_AngularCoefficient`, `Conductivity_Sources_AngularJet`, `Conductivity_Sources_AngularLocalizedSources`, `Conductivity_Sources_LocalPhysicalCorrection`, `Conductivity_Sources_ParametricSymmetricSources`, `Conductivity_Sources_PhysicalC1Pullback`, `Conductivity_Variational_CentralAnchor`, `Conductivity_Variational_CentralCoercivitySmooth`, `Conductivity_Variational_CentralEnergySpace`, `Conductivity_Variational_CentralHarmonicOpen`, `Conductivity_Variational_CentralJetIdentity`, `Conductivity_Variational_CentralSmoothTrace`, `Conductivity_Variational_CompactBridge`, `Conductivity_Variational_CompactRegularC0`, `Conductivity_Variational_CompactRegularCorrection`, `Conductivity_Variational_CompactSymmetricMoments`, `Conductivity_Variational_ConjugateDiagonal`, `Conductivity_Variational_CrossingGradient`, `Conductivity_Variational_DirectionCalculus`, `Conductivity_Variational_FiberTangentialDerivative`, `Conductivity_Variational_FiniteEndPhysicalDescent`, `Conductivity_Variational_GradientColumns`, `Conductivity_Variational_ParametricMomentSmall`, `Conductivity_Variational_ParametricSpatialDerivative`, `Conductivity_Variational_PhysicalEndLocalLipschitz`, `Conductivity_Variational_PhysicalStripIntegral`, `Conductivity_Variational_PhysicalTerminalBands`, `Conductivity_Variational_QuantitativeGlobalCorrection`, `Conductivity_Variational_RankProjectionFirst`, `Conductivity_Variational_ScaledSmoothSeries`, `Conductivity_Variational_UniformC1Bounds`, `Conductivity_Variational_VoltageBoundaryTrace`, `Conductivity_Walls_CriticalWall`, `Conductivity_Walls_CriticalWallBounds`, `Conductivity_Walls_CriticalWallHomogeneous`, `Conductivity_Walls_CriticalWallTensor`, `Conductivity_Walls_LocalizedMatchedSeam`, `Conductivity_Walls_ParametricWallAmplitude`, `Conductivity_Walls_ParametricWallOperators`, `Conductivity_Walls_PhysicalTerminalCutoff`, `Conductivity_Walls_WallHomogeneous`, `Conductivity_Walls_WallMomentAmplitudeBounds`, `Conductivity_Walls_WallSideMoments`.
--
--   **Imports.** It imports the published bundle `Def_Conductivity`; the bundles `OAIQ059C000`, `OAIQ059C001` and `OAIQ059C002` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ059C006` and `OAIQ059C007`; the statements `OAI.ScalarConductivity.elliptic_fourier_matching_regular` and `OAI.ScalarConductivity.fine_global_scalar_tensor_approximation`.
-- source:
--   OpenAI, Nonuniqueness for bounded measurable scalar conductivities in three dimensions (result family 365), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 365; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-for-Bounded-Measurable-Scalar-Conductivities-in-Three-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_Conductivity
import Definitions.Def_OAIQ059C000
import Definitions.Def_OAIQ059C001
import Definitions.Def_OAIQ059C002

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_TwoFluxDivergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ScalarConductivity

def airyFlux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : Fin 3 → E) (φ : SmoothScalar E) : Fin 5 → SmoothScalar E :=
  ![smoothDirection (v 1) (smoothDirection (v 1) φ),
    -(smoothDirection (v 0) (smoothDirection (v 1) φ)),
    smoothDirection (v 0) (smoothDirection (v 0) φ), 0, 0]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_GradientColumns
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
open Matrix
open scoped Matrix.Norms.Elementwise

lemma gradientColumns_pairing {m : Type*} [Fintype m] [DecidableEq m]
    (D : (Fin 3 → ℝ) →L[ℝ] (m → ℝ)) (F : Matrix (Fin 3) m ℝ) (i j : m) :
    D (F.col j) i = ((gradientColumns D)ᵀ * F) i j := by
  rw [← gradientColumns_apply]
  rfl

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_ScaledSmoothSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory

def cascadeMother (L K : ℝ) (axis : Fin 3) (x : Coord3) : ℝ :=
  cascadeProfile L K (x 0)*cos (x axis)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_CascadeGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory

def cascadeCenter (D k : ℝ) (j : ℕ) : Coord3 :=
  Pi.single 0 ((2*D/k)*(1-1/(2:ℝ)^j))

def cascadeTerm (L K k A : ℝ) (j : ℕ) (x : Coord3) : ℝ :=
  (A*cascadeRatio L K^j)*cascadeProfile L K (cascadePhase (cascadeLength L K) k j (x 0))*
    cos (k*2^j*x (cascadeAxis j))

def cascadeValue (L K k A : ℝ) (x : Coord3) : ℝ := ∑' j : ℕ, cascadeTerm L K k A j x

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_CascadeStreams
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory

def cascadeBaseStream (L K : ℝ) (a : Fin 3) (x : Coord3) : ℝ :=
  deriv (cascadeProfile L K) (x 0)*sin (x a)

def cascadeCrossStream (L K : ℝ) (a b : Fin 3) (x : Coord3) : ℝ :=
  connectorProfile K (K+2)*exp (-3*L)*
    (crossingResidualFirst L (x 0-(K+2+L))/4*sin (4*x b)*sin (x a) -
      crossingResidualSecond L (x 0-(K+2+L))/2*cos (x a)*sin (x a)*sin (2*x b))

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_AntisymmetricFlux
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory

def cascadePotentialMother (L K : ℝ) (a b i j : Fin 3) (x : Coord3) : ℝ :=
  ((if i=0 ∧ j=a then cascadeBaseStream L K a x else 0) +
    (if i=a ∧ j=b then cascadeCrossStream L K a b x else 0)) -
  ((if j=0 ∧ i=a then cascadeBaseStream L K a x else 0) +
    (if j=a ∧ i=b then cascadeCrossStream L K a b x else 0))

def cascadePotential (L K k A : ℝ) (i j : Fin 3) (x : Coord3) : ℝ :=
  ∑' n : ℕ, (A*cascadeRatio L K^n)*
    cascadePotentialMother L K (cascadeAxis n) (cascadeAxis (n+1)) i j
      ((k*2^n) • (x-cascadeCenter (cascadeLength L K) k n))

def cascadeFlux (L K k A : ℝ) (x : Coord3) (i : Fin 3) : ℝ :=
  ∑ j, direction (Pi.single j 1) (cascadePotential L K k A i j) x

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_CascadeFluxLocal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory

def cascadePotentialTerm (L K k A : ℝ) (n : ℕ) (i j : Fin 3) (x : Coord3) : ℝ :=
  (A*cascadeRatio L K^n)*cascadePotentialMother L K (cascadeAxis n) (cascadeAxis (n+1)) i j
    ((k*2^n) • (x-cascadeCenter (cascadeLength L K) k n))

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_DirectionCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory

def wedgePotential (a b : Fin 3) (H : Coord3 → ℝ) (i j : Fin 3) (x : Coord3) : ℝ :=
  (if i=a ∧ j=b then H x else 0) - (if j=a ∧ i=b then H x else 0)

def angularStream (F G : ℝ → ℝ) (a b : Fin 3) (x : Coord3) : ℝ :=
  F (x 0)/4*sin (4*x b)*sin (x a) -
    G (x 0)/2*cos (x a)*sin (x a)*sin (2*x b)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_CrossingGradient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory Matrix

def crossingTensor (L : ℝ) (a b : Fin 3) (x : Coord3) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j =>
    (if i=0 ∧ j=0 then 1 else 0) +
    (if i=a ∧ j=a then crossingXX L (x 0) (x a) (x b) else 0) +
    (if i=b ∧ j=b then crossingYY L (x 0) (x a) (x b) else 0) +
    (if i=a ∧ j=b then crossingXY L (x 0) (x a) (x b) else 0) +
    (if i=b ∧ j=a then crossingXY L (x 0) (x a) (x b) else 0)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_PureMode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory Matrix

def pureModeValue (f : ℝ → ℝ) (a : Fin 3) (x : Coord3) : ℝ :=
  f (x 0)*cos (x a)

def pureModePotential (f : ℝ → ℝ) (a : Fin 3) : Fin 3 → Fin 3 → Coord3 → ℝ :=
  wedgePotential 0 a (fun x => deriv f (x 0)*sin (x a))

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_CascadeTensorBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory Matrix

lemma crossingTensor_symm (L : ℝ) (a b : Fin 3) (x : Coord3) :
    (crossingTensor L a b x).IsSymm := by
  ext i j
  simp only [transpose_apply,crossingTensor]
  simp_rw [and_comm]
  ring

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_CascadeCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory Matrix

def cascadeIndex (D k : ℝ) (x : Coord3) : ℕ := Nat.find (exists_cascade_index D k (x 0))

def cascadeStageTensor (L K k : ℝ) (n : ℕ) (x : Coord3) : Matrix (Fin 3) (Fin 3) ℝ :=
  if cascadePhase (cascadeLength L K) k n (x 0)<K+2 then
    pureModeTensor (connectorAngular K (cascadePhase (cascadeLength L K) k n (x 0))) (cascadeAxis n)
  else crossingTensor L (cascadeAxis n) (cascadeAxis (n+1))
    ((k*2^n) • (x-cascadeCenter (cascadeLength L K) k n)-Pi.single 0 (K+2+L))

def cascadeTensor (L K k : ℝ) (x : Coord3) : Matrix (Fin 3) (Fin 3) ℝ :=
  if 0≤k*x 0 ∧ k*x 0<2*cascadeLength L K then
    cascadeStageTensor L K k (cascadeIndex (cascadeLength L K) k x) x
  else 1

lemma cascadeTensor_symm (L K k : ℝ) (x : Coord3) : (cascadeTensor L K k x).IsSymm := by
  unfold cascadeTensor cascadeStageTensor
  split_ifs
  · exact pureModeTensor_symm _ _
  · exact crossingTensor_symm _ _ _ _
  · exact isSymm_one

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_Ending
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity

section
open Real Set Filter Topology MeasureTheory Matrix

def finiteEndingValue (a J L K : ℝ) (x : Coord3) : ℝ :=
  if x 0<J+2 then pureModeValue (initialConnectorProfile a (1/2) J) 1 x
  else cascadeValue L K 1 (initialConnectorProfile a (1/2) J (J+2))
    (x-Pi.single 0 (J+2))

def finiteEndingPotential (a J L K : ℝ) (i j : Fin 3) (x : Coord3) : ℝ :=
  if x 0<J+2 then pureModePotential (initialConnectorProfile a (1/2) J) 1 i j x
  else cascadePotential L K 1 (initialConnectorProfile a (1/2) J (J+2)) i j
    (x-Pi.single 0 (J+2))

def finiteEndingTensor (a J L K : ℝ) (x : Coord3) : Matrix (Fin 3) (Fin 3) ℝ :=
  if x 0<J+2 then pureModeTensor (initialConnectorAngular a (1/2) J (x 0)) 1
  else cascadeTensor L K 1 (x-Pi.single 0 (J+2))

lemma finiteEndingTensor_symm (a J L K : ℝ) (x : Coord3) :
    (finiteEndingTensor a J L K x).IsSymm := by
  unfold finiteEndingTensor
  split_ifs
  · exact pureModeTensor_symm _ _
  · exact cascadeTensor_symm _ _ _ _

end

open Real Set Filter Topology MeasureTheory Matrix

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_EndingCoordinateTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory Matrix

def permutedDilation (e : Equiv.Perm (Fin 3)) (r : ℝ) (x : Coord3) : Coord3 :=
  fun i => r*x (e i)

end ScalarConductivity



namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory Matrix

def alignedEndingValue (lam k J L K : ℝ) (x : Coord3) : ℝ :=
  finiteEndingValue (lam/k) J L K (permutedDilation angularAxisSwap k x)

def alignedEndingTensor (lam k J L K : ℝ) (x : Coord3) : Mat3 :=
  fun i j => finiteEndingTensor (lam/k) J L K (permutedDilation angularAxisSwap k x)
    (angularAxisSwap i) (angularAxisSwap j)

def alignedEndingPotential (lam k J L K : ℝ) (i j : Fin 3) (x : Coord3) : ℝ :=
  finiteEndingPotential (lam/k) J L K (angularAxisSwap i) (angularAxisSwap j)
    (permutedDilation angularAxisSwap k x)

lemma alignedEndingTensor_symm (lam k J L K : ℝ) (x : Coord3) :
    (alignedEndingTensor lam k J L K x).IsSymm := by
  ext i j
  exact congrFun (congrFun (finiteEndingTensor_symm (lam/k) J L K (permutedDilation angularAxisSwap k x))
    (angularAxisSwap i)) (angularAxisSwap j)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_TorusExponential
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology

lemma torusRate_lower {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ, (1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (h : Fin 2 → ℤ) : torusSize h/2 ≤ torusRate s h := by
  have hq := hs (h 0) (h 1)
  change (1/2)*((h 0:ℝ)^2+(h 1:ℝ)^2) ≤ torusQuadratic s h at hq
  have hq0 : 0≤torusQuadratic s h := le_trans (by positivity) hq
  have hr := Real.sq_sqrt hq0
  have h0 := Real.sqrt_nonneg (torusQuadratic s h)
  have ha := sq_abs (h 0:ℝ)
  have hb := sq_abs (h 1:ℝ)
  have hab := sq_nonneg (|(h 0:ℝ)|-|(h 1:ℝ)|)
  dsimp [torusSize,torusRate]
  nlinarith [abs_nonneg (h 0:ℝ),abs_nonneg (h 1:ℝ)]

lemma torusRate_exp_summable {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ, (1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {r : ℝ} (hr : 0 < r) : Summable (fun h => exp (-r*torusRate s h)) := by
  refine (torus_exp_summable (show 0 < r/2 by positivity)).of_nonneg_of_le
    (fun _ => exp_nonneg _) (fun h => ?_)
  apply exp_le_exp.mpr
  have := mul_le_mul_of_nonpos_left (torusRate_lower hs h) (by linarith : -r≤0)
  linarith

lemma torusRate_poly_exp_summable {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ, (1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (n : ℕ) {r : ℝ} (hr : 0 < r) :
    Summable (fun h => (torusRate s h)^n*exp (-r*torusRate s h)) := by
  refine ((torusRate_exp_summable hs (show 0 < r/2 by positivity)).mul_left
    ((n.factorial:ℝ)/(r/2)^n)).of_nonneg_of_le (fun h => by dsimp [torusRate]; positivity) ?_
  intro h
  exact pow_mul_exp_bound n hr (sqrt_nonneg _)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_TorusPoissonFlow
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal

lemma poissonMultiplier_bound (s : Fin 3 → ℝ) (t : ℝ) (h : Fin 2 → ℤ) :
    ‖(Real.exp (-torusRate s h*|t|):ℂ)‖≤1 := by
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Real.sqrt_nonneg _)) (abs_nonneg _)

attribute [local instance] OAI.ScalarConductivity.torusPoissonFlowMeasureSpace
def torusPoissonFlow (s : Fin 3 → ℝ) (t : ℝ) (f : TorusL2) : TorusL2 :=
    (mFourierBasis (d:=Fin 2)).repr.symm
      (sequenceMultiplier (fun h => (Real.exp (-torusRate s h*|t|):ℂ)) 1
        zero_le_one (poissonMultiplier_bound s t) ((mFourierBasis (d:=Fin 2)).repr f))

lemma torusPoissonFlow_coeff (s : Fin 3 → ℝ) (t : ℝ) (f : TorusL2) (h : Fin 2 → ℤ) :
    mFourierCoeff (torusPoissonFlow s t f) h=
      (Real.exp (-torusRate s h*|t|):ℂ)*mFourierCoeff f h := by
  rw [←mFourierBasis_repr,torusPoissonFlow,LinearIsometryEquiv.apply_symm_apply,
    sequenceMultiplier_apply,mFourierBasis_repr]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_AffineBoxPoincare
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.instCoeFunSubtypeForallBox3RealMemSubmoduleCentralSmoothFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory

def boxRescale (a r : Box3) (z : Box3) : Box3 :=
  ((a.1.1+r.1.1*z.1.1,a.1.2+r.1.2*z.1.2),a.2+r.2*z.2)

def closedBox (a r : Box3) : Set Box3 :=
  (Icc a.1.1 (a.1.1+r.1.1) ×ˢ Icc a.1.2 (a.1.2+r.1.2)) ×ˢ Icc a.2 (a.2+r.2)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_ExtendedCollar
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.instCoeFunSubtypeForallBox3RealMemSubmoduleCentralSmoothFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory

lemma squareFace_abs_le (i : Fin 4) {a : ℝ} (ha : |a|≤1) (k : Fin 2) :
    |squareFace i a k|≤1 := by
  fin_cases k
  · exact (le_max_left _ _).trans (squareFace_max i ha).le
  · exact (le_max_right _ _).trans (squareFace_max i ha).le

lemma sourceRadius_trim_bounds (j : Fin 4) {t b : ℝ}
    (ht : centralThickness≤t ∧ t≤2*centralThickness) (hb : |b|≤1) :
    centralInnerY≤ sourceCollarRadius j t b ∧ sourceCollarRadius j t b ≤ centralOuterY := by
  have hq := squareFace_abs_le j hb 0
  have hqt : |(1-t)*squareFace j b 0|≤1-centralThickness := by
    have ht0 : 0≤1-t := by norm_num [centralThickness] at ht; linarith
    rw [abs_mul,abs_of_nonneg ht0]
    have hh := mul_le_mul_of_nonneg_left hq ht0
    linarith [ht.1]
  have hh := abs_le.mp hqt
  dsimp [sourceCollarRadius,centralInnerY,centralOuterY,sourceRadialCenter,sourceRadialWidth,sourceHole,centralThickness] at *
  constructor <;> linarith

lemma sourceParentCollar_parent (i j : Fin 4) {x : Fin 3 → ℝ}
    (hx : x∈sourceExtendedBox centralThickness (2*centralThickness)) :
    centralParentFootprint (sourcePairCoordinates (sourceCollarPiece i j x)).1 ∧
      |(sourcePairCoordinates (sourceCollarPiece i j x)).2| ≤ centralHeight := by
  obtain ⟨ht,ha,hb⟩ := mem_sourceExtendedBox.mp hx
  have hr := sourceRadius_trim_bounds j ht hb
  have hr0 : 0≤ sourceCollarRadius j (x 0) (x 2) := by
    have hh : 0 < centralInnerY := by norm_num [centralInnerY,sourceHole,sourceRadialWidth,centralThickness]
    linarith
  have hL : 0 < sourceLength := by norm_num [sourceLength]
  have ht0 : 0≤1-x 0 := by norm_num [centralThickness] at ht; linarith
  have hq0 := squareFace_abs_le i ha 0
  have hq1 := squareFace_abs_le i ha 1
  have hq2 := squareFace_abs_le j hb 1
  have hx0 : |sourceLength*sourceCollarRadius j (x 0) (x 2)*squareFace i (x 1) 0| ≤ centralOuterX := by
    rw [abs_mul,abs_mul,abs_of_pos hL,abs_of_nonneg hr0]
    have hh := mul_le_mul_of_nonneg_left hq0 (mul_nonneg hL.le hr0)
    dsimp [centralOuterX,centralOuterY] at *
    nlinarith
  have hx1 : |sourceCollarRadius j (x 0) (x 2)*squareFace i (x 1) 1| ≤ centralOuterY := by
    rw [abs_mul,abs_of_nonneg hr0]
    nlinarith
  have hin : centralInnerX≤|sourceLength*sourceCollarRadius j (x 0) (x 2)*squareFace i (x 1) 0| ∨
      centralInnerY≤|sourceCollarRadius j (x 0) (x 2)*squareFace i (x 1) 1| := by
    have hm := squareFace_max i ha
    rcases max_cases |squareFace i (x 1) 0| |squareFace i (x 1) 1| with h|h
    · left
      rw [abs_mul,abs_mul,abs_of_pos hL,abs_of_nonneg hr0,←h.1,hm,mul_one]
      dsimp [centralInnerX,centralInnerY] at *
      nlinarith
    · right
      rw [abs_mul,abs_of_nonneg hr0,←h.1,hm,mul_one]
      exact hr.1
  have ht1 : |(1-x 0)*squareFace j (x 2) 1| ≤ centralHeight := by
    rw [abs_mul,abs_of_nonneg ht0]
    dsimp [centralHeight]
    nlinarith [ht.1]
  exact ⟨⟨hx0,hx1,hin⟩,ht1⟩

lemma sourceParentCollar_avoids (i j : Fin 4) {x : Fin 3 → ℝ}
    (hx : x∈sourceExtendedBox centralThickness (2*centralThickness)) :
    centralChildHeight≤|(sourceCollarPiece i j x) 2| ∨
      (centralAvoidChild 1 ((sourceCollarPiece i j x) 0,(sourceCollarPiece i j x) 1) ∧
        centralAvoidChild (-1) ((sourceCollarPiece i j x) 0,(sourceCollarPiece i j x) 1)) := by
  obtain ⟨ht,ha,hb⟩ := mem_sourceExtendedBox.mp hx
  have hr := sourceRadius_trim_bounds j ht hb
  have hr0 : 0≤ sourceCollarRadius j (x 0) (x 2) := by
    have hh : 0 < centralInnerY := by norm_num [centralInnerY,sourceHole,sourceRadialWidth,centralThickness]
    linarith
  have hL : 0 < sourceLength := by norm_num [sourceLength]
  fin_cases j
  · right
    change 0≤ sourceCollarRadius 0 (x 0) (x 2) at hr0
    have hlarge : (999:ℝ)/1000≤ sourceCollarRadius 0 (x 0) (x 2) := by
      norm_num [sourceCollarRadius,squareFace,squareFaceBase,squareFaceDirection,Matrix.cons_val_succ,sourceRadialCenter,sourceRadialWidth,sourceHole,centralThickness] at ht ⊢
      linarith
    have hm := squareFace_max i ha
    rcases max_cases |squareFace i (x 1) 0| |squareFace i (x 1) 1| with h|h
    · have he : |(sourceCollarPiece i 0 x) 0|=sourceLength*sourceCollarRadius 0 (x 0) (x 2) := by
        simp only [sourceCollarPiece,Matrix.cons_val_zero,abs_mul,abs_of_pos hL,abs_of_nonneg hr0]
        rw [←h.1,hm,mul_one]
      have hbig : (1598:ℝ)/1000≤|(sourceCollarPiece i 0 x) 0| := by rw [he]; norm_num [sourceLength]; linarith
      have hb1 := abs_sub_le ((sourceCollarPiece i 0 x) 0) sourceOffset
      have hb2 := abs_sub_le ((sourceCollarPiece i 0 x) 0) (-sourceOffset)
      have hlow1 := abs_add_le ((sourceCollarPiece i 0 x) 0-sourceOffset) sourceOffset
      have hlow2 := abs_add_le ((sourceCollarPiece i 0 x) 0+sourceOffset) (-sourceOffset)
      simp only [sub_add_cancel,add_neg_cancel_right] at hlow1 hlow2
      constructor <;> apply Or.inl
      · norm_num [centralChildOuterX,sourceScale,sourceRadialWidth,sourceHole,centralThickness,sourceOffset] at *
        linarith
      · norm_num [centralChildOuterX,sourceScale,sourceRadialWidth,sourceHole,centralThickness,sourceOffset] at *
        linarith
    · have he : |(sourceCollarPiece i 0 x) 1|=sourceCollarRadius 0 (x 0) (x 2) := by
        simp only [sourceCollarPiece,Matrix.cons_val_one,Matrix.cons_val_zero,abs_mul,abs_of_nonneg hr0]
        rw [←h.1,hm,mul_one]
      have hh : centralChildOuterY≤|(sourceCollarPiece i 0 x) 1| := by
        rw [he]
        norm_num [centralChildOuterY,sourceScale,sourceLength,sourceRadialWidth,sourceHole,centralThickness]
        linarith
      exact ⟨Or.inr (Or.inl hh),Or.inr (Or.inl hh)⟩
  · left
    simp only [sourceCollarPiece,Matrix.cons_val_two,squareFace,squareFaceBase,squareFaceDirection,
      Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    norm_num [centralChildHeight,sourceScale,centralThickness] at ht ⊢
    linarith [le_abs_self (1-x 0),neg_le_abs (x 0-1)]
  · right
    change 0≤ sourceCollarRadius 2 (x 0) (x 2) at hr0
    have hsmall : sourceCollarRadius 2 (x 0) (x 2)≤(31:ℝ)/1000 := by
      change sourceRadialCenter+sourceRadialWidth*(1-x 0)*((-1:ℝ)+x 2*0)≤31/1000
      norm_num [sourceRadialCenter,sourceRadialWidth,sourceHole,centralThickness] at ht ⊢
      linarith
    have hq := squareFace_abs_le i ha 0
    have hsmall' : |(sourceCollarPiece i 2 x) 0|≤(1:ℝ)/20 := by
      simp only [sourceCollarPiece,Matrix.cons_val_zero,abs_mul,abs_of_pos hL,abs_of_nonneg hr0]
      norm_num [sourceLength]
      nlinarith
    have hlow1 := abs_sub_le sourceOffset ((sourceCollarPiece i 2 x) 0)
    have hlow2 := abs_sub_le (-sourceOffset) ((sourceCollarPiece i 2 x) 0)
    have htri1 := abs_add_le (sourceOffset-(sourceCollarPiece i 2 x) 0) ((sourceCollarPiece i 2 x) 0)
    have htri2 := abs_add_le (-sourceOffset-(sourceCollarPiece i 2 x) 0) ((sourceCollarPiece i 2 x) 0)
    simp only [sub_add_cancel,abs_sub_comm sourceOffset,abs_sub_comm (-sourceOffset)] at htri1 htri2
    have hc1 : centralChildOuterX≤|(sourceCollarPiece i 2 x) 0-sourceOffset| := by
      norm_num [centralChildOuterX,sourceScale,sourceRadialWidth,sourceHole,centralThickness,sourceOffset] at *
      linarith
    have hc2 : centralChildOuterX≤|(sourceCollarPiece i 2 x) 0+sourceOffset| := by
      norm_num [centralChildOuterX,sourceScale,sourceRadialWidth,sourceHole,centralThickness,sourceOffset] at *
      linarith
    exact ⟨Or.inl (by simpa using hc1),Or.inl (by simpa using hc2)⟩
  · left
    simp only [sourceCollarPiece,Matrix.cons_val_two,squareFace,squareFaceBase,squareFaceDirection,
      Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    norm_num [centralChildHeight,sourceScale,centralThickness] at ht ⊢
    linarith [le_abs_self (1-x 0),neg_le_abs (x 0-1)]

theorem sourceParentCollar_central (i j : Fin 4) {x : Fin 3 → ℝ}
    (hx : x∈sourceExtendedBox centralThickness (2*centralThickness)) :
    sourcePairCoordinates (sourceCollarPiece i j x)∈centralClosed :=
  ⟨(sourceParentCollar_parent i j hx).1,(sourceParentCollar_parent i j hx).2,
    sourceParentCollar_avoids i j hx⟩

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_CentralChildCollar
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.instCoeFunSubtypeForallBox3RealMemSubmoduleCentralSmoothFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory

lemma sourceRadius_child_bounds (j : Fin 4) {t b : ℝ}
    (ht : -2*centralThickness≤t ∧ t≤ -centralThickness) (hb : |b|≤1) :
    (29:ℝ)/1000≤ sourceCollarRadius j t b ∧ sourceCollarRadius j t b≤1001/1000 := by
  have hq := squareFace_abs_le j hb 0
  have hqt : |(1-t)*squareFace j b 0|≤1+2*centralThickness := by
    have ht0 : 0≤1-t := by norm_num [centralThickness] at ht; linarith
    rw [abs_mul,abs_of_nonneg ht0]
    have hh := mul_le_mul_of_nonneg_left hq ht0
    linarith [ht.1]
  have hh := abs_le.mp hqt
  dsimp [sourceCollarRadius,sourceRadialCenter,sourceRadialWidth,sourceHole,centralThickness] at *
  constructor <;> linarith

lemma sourceChildCollar_bounds (i j : Fin 4) {x : Fin 3 → ℝ}
    (hx : x∈sourceExtendedBox (-2*centralThickness) (-centralThickness)) :
    |(sourceCollarPiece i j x) 0|≤(1602:ℝ)/1000 ∧
    |(sourceCollarPiece i j x) 1|≤(1001:ℝ)/1000 ∧
    |(sourceCollarPiece i j x) 2|≤(1002:ℝ)/1000 := by
  obtain ⟨ht,ha,hb⟩ := mem_sourceExtendedBox.mp hx
  have hr := sourceRadius_child_bounds j ht hb
  have hr0 : 0≤ sourceCollarRadius j (x 0) (x 2) := by linarith
  have ht0 : 0≤1-x 0 := by norm_num [centralThickness] at ht; linarith
  have h0 := squareFace_abs_le i ha 0
  have h1 := squareFace_abs_le i ha 1
  have h2 := squareFace_abs_le j hb 1
  have hh0 := mul_le_mul_of_nonneg_left h0 hr0
  have hh1 := mul_le_mul_of_nonneg_left h1 hr0
  have hh2 := mul_le_mul_of_nonneg_left h2 ht0
  change |sourceLength*sourceCollarRadius j (x 0) (x 2)*squareFace i (x 1) 0|≤_ ∧
    |sourceCollarRadius j (x 0) (x 2)*squareFace i (x 1) 1|≤_ ∧
    |(1-x 0)*squareFace j (x 2) 1|≤_
  simp only [abs_mul,abs_of_nonneg hr0,abs_of_nonneg ht0]
  norm_num [sourceLength,centralThickness] at ht ⊢
  constructor
  · nlinarith
  · constructor <;> linarith

lemma sourceChildCoordinates_offset (σ : ℝ) (y : Fin 3 → ℝ) :
    sourceChildCoordinates σ y 0-σ*sourceOffset=sourceScale*y 1 := by
  simp [sourceChildCoordinates]

lemma sourceChildCollar_parent (i j : Fin 4) {σ : ℝ} (hσ : |σ|=1) {x : Fin 3 → ℝ}
    (hx : x∈sourceExtendedBox (-2*centralThickness) (-centralThickness)) :
    centralParentFootprint (sourcePairCoordinates (sourceChildCoordinates σ (sourceCollarPiece i j x))).1 ∧
      |(sourceChildCoordinates σ (sourceCollarPiece i j x)) 2| ≤ centralHeight := by
  have hb := sourceChildCollar_bounds i j hx
  let y := sourceCollarPiece i j x
  have ha : |σ*sourceOffset|=sourceOffset := by rw [abs_mul,hσ,one_mul]; norm_num [sourceOffset]
  have hs : 0 < sourceScale := by norm_num [sourceScale]
  have hxa := abs_add_le (sourceScale*y 1) (σ*sourceOffset)
  rw [abs_mul,abs_of_pos hs,ha] at hxa
  have hxb := abs_add_le (-sourceScale*y 1) (sourceScale*y 1+σ*sourceOffset)
  have he : -sourceScale*y 1+(sourceScale*y 1+σ*sourceOffset)=σ*sourceOffset := by ring
  rw [he,ha,abs_mul,abs_neg,abs_of_pos hs] at hxb
  change (|sourceScale*y 1+σ*sourceOffset| ≤ centralOuterX ∧
    |sourceScale*y 0| ≤ centralOuterY ∧ (centralInnerX≤|sourceScale*y 1+σ*sourceOffset| ∨
      centralInnerY≤|sourceScale*y 0|)) ∧ |sourceScale*y 2| ≤ centralHeight
  simp only [abs_mul,abs_of_pos hs]
  constructor
  · refine ⟨?_,?_,Or.inl ?_⟩
    · dsimp [centralOuterX,sourceLength,sourceRadialWidth,sourceHole,centralThickness,sourceScale,sourceOffset]
      dsimp [sourceScale,sourceOffset] at hxa
      linarith [hb.2.1]
    · norm_num [centralOuterY,sourceRadialWidth,sourceHole,centralThickness,sourceScale]
      linarith [hb.1]
    · norm_num [centralInnerX,sourceLength,sourceHole,sourceRadialWidth,centralThickness,sourceScale,sourceOffset]
      dsimp [sourceScale,sourceOffset] at hxb
      linarith [hb.2.1]
  · norm_num [sourceScale,centralHeight,centralThickness]
    linarith [hb.2.2]

lemma sourceChildCollar_other (i j : Fin 4) {σ : ℝ} (hσ : |σ|=1) {x : Fin 3 → ℝ}
    (hx : x∈sourceExtendedBox (-2*centralThickness) (-centralThickness)) :
    centralAvoidChild (-σ) (sourcePairCoordinates (sourceChildCoordinates σ (sourceCollarPiece i j x))).1 := by
  apply Or.inl
  have hb := (sourceChildCollar_bounds i j hx).2.1
  let y := sourceCollarPiece i j x
  have ha : |2*σ*sourceOffset|=2*sourceOffset := by rw [abs_mul,abs_mul,hσ]; norm_num [sourceOffset]
  have ht := abs_add_le (-sourceScale*y 1) (sourceScale*y 1+2*σ*sourceOffset)
  have he : -sourceScale*y 1+(sourceScale*y 1+2*σ*sourceOffset)=2*σ*sourceOffset := by ring
  rw [he,ha,abs_mul,abs_neg,abs_of_pos (show 0 < sourceScale by norm_num [sourceScale])] at ht
  change centralChildOuterX≤|sourceScale*y 1+σ*sourceOffset-(-σ)*sourceOffset|
  have he' : sourceScale*y 1+σ*sourceOffset-(-σ)*sourceOffset=sourceScale*y 1+2*σ*sourceOffset := by ring
  rw [he']
  norm_num [centralChildOuterX,sourceScale,sourceRadialWidth,sourceHole,centralThickness,sourceOffset]
  dsimp [sourceScale,sourceOffset] at ht
  linarith

lemma sourceChildCollar_same (i j : Fin 4) (σ : ℝ) {x : Fin 3 → ℝ}
    (hx : x∈sourceExtendedBox (-2*centralThickness) (-centralThickness)) :
    centralChildHeight≤|(sourceChildCoordinates σ (sourceCollarPiece i j x)) 2| ∨
      centralAvoidChild σ (sourcePairCoordinates (sourceChildCoordinates σ (sourceCollarPiece i j x))).1 := by
  obtain ⟨ht,ha,hb⟩ := mem_sourceExtendedBox.mp hx
  have hr := sourceRadius_child_bounds j ht hb
  have hr0 : 0≤ sourceCollarRadius j (x 0) (x 2) := by linarith
  have hL : 0 < sourceLength := by norm_num [sourceLength]
  have hs : 0 < sourceScale := by norm_num [sourceScale]
  have ht0 : 0≤1-x 0 := by norm_num [centralThickness] at ht; linarith
  have hcoord : (sourceChildCoordinates σ (sourceCollarPiece i j x)) 0-σ*sourceOffset=
      sourceScale*sourceCollarRadius j (x 0) (x 2)*squareFace i (x 1) 1 := by
    rw [sourceChildCoordinates_offset]
    change sourceScale*(sourceCollarRadius j (x 0) (x 2)*squareFace i (x 1) 1)=_
    ring
  change centralChildHeight≤|sourceScale*((1-x 0)*squareFace j (x 2) 1)| ∨
    (centralChildOuterX≤|(sourceChildCoordinates σ (sourceCollarPiece i j x)) 0-σ*sourceOffset| ∨
      centralChildOuterY≤|sourceScale*(sourceLength*sourceCollarRadius j (x 0) (x 2)*squareFace i (x 1) 0)| ∨
      (|(sourceChildCoordinates σ (sourceCollarPiece i j x)) 0-σ*sourceOffset| ≤ centralChildInnerX ∧
        |sourceScale*(sourceLength*sourceCollarRadius j (x 0) (x 2)*squareFace i (x 1) 0)| ≤ centralChildInnerY))
  rw [hcoord]
  simp only [abs_mul,abs_of_pos hs,abs_of_pos hL,abs_of_nonneg hr0,abs_of_nonneg ht0]
  fin_cases j
  · right
    have hrad : 1+sourceRadialWidth*centralThickness≤ sourceCollarRadius 0 (x 0) (x 2) := by
      norm_num [sourceCollarRadius,squareFace,squareFaceBase,squareFaceDirection,Matrix.cons_val_succ,
        sourceRadialCenter,sourceRadialWidth,sourceHole,centralThickness] at ht ⊢
      linarith
    have hm := squareFace_max i ha
    rcases max_cases |squareFace i (x 1) 0| |squareFace i (x 1) 1| with h|h
    · right; left
      rw [←h.1,hm,mul_one]
      dsimp [centralChildOuterY]
      nlinarith [mul_nonneg hs.le hL.le]
    · left
      rw [←h.1,hm,mul_one]
      dsimp [centralChildOuterX]
      exact mul_le_mul_of_nonneg_left hrad hs.le
  · left
    norm_num [squareFace,squareFaceBase,squareFaceDirection,Matrix.cons_val_succ,centralChildHeight,centralThickness,sourceScale] at ht ⊢
    linarith
  · right; right; right
    have hrad : sourceCollarRadius 2 (x 0) (x 2)≤ sourceHole-sourceRadialWidth*centralThickness := by
      change sourceRadialCenter+sourceRadialWidth*(1-x 0)*((-1:ℝ)+x 2*0)≤_
      norm_num [sourceRadialCenter,sourceRadialWidth,sourceHole,centralThickness] at ht ⊢
      linarith
    have h0 := squareFace_abs_le i ha 0
    have h1 := squareFace_abs_le i ha 1
    change 0≤ sourceCollarRadius 2 (x 0) (x 2) at hr0
    have hh0 := mul_le_mul_of_nonneg_left h0 hr0
    have hh1 := mul_le_mul_of_nonneg_left h1 hr0
    constructor
    · dsimp [centralChildInnerX,sourceScale,sourceHole,sourceRadialWidth,centralThickness] at *
      nlinarith
    · dsimp [centralChildInnerY,sourceScale,sourceLength,sourceHole,sourceRadialWidth,centralThickness] at *
      nlinarith
  · left
    norm_num [squareFace,squareFaceBase,squareFaceDirection,Matrix.cons_val_succ,centralChildHeight,centralThickness,sourceScale] at ht ⊢
    linarith

theorem sourceChildCollar_central (i j : Fin 4) {σ : ℝ} (hσ : σ=1 ∨ σ= -1)
    {x : Fin 3 → ℝ} (hx : x∈sourceExtendedBox (-2*centralThickness) (-centralThickness)) :
    sourcePairCoordinates (sourceChildCoordinates σ (sourceCollarPiece i j x))∈centralClosed := by
  have ha : |σ|=1 := by rcases hσ with rfl|rfl <;> norm_num
  have hp := sourceChildCollar_parent i j ha hx
  refine ⟨hp.1,hp.2,?_⟩
  rcases sourceChildCollar_same i j σ hx with ht|hs
  · exact Or.inl ht
  · right
    have ho := sourceChildCollar_other i j ha hx
    rcases hσ with rfl|rfl
    · exact ⟨hs,ho⟩
    · exact ⟨by simpa using ho,hs⟩

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_RectanglePoincare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory

def RectFootprint.poincareConstant (Q : RectFootprint) (lo hi : ℝ) : ℝ :=
  4*((Q.xu-Q.xl)^2+(Q.yu-Q.yl)^2+(hi-lo)^2)

open Set MeasureTheory

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_CentralAnchor
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.instCoeFunSubtypeForallBox3RealMemSubmoduleCentralSmoothFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory

def centralConnector : RectFootprint := ⟨3/2,centralOuterX,-centralOuterY,centralOuterY⟩

def centralAnchorData : ℕ → RectFootprint×(ℝ×ℝ)
  | 0 => (centralParentStrip 0,centralChildHeight,centralHeight)
  | 1 => (centralParentStrip 1,centralChildHeight,centralHeight)
  | 2 => (centralParentStrip 2,centralChildHeight,centralHeight)
  | 3 => (centralParentStrip 3,centralChildHeight,centralHeight)
  | 4 => (centralConnector,-centralHeight,centralHeight)
  | 5 => (centralParentStrip 0,-centralHeight,-centralChildHeight)
  | 6 => (centralParentStrip 1,-centralHeight,-centralChildHeight)
  | 7 => (centralParentStrip 2,-centralHeight,-centralChildHeight)
  | 8 => (centralParentStrip 3,-centralHeight,-centralChildHeight)
  | _ => (centralParentStrip 0,centralChildHeight,centralHeight)

def centralAnchorPiece (n : ℕ) : Set Box3 :=
  (centralAnchorData n).1.prism (centralAnchorData n).2.1 (centralAnchorData n).2.2

def centralAnchor : Set Box3 := patchCluster centralAnchorPiece 8

def centralAnchorLocalConstant (n : ℕ) : ℝ :=
  (centralAnchorData n).1.poincareConstant (centralAnchorData n).2.1 (centralAnchorData n).2.2

def centralAnchorConstant : ℝ := patchPoincareConstant volume centralAnchorPiece centralAnchorLocalConstant 8

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_PhysicalCollarTrace
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.instCoeFunSubtypeForallBox3RealMemSubmoduleCentralSmoothFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity

open Set MeasureTheory

def sourcePairMeasurable : (Fin 3 → ℝ) ≃ᵐ Box3 :=
  threeArrow.trans (MeasurableEquiv.prodAssoc (α:=ℝ) (β:=ℝ) (γ:=ℝ)).symm

lemma sourcePairMeasurable_apply (x : Fin 3 → ℝ) : sourcePairMeasurable x=sourcePairCoordinates x := rfl

lemma sourcePair_volume : MeasurePreserving sourcePairMeasurable :=
  (volume_preserving_prodAssoc (α₁:=ℝ) (β₁:=ℝ) (γ₁:=ℝ)).symm.comp threeArrow_volume

def centralPhysical : Set (Fin 3 → ℝ) := sourcePairCoordinates ⁻¹' centralClosed

lemma centralPhysical_compact : IsCompact centralPhysical := by
  exact sourcePairCLE.toHomeomorph.isCompact_preimage.mpr centralClosed_compact

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_CentralPhysicalTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory UnitAddTorus

def centralTraceConstant : ℝ := ((1+1/centralThickness)*physicalRayConstant)*(sourceScale^3)⁻¹

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_CentralPoincare
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory

def centralColumnConstant (i : Fin 4) (j k : Fin 5) : ℝ :=
  let B := (centralColumn i j k).poincareConstant (-centralHeight) centralHeight
  let R := (centralColumn i j k).prism (-centralHeight) centralHeight
  centralAnchorConstant+2*B+4*volume.real R/(volume.real (centralAnchor∩R))*(centralAnchorConstant+B)

def centralPoincareConstant : ℝ := centralAnchorConstant+
  ∑ i : Fin 4,∑ j : Fin 5,∑ k : Fin 5,centralColumnConstant i j k

open Set MeasureTheory
open scoped ENNReal

instance centralMeasure_finite : IsFiniteMeasure centralMeasure := by
  constructor
  simpa [centralMeasure] using centralClosed_compact.measure_lt_top

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_CentralSmoothTrace
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity

section
open Set MeasureTheory UnitAddTorus
open scoped ENNReal

lemma unitTorus_volume_eq_normalized : (volume : Measure (UnitAddTorus (Fin 2)))=normalizedTorusVolume := by
  change Measure.pi (fun _ : Fin 2 => (volume : Measure UnitAddCircle))=_
  simp only [unitCircle_volume_eq_haar]
  rfl

end

open Set MeasureTheory UnitAddTorus
open scoped ENNReal

def centralSmoothOne : centralSmoothFunctions := ⟨fun _ => 1,by change ContDiff ℝ (↑(⊤ : ℕ∞)) (fun _ : Box3 => (1 : ℝ)); exact contDiff_const⟩

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_CompactBoxDivergence
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralMeasure_finite _root_.OAI.ScalarConductivity.instCoeFunSubtypeForallBox3RealMemSubmoduleCentralSmoothFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma cube_partial_fiber (f : Box3 → ℝ) (p : Box3) :
    cubePartial f ((0,0),1) p=wallDerivative f p := rfl

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

lemma wallAlong_smooth [ProperSpace E] (d : E) {f : E × ℝ → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (wallAlong d f) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Walls_WallHomogeneous
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity

section
open Set MeasureTheory Filter Topology
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

omit [ProperSpace E] in
lemma wallAlong_mul (d : E) {f g : E × ℝ → ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (p : E × ℝ) :
    wallAlong d (fun q => f q*g q) p=wallAlong d f p*g p+f p*wallAlong d g p := by
  simp only [wallAlong,fderiv_fun_mul (hf p) (hg p),add_apply,
    smul_apply,smul_eq_mul]
  ring

omit [ProperSpace E] in
lemma wall_mixed_commute (d : E) {v : E × ℝ → ℝ}
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v) (p : E × ℝ) :
    wallDerivative (wallAlong d v) p=wallAlong d (wallDerivative v) p := by
  have hv2 : ContDiff ℝ 2 v := hv.of_le (show ((2 : ℕ∞) : WithTop ℕ∞)≤↑(⊤ : ℕ∞) from WithTop.coe_le_coe.mpr le_top)
  have hd : DifferentiableAt ℝ (fderiv ℝ v) p :=
    (hv2.fderiv_right (show (1 : WithTop ℕ∞)+1≤2 by norm_num)).contDiffAt.differentiableAt (by norm_num)
  unfold wallDerivative wallAlong
  rw [fderiv_clm_apply hd (differentiableAt_const _),fderiv_clm_apply hd (differentiableAt_const _)]
  simpa using hv2.contDiffAt.isSymmSndFDerivAt (by simp) (0,1) (d,0)

def wallHomogeneousNumerator (d : E) (v : E × ℝ → ℝ) (a : E → ℝ) (p : E × ℝ) : ℝ :=
  -2*a p.1*(wallAlong d v p-wallAlong d v (p.1,0))-
    wallAlong d (fun q => a q.1) p*(v p-v (p.1,0))

lemma wallHomogeneousNumerator_smooth (d : E) {v : E × ℝ → ℝ} {a : E → ℝ}
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v) (ha : ContDiff ℝ (↑(⊤ : ℕ∞)) a) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (wallHomogeneousNumerator d v a) := by
  exact ((contDiff_const.mul (ha.comp contDiff_fst)).mul
    ((wallAlong_smooth d hv).sub ((wallAlong_smooth d hv).comp (contDiff_fst.prodMk contDiff_const)))).sub
    ((wallAlong_smooth d (ha.comp contDiff_fst)).mul
      (hv.sub (hv.comp (contDiff_fst.prodMk contDiff_const))))

omit [ProperSpace E] in
lemma wallHomogeneousNumerator_zero (d : E) (v : E × ℝ → ℝ) (a : E → ℝ) (x : E) :
    wallHomogeneousNumerator d v a (x,0)=0 := by
  simp only [wallHomogeneousNumerator,sub_self,mul_zero]

omit [ProperSpace E] in
lemma wallDerivative_pullback_along (d : E) {a : E → ℝ}
    (ha : ContDiff ℝ (↑(⊤ : ℕ∞)) a) (p : E × ℝ) :
    wallDerivative (wallAlong d (fun q => a q.1)) p=0 := by
  have he : wallDerivative (fun q : E × ℝ => a q.1)=fun _ => 0 :=
    funext (wallDerivative_pullback (ha.differentiable (by simp)))
  rw [wall_mixed_commute d (v := fun q => a q.1) (ha.comp contDiff_fst),he]
  simp [wallAlong]

theorem wall_homogeneous_flux_equations (d : E) {v : E × ℝ → ℝ} {a : E → ℝ}
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v) (ha : ContDiff ℝ (↑(⊤ : ℕ∞)) a) (p : E × ℝ) :
    wallDerivative (fun q : E × ℝ => a q.1) p=0 ∧
    wallAlong d (fun q => a q.1*wallDerivative v q) p+
      wallDerivative (fun q => a q.1*wallAlong d v q+
        wallHomogeneousNumerator d v a q) p=0 := by
  have hvd := hv.differentiable (by simp)
  have had := ha.differentiable (by simp)
  have hAc : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun q : E × ℝ => a q.1) := ha.comp contDiff_fst
  have hA := hAc.differentiable (by simp)
  have hs := (wallAlong_smooth d hv).differentiable (by simp)
  have hz := (wallDerivative_smooth hv).differentiable (by simp)
  have has := (wallAlong_smooth d hAc).differentiable (by simp)
  have hv₀ : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x : E => v (x,0)) :=
    hv.comp (contDiff_id.prodMk contDiff_const)
  have hvs₀ : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x : E => wallAlong d v (x,0)) :=
    (wallAlong_smooth d hv).comp (contDiff_id.prodMk contDiff_const)
  refine ⟨wallDerivative_pullback had p,?_⟩
  rw [wallAlong_mul d hA hz,
    wallDerivative_add (f := fun q => a q.1*wallAlong d v q) (hA.mul hs) ((wallHomogeneousNumerator_smooth d hv ha).differentiable (by simp)),
    wallDerivative_mul hA hs,wallDerivative_pullback had]
  have hneg : Differentiable ℝ (fun q : E × ℝ => -2*a q.1) := (differentiable_const (-2)).mul hA
  have hsub : Differentiable ℝ (fun q : E × ℝ => wallAlong d v q-wallAlong d v (q.1,0)) :=
    hs.sub ((hvs₀.comp contDiff_fst).differentiable (by simp))
  have hsubv : Differentiable ℝ (fun q : E × ℝ => v q-v (q.1,0)) :=
    hvd.sub ((hv₀.comp contDiff_fst).differentiable (by simp))
  change _+(_+_+wallDerivative (fun q => -2*a q.1*(wallAlong d v q-wallAlong d v (q.1,0))-
    wallAlong d (fun q => a q.1) q*(v q-v (q.1,0))) p)=0
  rw [wallDerivative_sub (f := fun q => -2*a q.1*(wallAlong d v q-wallAlong d v (q.1,0)))
      (g := fun q => wallAlong d (fun q => a q.1) q*(v q-v (q.1,0)))
      (hneg.mul hsub) (has.mul hsubv),
    wallDerivative_mul hneg hsub,wallDerivative_mul has hsubv,
    wallDerivative_pullback (a := fun x => -2*a x) (((differentiable_const (-2)).mul had)),
    wallDerivative_sub (f := wallAlong d v) (g := fun q => wallAlong d v (q.1,0)) hs ((hvs₀.comp contDiff_fst).differentiable (by simp)),
    wallDerivative_sub (f := v) (g := fun q => v (q.1,0)) hvd ((hv₀.comp contDiff_fst).differentiable (by simp)),
    wallDerivative_pullback (hvs₀.differentiable (by simp)),
    wallDerivative_pullback (hv₀.differentiable (by simp)),
    wallDerivative_pullback_along d ha,wall_mixed_commute d hv]
  ring

end

open Set MeasureTheory Filter Topology
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

omit [ProperSpace E] in
lemma wallAlong_zero_trace (d : E) {f : E × ℝ → ℝ}
    (hf : Differentiable ℝ f) (hz : ∀ x,f (x,0)=0) (x : E) :
    wallAlong d f (x,0)=0 := by
  have hin : HasFDerivAt (fun q : E => (q,(0:ℝ)))
      (ContinuousLinearMap.inl ℝ E ℝ) x := (ContinuousLinearMap.inl ℝ E ℝ).hasFDerivAt
  have hc := (hf (x,0)).hasFDerivAt.comp x hin
  have hc0 : HasFDerivAt (fun _ : E => (0:ℝ))
      ((fderiv ℝ f (x,0)).comp (ContinuousLinearMap.inl ℝ E ℝ)) x := by
    simpa only [Function.comp_def,hz] using hc
  have hi := hc0.unique (hasFDerivAt_const (0:ℝ) x)
  have hv := congrArg (fun L : E →L[ℝ] ℝ => L d) hi
  simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.inl_apply,
    zero_apply,wallAlong] using hv

lemma wallAlong_primitive (d : E) {f : E × ℝ → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (p : E × ℝ) :
    wallAlong d (wallPrimitive f) p=wallPrimitive (wallAlong d f) p := by
  have hA := wallPrimitive_smooth hf
  have hd : wallDerivative (wallAlong d (wallPrimitive f))=wallAlong d f := by
    funext q
    rw [wall_mixed_commute d hA]
    congr 1
    exact funext (wallDerivative_primitive hf)
  have hh := wallQuotient_identity (wallAlong_smooth d hA) p.1 p.2
  rw [wallAlong_zero_trace d (hA.differentiable (by simp)) (wallPrimitive_zero f),sub_zero] at hh
  simpa only [wallQuotient,wallPrimitive,hd] using hh

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_FiberTangentialDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

omit [ProperSpace E] in
lemma wallAlong_fixed_normal (d : E) (a : ℝ) {f : E×ℝ → ℝ}
    (hf : Differentiable ℝ f) (p : E×ℝ) :
    wallAlong d (fun q : E×ℝ => f (q.1,a)) p=wallAlong d f (p.1,a) := by
  have hh := (hf (p.1,a)).hasFDerivAt.comp p
    ((hasFDerivAt_fst (𝕜 := ℝ) (p := p)).prodMk (hasFDerivAt_const (𝕜 := ℝ) a p))
  simp only [Function.comp_def] at hh
  rw [wallAlong,hh.fderiv]
  rfl

lemma wallAlong_fiberPrimitive (d : E) (a : ℝ) {f : E×ℝ → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (p : E×ℝ) :
    wallAlong d (fiberPrimitive a f) p=fiberPrimitive a (wallAlong d f) p := by
  have hP := wallPrimitive_smooth hf
  have hQ : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun q : E×ℝ => wallPrimitive f (q.1,a)) :=
    hP.comp (contDiff_fst.prodMk contDiff_const)
  change fderiv ℝ (fun p => wallPrimitive f p-wallPrimitive f (p.1,a)) p (d,0)=_
  rw [fderiv_fun_sub (hP.differentiable (by simp) p) (hQ.differentiable (by simp) p),
    sub_apply]
  change wallAlong d (wallPrimitive f) p-wallAlong d (fun q => wallPrimitive f (q.1,a)) p=_
  rw [wallAlong_fixed_normal d a (hP.differentiable (by simp)),
    wallAlong_primitive d hf,wallAlong_primitive d hf]
  rfl

lemma compactFiberMarginal_fderiv (d : E) {a b : ℝ}
    {f : E×ℝ → ℝ} (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (x : E) :
    fderiv ℝ (compactFiberMarginal a b f) x d=
      compactFiberMarginal a b (wallAlong d f) x := by
  have he : compactFiberMarginal a b f=fun x => fiberPrimitive a f (x,b) := by
    funext x
    exact (fiberPrimitive_eq_integral a hf.continuous (x,b)).symm
  have hh := ((fiberPrimitive_smooth a hf).differentiable (by simp) (x,b)).hasFDerivAt.comp x
    ((hasFDerivAt_id (𝕜 := ℝ) x).prodMk (hasFDerivAt_const (𝕜 := ℝ) b x))
  simp only [Function.comp_def,id_eq] at hh
  rw [he,hh.fderiv]
  change wallAlong d (fiberPrimitive a f) (x,b)=_
  rw [wallAlong_fiberPrimitive d a hf,
    fiberPrimitive_eq_integral a (wallAlong_smooth d hf).continuous]
  rfl

omit [ProperSpace E] in
lemma wallAlong_tsupport (d : E) (f : E×ℝ → ℝ) :
    tsupport (wallAlong d f)⊆tsupport f := tsupport_fderiv_apply_subset ℝ (d,0)

lemma fiberPrimitive_tangential_bound (d : E) {a b : ℝ} (hab : a≤b)
    {f : E×ℝ → ℝ} (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (hv : ∀ p∈tsupport f,p.2∈Ioo a b)
    (hz : ∀ x,(∫ t in a..b,f (x,t))=0)
    {M : ℝ} (hM : 0≤M) (hbound : ∀ p,|wallAlong d f p|≤M) (p : E×ℝ) :
    |wallAlong d (fiberPrimitive a f) p|≤(b-a)*M := by
  rw [wallAlong_fiberPrimitive d a hf]
  apply fiberPrimitive_abs_bound hab (wallAlong_smooth d hf).continuous _ _ hM hbound p
  · intro q hq
    exact hv q (wallAlong_tsupport d f (subset_tsupport _ hq))
  · intro x
    change compactFiberMarginal a b (wallAlong d f) x=0
    rw [←compactFiberMarginal_fderiv d hf]
    have he : compactFiberMarginal a b f=fun _ => (0:ℝ) := funext hz
    rw [he]
    simp

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_FiberDivergenceC1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

omit [ProperSpace E] in
lemma wallAlong_pullback (d : E) {f : E → ℝ} (hf : Differentiable ℝ f) (p : E×ℝ) :
    wallAlong d (fun q : E×ℝ => f q.1) p=fderiv ℝ f p.1 d := by
  have hh := (hf p.1).hasFDerivAt.comp p (hasFDerivAt_fst (𝕜 := ℝ) (p := p))
  simp only [Function.comp_def] at hh
  rw [wallAlong,hh.fderiv]
  rfl

omit [ProperSpace E] in
lemma wallAlong_normal (d : E) {f : ℝ → ℝ} (hf : Differentiable ℝ f) (p : E×ℝ) :
    wallAlong d (fun q : E×ℝ => f q.2) p=0 := by
  have hh := (hf p.2).hasFDerivAt.comp p (hasFDerivAt_snd (𝕜 := ℝ) (p := p))
  simp only [Function.comp_def] at hh
  rw [wallAlong,hh.fderiv]
  simp

omit [ProperSpace E] in
lemma wallAlong_sub (d : E) {f g : E×ℝ → ℝ}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (p : E×ℝ) :
    wallAlong d (fun q => f q-g q) p=wallAlong d f p-wallAlong d g p := by
  simp only [wallAlong,fderiv_fun_sub (hf p) (hg p),sub_apply]

omit [ProperSpace E] in
lemma wallAlong_opNorm_bound (d : E) {f : E×ℝ → ℝ} {M : ℝ}
    (h : ∀ p,‖fderiv ℝ f p‖≤M) (p : E×ℝ) : |wallAlong d f p|≤M*‖d‖ := by
  have hh := (fderiv ℝ f p).le_opNorm (d,0)
  simp only [Prod.norm_def,norm_zero,max_eq_left (norm_nonneg d),Real.norm_eq_abs] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right (h p) (norm_nonneg d))

omit [ProperSpace E] in
lemma fderiv_normal_tangent (f : E×ℝ → ℝ) (p v : E×ℝ) :
    fderiv ℝ f p v=wallAlong v.1 f p+v.2*wallDerivative f p := by
  have he : v=(v.1,0)+v.2 • ((0:E),1) := by ext <;> simp
  calc
    _ = fderiv ℝ f p ((v.1,0)+v.2 • ((0:E),1)) := congrArg (fderiv ℝ f p) he
    _ = _ := by simp only [map_add,map_smul,smul_eq_mul,wallAlong,wallDerivative]

theorem compact_fiber_decomposition_C1 {a b : ℝ} (hab : a<b)
    {f : E×ℝ → ℝ} (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (hs : HasCompactSupport f) (hv : ∀ p∈tsupport f,p.2∈Ioo a b)
    {η : ℝ → ℝ} (hη : ContDiff ℝ (↑(⊤ : ℕ∞)) η) (hsη : HasCompactSupport η)
    (hvη : tsupport η⊆Ioo a b) (hiη : (∫ t in a..b,η t)=1)
    {M K : ℝ} (hM : 0≤M) (hK : 0≤K)
    (hb : ∀ p,|f p|≤M) (hdb : ∀ p,‖fderiv ℝ f p‖≤M) (hηb : ∀ t,|η t|≤K) :
    ∃ F : E×ℝ → ℝ,ContDiff ℝ (↑(⊤ : ℕ∞)) F ∧ HasCompactSupport F ∧
      (∀ p,wallDerivative F p+η p.2*compactFiberMarginal a b f p.1=f p) ∧
      tsupport F⊆(Prod.fst '' tsupport f) ×ˢ Icc a b ∧
      (∀ p,|F p|≤(b-a)*(1+K*(b-a))*M) ∧
      (∀ p,‖fderiv ℝ F p‖≤(b-a+1)*(1+K*(b-a))*M) := by
  obtain ⟨F,hF,hsF,heF,htF,hbF,hdbF,hformula⟩ := compact_fiber_decomposition_bounded hab hf hs
    (fun p hp => hv p (subset_tsupport f hp)) hη hsη hvη hiη hM hK hb hηb
  let R := compactFiberMarginal a b f
  have hR := compactFiberMarginal_smooth hab.le hf
  let g : E×ℝ → ℝ := fun p => f p-η p.2*R p.1
  have hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g := hf.sub ((hη.comp contDiff_snd).mul (hR.comp contDiff_fst))
  have hvG : ∀ p∈tsupport g,p.2∈Ioo a b := by
    intro p hp
    rcases tsupport_sub _ _ hp with hp|hp
    · exact hv p hp
    · exact hvη ((tsupport_comp_subset_preimage η continuous_snd)
        (tsupport_mul_subset_left hp))
  have hzG : ∀ x,(∫ t in a..b,g (x,t))=0 := by
    intro x
    rw [show (fun t => g (x,t))=(fun t => f (x,t)-η t*R x) from rfl,
      intervalIntegral.integral_sub (f := fun t => f (x,t)) (g := fun t => η t*R x)
        ((hf.continuous.comp (continuous_const.prodMk continuous_id)).intervalIntegrable a b)
        ((hη.continuous.mul continuous_const).intervalIntegrable a b)]
    rw [intervalIntegral.integral_mul_const,hiη,one_mul]
    exact sub_self _
  have hdg (d : E) (p : E×ℝ) : wallAlong d g p=
      wallAlong d f p-η p.2*compactFiberMarginal a b (wallAlong d f) p.1 := by
    change wallAlong d (fun p => f p-(η ∘ Prod.snd) p*(compactFiberMarginal a b f ∘ Prod.fst) p) p = _
    rw [wallAlong_sub d (hf.differentiable (by simp))
        (((hη.comp contDiff_snd).mul (hR.comp contDiff_fst)).differentiable (by simp)),
      wallAlong_mul d ((hη.comp contDiff_snd).differentiable (by simp))
        ((hR.comp contDiff_fst).differentiable (by simp))]
    dsimp only [Function.comp_def]
    rw [wallAlong_normal d (hη.differentiable (by simp)),
      wallAlong_pullback d (hR.differentiable (by simp)),compactFiberMarginal_fderiv d hf]
    ring
  have hbg (d : E) (p : E×ℝ) : |wallAlong d g p|≤(1+K*(b-a))*M*‖d‖ := by
    rw [hdg]
    calc
      _ ≤ |wallAlong d f p|+|η p.2| * |compactFiberMarginal a b (wallAlong d f) p.1| := by
        simpa only [abs_mul] using abs_sub (wallAlong d f p) (η p.2*compactFiberMarginal a b (wallAlong d f) p.1)
      _ ≤ M*‖d‖+K*((b-a)*(M*‖d‖)) := add_le_add (wallAlong_opNorm_bound d hdb p)
        (mul_le_mul (hηb p.2) (compactFiberMarginal_abs_bound hab.le (wallAlong_opNorm_bound d hdb) p.1)
          (abs_nonneg _) hK)
      _ = _ := by ring
  have htang (d : E) (p : E×ℝ) : |wallAlong d F p|≤(b-a)*(1+K*(b-a))*M*‖d‖ := by
    rw [hformula]
    simpa only [mul_assoc] using fiberPrimitive_tangential_bound d hab.le hg hvG hzG
      (by positivity : 0≤(1+K*(b-a))*M*‖d‖) (hbg d) p
  refine ⟨F,hF,hsF,heF,htF,hbF,?_⟩
  intro p
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  rw [Real.norm_eq_abs,fderiv_normal_tangent]
  calc
    _ ≤ |wallAlong v.1 F p|+|v.2| * |wallDerivative F p| := by
      simpa only [abs_mul] using abs_add_le (wallAlong v.1 F p) (v.2*wallDerivative F p)
    _ ≤ (b-a)*(1+K*(b-a))*M*‖v.1‖+|v.2| *((1+K*(b-a))*M) :=
      add_le_add (htang v.1 p) (mul_le_mul_of_nonneg_left (hdbF p) (abs_nonneg _))
    _ ≤ (b-a)*(1+K*(b-a))*M*‖v‖+‖v‖*((1+K*(b-a))*M) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (norm_fst_le v) (by positivity)
      · exact mul_le_mul_of_nonneg_right (by simpa only [Real.norm_eq_abs] using norm_snd_le v) (by positivity)
    _ = _ := by ring

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_UniformC1Bounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

variable {E P : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

lemma exists_uniformC1Bound {f : E → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hs : HasCompactSupport f) :
    ∃ M : ℝ,0<M ∧ UniformC1Bound f M := by
  obtain ⟨A,hA⟩ := hs.exists_bound_of_continuous hf.continuous
  obtain ⟨B,hB⟩ := (hs.fderiv ℝ).exists_bound_of_continuous (hf.continuous_fderiv (by simp))
  refine ⟨|A|+|B|+1,by positivity,?_⟩
  intro x
  constructor
  · have := hA x
    rw [Real.norm_eq_abs] at this
    exact this.trans (by linarith [le_abs_self A,abs_nonneg B])
  · exact (hB x).trans (by linarith [le_abs_self B,abs_nonneg A])

lemma compactFiberMarginal_C1Bound [ProperSpace E] {a b : ℝ} (hab : a≤b)
    {f : E×ℝ → ℝ} (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    {M : ℝ} (hM : 0≤M) (hb : UniformC1Bound f M) :
    UniformC1Bound (compactFiberMarginal a b f) ((b-a)*M) := by
  intro x
  refine ⟨compactFiberMarginal_abs_bound hab (fun p => (hb p).1) x,?_⟩
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro d
  rw [Real.norm_eq_abs,compactFiberMarginal_fderiv d hf]
  simpa only [mul_assoc] using compactFiberMarginal_abs_bound hab
    (wallAlong_opNorm_bound d (fun p => (hb p).2)) x

lemma compact_scalar_primitive_bounded {a b : ℝ} (hab : a<b)
    {r : ℝ → ℝ} (hr : ContDiff ℝ (↑(⊤ : ℕ∞)) r)
    (hv : ∀ t,r t≠0 → t∈Ioo a b) (hz : (∫ t,r t)=0)
    {M : ℝ} (hM : 0≤M) (hb : ∀ t,|r t|≤M) :
    ∃ P : ℝ → ℝ,ContDiff ℝ (↑(⊤ : ℕ∞)) P ∧ HasCompactSupport P ∧
      (∀ t,deriv P t=r t) ∧ tsupport P⊆Icc a b ∧ UniformC1Bound P ((b-a+1)*M) := by
  let f : ℝ×ℝ → ℝ := fun p => r p.2
  have hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f := hr.comp contDiff_snd
  let P : ℝ → ℝ := fun t => fiberPrimitive a f (0,t)
  have hP : ContDiff ℝ (↑(⊤ : ℕ∞)) P :=
    (fiberPrimitive_smooth a hf).comp (contDiff_const.prodMk contDiff_id)
  have hvf : ∀ p,f p≠0 → p.2∈Ioo a b := fun p hp => hv p.2 hp
  have hzf : ∀ x,(∫ t in a..b,f (x,t))=0 := by
    intro x
    exact (interval_integral_eq_integral_of_support hab.le hv).trans hz
  have hs : Function.support P⊆Icc a b := by
    intro t ht
    refine ⟨?_,?_⟩
    · by_contra hn
      exact ht (fiberPrimitive_below hf.continuous hvf (0,t) (le_of_not_ge hn))
    · by_contra hn
      exact ht (fiberPrimitive_above hf.continuous hvf hzf (0,t) (le_of_not_ge hn))
  have hdP (t : ℝ) : deriv P t=r t := by
    have hd := (((fiberPrimitive_smooth a hf).differentiable (by simp)) (0,t)).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_const t (0:ℝ)).prodMk (hasDerivAt_id t))
    exact hd.deriv.trans (fiberPrimitive_derivative a hf (0,t))
  refine ⟨P,hP,HasCompactSupport.of_support_subset_isCompact isCompact_Icc hs,hdP,
    closure_minimal hs isClosed_Icc,?_⟩
  intro t
  constructor
  · exact (fiberPrimitive_abs_bound hab.le hf.continuous hvf hzf hM (fun p => hb p.2) (0,t)).trans
      (by nlinarith [sub_nonneg.mpr hab.le])
  · rw [←norm_deriv_eq_norm_fderiv,hdP,Real.norm_eq_abs]
    exact (hb t).trans (by nlinarith [sub_nonneg.mpr hab.le])

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_CylinderFourier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal

attribute [local instance] OAI.ScalarConductivity.instMeasureSpaceUnitAddCircle_solutions_5
attribute [local instance] OAI.ScalarConductivity.instIsProbabilityMeasureUnitAddCircleVolume_solutions_5
def cylinderMode (μ : Measure ℝ) [SFinite μ] (h : TorusModes) :
    Lp ℂ 2 μ →ₗᵢ[ℂ] CylinderL2 μ where
  toFun f := cylinderTensor f (mFourierLp 2 h)
  map_add' f g := cylinderTensor_add f g _
  map_smul' c f := cylinderTensor_smul c f _
  norm_map' f := by
    change ‖cylinderTensor f (mFourierLp 2 h)‖=‖f‖
    have he := cylinderTensor_norm_sq f (mFourierLp 2 h)
    rw [(orthonormal_mFourier (d:=Fin 2)).norm_eq_one h,one_pow,mul_one] at he
    nlinarith only [he,norm_nonneg (cylinderTensor f (mFourierLp 2 h)),norm_nonneg f]

lemma cylinderMode_orthogonal (μ : Measure ℝ) [SFinite μ] :
    OrthogonalFamily ℂ (fun _ : TorusModes => Lp ℂ 2 μ) (cylinderMode μ) := by
  intro h k hk f g
  change inner ℂ (cylinderTensor f (mFourierLp 2 h))
    (cylinderTensor g (mFourierLp 2 k))=0
  rw [cylinderTensor_inner,(orthonormal_mFourier (d:=Fin 2)).inner_eq_zero hk,mul_zero]

def cylinderFourier (μ : Measure ℝ) [SFinite μ] :
    lp (fun _ : TorusModes => Lp ℂ 2 μ) 2 →ₗᵢ[ℂ] CylinderL2 μ :=
  (cylinderMode_orthogonal μ).linearIsometry

lemma cylinderFourier_hasSum (μ : Measure ℝ) [SFinite μ]
    (f : lp (fun _ : TorusModes => Lp ℂ 2 μ) 2) :
    HasSum (fun h => cylinderMode μ h (f h)) (cylinderFourier μ f) :=
  (cylinderMode_orthogonal μ).hasSum_linearIsometry f

lemma cylinderFourier_norm_sq (μ : Measure ℝ) [SFinite μ]
    (f : lp (fun _ : TorusModes => Lp ℂ 2 μ) 2) :
    ‖cylinderFourier μ f‖^2=∑' h,‖f h‖^2 := by
  rw [(cylinderFourier μ).norm_map]
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
    lp.norm_rpow_eq_tsum (by norm_num : 0<(2:ℝ≥0∞).toReal) f

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_EndPoissonJets
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.spectralTraceGraph_realInner
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

lemma torusFrequency_sq_le_rate (s : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (h : TorusModes) (j : Fin 2) : (h j:ℝ)^2 ≤ 4*(torusRate s h)^2 := by
  have hh := torusRate_lower hs h
  have hj : |(h j:ℝ)| ≤ torusSize h := by
    fin_cases j <;> simp only [torusSize,Fin.zero_eta,Fin.mk_one]
    · exact le_add_of_nonneg_right (abs_nonneg _)
    · exact le_add_of_nonneg_left (abs_nonneg _)
  have hnon : 0 ≤ torusRate s h := Real.sqrt_nonneg _
  have habs : |(h j:ℝ)| ≤ 2*torusRate s h := by linarith
  have he := pow_le_pow_left₀ (abs_nonneg (h j:ℝ)) habs 2
  simpa only [sq_abs,mul_pow,show (2:ℝ)^2=4 by norm_num] using he

lemma finiteDecayLp_angular_bound (s : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (R : ℝ) (h : TorusModes) (j : Fin 2) (a : ℂ) :
    ‖finiteDecayLp (torusRate s h) R (Complex.I*(h j:ℂ)*a)‖^2 ≤
      2*torusRate s h*‖a‖^2 := by
  have hr := finiteDecayLp_rate_norm_sq (torusRate s h) R (Real.sqrt_nonneg _) a
  rw [finiteDecayLp_real_norm_sq] at hr
  have hh := mul_le_mul_of_nonneg_right (torusFrequency_sq_le_rate s hs h j)
    (sq_nonneg ‖finiteDecayLp (torusRate s h) R a‖)
  have he : (h j:ℂ)=((h j:ℝ):ℂ) := by norm_cast
  rw [he,finiteDecayLp_imag_norm_sq]
  nlinarith only [hr,hh]

end

open Set MeasureTheory Filter Topology
open scoped ENNReal

lemma spectralGraph_norm_sq {ι : Type*} (w : ι → ℝ) (f : spectralTraceGraph w) :
    ‖f‖^2=‖f.val 0‖^2+‖f.val 1‖^2 := by
  change ‖f.val‖^2=_
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [Fin.sum_univ_two]

lemma spectralGraph_weight_norm_sq {ι : Type*} (w : ι → ℝ) (hw : ∀ i,0 ≤ w i)
    (f : spectralTraceGraph w) :
    ‖f.val 1‖^2=∑' i,w i*‖f.val 0 i‖^2 := by
  have hn := lp.norm_rpow_eq_tsum (by norm_num : 0<(2:ℝ≥0∞).toReal) (f.val 1)
  have he (i : ι) : ‖f.val 1 i‖^2=w i*‖f.val 0 i‖^2 := by
    rw [f.property i]
    exact sqrt_weight_norm_sq hw (f.val 0) i
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two,he] using hn

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_TorusFlatMode
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Real Set Filter Topology

lemma flatMode_derivative_summable {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ, (1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (n : ℕ) {δ : ℝ} (hδ : 0<δ) :
    Summable (fun h => (torusRate s h+torusSize h)^n*exp (-δ*torusRate s h)) := by
  refine ((torusRate_poly_exp_summable hs n hδ).mul_left ((3:ℝ)^n)).of_nonneg_of_le
    (fun h => by dsimp [torusRate,torusSize]; positivity) ?_
  intro h
  have hl := torusRate_lower hs h
  have hlam : 0≤torusRate s h := sqrt_nonneg _
  calc
    _ ≤ (3*torusRate s h)^n*exp (-δ*torusRate s h) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (add_nonneg hlam (torusSize_nonneg h)) (by linarith) _) (exp_nonneg _)
    _ = _ := by rw [mul_pow,mul_assoc]

def flatPhaseMode (s : Fin 3 → ℝ) (h : Fin 2 → ℤ) (phase : ℝ) (x : Fin 3 → ℝ) : ℝ :=
  exp (-torusRate s h*x 0) * cos (torusAngular h x+phase)

lemma flatPhaseMode_smooth (s : Fin 3 → ℝ) (h : Fin 2 → ℤ) (phase : ℝ) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (flatPhaseMode s h phase) := by
  unfold flatPhaseMode
  fun_prop

lemma flatPhaseMode_iterated_bound (s : Fin 3 → ℝ) (h : Fin 2 → ℤ) (phase : ℝ)
    (n : ℕ) (x : Fin 3 → ℝ) :
    ‖iteratedFDeriv ℝ n (flatPhaseMode s h phase) x‖≤
      (torusRate s h+torusSize h)^n*exp (-torusRate s h*x 0) := by
  have he : ContDiff ℝ (↑(⊤:ℕ∞)) (fun y : Fin 3 → ℝ => exp (-torusRate s h*y 0)) := by fun_prop
  have hc : ContDiff ℝ (↑(⊤:ℕ∞)) (fun y => cos (torusAngular h y+phase)) := by fun_prop
  apply (norm_iteratedFDeriv_mul_le he hc x (by exact_mod_cast (le_top : (n:ℕ∞)≤⊤))).trans
  calc
    _ ≤ ∑ i∈Finset.range (n+1), (n.choose i:ℝ)*
        ((torusRate s h)^i*exp (-torusRate s h*x 0))*(torusSize h)^(n-i) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul (mul_le_mul_of_nonneg_left
        (axial_exp_iterated_bound _ (sqrt_nonneg _) i x) (Nat.cast_nonneg _))
        (angular_phase_iterated_bound h phase (n-i) x) (norm_nonneg _) (by dsimp [torusRate]; positivity)
    _ = _ := by
      rw [add_pow,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      ring

lemma weighted_phase_iterated_bound {s : Fin 3 → ℝ} {h : Fin 2 → ℤ}
    (phase a : ℝ) (n : ℕ) (x : Fin 3 → ℝ) :
    ‖iteratedFDeriv ℝ n (fun y => a*flatPhaseMode s h phase y) x‖≤
      |a| *((torusRate s h+torusSize h)^n*exp (-torusRate s h*x 0)) := by
  have hh : ContDiffAt ℝ (↑n) (flatPhaseMode s h phase) x :=
    ((contDiff_infty.mp (flatPhaseMode_smooth s h phase)) n).contDiffAt
  change ‖iteratedFDeriv ℝ n (a • flatPhaseMode s h phase) x‖≤_
  rw [iteratedFDeriv_const_smul_apply hh,norm_smul,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (flatPhaseMode_iterated_bound s h phase n x) (abs_nonneg _)

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

def sourcePhysicalCollarMeasure (l r : ℝ) : Measure (Fin 3 → ℝ) :=
  ∑ i : Fin 4,∑ j : Fin 4,volume.restrict (sourceCollarPiece i j '' sourceExtendedBox l r)

def sourceAngularCollarMeasure (l r : ℝ) : Measure (Fin 3 → ℝ) :=
  Measure.map (Function.uncurry sourceAngularCollar)
    ((volume.restrict (Ioc l r)).prod (volume : Measure (UnitAddTorus (Fin 2))))

instance sourcePhysicalCollarMeasure_finite (l r : ℝ) :
    IsFiniteMeasure (sourcePhysicalCollarMeasure l r) := by
  have (i j : Fin 4) : IsFiniteMeasure
      (volume.restrict (sourceCollarPiece i j '' sourceExtendedBox l r)) :=
    ⟨by simpa only [Measure.restrict_apply_univ,sourceExtendedBox] using (isCompact_Icc.image (sourceCollarPiece_contDiff i j).continuous).measure_lt_top⟩
  unfold sourcePhysicalCollarMeasure
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

instance sourceAngularCollarMeasure_finite (l r : ℝ) :
    IsFiniteMeasure (sourceAngularCollarMeasure l r) := by
  unfold sourceAngularCollarMeasure
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

lemma integral_sourcePhysicalCollarMeasure {f : (Fin 3 → ℝ) → ℝ}
    (hf : Continuous f) (l r : ℝ) :
    (∫ x,f x ∂sourcePhysicalCollarMeasure l r)=
      ∑ i : Fin 4,∑ j : Fin 4,∫ x in sourceCollarPiece i j '' sourceExtendedBox l r,f x := by
  have hi (i j : Fin 4) : IntegrableOn f (sourceCollarPiece i j '' sourceExtendedBox l r) :=
    hf.continuousOn.integrableOn_compact (isCompact_Icc.image (sourceCollarPiece_contDiff i j).continuous)
  unfold sourcePhysicalCollarMeasure
  rw [integral_finsetSum_measure (fun i _ => integrable_finsetSum_measure.mpr (fun j _ => hi i j))]
  apply Finset.sum_congr rfl
  intro i _
  exact integral_finsetSum_measure (fun j _ => hi i j)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_CollarAngularInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped NNReal ENNReal

def sourceComplexDirections (y : Fin 3 → ℝ) : Fin 2 → ℂ :=
  ![((y 0/sourceLength:ℝ):ℂ)+Complex.I*(y 1:ℂ),
    ((sourceRadial y-sourceRadialCenter:ℝ):ℂ)+Complex.I*(y 2:ℂ)]

def sourcePhysicalAngles (y : Fin 3 → ℝ) : UnitAddTorus (Fin 2) :=
  fun i => complexUnitAngle (sourceComplexDirections y i)

lemma continuous_sourceComplexDirections : Continuous sourceComplexDirections := by
  apply continuous_pi
  intro i
  fin_cases i <;> unfold sourceComplexDirections sourceRadial <;> fun_prop

lemma measurable_sourcePhysicalAngles : Measurable sourcePhysicalAngles := by
  apply Measurable.of_eval
  intro i
  exact measurable_complexUnitAngle.comp
    (((continuous_apply i).comp continuous_sourceComplexDirections).measurable)

lemma sourceComplexDirections_angular {t : ℝ} (ht : t∈Icc (-(1:ℝ)/100) (1/100))
    (θ : UnitAddTorus (Fin 2)) :
    sourceComplexDirections (sourceAngularCollar t θ)=
      ![(((sourceRadialCenter+(1-t)*rectangularRay sourceRadialWidth (θ 1) 0)/
          rayDenominator 1 (θ 0):ℝ):ℂ)*fourier 1 (θ 0),
        (((1-t)/rayDenominator sourceRadialWidth (θ 1):ℝ):ℂ)*fourier 1 (θ 1)] := by
  ext i
  fin_cases i
  · apply Complex.ext <;>
      simp [sourceComplexDirections,sourceAngularCollar,sourceAngularPolynomial,
        sourceRayCoordinates,rectangularRay,rayDirection,Complex.mul_re,Complex.mul_im] <;>
      norm_num [sourceLength] <;> ring
  · change ((sourceRadial (sourceAngularCollar t θ)-sourceRadialCenter:ℝ):ℂ)+
      Complex.I*((sourceAngularCollar t θ) 2:ℂ)=_
    rw [sourceAngular_radial ht,add_sub_cancel_left]
    apply Complex.ext <;>
      simp [sourceAngularCollar,sourceAngularPolynomial,sourceRayCoordinates,
        rectangularRay,rayDirection,Complex.mul_re,Complex.mul_im] <;> ring

lemma sourcePhysicalAngles_angular {t : ℝ} (ht : t∈Icc (-(1:ℝ)/100) (1/100))
    (θ : UnitAddTorus (Fin 2)) : sourcePhysicalAngles (sourceAngularCollar t θ)=θ := by
  have h0 : 0 < rayDenominator 1 (θ 0) :=
    lt_of_lt_of_le (by norm_num) (rayDenominator_lower (by norm_num) (by norm_num) _)
  have h1 : 0 < rayDenominator sourceRadialWidth (θ 1) :=
    lt_of_lt_of_le (by norm_num) (rayDenominator_lower
      (by norm_num [sourceRadialWidth,sourceHole]) (by norm_num [sourceRadialWidth,sourceHole]) _)
  ext i
  change complexUnitAngle (sourceComplexDirections (sourceAngularCollar t θ) i)=θ i
  rw [sourceComplexDirections_angular ht]
  fin_cases i
  · exact (complexUnitAngle_pos_mul _ (div_pos (sourceAngular_radius_pos ht θ) h0)).trans
      (complexUnitAngle_fourier _)
  · exact (complexUnitAngle_pos_mul _ (div_pos (by linarith [ht.2] : 0<1-t) h1)).trans
      (complexUnitAngle_fourier _)

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

def sourcePhysicalCoordinates (y : Fin 3 → ℝ) : ℝ×UnitAddTorus (Fin 2) :=
  (sourceCollarTime y,sourcePhysicalAngles y)

lemma measurable_sourcePhysicalCoordinates : Measurable sourcePhysicalCoordinates := by
  have ht : Continuous sourceCollarTime := by
    unfold sourceCollarTime sourceCrossCoordinates sourceRadial
    fun_prop
  exact ht.measurable.prodMk measurable_sourcePhysicalAngles

lemma sourcePhysicalCoordinates_angular {t : ℝ} (ht : t∈Icc (-(1:ℝ)/100) (1/100))
    (θ : UnitAddTorus (Fin 2)) :
    sourcePhysicalCoordinates (sourceAngularCollar t θ)=(t,θ) := by
  exact Prod.ext (sourceAngular_time ht θ) (sourcePhysicalAngles_angular ht θ)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_TorusFourierSmooth
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology

def flatFourier (s : Fin 3 → ℝ) (a phase : (Fin 2 → ℤ) → ℝ) (x : Fin 3 → ℝ) : ℝ :=
  ∑' h, a h*flatPhaseMode s h (phase h) x

lemma weighted_phase_halfspace_bound {s : Fin 3 → ℝ} {a phase : (Fin 2 → ℤ) → ℝ}
    {B δ : ℝ} (ha : ∀ h, |a h|≤B) (n : ℕ) (h : Fin 2 → ℤ)
    {x : Fin 3 → ℝ} (hx : δ≤x 0) :
    ‖iteratedFDeriv ℝ n (fun y => a h*flatPhaseMode s h (phase h) y) x‖≤
      B*((torusRate s h+torusSize h)^n*exp (-δ*torusRate s h)) := by
  apply (weighted_phase_iterated_bound (phase h) (a h) n x).trans
  have hrate : 0≤torusRate s h := sqrt_nonneg _
  have hexp : exp (-torusRate s h*x 0)≤exp (-δ*torusRate s h) := by
    apply exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hx hrate]
  have hsize := torusSize_nonneg h
  exact mul_le_mul (ha h) (mul_le_mul_of_nonneg_left hexp (by positivity))
    (by positivity) ((abs_nonneg _).trans (ha h))

lemma flatFourier_smooth_halfspace {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ, (1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {a phase : (Fin 2 → ℤ) → ℝ} {B δ : ℝ} (ha : ∀ h, |a h|≤B) (hδ : 0<δ) :
    ContDiffOn ℝ (↑(⊤:ℕ∞)) (flatFourier s a phase) {x | δ<x 0} := by
  apply local_smooth_tsum (axial_halfspace_open δ) (axial_halfspace_connected δ)
    (fun h => contDiff_const.mul (flatPhaseMode_smooth s h (phase h)))
    (fun n h => B*((torusRate s h+torusSize h)^n*exp (-δ*torusRate s h)))
  · intro n
    exact (flatMode_derivative_summable hs n hδ).mul_left B
  · intro n h x hx
    exact weighted_phase_halfspace_bound ha n h hx.le

lemma flatFourier_smooth {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ, (1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {a phase : (Fin 2 → ℤ) → ℝ} {B : ℝ} (ha : ∀ h, |a h|≤B) :
    ContDiffOn ℝ (↑(⊤:ℕ∞)) (flatFourier s a phase) {x | 0<x 0} := by
  apply (axial_halfspace_open 0).contDiffOn_iff.mpr
  intro x hx
  change 0<x 0 at hx
  exact (flatFourier_smooth_halfspace hs ha (show 0<x 0/2 by linarith)).contDiffAt
    ((axial_halfspace_open (x 0/2)).mem_nhds (show x 0/2<x 0 by linarith))

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_TorusPoissonContinuous
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace
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
lemma poisson_series_norm_summable {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ, (1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {t : ℝ} (ht : 0<t) (f : TorusL2) :
    Summable (fun h => ‖((Real.exp (-torusRate s h*t):ℂ)*mFourierCoeff f h) • mFourier h‖) := by
  apply ((torusRate_exp_summable hs ht).mul_left ‖f‖).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun h => ?_)
  rw [norm_smul,mFourier_norm,mul_one,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  simpa only [mul_comm,neg_mul,mul_neg] using
    mul_le_mul_of_nonneg_left (torusFourierCoeff_bound f h) (Real.exp_nonneg (-torusRate s h*t))

end

open MeasureTheory Filter Topology UnitAddTorus Real Set
open scoped ENNReal

lemma mFourier_torusAngles (h : Fin 2 → ℤ) (x : Fin 3 → ℝ) :
    mFourier h (torusAngles x)=Complex.exp ((torusAngular h x:ℂ)*Complex.I) := by
  simp only [mFourier,ContinuousMap.coe_mk,Fin.prod_univ_two,torusAngles,
    Matrix.cons_val_zero,Matrix.cons_val_one,fourier_coe_apply,
    Complex.ofReal_one,div_one,←Complex.exp_add,torusAngular,add_apply,
    smul_apply,ContinuousLinearMap.proj_apply,smul_eq_mul]
  congr 1
  push_cast
  field_simp [Real.pi_ne_zero]

lemma flatFourier_summable {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ, (1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {a phase : (Fin 2 → ℤ) → ℝ} {B : ℝ} (ha : ∀ h,|a h|≤B)
    {x : Fin 3 → ℝ} (hx : 0<x 0) :
    Summable (fun h => a h*flatPhaseMode s h (phase h) x) := by
  apply Summable.of_norm
  apply ((torusRate_exp_summable hs hx).mul_left B).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro h
  rw [Real.norm_eq_abs,abs_mul,flatPhaseMode,abs_mul,abs_of_pos (exp_pos _)]
  calc
    _ ≤ B*(exp (-torusRate s h*x 0)*1) := mul_le_mul (ha h)
      (mul_le_mul_of_nonneg_left (abs_cos_le_one _) (exp_nonneg _)) (by positivity)
      ((abs_nonneg _).trans (ha h))
    _ = _ := by rw [mul_one]; congr 2; ring

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_PoissonTraceRate
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.spectralTraceGraph_realInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity

section
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped NNReal ENNReal

lemma torusPoissonFlow_trace_rate (s : Fin 3 → ℝ) {t : ℝ} (ht : 0≤t)
    (f : TorusL2) (g : SpectralL2 (Fin 2 → ℤ))
    (hg : ∀ h,g h=(torusRate s h:ℂ)*mFourierCoeff f h) :
    ‖torusPoissonFlow s t f-f‖≤t*‖g‖ := by
  let F := (mFourierBasis (d:=Fin 2)).repr
  have hb : ‖F (torusPoissonFlow s t f-f)‖≤‖t • g‖ := by
    apply lp.norm_mono (p:=2) (by norm_num)
    intro h
    change ‖mFourierBasis.repr (torusPoissonFlow s t f-f) h‖≤‖(t • g) h‖
    rw [map_sub,lp.coeFn_sub,Pi.sub_apply,mFourierBasis_repr,mFourierBasis_repr,
      torusPoissonFlow_coeff,abs_of_nonneg ht,←sub_one_mul]
    change ‖((Real.exp (-torusRate s h*t):ℂ)-1)*mFourierCoeff f h‖≤‖t • g h‖
    rw [norm_mul,norm_smul,Real.norm_eq_abs,abs_of_nonneg ht,hg,norm_mul,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (show 0≤torusRate s h from Real.sqrt_nonneg _)]
    exact (mul_le_mul_of_nonneg_right
      (poissonMultiplier_sub_one_bound (Real.sqrt_nonneg _) ht) (norm_nonneg _)).trans_eq (by dsimp [torusRate]; ring)
  simpa only [F,LinearIsometryEquiv.norm_map,norm_smul,Real.norm_eq_abs,abs_of_nonneg ht] using hb

lemma torusRate_sq_polynomial_bound (s : Fin 3 → ℝ) (h : Fin 2 → ℤ) :
    (torusRate s h)^2 ≤ (|s 0|+|s 1|+|s 2|)*((h 0:ℝ)^2+(h 1:ℝ)^2) := by
  let B := (h 0:ℝ)^2+(h 1:ℝ)^2
  have hB : 0≤B := by dsimp [B]; positivity
  have hab : 2*|(h 0:ℝ)| * |(h 1:ℝ)|≤B := by
    dsimp [B]
    nlinarith [sq_nonneg (|(h 0:ℝ)|-|(h 1:ℝ)|),sq_abs (h 0:ℝ),sq_abs (h 1:ℝ)]
  have hcross : 2*s 1*(h 0:ℝ)*(h 1:ℝ)≤|s 1| * B := by
    calc
      _ ≤ |2*s 1*(h 0:ℝ)*(h 1:ℝ)| := le_abs_self _
      _ = |s 1| * (2*|(h 0:ℝ)| * |(h 1:ℝ)|) := by
        rw [abs_mul,abs_mul,abs_mul]; norm_num; ring
      _ ≤ |s 1| * B := mul_le_mul_of_nonneg_left hab (abs_nonneg _)
  have hx := mul_le_mul_of_nonneg_right (le_abs_self (s 0)) (sq_nonneg (h 0:ℝ))
  have hy := mul_le_mul_of_nonneg_right (le_abs_self (s 2)) (sq_nonneg (h 1:ℝ))
  have hx' : |s 0| * (h 0:ℝ)^2≤|s 0| * B := mul_le_mul_of_nonneg_left
    (by dsimp [B]; nlinarith [sq_nonneg (h 1:ℝ)]) (abs_nonneg _)
  have hy' : |s 2| * (h 1:ℝ)^2≤|s 2| * B := mul_le_mul_of_nonneg_left
    (by dsimp [B]; nlinarith [sq_nonneg (h 0:ℝ)]) (abs_nonneg _)
  by_cases hq : 0≤torusQuadratic s h
  · rw [torusRate,Real.sq_sqrt hq]
    dsimp [torusQuadratic,B] at *
    nlinarith
  · rw [torusRate,Real.sqrt_eq_zero_of_nonpos (le_of_not_ge hq),zero_pow (by decide)]
    positivity

lemma sourceAngularTrace_H1_summable (t : ℝ) {f : (Fin 3 → ℝ) → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) :
    Summable (fun h : Fin 2 → ℤ => (1+(h 0:ℝ)^2+(h 1:ℝ)^2)*
      ‖mFourierCoeff (fun x => (f (sourceAngularCollar t x):ℂ)) h‖^2) := by
  let G : (Fin 4 → ℝ) → ℂ := fun z => (f (sourceAngularPolynomial t z):ℂ)
  have hG : ContDiff ℝ (↑(⊤ : ℕ∞)) G :=
    Complex.ofRealCLM.contDiff.comp (hf.comp (contDiff_sourceAngularPolynomial t))
  obtain ⟨K,hK⟩ := hG.contDiffOn.exists_lipschitzOnWith (by simp)
    (convex_Icc _ _) isCompact_Icc
  let F : C(UnitAddTorus (Fin 2),ℂ) :=
    ⟨fun x => G (sourceRayCoordinates x),hG.continuous.comp continuous_sourceRayCoordinates⟩
  have hdiff (j : Fin 2) (u : ℝ) (x : UnitAddTorus (Fin 2)) :
      ‖F (x+torusCoordinateShift j u)-F x‖≤((K:ℝ)*sourceRayConstant)*|u| := by
    have hh := hK.dist_le_mul _ (sourceRayCoordinates_mem (x+torusCoordinateShift j u))
      _ (sourceRayCoordinates_mem x)
    rw [dist_eq_norm,dist_eq_norm] at hh
    apply hh.trans
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
      (sourceRayCoordinates_difference j u x) K.coe_nonneg
  exact torus_coordinate_H1_summable F (fun _ => (K:ℝ)*sourceRayConstant)
    (fun _ => mul_nonneg K.coe_nonneg sourceRayConstant_nonneg) hdiff

lemma sourceAngularTrace_rate_sq_summable (s : Fin 3 → ℝ) (t : ℝ)
    {f : (Fin 3 → ℝ) → ℝ} (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) :
    Summable (fun h : Fin 2 → ℤ => (torusRate s h)^2*
      ‖mFourierCoeff (fun x => (f (sourceAngularCollar t x):ℂ)) h‖^2) := by
  refine ((sourceAngularTrace_H1_summable t hf).mul_left
    (|s 0|+|s 1|+|s 2|)).of_nonneg_of_le (fun h => by positivity) (fun h => ?_)
  rw [←mul_assoc]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact (torusRate_sq_polynomial_bound s h).trans
    (mul_le_mul_of_nonneg_left (by linarith) (by positivity))

end

open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_EndPoissonDifferential
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.spectralTraceGraph_realInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus

def endFrequency (s : Fin 3 → ℝ) (h : TorusModes) : (Fin 3 → ℝ) →L[ℝ] ℂ :=
  (-(torusRate s h:ℂ)) • Complex.ofRealCLM.comp (ContinuousLinearMap.proj 0) +
  (Complex.I*(h 0:ℂ)) • Complex.ofRealCLM.comp (ContinuousLinearMap.proj 1) +
  (Complex.I*(h 1:ℂ)) • Complex.ofRealCLM.comp (ContinuousLinearMap.proj 2)

lemma endFrequency_apply (s : Fin 3 → ℝ) (h : TorusModes) (x : Fin 3 → ℝ) :
    endFrequency s h x= (-(torusRate s h*x 0):ℝ)+
      (torusAngular h x:ℂ)*Complex.I := by
  simp [endFrequency,torusAngular]
  ring

lemma endFrequency_norm_le (s : Fin 3 → ℝ) (h : TorusModes) :
    ‖endFrequency s h‖≤torusRate s h+torusSize h := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by
    have hm : 0≤torusRate s h := Real.sqrt_nonneg _
    linarith [torusSize_nonneg h])
  intro v
  have hv (j : Fin 3) : ‖(v j:ℂ)‖≤‖v‖ := by simpa using norm_le_pi_norm v j
  have hm : 0≤torusRate s h := Real.sqrt_nonneg _
  change ‖-(torusRate s h:ℂ)*(v 0:ℂ)+Complex.I*(h 0:ℂ)*(v 1:ℂ)+
      Complex.I*(h 1:ℂ)*(v 2:ℂ)‖≤_
  calc
    _ ≤ ‖-(torusRate s h:ℂ)*(v 0:ℂ)‖+‖Complex.I*(h 0:ℂ)*(v 1:ℂ)‖+
        ‖Complex.I*(h 1:ℂ)*(v 2:ℂ)‖ := (norm_add_le _ _).trans
      (add_le_add (norm_add_le _ _) (le_refl _))
    _ = torusRate s h*‖(v 0:ℂ)‖+|(h 0:ℝ)| *‖(v 1:ℂ)‖+
        |(h 1:ℝ)| *‖(v 2:ℂ)‖ := by simp [abs_of_nonneg hm]
    _ ≤ torusRate s h*‖v‖+|(h 0:ℝ)| *‖v‖+|(h 1:ℝ)| *‖v‖ := by gcongr <;> exact hv _
    _ = _ := by dsimp [torusSize]; ring

def endFlatMode (s : Fin 3 → ℝ) (h : TorusModes) (a : ℂ) (x : Fin 3 → ℝ) : ℂ :=
  a*Complex.exp (endFrequency s h x)

lemma endFlatMode_norm (s : Fin 3 → ℝ) (h : TorusModes) (a : ℂ) (x : Fin 3 → ℝ) :
    ‖endFlatMode s h a x‖=‖a‖*Real.exp (-torusRate s h*x 0) := by
  rw [endFlatMode,norm_mul,Complex.norm_exp,endFrequency_apply]
  simp

lemma endFlatMode_hasFDeriv (s : Fin 3 → ℝ) (h : TorusModes) (a : ℂ) (x : Fin 3 → ℝ) :
    HasFDerivAt (endFlatMode s h a) (endFlatMode s h a x • endFrequency s h) x := by
  convert! ((endFrequency s h).hasFDerivAt (x:=x)).cexp.const_mul a using 1
  all_goals try with_reducible_and_instances rfl
  simp only [endFlatMode,mul_smul]

lemma endFlatMode_derivative_bound (s : Fin 3 → ℝ) (h : TorusModes)
    {a : ℂ} {B δ : ℝ} (ha : ‖a‖≤B) {x : Fin 3 → ℝ} (hx : δ≤x 0) :
    ‖endFlatMode s h a x • endFrequency s h‖≤
      B*((torusRate s h+torusSize h)*Real.exp (-δ*torusRate s h)) := by
  have hm : 0≤torusRate s h := Real.sqrt_nonneg _
  have hr : 0≤torusRate s h+torusSize h := add_nonneg hm (torusSize_nonneg h)
  have he : Real.exp (-torusRate s h*x 0)≤Real.exp (-δ*torusRate s h) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hx hm]
  rw [norm_smul,endFlatMode_norm]
  calc
    _ ≤ (B*Real.exp (-δ*torusRate s h))*(torusRate s h+torusSize h) :=
      mul_le_mul (mul_le_mul ha he (Real.exp_nonneg _) ((norm_nonneg _).trans ha))
        (endFrequency_norm_le s h) (norm_nonneg _) (mul_nonneg ((norm_nonneg _).trans ha) (Real.exp_nonneg _))
    _ = _ := by ring

def endFlatPoisson (s : Fin 3 → ℝ) (f : spectralTraceGraph (torusRate s))
    (x : Fin 3 → ℝ) : ℂ := ∑' h,endFlatMode s h (f.val 0 h) x

lemma endFlatPoisson_derivative_summable (s : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (f : spectralTraceGraph (torusRate s)) {x : Fin 3 → ℝ} (hx : 0<x 0) :
    Summable (fun h => endFlatMode s h (f.val 0 h) x • endFrequency s h) := by
  apply Summable.of_norm
  have hu : Summable (fun h => ‖f.val 0‖*((torusRate s h+torusSize h)*
      Real.exp (-x 0*torusRate s h))) := by
    simpa only [pow_one] using (flatMode_derivative_summable hs 1 hx).mul_left ‖f.val 0‖
  exact hu.of_nonneg_of_le (fun h => norm_nonneg _) (fun h =>
    endFlatMode_derivative_bound s h (lp.norm_apply_le_norm (by norm_num) (f.val 0) h) le_rfl)

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

lemma sourceCollarOpenBox_subset : sourceCollarOpenBox ⊆
    sourceExtendedBox (-(1:ℝ)/100) (1/100) := by
  intro x hx
  exact mem_sourceExtendedBox.mpr ⟨⟨hx.1.1.le,hx.1.2.le⟩,hx.2.1.le,hx.2.2.le⟩

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_PhysicalEndLocalLipschitz
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus

lemma locallyLipschitz_sourceRadial : LocallyLipschitz sourceRadial := by
  have h0 : LocallyLipschitz (fun y : Fin 3 → ℝ => |y 0|/sourceLength) :=
    (show ContDiff ℝ 1 (fun r : ℝ => r/sourceLength) by fun_prop).locallyLipschitz.comp
      (localLipschitz_abs.locallyLipschitz.comp (LipschitzWith.eval 0).locallyLipschitz)
  exact h0.max (localLipschitz_abs.locallyLipschitz.comp (LipschitzWith.eval 1).locallyLipschitz)

lemma locallyLipschitz_sourceCollarTime : LocallyLipschitz sourceCollarTime := by
  have h0 : LocallyLipschitz (fun y : Fin 3 → ℝ => |(sourceRadial y-sourceRadialCenter)/sourceRadialWidth|) :=
    localLipschitz_abs.locallyLipschitz.comp
      ((show ContDiff ℝ 1 (fun r : ℝ => (r-sourceRadialCenter)/sourceRadialWidth) by fun_prop).locallyLipschitz.comp
        locallyLipschitz_sourceRadial)
  exact (show ContDiff ℝ 1 (fun r : ℝ => 1-r) by fun_prop).locallyLipschitz.comp
    (h0.max (localLipschitz_abs.locallyLipschitz.comp (LipschitzWith.eval 2).locallyLipschitz))

lemma locallyLipschitz_sourceDirection (j : Fin 2) :
    LocallyLipschitz (fun y => sourceComplexDirections y j) := by
  fin_cases j
  · have h0 : ContDiff ℝ 1 (fun y : Fin 3 → ℝ => y 0/sourceLength) := by fun_prop
    have h1 : ContDiff ℝ 1 (fun y : Fin 3 → ℝ => y 1) := by fun_prop
    have hc : ContDiff ℝ 1 (fun y : Fin 3 → ℝ => ((y 0/sourceLength:ℝ):ℂ)+Complex.I*(y 1:ℂ)) :=
      (Complex.ofRealCLM.contDiff.comp h0).add (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp h1))
    exact hc.locallyLipschitz
  · have h0 : ContDiff ℝ 1 (fun p : ℝ×ℝ => p.1-sourceRadialCenter) := by fun_prop
    have h1 : ContDiff ℝ 1 (fun p : ℝ×ℝ => p.2) := by fun_prop
    have hc : ContDiff ℝ 1 (fun p : ℝ×ℝ => ((p.1-sourceRadialCenter:ℝ):ℂ)+Complex.I*(p.2:ℂ)) :=
      (Complex.ofRealCLM.contDiff.comp h0).add (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp h1))
    have hpr : LocallyLipschitz (fun y : Fin 3 → ℝ => (sourceRadial y,y 2)) :=
      locallyLipschitz_sourceRadial.prodMk (LipschitzWith.eval 2).locallyLipschitz
    convert! hc.locallyLipschitz.comp hpr using 1
    all_goals try with_reducible_and_instances rfl

def sourceLocalFlat (x y : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![sourceCollarTime y,localComplexArg (sourceComplexDirections x 0) (sourceComplexDirections y 0),
    localComplexArg (sourceComplexDirections x 1) (sourceComplexDirections y 1)]

lemma sourceLocalFlat_localLip {x : Fin 3 → ℝ} (hx : ∀ i,sourceComplexDirections x i≠0) :
    LocalLipAt (sourceLocalFlat x) x := by
  have ha (i : Fin 2) : LocalLipAt (fun y => localComplexArg (sourceComplexDirections x i) (sourceComplexDirections y i)) x :=
    (localLipAt_of_contDiffAt (localComplexArg_contDiffAt (hx i))).comp
      (f:=fun y => sourceComplexDirections y i) (locallyLipschitz_sourceDirection i x)
  have hv : ContDiff ℝ 1 (fun p : ℝ×(ℝ×ℝ) => ![p.1,p.2.1,p.2.2]) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i
    · change ContDiff ℝ 1 (fun p : ℝ×(ℝ×ℝ) => p.1); fun_prop
    · change ContDiff ℝ 1 (fun p : ℝ×(ℝ×ℝ) => p.2.1); fun_prop
    · change ContDiff ℝ 1 (fun p : ℝ×(ℝ×ℝ) => p.2.2); fun_prop
  have hp : LocalLipAt (fun y : Fin 3 → ℝ => (sourceCollarTime y,
      (localComplexArg (sourceComplexDirections x 0) (sourceComplexDirections y 0),
       localComplexArg (sourceComplexDirections x 1) (sourceComplexDirections y 1)))) x :=
    (show LocalLipAt sourceCollarTime x from locallyLipschitz_sourceCollarTime x).prodMk ((ha 0).prodMk (ha 1))
  convert! (localLipAt_of_contDiffAt hv.contDiffAt).comp (f:=fun y : Fin 3 → ℝ =>
    (sourceCollarTime y,(localComplexArg (sourceComplexDirections x 0) (sourceComplexDirections y 0),
      localComplexArg (sourceComplexDirections x 1) (sourceComplexDirections y 1)))) hp using 1
  all_goals try with_reducible_and_instances rfl

lemma sourceLocalFlat_angles {x y : Fin 3 → ℝ}
    (hx : ∀ i,sourceComplexDirections x i≠0) (hy : ∀ i,sourceComplexDirections y i≠0) :
    torusAngles (sourceLocalFlat x y)=sourcePhysicalAngles y := by
  funext i
  fin_cases i <;> simp only [torusAngles,sourceLocalFlat,sourcePhysicalAngles,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  · exact localComplexArg_unitAngle (hx 0) (hy 0)
  · exact localComplexArg_unitAngle (hx 1) (hy 1)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_AttachedEndPoisson
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus Matrix

lemma torusAngles_endAxialAffine (a b : ℝ) (x : Fin 3 → ℝ) :
    torusAngles (endAxialAffine a b x)=torusAngles x := by
  ext k
  fin_cases k <;> rfl

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_PhysicalCollarBand
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus

lemma sourceClosedCollarBand_measure_le {l r : ℝ}
    (hl : -(1:ℝ)/100≤l) (hr : r≤1/100) :
    volume.restrict (sourceClosedCollarBand l r) ≤ sourcePhysicalCollarMeasure l r := by
  rw [sourceClosedCollarBand_eq l r hl hr]
  calc
    _ ≤ Measure.sum (fun i : Fin 4 => volume.restrict
        (⋃ j : Fin 4,sourceCollarPiece i j '' sourceExtendedBox l r)) := Measure.restrict_iUnion_le
    _ = ∑ i : Fin 4,volume.restrict
        (⋃ j : Fin 4,sourceCollarPiece i j '' sourceExtendedBox l r) := Measure.sum_fintype _
    _ ≤ ∑ i : Fin 4,∑ j : Fin 4,volume.restrict
        (sourceCollarPiece i j '' sourceExtendedBox l r) := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [Measure.sum_fintype] using
        (Measure.restrict_iUnion_le (μ:=volume)
          (s:=fun j : Fin 4 => sourceCollarPiece i j '' sourceExtendedBox l r))
    _ = _ := rfl

lemma sourceClosedCollarBand_memLp {l r : ℝ}
    (hl : -(1:ℝ)/100≤l) (hr : r≤1/100) {f : (Fin 3 → ℝ) → ℂ}
    (hf : MemLp f 2 (sourcePhysicalCollarMeasure l r)) :
    MemLp f 2 (volume.restrict (sourceClosedCollarBand l r)) :=
  hf.mono_measure (sourceClosedCollarBand_measure_le hl hr)

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

lemma sourceCollarOpenBox_eq_interior : sourceCollarOpenBox=
    interior (sourceExtendedBox (-(1:ℝ)/100) (1/100)) := by
  have hbox : sourceExtendedBox (-(1:ℝ)/100) (1/100)=
      (univ : Set (Fin 3)).pi (fun k => Icc (![(-(1:ℝ)/100),-1,-1] k) (![1/100,1,1] k)) := by
    ext x
    simp only [sourceExtendedBox,mem_Icc,Set.mem_pi,mem_univ,true_implies,Pi.le_def]
    simp only [forall_and]
  rw [hbox,interior_pi_set (finite_univ),show (fun k : Fin 3 => interior
    (Icc (![(-(1:ℝ)/100),-1,-1] k) (![1/100,1,1] k)))=
      (fun k => Ioo (![(-(1:ℝ)/100),-1,-1] k) (![1/100,1,1] k)) from funext (fun _ => interior_Icc)]
  ext x
  simp only [sourceCollarOpenBox,mem_ofPred_eq,Set.mem_pi,mem_univ,true_implies,Fin.forall_fin_succ,
    mem_Ioo,Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.forall_fin_zero,
    abs_lt]
  simp

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_AttachedEndDifferential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus Matrix

lemma sourceCollarPiece_time_open {i j : Fin 4} {x : Fin 3 → ℝ}
    (hx : x∈sourceCollarOpenBox) : sourceCollarTime (sourceCollarPiece i j x)=x 0 := by
  obtain ⟨ht,hi,hj⟩ := mem_sourceExtendedBox.mp (sourceCollarOpenBox_subset hx)
  rw [←sourceFaceAngles_physical i j hi hj,sourceAngular_time ht]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_AttachedEndGradientL2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus Matrix
open scoped ENNReal

lemma sourceAngularCollarMeasure_self (b : ℝ) : sourceAngularCollarMeasure b b=0 := by
  simp [sourceAngularCollarMeasure]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_CollarLip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology
open scoped NNReal

lemma sourceRadial_lipschitz : ∃ K,LipschitzWith K sourceRadial := by
  have h0 := ((ContinuousLinearMap.toSpanSingleton ℝ (sourceLength⁻¹ : ℝ)).lipschitz.comp
    (localLipschitz_abs.comp (LipschitzWith.eval (α := fun _ : Fin 3 => ℝ) (0:Fin 3))))
  have h1 := localLipschitz_abs.comp (LipschitzWith.eval (α := fun _ : Fin 3 => ℝ) (1:Fin 3))
  have H := h0.max h1
  refine ⟨max (‖ContinuousLinearMap.toSpanSingleton ℝ sourceLength⁻¹‖₊*(1*1)) (1*1),?_⟩
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [sourceRadial,div_eq_mul_inv,ContinuousLinearMap.toSpanSingleton_apply,Function.comp_apply,smul_eq_mul] using H.dist_le_mul x y

lemma sourceCollarTime_lipschitz : ∃ K,LipschitzWith K sourceCollarTime := by
  obtain ⟨K,hK⟩ := sourceRadial_lipschitz
  have h0 := localLipschitz_abs.comp ((ContinuousLinearMap.toSpanSingleton ℝ (sourceRadialWidth⁻¹ : ℝ)).lipschitz.comp
    (hK.sub (LipschitzWith.const sourceRadialCenter)))
  have h1 := localLipschitz_abs.comp (LipschitzWith.eval (α := fun _ : Fin 3 => ℝ) (2:Fin 3))
  have H := (LipschitzWith.const (1:ℝ)).sub (h0.max h1)
  refine ⟨0+max (1*(‖ContinuousLinearMap.toSpanSingleton ℝ sourceRadialWidth⁻¹‖₊*(K+0))) (1*1),?_⟩
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [Matrix.cons_val_zero,Matrix.cons_val_one,sourceCollarTime,sourceCrossCoordinates,div_eq_mul_inv,ContinuousLinearMap.toSpanSingleton_apply,Function.comp_apply,smul_eq_mul] using H.dist_le_mul x y

lemma attachedEndTime_lipschitz (a b : ℝ) :
    ∃ K,LipschitzWith K (fun y => a*(sourceCollarTime y-b)) := by
  obtain ⟨K,hK⟩ := sourceCollarTime_lipschitz
  have H := (ContinuousLinearMap.toSpanSingleton ℝ a).lipschitz.comp (hK.sub (LipschitzWith.const b))
  refine ⟨‖ContinuousLinearMap.toSpanSingleton ℝ a‖₊*(K+0),?_⟩
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [ContinuousLinearMap.toSpanSingleton_apply,Function.comp_apply,smul_eq_mul,mul_comm] using H.dist_le_mul x y

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

instance centralAmbientNormedSpace (s : Fin 3 → ℝ) : NormedSpace ℝ (CentralAmbient s) := inferInstance

def centralAmbientOne (s : Fin 3 → ℝ) : CentralAmbient s := centralEmbedL s centralSmoothOne

def centralOne (s : Fin 3 → ℝ) : centralEnergySpace s :=
  ⟨centralAmbientOne s,(LinearMap.range (centralEmbedL s)).le_topologicalClosure ⟨centralSmoothOne,rfl⟩⟩

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

def centralCoercivityBase : ℝ :=
  1+centralPoincareConstant+3*centralTraceConstant*(192+2*centralPoincareConstant)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_CentralDistribution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

def centralDirection (i : Fin 3) : Box3 := ![((1,0),0),((0,1),0),((0,0),1)] i

lemma centralJetField_succ (f : Box3 → ℝ) (i : Fin 3) :
    centralJetField f i.succ=cubePartial f (centralDirection i) := by
  fin_cases i <;> rfl

def centralSmoothElement (s : Fin 3 → ℝ) (f : centralSmoothFunctions) : centralEnergySpace s :=
  ⟨centralEmbedL s f,(LinearMap.range (centralEmbedL s)).le_topologicalClosure ⟨f,rfl⟩⟩

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_SmoothCollarRate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal NNReal

lemma smooth_sourceCollar_lipschitz {q : (Fin 3 → ℝ) → ℝ}
    (hq : ContDiff ℝ (↑(⊤:ℕ∞)) q) :
    ∃ K : ℝ≥0,LipschitzOnWith K q (sourceClosedCollarBand (-(1:ℝ)/100) (1/100)) := by
  obtain ⟨R,hR⟩ := (isCompact_sourceClosedCollarBand (le_refl _) (le_refl _)).isBounded.subset_closedBall 0
  obtain ⟨K,hK⟩ := hq.contDiffOn.exists_lipschitzOnWith (s:=Metric.closedBall 0 R)
    (by simp) (convex_closedBall (0:Fin 3 → ℝ) R) (isCompact_closedBall _ _)
  exact ⟨K,hK.mono hR⟩

attribute [local instance] OAI.ScalarConductivity.smoothCollarRateMeasureSpace
local instance smoothCollarRateProbabilityMeasure : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

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

def sourceCollarVolumeConstant : ℝ :=
  2/(faceRayDensityLower 1*faceRayDensityLower sourceRadialWidth)

lemma sourceCollarVolumeConstant_pos : 0 < sourceCollarVolumeConstant := by
  apply div_pos (by norm_num)
  exact mul_pos (faceRayDensityLower_pos (by norm_num))
    (faceRayDensityLower_pos (by norm_num [sourceRadialWidth,sourceHole]))

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_NonlinearLp
attribute [-instance] _root_.OAI.ScalarConductivity.bumpProbability_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory Filter Topology
open scoped ENNReal

def jetSuperposition (g dg : ℝ → ℝ) (z : JetFiber) : JetFiber :=
  jetLiftValue (g (jetValue z)) + jetLiftGradient (dg (jetValue z) • jetGradient z)

lemma jetSuperposition_continuous {g dg : ℝ → ℝ} (hg : Continuous g) (hdg : Continuous dg) :
    Continuous (jetSuperposition g dg) := by
  exact (jetLiftValue.continuous.comp (hg.comp jetValue.continuous)).add
    (jetLiftGradient.continuous.comp ((hdg.comp jetValue.continuous).smul jetGradient.continuous))

def jetSuperpositionBound (C : ℝ) : ℝ :=
  ‖jetLiftValue‖*C*‖jetValue‖ + ‖jetLiftGradient‖*C*‖jetGradient‖

lemma jetSuperpositionBound_nonneg {C : ℝ} (hC : 0≤C) : 0≤jetSuperpositionBound C := by
  unfold jetSuperpositionBound
  positivity

lemma jetSuperposition_bound {g dg : ℝ → ℝ} {C : ℝ} (hC : 0≤C)
    (hg : ∀ r, ‖g r‖≤C*‖r‖) (hdg : ∀ r, ‖dg r‖≤C) (z : JetFiber) :
    ‖jetSuperposition g dg z‖≤jetSuperpositionBound C*‖z‖ := by
  have hval := jetValue.le_opNorm z
  have hgrad := jetGradient.le_opNorm z
  have h1 := jetLiftValue.le_opNorm (g (jetValue z))
  have h2 := jetLiftGradient.le_opNorm (dg (jetValue z) • jetGradient z)
  rw [norm_smul] at h2
  calc
    _ ≤ ‖jetLiftValue (g (jetValue z))‖ +
        ‖jetLiftGradient (dg (jetValue z) • jetGradient z)‖ := norm_add_le _ _
    _ ≤ ‖jetLiftValue‖*(C*(‖jetValue‖*‖z‖)) +
        ‖jetLiftGradient‖*(C*(‖jetGradient‖*‖z‖)) := by
      apply add_le_add
      · exact h1.trans (mul_le_mul_of_nonneg_left ((hg _).trans
          (mul_le_mul_of_nonneg_left hval hC)) (norm_nonneg _))
      · exact h2.trans (mul_le_mul_of_nonneg_left
          (mul_le_mul (hdg _) hgrad (norm_nonneg _) hC) (norm_nonneg _))
    _ = _ := by unfold jetSuperpositionBound; ring

lemma smoothJet_comp {g dg : ℝ → ℝ} (hdg : ∀ r, HasDerivAt g (dg r) r)
    {f : R3 → ℝ} (hf : Differentiable ℝ f) (x : R3) :
    smoothJet (g ∘ f) x = jetSuperposition g dg (smoothJet f x) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · change g (f x)=g (f x)+0; simp
  · change gradient (g ∘ f) x j = 0 + (dg (f x) • gradient f x) j
    rw [gradient_comp_scalar hdg hf]
    simp

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

def sobolevChainLp : JetSpace → JetSpace :=
  nonlinearLp ballMeasure (jetSuperposition g dg)
    (jetSuperposition_continuous hg.continuous hdg) (jetSuperpositionBound C)
    (jetSuperpositionBound_nonneg hC) (jetSuperposition_bound hC hgb hdgb)

lemma sobolevChainLp_continuous : Continuous (sobolevChainLp hg hdg hC hgb hdgb) :=
  nonlinearLp_continuous _ _ _ _ _ _

lemma sobolevChainLp_coe_ae (z : JetSpace) :
    sobolevChainLp hg hdg hC hgb hdgb z =ᵐ[ballMeasure]
      fun x => jetSuperposition g dg (z x) := nonlinearLp_coe_ae _ _ _ _ _ _ _

include hderiv

lemma sobolevChainLp_smooth {f : R3 → ℝ} (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (hm : MemLp (smoothJet f) 2 ballMeasure) :
    ∃ hgm : MemLp (smoothJet (g ∘ f)) 2 ballMeasure,
      sobolevChainLp hg hdg hC hgb hdgb (hm.toLp _) = hgm.toLp _ := by
  have he : sobolevChainLp hg hdg hC hgb hdgb (hm.toLp _) =ᵐ[ballMeasure]
      smoothJet (g ∘ f) := by
    filter_upwards [sobolevChainLp_coe_ae hg hdg hC hgb hdgb (hm.toLp _),hm.coeFn_toLp] with x hx hy
    rw [hx,hy,←smoothJet_comp hderiv (hf.differentiable (by simp))]
  have hgm := MemLp.ae_eq he (Lp.memLp (sobolevChainLp hg hdg hC hgb hdgb (hm.toLp _)))
  refine ⟨hgm,?_⟩
  apply Lp.ext
  exact he.trans hgm.coeFn_toLp.symm

lemma sobolevChainLp_preserves_H1 {z : JetSpace} (hz : z∈H1Space) :
    sobolevChainLp hg hdg hC hgb hdgb z ∈ H1Space := by
  change z ∈ (H1Space : Set JetSpace) at hz
  change _ ∈ (H1Space : Set JetSpace)
  rw [H1Space_eq_closure] at hz ⊢
  apply nonlinear_closure_preservation (sobolevChainLp_continuous hg hdg hC hgb hdgb) _ hz
  rintro w ⟨f,hf,hm,rfl⟩
  obtain ⟨hgm,he⟩ := sobolevChainLp_smooth hg hdg hderiv hC hgb hdgb hf hm
  exact ⟨g ∘ f,hg.comp hf,hgm,he⟩

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_SobolevSmoothOperations
attribute [-instance] _root_.OAI.ScalarConductivity.bumpProbability_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory Filter Topology Real

namespace SmoothLipZero

def onLp (F : SmoothLipZero) : JetSpace → JetSpace :=
  sobolevChainLp F.smooth (smooth_deriv_infty F.smooth).continuous F.bound_nonneg F.growth F.deriv_bound

lemma preserves_H1 (F : SmoothLipZero) {z : JetSpace} (hz : z∈H1Space) :
    F.onLp z∈H1Space :=
  sobolevChainLp_preserves_H1 _ _ F.derivative _ _ _ hz

def onH1 (F : SmoothLipZero) (u : H1) : H1 := ⟨F.onLp u.val,F.preserves_H1 u.property⟩

end SmoothLipZero

def squareOperation (M : ℝ) : SmoothLipZero :=
  SmoothLipZero.ofCompact (squaredValue M) (squaredValue_smooth M)
    (squaredValue_compact M) (squaredValue_zero M)

def clipOperation (M : ℝ) : SmoothLipZero :=
  SmoothLipZero.ofCompact (clippedValue M) (clippedValue_smooth M)
    (clippedValue_compact M) (clippedValue_zero M)

variable (F G : SmoothLipZero) (A B : ℝ)

def clippedProductLp (z w : JetSpace) : JetSpace :=
  (1/2:ℝ) • ((squareOperation (A+B)).onLp (F.onLp z+G.onLp w) -
    (squareOperation (A+B)).onLp (F.onLp z) -
    (squareOperation (A+B)).onLp (G.onLp w))

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_SobolevTraceChain
attribute [-instance] _root_.OAI.ScalarConductivity.bumpProbability_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma smoothJet_constant (r : ℝ) : smoothJet (fun _ : R3 => r)=fun _ => jetLiftValue r := by
  ext x i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · simp [smoothJet,gradient,jetLiftValue]

lemma constantJet_memLp (r : ℝ) : MemLp (smoothJet (fun _ : R3 => r)) 2 ballMeasure := by
  rw [smoothJet_constant]
  exact memLp_const _

def constantH1 (r : ℝ) : H1 :=
  ⟨(constantJet_memLp r).toLp _,(Submodule.le_topologicalClosure _)
    (Submodule.subset_span ⟨fun _ => r,contDiff_const,constantJet_memLp r,rfl⟩)⟩

lemma weakValue_add (u v : H1) : weakValue (u+v) =ᵐ[ballMeasure] weakValue u+weakValue v := by
  filter_upwards [Lp.coeFn_add u.val v.val] with x hx
  change jetValue ((u.val+v.val) x)=jetValue (u.val x)+jetValue (v.val x)
  rw [hx,Pi.add_apply,map_add]

lemma weakGradient_add (u v : H1) : weakGradient (u+v) =ᵐ[ballMeasure] weakGradient u+weakGradient v := by
  filter_upwards [Lp.coeFn_add u.val v.val] with x hx
  change jetGradient ((u.val+v.val) x)=jetGradient (u.val x)+jetGradient (v.val x)
  rw [hx,Pi.add_apply,map_add]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_SobolevSmoothTests
attribute [-instance] _root_.OAI.ScalarConductivity.bumpProbability_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity

open Set MeasureTheory Filter Topology

lemma smoothH1_value (f : R3 → ℝ) (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) :
    weakValue (smoothH1 f hf) =ᵐ[ballMeasure] f := by
  filter_upwards [(smoothJet_memLp hf).coeFn_toLp] with x hx
  exact congrArg jetValue hx

lemma smoothH1_gradient (f : R3 → ℝ) (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) :
    weakGradient (smoothH1 f hf) =ᵐ[ballMeasure] gradient f := by
  filter_upwards [(smoothJet_memLp hf).coeFn_toLp] with x hx
  exact congrArg jetGradient hx

open Set MeasureTheory Filter Topology Real

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_CompactBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity

open Set MeasureTheory Filter Topology

lemma mollifiedJet_eq (F : Fin 4 → WholeL2)
    (hw : ∀ i : Fin 3, WeakL2Direction (F 0) (F i.succ) (EuclideanSpace.single i 1))
    (φ : SpatialBump) :
    ballJet (fun i => mollifyL2 φ (F i))=
      (smoothH1 (mollifyReal φ (F 0))
        (mollifyReal_smooth φ ((Lp.memLp (F 0)).locallyIntegrable (by norm_num)))).val := by
  apply Lp.ext
  have hma : ∀ᵐ x ∂ballMeasure, ∀ i : Fin 4,
      mollifyL2 φ (F i) x=mollifyReal φ (F i) x :=
    (ae_all_iff.mpr (fun i => mollifyL2_ae φ (F i))).filter_mono (ae_mono Measure.restrict_le_self)
  filter_upwards [ballJet_ae (fun i => mollifyL2 φ (F i)),hma,
    (smoothJet_memLp (mollifyReal_smooth φ
      ((Lp.memLp (F 0)).locallyIntegrable (by norm_num)))).coeFn_toLp] with x hx hy hz
  change _ = (smoothJet_memLp (mollifyReal_smooth φ
    ((Lp.memLp (F 0)).locallyIntegrable (by norm_num)))).toLp _ x
  rw [hz]
  ext i
  rw [hx i,hy i]
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · change mollifyReal φ (F j.succ) x=gradient (mollifyReal φ (F 0)) x j
    have hd := mollifyReal_direction (Lp.memLp (F 0)) (Lp.memLp (F j.succ))
      (EuclideanSpace.single j 1) (hw j) φ x
    have he : inner ℝ (EuclideanSpace.single j 1) (gradient (mollifyReal φ (F 0)) x)=
        fderiv ℝ (mollifyReal φ (F 0)) x (EuclideanSpace.single j 1) := by
      simp only [inner_gradient_right,RCLike.conj_to_real]
    simpa only [EuclideanSpace.inner_single_left,RCLike.conj_to_real,one_mul]
      using (he.trans hd).symm

theorem compact_weakJet_mem_zeroTrace (F : Fin 4 → WholeL2)
    (hw : ∀ i : Fin 3, WeakL2Direction (F 0) (F i.succ) (EuclideanSpace.single i 1))
    {R : ℝ} (hR : R<3) (hs : ∀ᵐ x, R<‖x‖ → F 0 x=0) :
    ballJet F∈zeroTraceAmbient := by
  apply (Submodule.isClosed_topologicalClosure (Submodule.span ℝ compactSmoothJets)).mem_of_tendsto
    (ballJet_mollify_tendsto F)
  have he : ∀ᶠ n in atTop, (dyadicBump n).rOut<3-R :=
    dyadicBump_radius.eventually (gt_mem_nhds (by linarith))
  filter_upwards [he] with n hn
  rw [mollifiedJet_eq F hw]
  apply Submodule.le_topologicalClosure
  apply Submodule.subset_span
  refine ⟨mollifyReal (dyadicBump n) (F 0),
    mollifyReal_smooth _ ((Lp.memLp (F 0)).locallyIntegrable (by norm_num)),
    mollifyReal_compact hs _,?_,smoothJet_memLp (mollifyReal_smooth _
      ((Lp.memLp (F 0)).locallyIntegrable (by norm_num))),rfl⟩
  intro x hx
  have hb := mollifyReal_support hs (dyadicBump n) hx
  change ‖x-0‖<3
  rw [sub_zero]
  have hh : ‖x‖≤R+(dyadicBump n).rOut := by simpa using hb
  linarith

theorem compact_weak_H1 (F : Fin 4 → WholeL2)
    (hw : ∀ i : Fin 3, WeakL2Direction (F 0) (F i.succ) (EuclideanSpace.single i 1))
    {R : ℝ} (hR : R<3) (hs : ∀ᵐ x, R<‖x‖ → F 0 x=0) :
    ∃ u : H1, u∈H10 ∧
      (∀ᵐ x ∂ballMeasure, weakValue u x=F 0 x ∧ ∀ i : Fin 3, weakGradient u x i=F i.succ x) := by
  have hz := compact_weakJet_mem_zeroTrace F hw hR hs
  let u : H1 := ⟨ballJet F,zeroTraceAmbient_le_H1Space hz⟩
  refine ⟨u,hz,?_⟩
  filter_upwards [ballJet_ae F] with x hx
  exact ⟨hx 0,fun i => hx i.succ⟩

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_MatchedSeamH1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory Filter Topology
open scoped NNReal

theorem compact_matched_seam_H1 {τ u : R3 → ℝ} {K : ℝ≥0}
    (hτ : LipschitzWith K τ) (hu : MemLp u 2 volume)
    (hlocal : ∀ x,0<τ x → LocalLipAt u x)
    (g : Fin 3 → R3 → ℝ) (hg : ∀ i,MemLp (g i) 2 volume)
    (hd : ∀ i,∀ᵐ x,0<τ x → HasLineDerivAt ℝ u (g i x) x (EuclideanSpace.single i 1))
    (hz : ∀ᵐ x,τ x≤0 → u x=0 ∧ ∀ i,g i x=0)
    {R : ℝ} (hR : R<3) (hs : ∀ x,R<‖x‖ → u x=0)
    (hthin : Tendsto (fun n : ℕ => ((n:ℝ)+1)^2*∫ x in seamLayer τ n,u x^2) atTop (𝓝 0)) :
    ∃ w : H1,w∈H10 ∧ (∀ᵐ x∂ballMeasure,
      weakValue w x=u x ∧ ∀ i,weakGradient w x i=g i x) := by
  let f : ℕ → R3 → ℝ := fun n x => seamCutoff n (τ x)*u x
  have hfs (n : ℕ) (x : R3) (hx : R<‖x‖) : f n x=0 := by
    dsimp [f]; rw [hs x hx,mul_zero]
  have hfl (n : ℕ) : ∃ L,LipschitzWith L (f n) :=
    seamCutoff_mul_lipschitz hτ.locallyLipschitz hlocal (bounded_support_compact hs) n
  choose L hL using hfl
  have hfm (n : ℕ) : MemLp (f n) 2 volume :=
    (hL n).continuous.memLp_of_hasCompactSupport (bounded_support_compact (hfs n))
  let d : ℕ → Fin 3 → R3 → ℝ := fun n i x => lineDeriv ℝ (f n) x (EuclideanSpace.single i 1)
  have hdm (n : ℕ) (i : Fin 3) : MemLp (d n i) 2 volume :=
    lipschitz_lineDeriv_memLp (hL n) (hfs n) _
  have hv : Tendsto (fun n => (hfm n).toLp (f n)) atTop (𝓝 (hu.toLp u)) := by
    apply memLp_toLp_tendsto_of_sq hfm hu
    exact seamCutoff_L2_approx hτ.continuous hu (hz.mono (fun x hx ht => (hx ht).1))
  have hgrad (i : Fin 3) : Tendsto (fun n => (hdm n i).toLp (d n i)) atTop (𝓝 ((hg i).toLp (g i))) := by
    apply memLp_toLp_tendsto_of_sq (fun n => hdm n i) (hg i)
    exact seamCutoff_gradient_L2_approx hτ _ hu (hg i) (hd i)
      (hz.mono (fun x hx ht => ⟨(hx ht).1,(hx ht).2 i⟩)) (fun n => hdm n i) hthin
  have hw (i : Fin 3) : WeakL2Direction (hu.toLp u) ((hg i).toLp (g i)) (EuclideanSpace.single i 1) := by
    apply WeakL2Direction.closed hv (hgrad i)
    intro n
    exact (lipschitz_weakDirection (hL n) _).congr (hfm n).coeFn_toLp (hdm n i).coeFn_toLp
  let F : Fin 4 → WholeL2 := Fin.cases (hu.toLp u) (fun i => (hg i).toLp (g i))
  obtain ⟨w,hw₀,he⟩ := compact_weak_H1 F hw hR (by
    filter_upwards [hu.coeFn_toLp] with x hx
    intro hn
    exact hx.trans (hs x hn))
  refine ⟨w,hw₀,?_⟩
  have hv' := hu.coeFn_toLp.filter_mono (ae_mono (Measure.restrict_le_self (s:=ball)))
  have hg' := (ae_all_iff.mpr (fun i => (hg i).coeFn_toLp)).filter_mono
    (ae_mono (Measure.restrict_le_self (s:=ball)))
  filter_upwards [he,hv',hg'] with x hx hy hz
  exact ⟨hx.1.trans hy,fun i => (hx.2 i).trans (hz i)⟩

theorem compact_matched_seam_H1_pi {τ u : (Fin 3 → ℝ) → ℝ} {K : ℝ≥0}
    (hτ : LipschitzWith K τ) (hu : MemLp u 2 volume)
    (hlocal : ∀ x,0<τ x → LocalLipAt u x)
    (g : Fin 3 → (Fin 3 → ℝ) → ℝ) (hg : ∀ i,MemLp (g i) 2 volume)
    (hd : ∀ i,∀ᵐ x,0<τ x → HasLineDerivAt ℝ u (g i x) x (Pi.single i 1))
    (hz : ∀ᵐ x,τ x≤0 → u x=0 ∧ ∀ i,g i x=0)
    {R : ℝ} (hR : R<3) (hs : ∀ x,R<‖WithLp.toLp 2 x‖ → u x=0)
    (hthin : Tendsto (fun n : ℕ => ((n:ℝ)+1)^2*
      ∫ x in {x | 0<τ x ∧ ((n:ℝ)+1)*τ x≤2},u x^2) atTop (𝓝 0)) :
    ∃ w : H1,w∈H10 ∧ (∀ᵐ x∂ballMeasure,
      weakValue w x=u (WithLp.ofLp x) ∧ ∀ i,weakGradient w x i=g i (WithLp.ofLp x)) := by
  let E : R3 ≃L[ℝ] (Fin 3 → ℝ) := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)
  have hm : MeasurePreserving E volume volume := PiLp.volume_preserving_ofLp (Fin 3)
  have hd' (i : Fin 3) : ∀ᵐ x : R3,0<τ (E x) →
      HasLineDerivAt ℝ (u ∘ E) (g i (E x)) x (EuclideanSpace.single i 1) := by
    filter_upwards [hm.quasiMeasurePreserving.ae (hd i)] with x hx ht
    have hh := hx ht
    have he : E (EuclideanSpace.single i 1)=Pi.single i 1 := rfl
    simpa only [HasLineDerivAt,Function.comp_apply,map_add,map_smul,he]
      using hh
  have hthin' : Tendsto (fun n : ℕ => ((n:ℝ)+1)^2*
      ∫ x in seamLayer (τ ∘ E) n,(u (E x))^2) atTop (𝓝 0) := by
    convert hthin using 1
    all_goals try with_reducible_and_instances rfl
    ext n
    congr 1
    have hs' : MeasurableSet {x : Fin 3 → ℝ | 0<τ x ∧ ((n:ℝ)+1)*τ x≤2} :=
      (measurableSet_lt measurable_const hτ.continuous.measurable).inter
        (measurableSet_le (measurable_const.mul hτ.continuous.measurable) measurable_const)
    exact (hm.restrict_preimage hs').integral_comp E.toHomeomorph.measurableEmbedding (fun x => u x^2)
  apply compact_matched_seam_H1 (hτ.comp E.lipschitz) (hu.comp_measurePreserving hm)
    (fun x ht => (hlocal (E x) ht).comp (E.lipschitz.locallyLipschitz x))
    (fun i => g i ∘ E) (fun i => (hg i).comp_measurePreserving hm) hd'
    (hm.quasiMeasurePreserving.ae hz) hR _ hthin'
  intro x hx
  exact hs (E x) hx

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Walls_LocalizedMatchedSeam
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology
open scoped NNReal

theorem localized_matched_seam_H1_pi {τ χ p : (Fin 3 → ℝ) → ℝ} {K : ℝ≥0}
    (hτ : LipschitzWith K τ) (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ)
    (hc : HasCompactSupport χ) {D : Set (Fin 3 → ℝ)} (hD : MeasurableSet D)
    (hp : MemLp p 2 (volume.restrict D))
    (hs : ∀ x∈tsupport χ,0<τ x → x∈D)
    (hl : ∀ x∈tsupport χ,0<τ x → LocalLipAt p x)
    (F : (Fin 3 → ℝ) → (Fin 3 → ℝ) →L[ℝ] ℝ)
    (hF : ∀ i : Fin 3,MemLp (fun x => F x (Pi.single i 1)) 2 (volume.restrict D))
    (hd : ∀ᵐ x∂volume.restrict D,0<τ x → HasFDerivAt p (F x) x)
    {R : ℝ} (hR : R<3) (hb : ∀ x∈tsupport χ,‖WithLp.toLp 2 x‖≤R)
    (hthin : Tendsto (fun n : ℕ => ((n:ℝ)+1)^2*
      ∫ x in {x | 0<τ x ∧ ((n:ℝ)+1)*τ x≤2},(cutMatchedValue τ χ p x)^2) atTop (𝓝 0)) :
    ∃ w : H1,w∈H10 ∧ (∀ᵐ x∂ballMeasure,
      weakValue w x=cutMatchedValue τ χ p (WithLp.ofLp x) ∧
      ∀ i,weakGradient w x i=cutMatchedGradient τ χ p F i (WithLp.ofLp x)) := by
  have hχd := hχ.differentiable (by simp)
  have hχf : Continuous (fderiv ℝ χ) := hχ.continuous_fderiv (by simp)
  have hgm (i : Fin 3) : MemLp (cutMatchedGradient τ χ p F i) 2 volume := by
    have h1 := cutMatchedValue_memLp hτ.continuous (hχf.clm_apply continuous_const)
      (hc.fderiv_apply ℝ (Pi.single i 1)) hD hp
      (fun x hx ht => hs x (tsupport_fderiv_apply_subset ℝ _ hx) ht)
    have h2 := cutMatchedValue_memLp hτ.continuous hχ.continuous hc hD (hF i) hs
    convert h1.add h2 using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    by_cases ht : 0<τ x <;> simp [cutMatchedValue,cutMatchedGradient,ht]
  have hu_eq {x : Fin 3 → ℝ} (ht : 0<τ x) :
      cutMatchedValue τ χ p =ᶠ[𝓝 x] (fun y => χ y*p y) := by
    filter_upwards [hτ.continuous.continuousAt.eventually (lt_mem_nhds ht)] with y hy
    exact ite_eq_left hy
  have hz_eq {x : Fin 3 → ℝ} (hx : x∉tsupport χ) :
      cutMatchedValue τ χ p =ᶠ[𝓝 x] 0 := by
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
    change χ y=0 at hy
    simp [cutMatchedValue,hy]
  have hul (x : Fin 3 → ℝ) (ht : 0<τ x) : LocalLipAt (cutMatchedValue τ χ p) x := by
    by_cases hx : x∈tsupport χ
    · exact ((localLipAt_of_contDiffAt (hχ.of_le (by simp)).contDiffAt).mul (hl x hx ht)).congr (hu_eq ht).symm
    · exact (localLipAt_of_contDiffAt (contDiffAt_const (c:=(0:ℝ)))).congr (hz_eq hx).symm
  have hud (i : Fin 3) : ∀ᵐ x,0<τ x → HasLineDerivAt ℝ (cutMatchedValue τ χ p)
      (cutMatchedGradient τ χ p F i x) x (Pi.single i 1) := by
    filter_upwards [(ae_restrict_iff' hD).mp hd] with x hx ht
    by_cases hxχ : x∈tsupport χ
    · have hh := (hχd x).hasFDerivAt.mul (hx (hs x hxχ ht) ht)
      have hh' := (hh.congr_of_eventuallyEq (hu_eq ht)).hasLineDerivAt (Pi.single i 1)
      simpa [cutMatchedGradient,ht,add_comm,mul_comm] using hh'
    · have hzero : cutMatchedGradient τ χ p F i x=0 := by
        have hd0 : fderiv ℝ χ x (Pi.single i 1)=0 :=
          image_eq_zero_of_notMem_tsupport (f:=fun y => fderiv ℝ χ y (Pi.single i 1))
            (fun h => hxχ (tsupport_fderiv_apply_subset ℝ _ h))
        simp [cutMatchedGradient,ht,image_eq_zero_of_notMem_tsupport hxχ,hd0]
      rw [hzero]
      exact ((hasFDerivAt_const (c:=(0:ℝ)) x).congr_of_eventuallyEq (hz_eq hxχ)).hasLineDerivAt _
  apply compact_matched_seam_H1_pi hτ (cutMatchedValue_memLp hτ.continuous hχ.continuous hc hD hp hs)
    hul (cutMatchedGradient τ χ p F) hgm hud _ hR _ hthin
  · exact Eventually.of_forall (fun x hx => by simp [cutMatchedValue,cutMatchedGradient,not_lt.mpr hx])
  · intro x hx
    have hnot : x∉tsupport χ := fun h => (hb x h).not_gt hx
    simp [cutMatchedValue,image_eq_zero_of_notMem_tsupport hnot]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_AttachedCutLayer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped NNReal

lemma continuous_sourceBand_memLp {q : (Fin 3 → ℝ) → ℝ} (hq : Continuous q)
    {l r : ℝ} (hl : -(1:ℝ)/100≤l) (hr : r≤1/100) :
    MemLp q 2 (volume.restrict (sourceClosedCollarBand l r)) := by
  have hc := isCompact_sourceClosedCollarBand hl hr
  let : IsFiniteMeasure (volume.restrict (sourceClosedCollarBand l r)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hc.measure_lt_top⟩
  obtain ⟨M,hM⟩ := hc.exists_bound_of_continuousOn hq.continuousOn
  exact MemLp.of_bound hq.aestronglyMeasurable M
    ((ae_restrict_mem hc.measurableSet).mono (fun x hx => hM x hx))

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_CollarInteriorFacts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma sourceDirections_ne_zero_on_band {y : Fin 3 → ℝ}
    (hy : y∈sourceClosedCollarBand (-(1:ℝ)/100) (1/100)) :
    ∀ i,sourceComplexDirections y i≠0 := by
  intro i he
  have hr := congrArg Complex.re he
  have hi := congrArg Complex.im he
  fin_cases i
  · simp [sourceComplexDirections] at hr hi
    have hy0 : y 0=0 := hr.resolve_right (by norm_num [sourceLength])
    have hh := sourceRadial_pos_of_time hy.1
    simp [sourceRadial,hy0,hi] at hh
  · simp [sourceComplexDirections] at hr hi
    have hh : sourceCollarTime y=1 := by
      simp [sourceCollarTime,sourceCrossCoordinates,hr,hi]
    have ht := hy.2
    rw [hh] at ht
    norm_num at ht

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

attribute [local instance] OAI.ScalarConductivity.smoothCollarTraceCircleMeasureSpace
attribute [local instance] OAI.ScalarConductivity.smoothCollarTraceCircleIsProbabilityMeasure
def smoothCollarTraceFourier (b : ℝ) {q : (Fin 3 → ℝ) → ℝ}
    (hq : ContDiff ℝ (↑(⊤:ℕ∞)) q) : SpectralL2 TorusModes :=
  (mFourierBasis (d:=Fin 2)).repr
    (ContinuousMap.toLp 2 volume ℂ
      ⟨fun θ => (q (sourceAngularCollar b θ):ℂ),
        Complex.continuous_ofReal.comp (hq.continuous.comp (continuous_sourceAngularCollar b))⟩)

lemma smoothCollarTraceFourier_apply (b : ℝ) {q : (Fin 3 → ℝ) → ℝ}
    (hq : ContDiff ℝ (↑(⊤:ℕ∞)) q) (h : TorusModes) :
    smoothCollarTraceFourier b hq h=mFourierCoeff (fun θ => (q (sourceAngularCollar b θ):ℂ)) h := by
  rw [smoothCollarTraceFourier,mFourierBasis_repr,mFourierCoeff_toLp]
  rfl

def smoothCollarTrace (s : Fin 3 → ℝ) (b : ℝ) {q : (Fin 3 → ℝ) → ℝ}
    (hq : ContDiff ℝ (↑(⊤:ℕ∞)) q) : spectralTraceGraph (torusRate s) :=
  ((spectralTraceGraph_exists_iff (w:=torusRate s) (fun h => Real.sqrt_nonneg _) (smoothCollarTraceFourier b hq)).mpr
    (by simpa only [smoothCollarTraceFourier_apply] using sourceAngularTrace_summable s b hq)).choose

lemma smoothCollarTrace_fst (s : Fin 3 → ℝ) (b : ℝ) {q : (Fin 3 → ℝ) → ℝ}
    (hq : ContDiff ℝ (↑(⊤:ℕ∞)) q) (h : TorusModes) :
    (smoothCollarTrace s b hq).val 0 h=mFourierCoeff (fun θ => (q (sourceAngularCollar b θ):ℂ)) h := by
  have he := ((spectralTraceGraph_exists_iff (w:=torusRate s) (fun h => Real.sqrt_nonneg _) (smoothCollarTraceFourier b hq)).mpr
    (by simpa only [smoothCollarTraceFourier_apply] using sourceAngularTrace_summable s b hq)).choose_spec
  change (smoothCollarTrace s b hq).val 0=smoothCollarTraceFourier b hq at he
  rw [he,smoothCollarTraceFourier_apply]

lemma smoothCollarTrace_rate_memℓp (s : Fin 3 → ℝ) (b : ℝ) {q : (Fin 3 → ℝ) → ℝ}
    (hq : ContDiff ℝ (↑(⊤:ℕ∞)) q) :
    Memℓp (fun h => (torusRate s h:ℂ)*(smoothCollarTrace s b hq).val 0 h) 2 := by
  apply (memℓp_gen_iff (by norm_num : 0<(2:ℝ≥0∞).toReal)).mpr
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two,norm_mul,mul_pow,
    Complex.norm_real,Real.norm_eq_abs,sq_abs,smoothCollarTrace_fst] using sourceAngularTrace_rate_sq_summable s b hq

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

lemma parentBand_central {y : Fin 3 → ℝ}
    (hy : y∈sourceClosedCollarBand centralThickness (2*centralThickness)) :
    sourcePairCoordinates y∈centralClosed := by
  rw [sourceClosedCollarBand_eq _ _ (by norm_num [centralThickness])
    (by norm_num [centralThickness])] at hy
  rcases mem_iUnion.mp hy with ⟨i, hi⟩
  rcases mem_iUnion.mp hi with ⟨j, hj⟩
  rcases hj with ⟨x, hx, rfl⟩
  exact sourceParentCollar_central i j hx

lemma parentBand_measurable : MeasurableSet (sourceClosedCollarBand centralThickness (2*centralThickness)) :=
  (isCompact_sourceClosedCollarBand (by norm_num [centralThickness]) (by norm_num [centralThickness])).measurableSet

def centralPhysicalWholeCLM : CentralL2 →L[ℝ] Lp ℝ 2 (volume : Measure (Fin 3 → ℝ)) :=
  (Lp.compMeasurePreservingₗᵢ ℝ sourcePairMeasurable sourcePair_volume).toContinuousLinearMap.comp
    (lpZeroExtensionCLM centralClosed_compact.measurableSet)

lemma centralPhysicalWholeCLM_smooth_ae (f : centralSmoothFunctions) (i : Fin 4) :
    centralPhysicalWholeCLM (centralSmoothJet f i)=ᵐ[volume]
      (fun y => centralPhysical.indicator (fun y => centralJetField f i (sourcePairCoordinates y)) y) := by
  have he := lpZeroExtensionCLM_ae_of_ae centralClosed_compact.measurableSet
    (centralSmoothJet f i) (centralSmoothJet_ae f i)
  have he' := sourcePair_volume.quasiMeasurePreserving.ae_eq_comp he
  apply (Lp.coeFn_compMeasurePreserving _ sourcePair_volume).trans
  apply he'.trans
  filter_upwards [] with y
  by_cases hy : sourcePairCoordinates y∈centralClosed <;> simp [centralPhysical,hy,sourcePairMeasurable_apply]

lemma central_parent_trace_eq (s : Fin 3 → ℝ) (f : centralSmoothFunctions) :
    smoothCollarTrace s centralThickness ((central_smooth f).comp sourcePairCLE.contDiff)=
      centralSmoothTrace s f 0 := by
  apply spectralTraceGraph_fst_injective (torusRate s)
  change (smoothCollarTrace s centralThickness ((central_smooth f).comp sourcePairCLE.contDiff)).val 0 =
    (centralSmoothTrace s f 0).val 0
  rw [centralSmoothTrace_fst]
  ext h
  rw [smoothCollarTrace_fst, centralTraceFourier_apply]
  rfl

lemma central_parent_partial (f : centralSmoothFunctions) (i : Fin 3) (y : Fin 3 → ℝ) :
    centralJetField f i.succ (sourcePairCoordinates y)=
      fderiv ℝ (fun y => f (sourcePairCoordinates y)) y (Pi.single i 1) := by
  rw [centralJetField_succ]
  have he := (((central_smooth f).differentiable (by simp) _).hasFDerivAt.comp y sourcePairCLE.hasFDerivAt).fderiv
  change fderiv ℝ f (sourcePairCLE y) (centralDirection i) =
    fderiv ℝ (f ∘ sourcePairCLE) y (Pi.single i 1)
  rw [he]
  have hi : sourcePairCLE.toContinuousLinearMap (Pi.single i 1)=centralDirection i := by
    fin_cases i <;> rfl
  exact congrArg (fderiv ℝ f (sourcePairCoordinates y)) hi |>.symm

lemma parentEndBand_measurable : MeasurableSet (sourceClosedCollarBand 0 centralThickness) :=
  (isCompact_sourceClosedCollarBand (by norm_num) (by norm_num [centralThickness])).measurableSet

lemma parentEndTime_mem {a : ℝ} (ha : a<0) (t : ℝ) (ht : t∈Icc 0 centralThickness) :
    affineEndTime a centralThickness t∈Icc 0 (-a*centralThickness) := by
  have hδ : 0 < centralThickness := by norm_num [centralThickness]
  dsimp [affineEndTime]
  constructor
  · exact mul_nonneg_of_nonpos_of_nonpos ha.le (sub_nonpos.mpr ht.2)
  · nlinarith [mul_nonpos_of_nonpos_of_nonneg ha.le ht.1]

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

lemma parent_band_indicator_join {a : ℝ} (ha : a<0) (y : Fin 3 → ℝ)
    (hy : y∈sourceClosedCollarBand 0 (2*centralThickness))
    (hne : sourceCollarTime y≠centralThickness) (q p : (Fin 3 → ℝ) → ℝ) :
    (sourceClosedCollarBand centralThickness (2*centralThickness)).indicator q y+
      (sourceClosedCollarBand 0 centralThickness).indicator p y=
        if 0<a*(sourceCollarTime y-centralThickness) then p y else q y := by
  rcases lt_or_gt_of_ne hne with ht | ht
  · have hp : 0<a*(sourceCollarTime y-centralThickness) :=
      mul_pos_of_neg_of_neg ha (sub_neg.mpr ht)
    have hc : y∉sourceClosedCollarBand centralThickness (2*centralThickness) := fun h => not_le_of_gt ht h.1
    have he : y∈sourceClosedCollarBand 0 centralThickness := ⟨hy.1,ht.le⟩
    simp [hc,he,hp]
  · have hp : ¬0<a*(sourceCollarTime y-centralThickness) :=
      not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg ha.le (sub_nonneg.mpr ht.le))
    have hc : y∈sourceClosedCollarBand centralThickness (2*centralThickness) := ⟨ht.le,hy.2⟩
    have he : y∉sourceClosedCollarBand 0 centralThickness := fun h => not_le_of_gt ht h.2
    simp [hc,he,hp]

end

open Set MeasureTheory Filter Topology

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

lemma childBand_central (k : Fin 2) {y : Fin 3 → ℝ}
    (hy : y∈sourceClosedCollarBand (-2*centralThickness) (-centralThickness)) :
    sourcePairCoordinates (sourceChildCoordinates (actualChildSign k) y)∈centralClosed := by
  rw [sourceClosedCollarBand_eq _ _ (by norm_num [centralThickness])
    (by norm_num [centralThickness])] at hy
  rcases mem_iUnion.mp hy with ⟨i,hi⟩
  rcases mem_iUnion.mp hi with ⟨j,hj⟩
  rcases hj with ⟨x,hx,rfl⟩
  exact sourceChildCollar_central i j (by fin_cases k <;> simp [actualChildSign]) hx

lemma childCentralBand_measurable :
    MeasurableSet (sourceClosedCollarBand (-2*centralThickness) (-centralThickness)) :=
  (isCompact_sourceClosedCollarBand (by norm_num [centralThickness]) (by norm_num [centralThickness])).measurableSet

lemma central_child_partial (k : Fin 2) (f : centralSmoothFunctions) (i : Fin 3) (y : Fin 3 → ℝ) :
    sourceScale*centralJetField f (childAxis i).succ
      (sourcePairCoordinates (sourceChildCoordinates (actualChildSign k) y))=
        fderiv ℝ (fun y => f (sourcePairCoordinates (sourceChildCoordinates (actualChildSign k) y))) y (Pi.single i 1) := by
  have he := (((central_smooth f).comp sourcePairCLE.contDiff).differentiable (by simp)
    (sourceChildCoordinates (actualChildSign k) y)).hasFDerivAt.comp y (sourceChildCoordinates_hasFDeriv (actualChildSign k) y)
  have hi : sourceChildDerivative (Pi.single i 1)=sourceScale • Pi.single (childAxis i) 1 := by
    rw [sourceChildDerivative_apply]
    fin_cases i <;> ext j <;> fin_cases j <;> norm_num [childAxis,Pi.single_apply,Fin.ext_iff]
  rw [central_parent_partial]
  change sourceScale*(fderiv ℝ (f ∘ sourcePairCLE) (sourceChildCoordinates (actualChildSign k) y)) (Pi.single (childAxis i) 1)=
    fderiv ℝ ((f ∘ sourcePairCLE) ∘ sourceChildCoordinates (actualChildSign k)) y (Pi.single i 1)
  rw [he.fderiv,ContinuousLinearMap.comp_apply,hi,map_smul,smul_eq_mul]

lemma central_child_trace_eq (s : Fin 3 → ℝ) (k : Fin 2) (f : centralSmoothFunctions) :
    smoothCollarTrace s (-centralThickness)
      (((central_smooth f).comp sourcePairCLE.contDiff).comp (sourceChildCoordinates_contDiff (actualChildSign k)))=
        centralSmoothTrace s f k.succ := by
  apply spectralTraceGraph_fst_injective (torusRate s)
  change (smoothCollarTrace s (-centralThickness)
    (((central_smooth f).comp sourcePairCLE.contDiff).comp (sourceChildCoordinates_contDiff (actualChildSign k)))).val 0 =
      (centralSmoothTrace s f k.succ).val 0
  rw [centralSmoothTrace_fst]
  ext h
  rw [smoothCollarTrace_fst,centralTraceFourier_apply]
  fin_cases k <;> rfl

lemma childEndBand_measurable : MeasurableSet (sourceClosedCollarBand (-centralThickness) 0) :=
  (isCompact_sourceClosedCollarBand (by norm_num [centralThickness]) (by norm_num [centralThickness])).measurableSet

lemma childEndTime_mem {a : ℝ} (ha : 0<a) (t : ℝ) (ht : t∈Icc (-centralThickness) 0) :
    affineEndTime a (-centralThickness) t∈Icc 0 (a*centralThickness) := by
  dsimp [affineEndTime]
  constructor
  · exact mul_nonneg ha.le (sub_nonneg.mpr ht.1)
  · nlinarith [mul_nonpos_of_nonneg_of_nonpos ha.le ht.2]

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

lemma sourceCollarTime_le_iff (y : Fin 3 → ℝ) (b : ℝ) :
    sourceCollarTime y ≤ b ↔
      1-b ≤ |y 2| ∨ sourceRadial y ≤ sourceHole+sourceRadialWidth*b ∨
        1-sourceRadialWidth*b ≤ sourceRadial y := by
  have hw : 0 < sourceRadialWidth := by norm_num [sourceRadialWidth,sourceHole]
  have hd : sourceRadialCenter-sourceRadialWidth=sourceHole := by
    norm_num [sourceRadialCenter,sourceRadialWidth,sourceHole]
  have hd' : sourceRadialCenter+sourceRadialWidth=1 := by
    norm_num [sourceRadialCenter,sourceRadialWidth,sourceHole]
  simp only [sourceCollarTime,sourceCrossCoordinates,Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [sub_le_iff_le_add,←sub_le_iff_le_add',le_max_iff,le_abs]
  constructor
  · rintro ((hr|hl)|hz)
    · exact Or.inr (Or.inr (by have h := (le_div_iff₀ hw).mp hr; nlinarith))
    · exact Or.inr (Or.inl (by have h := (div_le_iff₀ hw).mp (show (sourceRadial y-sourceRadialCenter)/sourceRadialWidth ≤  -(1-b) by linarith); nlinarith))
    · exact Or.inl hz
  · rintro (hz|hl|hr)
    · exact Or.inr hz
    · exact Or.inl (Or.inr (by have h : (sourceRadial y-sourceRadialCenter)/sourceRadialWidth ≤  -(1-b) := (div_le_iff₀ hw).mpr (by nlinarith); linarith))
    · exact Or.inl (Or.inl ((le_div_iff₀ hw).mpr (by nlinarith)))

lemma centralChild_time_iff (σ : ℝ) (y : Fin 3 → ℝ) :
    sourceCollarTime ((sourceChildHomeomorph σ).symm y) ≤  -centralThickness ↔
      centralChildHeight ≤ |y 2| ∨ centralAvoidChild σ (sourcePairCoordinates y).1 := by
  change sourceCollarTime ![y 1/sourceScale,(y 0-σ*sourceOffset)/sourceScale,y 2/sourceScale] ≤ -centralThickness ↔ _
  rw [sourceCollarTime_le_iff]
  have hs : 0 < sourceScale := by norm_num [sourceScale]
  have hL : 0 < sourceLength := by norm_num [sourceLength]
  simp only [sourceRadial,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,
    abs_div,abs_of_pos hs,max_le_iff,le_max_iff,centralAvoidChild,sourcePairCoordinates,
    centralChildHeight,centralChildOuterX,centralChildOuterY,centralChildInnerX,centralChildInnerY,
    div_le_iff₀ hs,le_div_iff₀ hs,div_le_iff₀ hL,le_div_iff₀ hL]
  constructor
  · rintro (hz|⟨hy,hx⟩|hy|hx)
    · left; nlinarith
    · right; right; right; constructor <;> nlinarith
    · right; right; left; nlinarith
    · right; left; nlinarith
  · rintro (hz|hx|hy|⟨hx,hy⟩)
    · left; nlinarith
    · right; right; right; nlinarith
    · right; right; left; nlinarith
    · right; left; constructor <;> nlinarith

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

def centralJoinOpen (i : Fin 4) : Set (Fin 3 → ℝ) :=
  ![interior centralPhysical,
    sourceCollarTime ⁻¹' Ioo 0 (2*centralThickness),
    (fun y => sourceCollarTime ((sourceChildHomeomorph 1).symm y)) ⁻¹' Ioo (-2*centralThickness) 0,
    (fun y => sourceCollarTime ((sourceChildHomeomorph (-1)).symm y)) ⁻¹' Ioo (-2*centralThickness) 0] i

lemma centralJoinOpen_isOpen (i : Fin 4) : IsOpen (centralJoinOpen i) := by
  have ht := locallyLipschitz_sourceCollarTime.continuous
  fin_cases i
  · exact isOpen_interior
  · exact isOpen_Ioo.preimage ht
  · exact isOpen_Ioo.preimage (ht.comp (sourceChildHomeomorph 1).symm.continuous)
  · exact isOpen_Ioo.preimage (ht.comp (sourceChildHomeomorph (-1)).symm.continuous)

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

lemma child_band_indicator_join {a : ℝ} (ha : 0<a) (y : Fin 3 → ℝ)
    (hy : y∈sourceClosedCollarBand (-2*centralThickness) 0)
    (hne : sourceCollarTime y≠-centralThickness) (q p : (Fin 3 → ℝ) → ℝ) :
    (sourceClosedCollarBand (-2*centralThickness) (-centralThickness)).indicator q y+
      (sourceClosedCollarBand (-centralThickness) 0).indicator p y=
        if 0<a*(sourceCollarTime y-(-centralThickness)) then p y else q y := by
  rcases lt_or_gt_of_ne hne with ht | ht
  · have hp : ¬0<a*(sourceCollarTime y-(-centralThickness)) :=
      not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos ha.le (sub_nonpos.mpr ht.le))
    have hc : y∈sourceClosedCollarBand (-2*centralThickness) (-centralThickness) := ⟨hy.1,ht.le⟩
    have he : y∉sourceClosedCollarBand (-centralThickness) 0 := fun h => not_le_of_gt ht h.1
    simp only [indicator_of_mem hc,indicator_of_notMem he,add_zero,ite_eq_right hp]
  · have hp : 0<a*(sourceCollarTime y-(-centralThickness)) := mul_pos ha (sub_pos.mpr ht)
    have hc : y∉sourceClosedCollarBand (-2*centralThickness) (-centralThickness) := fun h => not_le_of_gt ht h.2
    have he : y∈sourceClosedCollarBand (-centralThickness) 0 := ⟨ht.le,hy.2⟩
    simp only [indicator_of_notMem hc,indicator_of_mem he,zero_add,ite_eq_left hp]

end

open Set MeasureTheory Filter Topology

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_ChildTransportFormula
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma sourceChildDerivative_single (i : Fin 3) :
    sourceChildDerivative (Pi.single i 1)=sourceScale • Pi.single (childAxis i) 1 := by
  rw [sourceChildDerivative_apply]
  fin_cases i <;> ext j <;> fin_cases j <;> norm_num [childAxis,Pi.single_apply,Fin.ext_iff]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_CentralJetIdentity
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
  {a : Fin 3 → ℝ} (ha₀ : a 0<0) (ha : ∀ k : Fin 2,0<a k.succ)

def centralBallSet : Set R3 := WithLp.ofLp ⁻¹' centralPhysical

end

open Set MeasureTheory Filter Topology

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

lemma cubePartial_add {f g : Box3 → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (v p : Box3) : cubePartial (fun x => f x+g x) v p=cubePartial f v p+cubePartial g v p := by
  simp only [cubePartial,fderiv_fun_add (hf p) (hg p),add_apply]

lemma cubePartial_sub {f g : Box3 → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (v p : Box3) : cubePartial (fun x => f x-g x) v p=cubePartial f v p-cubePartial g v p := by
  simp only [cubePartial,fderiv_fun_sub (hf p) (hg p),sub_apply]

lemma cubePartial_commute {f : Box3 → ℝ} (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (v w p : Box3) :
    cubePartial (cubePartial f v) w p=cubePartial (cubePartial f w) v p := by
  have hf2 : ContDiff ℝ 2 f := hf.of_le (show ((2 : ℕ∞) : WithTop ℕ∞)≤↑(⊤ : ℕ∞) from WithTop.coe_le_coe.mpr le_top)
  have hd : DifferentiableAt ℝ (fderiv ℝ f) p :=
    (hf2.fderiv_right (show (1 : WithTop ℕ∞)+1≤2 by norm_num)).contDiffAt.differentiableAt (by norm_num)
  unfold cubePartial
  rw [fderiv_clm_apply hd (differentiableAt_const _),fderiv_clm_apply hd (differentiableAt_const _)]
  simpa using hf2.contDiffAt.isSymmSndFDerivAt (by simp) w v

lemma cubePartial_fst_fst (v p : Box3) : cubePartial (fun x => x.1.1) v p=v.1.1 := by
  have hh : HasFDerivAt (fun x : Box3 => x.1.1)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ×ℝ) ℝ)) p :=
    hasFDerivAt_fst.comp p hasFDerivAt_fst
  rw [cubePartial,hh.fderiv]; rfl

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

lemma cube_fderiv_expansion (f : Box3 → ℝ) (p w : Box3) :
    fderiv ℝ f p w=cubePartial f ((1,0),0) p*w.1.1+
      cubePartial f ((0,1),0) p*w.1.2+cubePartial f ((0,0),1) p*w.2 := by
  have hw : w=w.1.1 • ((1,0),0)+w.1.2 • ((0,1),0)+w.2 • ((0,0),1) := by
    ext <;> simp
  calc
    _ = fderiv ℝ f p (w.1.1 • ((1,0),0)+w.1.2 • ((0,1),0)+w.2 • ((0,0),1)) := congrArg _ hw
    _ = _ := by simp only [map_add,map_smul,smul_eq_mul,cubePartial]; ring

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_PhysicalBoxCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

lemma coordinatePair_smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) coordinatePair :=
  coordinatePairCLM.contDiff

lemma coordinatePair_columns (B : Mat3) (x : Coord3) (j : Fin 2) :
    (B*gradientColumns (fderiv ℝ coordinatePair x)).col j=(B.col (j.castLE (by decide : 2≤3))) := by
  have hd : fderiv ℝ coordinatePair x=coordinatePairCLM := coordinatePairCLM.hasFDerivAt.fderiv
  rw [hd]
  ext i
  fin_cases j
  all_goals simp [Matrix.mul_apply,gradientColumns,LinearMap.toMatrix',
    coordinatePairCLM,Matrix.transpose_apply,Matrix.col,Pi.single_apply]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_LocalPhysicalCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise

lemma localPiolaSource_tsupport_image
    (X : OpenPartialHomeomorph Coord3 Coord3) (r : Coord3 → ℝ)
    (hc : HasCompactSupport r) (hs : tsupport r⊆X.source) :
    tsupport (localPiolaSource X r)⊆X '' tsupport r := by
  exact closure_minimal ((localPiolaSource_support X r).trans
    (image_mono (fun _ hx => subset_closure hx.1)))
    (hc.image_of_continuousOn (X.continuousOn.mono hs)).isClosed

lemma localPiolaSource_inverse
    (X : OpenPartialHomeomorph Coord3 Coord3)
    (hX : DifferentiableOn ℝ X X.source) (hXi : DifferentiableOn ℝ X.symm X.target)
    (r : Coord3 → ℝ) (hs : Function.support r⊆X.target) :
    localPiolaSource X (localPiolaSource X.symm r)=r := by
  funext y
  by_cases hy : y∈X.target
  · have he := congrArg (fun D : Coord3 →L[ℝ] Coord3 => D.det)
      (local_fderiv_symm_comp X.symm hXi hX hy)
    simp only [OpenPartialHomeomorph.symm_symm,ContinuousLinearMap.det,
      ContinuousLinearMap.toLinearMap_comp,ContinuousLinearMap.coe_id,
      LinearMap.det_comp,LinearMap.det_id] at he
    have habs : |(fderiv ℝ X (X.symm y)).det| * |(fderiv ℝ X.symm y).det|=1 := by
      rw [←abs_mul]
      exact congrArg abs he |>.trans abs_one
    classical
    change (if y∈X.target then |(fderiv ℝ X (X.symm y)).det|⁻¹ *
      (if X.symm y∈X.source then |(fderiv ℝ X.symm (X (X.symm y))).det|⁻¹ *
        r (X (X.symm y)) else 0) else 0) = r y
    rw [ite_eq_left hy,ite_eq_left (X.map_target hy),X.right_inv hy]
    rw [←mul_assoc,←mul_inv,habs,inv_one,one_mul]
  · rw [localPiolaSource,ite_eq_right hy,Function.notMem_support.mp (fun h => hy (hs h))]

lemma localPiolaSource_inverse_support
    (X : OpenPartialHomeomorph Coord3 Coord3) (r : Coord3 → ℝ)
    (hc : HasCompactSupport r) {V : Set Coord3} (hV : V⊆X.source)
    (hs : tsupport r⊆X '' V) :
    tsupport (localPiolaSource X.symm r)⊆V := by
  have ht : tsupport r⊆X.target := hs.trans (by rintro y ⟨x,hx,rfl⟩; exact X.map_source (hV hx))
  intro x hx
  obtain ⟨y,hy,rfl⟩ := localPiolaSource_tsupport_image X.symm r hc ht hx
  obtain ⟨z,hz,rfl⟩ := hs hy
  simpa only [X.left_inv (hV hz)] using hz

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_CompactFluxDivergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma coordinateDivergence_compact {F : Coord3 → Coord3}
    (hs : HasCompactSupport F) : HasCompactSupport (coordinateDivergence F) := by
  have hc (i : Fin 3) : HasCompactSupport (fun x => fderiv ℝ (fun y => F y i) x (Pi.single i 1)) := by
    have hci : HasCompactSupport (fun x => F x i) := hs.comp_left (g := fun v : Coord3 => v i) rfl
    exact hci.fderiv_apply ℝ _
  have he : coordinateDivergence F = fun x =>
      (fderiv ℝ (fun y => F y 0) x (Pi.single 0 1)+
       fderiv ℝ (fun y => F y 1) x (Pi.single 1 1))+
       fderiv ℝ (fun y => F y 2) x (Pi.single 2 1) := by
    funext x
    simp [coordinateDivergence,Fin.sum_univ_three]
  rw [he]
  exact ((hc 0).add (hc 1)).add (hc 2)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_CompactSymmetricMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma potential_component_fderiv {u : Coord3 → Fin 2 → ℝ}
    (hu : Differentiable ℝ u) (j : Fin 2) (x v : Coord3) :
    fderiv ℝ (fun y => u y j) x v=fderiv ℝ u x v j := by
  rw [(hasFDerivAt_pi'.mp (hu x).hasFDerivAt j).fderiv]
  rfl

lemma symmetric_potential_pairing (D : Coord3 →L[ℝ] (Fin 2 → ℝ))
    (B : Mat3) (hB : B.IsSymm) :
    D ((B*gradientColumns D).col 0) 1=D ((B*gradientColumns D).col 1) 0 := by
  rw [gradientColumns_pairing,gradientColumns_pairing]
  have hs : ((gradientColumns D)ᵀ*(B*gradientColumns D)).IsSymm := by
    unfold Matrix.IsSymm
    rw [transpose_mul,transpose_mul,transpose_transpose,hB]
    exact Matrix.mul_assoc _ _ _
  exact congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) hs

theorem compact_symmetric_source_moments
    (u : Coord3 → Fin 2 → ℝ) (hu : ContDiff ℝ (↑(⊤ : ℕ∞)) u)
    (H : Coord3 → Mat3) (hH : ∀ x,(H x).IsSymm)
    (r : Fin 2 → Coord3 → ℝ)
    (hr : ∀ j,ContDiff ℝ (↑(⊤ : ℕ∞)) (r j))
    (hsr : ∀ j,HasCompactSupport (r j))
    (hw : ∀ j (ψ : Coord3 → ℝ),ContDiff ℝ (↑(⊤ : ℕ∞)) ψ →
      (∫ x,fderiv ℝ ψ x ((H x*gradientColumns (fderiv ℝ u x)).col j))=
        -(∫ x,ψ x*r j x)) :
    (∫ x,r 0 x)=0 ∧ (∫ x,r 1 x)=0 ∧
      (∫ x,u x 1*r 0 x-u x 0*r 1 x)=0 := by
  have hz (j : Fin 2) : (∫ x,r j x)=0 := by
    have hh := hw j (fun _ => 1) contDiff_const
    simpa using hh
  have huj (j : Fin 2) : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => u x j) :=
    (contDiff_pi.mp hu) j
  have he : (∫ x,u x 1*r 0 x)=(∫ x,u x 0*r 1 x) := by
    have hw₁ := hw 0 (fun x => u x 1) (huj 1)
    have hw₂ := hw 1 (fun x => u x 0) (huj 0)
    have hp : (fun x => fderiv ℝ (fun y => u y 1) x ((H x*gradientColumns (fderiv ℝ u x)).col 0))=
        (fun x => fderiv ℝ (fun y => u y 0) x ((H x*gradientColumns (fderiv ℝ u x)).col 1)) := by
      funext x
      rw [potential_component_fderiv (hu.differentiable (by simp)),
        potential_component_fderiv (hu.differentiable (by simp))]
      exact symmetric_potential_pairing _ _ (hH x)
    rw [hp] at hw₁
    linarith
  refine ⟨hz 0,hz 1,?_⟩
  have hi₁ : Integrable (fun x => u x 1*r 0 x) :=
    ((huj 1).continuous.mul (hr 0).continuous).integrable_of_hasCompactSupport (hsr 0).mul_left
  have hi₂ : Integrable (fun x => u x 0*r 1 x) :=
    ((huj 0).continuous.mul (hr 1).continuous).integrable_of_hasCompactSupport (hsr 1).mul_left
  rw [integral_sub hi₁ hi₂,he,sub_self]

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

omit [FiniteDimensional ℝ P] in
lemma fiberSlice_smooth
    (Y : OpenPartialHomeomorph (P×Coord3) (P×Coord3))
    (hY : ∀ p x,(Y (p,x)).1=p)
    (hsm : ContDiff ℝ (↑(⊤:ℕ∞)) Y)
    (hinv : ContDiffOn ℝ (↑(⊤:ℕ∞)) Y.symm Y.target) (p : P) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (fiberSlice Y hY p) ∧
    ContDiffOn ℝ (↑(⊤:ℕ∞)) (fiberSlice Y hY p).symm (fiberSlice Y hY p).target := by
  constructor
  · exact contDiff_snd.comp (hsm.comp (contDiff_const.prodMk contDiff_id))
  · exact contDiff_snd.contDiffOn.comp
      (hinv.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ hx => hx))
      (fun _ _ => mem_univ _)

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

def inverseSourceWeight (X : OpenPartialHomeomorph Coord3 Coord3) (x : Coord3) : ℝ :=
  |(fderiv ℝ X.symm (X x)).det|⁻¹

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
open Set Filter Topology

variable {P E F : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma spatialFDeriv_smooth {f : P×E → F} (hf : ContDiff ℝ (↑(⊤:ℕ∞)) f) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (spatialFDeriv f) := by
  rw [←contDiffOn_univ]
  exact spatialFDeriv_smoothOn isOpen_univ hf.contDiffOn

end ScalarConductivity



namespace ScalarConductivity
open Set Filter Topology Matrix
open scoped Matrix.Norms.Elementwise

lemma inverseSourceWeight_eq_det
    (X : OpenPartialHomeomorph Coord3 Coord3)
    (hX : DifferentiableOn ℝ X X.source) (hXi : DifferentiableOn ℝ X.symm X.target)
    {x : Coord3} (hx : x∈X.source) : inverseSourceWeight X x=|(fderiv ℝ X x).det| := by
  have he := congrArg (fun L : Coord3 →L[ℝ] Coord3 => L.det)
    (local_fderiv_symm_comp X hX hXi hx)
  simp only [ContinuousLinearMap.det,ContinuousLinearMap.toLinearMap_comp,
    ContinuousLinearMap.coe_id,LinearMap.det_comp,LinearMap.det_id] at he
  apply inv_eq_of_mul_eq_one_right
  rw [←abs_mul]
  simpa only [abs_one,ContinuousLinearMap.det] using congrArg abs he

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

omit [FiniteDimensional ℝ P] in
theorem parametric_inverseSourceWeight_smooth
    (Y : OpenPartialHomeomorph (P×Coord3) (P×Coord3))
    (hY : ∀ p x,(Y (p,x)).1=p)
    (hsm : ContDiff ℝ (↑(⊤:ℕ∞)) Y)
    (hinv : ContDiffOn ℝ (↑(⊤:ℕ∞)) Y.symm Y.target) :
    ContDiffOn ℝ (↑(⊤:ℕ∞))
      (fun q : P×Coord3 => inverseSourceWeight (fiberSlice Y hY q.1).symm q.2) Y.target := by
  let f : P×Coord3 → Coord3 := fun q => (Y.symm q).2
  have hf : ContDiffOn ℝ (↑(⊤:ℕ∞)) f Y.target :=
    contDiff_snd.contDiffOn.comp hinv (fun _ _ => mem_univ _)
  have hd := spatialFDeriv_smoothOn Y.open_target hf
  have heq (q : P×Coord3) (hq : q∈Y.target) :
      inverseSourceWeight (fiberSlice Y hY q.1).symm q.2=|(spatialFDeriv f q).det| := by
    obtain ⟨hs,hi⟩ := fiberSlice_smooth Y hY hsm hinv q.1
    exact inverseSourceWeight_eq_det _ (hi.differentiableOn (by simp))
      (hs.differentiable (by simp)).differentiableOn hq
  apply Y.open_target.contDiffOn_iff.mpr
  intro q hq
  have hne : (spatialFDeriv f q).det≠0 := by
    obtain ⟨hs,hi⟩ := fiberSlice_smooth Y hY hsm hinv q.1
    exact local_fderiv_det_ne_zero (fiberSlice Y hY q.1).symm
      (hi.differentiableOn (by simp)) (hs.differentiable (by simp)).differentiableOn hq
  have hc := ((contDiff_clm_det (E := Coord3) (↑(⊤:ℕ∞))).contDiffAt.comp q
    (hd.contDiffAt (Y.open_target.mem_nhds hq))).abs hne
  apply hc.congr_of_eventuallyEq
  filter_upwards [Y.open_target.mem_nhds hq] with z hz
  exact heq z hz

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

lemma smooth_wall_cutoff_ratio {χ f g : Box3 → ℝ}
    (hχ : ContDiff ℝ (↑(⊤ : ℕ∞)) χ) (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g)
    (hne : ∀ p∈tsupport χ,wallQuotient g p≠0) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun p => χ p*(wallQuotient f p/wallQuotient g p)) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : p∈tsupport χ
  · exact hχ.contDiffAt.mul ((wallQuotient_smooth hf).contDiffAt.div
      (wallQuotient_smooth hg).contDiffAt (hne p hp))
  · apply (show ContDiffAt ℝ (↑(⊤ : ℕ∞)) (fun _ : Box3 => (0:ℝ)) p from contDiffAt_const).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hp] with q hq
    change χ q=0 at hq
    simp only [hq,zero_mul]

end ScalarConductivity

end


end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_ParametricSymmetricSources
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

lemma coordinateDivergence_parametric_smoothOn {f : P×Coord3 → Coord3}
    {V : Set (P×Coord3)} (hV : IsOpen V) (hf : ContDiffOn ℝ (↑(⊤:ℕ∞)) f V) :
    ContDiffOn ℝ (↑(⊤:ℕ∞)) (fun q => coordinateDivergence (fun x => f (q.1,x)) q.2) V := by
  apply ContDiffOn.sum
  intro i _
  exact (spatialFDeriv_smoothOn hV (contDiffOn_pi.mp hf i)).clm_apply contDiffOn_const

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
open Set MeasureTheory Matrix Filter Topology

def wallActualMoment (v : Box3 → ℝ) (q : ℝ×ℝ) : Fin 3 → ℝ :=
  ![1,wallAlong (1,0) v (q,0),v (q,0)-q.1*wallAlong (1,0) v (q,0)]

lemma wallActualMoment_limit {v : Box3 → ℝ} {σ lam : ℝ}
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v)
    (he : ∀ q : ℝ×ℝ,v (q,0)=σ*Real.exp (-lam*q.1)) (q : ℝ×ℝ) :
    wallActualMoment v q=wallMomentBasis σ lam q.1 := by
  have hs : wallAlong (1,0) v (q,0)= -σ*lam*Real.exp (-lam*q.1) := by
    have hpath : HasDerivAt (fun s : ℝ => ((s,q.2),(0:ℝ))) ((1,0),0) q.1 :=
      ((hasDerivAt_id q.1).prodMk (hasDerivAt_const q.1 q.2)).prodMk (hasDerivAt_const q.1 0)
    have hd := ((hv.differentiable (by simp) (q,0)).hasFDerivAt.comp_hasDerivAt q.1 hpath)
    have hd' : HasDerivAt (fun s : ℝ => σ*Real.exp (-lam*s))
        (-σ*lam*Real.exp (-lam*q.1)) q.1 := by
      convert! (((hasDerivAt_id q.1).const_mul (-lam)).exp.const_mul σ) using 1
      all_goals try with_reducible_and_instances rfl
      first | rfl | (simp only [id_eq]; ring)
    have heq : (fun s : ℝ => v ((s,q.2),0))=(fun s => σ*Real.exp (-lam*s)) := funext (fun s => he (s,q.2))
    change HasDerivAt (fun s : ℝ => v ((s,q.2),0)) (wallAlong (1,0) v (q,0)) q.1 at hd
    rw [heq] at hd
    exact hd.unique hd'
  ext i
  fin_cases i
  · rfl
  · exact hs
  · change v (q,0)-q.1*wallAlong (1,0) v (q,0)=σ*(1+lam*q.1)*Real.exp (-lam*q.1)
    rw [he,hs]
    ring

variable {P : Type*} [TopologicalSpace P] [FirstCountableTopology P] [LocallyCompactSpace P]

omit [FirstCountableTopology P] [LocallyCompactSpace P] in
lemma wallActualMoment_joint_continuous {v : P → Box3 → ℝ}
    (hv : Continuous (fun pq : P × Box3 => v pq.1 pq.2))
    (hvs : Continuous (fun pq : P × Box3 => wallAlong (1,0) (v pq.1) pq.2)) (i : Fin 3) :
    Continuous (fun pq : P × (ℝ×ℝ) => wallActualMoment (v pq.1) pq.2 i) := by
  have hmap : Continuous (fun pq : P × (ℝ×ℝ) => (pq.1,(pq.2,(0:ℝ)))) :=
    continuous_fst.prodMk (continuous_snd.prodMk continuous_const)
  fin_cases i
  · exact continuous_const
  · exact hvs.comp hmap
  · exact (hv.comp hmap).sub (continuous_snd.fst.mul (hvs.comp hmap))

theorem actual_wall_moment_uniform_inverse {l r a b σ lam : ℝ}
    (hlr : l < r) (hab : a<b) (hσ : σ≠0) (hlam : lam≠0)
    {v : P → Box3 → ℝ} {p₀ : P}
    (hv₀ : ContDiff ℝ (↑(⊤ : ℕ∞)) (v p₀))
    (hv : Continuous (fun pq : P × Box3 => v pq.1 pq.2))
    (hvs : Continuous (fun pq : P × Box3 => wallAlong (1,0) (v pq.1) pq.2))
    (hlim : ∀ q : ℝ×ℝ,v p₀ (q,0)=σ*Real.exp (-lam*q.1)) :
    ∃ χ η : ℝ → ℝ,
      ContDiff ℝ (↑(⊤ : ℕ∞)) χ ∧ ContDiff ℝ (↑(⊤ : ℕ∞)) η ∧
      HasCompactSupport χ ∧ HasCompactSupport η ∧
      tsupport χ⊆Icc l r ∧ tsupport η⊆Ioo a b ∧
      ∃ C : ℝ,0<C ∧ ∀ᶠ p in 𝓝 p₀,∀ m : Fin 3 → ℝ,
        ∃ c : Fin 3 → ℝ,(∀ i,‖c i‖≤C*‖m‖) ∧
          let f := fun q : ℝ×ℝ => (χ q.1*(c ⬝ᵥ wallMomentBasis σ lam q.1))*η q.2
          ContDiff ℝ (↑(⊤ : ℕ∞)) f ∧ HasCompactSupport f ∧
          tsupport f⊆Icc l r ×ˢ Ioo a b ∧
          (∀ i,(∫ q,f q*wallActualMoment (v p) q i)=m i) := by
  exact wall_surface_moment_uniform_inverse hlr hab hσ hlam
    (wallActualMoment_joint_continuous hv hvs) (wallActualMoment_limit hv₀ hlim)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Walls_WallMomentAmplitudeBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix Filter Topology

def wallMomentAmplitude (χ η : ℝ → ℝ) (σ lam : ℝ) (c : Fin 3 → ℝ) (q : ℝ×ℝ) : ℝ :=
  (χ q.1*(c ⬝ᵥ wallMomentBasis σ lam q.1))*η q.2

def wallMomentTest (χ η : ℝ → ℝ) (σ lam : ℝ) (i : Fin 3) (q : ℝ×ℝ) : ℝ :=
  (χ q.1*wallMomentBasis σ lam q.1 i)*η q.2

lemma wallMomentTest_smooth {χ η : ℝ → ℝ} (σ lam : ℝ)
    (hχ : ContDiff ℝ (↑(⊤ : ℕ∞)) χ) (hη : ContDiff ℝ (↑(⊤ : ℕ∞)) η) (i : Fin 3) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (wallMomentTest χ η σ lam i) :=
  ((hχ.mul (wallMomentBasis_smooth σ lam i)).comp contDiff_fst).mul (hη.comp contDiff_snd)

lemma wallMomentAmplitude_sum (χ η : ℝ → ℝ) (σ lam : ℝ) (c : Fin 3 → ℝ) :
    wallMomentAmplitude χ η σ lam c=(fun q => ∑ i,c i • wallMomentTest χ η σ lam i q) := by
  funext q
  simp only [wallMomentAmplitude,dotProduct,Finset.mul_sum,Finset.sum_mul,wallMomentTest,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

end ScalarConductivity



end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Walls_CriticalWallBounds
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

lemma wallHomogeneousNumerator_derivative {v : Box3 → ℝ} {a : (ℝ×ℝ) → ℝ}
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v) (ha : ContDiff ℝ (↑(⊤ : ℕ∞)) a) (p : Box3) :
    wallDerivative (wallHomogeneousNumerator (1,0) v a) p=
      -2*a p.1*wallAlong (1,0) (wallDerivative v) p-
       wallAlong (1,0) (fun q : Box3 => a q.1) p*wallDerivative v p := by
  have hA : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun q : Box3 => a q.1) := ha.comp contDiff_fst
  have hG := wallHomogeneousNumerator_smooth (1,0) hv ha
  have hh := (wall_homogeneous_flux_equations (1,0) hv ha p).2
  rw [wallAlong_mul (1,0) (hA.differentiable (by simp))
      ((wallDerivative_smooth hv).differentiable (by simp)),
    wallDerivative_add ((hA.mul (wallAlong_smooth (1,0) hv)).differentiable (by simp))
      (hG.differentiable (by simp)),
    wallDerivative_mul (hA.differentiable (by simp))
      ((wallAlong_smooth (1,0) hv).differentiable (by simp)),
    wallDerivative_pullback (ha.differentiable (by simp)),wall_mixed_commute (1,0) hv] at hh
  linarith

lemma wallAlong_pullback_box {a : (ℝ×ℝ) → ℝ} (ha : Differentiable ℝ a) (d : ℝ×ℝ) (p : Box3) :
    wallAlong d (fun q : Box3 => a q.1) p=fderiv ℝ a p.1 d := by
  change fderiv ℝ (a∘Prod.fst) p (d,0)=_
  rw [fderiv_comp p (ha p.1) differentiableAt_fst,fderiv_fst]
  rfl

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

lemma coordinateDivergence_tsupport (F : Coord3 → Coord3) :
    tsupport (coordinateDivergence F)⊆tsupport F := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro x hx
  by_contra hn
  have he : F =ᶠ[𝓝 x] (fun _ => 0) := notMem_tsupport_iff_eventuallyEq.mp hn
  apply hx
  unfold coordinateDivergence
  apply Finset.sum_eq_zero
  intro i _
  have hei : (fun y => F y i) =ᶠ[𝓝 x] (fun _ => 0) := he.mono (fun y hy => congrFun hy i)
  rw [hei.fderiv_eq]
  simp

lemma symmetricSource_tsupport (H : Coord3 → Mat3) (u : Coord3 → Fin 2 → ℝ) (j : Fin 2) :
    tsupport (symmetricSource H u j)⊆tsupport H :=
  (coordinateDivergence_tsupport _).trans (tensorColumn_tsupport H _ j)

lemma wallHomogeneousQuotient_zero_off_surface {v : Box3 → ℝ} {a : (ℝ×ℝ) → ℝ}
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v) (ha : ContDiff ℝ (↑(⊤ : ℕ∞)) a)
    {p : Box3} (hp : p.1∉tsupport a) :
    wallQuotient (wallHomogeneousNumerator (1,0) v a) p=0 := by
  unfold wallQuotient
  have haz : a p.1=0 := image_eq_zero_of_notMem_tsupport hp
  have had : fderiv ℝ a p.1=0 := fderiv_of_notMem_tsupport ℝ hp
  have hz (t : ℝ) : wallDerivative (wallHomogeneousNumerator (1,0) v a) (p.1,t*p.2)=0 := by
    rw [wallHomogeneousNumerator_derivative hv ha,wallAlong_pullback_box (ha.differentiable (by simp))]
    simp only [haz,had,_root_.zero_apply,mul_zero,zero_mul,sub_zero]
  simp only [hz,integral_zero]

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

omit [ProperSpace P] [ProperSpace E] in
lemma wallDerivative_parametric_smooth {f : P×(E×ℝ) → ℝ}
    (hf : ContDiff ℝ (↑(⊤:ℕ∞)) f) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (fun q : P×(E×ℝ) => wallDerivative (fun x => f (q.1,x)) q.2) :=
  (spatialFDeriv_smooth hf).clm_apply contDiff_const

omit [ProperSpace P] [ProperSpace E] in
lemma wallAlong_parametric_smooth (d : E) {f : P×(E×ℝ) → ℝ}
    (hf : ContDiff ℝ (↑(⊤:ℕ∞)) f) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (fun q : P×(E×ℝ) => wallAlong d (fun x => f (q.1,x)) q.2) :=
  (spatialFDeriv_smooth hf).clm_apply contDiff_const

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_AngularPeriodization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def angularPeriodize (T : ℝ) (f : Coord3 → E) (x : Coord3) : E :=
  ∑ᶠ n : Fin 2 → ℤ,f (x+angularShift T n)

end ScalarConductivity



end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_ConjugateDiagonal
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
open Matrix Set Filter Topology
open scoped Matrix.Norms.Elementwise

def conjugateDiagonal (Q : Mat3) (α : DiagonalTriple) : Symmetric3 :=
  ⟨Q * Matrix.diagonal α * Qᵀ, by
    rw [Matrix.isHermitian_iff_isSymm]
    unfold Matrix.IsSymm
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.diagonal_transpose, Matrix.mul_assoc]⟩

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_AxialPairRank
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

def axialPair (f : Coord3 → ℝ) (x : Coord3) : Fin 2 → ℝ := ![x 0,f x]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_CascadeRankPieces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

def cascadeSymmetricTensor (L K k : ℝ) (x : Coord3) : Symmetric3 :=
  ⟨cascadeTensor L K k x,cascadeTensor_symm L K k x⟩

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
open Real Set Filter Topology MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

def alignedEndingSymmetricTensor (lam k J L K : ℝ) (x : Coord3) : Symmetric3 :=
  ⟨alignedEndingTensor lam k J L K x,alignedEndingTensor_symm lam k J L K x⟩

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

lemma sourceChildEuclidean_contDiff (σ : ℝ) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (sourceChildEuclidean σ : R3 → R3) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.contDiff.comp
    ((sourceChildCoordinates_contDiff σ).comp (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).contDiff)

lemma sourceChildEuclidean_gradient (σ : ℝ) {f : R3 → ℝ}
    (hf : ContDiff ℝ (↑(⊤:ℕ∞)) f) (x : R3) (i : Fin 3) :
    gradient (f ∘ sourceChildEuclidean σ) x i=
      sourceScale*gradient f (sourceChildEuclidean σ x) (childAxis i) := by
  let E : R3 ≃L[ℝ] Coord3 := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)
  have hD := E.symm.hasFDerivAt.comp (E x) (sourceChildCoordinates_hasFDeriv σ (E x))
  have hC := (hf.differentiable (by simp) (sourceChildEuclidean σ x)).hasFDerivAt.comp x
    (hD.comp x E.hasFDerivAt)
  have hi : E.toContinuousLinearMap (EuclideanSpace.single i 1)=Pi.single i 1 := rfl
  have hj : E.symm.toContinuousLinearMap (Pi.single (childAxis i) 1)=EuclideanSpace.single (childAxis i) 1 := rfl
  rw [gradient_apply_single,gradient_apply_single]
  rw [hC.fderiv,ContinuousLinearMap.comp_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply,hi,sourceChildDerivative_single,map_smul,hj,map_smul,smul_eq_mul]

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_ChildJetScaling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology
attribute [local instance] Classical.propDecidable

def childAxisSwap (v : R3) : R3 := WithLp.toLp 2 (fun i => v (childAxis i))

end ScalarConductivity



end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_LinearTensorEllipticity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma RegularPatch.tensor_smul {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    {O : Set Coord3} (h : RegularPatch u A O) (r : ℝ) :
    RegularPatch u (fun x => ⟨r • (A x).val,by
      change (r • (A x).val)ᵀ=r • (A x).val
      rw [Matrix.transpose_smul]
      exact congrArg (r • ·) (show (A x).valᵀ=(A x).val from (A x).property)⟩) O := by
  refine ⟨h.1,h.2.1,?_,h.2.2.2⟩
  change ContDiffOn ℝ (↑(⊤ : ℕ∞)) (fun x => r • (A x).val) O
  exact (contDiffOn_const : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (fun _ : Coord3 => r) O).smul h.2.2.1

lemma mem_regularRegion_tensor_smul {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    {U : Set Coord3} {x : Coord3} (h : x∈regularRegion u A U) (r : ℝ) :
    x∈regularRegion u (fun y => ⟨r • (A y).val,by
      change (r • (A y).val)ᵀ=r • (A y).val
      rw [Matrix.transpose_smul]
      exact congrArg (r • ·) (show (A y).valᵀ=(A y).val from (A y).property)⟩) U := by
  obtain ⟨O,hOU,hO,hx⟩ := mem_regularRegion_iff.mp h
  exact mem_regularRegion_iff.mpr ⟨O,hOU,hO.tensor_smul r,hx⟩

end ScalarConductivity

end


noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma scalar_flux_weak {F : Coord3 → Coord3} {U : Set Coord3} (r : ℝ)
    (hF : ∀ ψ : SmoothScalar Coord3,HasCompactSupport ψ.val → tsupport ψ.val⊆U →
      (∫ x,fderiv ℝ ψ.val x (F x))=0)
    (ψ : SmoothScalar Coord3) (hc : HasCompactSupport ψ.val) (hs : tsupport ψ.val⊆U) :
    (∫ x,fderiv ℝ ψ.val x (r • F x))=0 := by
  simp only [map_smul,smul_eq_mul,integral_const_mul,hF ψ hc hs,mul_zero]

end ScalarConductivity

end


noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

attribute [local instance] OAI.ScalarConductivity.instMeasurableSpaceMat3
local instance instBorelSpaceMat3 : BorelSpace Mat3 :=
  inferInstanceAs (BorelSpace (Fin 3 → Fin 3 → ℝ))

namespace WeakFiniteTensorPair

attribute [local instance] OAI.ScalarConductivity.instMeasurableSpaceMat3
def scaleTensor {U : Set Coord3} (d : WeakFiniteTensorPair U) (r : ℝ) (hr : 0 < r) :
    WeakFiniteTensorPair U where
  v := d.v
  E x := r • d.E x
  symm x := by
    change (r • d.E x)ᵀ=r • d.E x
    rw [Matrix.transpose_smul,(d.symm x).eq]
  smooth := d.smooth
  measurable := (measurable_const : Measurable (fun _ : Coord3 => r)).smul d.measurable
  elliptic := by
    obtain ⟨l,L,hl,hlL,hb⟩ := d.elliptic
    refine ⟨r*l,r*L,mul_pos hr hl,mul_le_mul_of_nonneg_left hlL hr.le,?_⟩
    intro x w
    simp only [Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul]
    constructor
    · simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hb x w).1 hr.le
    · simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hb x w).2 hr.le
  regular := by
    filter_upwards [d.regular] with x hx
    exact fun hxU => mem_regularRegion_tensor_smul (hx hxU) r
  G x := r • d.G x
  flux_C1 := (contDiff_const : ContDiff ℝ 1 (fun _ : Coord3 => r)).smul d.flux_C1
  constitution := by
    filter_upwards [d.constitution] with x hx
    rw [Matrix.smul_mul,hx]
  weak j ψ hc hs := by
    change (∫ x,fderiv ℝ ψ.val x (r • (d.G x).col j))=0
    exact scalar_flux_weak r (d.weak j) ψ hc hs

end WeakFiniteTensorPair
end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_FlatFourierFlux
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix

def flatModeFlux (s : Fin 3 → ℝ) (f : Coord3 → ℝ) (x : Coord3) : Coord3 :=
  ![fderiv ℝ f x (flatAxis 0),
    s 0*fderiv ℝ f x (flatAxis 1)+s 1*fderiv ℝ f x (flatAxis 2),
    s 1*fderiv ℝ f x (flatAxis 1)+s 2*fderiv ℝ f x (flatAxis 2)]

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_AngularLocalizedSources
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory

def angularCutoff (T : ℝ) (x : Coord3) : ℝ := periodCutoff T (x 1)*periodCutoff T (x 2)

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_CompactBoxDivergenceC1
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

theorem compact_box_divergence_C1 {a b : Fin 3 → ℝ} (hab : ∀ i,a i<b i) :
    ∃ C : ℝ,0<C ∧ ∀ (r : Box3 → ℝ),ContDiff ℝ (↑(⊤ : ℕ∞)) r →
      HasCompactSupport r →
      tsupport r⊆(Ioo (a 0) (b 0) ×ˢ Ioo (a 1) (b 1)) ×ˢ Ioo (a 2) (b 2) →
      (∫ p,r p)=0 → ∀ M : ℝ,0≤M → UniformC1Bound r M →
      ∃ F₁ F₂ F₃ : Box3 → ℝ,
        ContDiff ℝ (↑(⊤ : ℕ∞)) F₁ ∧ ContDiff ℝ (↑(⊤ : ℕ∞)) F₂ ∧
        ContDiff ℝ (↑(⊤ : ℕ∞)) F₃ ∧
        HasCompactSupport F₁ ∧ HasCompactSupport F₂ ∧ HasCompactSupport F₃ ∧
        (∀ p,cubePartial F₁ ((1,0),0) p+cubePartial F₂ ((0,1),0) p+
          cubePartial F₃ ((0,0),1) p=r p) ∧
        tsupport F₁∪tsupport F₂∪tsupport F₃⊆
          (Icc (a 0) (b 0) ×ˢ Icc (a 1) (b 1)) ×ˢ Icc (a 2) (b 2) ∧
        UniformC1Bound F₁ (C*M) ∧ UniformC1Bound F₂ (C*M) ∧ UniformC1Bound F₃ (C*M) := by
  obtain ⟨η₃,hη₃,hsη₃,hvη₃,hiη₃⟩ := exists_unit_interval_bump (hab 2)
  obtain ⟨η₂,hη₂,hsη₂,hvη₂,hiη₂⟩ := exists_unit_interval_bump (hab 1)
  obtain ⟨K₃,hK₃,hbη₃⟩ := exists_uniformC1Bound hη₃ hsη₃
  obtain ⟨K₂,hK₂,hbη₂⟩ := exists_uniformC1Bound hη₂ hsη₂
  have hl₀ : 0<b 0-a 0 := sub_pos.mpr (hab 0)
  have hl₁ : 0<b 1-a 1 := sub_pos.mpr (hab 1)
  have hl₂ : 0<b 2-a 2 := sub_pos.mpr (hab 2)
  let c₁ := 4*K₃*K₂*(b 0-a 0+1)*(b 1-a 1)*(b 2-a 2)
  let c₂ := 2*K₃*(b 1-a 1+1)*(1+K₂*(b 1-a 1))*(b 2-a 2)
  let c₃ := (b 2-a 2+1)*(1+K₃*(b 2-a 2))
  have hc₁ : 0 ≤ c₁ := by dsimp [c₁]; positivity
  have hc₂ : 0 ≤ c₂ := by dsimp [c₂]; positivity
  have hc₃ : 0 ≤ c₃ := by dsimp [c₃]; positivity
  let C := c₁+c₂+c₃+1
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro r hr hs hv hz M hM hbound
  let R := compactFiberMarginal (a 2) (b 2) r
  have hR := compactFiberMarginal_smooth (hab 2).le hr
  have hsR := (compactFiberMarginal_support hs (a := a 2) (b := b 2)).1
  have hvR : tsupport R⊆Ioo (a 0) (b 0) ×ˢ Ioo (a 1) (b 1) := by
    intro x hx
    obtain ⟨p,hp,rfl⟩ := (compactFiberMarginal_support hs).2 hx
    exact (hv hp).1
  have hbR : UniformC1Bound R ((b 2-a 2)*M) := compactFiberMarginal_C1Bound (hab 2).le hr hM hbound
  obtain ⟨F₃,hF₃,hsF₃,hd₃,ht₃,hb₃,hdB₃⟩ := compact_fiber_decomposition_C1 (hab 2) hr hs
    (fun p hp => (hv hp).2) hη₃ hsη₃ hvη₃ hiη₃ hM hK₃.le
    (fun p => (hbound p).1) (fun p => (hbound p).2) (fun t => (hbη₃ t).1)
  let S := compactFiberMarginal (a 1) (b 1) R
  have hS := compactFiberMarginal_smooth (hab 1).le hR
  have hsS := (compactFiberMarginal_support hsR (a := a 1) (b := b 1)).1
  have hvS : tsupport S⊆Ioo (a 0) (b 0) := by
    intro x hx
    obtain ⟨p,hp,rfl⟩ := (compactFiberMarginal_support hsR).2 hx
    exact (hvR hp).1
  have hbS : UniformC1Bound S ((b 1-a 1)*((b 2-a 2)*M)) :=
    compactFiberMarginal_C1Bound (hab 1).le hR (by positivity) hbR
  obtain ⟨G,hG,hsG,hdG,htG,hbG₀,hdbG⟩ := compact_fiber_decomposition_C1 (hab 1) hR hsR
    (fun p hp => (hvR hp).2) hη₂ hsη₂ hvη₂ hiη₂ (by positivity) hK₂.le
    (fun p => (hbR p).1) (fun p => (hbR p).2) (fun t => (hbη₂ t).1)
  have hbG : UniformC1Bound G ((b 1-a 1+1)*(1+K₂*(b 1-a 1))*((b 2-a 2)*M)) := by
    intro p
    refine ⟨(hbG₀ p).trans ?_,hdbG p⟩
    nlinarith [mul_nonneg (by positivity : 0≤1+K₂*(b 1-a 1)) (by positivity : 0≤(b 2-a 2)*M)]
  have hzR : (∫ x,R x)=0 := by
    rw [compactFiberMarginal_integral (hab 2).le
      (hr.continuous.integrable_of_hasCompactSupport hs)
      (fun p hp => (hv (subset_tsupport r hp)).2)]
    exact hz
  have hzS : (∫ x,S x)=0 := by
    rw [compactFiberMarginal_integral (hab 1).le
      (hR.continuous.integrable_of_hasCompactSupport hsR)
      (fun p hp => (hvR (subset_tsupport R hp)).2)]
    exact hzR
  obtain ⟨P,hP,hsP,hdP,htP,hbP⟩ := compact_scalar_primitive_bounded (hab 0) hS
    (fun x hx => hvS (subset_tsupport S hx)) hzS (by positivity) (fun t => (hbS t).1)
  let F₁ : Box3 → ℝ := fun p => η₃ p.2*η₂ p.1.2*P p.1.1
  let F₂ : Box3 → ℝ := fun p => η₃ p.2*G p.1
  have hF₁ : ContDiff ℝ (↑(⊤ : ℕ∞)) F₁ :=
    ((hη₃.comp contDiff_snd).mul (hη₂.comp (contDiff_snd.comp contDiff_fst))).mul
      (hP.comp (contDiff_fst.comp contDiff_fst))
  have hF₂ : ContDiff ℝ (↑(⊤ : ℕ∞)) F₂ :=
    (hη₃.comp contDiff_snd).mul (hG.comp contDiff_fst)
  have hbf : UniformC1Bound (fun p : Box3 => η₃ p.2) K₃ :=
    hbη₃.comp_snd (hη₃.differentiable (by simp)) hK₃.le
  have hbg : UniformC1Bound (fun p : Box3 => η₂ p.1.2) K₂ :=
    (hbη₂.comp_snd (E := ℝ) (hη₂.differentiable (by simp)) hK₂.le).comp_fst
      ((hη₂.comp contDiff_snd).differentiable (by simp)) hK₂.le
  have hbp : UniformC1Bound (fun p : Box3 => P p.1.1)
      ((b 0-a 0+1)*((b 1-a 1)*((b 2-a 2)*M))) :=
    (hbP.comp_fst (P := ℝ) (hP.differentiable (by simp)) (by positivity)).comp_fst
      ((hP.comp contDiff_fst).differentiable (by simp)) (by positivity)
  have hbf₁ : UniformC1Bound F₁ (c₁*M) := by
    have hh := (hbf.mul ((hη₃.comp contDiff_snd).differentiable (by simp))
      ((hη₂.comp (contDiff_snd.comp contDiff_fst)).differentiable (by simp)) hK₃.le hK₂.le hbg).mul
      (((hη₃.comp contDiff_snd).mul (hη₂.comp (contDiff_snd.comp contDiff_fst))).differentiable (by simp))
      ((hP.comp (contDiff_fst.comp contDiff_fst)).differentiable (by simp)) (by positivity) (by positivity) hbp
    convert hh using 1 <;> dsimp [F₁,c₁]
    ring
  have hbf₂ : UniformC1Bound F₂ (c₂*M) := by
    have hh := hbf.mul ((hη₃.comp contDiff_snd).differentiable (by simp))
      ((hG.comp contDiff_fst).differentiable (by simp)) hK₃.le (by positivity)
      (hbG.comp_fst (hG.differentiable (by simp)) (by positivity))
    convert hh using 1 <;> dsimp [F₂,c₂]
    ring
  have hbf₃ : UniformC1Bound F₃ (c₃*M) := by
    intro p
    refine ⟨(hb₃ p).trans ?_,hdB₃ p⟩
    dsimp [c₃]
    nlinarith [mul_nonneg (by positivity : 0≤1+K₃*(b 2-a 2)) hM]
  let K := (Icc (a 0) (b 0) ×ˢ Icc (a 1) (b 1)) ×ˢ Icc (a 2) (b 2)
  have hK : IsCompact K := (isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc
  have ht₁ : tsupport F₁⊆K := by
    apply closure_minimal _ hK.isClosed
    intro p hp
    obtain ⟨h₁,h₂⟩ := mul_ne_zero_iff.mp hp
    obtain ⟨h₃,h₄⟩ := mul_ne_zero_iff.mp h₁
    exact ⟨⟨htP (subset_tsupport P h₂),Ioo_subset_Icc_self (hvη₂ (subset_tsupport η₂ h₄))⟩,
      Ioo_subset_Icc_self (hvη₃ (subset_tsupport η₃ h₃))⟩
  have ht₂ : tsupport F₂⊆K := by
    apply closure_minimal _ hK.isClosed
    intro p hp
    obtain ⟨h₁,h₂⟩ := mul_ne_zero_iff.mp hp
    have hh := htG (subset_tsupport G h₂)
    obtain ⟨q,hq,hqx⟩ := hh.1
    exact ⟨⟨Ioo_subset_Icc_self (hqx ▸ (hvR hq).1),hh.2⟩,
      Ioo_subset_Icc_self (hvη₃ (subset_tsupport η₃ h₁))⟩
  have ht₃' : tsupport F₃⊆K := by
    intro p hp
    have hh := ht₃ hp
    obtain ⟨q,hq,hqp⟩ := hh.1
    have hxy := (hv hq).1
    change q.1∈_ at hxy
    rw [hqp] at hxy
    exact ⟨⟨Ioo_subset_Icc_self hxy.1,Ioo_subset_Icc_self hxy.2⟩,hh.2⟩
  refine ⟨F₁,F₂,F₃,hF₁,hF₂,hF₃,
    HasCompactSupport.of_support_subset_isCompact hK (subset_tsupport F₁ |>.trans ht₁),
    HasCompactSupport.of_support_subset_isCompact hK (subset_tsupport F₂ |>.trans ht₂),hsF₃,?_,
    union_subset (union_subset ht₁ ht₂) ht₃',
    hbf₁.mono (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) hM),
    hbf₂.mono (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) hM),
    hbf₃.mono (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) hM)⟩
  intro p
  have hd₁ : cubePartial F₁ ((1,0),0) p=η₃ p.2*η₂ p.1.2*S p.1.1 := by
    have hline := (hasDerivAt_id p.1.1).prodMk (hasDerivAt_const p.1.1 p.1.2)
    have he := ((hF₁.differentiable (by simp)) p).hasFDerivAt.comp_hasDerivAt p.1.1
      (hline.prodMk (hasDerivAt_const p.1.1 p.2))
    have he' : HasDerivAt (fun t => F₁ ((t,p.1.2),p.2))
        (cubePartial F₁ ((1,0),0) p) p.1.1 := he
    have hp := ((hP.differentiable (by simp)) p.1.1).hasDerivAt.const_mul
      (η₃ p.2*η₂ p.1.2)
    rw [hdP] at hp
    exact he'.unique hp
  have hd₂ : cubePartial F₂ ((0,1),0) p=η₃ p.2*wallDerivative G p.1 := by
    have hline := (hasDerivAt_const p.1.2 p.1.1).prodMk (hasDerivAt_id p.1.2)
    have he := ((hF₂.differentiable (by simp)) p).hasFDerivAt.comp_hasDerivAt p.1.2
      (hline.prodMk (hasDerivAt_const p.1.2 p.2))
    have he' : HasDerivAt (fun t => F₂ ((p.1.1,t),p.2))
        (cubePartial F₂ ((0,1),0) p) p.1.2 := he
    have hg := (((hG.differentiable (by simp)) p.1).hasFDerivAt.comp_hasDerivAt
      p.1.2 hline).const_mul (η₃ p.2)
    exact he'.unique hg
  rw [hd₁,hd₂,cube_partial_fiber]
  have h₁ := hdG p.1
  have h₂ := hd₃ p
  dsimp [S,R] at *
  linear_combination (η₃ p.2)*h₁+h₂

end ScalarConductivity

end
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

lemma cubePartial_bound_of_C1 {f : Box3 → ℝ} {M : ℝ}
    (hb : UniformC1Bound f M) {v : Box3} (hv : ‖v‖≤1) (p : Box3) :
    |cubePartial f v p|≤M := by
  have hM : 0≤M := (norm_nonneg _).trans (hb p).2
  exact ((fderiv ℝ f p).le_opNorm v).trans
    ((mul_le_mul (hb p).2 hv (norm_nonneg _) hM).trans_eq (mul_one M))

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_CompactifiedFourierTail
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology

def compactifiedFourierTerm (s : Fin 3→ℝ) (lam T0 : ℝ)
    (a phase : (Fin 2→ℤ)→ℝ) (h : Fin 2→ℤ) (z : ℝ×Coord3) : ℝ :=
  a h*exp (lam*T0) *
    (expNegInvGlue (z.1/(torusRate s h-lam))*flatPhaseMode s h (phase h) (z.2+![T0,0,0]))

def compactifiedFourierTail (s : Fin 3→ℝ) (lam T0 : ℝ)
    (a phase : (Fin 2→ℤ)→ℝ) (z : ℝ×Coord3) : ℝ :=
  ∑' h,compactifiedFourierTerm s lam T0 a phase h z

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_QuantitativeGlobalCorrection
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

lemma UniformC1Bound.add {f g : Coord3 → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    {M N : ℝ} (hb : UniformC1Bound f M) (hc : UniformC1Bound g N) :
    UniformC1Bound (fun x => f x+g x) (M+N) := by
  intro x
  constructor
  · exact (abs_add_le _ _).trans (add_le_add (hb x).1 (hc x).1)
  · rw [fderiv_fun_add (hf x) (hg x)]
    exact (norm_add_le _ _).trans (add_le_add (hb x).2 (hc x).2)

lemma UniformC1Bound.sum {ι : Type*} (s : Finset ι) (f : ι → Coord3 → ℝ) (N : ι → ℝ)
    (hf : ∀ i∈s,Differentiable ℝ (f i)) (hb : ∀ i∈s,UniformC1Bound (f i) (N i)) :
    UniformC1Bound (∑ i∈s,f i) (∑ i∈s,N i) := by
  classical
  induction s using Finset.induction_on with
  | empty => intro x; simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha,Finset.sum_insert ha]
    exact (hb a (Finset.mem_insert_self a s)).add (hf a (Finset.mem_insert_self a s))
      (Differentiable.sum (fun i hi => hf i (Finset.mem_insert_of_mem hi)))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)) (fun i hi => hb i (Finset.mem_insert_of_mem hi)))

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

lemma compact_parametric_norm_small_global {P F : Type*} [TopologicalSpace P]
    [NormedAddCommGroup F] {f : P×Coord3 → F} {p : P} {K : Set Coord3}
    (hK : IsCompact K) (hf : ∀ x∈K,ContinuousAt f (p,x))
    (hz : ∀ x,f (p,x)=0)
    (hs : ∀ᶠ q in 𝓝 p,tsupport (fun x => f (q,x))⊆K)
    {ε : ℝ} (hε : 0<ε) : ∀ᶠ q in 𝓝 p,∀ x,‖f (q,x)‖≤ε := by
  filter_upwards [compact_parametric_norm_small hK hf (fun x _ => hz x) hε,hs] with q small supp
  intro x
  by_cases hx : x∈K
  · exact small x hx
  · rw [image_eq_zero_of_notMem_tsupport (f:=fun x => f (q,x)) (fun hh => hx (supp hh)),norm_zero]
    exact hε.le

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

lemma compact_supported_integral_tendsto_zero {P : Type*} [TopologicalSpace P]
    [FirstCountableTopology P] {f : P×Coord3 → ℝ} {p : P} {K : Set Coord3}
    (hK : IsCompact K) (hf : ∀ x,ContinuousAt f (p,x)) (hz : ∀ x,f (p,x)=0)
    (hc : ∀ᶠ q in 𝓝 p,Continuous (fun x => f (q,x)))
    (hs : ∀ᶠ q in 𝓝 p,tsupport (fun x => f (q,x))⊆K) :
    Tendsto (fun q => ∫ x,f (q,x)) (𝓝 p) (𝓝 0) := by
  have ht : ContinuousAt (fun q => ∫ x in K,f (q,x)) p := by
    apply continuousAt_of_dominated (bound:=fun _ => (1:ℝ))
      (hc.mono (fun q hh => hh.aestronglyMeasurable))
    · filter_upwards [compact_parametric_norm_small hK (fun x _ => hf x)
        (fun x _ => hz x) zero_lt_one] with q hq
      exact (ae_restrict_mem hK.measurableSet).mono (fun x hx => hq x hx)
    · exact integrableOn_const hK.measure_ne_top
    · apply Eventually.of_forall
      intro x
      have hg : ContinuousAt (fun q : P => (q,x)) p := continuousAt_id.prodMk continuousAt_const
      exact (hf x).comp (f:=fun q : P => (q,x)) hg
  have ht' : Tendsto (fun q => ∫ x in K,f (q,x)) (𝓝 p) (𝓝 0) := by
    simpa only [ContinuousAt,hz,integral_zero] using ht
  apply ht'.congr'
  filter_upwards [hs] with q hq
  exact setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx =>
    image_eq_zero_of_notMem_tsupport (f:=fun x => f (q,x)) (fun hh => hx (hq hh)))

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

lemma wallMomentAmplitude_parametric_smooth {χ η : ℝ → ℝ} (σ lam : ℝ)
    (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ) (hη : ContDiff ℝ (↑(⊤:ℕ∞)) η) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (fun q : Coord3×(ℝ×ℝ) => wallMomentAmplitude χ η σ lam q.1 q.2) := by
  simp_rw [wallMomentAmplitude_sum]
  apply ContDiff.sum
  intro i _
  exact ((contDiff_apply ℝ ℝ i).comp contDiff_fst).smul
    ((wallMomentTest_smooth σ lam hχ hη i).comp contDiff_snd)

lemma wallMomentAmplitude_zero (χ η : ℝ → ℝ) (σ lam : ℝ) :
    wallMomentAmplitude χ η σ lam 0=0 := by
  funext q; simp [wallMomentAmplitude]

lemma wallMomentAmplitude_compact {χ η : ℝ → ℝ} (σ lam : ℝ)
    (hχ : HasCompactSupport χ) (hη : HasCompactSupport η) (c : Coord3) :
    HasCompactSupport (wallMomentAmplitude χ η σ lam c) ∧
      tsupport (wallMomentAmplitude χ η σ lam c)⊆tsupport χ×ˢtsupport η := by
  have hh := surface_product_compact (f:=fun s => χ s*(c ⬝ᵥ wallMomentBasis σ lam s))
    hχ.mul_right hη
  exact ⟨hh.1,hh.2.trans (prod_mono tsupport_mul_subset_left Subset.rfl)⟩

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

omit [NormedSpace ℝ P] [FiniteDimensional ℝ P] in
lemma compact_parameter_nonzero_neighborhood {f : P×Box3 → ℝ} (hf : Continuous f)
    {p : P} {K : Set Box3} (hK : IsCompact K) (hne : ∀ x∈K,f (p,x)≠0) :
    ∃ V : Set P,IsOpen V ∧ p∈V ∧ ∀ q∈V,∀ x∈K,f (q,x)≠0 := by
  have hh : ∀ᶠ q in 𝓝 p,∀ x∈K,f (q,x)≠0 := by
    apply hK.eventually_forall_of_forall_eventually
    intro x hx
    exact hf.continuousAt.eventually_ne (hne x hx)
  obtain ⟨V,hsub,hV,hp⟩ := mem_nhds_iff.mp hh
  exact ⟨V,hV,hp,fun q hq => hsub hq⟩

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_AffineFourierField
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix

def affineFourierField (s : Fin 3→ℝ) (a phase : (Fin 2→ℤ)→ℝ) (α β : ℝ) (x : Coord3) : ℝ :=
  α*x 0+β+flatFourier s a phase x

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

def torusRealProjection (x : TorusRealPlane) : UnitAddTorus (Fin 2) := fun j => (x j:UnitAddCircle)
def torusRealRepresentative (θ : UnitAddTorus (Fin 2)) : TorusRealPlane :=
  (measurableEquivPiIoc (fun _ : Fin 2 => (0:ℝ)) θ).val

lemma continuous_torusRealProjection : Continuous torusRealProjection := by
  apply continuous_pi
  intro j
  exact (AddCircle.continuous_mk' (1:ℝ)).comp (continuous_apply j)

lemma torusRealProjection_representative (θ : UnitAddTorus (Fin 2)) :
    torusRealProjection (torusRealRepresentative θ)=θ :=
  (measurableEquivPiIoc (fun _ : Fin 2 => (0:ℝ))).symm_apply_apply θ

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

lemma contDiff_sourceAngularPolynomial_joint :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun z : ℝ × (Fin 4 → ℝ) => sourceAngularPolynomial z.1 z.2) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [sourceAngularPolynomial] <;> fun_prop

def sourceAngularAxial (f : (Fin 3 → ℝ) → ℝ) (a b t : ℝ)
    (θ : UnitAddTorus (Fin 2)) : ℂ :=
  ((deriv (fun u => f (sourceAngularCollar (a*u+b) θ)) t : ℝ) : ℂ)

lemma continuous_sourceAngularAxial {f : (Fin 3 → ℝ) → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (a b : ℝ) :
    Continuous (fun z : ℝ × UnitAddTorus (Fin 2) => sourceAngularAxial f a b z.1 z.2) := by
  let F : ℝ × (Fin 4 → ℝ) → ℝ := fun z =>
    f (sourceAngularPolynomial (a*z.1+b) z.2)
  have hF : ContDiff ℝ (↑(⊤ : ℕ∞)) F :=
    hf.comp (contDiff_sourceAngularPolynomial_joint.comp
      ((contDiff_const.mul contDiff_fst |>.add contDiff_const).prodMk contDiff_snd))
  have he (t : ℝ) (θ : UnitAddTorus (Fin 2)) :
      sourceAngularAxial f a b t θ =
        (fderiv ℝ F (t,sourceRayCoordinates θ) (1,0) : ℂ) := by
    have h := (hF.differentiable (by simp)).differentiableAt.hasFDerivAt
      (x:=(t,sourceRayCoordinates θ))
    have hg := h.comp_hasDerivAt t ((hasDerivAt_id t).prodMk
      (hasDerivAt_const t (sourceRayCoordinates θ)))
    simpa only [sourceAngularAxial,sourceAngularCollar,F,Function.comp_def,id_eq] using
      congrArg (fun u : ℝ => (u:ℂ)) hg.deriv
  simp_rw [he]
  exact Complex.continuous_ofReal.comp
    ((hF.continuous_fderiv (by simp)).comp
      (continuous_fst.prodMk (continuous_sourceRayCoordinates.comp continuous_snd))
      |>.clm_apply continuous_const)

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

def sourceAngularTest (f : (Fin 3 → ℝ) → ℝ) (a b : ℝ)
    (z : ℝ × UnitAddTorus (Fin 2)) : ℂ :=
  (f (sourceAngularCollar (a*z.1+b) z.2) : ℂ)

lemma continuous_sourceAngularTest {f : (Fin 3 → ℝ) → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (a b : ℝ) :
    Continuous (sourceAngularTest f a b) :=
  Complex.continuous_ofReal.comp (hf.continuous.comp
    (contDiff_sourceAngularPolynomial_joint.continuous.comp
      ((continuous_const.mul continuous_fst |>.add continuous_const).prodMk
        (continuous_sourceRayCoordinates.comp continuous_snd))))

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
lemma finiteCylinder_ae_mem (R : ℝ) :
    ∀ᵐ z ∂(FiniteAxisMeasure R).prod (volume : Measure (UnitAddTorus (Fin 2))),
      z.1∈Icc (0:ℝ) R :=
  Measure.quasiMeasurePreserving_fst.ae
    ((ae_restrict_mem measurableSet_Ioc).mono fun _ ht => Ioc_subset_Icc_self ht)

lemma continuous_memLp_finiteCylinder {f : ℝ × UnitAddTorus (Fin 2) → ℂ}
    (hf : Continuous f) (R : ℝ) :
    MemLp f 2 ((FiniteAxisMeasure R).prod volume) := by
  obtain ⟨C,hC⟩ := ((isCompact_Icc (a:=(0:ℝ)) (b:=R)).prod
    (isCompact_univ : IsCompact (univ : Set (UnitAddTorus (Fin 2))))).exists_bound_of_continuousOn hf.continuousOn
  apply MemLp.of_bound hf.aestronglyMeasurable C
  filter_upwards [finiteCylinder_ae_mem R] with z hz
  exact hC z ⟨hz,mem_univ _⟩

end ScalarConductivity

end
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

def angularFrequency (h : TorusModes) : Coord3 →L[ℝ] ℂ :=
  (Complex.I*(h 0:ℂ)) • Complex.ofRealCLM.comp (ContinuousLinearMap.proj 1)+
  (Complex.I*(h 1:ℂ)) • Complex.ofRealCLM.comp (ContinuousLinearMap.proj 2)

end ScalarConductivity

end
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
open Set Filter Topology MeasureTheory Matrix

def axialFluxBlend (χ : ℝ → ℝ) (F G : Coord3 → Coord3) (x : Coord3) : Coord3 :=
  fun i => (1-χ (x 0))*F x i+χ (x 0)*G x i

end ScalarConductivity



end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_AngularPhaseTranslation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix

def angularRealTranslation (v : Fin 2 → ℝ) (x : Coord3) : Coord3 :=
  ![x 0,x 1+v 0,x 2+v 1]

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_SmoothFluxIntegrable
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

def SmoothFluxIntegrable (μ : Measure Coord3) (U : Set Coord3)
    (F : Coord3 → Matrix (Fin 3) (Fin 2) ℝ) : Prop :=
  ∀ (j : Fin 2) (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ →
    HasCompactSupport ψ → tsupport ψ ⊆ U →
    Integrable (fun x => fderiv ℝ ψ x ((F x).col j)) μ

end ScalarConductivity

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

abbrev VoltageJetSpace (μ : Measure Coord3) (U : Set Coord3) :=
  Lp (Fin 2 → ℝ) 2 (μ.restrict U) × Lp FieldVector 2 (μ.restrict U)

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Scalarization_ConcreteFluxScalarization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology TopologicalSpace MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise ENNReal

lemma continuous_memLp_bounded_coord {F : Type*} [NormedAddCommGroup F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    {f : Coord3 → F} (hf : Continuous f) {U : Set Coord3}
    (hUb : Bornology.IsBounded U) (hUm : MeasurableSet U) :
    MemLp f 2 (volume.restrict U) := by
  let : IsFiniteMeasure (volume.restrict U) :=
    isFiniteMeasure_restrict.mpr hUb.measure_lt_top.ne
  obtain ⟨M,hM⟩ := hUb.isCompact_closure.exists_bound_of_continuousOn hf.continuousOn
  apply MemLp.of_bound hf.measurable.aestronglyMeasurable M
  filter_upwards [ae_restrict_mem hUm] with x hx
  exact hM x (subset_closure hx)

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_GeneralModeFiniteEndNormal
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

def angularLiftMatrix (A : Matrix (Fin 2) (Fin 2) ℤ) : Mat3 :=
  !![Real.sqrt (angularNormalization A),0,0;
    0,(A 0 0:ℝ),(A 0 1:ℝ);0,(A 1 0:ℝ),(A 1 1:ℝ)]

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

def undoAngularPoint (A : Matrix (Fin 2) (Fin 2) ℤ) (θ : Fin 2 → ℝ)
    (d : ℝ) (x : Coord3) : Coord3 :=
  angularInverseLift A (x-![d,0,0])-![0,θ 0,θ 1]

lemma undoAngularPoint_zero (A : Matrix (Fin 2) (Fin 2) ℤ) (θ : Fin 2 → ℝ)
    (d : ℝ) (x : Coord3) :
    undoAngularPoint A θ d x 0=(x 0-d)/sqrt (angularNormalization A) := by
  simp [undoAngularPoint,angularInverseLift]

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_UndoAngularWeakPair
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

def undoAngularOutput (A : Matrix (Fin 2) (Fin 2) ℤ) (d lam : ℝ) :
    (Fin 2 → ℝ) ≃L[ℝ] (Fin 2 → ℝ) :=
  ContinuousLinearEquiv.piCongrRight (fun i : Fin 2 =>
    (LinearEquiv.smulOfNeZero ℝ ℝ
      (if i=0 then sqrt (angularNormalization A) else exp (-lam*d))
      (by split_ifs; exact (sqrt_pos.mpr (angularNormalization_pos A)).ne'; exact exp_ne_zero _)).toContinuousLinearEquiv)

@[simp] lemma undoAngularOutput_apply (A : Matrix (Fin 2) (Fin 2) ℤ) (d lam : ℝ)
    (v : Fin 2 → ℝ) (i : Fin 2) :
    undoAngularOutput A d lam v i=
      (if i=0 then sqrt (angularNormalization A) else exp (-lam*d))*v i := rfl

def undoAngularTranslation (A : Matrix (Fin 2) (Fin 2) ℤ) (θ : Fin 2 → ℝ) (d : ℝ) : Coord3 :=
  ![d,0,0]+angularNormalizedLift A ![0,θ 0,θ 1]

lemma undoAngularPoint_eq_affine {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : A.det=1)
    (θ : Fin 2 → ℝ) (d : ℝ) (x : Coord3) :
    (angularNormalizedEquiv A hA).symm (x-undoAngularTranslation A θ d)=
      undoAngularPoint A θ d x := by
  unfold undoAngularTranslation
  rw [←sub_sub,map_sub,angularNormalizedEquiv_symm_apply,
    angularNormalizedEquiv_symm_apply,angularInverseLift_normalized hA]
  rfl

lemma undoAngular_domain {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : A.det=1)
    (θ : Fin 2 → ℝ) (d : ℝ) :
    ((fun x => x-undoAngularTranslation A θ d) ⁻¹'
      ((angularNormalizedEquiv A hA).symm ⁻¹' {y : Coord3 | 0<y 0}))=
      {x : Coord3 | d<x 0} := by
  ext x
  change (0<(angularNormalizedEquiv A hA).symm (x-undoAngularTranslation A θ d) 0) ↔ _
  rw [undoAngularPoint_eq_affine hA,undoAngularPoint_zero]
  exact (div_pos_iff_of_pos_right (sqrt_pos.mpr (angularNormalization_pos A))).trans sub_pos

namespace WeakFiniteTensorPair

def undoAngular {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : A.det=1)
    (θ : Fin 2 → ℝ) (d lam : ℝ) (w : WeakFiniteTensorPair {y : Coord3 | 0<y 0}) :
    WeakFiniteTensorPair {x : Coord3 | d<x 0} := by
  let z := ((w.linear (angularNormalizedEquiv A hA).symm
    (undoAngularOutput A d lam)).translate (undoAngularTranslation A θ d) ![d,0]).scaleTensor
      (angularNormalization A)⁻¹ (inv_pos.mpr (angularNormalization_pos A))
  exact z.onEq (undoAngular_domain hA θ d)

end WeakFiniteTensorPair
end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_RankProjectionFirst
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology Matrix

lemma TwoFieldRankRegular.projectFirst {u : Coord3 → Fin 2 → ℝ} {O : Set Coord3}
    (hO : IsOpen O) (hs : ContDiffOn ℝ (↑(⊤ : ℕ∞)) u O)
    (h : TwoFieldRankRegular u O) :
    TwoFieldRankRegular (fun x => ![u x 0,0]) O := by
  rcases h with h|h|⟨κ,hκ⟩
  · right; left
    have hs0 : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (fun x => u x 0) O :=
      (contDiff_apply ℝ ℝ (0:Fin 2)).comp_contDiffOn hs
    refine ⟨fun x => u x 0,![1,0],0,hs0,⟨0,by simp⟩,?_,?_⟩
    · intro x hx hz
      have hd := ((hs.differentiableOn (by simp)) x hx).differentiableAt (hO.mem_nhds hx)
      have he := ((ContinuousLinearMap.proj (0:Fin 2) : (Fin 2 → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp x hd.hasFDerivAt).fderiv
      have hn := (h x hx).ne_zero (0:Fin 2)
      apply hn
      ext i
      have hi := congrArg (fun D : Coord3 →L[ℝ] ℝ => D (Pi.single i 1)) hz
      change fderiv ℝ (fun y => u y 0) x = _ at he
      rw [he] at hi
      exact hi
    · intro x hx j
      fin_cases j <;> simp
  · obtain ⟨v,l,κ,hv,hl,hd,he⟩ := h
    by_cases hl0 : l 0=0
    · right; right
      refine ⟨![κ 0,0],?_⟩
      intro x hx
      ext j
      fin_cases j <;> simp [he x hx,hl0]
    · right; left
      refine ⟨v,![l 0,0],![κ 0,0],hv,⟨0,hl0⟩,hd,?_⟩
      intro x hx j
      fin_cases j <;> simp [he x hx]
  · right; right
    exact ⟨![κ 0,0],fun x hx => by dsimp only; rw [hκ x hx]⟩

lemma RegularPatch.projectFirst {u : Coord3 → Fin 2 → ℝ}
    {A : Coord3 → Symmetric3} {O : Set Coord3} (h : RegularPatch u A O) :
    RegularPatch (fun x => ![u x 0,0]) A O := by
  refine ⟨h.1,?_,h.2.2.1,h.2.2.2.projectFirst h.1 h.2.1⟩
  apply contDiffOn_pi.mpr
  intro j
  fin_cases j
  · change ContDiffOn ℝ (↑(⊤ : ℕ∞)) (fun x => u x 0) O
    exact (contDiff_apply ℝ ℝ (0:Fin 2)).comp_contDiffOn h.2.1
  · exact contDiffOn_const

lemma mem_regularRegion_projectFirst {u : Coord3 → Fin 2 → ℝ}
    {A : Coord3 → Symmetric3} {U : Set Coord3} {x : Coord3}
    (h : x∈regularRegion u A U) :
    x∈regularRegion (fun y => ![u y 0,0]) A U := by
  obtain ⟨O,hOU,hO,hx⟩ := mem_regularRegion_iff.mp h
  exact mem_regularRegion_iff.mpr ⟨O,hOU,hO.projectFirst,hx⟩

end ScalarConductivity



namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma fderiv_projectFirst {u : Coord3 → Fin 2 → ℝ} {x : Coord3}
    (hu : DifferentiableAt ℝ u x) :
    gradientColumns (fderiv ℝ (fun y => ![u y 0,0]) x)=
      fun i => ![gradientColumns (fderiv ℝ u x) i 0,0] := by
  have hproj : HasFDerivAt (fun y => ![u y 0,0])
      (ContinuousLinearMap.pi (fun j : Fin 2 => if j=0 then
        (ContinuousLinearMap.proj (0:Fin 2) : (Fin 2 → ℝ) →L[ℝ] ℝ).comp (fderiv ℝ u x) else 0)) x := by
    apply hasFDerivAt_pi.mpr
    intro j
    fin_cases j
    · change HasFDerivAt (fun y => u y 0) ((ContinuousLinearMap.proj (0:Fin 2) : (Fin 2 → ℝ) →L[ℝ] ℝ).comp (fderiv ℝ u x)) x
      simpa only [Function.comp_def,ContinuousLinearMap.proj_apply] using ((ContinuousLinearMap.proj (0:Fin 2) : (Fin 2 → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp x hu.hasFDerivAt)
    · simpa using (hasFDerivAt_const (0:ℝ) x)
  rw [hproj.fderiv]
  ext i j
  fin_cases j <;> simp [gradientColumns]

namespace WeakFiniteTensorPair

def projectFirst {U : Set Coord3} (w : WeakFiniteTensorPair U) : WeakFiniteTensorPair U where
  v x := ![w.v x 0,0]
  E := w.E
  symm := w.symm
  smooth := by
    apply contDiff_pi.mpr
    intro j
    fin_cases j
    · change ContDiff ℝ 2 (fun x => w.v x 0)
      exact (contDiff_apply ℝ ℝ (0:Fin 2)).comp w.smooth
    · exact contDiff_const
  measurable := w.measurable
  elliptic := w.elliptic
  regular := by
    filter_upwards [w.regular] with x hx
    exact fun hxU => mem_regularRegion_projectFirst (hx hxU)
  G x i := ![w.G x i 0,0]
  flux_C1 := by
    apply contDiff_pi.mpr; intro i
    apply contDiff_pi.mpr; intro j
    fin_cases j
    · change ContDiff ℝ 1 (fun x => w.G x i 0)
      exact (contDiff_apply ℝ ℝ (0:Fin 2)).comp ((contDiff_apply ℝ (Fin 2 → ℝ) i).comp w.flux_C1)
    · exact contDiff_const
  constitution := by
    filter_upwards [w.constitution] with x hx
    rw [fderiv_projectFirst (w.smooth.differentiable (by norm_num) x)]
    ext i j
    fin_cases j
    · exact congrFun (congrFun hx i) 0
    · change (∑ k,w.E x i k*0)=0
      simp
  weak j ψ hc hs := by
    fin_cases j
    · exact w.weak 0 ψ hc hs
    · change (∫ x,fderiv ℝ ψ.val x (0:Coord3))=0
      simp

end WeakFiniteTensorPair
end ScalarConductivity

end


end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_AxialExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def axialZeroExtension (d e : ℝ) (f : Coord3 → E) (x : Coord3) : E :=
  if d+e/2<x 0 then f x else 0

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_TorusEndingCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix UnitAddTorus
open scoped Matrix.Norms.Elementwise

def torusEndingCorrection (d e : ℝ) (v f : Coord3 → ℝ) : Coord3 → ℝ :=
  axialZeroExtension (d+e/4) (e/2) (v-f)

def torusEndingFluxCorrection (d e : ℝ) (G F : Coord3 → Coord3) : Coord3 → Coord3 :=
  axialZeroExtension (d+e/4) (e/2) (G-F)

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

def centralLaplacian (f : Box3 → ℝ) (x : Box3) : ℝ :=
  ∑ i : Fin 3,cubePartial (cubePartial f (centralDirection i)) (centralDirection i) x

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_FiniteEndPhysicalDescent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus Matrix

def sourceRealFlat (y : Coord3) : Coord3 :=
  ![sourceCollarTime y,(sourceComplexDirections y 0).arg,
    (sourceComplexDirections y 1).arg]

def physicalPeriodicField {E : Type*} (f : Coord3 → E) (y : Coord3) : E :=
  f (sourceRealFlat y)

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_TorusPeriodicDescent
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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def torusPeriodicDescent (f : Coord3 → E) (z : ℝ × UnitAddTorus (Fin 2)) : E :=
  f ![z.1,2*Real.pi*torusRealRepresentative z.2 0,
    2*Real.pi*torusRealRepresentative z.2 1]

lemma torusAngles_scaled (t : ℝ) (x : Fin 2 → ℝ) :
    torusAngles ![t,2*Real.pi*x 0,2*Real.pi*x 1]=torusRealProjection x := by
  ext i
  fin_cases i <;> simp [torusAngles,torusRealProjection,Real.pi_ne_zero]

lemma torusPeriodicDescent_real {f : Coord3 → E}
    (hp : AngularPeriodic (2*Real.pi) f) (t : ℝ) (x : Fin 2 → ℝ) :
    torusPeriodicDescent f (t,torusRealProjection x)=f ![t,2*Real.pi*x 0,2*Real.pi*x 1] := by
  change f ![t,2*Real.pi*torusRealRepresentative (torusRealProjection x) 0,
    2*Real.pi*torusRealRepresentative (torusRealProjection x) 1]=_
  apply hp.eq_of_angles
  · rfl
  rw [torusAngles_scaled,torusAngles_scaled,torusRealProjection_representative]

lemma isOpenMap_torusRealProjection : IsOpenMap torusRealProjection := by
  change IsOpenMap (Pi.map (fun _ : Fin 2 => ((↑) : ℝ → UnitAddCircle)))
  exact IsOpenMap.piMap (fun _ => QuotientAddGroup.isOpenMap_coe)
    (Filter.Eventually.of_forall fun _ => QuotientAddGroup.mk_surjective)

lemma torusRealProjection_surjective : Function.Surjective torusRealProjection :=
  fun θ => ⟨torusRealRepresentative θ,torusRealProjection_representative θ⟩

lemma continuous_torusPeriodicDescent {f : Coord3 → E}
    (hf : Continuous f) (hp : AngularPeriodic (2*Real.pi) f) :
    Continuous (torusPeriodicDescent f) := by
  let P := Prod.map (id : ℝ → ℝ) torusRealProjection
  have hP : IsQuotientMap P := (IsOpenMap.id.prodMap isOpenMap_torusRealProjection).isQuotientMap
    (continuous_id.prodMap continuous_torusRealProjection)
    (Function.surjective_id.prodMap torusRealProjection_surjective)
  apply hP.continuous_iff.mpr
  have he : torusPeriodicDescent f ∘ P =
      fun z : ℝ × (Fin 2 → ℝ) => f ![z.1,2*Real.pi*z.2 0,2*Real.pi*z.2 1] := by
    funext z
    exact torusPeriodicDescent_real hp z.1 z.2
  rw [he]
  exact hf.comp (by fun_prop)

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

lemma continuous_torusFluxComponent (hF : Continuous F) (hp : AngularPeriodic (2*Real.pi) F)
    (j : Fin 3) : Continuous (fun z => (torusPeriodicDescent F z j:ℂ)) :=
  Complex.continuous_ofReal.comp ((continuous_apply j).comp (continuous_torusPeriodicDescent hF hp))

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_CentralPhysicalEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix

lemma centralPhysicalWholeCLM_norm (f : CentralL2) :
    ‖centralPhysicalWholeCLM f‖=‖f‖ := by
  change ‖(Lp.compMeasurePreservingₗᵢ ℝ sourcePairMeasurable sourcePair_volume)
    (lpZeroExtensionCLM centralClosed_compact.measurableSet f)‖=‖f‖
  rw [LinearIsometry.norm_map]
  exact lpZeroExtensionL_norm centralClosed_compact.measurableSet f

def centralPhysicalWholeLI : CentralL2 →ₗᵢ[ℝ] Lp ℝ 2 (volume : Measure (Fin 3 → ℝ)) where
  toLinearMap := centralPhysicalWholeCLM.toLinearMap
  norm_map' := centralPhysicalWholeCLM_norm

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_CentralHarmonicOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

def centralStrict : Set Coord3 := {y | centralThickness < sourceCollarTime y ∧
  ∀ k : Fin 2,sourceCollarTime ((sourceChildHomeomorph (actualChildSign k)).symm y)< -centralThickness}

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
variable {s : Fin 3 → ℝ}

def terminalTime (i : Fin 3) (y : Coord3) : ℝ :=
  Fin.cases (sourceCollarTime y)
    (fun k => sourceCollarTime ((sourceChildHomeomorph (actualChildSign k)).symm y)) i

def terminalBase (i : Fin 3) : ℝ := if i=0 then centralThickness else -centralThickness

end PhysicalFiniteEndingData
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
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped Convolution ENNReal NNReal

def continuousOuterMap (i : Fin 3) {f : R3 → ℝ} (hf : Continuous f) :
    C(UnitAddTorus (Fin 2),ℂ) :=
  ⟨fun θ => (f (WithLp.toLp 2 (physicalOuterBoundary i θ)):ℂ),
    Complex.continuous_ofReal.comp (hf.comp
      ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.continuous.comp
        (physicalOuterBoundary_continuous i)))⟩

attribute [local instance] OAI.ScalarConductivity.instMeasureSpaceUnitAddCircle_solutions_10
attribute [local instance] OAI.ScalarConductivity.instIsProbabilityMeasureUnitAddCircleVolume_solutions_10
def continuousOuterFourier (i : Fin 3) {f : R3 → ℝ} (hf : Continuous f) : SpectralL2 TorusModes :=
  (mFourierBasis (d:=Fin 2)).repr (ContinuousMap.toLp 2 volume ℂ (continuousOuterMap i hf))

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Walls_PhysicalTerminalCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory
namespace PhysicalFiniteEndingData

def terminalCore (η : ℝ) : Set Coord3 :=
  {y | η≤terminalTime 0 y ∧ ∀ k : Fin 2,terminalTime k.succ y≤-η}

end PhysicalFiniteEndingData
end ScalarConductivity

end
end

end OAI
end


