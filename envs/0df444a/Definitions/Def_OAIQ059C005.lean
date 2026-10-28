-- Prove2me | Definitions.Def_OAIQ059C005
-- name    : OAIQ059C005
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T21:34:53.205635+00:00
-- url     : https://prove2.me/theorems/29a9917c-23f9-45b9-80b1-6a8117825445
-- title:
--   Definitions bundle OAIQ059C005 of the split of OpenAI, Nonuniqueness for bounded measurable scalar conductivities in three dimensions (result family 365)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ScalarConductivity.main_nonuniqueness`, carved from OpenAI's openai/math development (OpenAI, *Nonuniqueness for bounded measurable scalar conductivities in three dimensions (result family 365)*, OpenAI Math Release, September 23, 2026, result family 365, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 136 declarations of OpenAI's Lean: 104 definitions and 32 theorems. The definitions and types are `OAI.ScalarConductivity.crossingCurrentX`, `OAI.ScalarConductivity.crossingCurrentY`, `OAI.ScalarConductivity.crossingCurrentZ`, `OAI.ScalarConductivity.crossingValue`, `OAI.ScalarConductivity.crossingValue3`, `OAI.ScalarConductivity.cubeEnergyDensity`, `OAI.ScalarConductivity.cylinderCoefficient`, `OAI.ScalarConductivity.cylinderCoefficientLp`, `OAI.ScalarConductivity.cylinderJetCoefficient`, `OAI.ScalarConductivity.cylinderPolynomialTraceL`, `OAI.ScalarConductivity.delayedInitialTensor`, `OAI.ScalarConductivity.depthClass`, `OAI.ScalarConductivity.endingCoordinateTransportMeasurableSpace`, `OAI.ScalarConductivity.endingJoinEllipticMeasurableSpace`, `OAI.ScalarConductivity.flatCylinderEnergy`, `OAI.ScalarConductivity.flatCylinderEnergyLeftCLM`, `OAI.ScalarConductivity.flatCylinderEnergyRightCLM`, `OAI.ScalarConductivity.flatTensorLaplacian`, `OAI.ScalarConductivity.flatTensorLaplacianCLM`, `OAI.ScalarConductivity.fourierFiniteEndingNormalMeasurableSpace`, `OAI.ScalarConductivity.gaugeCoefficient`, `OAI.ScalarConductivity.generalModeFiniteEndNormalMeasurableSpace`, `OAI.ScalarConductivity.h10PoincareConstant`, `OAI.ScalarConductivity.inverseOperation`, `OAI.ScalarConductivity.jetProduct`, `OAI.ScalarConductivity.joinHull`, `OAI.ScalarConductivity.localizedFirstPotential`, `OAI.ScalarConductivity.localizedSecondPotential`, `OAI.ScalarConductivity.matchingFlux`, `OAI.ScalarConductivity.matrixFiniteLaminate`, `OAI.ScalarConductivity.nonlinearFirstPotential`, `OAI.ScalarConductivity.normalStretch`, `OAI.ScalarConductivity.normalizedAngularTensor`, `OAI.ScalarConductivity.normalizedFourierCoefficients`, `OAI.ScalarConductivity.originalCartesianJetCLM`, `OAI.ScalarConductivity.originalMulComponentCLM`, `OAI.ScalarConductivity.originalMulJetCLM`, `OAI.ScalarConductivity.originalVoltageGradient`, `OAI.ScalarConductivity.originalWholeDirection`, `OAI.ScalarConductivity.originalWholeValue` and 64 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `Conductivity_Branching_AlignedEndingRegularity`, `Conductivity_Branching_CrossingBlock`, `Conductivity_Branching_EndingCoordinateTransport`, `Conductivity_Branching_EndingJoinElliptic`, `Conductivity_Branching_JoinHull`, `Conductivity_Branching_PhysicalBlockRepresentative`, `Conductivity_Branching_RecoverJoinChild`, `Conductivity_Branching_VariableBlockEnergy`, `Conductivity_Flux_AttachedPhysicalSmoothGreen`, `Conductivity_Flux_CylinderCompletedGreen`, `Conductivity_Flux_CylinderGreen`, `Conductivity_Flux_CylinderSeriesGreen`, `Conductivity_Flux_CylinderSlopeGreen`, `Conductivity_Flux_PhysicalAttachedGreen`, `Conductivity_Flux_PotentialCurl`, `Conductivity_Flux_TorusBoxFlux`, `Conductivity_Flux_TwoFluxColumns`, `Conductivity_Flux_TwoFluxDivergence`, `Conductivity_Fourier_AngularLocalizedMoments`, `Conductivity_Fourier_CylinderFourierComplete`, `Conductivity_Fourier_CylinderFourierGraph`, `Conductivity_Fourier_CylinderModeGreen`, `Conductivity_Fourier_EndingJoinMiddleModel`, `Conductivity_Fourier_FourierFiniteEndingNormal`, `Conductivity_Fourier_FourierPairFlux`, `Conductivity_Fourier_GeneralModeFiniteEndNormal`, `Conductivity_Fourier_LeadingFrequencyAlignment`, `Conductivity_Fourier_PureModeWall`, `Conductivity_Fourier_SpectralExtensionMono`, `Conductivity_Fourier_SpectralExtensionNonemptyNonempty`, `Conductivity_Fourier_SpectralTerminalL2`, `Conductivity_Fourier_TorusLeadingRealMode`, `Conductivity_Fourier_TorusNonresonance`, `Conductivity_Fourier_TorusSmoothModeJet`, `Conductivity_Geometry_BoxEnergyPoincare`, `Conductivity_Geometry_CylinderJetOrthogonal`, `Conductivity_Geometry_CylinderPolynomial`, `Conductivity_Geometry_FlatTorusPDE`, `Conductivity_Geometry_SplitJacobian`, `Conductivity_Scalarization_EndingJoinConstitution`, `Conductivity_Sobolev_BoundedMultiplier`, `Conductivity_Sobolev_OriginalSmoothMultiplier`, `Conductivity_Sobolev_SobolevDistribution`, `Conductivity_Sobolev_SobolevGaugeTransform`, `Conductivity_Sobolev_SobolevMaximum`, `Conductivity_Sobolev_SobolevSmoothOperations`, `Conductivity_Sobolev_SobolevSmoothTests`, `Conductivity_Sobolev_VoltageOriginalH10`, `Conductivity_Sobolev_WallParticular`, `Conductivity_Sources_AngularCoefficient`, `Conductivity_Sources_FaceMeasure`, `Conductivity_Sources_ParametricSymmetricSources`, `Conductivity_Sources_TorusMoments`, `Conductivity_Variational_CrossingGradient`, `Conductivity_Variational_CrossingHxx`, `Conductivity_Variational_CrossingProfiles`, `Conductivity_Variational_L2TranslationAverage`, `Conductivity_Variational_LocalSmoothWeakDerivative`, `Conductivity_Variational_LocalizedFirstPotential`, `Conductivity_Variational_MatrixFiniteLaminate`, `Conductivity_Variational_MatrixOperator`, `Conductivity_Variational_NormalStretch`, `Conductivity_Variational_OriginalVoltageRestriction`, `Conductivity_Variational_PairedPotential`, `Conductivity_Variational_PhysicalEndOpen`, `Conductivity_Variational_PhysicalEnergyContinuous`, `Conductivity_Variational_PhysicalSmoothTest`, `Conductivity_Variational_PreliminaryQ`, `Conductivity_Variational_RadialLaplacian`, `Conductivity_Variational_RadialWeylScale`, `Conductivity_Variational_SimpleLevelNull`, `Conductivity_Variational_SmoothCompose`, `Conductivity_Variational_Symmetrize`, `Conductivity_Variational_VanishingMomentChoice`, `Conductivity_Variational_VariationalDN`, `Conductivity_Variational_WeakHarmonicMean`, `Conductivity_Walls_CriticalWallResidual`, `Conductivity_Walls_ParametricWallTensors`, `Conductivity_Walls_WallHalfspaceIntegral`.
--
--   **Imports.** It imports the published bundle `Def_Conductivity`; the bundles `OAIQ059C000`, `OAIQ059C001` and `OAIQ059C002` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ059C007`; the statements `OAI.ScalarConductivity.central_pair_regular_exists`, `OAI.ScalarConductivity.elliptic_fourier_matching_regular`, `OAI.ScalarConductivity.exists_local_split_on_subpatch_retained` and `OAI.ScalarConductivity.fine_global_scalar_tensor_approximation`; the proof of `OAI.ScalarConductivity.central_pair_regular_exists`.
-- source:
--   OpenAI, Nonuniqueness for bounded measurable scalar conductivities in three dimensions (result family 365), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 365; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-for-Bounded-Measurable-Scalar-Conductivities-in-Three-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_Conductivity
import Definitions.Def_OAIQ059C000
import Definitions.Def_OAIQ059C001
import Definitions.Def_OAIQ059C002

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_CrossingProfiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory

lemma exists_transition_derivative_bound : ∃ M : ℝ, 1 ≤ M ∧ ∀ x : ℝ,
    |deriv smoothTransition x| ≤ M ∧ |deriv (deriv smoothTransition) x| ≤ M := by
  have hc : HasCompactSupport (deriv smoothTransition) := by
    apply HasCompactSupport.intro (K := Icc (0 : ℝ) 1) isCompact_Icc
    intro x hx
    by_cases h : x < 0
    · exact (smoothTransition_flat_left h).1
    · exact (smoothTransition_flat_right (by simp only [mem_Icc, not_and_or, not_le] at hx
                                             rcases hx with hx | hx
                                             · exact False.elim (h hx)
                                             · exact hx)).1
  obtain ⟨M,hM⟩ := hc.exists_bound_of_continuous
    (smooth_deriv_infty smoothTransition.contDiff).continuous
  obtain ⟨N,hN⟩ := hc.deriv.exists_bound_of_continuous
    (smooth_deriv_infty (smooth_deriv_infty smoothTransition.contDiff)).continuous
  refine ⟨max 1 (max M N), le_max_left _ _, fun x => ⟨?_,?_⟩⟩
  · exact (show |deriv smoothTransition x| ≤ M by simpa only [Real.norm_eq_abs] using hM x).trans
      ((le_max_left M N).trans (le_max_right _ _))
  · exact (show |deriv (deriv smoothTransition) x| ≤ N by simpa only [Real.norm_eq_abs] using hN x).trans
      ((le_max_right M N).trans (le_max_right _ _))

end ScalarConductivity

end

end OAI
end

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

def twoFluxDivergence {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : Fin 3 → E) (F : Fin 5 → SmoothScalar E) : Fin 2 → SmoothScalar E :=
  ![smoothDirection (v 0) (F 0) + smoothDirection (v 1) (F 1) +
      smoothDirection (v 2) (F 3),
    smoothDirection (v 0) (F 1) + smoothDirection (v 1) (F 2) +
      smoothDirection (v 2) (F 4)]

def transverseFlux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : Fin 3 → E) (ψ η ω : SmoothScalar E) : Fin 5 → SmoothScalar E :=
  ![smoothDirection (v 2) ψ, smoothDirection (v 2) η, smoothDirection (v 2) ω,
    -(smoothDirection (v 0) ψ) - smoothDirection (v 1) η,
    -(smoothDirection (v 0) η) - smoothDirection (v 1) ω]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_LocalizedFirstPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ScalarConductivity

def localizedFirstPotential {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (χ : SmoothScalar E) (L : E →L[ℝ] ℝ) (H : SmoothScalar ℝ) (k : ℝ) :
    SmoothScalar E := k⁻¹ • (χ * smoothPhase (k • L) H)

def localizedSecondPotential {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (χ : SmoothScalar E) (L : E →L[ℝ] ℝ) (H : SmoothScalar ℝ) (k : ℝ) :
    SmoothScalar E := (k ^ 2)⁻¹ • (χ * smoothPhase (k • L) H)

open Filter Topology

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_TwoFluxColumns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ScalarConductivity

def twoFluxColumns {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : Fin 5 → SmoothScalar E) : Fin 2 → Fin 3 → SmoothScalar E :=
  ![![G 0, G 1, G 3], ![G 1, G 2, G 4]]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_VariationalDN
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ScalarConductivity

def productFactorMinus (M : ℝ) (α : DiagonalTriple) (i : Fin 3) : ℝ :=
  1 - Real.sqrt (1 - α i / M)

def productFactorPlus (M : ℝ) (α : DiagonalTriple) (i : Fin 3) : ℝ :=
  1 + Real.sqrt (1 - α i / M)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_PreliminaryQ
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity

open MeasureTheory
open scoped ENNReal
section
def preliminaryQ (i : Fin 3) (A α : DiagonalTriple) : ℝ := α i / A i

def preliminaryB (i : Fin 3) (A α : DiagonalTriple) : DiagonalTriple :=
  fun j => if j = i then A i else preliminaryQ i A α * α j

def stretchedDiagonal (i : Fin 3) (q : ℝ) (B : DiagonalTriple) : DiagonalTriple :=
  fun j => if j = i then q * B j else B j / q

end
open Matrix Filter Topology

def orthogonalFrames : Set Mat3 := {Q | Qᵀ * Q = 1 ∧ Q * Qᵀ = 1}

def spectralExtension (U : Set (Fin 3 → ℝ)) : Set Symmetric3 :=
  { A | ∃ Q ∈ orthogonalFrames, ∃ α ∈ U, A.val = Q * diagonal α * Qᵀ }

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_Symmetrize
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

def repairError {m : Type*} [Fintype m] [DecidableEq m]
    (A : Symmetric3) (E R : Matrix (Fin 3) m ℝ) : Symmetric3 :=
  ⟨A.val + symmetrize (symmetricCorrection E R ((Eᵀ * E)⁻¹ * Eᵀ)), by
    rw [Matrix.isHermitian_iff_isSymm]
    exact (Matrix.isHermitian_iff_isSymm.mp A.property).add (symmetrize_isSymm _)⟩

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_CrossingHxx
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

def pushFlux {m : Type*} [Fintype m] (J : Mat3) (F : Matrix (Fin 3) m ℝ) :
    Matrix (Fin 3) m ℝ := J.det⁻¹ • (J * F)

def repairPushed {m : Type*} [Fintype m] [DecidableEq m]
    (A : Symmetric3) (J : Mat3) (E F : Matrix (Fin 3) m ℝ) : Symmetric3 :=
  repairError A (pushGradient J E) (pushFlux J F - A.val * pushGradient J E)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_SmoothCompose
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
open Filter Topology

def nonlinearFirstPotential {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (χ φ : SmoothScalar E) (H : SmoothScalar ℝ) (k : ℝ) : SmoothScalar E :=
  k⁻¹ • (χ * smoothCompose (k • φ) H)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_CrossingBlock
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory

def crossingValue (L z x y : ℝ) : ℝ :=
  crossingFirst L z*cos x + crossingSecond L z*cos (2*y)

def crossingCurrentX (L z x y : ℝ) : ℝ :=
  -9*crossingFirst L z*sin x - crossingResidualSecond L z*cos x*sin x*cos (2*y) -
    2*crossingResidualFirst L z*(sin (2*y))^2*sin x

def crossingCurrentY (L z x y : ℝ) : ℝ :=
  -(crossingSecond L z/2)*sin (2*y) - crossingResidualSecond L z*(sin x)^2*sin (2*y) -
    (crossingResidualFirst L z/2)*cos (2*y)*sin (2*y)*cos x

def crossingCurrentZ (L z x y : ℝ) : ℝ :=
  deriv (crossingFirst L) z*cos x + deriv (crossingSecond L) z*cos (2*y)

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

def potentialCurl (S : Fin 3 → Fin 3 → Coord3 → ℝ) (x : Coord3) (i : Fin 3) : ℝ :=
  ∑ j, direction (Pi.single j 1) (S i j) x

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

def crossingValue3 (L : ℝ) (a b : Fin 3) (x : Coord3) : ℝ :=
  crossingValue L (x 0) (x a) (x b)

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

local instance endingCoordinateTransportMeasurableSpace : MeasurableSpace Mat3 :=
  inferInstanceAs (MeasurableSpace (Fin 3 → Fin 3 → ℝ))

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_TorusNonresonance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity

section
open Set MeasureTheory

def torusResonanceForm (h l : Fin 2 → ℤ) : (Fin 3 → ℝ) →ₗ[ℝ] ℝ where
  toFun s := torusQuadratic s h-torusQuadratic s l
  map_add' _ _ := by simp only [torusQuadratic,Pi.add_apply]; ring
  map_smul' _ _ := by simp only [torusQuadratic,Pi.smul_apply,smul_eq_mul,RingHom.id_apply]; ring

end

open Set

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_BoxEnergyPoincare
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.instCoeFunSubtypeForallBox3RealMemSubmoduleCentralSmoothFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory

def cubeEnergyDensity (f : Box3 → ℝ) (z : Box3) : ℝ :=
  (cubePartial f ((1,0),0) z)^2+(cubePartial f ((0,1),0) z)^2+
    (cubePartial f ((0,0),1) z)^2

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

def wallParticularNumerator (d : E) (v r₁ r₂ : E × ℝ → ℝ) (p : E × ℝ) : ℝ :=
  wallPrimitive (fun q => r₂ q-wallAlong d (fun q => wallPrimitive r₁ q*wallDerivative v q) q) p
    -wallPrimitive r₁ p*wallAlong d v p

lemma wallParticularNumerator_zero [ProperSpace E] (d : E) (v r₁ r₂ : E × ℝ → ℝ) (x : E) :
    wallParticularNumerator d v r₁ r₂ (x,0)=0 := by
  simp only [wallParticularNumerator,wallPrimitive_zero,zero_mul,sub_zero]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_CylinderGreen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus

lemma smoothFiniteAxis_memLp {q : ℝ → ℂ} (hq : Continuous q) (R : ℝ) :
    MemLp q 2 (FiniteAxisMeasure R) := by
  apply (memLp_two_iff_integrable_sq_norm hq.aestronglyMeasurable).mpr
  exact (hq.norm.pow 2).integrableOn_Icc.mono_set Ioc_subset_Icc_self

def smoothFiniteAxisLp {q : ℝ → ℂ} (hq : Continuous q) (R : ℝ) : FiniteAxisL2 R :=
  (smoothFiniteAxis_memLp hq R).toLp q

lemma smoothFiniteAxisLp_ae {q : ℝ → ℂ} (hq : Continuous q) (R : ℝ) :
    smoothFiniteAxisLp hq R=ᵐ[FiniteAxisMeasure R] q :=
  (smoothFiniteAxis_memLp hq R).coeFn_toLp

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

local instance cylinderModeGreenMeasureSpace_rec4dcf_1 : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
def flatCylinderEnergy (s : Fin 3 → ℝ) {R : ℝ} (u v : FiniteCylinderJets R) : ℂ :=
  inner ℂ (u 1) (v 1)+(s 0:ℂ)*inner ℂ (u 2) (v 2)+
    (s 1:ℂ)*(inner ℂ (u 2) (v 3)+inner ℂ (u 3) (v 2))+
    (s 2:ℂ)*inner ℂ (u 3) (v 3)

lemma flatCylinderEnergy_continuous_left (s : Fin 3 → ℝ) {R : ℝ} (v : FiniteCylinderJets R) :
    Continuous (fun u => flatCylinderEnergy s u v) := by
  unfold flatCylinderEnergy
  fun_prop

lemma flatCylinderEnergy_continuous_right (s : Fin 3 → ℝ) {R : ℝ} (u : FiniteCylinderJets R) :
    Continuous (fun v => flatCylinderEnergy s u v) := by
  unfold flatCylinderEnergy
  fun_prop

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_CylinderSeriesGreen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

def flatCylinderEnergyLeftCLM (s : Fin 3 → ℝ) {R : ℝ} (v : FiniteCylinderJets R) :
    FiniteCylinderJets R →L[ℝ] ℂ where
  toFun u := flatCylinderEnergy s u v
  map_add' u w := by
    simp only [flatCylinderEnergy,PiLp.add_apply,inner_add_left]
    ring
  map_smul' c u := by
    simp only [flatCylinderEnergy,PiLp.smul_apply,inner_smul_left_eq_smul,Complex.real_smul,RingHom.id_apply]
    ring
  cont := flatCylinderEnergy_continuous_left s v

def flatCylinderEnergyRightCLM (s : Fin 3 → ℝ) {R : ℝ} (u : FiniteCylinderJets R) :
    FiniteCylinderJets R →L[ℂ] ℂ where
  toFun v := flatCylinderEnergy s u v
  map_add' v w := by
    simp only [flatCylinderEnergy,PiLp.add_apply,inner_add_right]
    ring
  map_smul' c v := by
    simp only [flatCylinderEnergy,PiLp.smul_apply,inner_smul_right,smul_eq_mul,RingHom.id_apply]
    ring
  cont := flatCylinderEnergy_continuous_right s u

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

def smoothAxisModeJet {q : ℝ → ℂ} (hq : ContDiff ℝ (↑(⊤:ℕ∞)) q)
    (R : ℝ) (h : TorusModes) : FiniteAxisJets R :=
  WithLp.toLp 2 ![smoothFiniteAxisLp hq.continuous R,
    smoothFiniteAxisLp (hq.continuous_deriv (by simp)) R,
    (Complex.I*(h 0:ℂ))•smoothFiniteAxisLp hq.continuous R,
    (Complex.I*(h 1:ℂ))•smoothFiniteAxisLp hq.continuous R]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_CylinderPolynomial
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.spectralTraceGraph_realInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma smoothFiniteAxisLp_add {q r : ℝ → ℂ} (hq : Continuous q) (hr : Continuous r) (R : ℝ) :
    smoothFiniteAxisLp (hq.add hr) R=smoothFiniteAxisLp hq R+smoothFiniteAxisLp hr R := by
  apply Lp.ext
  filter_upwards [smoothFiniteAxisLp_ae (hq.add hr) R,smoothFiniteAxisLp_ae hq R,
    smoothFiniteAxisLp_ae hr R,Lp.coeFn_add (smoothFiniteAxisLp hq R) (smoothFiniteAxisLp hr R)]
    with t h1 h2 h3 h4
  simp only [h1,h4,h2,h3,Pi.add_apply]

lemma smoothFiniteAxisLp_smul {q : ℝ → ℂ} (hq : Continuous q) (c : ℂ) (R : ℝ) :
    smoothFiniteAxisLp (hq.const_smul c) R=c•smoothFiniteAxisLp hq R := by
  apply Lp.ext
  filter_upwards [smoothFiniteAxisLp_ae (hq.const_smul c) R,smoothFiniteAxisLp_ae hq R,
    Lp.coeFn_smul c (smoothFiniteAxisLp hq R)] with t h1 h2 h3
  simp only [h1,h3,h2,Pi.smul_apply]

lemma smoothAxisModeJet_add (q r : smoothComplexAxis) (R : ℝ) (h : TorusModes) :
    smoothAxisModeJet (smoothComplexAxis_smooth (q+r)) R h=
      smoothAxisModeJet (smoothComplexAxis_smooth q) R h+
        smoothAxisModeJet (smoothComplexAxis_smooth r) R h := by
  have hd : deriv (fun t => q t+r t)=deriv q+deriv r := by
    funext t
    exact deriv_add ((smoothComplexAxis_smooth q).differentiable (by simp) t)
      ((smoothComplexAxis_smooth r).differentiable (by simp) t)
  apply PiLp.ext
  intro j
  fin_cases j
  · exact smoothFiniteAxisLp_add (smoothComplexAxis_smooth q).continuous
      (smoothComplexAxis_smooth r).continuous R
  · change smoothFiniteAxisLp ((smoothComplexAxis_smooth (q+r)).continuous_deriv (by simp)) R=
      smoothFiniteAxisLp ((smoothComplexAxis_smooth q).continuous_deriv (by simp)) R+
        smoothFiniteAxisLp ((smoothComplexAxis_smooth r).continuous_deriv (by simp)) R
    simp only [show ((q+r : smoothComplexAxis) : ℝ → ℂ)=(fun t => q t+r t) from rfl,hd]
    exact smoothFiniteAxisLp_add _ _ R
  · change (Complex.I*(h 0:ℂ))•smoothFiniteAxisLp _ R=_
    rw [smoothFiniteAxisLp_add]
    exact smul_add _ _ _
  · change (Complex.I*(h 1:ℂ))•smoothFiniteAxisLp _ R=_
    rw [smoothFiniteAxisLp_add]
    exact smul_add _ _ _

lemma smoothAxisModeJet_smul (c : ℂ) (q : smoothComplexAxis) (R : ℝ) (h : TorusModes) :
    smoothAxisModeJet (smoothComplexAxis_smooth (c•q)) R h=
      c•smoothAxisModeJet (smoothComplexAxis_smooth q) R h := by
  have hd : deriv (fun t => c•q t)=c•deriv q := by
    funext t
    exact deriv_const_smul c ((smoothComplexAxis_smooth q).differentiable (by simp) t)
  apply PiLp.ext
  intro j
  fin_cases j
  · exact smoothFiniteAxisLp_smul (smoothComplexAxis_smooth q).continuous c R
  · change smoothFiniteAxisLp ((smoothComplexAxis_smooth (c•q)).continuous_deriv (by simp)) R=
      c•smoothFiniteAxisLp ((smoothComplexAxis_smooth q).continuous_deriv (by simp)) R
    simp only [show ((c•q : smoothComplexAxis) : ℝ → ℂ)=(fun t => c•q t) from rfl,hd]
    exact smoothFiniteAxisLp_smul _ c R
  · change (Complex.I*(h 0:ℂ))•smoothFiniteAxisLp _ R=_
    rw [smoothFiniteAxisLp_smul]
    exact smul_comm _ _ _
  · change (Complex.I*(h 1:ℂ))•smoothFiniteAxisLp _ R=_
    rw [smoothFiniteAxisLp_smul]
    exact smul_comm _ _ _

def smoothAxisModeJetL (R : ℝ) (h : TorusModes) : smoothComplexAxis →ₗ[ℂ] FiniteAxisJets R where
  toFun q := smoothAxisModeJet (smoothComplexAxis_smooth q) R h
  map_add' q r := smoothAxisModeJet_add q r R h
  map_smul' c q := smoothAxisModeJet_smul c q R h

open Set MeasureTheory Filter Topology
open scoped ENNReal

def spectralJetSingle (h : TorusModes) : SpectralModeFiber →ₗᵢ[ℂ] SpectralJet TorusModes where
  toFun a := WithLp.toLp 2 (fun j => (lp.single 2 h (a j) : SpectralL2 TorusModes))
  map_add' a b := by
    apply PiLp.ext
    intro j
    exact lp.single_add (E := fun _ : TorusModes => ℂ) 2 h (a j) (b j)
  map_smul' c a := by
    apply PiLp.ext
    intro j
    exact lp.single_smul (E := fun _ : TorusModes => ℂ) 2 h c (a j)
  norm_map' a := by
    have he : ‖WithLp.toLp 2 (fun j : Fin 2 => (lp.single 2 h (a j) : SpectralL2 TorusModes))‖^2=‖a‖^2 := by
      simp only [PiLp.norm_sq_eq_of_L2,lp.norm_single (by norm_num : (0:ℝ≥0∞)<2)]
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp he

def weightedModeFiberL (s : Fin 3 → ℝ) (h : TorusModes) : ℂ →ₗ[ℂ] SpectralModeFiber where
  toFun a := WithLp.toLp 2 ![a,(Real.sqrt (torusRate s h):ℂ)*a]
  map_add' a b := by apply PiLp.ext; intro j; fin_cases j <;> simp [mul_add]
  map_smul' c a := by
    apply PiLp.ext
    intro j
    fin_cases j <;> simp [mul_comm,mul_assoc]

def spectralTraceSingleL (s : Fin 3 → ℝ) (h : TorusModes) :
    ℂ →ₗ[ℂ] spectralTraceGraph (torusRate s) :=
  ((spectralJetSingle h).toLinearMap.comp (weightedModeFiberL s h)).codRestrict _ (by
    intro a k
    change (lp.single 2 h ((Real.sqrt (torusRate s h):ℂ)*a) : SpectralL2 TorusModes) k=
      (Real.sqrt (torusRate s k):ℂ)*(lp.single 2 h a : SpectralL2 TorusModes) k
    by_cases hk : k=h
    · subst k; simp
    · simp only [lp.single_apply,Pi.single_eq_of_ne hk,mul_zero])

def cylinderPolynomialTraceL (s : Fin 3 → ℝ) (t : ℝ) :
    (TorusModes →₀ smoothComplexAxis) →ₗ[ℂ] spectralTraceGraph (torusRate s) :=
  Finsupp.lsum ℂ (fun h => (spectralTraceSingleL s h).comp
    ((LinearMap.proj t).comp smoothComplexAxis.subtype))

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_CylinderCompletedGreen
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.spectralTraceGraph_realInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

def spectralWeightedPairL (s : Fin 3 → ℝ) (g : SpectralL2 TorusModes) :
    spectralTraceGraph (torusRate s) →L[ℂ] ℂ :=
  (innerSL ℂ g).comp ((PiLp.proj 2 (fun _ : Fin 2 => SpectralL2 TorusModes) 1).comp
    (spectralTraceGraph (torusRate s)).subtypeL)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_CylinderSlopeGreen
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.spectralTraceGraph_realInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

def spectralMeanCLM (s : Fin 3 → ℝ) : spectralTraceGraph (torusRate s) →L[ℂ] ℂ :=
  (lp.evalCLM ℂ (fun _ : TorusModes => ℂ) 2 0).comp
    ((PiLp.proj 2 (fun _ : Fin 2 => SpectralL2 TorusModes) 0).comp
      (spectralTraceGraph (torusRate s)).subtypeL)

end ScalarConductivity



end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_SplitJacobian
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
open Matrix Set Filter Topology MeasureTheory
open scoped Matrix.Norms.Elementwise

def splitJacobian (d : Coord3) (L : Coord3 →L[ℝ] ℝ) (c z : ℝ) : Mat3 :=
  operatorMatrix (ContinuousLinearMap.id ℝ Coord3 + lineShiftGradientOperator d c (z • L))

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_NormalStretch
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

section
open Matrix Set
open scoped Matrix.Norms.Elementwise

def normalStretch (i : Fin 3) (q : ℝ) : Mat3 :=
  Matrix.diagonal (fun j => if j = i then q else 1)

end

open MeasureTheory Set Filter Topology

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_RecoverJoinChild
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

def recoverJoinChild (i : Fin 3) (θ : ℝ) (β δ : DiagonalTriple) : DiagonalTriple :=
  fun j => if j = i then θ / ((δ j)⁻¹ - (1 - θ) / β j)
    else (δ j - (1 - θ) * β j) / θ

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_BoundedMultiplier
attribute [-instance] _root_.OAI.ScalarConductivity.H10_completeSpace _root_.OAI.ScalarConductivity.H1_completeSpace _root_.OAI.ScalarConductivity.H1_isClosed _root_.OAI.ScalarConductivity.ballMeasure_finite _root_.OAI.ScalarConductivity.bumpProbability_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ScalarConductivity

theorem weakGradientL_apply_ae (u : H1) :
    (weakGradientL u : R3 → R3) =ᵐ[ballMeasure] weakGradient u :=
  jetGradient.coeFn_compLp u.val

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_MatrixFiniteLaminate
attribute [-instance] _root_.OAI.ScalarConductivity.ballMeasure_finite _root_.OAI.ScalarConductivity.bumpProbability_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
namespace ScalarConductivity

def matrixFiniteLaminate (a b : ℝ) : Set Symmetric3 :=
  spectralExtension {α | IsFiniteLaminate a b α}

open Set Filter Topology

def h10PoincareConstant : ℝ :=
  ‖jetLiftValue.compLpL 2 ballMeasure‖ * ballPoincareConstant +
    ‖jetLiftGradient.compLpL 2 ballMeasure‖ + 1

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

def jetProduct (z w : JetFiber) : JetFiber :=
  jetLiftValue (jetValue z*jetValue w) +
    jetLiftGradient (jetValue z • jetGradient w + jetValue w • jetGradient z)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_SobolevSmoothTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity

open Set MeasureTheory Filter Topology

open Set MeasureTheory Filter Topology Real

def inverseOperation : SmoothLipZero := SmoothLipZero.ofCompact inverseCorrection
  inverseCorrection_smooth inverseCorrection_compact inverseCorrection_zero

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_RadialLaplacian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity

section
open MeasureTheory Set InnerProductSpace Laplacian
open scoped RealInnerProductSpace

def radialTheta (Ψ : ℝ → ℝ) (s : ℝ) (x : WeylSpace) : ℝ :=
  Ψ (‖x‖^2/s^2)/(2*s^2)

end

open Set MeasureTheory Filter Topology InnerProductSpace Laplacian
open scoped RealInnerProductSpace

def radialProfilePrimitive (t : ℝ) : ℝ := ∫ r in t..1, radialProfile r

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_RadialWeylScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity

section
open Set Filter Topology MeasureTheory Laplacian InnerProductSpace
open scoped Convolution

def radialMollify (f : WeylSpace → ℝ) (s : ℝ) : WeylSpace → ℝ :=
  f ⋆[ContinuousLinearMap.lsmul ℝ ℝ,volume] radialEta radialProfile s

end

open Set MeasureTheory

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_L2TranslationAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory Filter Topology

open Set MeasureTheory Filter Topology
open scoped Convolution

def radialProbability (s : ℝ) : Measure WeylSpace :=
  volume.withDensity (fun x => ENNReal.ofReal (radialEta radialProfile s x))

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_MatrixOperator
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
open Matrix Set
open scoped Matrix.Norms.Elementwise

def rotatedDirection (Q : Mat3) (i : Fin 3) : Coord3 := Q *ᵥ Pi.single i 1

def rotatedPhase (Q : Mat3) (i : Fin 3) : Coord3 →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp (matrixOperator Qᵀ)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_PairedPotential
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
open Set

def pairedPotential (u : Coord3 → ℝ) (j : Fin 3) (x : Coord3) : Fin 2 → ℝ :=
  ![u x, x j]

def pairedFunctional (L : Coord3 →L[ℝ] ℝ) (j : Fin 3) : Coord3 →L[ℝ] (Fin 2 → ℝ) :=
  ContinuousLinearMap.pi ![L, ContinuousLinearMap.proj j]

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

lemma gradientColumns_parametric_smoothOn {u : P×Coord3 → Fin 2 → ℝ}
    {V : Set (P×Coord3)} (hV : IsOpen V) (hu : ContDiffOn ℝ (↑(⊤:ℕ∞)) u V) :
    ContDiffOn ℝ (↑(⊤:ℕ∞)) (fun q => gradientColumns (fderiv ℝ (fun x => u (q.1,x)) q.2)) V := by
  apply contDiffOn_pi.mpr
  intro i
  apply contDiffOn_pi.mpr
  intro j
  exact (contDiffOn_pi.mp ((spatialFDeriv_smoothOn hV hu).clm_apply contDiffOn_const)) j

end ScalarConductivity

end


end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Walls_WallHalfspaceIntegral
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.instCoeFunSubtypeForallBox3RealMemSubmoduleCentralSmoothFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma wallDerivative_slice {g : Box3 → ℝ} (hg : Differentiable ℝ g) (q : ℝ×ℝ) (z : ℝ) :
    wallDerivative g (q,z)=deriv (fun t => g (q,t)) z := by
  have hh : HasDerivAt (fun t => (q,t)) (0,1) z :=
    (hasDerivAt_const z q).prodMk (hasDerivAt_id z)
  exact ((hg (q,z)).hasFDerivAt.comp_hasDerivAt z hh).deriv.symm

lemma wallAlong_slice {f : Box3 → ℝ} (hf : Differentiable ℝ f) (d q : ℝ×ℝ) (z : ℝ) :
    wallAlong d f (q,z)=fderiv ℝ (fun p => f (p,z)) q d := by
  have hh : HasFDerivAt (fun p : ℝ×ℝ => (p,z))
      ((ContinuousLinearMap.id ℝ (ℝ×ℝ)).prod (0 : (ℝ×ℝ) →L[ℝ] ℝ)) q :=
    (hasFDerivAt_id q).prodMk (hasFDerivAt_const z q)
  change wallAlong d f (q,z)=fderiv ℝ (f∘(fun p => (p,z))) q d
  rw [((hf (q,z)).hasFDerivAt.comp q hh).fderiv]
  rfl

lemma wallAlong_integral_slice {f : Box3 → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hs : HasCompactSupport f) (d : ℝ×ℝ) (z : ℝ) :
    (∫ q,wallAlong d f (q,z))=0 := by
  let g := fun q : ℝ×ℝ => f (q,z)
  have hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g := hf.comp (contDiff_id.prodMk contDiff_const)
  have hgs : HasCompactSupport g := hasCompactSupport_prodMkRight hs z
  have hi := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure (ℝ×ℝ))) (f := fun _ : ℝ×ℝ => (1:ℝ)) (g := g) (v := d)
    (by simp)
    (by simpa using ((hg.fderiv_right (m := (↑(⊤ : ℕ∞) : WithTop ℕ∞)) (by simp)).clm_apply contDiff_const).continuous.integrable_of_hasCompactSupport (hgs.fderiv_apply ℝ d))
    (by simpa using hg.continuous.integrable_of_hasCompactSupport hgs)
    (fun p _ => differentiableAt_const 1) (fun p _ => hg.differentiable (by simp) p)
  simpa [wallAlong_slice (hf.differentiable (by simp)),g] using hi

end ScalarConductivity



namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma wallAlong_neg (f : Box3 → ℝ) (d : ℝ×ℝ) (p : Box3) :
    wallAlong d (fun q => -f q) p= -wallAlong d f p := by
  simp only [wallAlong,fderiv_fun_neg,neg_apply]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_WeakHarmonicMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

def radialGradientMass : ℝ := ∫ x, ‖fderiv ℝ (radialEta radialProfile 1) x‖

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Walls_CriticalWallResidual
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.instCoeFunSubtypeForallBox3RealMemSubmoduleCentralSmoothFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix Filter Topology

lemma wallPrimitive_tsupport_surface {K : Set (ℝ×ℝ)} (hK : IsClosed K)
    {r : Box3 → ℝ} (hr : tsupport r⊆Prod.fst ⁻¹' K) :
    tsupport (wallPrimitive r)⊆Prod.fst ⁻¹' K := by
  apply closure_minimal _ (hK.preimage continuous_fst)
  intro p hp
  by_contra hn
  have hz (t : ℝ) : r (p.1,t*p.2)=0 :=
    image_eq_zero_of_notMem_tsupport (fun (hh : (p.1,t*p.2) ∈ tsupport r) =>
      (show p.1∉K from hn) (@hr (p.1,t*p.2) hh))
  exact hp (by simp [wallPrimitive,hz])

lemma wallQuotient_tsupport_surface {K : Set (ℝ×ℝ)} (hK : IsClosed K)
    {r : Box3 → ℝ} (hr : tsupport r⊆Prod.fst ⁻¹' K) :
    tsupport (wallQuotient r)⊆Prod.fst ⁻¹' K := by
  apply closure_minimal _ (hK.preimage continuous_fst)
  intro p hp
  by_contra hn
  have hz (t : ℝ) : wallDerivative r (p.1,t*p.2)=0 := by
    dsimp [wallDerivative]
    rw [fderiv_of_notMem_tsupport ℝ (fun (hh : (p.1,t*p.2) ∈ tsupport r) =>
      (show p.1∉K from hn) (@hr (p.1,t*p.2) hh))]
    rfl
  exact hp (by simp [wallQuotient,hz])

end ScalarConductivity



end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Walls_ParametricWallTensors
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

lemma symmetricSource_zero (u : Coord3 → Fin 2 → ℝ) (j : Fin 2) :
    symmetricSource 0 u j=0 := by
  funext x
  simp [symmetricSource,coordinateDivergence]

end ScalarConductivity

end


end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_JoinHull
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
open Set Filter Topology

def joinHull (U : Set DiagonalTriple) : Set DiagonalTriple :=
  U ∪ {δ | ∃ i θ α β, 0 ≤ θ ∧ θ ≤ 1 ∧ α ∈ U ∧ β ∈ U ∧
    coordinateJoin i θ α β = δ}

def depthClass (U : Set DiagonalTriple) : ℕ → Set DiagonalTriple
  | 0 => U
  | n+1 => joinHull (depthClass U n)

def scalarNeighbourhood (a b ε : ℝ) : Set DiagonalTriple :=
  {α | IsFiniteLaminate a b α ∧ ∃ s : ℝ, ‖α - (fun _ => s)‖ < ε}

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

def permutedDilationEquiv (e : Equiv.Perm (Fin 3)) {k : ℝ} (hk : k≠0) : Coord3 ≃L[ℝ] Coord3 :=
  (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin 3 => ℝ) e.symm).trans
    (LinearEquiv.smulOfNeZero ℝ Coord3 k hk).toContinuousLinearEquiv

end ScalarConductivity

end


end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_TorusBoxFlux
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory

def torusCellIntegral (T : ℝ) (f : Coord3 → ℝ) (t : ℝ) : ℝ :=
  ∫ y in (0:ℝ)..T,∫ z in (0:ℝ)..T,f ![t,y,z]

end ScalarConductivity



end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_FlatTorusPDE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def flatTensorLaplacianCLM (s : Fin 3 → ℝ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin 2 => Fin 3 → ℝ) ℝ →L[ℝ] ℝ :=
  ContinuousMultilinearMap.apply ℝ _ ℝ ![flatAxis 0,flatAxis 0]+
  s 0 • ContinuousMultilinearMap.apply ℝ _ ℝ ![flatAxis 1,flatAxis 1]+
  (2*s 1) • ContinuousMultilinearMap.apply ℝ _ ℝ ![flatAxis 1,flatAxis 2]+
  s 2 • ContinuousMultilinearMap.apply ℝ _ ℝ ![flatAxis 2,flatAxis 2]

def flatTensorLaplacian (s : Fin 3 → ℝ) (f : (Fin 3 → ℝ) → ℝ) (x : Fin 3 → ℝ) : ℝ :=
  flatTensorLaplacianCLM s (iteratedFDeriv ℝ 2 f x)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_AngularLocalizedMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory

def periodicSourceMoment (T : ℝ) (u : Coord3 → Fin 2 → ℝ) (r : PhysicalSourcePair) : Coord3 :=
  ![∫ t,∫ y in (0:ℝ)..T,∫ z in (0:ℝ)..T,r 0 ![t,y,z],
    ∫ t,∫ y in (0:ℝ)..T,∫ z in (0:ℝ)..T,r 1 ![t,y,z],
    ∫ t,∫ y in (0:ℝ)..T,∫ z in (0:ℝ)..T,u ![t,y,z] 1*r 0 ![t,y,z]-u ![t,y,z] 0*r 1 ![t,y,z]]

end ScalarConductivity



end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_PureModeWall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology

def pureWallMode (σ lam k : ℝ) (x : Box3) : ℝ :=
  σ*exp (-lam*x.1.1)*cos (k*x.2)

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_SobolevDistribution
attribute [-instance] _root_.OAI.ScalarConductivity.bumpProbability_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

def weakValueL : H1 →L[ℝ] Lp ℝ 2 ballMeasure :=
  (jetValue.compLpL 2 ballMeasure).comp H1Space.subtypeL

lemma weakValueL_apply_ae (u : H1) :
    (weakValueL u : R3 → ℝ) =ᵐ[ballMeasure] weakValue u := jetValue.coeFn_compLp u.val

def weakDirectionL (v : R3) : H1 →L[ℝ] Lp ℝ 2 ballMeasure :=
  ((innerSL ℝ v).compLpL 2 ballMeasure).comp weakGradientL

lemma weakDirectionL_apply_ae (u : H1) (v : R3) :
    (weakDirectionL v u : R3 → ℝ) =ᵐ[ballMeasure] fun x => inner ℝ v (weakGradient u x) := by
  filter_upwards [(innerSL ℝ v).coeFn_compLp (weakGradientL u),weakGradientL_apply_ae u]
    with x hx hy
  exact hx.trans (congrArg (inner ℝ v) hy)

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_VanishingMomentChoice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Matrix Filter Topology

lemma exists_vanishing_moment_selection {P : Type*} [TopologicalSpace P]
    {p : P} {m : P → Coord3} (hm : Tendsto m (𝓝 p) (𝓝 0))
    {C : ℝ} {R : P → Coord3 → Prop}
    (he : ∀ᶠ q in 𝓝 p,∃ c : Coord3,‖c‖≤C*‖m q‖ ∧ R q c) :
    ∃ c : P → Coord3,Tendsto c (𝓝 p) (𝓝 0) ∧ ∀ᶠ q in 𝓝 p,R q (c q) := by
  classical
  have hx (q : P) : ∃ c : Coord3,
      (∃ d : Coord3,‖d‖≤C*‖m q‖ ∧ R q d) → ‖c‖≤C*‖m q‖ ∧ R q c := by
    by_cases h : ∃ d : Coord3,‖d‖≤C*‖m q‖ ∧ R q d
    · obtain ⟨c,hc⟩ := h
      exact ⟨c,fun _ => hc⟩
    · exact ⟨0,fun h' => (h h').elim⟩
  choose c hc using hx
  have hb : ∀ᶠ q in 𝓝 p,‖c q‖≤C*‖m q‖ ∧ R q (c q) := he.mono (fun q hq => hc q hq)
  refine ⟨c,?_,hb.mono (fun _ h => h.2)⟩
  apply squeeze_zero_norm' (hb.mono (fun _ h => h.1))
  simpa only [norm_zero,mul_zero] using hm.norm.const_mul C

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_TorusMoments
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

def symmetricCrossFlux (H : Coord3 → Mat3) (u : Coord3 → Fin 2 → ℝ) (x : Coord3) : Coord3 :=
  u x 1 • (H x*gradientColumns (fderiv ℝ u x)).col 0-
    u x 0 • (H x*gradientColumns (fderiv ℝ u x)).col 1

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

local instance endingJoinEllipticMeasurableSpace : MeasurableSpace Mat3 :=
  inferInstanceAs (MeasurableSpace (Fin 3 → Fin 3 → ℝ))

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
lemma cylinderL2_slice_memLp {μ : Measure ℝ} [SFinite μ] (F : CylinderL2 μ) :
    ∀ᵐ t ∂μ, MemLp (fun θ => F (t,θ)) 2 (volume : Measure (UnitAddTorus (Fin 2))) := by
  filter_upwards [(Lp.aestronglyMeasurable F).prodMk_left,
    ((Lp.memLp F).integrable_norm_pow (by decide : (2:ℕ)≠0)).prod_right_ae]
    with t ht hI
  exact (memLp_two_iff_integrable_sq_norm ht).mpr hI

lemma torusFourierCoeff_norm_sq_le {f : UnitAddTorus (Fin 2) → ℂ}
    (hf : MemLp f 2 volume) (h : TorusModes) :
    ‖mFourierCoeff f h‖^2 ≤ ∫ θ, ‖f θ‖^2 := by
  let g : TorusL2 := hf.toLp f
  have he : mFourierCoeff f h = mFourierCoeff g h := by
    unfold mFourierCoeff
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with θ hθ
    rw [hθ]
  rw [he,←mFourierBasis_repr, HilbertBasis.repr_apply_apply]
  have hN := norm_inner_le_norm (𝕜:=ℂ) (mFourierBasis (d:=Fin 2) h) g
  rw [coe_mFourierBasis,(orthonormal_mFourier (d:=Fin 2)).norm_eq_one h,one_mul] at hN
  have heN : ‖g‖^2 = ∫ θ, ‖f θ‖^2 := by
    rw [complexLp_norm_sq]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with θ hθ
    rw [hθ]
  rw [←heN]
  simpa only [coe_mFourierBasis] using pow_le_pow_left₀ (norm_nonneg _) hN 2

def cylinderCoefficient {μ : Measure ℝ} (F : CylinderL2 μ) (h : TorusModes) (t : ℝ) : ℂ :=
  mFourierCoeff (fun θ => F (t,θ)) h

lemma cylinderCoefficient_aestronglyMeasurable {μ : Measure ℝ} [SFinite μ]
    (F : CylinderL2 μ) (h : TorusModes) : AEStronglyMeasurable (cylinderCoefficient F h) μ := by
  exact (((mFourier (-h)).continuous.stronglyMeasurable.aestronglyMeasurable.comp_snd).mul
    (Lp.aestronglyMeasurable F)).integral_prod_right'

lemma cylinderCoefficient_memLp {μ : Measure ℝ} [SFinite μ]
    (F : CylinderL2 μ) (h : TorusModes) : MemLp (cylinderCoefficient F h) 2 μ := by
  apply (memLp_two_iff_integrable_sq_norm (cylinderCoefficient_aestronglyMeasurable F h)).mpr
  apply (((Lp.memLp F).integrable_norm_pow (by decide : (2:ℕ)≠0)).integral_prod_left).mono'
    ((cylinderCoefficient_aestronglyMeasurable F h).norm.pow 2)
  filter_upwards [cylinderL2_slice_memLp F] with t ht
  simpa only [Pi.pow_apply,Real.norm_eq_abs,abs_pow,abs_norm,cylinderCoefficient] using
    torusFourierCoeff_norm_sq_le ht h

def cylinderCoefficientLp {μ : Measure ℝ} [SFinite μ]
    (F : CylinderL2 μ) (h : TorusModes) : Lp ℂ 2 μ :=
  (cylinderCoefficient_memLp F h).toLp _

lemma cylinderCoefficientLp_ae {μ : Measure ℝ} [SFinite μ]
    (F : CylinderL2 μ) (h : TorusModes) :
    cylinderCoefficientLp F h =ᵐ[μ] cylinderCoefficient F h :=
  (cylinderCoefficient_memLp F h).coeFn_toLp

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_CylinderFourierGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

def cylinderJetCoefficient (R : ℝ) (J : FiniteCylinderJets R) (h : TorusModes) : FiniteAxisJets R :=
  WithLp.toLp 2 (fun j => cylinderCoefficientLp (J j) h)

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

def sourceAngularCoefficient (f : (Fin 3 → ℝ) → ℝ) (a b : ℝ)
    (h : TorusModes) (t : ℝ) : ℂ :=
  mFourierCoeff (fun θ => (f (sourceAngularCollar (a*t+b) θ) : ℂ)) h

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_TorusLeadingRealMode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory UnitAddTorus Real Complex

def realTorusCoeff (f : TorusL2) (h : Fin 2 → ℤ) : ℂ :=
  (mFourierCoeff f h+star (mFourierCoeff f (-h)))/2

def realTorusAmplitude (f : TorusL2) (h : Fin 2 → ℤ) : ℝ :=
  if h=0 then 0 else ‖realTorusCoeff f h‖

def realTorusPhase (f : TorusL2) (h : Fin 2 → ℤ) : ℝ := (realTorusCoeff f h).arg

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

def smoothModePointJet (q : ℝ → ℂ) (h : TorusModes) (j : Fin 4)
    (z : ℝ × UnitAddTorus (Fin 2)) : ℂ :=
  ![q z.1,deriv q z.1,(Complex.I*(h 0))*q z.1,(Complex.I*(h 1))*q z.1] j*mFourier h z.2

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_FourierPairFlux
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix

def normalizedFourierCoefficients (s : Fin 3 → ℝ) (lam T : ℝ)
    (a : (Fin 2 → ℤ) → ℝ) (h : Fin 2 → ℤ) : ℝ := a h*exp (-(torusRate s h-lam)*T)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_SimpleLevelNull
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

def pairMinor (u : Coord3 → Fin 2 → ℝ) (x : Coord3) : ℝ :=
  fderiv ℝ u x (Pi.single 0 1) 0*fderiv ℝ u x (Pi.single 2 1) 1-
    fderiv ℝ u x (Pi.single 2 1) 0*fderiv ℝ u x (Pi.single 0 1) 1

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_EndingJoinMiddleModel
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

def delayedInitialTensor (lam k J R : ℝ) (x : Coord3) : Mat3 :=
  fun i j => pureModeTensor (initialConnectorAngular (lam/k) (1/2) J (k*(x 0-R))) 1
    (angularAxisSwap i) (angularAxisSwap j)

lemma delayedInitialTensor_symm (lam k J R : ℝ) (x : Coord3) :
    (delayedInitialTensor lam k J R x).IsSymm := by
  ext i j
  exact congrFun (congrFun (pureModeTensor_symm _ _) (angularAxisSwap i)) (angularAxisSwap j)

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Scalarization_EndingJoinConstitution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix

def matchingFlux (D : Coord3 → Mat3) (u : Coord3 → Fin 2 → ℝ) (j : Fin 2) (x : Coord3) : Coord3 :=
  (D x*gradientColumns (fderiv ℝ u x)).col j

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_FourierFiniteEndingNormal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Real Matrix
open scoped Matrix.Norms.Elementwise

local instance fourierFiniteEndingNormalMeasurableSpace : MeasurableSpace Mat3 :=
  inferInstanceAs (MeasurableSpace (Fin 3 → Fin 3 → ℝ))

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_LeadingFrequencyAlignment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix

def normalizedAngularTensor (s : Fin 3 → ℝ) (A : Matrix (Fin 2) (Fin 2) ℤ) : Fin 3 → ℝ :=
  let a : ℝ := A 0 0
  let b : ℝ := A 0 1
  let c : ℝ := A 1 0
  let d : ℝ := A 1 1
  let M := angularNormalization A
  ![M*(s 0*d^2-2*s 1*b*d+s 2*b^2),
    M*(-s 0*c*d+s 1*(a*d+b*c)-s 2*a*b),
    M*(s 0*c^2-2*s 1*a*c+s 2*a^2)]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_SpectralExtensionMono
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

local instance spectralExtensionMonoMeasurableSpaceMat3 : MeasurableSpace Mat3 :=
  inferInstanceAs (MeasurableSpace (Fin 3 → Fin 3 → ℝ))

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_SpectralExtensionNonemptyNonempty
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

local instance spectralExtensionNonemptyMeasurableSpaceMat3 : MeasurableSpace Mat3 :=
  inferInstanceAs (MeasurableSpace (Fin 3 → Fin 3 → ℝ))

end ScalarConductivity

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
open Set Filter Topology TopologicalSpace MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

local instance generalModeFiniteEndNormalMeasurableSpace : MeasurableSpace Mat3 :=
  inferInstanceAs (MeasurableSpace (Fin 3 → Fin 3 → ℝ))

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_SpectralTerminalL2
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.spectralTraceGraph_realInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

def spectralTerminalDensity (s : Fin 3 → ℝ) {R : ℝ} (hR : 0<R)
    (f : spectralTraceGraph (torusRate s)) : SpectralL2 TorusModes :=
  sequenceMultiplier (fun h => ((Real.sqrt (torusRate s h)*Real.exp (-torusRate s h*R):ℝ):ℂ))
    (1+R⁻¹) (by positivity)
    (fun h => by simpa only [Complex.norm_real,Real.norm_eq_abs] using
      sqrt_rate_exp_bound (r:=torusRate s h) (Real.sqrt_nonneg _) hR) (f.val 1)

def terminalFluxL2CLM (s : Fin 3 → ℝ) (κ : ℝ) {R : ℝ} (hR : 0<R)
    (f : spectralTraceGraph (torusRate s)) : SpectralL2 TorusModes →L[ℝ] ℝ :=
  κ • Complex.reCLM.comp ((lp.evalCLM ℂ (fun _ : TorusModes => ℂ) 2 0).restrictScalars ℝ)-
    Complex.reCLM.comp ((innerSL ℂ (spectralTerminalDensity s hR f)).restrictScalars ℝ)

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_PhysicalSmoothTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix

def physicalSmoothCentral {φ : (Fin 3 → ℝ) → ℝ} (s : Fin 3 → ℝ)
    (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) : centralEnergySpace s :=
  ⟨centralEmbedL s ⟨φ ∘ sourcePairCLE.symm,hφ.comp sourcePairCLE.symm.contDiff⟩,
    (Submodule.le_topologicalClosure _) ⟨_,rfl⟩⟩

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_PhysicalEnergyContinuous
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped ENNReal Matrix.Norms.Elementwise

def physicalGradientComponentCLM (D : Set (Fin 3 → ℝ)) (i : Fin 3) :
    H1 →L[ℝ] Lp ℝ 2 (volume.restrict D) :=
  ((PiLp.proj 2 (fun _ : Fin 4 => ℝ) i.succ).compLpL 2 (volume.restrict D)).comp
    (physicalRestrictedJetCLM D)

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_FaceMeasure
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

def sourceFaceParameter (i j : Fin 4) (x : Fin 3 → ℝ) : ℝ × UnitAddTorus (Fin 2) :=
  (x 0,torusAngles (sourceFaceAngles i j x))

def sourceFaceWeight (i j : Fin 4) (x : Fin 3 → ℝ) : ℝ :=
  faceRayDensity 1 i (x 1)*faceRayDensity sourceRadialWidth j (x 2)

def sourceFaceMeasure (l r : ℝ) (i j : Fin 4) : Measure (ℝ × UnitAddTorus (Fin 2)) :=
  Measure.map (sourceFaceParameter i j) ((volume.restrict (sourceExtendedBox l r)).withDensity
    (fun x => ENNReal.ofReal (sourceFaceWeight i j x)))

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

def physicalEndLength (a : Fin 3 → ℝ) (i : Fin 3) : ℝ := |a i| *centralThickness

end ScalarConductivity



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

lemma physicalEndLength_pos (a : Fin 3 → ℝ) (ha : ∀ i,a i≠0) (i : Fin 3) :
    0<physicalEndLength a i :=
  mul_pos (abs_pos.mpr (ha i)) (by norm_num [centralThickness])

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_VariableBlockEnergy
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
local instance variableBlockEnergyMeasurableSpace : MeasurableSpace Mat3 :=
  inferInstanceAs (MeasurableSpace (Fin 3 → Fin 3 → ℝ))

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_LocalSmoothWeakDerivative
attribute [-instance] _root_.OAI.ScalarConductivity.bumpProbability_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

def originalWholeValue (u : H1) : WholeL2 :=
  lpZeroExtensionCLM (show MeasurableSet ball from Metric.isOpen_ball.measurableSet) (weakValueL u)

def originalWholeDirection (u : H1) (v : R3) : WholeL2 :=
  lpZeroExtensionCLM (show MeasurableSet ball from Metric.isOpen_ball.measurableSet) (weakDirectionL v u)

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_PhysicalEndOpen
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

def physicalEndOpen (i : Fin 3) : Set Coord3 :=
  Fin.cases {y | sourceCollarTime y∈Ioo 0 centralThickness}
    (fun k => {y | sourceCollarTime ((sourceChildHomeomorph (actualChildSign k)).symm y)∈Ioo (-centralThickness) 0}) i

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
local instance physicalBlockRepresentativeMeasurableSpace : MeasurableSpace Mat3 := inferInstanceAs (MeasurableSpace (Fin 3 → Fin 3 → ℝ))
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

def originalMulComponentCLM (i : Fin 4) : H1 →L[ℝ] Lp ℝ 2 ballMeasure :=
  Fin.cases ((compactMultiplierCLM hχ.continuous hc).comp weakValueL)
    (fun j => ((compactMultiplierCLM ((hχ.continuous_fderiv (by simp)).clm_apply continuous_const)
      (hc.fderiv_apply ℝ (EuclideanSpace.single j 1))).comp weakValueL)+
      ((compactMultiplierCLM hχ.continuous hc).comp (weakDirectionL (EuclideanSpace.single j 1)))) i

def originalMulJetCLM : H1 →L[ℝ] JetSpace :=
  (lpFourJetCLM ballMeasure).comp (ContinuousLinearMap.pi (originalMulComponentCLM hχ hc))

lemma originalMulComponentCLM_value (u : H1) :
    originalMulComponentCLM hχ hc 0 u=ᵐ[ballMeasure] fun x => χ x*weakValue u x := by
  filter_upwards [compactMultiplierCLM_ae hχ.continuous hc (weakValueL u),weakValueL_apply_ae u]
    with x hx hu
  exact hx.trans (congrArg (χ x*·) hu)

lemma originalMulComponentCLM_gradient (u : H1) (j : Fin 3) :
    originalMulComponentCLM hχ hc j.succ u=ᵐ[ballMeasure] fun x =>
      fderiv ℝ χ x (EuclideanSpace.single j 1)*weakValue u x+χ x*weakGradient u x j := by
  have h0 := compactMultiplierCLM_ae ((hχ.continuous_fderiv (by simp)).clm_apply continuous_const)
    (hc.fderiv_apply ℝ (EuclideanSpace.single j 1)) (weakValueL u)
  have h1 := compactMultiplierCLM_ae hχ.continuous hc (weakDirectionL (EuclideanSpace.single j 1) u)
  filter_upwards [h0,h1,weakValueL_apply_ae u,weakDirectionL_apply_ae u (EuclideanSpace.single j 1),
    Lp.coeFn_add
      (compactMultiplierCLM ((hχ.continuous_fderiv (by simp)).clm_apply continuous_const)
        (hc.fderiv_apply ℝ (EuclideanSpace.single j 1)) (weakValueL u))
      (compactMultiplierCLM hχ.continuous hc (weakDirectionL (EuclideanSpace.single j 1) u))]
    with x h0 h1 hu hd ha
  change (compactMultiplierCLM ((hχ.continuous_fderiv (by simp)).clm_apply continuous_const)
    (hc.fderiv_apply ℝ (EuclideanSpace.single j 1)) (weakValueL u)+
    compactMultiplierCLM hχ.continuous hc (weakDirectionL (EuclideanSpace.single j 1) u)) x=_
  rw [ha]
  simp only [Pi.add_apply,h0,h1,hu,hd,EuclideanSpace.inner_single_left,RCLike.conj_to_real,one_mul]

lemma originalMulJetCLM_ae (u : H1) :
    originalMulJetCLM hχ hc u=ᵐ[ballMeasure] fun x =>
      WithLp.toLp 2 (Fin.cases (χ x*weakValue u x)
        (fun j => fderiv ℝ χ x (EuclideanSpace.single j 1)*weakValue u x+χ x*weakGradient u x j)) := by
  filter_upwards [lpFourJetCLM_ae ballMeasure (fun i => originalMulComponentCLM hχ hc i u),
    originalMulComponentCLM_value hχ hc u,ae_all_iff.mpr (originalMulComponentCLM_gradient hχ hc u)]
    with x hj hv hg
  change lpFourJetCLM ballMeasure (fun i => originalMulComponentCLM hχ hc i u) x=_
  rw [hj]
  ext i
  exact Fin.cases hv hg i

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_SobolevMaximum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Real

def upperTransition (M : ℝ) (hM : 0≤M) : SmoothLipZero := by
  let C := Classical.choose exists_transition_derivative_bound
  have hc := Classical.choose_spec exists_transition_derivative_bound
  refine ⟨upperTransitionFun M,upperTransitionFun_smooth M,?_,C,by linarith [hc.1],?_⟩
  · exact smoothTransition.zero_of_nonpos (by linarith)
  · intro r
    rw [upperTransitionFun_deriv,Real.norm_eq_abs]
    exact (hc.2 (r-M)).1

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_SobolevGaugeTransform
attribute [-instance] _root_.OAI.ScalarConductivity.bumpProbability_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

def gaugeCoefficient (a : R3 → ℝ) (w : H1) (x : R3) : ℝ := a x*(1+weakValue w x)^2

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

def voltageGradientComponentJet (j : Fin 2) : FieldVector →L[ℝ] JetFiber :=
  ({ toFun := fun v => WithLp.toLp 2 (Fin.cases 0 (fun i => v (i,j)))
     map_add' := by intro v w; ext i; refine Fin.cases ?_ (fun k => ?_) i <;> simp
     map_smul' := by intro c v; ext i; refine Fin.cases ?_ (fun k => ?_) i <;> simp } :
    FieldVector →ₗ[ℝ] JetFiber).toContinuousLinearMap

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

def originalVoltageGradient (j : Fin 2) : JetFiber →L[ℝ] FieldVector :=
  ({ toFun := fun w => WithLp.toLp 2 (fun ik => if ik.2=j then w ik.1.succ else 0)
     map_add' := by intro w v; ext k; by_cases h : k.2=j <;> simp [h]
     map_smul' := by intro c w; ext k; by_cases h : k.2=j <;> simp [h] } :
    JetFiber →ₗ[ℝ] FieldVector).toContinuousLinearMap

def originalCartesianJetCLM (U : Set Coord3) : JetSpace →L[ℝ] Lp JetFiber 2 (volume.restrict U) :=
  (lpRestrictionCLM U).comp
    (((Lp.compMeasurePreservingₗᵢ ℝ (WithLp.toLp 2 : Coord3 → R3)
      (PiLp.volume_preserving_toLp (Fin 3))).toContinuousLinearMap).comp
      (lpZeroExtensionCLM Metric.isOpen_ball.measurableSet))

end ScalarConductivity

end
end

end OAI
end


