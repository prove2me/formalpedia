-- Prove2me | Definitions.Def_OAIQ059C001
-- name    : OAIQ059C001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T21:31:57.593623+00:00
-- url     : https://prove2.me/theorems/59db6a7b-4c5c-45aa-9661-9c3957cc6397
-- title:
--   Definitions bundle OAIQ059C001 of the split of OpenAI, Nonuniqueness for bounded measurable scalar conductivities in three dimensions (result family 365)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ScalarConductivity.main_nonuniqueness`, carved from OpenAI's openai/math development (OpenAI, *Nonuniqueness for bounded measurable scalar conductivities in three dimensions (result family 365)*, OpenAI Math Release, September 23, 2026, result family 365, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 408 declarations of OpenAI's Lean: 152 definitions, 2 inductive types or structures, 5 instances and 249 theorems. The definitions and types are `OAI.ScalarConductivity.BoundedSmooth`, `OAI.ScalarConductivity.CylinderL2`, `OAI.ScalarConductivity.DiagonalTriple`, `OAI.ScalarConductivity.EndAxisL2`, `OAI.ScalarConductivity.EndAxisMeasure`, `OAI.ScalarConductivity.FieldVector`, `OAI.ScalarConductivity.FiniteAxisJets`, `OAI.ScalarConductivity.FiniteAxisL2`, `OAI.ScalarConductivity.FiniteAxisMeasure`, `OAI.ScalarConductivity.FiniteCylinderJets`, `OAI.ScalarConductivity.H1JetOn`, `OAI.ScalarConductivity.HarmonicPairRegularOn`, `OAI.ScalarConductivity.IsFiniteLaminate`, `OAI.ScalarConductivity.LocalLipAt`, `OAI.ScalarConductivity.RadialMeanOn`, `OAI.ScalarConductivity.SmoothLipZero`, `OAI.ScalarConductivity.SmoothLipZero.ofCompact`, `OAI.ScalarConductivity.SpatialBump`, `OAI.ScalarConductivity.SpectralModeFiber`, `OAI.ScalarConductivity.TorusL2`, `OAI.ScalarConductivity.TorusRealPlane`, `OAI.ScalarConductivity.UniformC1Bound`, `OAI.ScalarConductivity.WeakL2Direction`, `OAI.ScalarConductivity.WeaklyHarmonicOn`, `OAI.ScalarConductivity.WeightedAnnihilation`, `OAI.ScalarConductivity.WeylSpace`, `OAI.ScalarConductivity.WholeJetSpace`, `OAI.ScalarConductivity.WholeL2`, `OAI.ScalarConductivity.affineCylinderIntegralMeasureSpace`, `OAI.ScalarConductivity.affineEndCoordinates`, `OAI.ScalarConductivity.affineEndPullback`, `OAI.ScalarConductivity.affineEndTime`, `OAI.ScalarConductivity.airySymbol`, `OAI.ScalarConductivity.angularAxisSwap`, `OAI.ScalarConductivity.angularCoefficientMeasureSpace`, `OAI.ScalarConductivity.angularFrequencyEquiv`, `OAI.ScalarConductivity.angularGraphMeasureSpace`, `OAI.ScalarConductivity.angularInteger`, `OAI.ScalarConductivity.angularInverseMatrix`, `OAI.ScalarConductivity.angularJetFiniteCylinderMeasureSpace` and 114 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `Conductivity_Branching_AlignedEndingRegularity`, `Conductivity_Branching_AttachedEndLinear`, `Conductivity_Branching_BranchOutputNormalization`, `Conductivity_Branching_CascadeCoefficient`, `Conductivity_Branching_CascadeGeometry`, `Conductivity_Branching_CascadeProfile`, `Conductivity_Branching_CentralJoinCover`, `Conductivity_Branching_ChildCentralL2`, `Conductivity_Branching_CollarMeasureTransport`, `Conductivity_Branching_CrossingBlock`, `Conductivity_Branching_DelayedEndingRegularity`, `Conductivity_Branching_Ending`, `Conductivity_Branching_EndingCoordinateTransport`, `Conductivity_Branching_PhysicalAttachedAssembly`, `Conductivity_Flux_AttachedFlatTensor`, `Conductivity_Flux_BranchTerminalFluxIntegral`, `Conductivity_Flux_CascadeTensorBounds`, `Conductivity_Flux_CentralCylinderGreen`, `Conductivity_Flux_PhysicalBlockTensor`, `Conductivity_Flux_PhysicalEndDifferential`, `Conductivity_Flux_PhysicalTensorPatch`, `Conductivity_Flux_PiolaFluxContDiff`, `Conductivity_Fourier_AngularFourierConjugacy`, `Conductivity_Fourier_AngularIntegratedTrace`, `Conductivity_Fourier_AngularNormalTrace`, `Conductivity_Fourier_AngularPhaseTranslation`, `Conductivity_Fourier_AttachedEndPoisson`, `Conductivity_Fourier_AttachedPeriodicFlux`, `Conductivity_Fourier_AttachedPeriodicGreen`, `Conductivity_Fourier_CascadePeriodicity`, `Conductivity_Fourier_CollarAngularInverse`, `Conductivity_Fourier_CylinderFourier`, `Conductivity_Fourier_EndPoissonJets`, `Conductivity_Fourier_EndPoissonRepresentative`, `Conductivity_Fourier_ModeConnector`, `Conductivity_Fourier_PureMode`, `Conductivity_Fourier_SmoothAngularCutoff`, `Conductivity_Fourier_SpectralTrace`, `Conductivity_Fourier_TorusFlatMode`, `Conductivity_Fourier_TorusFourierSmooth`, `Conductivity_Fourier_TorusPoissonContinuous`, `Conductivity_Fourier_TorusPoissonFlow`, `Conductivity_Geometry_AffineCylinder`, `Conductivity_Geometry_AffineCylinderIntegral`, `Conductivity_Geometry_BoxIteration`, `Conductivity_Geometry_BoxMomentRightInverse`, `Conductivity_Geometry_CollarInteriorFacts`, `Conductivity_Geometry_CollarLocalInverse`, `Conductivity_Geometry_CollarReverseBound`, `Conductivity_Geometry_CylinderJetOrthogonal`, `Conductivity_Geometry_CylinderPolynomial`, `Conductivity_Geometry_FlatTorusPDE`, `Conductivity_Geometry_MatrixPerturbInverse`, `Conductivity_Geometry_RectanglePoincare`, `Conductivity_Geometry_SmoothCollarRate`, `Conductivity_Geometry_SmoothCollarTrace`, `Conductivity_Geometry_TorusDirectionalDerivative`, `Conductivity_Geometry_TorusExponential`, `Conductivity_Geometry_TorusFaceIntegration`, `Conductivity_Geometry_UnitBoxAverage`, `Conductivity_Sobolev_BoundedMultiplier`, `Conductivity_Sobolev_CollarLpPullback`, `Conductivity_Sobolev_CompactLipschitzH1`, `Conductivity_Sobolev_IntervalTraceEnergy`, `Conductivity_Sobolev_LocalJoinedH1`, `Conductivity_Sobolev_LpExtension`, `Conductivity_Sobolev_LpFourJet`, `Conductivity_Sobolev_NonlinearLp`, `Conductivity_Sobolev_ParentCompletionJoin`, `Conductivity_Sobolev_SobolevGaugeTransform`, `Conductivity_Sobolev_SobolevSmoothOperations`, `Conductivity_Sobolev_SobolevSmoothTests`, `Conductivity_Sobolev_SobolevTraceChain`, `Conductivity_Sobolev_WallParticular`, `Conductivity_Sources_AngularCoefficient`, `Conductivity_Sources_AngularGraph`, `Conductivity_Sources_AngularJet`, `Conductivity_Sources_NestedGeometry`, `Conductivity_Sources_ParametricSymmetricSources`, `Conductivity_Variational_AffineLayer`, `Conductivity_Variational_AirySymbol`, `Conductivity_Variational_AxialDecayL2`, `Conductivity_Variational_CentralSmoothTrace`, `Conductivity_Variational_ChangeOld`, `Conductivity_Variational_CompactBridge`, `Conductivity_Variational_CompactFiberDecomposition`, `Conductivity_Variational_CompactFiberPrimitive`, `Conductivity_Variational_CompactMomentPerturbation`, `Conductivity_Variational_CompactParametricBounds`, `Conductivity_Variational_CompletedPotential`, `Conductivity_Variational_CrossingEstimates`, `Conductivity_Variational_CrossingHxx`, `Conductivity_Variational_CrossingProfiles`, `Conductivity_Variational_FieldVector`, `Conductivity_Variational_FieldVectorCLM`, `Conductivity_Variational_FiniteMomentTransfer`, `Conductivity_Variational_HarmonicRankAffine`, `Conductivity_Variational_L2TranslationAverage`, `Conductivity_Variational_LocalSmoothSeries`, `Conductivity_Variational_MatrixFiniteLaminate`, `Conductivity_Variational_NormalStretch`, `Conductivity_Variational_ParametricDiffeomorph`, `Conductivity_Variational_ParametricSpatialDerivative`, `Conductivity_Variational_PhysicalEndLocalLipschitz`, `Conductivity_Variational_PhysicalRealTrace`, `Conductivity_Variational_PhysicalTestEnergy`, `Conductivity_Variational_RadialLaplacian`, `Conductivity_Variational_RadialWeylScale`, `Conductivity_Variational_ScaledSmoothSeries`, `Conductivity_Variational_SmoothNormalizedEndFamily`, `Conductivity_Variational_UniformC1Bounds`, `Conductivity_Variational_UnitSquarePoincare`, `Conductivity_Variational_VariationalDN`, `Conductivity_Variational_WeakHarmonicClassical`, `Conductivity_Variational_WeakWeyl`, `Conductivity_Variational_WholeBallJet`, `Conductivity_Variational_WholeWeakClosure`, `Conductivity_Walls_LocalizedMatchedSeam`, `Conductivity_Walls_SeamCutoff`, `Conductivity_Walls_SeamL2`, `Conductivity_Walls_WallMomentIndependence`, `Conductivity_Walls_WallSurfaceMomentInverse`.
--
--   **Imports.** It imports the published bundle `Def_Conductivity`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ059C003`, `OAIQ059C004` and `OAIQ059C005`.
-- source:
--   OpenAI, Nonuniqueness for bounded measurable scalar conductivities in three dimensions (result family 365), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 365; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-for-Bounded-Measurable-Scalar-Conductivities-in-Three-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_Conductivity

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_ModeConnector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory

def connectorRate (K z : ℝ) : ℝ :=
  1/2 + (5/2)*smoothTransition ((z-1)/K)

def connectorProfile (K z : ℝ) : ℝ :=
  exp (-(∫ t in (0 : ℝ)..z, connectorRate K t))

def connectorAngular (K z : ℝ) : ℝ :=
  deriv (deriv (connectorProfile K)) z / connectorProfile K z

end ScalarConductivity

end

end OAI
end

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

lemma smooth_deriv_infty {f : ℝ → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (deriv f) :=
  (contDiff_infty_iff_deriv.mp hf).2

def crossingOn (L z : ℝ) : ℝ := smoothTransition (4*z/L+3)
def crossingOff (L z : ℝ) : ℝ := 1 - smoothTransition (4*z/L-2)

def crossingFirst (L z : ℝ) : ℝ := crossingOff L z * exp (-3*z)
def crossingSecond (L z : ℝ) : ℝ := crossingOn L z * exp (-z)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_CascadeProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory

def cascadeProfile (L K t : ℝ) : ℝ :=
  crossingOn L (t/2+L) * connectorProfile K t * crossingOff L (t-(K+2+L))

def cascadeRatio (L K : ℝ) : ℝ := exp (-4*L)*connectorProfile K (K+2)

def cascadeLength (L K : ℝ) : ℝ := K+2+2*L

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_AirySymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ScalarConductivity
open Matrix

def airySymbol (ξ : Fin 3 → ℝ) : Fin 5 → ℝ :=
  ![ξ 1 ^ 2, -(ξ 0 * ξ 1), ξ 0 ^ 2, 0, 0]

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

abbrev DiagonalTriple := Fin 3 → ℝ

def coordinateJoin (i : Fin 3) (θ : ℝ) (α β : DiagonalTriple) : DiagonalTriple :=
  fun j => if j = i then (θ / α j + (1 - θ) / β j)⁻¹
    else θ * α j + (1 - θ) * β j

inductive IsFiniteLaminate (a b : ℝ) : DiagonalTriple → Prop
  | scalar (s : ℝ) (ha : a < s) (hb : s < b) : IsFiniteLaminate a b (fun _ => s)
  | join (i : Fin 3) (θ : ℝ) (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1)
      {α β : DiagonalTriple} (hα : IsFiniteLaminate a b α)
      (hβ : IsFiniteLaminate a b β) : IsFiniteLaminate a b (coordinateJoin i θ α β)

def laminateUpper (C : ℝ) : ℝ := 16 * (2 * C)

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

section
open Real

def crossingHxx (D J R l m x y : ℝ) : ℝ :=
  R / (D * l ^ 2) * cos (l*x) * cos (m*y) -
    2*R*J / (D^2*l^2) * sin (m*y)^2

def crossingHxy (D R l m x y : ℝ) : ℝ :=
  2*R / (D*l*m) * sin (l*x) * sin (m*y)

end

open Matrix Set Filter Topology
open scoped Matrix.Norms.Elementwise

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

lemma sin_cos_iterated_bound (n : ℕ) (x : ℝ) :
    ‖iteratedDeriv n sin x‖ ≤ 1 ∧ ‖iteratedDeriv n cos x‖ ≤ 1 := by
  induction n with
  | zero => simpa using And.intro (abs_sin_le_one x) (abs_cos_le_one x)
  | succ n ih => simpa only [iteratedDeriv_add_one_sin,iteratedDeriv_add_one_cos,
      Pi.neg_apply,norm_neg] using ih.symm

lemma linear_comp_iterated_bound {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → ℝ} (g : F →L[ℝ] E)
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) {order : ℕ} {C : ℝ}
    (hC : ∀ x, ‖iteratedFDeriv ℝ order f x‖ ≤ C)
    (x : F) : ‖iteratedFDeriv ℝ order (f ∘ g) x‖ ≤ C*‖g‖^order := by
  rw [g.iteratedFDeriv_comp_right ((contDiff_infty.mp hf) order) x le_rfl]
  exact ((iteratedFDeriv ℝ order f (g x)).norm_compContinuousLinearMap_le (fun _ => g)).trans
    (by simpa using mul_le_mul_of_nonneg_right (hC (g x)) (by positivity : 0≤‖g‖^order))

def BoundedSmooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → ℝ) : Prop :=
  ContDiff ℝ (↑(⊤ : ℕ∞)) f ∧ ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖iteratedFDeriv ℝ n f x‖ ≤ C

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

def cascadePhase (D k : ℝ) (j : ℕ) (t : ℝ) : ℝ :=
  (2:ℝ)^j*(k*t-2*D)+2*D

def cascadeAxis (j : ℕ) : Fin 3 := if Even j then 1 else 2

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_CrossingEstimates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory

def crossingResidualFirst (L z : ℝ) : ℝ :=
  deriv (deriv (crossingFirst L)) z - 9*crossingFirst L z

def crossingResidualSecond (L z : ℝ) : ℝ :=
  deriv (deriv (crossingSecond L)) z - crossingSecond L z

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

def crossingXX (L z x y : ℝ) : ℝ :=
  9 + crossingHxx (exp (-3*z)) (crossingSecond L z) (crossingResidualSecond L z) 1 2 x y

def crossingYY (L z x y : ℝ) : ℝ :=
  1/4 + crossingHxx (exp (-z)) (crossingFirst L z) (crossingResidualFirst L z) 2 1 y x

def crossingXY (L z x y : ℝ) : ℝ :=
  crossingHxy (exp (-3*z)) (crossingResidualSecond L z) 1 2 x y +
  crossingHxy (exp (-z)) (crossingResidualFirst L z) 2 1 y x

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

def pureModeTensor (q : ℝ) (a : Fin 3) : Matrix (Fin 3) (Fin 3) ℝ :=
  diagonal (fun i => if i=a then q else 1)

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

lemma pureModeTensor_symm (q : ℝ) (a : Fin 3) : (pureModeTensor q a).IsSymm := by
  exact isSymm_diagonal _

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

local instance cascadeCoefficientMeasurableSpace : MeasurableSpace (Matrix (Fin 3) (Fin 3) ℝ) :=
  inferInstanceAs (MeasurableSpace (Fin 3 → Fin 3 → ℝ))

lemma exists_cascade_index (D k t : ℝ) :
    ∃ n : ℕ, cascadePhase D k n t ≤ D ∨ 2*D ≤ k*t := by
  by_cases ht : 2*D ≤ k*t
  · exact ⟨0,Or.inr ht⟩
  · obtain ⟨n,hn⟩ := pow_unbounded_of_one_lt (D/(2*D-k*t)) (by norm_num : (1:ℝ)<2)
    refine ⟨n,Or.inl ?_⟩
    have hh := (div_le_iff₀ (by linarith : 0<2*D-k*t)).mp hn.le
    unfold cascadePhase
    nlinarith

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

def initialConnectorRate (a b K t : ℝ) : ℝ :=
  a+(b-a)*smoothTransition ((t-1)/K)

def initialConnectorProfile (a b K t : ℝ) : ℝ :=
  exp (-(∫ r in (0:ℝ)..t,initialConnectorRate a b K r))

def initialConnectorAngular (a b K t : ℝ) : ℝ :=
  (initialConnectorRate a b K t)^2-deriv (initialConnectorRate a b K) t

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

def angularAxisSwap : Equiv.Perm (Fin 3) := Equiv.swap 1 2

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_TorusExponential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology

def torusSize (h : Fin 2 → ℤ) : ℝ := |(h 0:ℝ)|+|(h 1:ℝ)|

lemma torusSize_nonneg (h : Fin 2 → ℤ) : 0≤torusSize h := by unfold torusSize; positivity

lemma int_exp_summable {r : ℝ} (hr : 0 < r) :
    Summable (fun z : ℤ => exp (-r*|(z:ℝ)|)) := by
  rw [summable_int_iff_summable_nat_and_neg]
  have hn : Summable (fun n : ℕ => exp (-r*(n:ℝ))) := by
    simpa only [mul_comm (-r)] using summable_exp_nat_mul_iff.mpr (neg_neg_of_pos hr)
  constructor <;> simpa using hn

lemma torus_exp_summable {r : ℝ} (hr : 0 < r) :
    Summable (fun h : Fin 2 → ℤ => exp (-r*torusSize h)) := by
  have h := (int_exp_summable hr).mul_of_nonneg (int_exp_summable hr)
    (fun _ => exp_nonneg _) (fun _ => exp_nonneg _)
  have hh := (finTwoArrowEquiv ℤ).summable_iff.mpr h
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ext q
  simp only [Function.comp_def,finTwoArrowEquiv,piFinTwoEquiv,Equiv.coe_fn_mk]
  rw [torusSize,mul_add,exp_add]

lemma pow_mul_exp_bound (n : ℕ) {r x : ℝ} (hr : 0 < r) (hx : 0≤x) :
    x^n * exp (-r*x) ≤ ((n.factorial:ℝ)/(r/2)^n)*exp (-(r/2)*x) := by
  have hp : 0<(r/2)^n := pow_pos (by positivity) _
  have hf : 0<(n.factorial:ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hb := pow_div_factorial_le_exp ((r/2)*x) (mul_nonneg (by positivity) hx) n
  rw [div_le_iff₀ hf,mul_pow] at hb
  have hh : (r/2)^n*(x^n*exp (-(r/2)*x)) ≤ (n.factorial:ℝ) := by
    have hm := mul_le_mul_of_nonneg_right hb (exp_nonneg (-(r/2)*x))
    have he : exp ((r/2)*x)*exp (-(r/2)*x)=1 := by rw [←exp_add]; ring_nf; simp
    calc (r/2)^n*(x^n*exp (-(r/2)*x))
        = ((r/2)^n*x^n)*exp (-(r/2)*x) := by ring
      _ ≤ (exp ((r/2)*x)*(n.factorial:ℝ))*exp (-(r/2)*x) := hm
      _ = (n.factorial:ℝ) := by
        calc
          _ = (n.factorial:ℝ)*(exp ((r/2)*x)*exp (-(r/2)*x)) := by ring
          _ = _ := by rw [he,mul_one]
  have hh' : x^n*exp (-(r/2)*x) ≤ (n.factorial:ℝ)/(r/2)^n := by
    apply (le_div_iff₀ hp).mpr
    simpa only [mul_comm ((r/2)^n)] using hh
  have hmul := mul_le_mul_of_nonneg_right hh' (exp_nonneg (-(r/2)*x))
  calc
    x^n*exp (-r*x) = (x^n*exp (-(r/2)*x))*exp (-(r/2)*x) := by
      rw [mul_assoc,←exp_add]
      congr 2
      ring
    _ ≤ _ := hmul

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_TorusPoissonFlow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal

local instance torusPoissonFlowMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

abbrev TorusL2 := Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2)))

lemma torusFourierCoeff_bound (f : TorusL2) (h : Fin 2 → ℤ) :
    ‖mFourierCoeff f h‖≤‖f‖ := by
  rw [←mFourierBasis_repr]
  exact (lp.norm_apply_le_norm (by norm_num : (2:ℝ≥0∞)≠0) _ h).trans_eq
    ((mFourierBasis (d:=Fin 2)).repr.norm_map f)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_NestedGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

def sourceSwap : R3 ≃ₗᵢ[ℝ] R3 :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap (0:Fin 3) 1)

lemma sourceSwap_apply (x : R3) : sourceSwap x 0=x 1 ∧ sourceSwap x 1=x 0 ∧ sourceSwap x 2=x 2 := by
  change x ((Equiv.swap (0:Fin 3) 1).symm 0)=x 1 ∧
    x ((Equiv.swap (0:Fin 3) 1).symm 1)=x 0 ∧
    x ((Equiv.swap (0:Fin 3) 1).symm 2)=x 2
  simp [Equiv.symm_swap,Equiv.swap_apply_def]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_IntervalTraceEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory

lemma integral_sq_le_mass_mul {X : Type*} [MeasurableSpace X] {μ : Measure X}
    [IsFiniteMeasure μ] {f : X → ℝ} (hf : Integrable f μ)
    (hf2 : Integrable (fun x => f x^2) μ) :
    (∫ x, f x ∂μ)^2≤(μ univ).toReal*(∫ x, f x^2 ∂μ) := by
  by_cases h0 : μ univ=0
  · have : μ=0 := Measure.measure_univ_eq_zero.mp h0
    simp [this]
  have hm : 0<(μ univ).toReal := ENNReal.toReal_pos h0 (measure_ne_top _ _)
  let m := (∫ x, f x ∂μ)/(μ univ).toReal
  have hi : Integrable (fun x => f x^2-2*m*f x+m^2) μ :=
    (hf2.sub (hf.const_mul _)).add (integrable_const _)
  have hpos : 0≤∫ x, (f x^2-2*m*f x+m^2) ∂μ :=
    integral_nonneg (fun x => by change 0 ≤ f x^2-2*m*f x+m^2; nlinarith [sq_nonneg (f x-m)])
  rw [integral_add (f := fun x => f x^2-2*m*f x) (g := fun _ => m^2) (hf2.sub (hf.const_mul _)) (integrable_const _),
    integral_sub (f := fun x => f x^2) (g := fun x => 2*m*f x) hf2 (hf.const_mul _),integral_const_mul,integral_const,smul_eq_mul] at hpos
  have he : m*(μ univ).toReal=∫ x, f x ∂μ := by dsimp [m]; exact div_mul_cancel₀ _ hm.ne'
  dsimp [Measure.real] at hpos
  rw [←he] at hpos ⊢
  nlinarith [mul_nonneg hm.le hpos]

theorem fourier_mode_trace_energy {q : ℝ → ℝ}
    (hq : ContDiff ℝ (↑(⊤ : ℕ∞)) q) {η m : ℝ} (hη : 0<η) (_ : 0 ≤ m) :
    m*(q 0)^2≤(1+1/η)*(∫ t in (0:ℝ)..η,
      (deriv q t)^2+(1+m^2)*(q t)^2) := by
  let e := fun t => (deriv q t)^2+m^2*(q t)^2
  have hd : Continuous (deriv q) := hq.continuous_deriv (by simp)
  have he : Continuous e := (hd.pow 2).add (continuous_const.mul (hq.continuous.pow 2))
  have hpoint (t : ℝ) (ht : t∈Icc 0 η) :
      m*(q 0)^2≤ m*(q t)^2+∫ s in (0:ℝ)..η, e s := by
    have hder : ∀ s, HasDerivAt (fun x => m*(q x)^2) (2*m*q s*deriv q s) s := by
      intro s
      convert! ((hq.differentiable (by simp) s).hasDerivAt.pow 2).const_mul m using 1
      all_goals try with_reducible_and_instances rfl
      ring
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hder s)
      ((continuous_const.mul hq.continuous |>.mul hd).intervalIntegrable 0 t)
    have hi : ∫ s in (0:ℝ)..t, -(2*m*q s*deriv q s) ≤∫ s in (0:ℝ)..t, e s := by
      apply intervalIntegral.integral_mono_on ht.1
        ((continuous_const.mul hq.continuous |>.mul hd).neg.intervalIntegrable 0 t)
        (he.intervalIntegrable 0 t)
      intro s _
      dsimp [e]
      nlinarith [sq_nonneg (deriv q s+m*q s)]
    rw [intervalIntegral.integral_neg,hFTC] at hi
    have hi' : ∫ s in (0:ℝ)..t, e s ≤∫ s in (0:ℝ)..η, e s := by
      apply intervalIntegral.integral_mono_interval (le_refl 0) ht.1 ht.2
        _ (he.intervalIntegrable 0 η)
      exact Filter.Eventually.of_forall (fun s => by dsimp [e]; positivity)
    linarith
  have hav := intervalIntegral.integral_mono_on (μ := volume) (f := fun _ => m*(q 0)^2)
    (g := fun t => m*(q t)^2+∫ s in (0:ℝ)..η, e s) hη.le
    (continuous_const.intervalIntegrable 0 η)
    ((continuous_const.mul (hq.continuous.pow 2) |>.add continuous_const).intervalIntegrable 0 η)
    hpoint
  rw [intervalIntegral.integral_const,sub_zero,smul_eq_mul,
    intervalIntegral.integral_add (f := fun t => m*(q t)^2) (g := fun _ => ∫ s in (0:ℝ)..η, e s)
      ((continuous_const.mul (hq.continuous.pow 2)).intervalIntegrable 0 η)
      (continuous_const.intervalIntegrable 0 η),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const,sub_zero,smul_eq_mul] at hav
  have hI : 0≤∫ t in (0:ℝ)..η, (q t)^2 := intervalIntegral.integral_nonneg hη.le (fun _ _ => sq_nonneg _)
  have heI : 0≤∫ t in (0:ℝ)..η, e t := intervalIntegral.integral_nonneg hη.le (fun t _ => by dsimp [e]; positivity)
  have hE : (∫ t in (0:ℝ)..η, (deriv q t)^2+(1+m^2)*(q t)^2)=
      (∫ t in (0:ℝ)..η, e t)+(∫ t in (0:ℝ)..η, (q t)^2) := by
    rw [←intervalIntegral.integral_add (f := e) (g := fun t => (q t)^2) (he.intervalIntegrable 0 η) ((hq.continuous.pow 2).intervalIntegrable 0 η)]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp [e]; ring
  rw [hE]
  have hmI : m*(∫ t in (0:ℝ)..η, (q t)^2)≤
      (∫ t in (0:ℝ)..η, e t)+(∫ t in (0:ℝ)..η, (q t)^2) := by
    rw [←intervalIntegral.integral_const_mul,←intervalIntegral.integral_add (f := e) (g := fun t => (q t)^2) (he.intervalIntegrable 0 η) ((hq.continuous.pow 2).intervalIntegrable 0 η)]
    apply intervalIntegral.integral_mono_on hη.le
      ((continuous_const.mul (hq.continuous.pow 2)).intervalIntegrable 0 η)
      ((he.add (hq.continuous.pow 2)).intervalIntegrable 0 η)
    intro t _
    dsimp [e]
    have hmm : m≤1+m^2 := by nlinarith [sq_nonneg (m-1/2)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hmm) (sq_nonneg (q t)),sq_nonneg (deriv q t)]
  apply (mul_le_mul_iff_right₀ hη).mp
  have hfac : η*(1+1/η)=η+1 := by field_simp
  rw [←mul_assoc η (1+1/η),hfac]
  nlinarith [mul_nonneg hη.le hI]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_UnitBoxAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

def unitAverage (f : ℝ → G) : G := ∫ t in Icc (0:ℝ) 1, f t

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_UnitSquarePoincare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory

def unitSquareAverage (f : ℝ×ℝ → ℝ) : ℝ :=
  unitAverage (fun y => unitAverage (fun x => f (y,x)))

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_AngularNormalTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped NNReal ENNReal

def faceRayDensity (w : ℝ) (j : Fin 4) (b : ℝ) : ℝ :=
  ![(1/(1+(b/w)^2))/w,w/(1+(w*b)^2),
    (1/(1+(b/w)^2))/w,w/(1+(w*b)^2)] j/(2*Real.pi)

lemma continuous_faceRayDensity (w : ℝ) (j : Fin 4) : Continuous (faceRayDensity w j) := by
  have h0 : Continuous (fun b : ℝ => (1/(1+(b/w)^2))/w/(2*Real.pi)) := by
    have hd : Continuous (fun b : ℝ => 1+(b/w)^2) := by fun_prop
    exact ((continuous_const.div hd (fun b => ne_of_gt (by positivity))).div_const w).div_const _
  have h1 : Continuous (fun b : ℝ => (w/(1+(w*b)^2))/(2*Real.pi)) := by
    have hd : Continuous (fun b : ℝ => 1+(w*b)^2) := by fun_prop
    exact (continuous_const.div hd (fun b => ne_of_gt (by positivity))).div_const _
  fin_cases j
  · exact h0
  · exact h1
  · exact h0
  · exact h1

lemma faceRayDensity_bounds {w : ℝ} (hw : 0<w) (hw' : w≤1) (j : Fin 4) (b : ℝ) :
    0≤faceRayDensity w j b ∧ faceRayDensity w j b≤(1/w)/(2*Real.pi) := by
  have hp : 0<2*Real.pi := by positivity
  have H0 : 0≤(1/(1+(b/w)^2))/w ∧ (1/(1+(b/w)^2))/w≤1/w := by
    constructor
    · positivity
    · exact div_le_div_of_nonneg_right (by apply div_le_one_of_le₀; nlinarith; positivity) hw.le
  have H1 : 0≤w/(1+(w*b)^2) ∧ w/(1+(w*b)^2)≤1/w := by
    constructor
    · positivity
    · have hh : w/(1+(w*b)^2)≤w := div_le_self hw.le (by nlinarith [sq_nonneg (w*b)])
      apply hh.trans
      apply (le_div_iff₀ hw).mpr
      nlinarith
  fin_cases j
  · exact ⟨div_nonneg H0.1 hp.le,div_le_div_of_nonneg_right H0.2 hp.le⟩
  · exact ⟨div_nonneg H1.1 hp.le,div_le_div_of_nonneg_right H1.2 hp.le⟩
  · exact ⟨div_nonneg H0.1 hp.le,div_le_div_of_nonneg_right H0.2 hp.le⟩
  · exact ⟨div_nonneg H1.1 hp.le,div_le_div_of_nonneg_right H1.2 hp.le⟩

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_AngularIntegratedTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped NNReal ENNReal

lemma continuous_parametric_interval {X : Type*} [TopologicalSpace X]
    [FirstCountableTopology X] [LocallyCompactSpace X] {f : X → ℝ → ℝ}
    (hf : Continuous (Function.uncurry f)) {a b : ℝ} (hab : a≤b) :
    Continuous (fun x => ∫ t in a..b,f x t) := by
  have hh := continuous_parametric_integral_of_continuous (μ:=volume) hf (s:=Icc a b) isCompact_Icc
  simpa only [intervalIntegral.integral_of_le hab,integral_Icc_eq_integral_Ioc] using hh

lemma continuous_torus_interval_swap {f : ℝ → UnitAddTorus (Fin 2) → ℝ}
    (hf : Continuous (Function.uncurry f)) (a b : ℝ) :
    (∫ t in a..b,∫ x,f t x)=∫ x,∫ t in a..b,f t x := by
  have hi : IntegrableOn (Function.uncurry f) (uIoc a b ×ˢ (univ : Set (UnitAddTorus (Fin 2)))) :=
    (hf.continuousOn.integrableOn_compact (isCompact_uIcc.prod isCompact_univ)).mono_set
      (prod_mono uIoc_subset_uIcc Subset.rfl)
  apply intervalIntegral_integral_swap
  simpa only [IntegrableOn,Measure.volume_eq_prod,←Measure.prod_restrict,Measure.restrict_univ] using hi

lemma integrate_torus_interval_bound {F : UnitAddTorus (Fin 2) → ℝ}
    {G : ℝ → UnitAddTorus (Fin 2) → ℝ} (hF : Continuous F)
    (hG : Continuous (Function.uncurry G)) {a b C : ℝ} (hab : a≤b)
    (hb : ∀ x,F x≤C*(∫ t in a..b,G t x)) :
    (∫ x,F x)≤C*(∫ t in a..b,∫ x,G t x) := by
  have hs : Continuous (Function.uncurry (fun x t => G t x)) := hG.comp continuous_swap
  have ht : Continuous (fun x => ∫ t in a..b,G t x) := continuous_parametric_interval hs hab
  have hi : Integrable (fun x => C*(∫ t in a..b,G t x)) :=
    (continuous_const.mul ht).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [continuous_torus_interval_swap hG,←integral_const_mul]
  exact integral_mono (hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) hi hb

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_BoxIteration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory

def threeArrow : (Fin 3 → ℝ) ≃ᵐ ℝ×(ℝ×ℝ) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).trans
    ((MeasurableEquiv.refl ℝ).prodCongr (MeasurableEquiv.finTwoArrow))

lemma threeArrow_apply (x : Fin 3 → ℝ) : threeArrow x=(x 0,x 1,x 2) := by rfl
lemma threeArrow_symm_apply (x : ℝ×(ℝ×ℝ)) : threeArrow.symm x=![x.1,x.2.1,x.2.2] := by
  ext i; fin_cases i <;> rfl

lemma threeArrow_volume : MeasurePreserving threeArrow := by
  exact ((MeasurePreserving.id volume).prod (volume_preserving_finTwoArrow ℝ)).comp
    (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_TorusFaceIntegration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped NNReal ENNReal

lemma unitCircle_volume_eq_haar : (volume : Measure UnitAddCircle)=AddCircle.haarAddCircle := by
  simpa using (AddCircle.volume_eq_smul_haarAddCircle (T:=1))

lemma integral_unitTorus_iterated {F : UnitAddTorus (Fin 2) → ℝ} (hF : Continuous F) :
    (∫ x,F x)=∫ θ : UnitAddCircle,∫ φ : UnitAddCircle,F ![θ,φ]
      ∂AddCircle.haarAddCircle ∂AddCircle.haarAddCircle := by
  have hc : Continuous (MeasurableEquiv.finTwoArrow.symm :
      UnitAddCircle × UnitAddCircle → UnitAddTorus (Fin 2)) := by
    change Continuous (fun p : UnitAddCircle × UnitAddCircle => ![p.1,p.2])
    fun_prop
  rw [←(volume_preserving_finTwoArrow UnitAddCircle).symm.integral_comp']
  change (∫ x : UnitAddCircle × UnitAddCircle,F (MeasurableEquiv.finTwoArrow.symm x)
    ∂volume.prod volume)=_
  rw [integral_prod (fun x : UnitAddCircle × UnitAddCircle => F (MeasurableEquiv.finTwoArrow.symm x))
    ((hF.comp hc).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  simp only [unitCircle_volume_eq_haar]
  rfl

lemma continuous_parametric_unitInterval {X : Type*} [TopologicalSpace X]
    [FirstCountableTopology X] [LocallyCompactSpace X] {f : X → ℝ → ℝ}
    (hf : Continuous (Function.uncurry f)) :
    Continuous (fun x => ∫ b in (-1:ℝ)..1,f x b) := by
  have hh := continuous_parametric_integral_of_continuous (μ:=volume) hf (s:=Icc (-1:ℝ) 1) isCompact_Icc
  simpa only [intervalIntegral.integral_of_le (by norm_num : (-1:ℝ)≤1),
    integral_Icc_eq_integral_Ioc] using hh

lemma continuous_torus_partial_integral {F : UnitAddTorus (Fin 2) → ℝ} (hF : Continuous F) :
    Continuous (fun θ : UnitAddCircle => ∫ φ : UnitAddCircle,F ![θ,φ]
      ∂AddCircle.haarAddCircle) := by
  have hh := continuous_parametric_integral_of_continuous
    (μ:=AddCircle.haarAddCircle) (f:=fun θ φ : UnitAddCircle => F ![θ,φ])
    (hF.comp (by change Continuous (fun p : UnitAddCircle × UnitAddCircle => ![p.1,p.2]); fun_prop))
    (s:=univ) isCompact_univ
  simpa using hh

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

open Set MeasureTheory

variable {X : Type*} [MeasurableSpace X]

def patchCluster (Q : ℕ → Set X) : ℕ → Set X
  | 0 => Q 0
  | n+1 => patchCluster Q n ∪ Q (n+1)

def patchPoincareConstant (μ : Measure X) (Q : ℕ → Set X) (A : ℕ → ℝ) : ℕ → ℝ
  | 0 => A 0
  | n+1 => patchPoincareConstant μ Q A n+2*A (n+1)+
    4*μ.real (Q (n+1))/μ.real (patchCluster Q n ∩ Q (n+1))*
      (patchPoincareConstant μ Q A n+A (n+1))

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_CentralSmoothTrace
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

def normalizedTorusVolume : Measure (UnitAddTorus (Fin 2)) :=
  Measure.pi (fun _ => AddCircle.haarAddCircle)

end

open Set MeasureTheory UnitAddTorus
open scoped ENNReal

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_CompactFiberPrimitive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity

open Set MeasureTheory Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def compactMomentGram (χ : ℝ → ℝ) (w : ℝ → ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => ∫ s, χ s*w s i*w s j

omit [Fintype ι] [DecidableEq ι] in
lemma compactMoment_integrable {χ : ℝ → ℝ} {w : ℝ → ι → ℝ}
    (hc : Continuous χ) (hs : HasCompactSupport χ) (hw : ∀ i, Continuous (fun s => w s i))
    (i j : ι) : Integrable (fun s => χ s*w s i*w s j) :=
  ((hc.mul (hw i)).mul (hw j)).integrable_of_hasCompactSupport ((hs.mul_right).mul_right)

omit [DecidableEq ι] in
lemma compactMoment_dot_integrable {χ : ℝ → ℝ} {w : ℝ → ι → ℝ}
    (hc : Continuous χ) (hs : HasCompactSupport χ) (hw : ∀ i, Continuous (fun s => w s i))
    (a : ι → ℝ) : Integrable (fun s => χ s*(a ⬝ᵥ w s)^2) := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact hc.mul ((continuous_finsetSum _ (fun i _ => continuous_const.mul (hw i))).pow 2)
  · exact hs.mul_right

omit [DecidableEq ι] in
lemma compactMoment_quadratic {χ : ℝ → ℝ} {w : ℝ → ι → ℝ}
    (hc : Continuous χ) (hs : HasCompactSupport χ) (hw : ∀ i, Continuous (fun s => w s i))
    (a : ι → ℝ) : a ⬝ᵥ ((compactMomentGram χ w)*ᵥa)=∫ s, χ s*(a ⬝ᵥ w s)^2 := by
  have hi (i j : ι) : Integrable (fun s => a i*(χ s*w s i*w s j)*a j) :=
    ((compactMoment_integrable hc hs hw i j).const_mul _).mul_const _
  calc
    _ = ∑ i, ∑ j, ∫ s, a i*(χ s*w s i*w s j)*a j := by
      simp only [compactMomentGram,mulVec,dotProduct,Finset.mul_sum,
        integral_mul_const,integral_const_mul]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = ∫ s, ∑ i, ∑ j, a i*(χ s*w s i*w s j)*a j := by
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
      apply Finset.sum_congr rfl
      intro i _
      exact (integral_finsetSum _ (fun j _ => hi i j)).symm
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun s => by
        simp only [dotProduct,pow_two,Finset.sum_mul,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring

omit [DecidableEq ι] in
theorem compactMomentGram_posDef {χ : ℝ → ℝ} {w : ℝ → ι → ℝ}
    (hc : Continuous χ) (hs : HasCompactSupport χ) (hw : ∀ i, Continuous (fun s => w s i))
    (hn : ∀ s, 0≤χ s) {l r : ℝ} (hp : ∀ s∈Ioo l r, 0<χ s)
    (hind : ∀ a : ι → ℝ, (∀ s∈Ioo l r, a ⬝ᵥ w s=0) → a=0) :
    (compactMomentGram χ w).PosDef := by
  apply Matrix.posDef_iff_dotProduct_mulVec.mpr
  refine ⟨?_,?_⟩
  · ext i j
    simp only [conjTranspose_apply,star_trivial,compactMomentGram]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun s => by ring)
  · intro a ha
    simp only [star_trivial]
    rw [compactMoment_quadratic hc hs hw]
    have hnon : ∀ s, 0≤χ s*(a ⬝ᵥ w s)^2 := fun s => mul_nonneg (hn s) (sq_nonneg _)
    apply (integral_nonneg hnon).lt_of_ne'
    intro hz
    have hae := (integral_eq_zero_iff_of_nonneg hnon
      (compactMoment_dot_integrable hc hs hw a)).mp hz
    have he := MeasureTheory.Measure.eq_of_ae_eq hae
      (hc.mul ((continuous_finsetSum _ (fun i _ => continuous_const.mul (hw i))).pow 2))
      continuous_zero
    apply ha
    apply hind
    intro s hs
    have h := congrFun he s
    have hsq : (a ⬝ᵥ w s)^2=0 := (mul_eq_zero.mp h).resolve_left (hp s hs).ne'
    nlinarith [sq_nonneg (a ⬝ᵥ w s)]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Walls_WallMomentIndependence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity

section
open Set Filter Topology MeasureTheory Matrix

lemma deriv_zero_on_open {f : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hz : ∀ x∈U, f x=0) {x : ℝ} (hx : x∈U) : deriv f x=0 := by
  have he : f =ᶠ[𝓝 x] fun _ => 0 := Filter.eventually_of_mem (hU.mem_nhds hx) hz
  rw [he.deriv_eq,deriv_const]

lemma exp_affine_independent {l r lam A B C : ℝ} (hlr : l < r) (hlam : lam≠0)
    (h : ∀ x∈Ioo l r, A*Real.exp (lam*x)+B+C*x=0) : A=0 ∧ B=0 ∧ C=0 := by
  have hd (x : ℝ) : HasDerivAt (fun x : ℝ => A*Real.exp (lam*x)+B+C*x)
      (A*lam*Real.exp (lam*x)+C) x := by
    convert! ((((hasDerivAt_id x).const_mul lam).exp.const_mul A).add
      (hasDerivAt_const x B)).add ((hasDerivAt_id x).const_mul C) using 1
    all_goals try with_reducible_and_instances rfl
    first | rfl | (simp only [id_eq]; ring)
  have h₁ : ∀ x∈Ioo l r, A*lam*Real.exp (lam*x)+C=0 := by
    intro x hx
    rw [←(hd x).deriv]
    exact deriv_zero_on_open isOpen_Ioo h hx
  have hd₁ (x : ℝ) : HasDerivAt (fun x : ℝ => A*lam*Real.exp (lam*x)+C)
      (A*lam^2*Real.exp (lam*x)) x := by
    convert! (((hasDerivAt_id x).const_mul lam).exp.const_mul (A*lam)).add
      (hasDerivAt_const x C) using 1
    all_goals try with_reducible_and_instances rfl
    first | rfl | (simp only [id_eq]; ring)
  have h₂ : ∀ x∈Ioo l r, A*lam^2*Real.exp (lam*x)=0 := by
    intro x hx
    rw [←(hd₁ x).deriv]
    exact deriv_zero_on_open isOpen_Ioo h₁ hx
  let x := (l+r)/2
  have hx : x∈Ioo l r := ⟨by dsimp [x]; linarith,by dsimp [x]; linarith⟩
  have hA : A=0 := (mul_eq_zero.mp ((mul_eq_zero.mp (h₂ x hx)).resolve_right
      (Real.exp_ne_zero _))).resolve_right (pow_ne_zero _ hlam)
  have hC : C=0 := by simpa only [hA,zero_mul,zero_add] using h₁ x hx
  exact ⟨hA,by simpa only [hA,hC,zero_mul,zero_add,add_zero] using h x hx,hC⟩

def wallMomentBasis (σ lam s : ℝ) : Fin 3 → ℝ :=
  ![1,-σ*lam*Real.exp (-lam*s),σ*(1+lam*s)*Real.exp (-lam*s)]

lemma wallMomentBasis_smooth (σ lam : ℝ) (i : Fin 3) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun s => wallMomentBasis σ lam s i) := by
  fin_cases i <;> dsimp [wallMomentBasis] <;> fun_prop

lemma wallMomentBasis_dot (σ lam s : ℝ) (a : Fin 3 → ℝ) :
    a ⬝ᵥ wallMomentBasis σ lam s =
      a 0+(-σ*lam*a 1+σ*a 2+σ*lam*a 2*s)*Real.exp (-lam*s) := by
  simp [wallMomentBasis,dotProduct,Fin.sum_univ_succ]

  ring

lemma wallMomentBasis_independent {l r σ lam : ℝ} (hlr : l < r) (hσ : σ≠0) (hlam : lam≠0)
    (a : Fin 3 → ℝ) (ha : ∀ s∈Ioo l r, a ⬝ᵥ wallMomentBasis σ lam s=0) : a=0 := by
  have he : ∀ s∈Ioo l r,
      a 0*Real.exp (lam*s)+(-σ*lam*a 1+σ*a 2)+(σ*lam*a 2)*s=0 := by
    intro s hs
    have h := congrArg (fun t => t*Real.exp (lam*s)) (ha s hs)
    rw [wallMomentBasis_dot] at h
    have hexp : Real.exp (-lam*s)*Real.exp (lam*s)=1 := by
      rw [←Real.exp_add]; simp
    calc
      a 0*Real.exp (lam*s)+(-σ*lam*a 1+σ*a 2)+(σ*lam*a 2)*s =
          (a 0+(-σ*lam*a 1+σ*a 2+σ*lam*a 2*s)*Real.exp (-lam*s))*Real.exp (lam*s) := by
        calc
          _ = a 0*Real.exp (lam*s)+(-σ*lam*a 1+σ*a 2+σ*lam*a 2*s)*
              (Real.exp (-lam*s)*Real.exp (lam*s)) := by rw [hexp]; ring
          _ = _ := by ring
      _=0 := by simpa only [zero_mul] using h
  obtain ⟨h₀,h₁,h₂⟩ := exp_affine_independent hlr hlam he
  have ha₂ : a 2=0 := (mul_eq_zero.mp h₂).resolve_left (mul_ne_zero hσ hlam)
  have ha₁ : a 1=0 := by
    have hz : (-σ*lam)*(a 1)=0 := by simpa only [ha₂,mul_zero,add_zero] using h₁
    exact (mul_eq_zero.mp hz).resolve_left (mul_ne_zero (neg_ne_zero.mpr hσ) hlam)
  ext i
  fin_cases i <;> assumption

end

open Set MeasureTheory Matrix Topology

lemma positive_interval_bump {l r : ℝ} (_ : l < r) :
    ∃ χ : ℝ → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) χ ∧ HasCompactSupport χ ∧
      (∀ s, 0≤χ s) ∧ (∀ s∈Ioo l r, 0<χ s) ∧ tsupport χ ⊆ Icc l r := by
  obtain ⟨χ,hχ,hc,hb⟩ := (isOpen_Ioo : IsOpen (Ioo l r)).exists_contDiff_support_eq (n := ⊤)
  have hs : tsupport χ⊆Icc l r := by
    change closure (Function.support χ) ⊆ Icc l r
    rw [hχ]
    exact closure_minimal Ioo_subset_Icc_self isClosed_Icc
  refine ⟨χ,hc,isCompact_Icc.of_isClosed_subset isClosed_closure hs,
    fun s => (hb ⟨s,rfl⟩).1,?_,hs⟩
  intro s hs'
  have hn : χ s≠0 := by simpa only [←hχ,Function.mem_support] using hs'
  exact (hb ⟨s,rfl⟩).1.lt_of_ne' hn

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_CompactFiberDecomposition
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

lemma exists_unit_interval_bump {a b : ℝ} (hab : a<b) :
    ∃ η : ℝ → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) η ∧ HasCompactSupport η ∧
      tsupport η ⊆ Ioo a b ∧ (∫ t in a..b, η t)=1 := by
  let l := (2*a+b)/3
  let r := (a+2*b)/3
  have hal : a<l := by dsimp [l]; linarith
  have hlr : l < r := by dsimp [l,r]; linarith
  have hrb : r<b := by dsimp [r]; linarith
  obtain ⟨χ,hc,hs,hn,hp,hsub⟩ := positive_interval_bump hlr
  have hI : 0<∫ t, χ t := by
    apply integral_pos_iff_support_of_nonneg (fun t => hn t) (hc.continuous.integrable_of_hasCompactSupport hs) |>.2
    apply lt_of_lt_of_le ((Measure.measure_Ioo_pos volume).mpr hlr)
    exact measure_mono (fun t ht => (hp t ht).ne')
  let η := fun t => χ t/(∫ s, χ s)
  have hη : ContDiff ℝ (↑(⊤ : ℕ∞)) η := hc.div_const _
  have hsη : HasCompactSupport η := by
    apply HasCompactSupport.of_support_subset_isCompact hs
    intro t ht
    apply subset_tsupport χ
    exact (div_ne_zero_iff.mp ht).1
  have hsubη : tsupport η ⊆ Ioo a b := by
    change tsupport (fun t => χ t*(∫ s, χ s)⁻¹) ⊆ _
    apply tsupport_mul_subset_left.trans
    exact hsub.trans (fun t ht => ⟨hal.trans_le ht.1,ht.2.trans_lt hrb⟩)
  refine ⟨η,hη,hsη,hsubη,?_⟩
  rw [intervalIntegral.integral_of_le hab.le]
  have he : ∫ t in Ioc a b, η t=∫ t, η t := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t ht
    apply image_eq_zero_of_notMem_tsupport
    exact fun hh => ht ⟨(hsubη hh).1,(hsubη hh).2.le⟩
  rw [he]
  dsimp [η]
  rw [integral_div,div_self hI.ne']

end

open Set MeasureTheory

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

def wallAlong (d : E) (f : E × ℝ → ℝ) (p : E × ℝ) : ℝ :=
  fderiv ℝ f p (d,0)

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

def UniformC1Bound (f : E → ℝ) (M : ℝ) : Prop :=
  ∀ x,|f x|≤M ∧ ‖fderiv ℝ f x‖≤M

lemma UniformC1Bound.mono {f : E → ℝ} {M N : ℝ} (h : UniformC1Bound f M) (hMN : M≤N) :
    UniformC1Bound f N := fun x => ⟨(h x).1.trans hMN,(h x).2.trans hMN⟩

lemma UniformC1Bound.sub {f g : E → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    {M N : ℝ} (hb : UniformC1Bound f M) (hc : UniformC1Bound g N) :
    UniformC1Bound (fun x => f x-g x) (M+N) := by
  intro x
  constructor
  · exact (abs_sub (f x) (g x)).trans (add_le_add (hb x).1 (hc x).1)
  · rw [fderiv_fun_sub (hf x) (hg x)]
    exact (norm_sub_le _ _).trans (add_le_add (hb x).2 (hc x).2)

lemma UniformC1Bound.mul {f g : E → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    {M N : ℝ} (hM : 0≤M) (hN : 0≤N) (hb : UniformC1Bound f M) (hc : UniformC1Bound g N) :
    UniformC1Bound (fun x => f x*g x) (2*M*N) := by
  intro x
  constructor
  · rw [abs_mul]
    exact (mul_le_mul (hb x).1 (hc x).1 (abs_nonneg _) hM).trans (by nlinarith [mul_nonneg hM hN])
  · rw [fderiv_fun_mul (hf x) (hg x)]
    calc
      _ ≤ ‖f x • fderiv ℝ g x‖+‖g x • fderiv ℝ f x‖ := norm_add_le _ _
      _ = |f x| *‖fderiv ℝ g x‖+|g x| *‖fderiv ℝ f x‖ := by simp only [norm_smul,Real.norm_eq_abs]
      _ ≤ M*N+N*M := add_le_add
        (mul_le_mul (hb x).1 (hc x).2 (norm_nonneg _) hM)
        (mul_le_mul (hc x).1 (hb x).2 (norm_nonneg _) hN)
      _ = _ := by ring

lemma UniformC1Bound.comp_linear {f : E → ℝ} (hf : Differentiable ℝ f)
    {M : ℝ} (hM : 0≤M) (hb : UniformC1Bound f M)
    (L : P →L[ℝ] E) (hL : ‖L‖≤1) : UniformC1Bound (fun x => f (L x)) M := by
  intro x
  refine ⟨(hb (L x)).1,?_⟩
  have hd := (hf (L x)).hasFDerivAt.comp x L.hasFDerivAt
  simp only [Function.comp_def] at hd
  rw [hd.fderiv]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul (hb (L x)).2 hL (norm_nonneg _) hM).trans_eq (mul_one M))

lemma UniformC1Bound.comp_fst {f : E → ℝ} (hf : Differentiable ℝ f)
    {M : ℝ} (hM : 0≤M) (hb : UniformC1Bound f M) :
    UniformC1Bound (fun x : E×P => f x.1) M :=
  hb.comp_linear hf hM (ContinuousLinearMap.fst ℝ E P) (ContinuousLinearMap.norm_fst_le ..)

lemma UniformC1Bound.comp_snd {f : P → ℝ} (hf : Differentiable ℝ f)
    {M : ℝ} (hM : 0≤M) (hb : UniformC1Bound f M) :
    UniformC1Bound (fun x : E×P => f x.2) M :=
  hb.comp_linear hf hM (ContinuousLinearMap.snd ℝ E P) (ContinuousLinearMap.norm_snd_le ..)

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

local instance instMeasureSpaceUnitAddCircle_solutions_5 : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance instIsProbabilityMeasureUnitAddCircleVolume_solutions_5 : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

abbrev CylinderL2 (μ : Measure ℝ) :=
  Lp ℂ 2 (μ.prod (volume : Measure (UnitAddTorus (Fin 2))))

lemma cylinderTensor_memLp {μ : Measure ℝ} (f : Lp ℂ 2 μ) (g : TorusL2) :
    MemLp (fun z : ℝ × UnitAddTorus (Fin 2) => f z.1*g z.2) 2
      (μ.prod volume) := by
  apply (memLp_two_iff_integrable_sq_norm
    ((Lp.aestronglyMeasurable f).comp_fst.mul (Lp.aestronglyMeasurable g).comp_snd)).mpr
  simpa only [Pi.mul_apply,norm_mul,mul_pow] using
    ((Lp.memLp f).integrable_norm_pow (by decide : (2:ℕ)≠0)).mul_prod
      ((Lp.memLp g).integrable_norm_pow (by decide : (2:ℕ)≠0))

def cylinderTensor {μ : Measure ℝ} (f : Lp ℂ 2 μ) (g : TorusL2) : CylinderL2 μ :=
  (cylinderTensor_memLp f g).toLp _

lemma cylinderTensor_ae {μ : Measure ℝ} (f : Lp ℂ 2 μ) (g : TorusL2) :
    cylinderTensor f g =ᵐ[μ.prod volume]
      fun z : ℝ × UnitAddTorus (Fin 2) => f z.1*g z.2 :=
  (cylinderTensor_memLp f g).coeFn_toLp

lemma cylinderTensor_add {μ : Measure ℝ} (f f' : Lp ℂ 2 μ) (g : TorusL2) :
    cylinderTensor (f+f') g=cylinderTensor f g+cylinderTensor f' g := by
  apply Lp.ext
  filter_upwards [cylinderTensor_ae (f+f') g,cylinderTensor_ae f g,
    cylinderTensor_ae f' g,Lp.coeFn_add (cylinderTensor f g) (cylinderTensor f' g),
    Measure.quasiMeasurePreserving_fst.ae (Lp.coeFn_add f f')] with z hz h1 h2 h3 h4
  rw [hz,h3]
  simp only [Pi.add_apply] at h4 ⊢
  rw [h1,h2,h4]
  exact add_mul _ _ _

lemma cylinderTensor_smul {μ : Measure ℝ} (c : ℂ) (f : Lp ℂ 2 μ) (g : TorusL2) :
    cylinderTensor (c•f) g=c•cylinderTensor f g := by
  apply Lp.ext
  filter_upwards [cylinderTensor_ae (c•f) g,cylinderTensor_ae f g,
    Lp.coeFn_smul c (cylinderTensor f g),
    Measure.quasiMeasurePreserving_fst.ae (Lp.coeFn_smul c f)] with z hz h1 h2 h3
  rw [hz,h2]
  simp only [Pi.smul_apply] at h3 ⊢
  rw [h1,h3]
  simp only [smul_eq_mul,mul_assoc]

lemma cylinderTensor_inner {μ : Measure ℝ} [SFinite μ]
    (f f' : Lp ℂ 2 μ) (g g' : TorusL2) :
    inner ℂ (cylinderTensor f g) (cylinderTensor f' g')=
      inner ℂ f f'*inner ℂ g g' := by
  rw [L2.inner_def,L2.inner_def,L2.inner_def,←integral_prod_mul]
  apply integral_congr_ae
  filter_upwards [cylinderTensor_ae f g,cylinderTensor_ae f' g'] with z hz hz'
  rw [hz,hz']
  simp only [RCLike.inner_apply,map_mul]
  ring

lemma cylinderTensor_norm_sq {μ : Measure ℝ} [SFinite μ]
    (f : Lp ℂ 2 μ) (g : TorusL2) :
    ‖cylinderTensor f g‖^2=‖f‖^2*‖g‖^2 := by
  have he := cylinderTensor_inner f f g g
  simp only [inner_self_eq_norm_sq_to_K] at he
  exact_mod_cast he

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_SpectralTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory Filter Topology
open scoped ENNReal

lemma poisson_mode_energy {m : ℝ} (hm : 0 ≤ m) (a : ℂ) :
    IntegrableOn (fun t : ℝ => 2*m^2*Real.exp (-2*m*t)*‖a‖^2) (Ioi 0) ∧
    (∫ t in Ioi (0:ℝ), 2*m^2*Real.exp (-2*m*t)*‖a‖^2)=m*‖a‖^2 := by
  rcases hm.eq_or_lt with hm | hm
  · subst m; simp
  · have hn : -2*m<0 := by linarith
    have hi := (integrableOn_exp_mul_Ioi hn 0).const_mul (2*m^2*‖a‖^2)
    have he : (fun t : ℝ => 2*m^2*Real.exp (-2*m*t)*‖a‖^2)=
        (fun t => (2*m^2*‖a‖^2)*Real.exp ((-2*m)*t)) := by funext t; ring
    rw [he]
    refine ⟨hi,?_⟩
    rw [integral_const_mul,integral_exp_mul_Ioi hn 0]
    simp only [mul_zero,Real.exp_zero]
    field_simp

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_AxialDecayL2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory Filter Topology
open scoped ENNReal

abbrev EndAxisMeasure : Measure ℝ := volume.restrict (Ioi 0)
abbrev EndAxisL2 := Lp ℂ 2 EndAxisMeasure

lemma complexLp_norm_sq {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (f : Lp ℂ 2 μ) : ‖f‖^2=∫ x,‖f x‖^2 ∂μ := by
  rw [←real_inner_self_eq_norm_sq,L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

def axialRateField (m : ℝ) (a : ℂ) (t : ℝ) : ℂ :=
  (m*Real.exp (-m*t):ℝ)*a

lemma axialRateField_continuous (m : ℝ) (a : ℂ) :
    Continuous (axialRateField m a) := by unfold axialRateField; fun_prop

lemma axialRateField_norm_sq (m : ℝ) (a : ℂ) (t : ℝ) :
    ‖axialRateField m a t‖^2=(2*m^2*Real.exp (-2*m*t)*‖a‖^2)/2 := by
  unfold axialRateField
  rw [norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,mul_pow,
    ←Real.exp_nat_mul]
  ring_nf

lemma axialRateField_memLp {m : ℝ} (hm : 0 ≤ m) (a : ℂ) :
    MemLp (axialRateField m a) 2 EndAxisMeasure := by
  apply (memLp_two_iff_integrable_sq_norm (axialRateField_continuous m a).aestronglyMeasurable).mpr
  simpa only [axialRateField_norm_sq] using ((poisson_mode_energy hm a).1.div_const 2)

def axialRateLp (m : ℝ) (hm : 0 ≤ m) (a : ℂ) : EndAxisL2 :=
  (axialRateField_memLp hm a).toLp _

lemma axialRateLp_ae (m : ℝ) (hm : 0 ≤ m) (a : ℂ) :
    axialRateLp m hm a =ᵐ[EndAxisMeasure] axialRateField m a :=
  (axialRateField_memLp hm a).coeFn_toLp

lemma axialRateLp_norm_sq (m : ℝ) (hm : 0 ≤ m) (a : ℂ) :
    ‖axialRateLp m hm a‖^2=(m*‖a‖^2)/2 := by
  rw [complexLp_norm_sq]
  calc
    (∫ t,‖axialRateLp m hm a t‖^2 ∂EndAxisMeasure)=
        ∫ t,‖axialRateField m a t‖^2 ∂EndAxisMeasure :=
      by
        apply integral_congr_ae
        filter_upwards [axialRateLp_ae m hm a] with t ht
        rw [ht]
    _=(∫ t in Ioi (0:ℝ),2*m^2*Real.exp (-2*m*t)*‖a‖^2)/2 := by
      simp only [axialRateField_norm_sq,integral_div,EndAxisMeasure]
    _=(m*‖a‖^2)/2 := by rw [(poisson_mode_energy hm a).2]

abbrev FiniteAxisMeasure (R : ℝ) : Measure ℝ := volume.restrict (Ioc 0 R)
abbrev FiniteAxisL2 (R : ℝ) := Lp ℂ 2 (FiniteAxisMeasure R)

def axialDecayField (m : ℝ) (a : ℂ) (t : ℝ) : ℂ := (Real.exp (-m*t):ℂ)*a

lemma axialDecayField_continuous (m : ℝ) (a : ℂ) :
    Continuous (axialDecayField m a) := by unfold axialDecayField; fun_prop

lemma axialDecayField_memLp (m R : ℝ) (a : ℂ) :
    MemLp (axialDecayField m a) 2 (FiniteAxisMeasure R) := by
  apply (memLp_two_iff_integrable_sq_norm (axialDecayField_continuous m a).aestronglyMeasurable).mpr
  exact (((axialDecayField_continuous m a).norm.pow 2).integrableOn_Icc).mono_set Ioc_subset_Icc_self

def finiteDecayLp (m R : ℝ) (a : ℂ) : FiniteAxisL2 R :=
  (axialDecayField_memLp m R a).toLp _

lemma finiteDecayLp_ae (m R : ℝ) (a : ℂ) :
    finiteDecayLp m R a =ᵐ[FiniteAxisMeasure R] axialDecayField m a :=
  (axialDecayField_memLp m R a).coeFn_toLp

lemma finiteDecayLp_norm_sq {m R : ℝ} (hm : 0 ≤ m) (hR : 0≤R) (a : ℂ) :
    ‖finiteDecayLp m R a‖^2≤R*‖a‖^2 := by
  rw [complexLp_norm_sq]
  have he : (∫ t,‖finiteDecayLp m R a t‖^2 ∂FiniteAxisMeasure R)=
      ∫ t in Ioc (0:ℝ) R,‖axialDecayField m a t‖^2 := by
    apply integral_congr_ae
    filter_upwards [finiteDecayLp_ae m R a] with t ht
    rw [ht]
  rw [he]
  calc
    (∫ t in Ioc (0:ℝ) R,‖axialDecayField m a t‖^2) ≤
        ∫ t in Ioc (0:ℝ) R,‖a‖^2 := by
      apply setIntegral_mono_on
        ((axialDecayField_memLp m R a).integrable_norm_pow (by decide : (2:ℕ)≠0))
        (integrable_const _) measurableSet_Ioc
      intro t ht
      have hb : Real.exp (-m*t)≤1 := Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hm) ht.1.le)
      have hn : ‖axialDecayField m a t‖≤‖a‖ := by
        unfold axialDecayField
        rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
        exact (mul_le_mul_of_nonneg_right hb (norm_nonneg a)).trans_eq (one_mul _)
      exact pow_le_pow_left₀ (norm_nonneg _) hn 2
    _=R*‖a‖^2 := by
      rw [integral_const]
      change ((volume.restrict (Ioc (0:ℝ) R)) univ).toReal * ‖a‖^2=_
      rw [Measure.restrict_apply MeasurableSet.univ,univ_inter,Real.volume_Ioc,
        sub_zero,ENNReal.toReal_ofReal hR]

lemma finiteDecayLp_add (m R : ℝ) (a b : ℂ) :
    finiteDecayLp m R (a+b)=finiteDecayLp m R a+finiteDecayLp m R b := by
  apply Lp.ext
  filter_upwards [finiteDecayLp_ae m R (a+b),finiteDecayLp_ae m R a,finiteDecayLp_ae m R b,
    Lp.coeFn_add (finiteDecayLp m R a) (finiteDecayLp m R b)] with t h h1 h2 h3
  rw [h,h3]
  simp only [Pi.add_apply]
  rw [h1,h2]
  exact mul_add _ _ _

lemma finiteDecayLp_smul (m R : ℝ) (c a : ℂ) :
    finiteDecayLp m R (c*a)=c•finiteDecayLp m R a := by
  apply Lp.ext
  filter_upwards [finiteDecayLp_ae m R (c*a),finiteDecayLp_ae m R a,
    Lp.coeFn_smul c (finiteDecayLp m R a)] with t h h1 h2
  rw [h,h2]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [h1]
  unfold axialDecayField
  ring

lemma finiteAxisMeasure_le (R : ℝ) : FiniteAxisMeasure R≤EndAxisMeasure :=
  Measure.restrict_mono (fun _ h => h.1) le_rfl

def endAxisRestrict (R : ℝ) : EndAxisL2 →L[ℝ] FiniteAxisL2 R :=
  Lp.LpToLpOfMeasureLeSMul (c:=1) (by simp) (by simpa only [one_smul] using finiteAxisMeasure_le R)

lemma endAxisRestrict_ae (R : ℝ) (f : EndAxisL2) :
    endAxisRestrict R f =ᵐ[FiniteAxisMeasure R] f :=
  Lp.coeFn_LpToLpOfMeasureLeSMul (c:=1) (by simp)
    (by simpa only [one_smul] using finiteAxisMeasure_le R) f

lemma endAxisRestrict_norm (R : ℝ) (f : EndAxisL2) : ‖endAxisRestrict R f‖≤‖f‖ := by
  have hn : ‖endAxisRestrict R‖≤1 := by
    simpa only [endAxisRestrict,ENNReal.toReal_one,Real.one_rpow] using
      Lp.norm_LpToLpOfMeasureLeSMul_le (E:=ℂ) (p:=2) (c:=1) (by simp)
        (by simpa only [one_smul] using finiteAxisMeasure_le R)
  exact ((endAxisRestrict R).le_opNorm f).trans
    ((mul_le_mul_of_nonneg_right hn (norm_nonneg f)).trans_eq (one_mul _))

lemma finiteDecayLp_rate (m R : ℝ) (hm : 0 ≤ m) (a : ℂ) :
    finiteDecayLp m R ((m:ℂ)*a)=endAxisRestrict R (axialRateLp m hm a) := by
  apply Lp.ext
  filter_upwards [finiteDecayLp_ae m R ((m:ℂ)*a),
    endAxisRestrict_ae R (axialRateLp m hm a),
    (Measure.absolutelyContinuous_of_le (finiteAxisMeasure_le R)).ae_eq (axialRateLp_ae m hm a)]
    with t h h1 h2
  rw [h,h1,h2]
  simp only [axialDecayField,axialRateField,Complex.ofReal_mul]
  ring

lemma finiteDecayLp_rate_norm_sq (m R : ℝ) (hm : 0 ≤ m) (a : ℂ) :
    ‖finiteDecayLp m R ((m:ℂ)*a)‖^2≤(m*‖a‖^2)/2 := by
  rw [finiteDecayLp_rate m R hm a,←axialRateLp_norm_sq m hm a]
  exact pow_le_pow_left₀ (norm_nonneg _) (endAxisRestrict_norm R _) 2

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_EndPoissonJets
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

lemma finiteDecayLp_real_norm_sq (m R r : ℝ) (a : ℂ) :
    ‖finiteDecayLp m R ((r:ℂ)*a)‖^2=r^2*‖finiteDecayLp m R a‖^2 := by
  rw [finiteDecayLp_smul,norm_smul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]

lemma finiteDecayLp_imag_norm_sq (m R r : ℝ) (a : ℂ) :
    ‖finiteDecayLp m R (Complex.I*(r:ℂ)*a)‖^2=r^2*‖finiteDecayLp m R a‖^2 := by
  rw [finiteDecayLp_smul,norm_smul,norm_mul,Complex.norm_I,one_mul,mul_pow,
    Complex.norm_real,Real.norm_eq_abs,sq_abs]

lemma finiteDecayLp_axial_bound (m R : ℝ) (hm : 0  ≤  m) (a : ℂ) :
    ‖finiteDecayLp m R (-(m:ℂ)*a)‖^2 ≤ m*‖a‖^2/2 := by
  have hh := finiteDecayLp_rate_norm_sq m R hm a
  rw [finiteDecayLp_real_norm_sq] at hh
  rw [show -(m:ℂ)=((-m:ℝ):ℂ) by simp,finiteDecayLp_real_norm_sq,neg_sq]
  exact hh

local instance instMeasureSpaceUnitAddCircle_solutions_6_rb184c6_1 : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
abbrev FiniteCylinderJets (R : ℝ) :=
  PiLp 2 (fun _ : Fin 4 => CylinderL2 (FiniteAxisMeasure R))

end

open Set MeasureTheory Filter Topology
open scoped ENNReal

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_TorusFlatMode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Real Set Filter Topology

lemma flat_proj_norm (i : Fin 3) :
    ‖(ContinuousLinearMap.proj i : (Fin 3 → ℝ) →L[ℝ] ℝ)‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa using norm_le_pi_norm x i

def torusAngular (h : Fin 2 → ℤ) : (Fin 3 → ℝ) →L[ℝ] ℝ :=
  (h 0:ℝ) • ContinuousLinearMap.proj 1 + (h 1:ℝ) • ContinuousLinearMap.proj 2

lemma torusAngular_norm (h : Fin 2 → ℤ) : ‖torusAngular h‖≤torusSize h := by
  apply (norm_add_le _ _).trans
  rw [norm_smul,norm_smul]
  exact add_le_add (mul_le_of_le_one_right (norm_nonneg _) (flat_proj_norm _))
    (mul_le_of_le_one_right (norm_nonneg _) (flat_proj_norm _))

lemma axial_exp_iterated_bound (lam : ℝ) (hlam : 0≤lam) (n : ℕ) (x : Fin 3 → ℝ) :
    ‖iteratedFDeriv ℝ n (fun y : Fin 3 → ℝ => exp (-lam*y 0)) x‖ ≤ lam^n*exp (-lam*x 0) := by
  let P : (Fin 3 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj 0
  have he : ContDiff ℝ (↑n) (fun t => exp (-lam*t)) := by fun_prop
  change ‖iteratedFDeriv ℝ n ((fun t => exp (-lam*t)) ∘ P) x‖≤_
  rw [P.iteratedFDeriv_comp_right he x le_rfl]
  have hb := (iteratedFDeriv ℝ n (fun t => exp (-lam*t)) (P x)).norm_compContinuousLinearMap_le (fun _ => P)
  apply hb.trans
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  have hp : ‖P‖^n≤1 := pow_le_one₀ (norm_nonneg _) (flat_proj_norm 0)
  apply (mul_le_of_le_one_right (norm_nonneg _) hp).trans_eq
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,iteratedDeriv_exp_const_mul]
  simp only [Real.norm_eq_abs,abs_mul,abs_pow,abs_neg,abs_of_nonneg hlam,abs_of_pos (exp_pos _)]
  rfl

lemma angular_phase_iterated_bound (h : Fin 2 → ℤ) (phase : ℝ) (n : ℕ) (x : Fin 3 → ℝ) :
    ‖iteratedFDeriv ℝ n (fun y => cos (torusAngular h y+phase)) x‖≤(torusSize h)^n := by
  have hc : ContDiff ℝ (↑(⊤:ℕ∞)) (fun z : ℝ => cos (z+phase)) := by fun_prop
  have hh := linear_comp_iterated_bound (torusAngular h) hc
    (fun z => by simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv,iteratedDeriv_comp_add_const]
      using (sin_cos_iterated_bound n (z+phase)).2) x
  apply hh.trans
  rw [one_mul]
  exact pow_le_pow_left₀ (norm_nonneg _) (torusAngular_norm h) _

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

def faceRayDensityLower (w : ℝ) : ℝ := w/(1+w^2)/(2*Real.pi)

lemma faceRayDensityLower_pos {w : ℝ} (hw : 0<w) : 0<faceRayDensityLower w := by
  unfold faceRayDensityLower
  positivity

lemma faceRayDensity_lower {w : ℝ} (hw : 0<w) (j : Fin 4) {b : ℝ} (hb : |b|≤1) :
    faceRayDensityLower w≤ faceRayDensity w j b := by
  have hsq : b^2≤1 := by
    have hh := mul_le_mul hb hb (abs_nonneg b) (by norm_num : (0:ℝ)≤1)
    simpa [←sq_abs b,pow_two] using hh
  have hp : 0<2*Real.pi := by positivity
  have he : (1/(1+(b/w)^2))/w=w/(w^2+b^2) := by
    field_simp
  have h0 : w/(1+w^2)≤(1/(1+(b/w)^2))/w := by
    rw [he]
    apply div_le_div_of_nonneg_left hw.le (by positivity)
    linarith
  have h1 : w/(1+w^2)≤w/(1+(w*b)^2) := by
    apply div_le_div_of_nonneg_left hw.le (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left hsq (sq_nonneg w)]
  unfold faceRayDensityLower faceRayDensity
  fin_cases j
  · exact div_le_div_of_nonneg_right h0 hp.le
  · exact div_le_div_of_nonneg_right h1 hp.le
  · exact div_le_div_of_nonneg_right h0 hp.le
  · exact div_le_div_of_nonneg_right h1 hp.le

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

lemma finiteMeasure_le_of_nonneg_compact_integrals
    {n : ℕ} {μ ν : Measure (Fin n → ℝ)} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ f : (Fin n → ℝ) → ℝ, Continuous f → HasCompactSupport f →
      (∀ x,0≤f x) → (∫ x,f x ∂μ)≤∫ x,f x ∂ν) : μ≤ν := by
  have hc (K : Set (Fin n → ℝ)) (hK : IsCompact K) : μ K≤ν K := by
    rw [hK.measure_eq_biInf_integral_hasCompactSupport ν]
    simp only [le_iInf_iff]
    intro f hf hcomp hKf hn
    exact ((hf.integrable_of_hasCompactSupport hcomp).measure_le_integral
      (Eventually.of_forall hn) (fun x hx => by simp [hKf hx])).trans
      (ENNReal.ofReal_le_ofReal (h f hf hcomp hn))
  apply Measure.le_iff.mpr
  intro s hs
  rw [hs.measure_eq_iSup_isCompact_of_ne_top (measure_ne_top μ s)]
  simp only [iSup_le_iff]
  intro K hKs hK
  exact (hc K hK).trans (measure_mono hKs)

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

def complexUnitAngle (z : ℂ) : UnitAddCircle := (z.arg/(2*Real.pi) : ℝ)

lemma measurable_complexUnitAngle : Measurable complexUnitAngle := by
  exact (show Continuous (fun x : ℝ => (x : UnitAddCircle)) from continuous_quotient_mk').measurable.comp
    (Complex.measurable_arg.div_const _)

lemma fourier_complexUnitAngle (z : ℂ) :
    fourier 1 (complexUnitAngle z)=Complex.exp ((z.arg : ℂ)*Complex.I) := by
  rw [complexUnitAngle,fourier_coe_apply]
  congr 1
  push_cast
  field_simp

lemma complexUnitAngle_fourier (x : UnitAddCircle) :
    complexUnitAngle (fourier 1 x)=x := by
  apply AddCircle.injective_toCircle (by norm_num : (1:ℝ)≠0)
  apply Subtype.ext
  have hn : ‖fourier 1 x‖=1 := by simp [fourier_apply,Circle.norm_coe]
  have he := Complex.norm_mul_exp_arg_mul_I (fourier 1 x)
  rw [hn,Complex.ofReal_one,one_mul,←fourier_complexUnitAngle] at he
  simpa [fourier_apply] using he

lemma complexUnitAngle_pos_mul (z : ℂ) {r : ℝ} (hr : 0 < r) :
    complexUnitAngle ((r:ℂ)*z)=complexUnitAngle z := by
  simp only [complexUnitAngle,Complex.arg_real_mul z hr]

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

abbrev sourceCylinderMeasure (l r : ℝ) : Measure (ℝ×UnitAddTorus (Fin 2)) :=
  (volume.restrict (Ioc l r)).prod
    (Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle)))

lemma sourceCylinderMeasure_eq (l r : ℝ) : sourceCylinderMeasure l r =
    (volume.restrict (Ioc l r)).prod (volume : Measure (UnitAddTorus (Fin 2))) := by
  apply congrArg (Measure.prod (volume.restrict (Ioc l r)))
  change Measure.pi (fun _ : Fin 2 => AddCircle.haarAddCircle)=
    Measure.pi (fun _ : Fin 2 => (volume : Measure UnitAddCircle))
  simp_rw [AddCircle.volume_eq_smul_haarAddCircle]
  simp

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_EndPoissonRepresentative
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

local instance instMeasureSpaceUnitAddCircle_solutions_7 : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

lemma lp_hasSum_ae_unique {X E ι : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [Countable ι] [Infinite ι]
    {μ : Measure X} {p : ℝ≥0∞} [Fact (1≤p)]
    {u : Lp E p μ} {f : ι → Lp E p μ} {a : ι → X → E} {g : X → E}
    (hf : HasSum f u) (ha : ∀ i,f i=ᵐ[μ] a i)
    (hg : ∀ᵐ x∂μ,HasSum (fun i => a i x) (g x)) : u=ᵐ[μ] g := by
  obtain ⟨e⟩ := nonempty_equiv_of_countable (α:=ℕ) (β:=ι)
  have ht := (e.hasSum_iff.mpr hf).tendsto_sum_nat
  obtain ⟨ns,hns,hn⟩ := (tendstoInMeasure_of_tendsto_Lp ht).exists_seq_tendsto_ae
  have hs : ∀ᵐ x∂μ,∀ n : ℕ,(∑ i∈Finset.range n,f (e i)) x=
      ∑ i∈Finset.range n,a (e i) x := by
    have hA : ∀ᵐ x∂μ,∀ i : ℕ,f (e i) x=a (e i) x := ae_all_iff.mpr (fun i => ha (e i))
    have hF : ∀ᵐ x∂μ,∀ n : ℕ,(∑ i∈Finset.range n,f (e i)) x=
        ∑ i∈Finset.range n,f (e i) x :=
      ae_all_iff.mpr (fun n => Lp.coeFn_fun_finsetSum (Finset.range n) (fun i => f (e i)))
    filter_upwards [hA,hF] with x hx hy n
    rw [hy]
    exact Finset.sum_congr rfl (fun i _ => hx i)
  filter_upwards [hg,hn,hs] with x hx hn hs
  have hpoint := ((e.hasSum_iff.mpr hx).tendsto_sum_nat).comp hns.tendsto_atTop
  have hco : (fun i => (∑ k∈Finset.range (ns i),f (e k)) x)=
      (fun i => ∑ k∈Finset.range (ns i),a (e k) x) := funext (fun i => hs (ns i))
  change Tendsto (fun i => (∑ k∈Finset.range (ns i),f (e k)) x) atTop (𝓝 (u x)) at hn
  rw [hco] at hn
  exact tendsto_nhds_unique hn hpoint

end

open Set MeasureTheory Filter Topology UnitAddTorus
open scoped NNReal ENNReal

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_LocalSmoothSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set Filter Topology

lemma local_smooth_taylor {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : ι → E → F} {s : Set E} (hs : IsOpen s) (hsc : IsPreconnected s)
    (hf : ∀ i, ContDiff ℝ (↑(⊤:ℕ∞)) (f i))
    (v : ℕ → ι → ℝ) (hv : ∀ n, Summable (v n))
    (hbound : ∀ n i x, x∈s → ‖iteratedFDeriv ℝ n (f i) x‖≤v n i) :
    HasFTaylorSeriesUpToOn (↑(⊤:ℕ∞)) (fun x => ∑' i, f i x)
      (fun x n => ∑' i, iteratedFDeriv ℝ n (f i) x) s := by
  constructor
  · intro x hx
    simp_rw [iteratedFDeriv_zero_eq_comp,Function.comp_apply]
    have he : (continuousMultilinearCurryFin0 ℝ E F).symm (∑' i, f i x) =
        ∑' i, (continuousMultilinearCurryFin0 ℝ E F).symm (f i x) :=
      (continuousMultilinearCurryFin0 ℝ E F).symm.toContinuousLinearEquiv.map_tsum
    rw [←he]
    exact (continuousMultilinearCurryFin0 ℝ E F).apply_symm_apply _
  · intro n hn x hx
    have hd : HasFDerivAt (fun y => ∑' i, iteratedFDeriv ℝ n (f i) y)
        (∑' i, fderiv ℝ (iteratedFDeriv ℝ n (f i)) x) x := by
      apply hasFDerivAt_tsum_of_isPreconnected (hv (n+1)) hs hsc
        (x₀ := x) (x := x)
      · intro i y hy
        exact ((hf i).differentiable_iteratedFDeriv (m := n) (by exact_mod_cast (ENat.natCast_lt_top n))).differentiableAt.hasFDerivAt
      · intro i y hy
        simpa only [fderiv_iteratedFDeriv,Function.comp_apply,LinearIsometryEquiv.norm_map]
          using hbound (n+1) i y hy
      · exact hx
      · exact Summable.of_norm_bounded (hv n) (fun i => hbound n i x hx)
      · exact hx
    convert hd.hasFDerivWithinAt (s := s) using 1
    all_goals try with_reducible_and_instances rfl
    simp_rw [fderiv_iteratedFDeriv,Function.comp_apply]
    exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1) => E) F).toContinuousLinearEquiv.map_tsum
  · intro n hn
    exact continuousOn_tsum (fun i => ((hf i).continuous_iteratedFDeriv (m := n) (by exact_mod_cast (le_top : (n:ℕ∞)≤⊤))).continuousOn)
      (hv n) (fun i x hx => hbound n i x hx)

lemma local_smooth_tsum {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : ι → E → F} {s : Set E} (hs : IsOpen s) (hsc : IsPreconnected s)
    (hf : ∀ i, ContDiff ℝ (↑(⊤:ℕ∞)) (f i))
    (v : ℕ → ι → ℝ) (hv : ∀ n, Summable (v n))
    (hbound : ∀ n i x, x∈s → ‖iteratedFDeriv ℝ n (f i) x‖≤v n i) :
    ContDiffOn ℝ (↑(⊤:ℕ∞)) (fun x => ∑' i, f i x) s :=
  (local_smooth_taylor hs hsc hf v hv hbound).contDiffOn

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_TorusFourierSmooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology

lemma axial_halfspace_open (δ : ℝ) : IsOpen {x : Fin 3 → ℝ | δ<x 0} :=
  isOpen_lt continuous_const (continuous_apply 0)

lemma axial_halfspace_connected (δ : ℝ) : IsPreconnected {x : Fin 3 → ℝ | δ<x 0} :=
  (convex_halfSpace_gt (𝕜 := ℝ) (f := fun x : Fin 3 → ℝ => x 0)
    ⟨fun _ _ => rfl,fun _ _ => rfl⟩ δ).isPreconnected

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_TorusPoissonContinuous
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity

open MeasureTheory Filter Topology UnitAddTorus Real Set
open scoped ENNReal

lemma complex_mode_real (c : ℂ) (r θ : ℝ) :
    ((exp r:ℂ)*c*Complex.exp ((θ:ℂ)*Complex.I)).re=
      c.re*(exp r*cos θ)+c.im*(exp r*cos (θ+Real.pi/2)) := by
  rw [Complex.exp_mul_I]
  rw [←Complex.ofReal_cos, ←Complex.ofReal_sin]
  simp only [Complex.add_re, Complex.add_im,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,
    Complex.ofReal_im,Complex.I_re,Complex.I_im]
  rw [cos_add_pi_div_two]
  ring

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

abbrev FiniteAxisJets (R : ℝ) := PiLp 2 (fun _ : Fin 4 => FiniteAxisL2 R)

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

open Set MeasureTheory Filter Topology
open scoped ENNReal

abbrev SpectralModeFiber := PiLp 2 (fun _ : Fin 2 => ℂ)

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

def sourceCollarOpenBox : Set (Fin 3 → ℝ) :=
  {x | (-(1:ℝ)/100 < x 0 ∧ x 0 < 1/100) ∧ |x 1|<1 ∧ |x 2|<1}

lemma isOpen_sourceCollarOpenBox : IsOpen sourceCollarOpenBox := by
  exact ((isOpen_lt continuous_const (continuous_apply 0)).inter
    (isOpen_lt (continuous_apply 0) continuous_const)).inter
    ((isOpen_lt (continuous_apply 1).abs continuous_const).inter
      (isOpen_lt (continuous_apply 2).abs continuous_const))

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_PhysicalEndDifferential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus Matrix

lemma realCLM_apply_basis {n : Type*} [Fintype n] [DecidableEq n]
    (L : (n → ℝ) →L[ℝ] ℝ) (v : n → ℝ) :
    L v = (fun k => L (Pi.single k 1)) ⬝ᵥ v := by
  have hv : (∑ k,Pi.single k (v k))=v := LinearMap.sum_single_apply (fun _ : n => ℝ) v
  conv_lhs => rw [←hv]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  have hk : Pi.single k (v k)=v k • Pi.single k (1:ℝ) := by
    rw [←Pi.single_smul]; simp
  rw [hk,map_smul]
  change v k*L (Pi.single k 1)=L (Pi.single k 1)*v k
  ring

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

def LocalLipAt {E F : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F]
    (f : E → F) (x : E) : Prop := ∃ K,∃ t∈𝓝 x,LipschitzOnWith K f t

lemma LocalLipAt.continuousAt {E F : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F]
    {f : E → F} {x : E} (h : LocalLipAt f x) : ContinuousAt f x := by
  obtain ⟨K,t,ht,hh⟩ := h
  exact hh.continuousOn.continuousAt ht

lemma LocalLipAt.comp {E F G : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F]
    [PseudoMetricSpace G] {f : E → F} {g : F → G} {x : E}
    (hg : LocalLipAt g (f x)) (hf : LocalLipAt f x) : LocalLipAt (g ∘ f) x := by
  have hcont := hf.continuousAt
  obtain ⟨K,t,ht,hK⟩ := hf
  obtain ⟨L,u,hu,hL⟩ := hg
  refine ⟨L*K,t∩f⁻¹' u,inter_mem ht (hcont hu),?_⟩
  exact hL.comp (hK.mono inter_subset_left) ((mapsTo_preimage f u).mono_left inter_subset_right)

lemma LocalLipAt.prodMk {E F G : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F]
    [PseudoMetricSpace G] {f : E → F} {g : E → G} {x : E}
    (hf : LocalLipAt f x) (hg : LocalLipAt g x) : LocalLipAt (fun y => (f y,g y)) x := by
  obtain ⟨K,t,ht,hK⟩ := hf
  obtain ⟨L,u,hu,hL⟩ := hg
  exact ⟨max K L,t∩u,inter_mem ht hu,(hK.mono inter_subset_left).prodMk (hL.mono inter_subset_right)⟩

lemma LocalLipAt.congr {E F : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F]
    {f g : E → F} {x : E} (hf : LocalLipAt f x) (hfg : f=ᶠ[𝓝 x]g) : LocalLipAt g x := by
  obtain ⟨K,t,ht,hK⟩ := hf
  refine ⟨K,t∩{y | f y=g y},inter_mem ht hfg,?_⟩
  intro y hy z hz
  have hyy : f y=g y := hy.2
  have hzz : f z=g z := hz.2
  simpa only [←hyy,←hzz] using hK hy.1 hz.1

lemma localLipAt_of_contDiffAt {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {x : E}
    (h : ContDiffAt ℝ 1 f x) : LocalLipAt f x := h.exists_lipschitzOnWith

lemma localLipschitz_abs : LipschitzWith 1 (fun r : ℝ => |r|) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [NNReal.coe_one,one_mul,Real.dist_eq] using abs_abs_sub_abs_le_abs_sub x y

def localComplexArg (z₀ z : ℂ) : ℝ := (z/z₀).arg+z₀.arg

lemma localComplexArg_contDiffAt {z : ℂ} (hz : z≠0) :
    ContDiffAt ℝ 1 (localComplexArg z) z := by
  have hd : ContDiffAt ℝ 1 (fun w : ℂ => w/z) z := by fun_prop
  have hlog : ContDiffAt ℝ 1 Complex.log (z/z) :=
    (Complex.contDiffAt_log (by simpa only [div_self hz] using Complex.one_mem_slitPlane)).restrict_scalars ℝ
  have hi := Complex.imCLM.contDiff.contDiffAt.comp z (hlog.comp (f:=fun w : ℂ => w/z) z hd)
  change ContDiffAt ℝ 1 (fun w : ℂ => (w/z).arg+z.arg) z
  simpa only [Function.comp_apply,Complex.imCLM_apply,Complex.log_im] using hi.add contDiffAt_const

lemma localComplexArg_unitAngle {z₀ z : ℂ} (h₀ : z₀≠0) (hz : z≠0) :
    ((localComplexArg z₀ z/(2*Real.pi):ℝ):UnitAddCircle)=complexUnitAngle z := by
  have ha := Complex.arg_div_coe_angle hz h₀
  change (((z/z₀).arg:ℝ):AddCircle (2*Real.pi)) =
    ((z.arg:ℝ):AddCircle (2*Real.pi))-((z₀.arg:ℝ):AddCircle (2*Real.pi)) at ha
  have hh := congrArg (AddCircle.equivAddCircle (2*Real.pi) (1:ℝ)
    (by positivity) one_ne_zero) ha
  rw [map_sub,AddCircle.equivAddCircle_apply_mk,AddCircle.equivAddCircle_apply_mk,
    AddCircle.equivAddCircle_apply_mk] at hh
  simp only [mul_one,←div_eq_mul_inv] at hh
  unfold localComplexArg complexUnitAngle
  rw [add_div,AddCircle.coe_add,hh]
  abel

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

def endAxialAffine (a b : ℝ) (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![a*(x 0-b),x 1,x 2]

def endAxialMatrix (a : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := diagonal ![a,1,1]

lemma endAxialAffine_contDiff (a b : ℝ) : ContDiff ℝ (↑(⊤:ℕ∞)) (endAxialAffine a b) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · change ContDiff ℝ _ (fun x : Fin 3 → ℝ => a*(x 0-b))
    fun_prop
  · change ContDiff ℝ _ (fun x : Fin 3 → ℝ => x 1)
    fun_prop
  · change ContDiff ℝ _ (fun x : Fin 3 → ℝ => x 2)
    fun_prop

lemma endAxialAffine_hasFDeriv (a b : ℝ) (x : Fin 3 → ℝ) :
    HasFDerivAt (endAxialAffine a b) (Matrix.toLin' (endAxialMatrix a)).toContinuousLinearMap x := by
  have hc (k : Fin 3) : HasFDerivAt (fun y => endAxialAffine a b y k)
      ((ContinuousLinearMap.proj k : (Fin 3 → ℝ) →L[ℝ] ℝ).comp
        (Matrix.toLin' (endAxialMatrix a)).toContinuousLinearMap) x := by
    fin_cases k
    · convert! ((hasFDerivAt_apply (𝕜:=ℝ) (0:Fin 3) x).sub_const b).const_mul a using 1
      all_goals try with_reducible_and_instances rfl
      ext v
      simp [endAxialMatrix,Matrix.toLin'_apply,Matrix.mulVec_diagonal]
    · convert! hasFDerivAt_apply (𝕜:=ℝ) (1:Fin 3) x using 1
      all_goals try with_reducible_and_instances rfl
      ext v
      simp [endAxialMatrix,Matrix.toLin'_apply,Matrix.mulVec_diagonal]
    · convert! hasFDerivAt_apply (𝕜:=ℝ) (2:Fin 3) x using 1
      all_goals try with_reducible_and_instances rfl
      ext v
      simp [endAxialMatrix,Matrix.toLin'_apply,Matrix.mulVec_diagonal]
  convert! hasFDerivAt_pi.mpr hc using 1
  all_goals try with_reducible_and_instances rfl

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_AffineCylinder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal

def affineEndTime (a b : ℝ) (t : ℝ) : ℝ := a*(t-b)

def affineEndCoordinates (a b : ℝ) : ℝ×UnitAddTorus (Fin 2) → ℝ×UnitAddTorus (Fin 2) :=
  Prod.map (affineEndTime a b) id

lemma measurable_affineEndTime (a b : ℝ) : Measurable (affineEndTime a b) := by
  unfold affineEndTime; fun_prop

lemma measurable_affineEndCoordinates (a b : ℝ) : Measurable (affineEndCoordinates a b) :=
  (measurable_affineEndTime a b).prodMap measurable_id

lemma affineEndTime_volume {a : ℝ} (ha : a≠0) (b : ℝ) :
    Measure.map (affineEndTime a b) volume=ENNReal.ofReal |a⁻¹| • volume := by
  have he : affineEndTime a b=(fun t => a*t) ∘ (fun t : ℝ => t+(-b)) := by
    funext t; simp [affineEndTime,sub_eq_add_neg]
  rw [he,←Measure.map_map (f:=fun t : ℝ => t+(-b)) (g:=fun t : ℝ => a*t)
    (by fun_prop) (by fun_prop),map_add_right_eq_self,Real.map_volume_mul_left ha]

lemma affineEndTime_interval_le {a b l r R : ℝ} (ha : a≠0)
    (hT : ∀ t∈Icc l r,affineEndTime a b t∈Icc 0 R) :
    Measure.map (affineEndTime a b) (volume.restrict (Ioc l r)) ≤
      ENNReal.ofReal |a⁻¹| • FiniteAxisMeasure R := by
  have hS : Ioc l r⊆(affineEndTime a b) ⁻¹' Icc 0 R := fun t ht => hT t ⟨ht.1.le,ht.2⟩
  have hle : Measure.map (affineEndTime a b) (volume.restrict (Ioc l r)) ≤
      (Measure.map (affineEndTime a b) volume).restrict (Icc 0 R) := by
    rw [Measure.restrict_map (measurable_affineEndTime a b) measurableSet_Icc]
    exact Measure.map_mono (Measure.restrict_mono hS le_rfl) (measurable_affineEndTime a b)
  have hcc : volume.restrict (Icc (0:ℝ) R)=FiniteAxisMeasure R := by
    exact Measure.restrict_congr_set (Ioc_ae_eq_Icc' (measure_singleton (0:ℝ))).symm
  rwa [affineEndTime_volume ha,Measure.restrict_smul,hcc] at hle

lemma affineEndCoordinates_interval_le {a b l r R : ℝ} (ha : a≠0)
    (hT : ∀ t∈Icc l r,affineEndTime a b t∈Icc 0 R) :
    Measure.map (affineEndCoordinates a b) (sourceCylinderMeasure l r) ≤
      ENNReal.ofReal |a⁻¹| • sourceCylinderMeasure 0 R := by
  unfold sourceCylinderMeasure
  rw [affineEndCoordinates,←Measure.map_prod_map _ _ (measurable_affineEndTime a b) measurable_id,
    Measure.map_id,←Measure.prod_smul_left]
  exact Measure.prod_mono (affineEndTime_interval_le ha hT) le_rfl

def affineEndPullback {a b l r R : ℝ} (ha : a≠0)
    (hT : ∀ t∈Icc l r,affineEndTime a b t∈Icc 0 R) :
    Lp ℂ 2 (sourceCylinderMeasure 0 R) →L[ℝ] Lp ℂ 2 (sourceCylinderMeasure l r) :=
  ((Lp.compMeasurePreservingₗᵢ ℝ (affineEndCoordinates a b)
    ⟨measurable_affineEndCoordinates a b,rfl⟩).toContinuousLinearMap).comp
      (Lp.LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top (affineEndCoordinates_interval_le ha hT))

lemma affineEndPullback_ae {a b l r R : ℝ} (ha : a≠0)
    (hT : ∀ t∈Icc l r,affineEndTime a b t∈Icc 0 R)
    (f : Lp ℂ 2 (sourceCylinderMeasure 0 R)) :
    affineEndPullback ha hT f=ᵐ[sourceCylinderMeasure l r] f ∘ affineEndCoordinates a b := by
  have h0 := Lp.coeFn_LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top
    (affineEndCoordinates_interval_le ha hT) f
  have h1 := Lp.coeFn_compMeasurePreserving
    (Lp.LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top (affineEndCoordinates_interval_le ha hT) f)
    (show MeasurePreserving (affineEndCoordinates a b) (sourceCylinderMeasure l r)
      (Measure.map (affineEndCoordinates a b) (sourceCylinderMeasure l r)) from
      ⟨measurable_affineEndCoordinates a b,rfl⟩)
  exact h1.trans ((show Measure.QuasiMeasurePreserving (affineEndCoordinates a b) (sourceCylinderMeasure l r)
    (Measure.map (affineEndCoordinates a b) (sourceCylinderMeasure l r)) from
    ⟨measurable_affineEndCoordinates a b,Measure.absolutelyContinuous_rfl⟩).ae_eq_comp h0)

lemma affineEndPullback_ae_of_ae {a b l r R : ℝ} (ha : a≠0)
    (hT : ∀ t∈Icc l r,affineEndTime a b t∈Icc 0 R)
    (f : Lp ℂ 2 (sourceCylinderMeasure 0 R)) {g : ℝ×UnitAddTorus (Fin 2) → ℂ}
    (hg : f=ᵐ[sourceCylinderMeasure 0 R] g) :
    affineEndPullback ha hT f=ᵐ[sourceCylinderMeasure l r] g ∘ affineEndCoordinates a b := by
  apply (affineEndPullback_ae ha hT f).trans
  have hq : Measure.QuasiMeasurePreserving (affineEndCoordinates a b) (sourceCylinderMeasure l r)
      (sourceCylinderMeasure 0 R) :=
    ⟨measurable_affineEndCoordinates a b,
      Measure.absolutelyContinuous_of_le_smul (affineEndCoordinates_interval_le ha hT)⟩
  exact hq.ae_eq_comp hg

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_CompletedPotential
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
namespace ScalarConductivity

def completedPotential {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (u : E → F) (D : E →L[ℝ] F) (Q : F →L[ℝ] E) (y : E) : E :=
  Q (u y) + y - Q (D y)

lemma completedPotential_pairing {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (u : E → F) (D : E →L[ℝ] F) (Q : F →L[ℝ] E)
    (hQ : Function.RightInverse Q D) (y : E) :
    D (completedPotential u D Q y) = u y := by
  simp only [completedPotential, map_sub, map_add, hQ (u y), hQ (D y)]
  abel

lemma completedPotential_smooth {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : E → F} (hu : ContDiff ℝ (↑(⊤ : ℕ∞)) u)
    (D : E →L[ℝ] F) (Q : F →L[ℝ] E) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (completedPotential u D Q) :=
  ((Q.contDiff.comp hu).add contDiff_id).sub (Q.contDiff.comp D.contDiff)

lemma completedPotential_derivative {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : E → F} {D : E →L[ℝ] F} {a : E} (hu : HasFDerivAt u D a)
    (Q : F →L[ℝ] E) :
    HasFDerivAt (completedPotential u D Q) (ContinuousLinearMap.id ℝ E) a := by
  convert ((Q.hasFDerivAt.comp a hu).add (hasFDerivAt_id a)).sub
    (Q.hasFDerivAt.comp a D.hasFDerivAt) using 1
  · rfl
  · abel

theorem exists_potential_chart
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {u : E → F} (hu : ContDiff ℝ (↑(⊤ : ℕ∞)) u) (a : E)
    (hD : Function.Surjective (fderiv ℝ u a)) {U : Set E} (hU : IsOpen U) (ha : a ∈ U) :
    ∃ X : OpenPartialHomeomorph E E,
      a ∈ X.source ∧ X.source ⊆ U ∧
      ContDiff ℝ (↑(⊤ : ℕ∞)) X ∧
      ContDiffOn ℝ (↑(⊤ : ℕ∞)) X.symm X.target ∧
      (∀ y, (fderiv ℝ u a) (X y) = u y) ∧
      fderiv ℝ X a = ContinuousLinearMap.id ℝ E := by
  let D := fderiv ℝ u a
  obtain ⟨Q, hQ⟩ := ContinuousLinearMap.HasRightInverse.of_surjective_of_finiteDimensional hD
  let f := completedPotential u D Q
  have hf := completedPotential_smooth hu D Q
  have hfa : HasFDerivAt f (ContinuousLinearEquiv.refl ℝ E : E →L[ℝ] E) a :=
    completedPotential_derivative ((hu.differentiable (by simp) a).hasFDerivAt) Q
  let X₀ := hf.contDiffAt.toOpenPartialHomeomorph f hfa (by simp)
  let V := U ∩ {y | IsUnit (fderiv ℝ f y)}
  have hV : IsOpen V := hU.inter (Units.isOpen.preimage (hf.continuous_fderiv (by simp)))
  have haV : a ∈ V := ⟨ha, by change IsUnit (fderiv ℝ f a); rw [hfa.fderiv]; exact isUnit_one⟩
  let X := X₀.restr V
  have hXeq : (X : E → E) = f := rfl
  have hsource : X.source = X₀.source ∩ V := by
    simp only [X, OpenPartialHomeomorph.restr_source, hV.interior_eq]
  have hinv : ContDiffOn ℝ (↑(⊤ : ℕ∞)) X.symm X.target := by
    intro y hy
    have hx : X.symm y ∈ V := (hsource ▸ X.map_target hy).2
    obtain ⟨v, hv⟩ := hx.2
    let e : E ≃L[ℝ] E := ContinuousLinearEquiv.ofUnit v
    have he : (e : E →L[ℝ] E) = fderiv ℝ X (X.symm y) := by
      change (v : E →L[ℝ] E) = _
      simpa only [hXeq] using hv
    have hd : HasFDerivAt X (e : E →L[ℝ] E) (X.symm y) := by
      rw [he, hXeq]
      exact (hf.differentiable (by simp) _).hasFDerivAt
    exact (X.contDiffAt_symm hy hd (hXeq ▸ hf.contDiffAt)).contDiffWithinAt
  refine ⟨X, ?_, ?_, ?_, hinv, ?_, ?_⟩
  · rw [hsource]
    exact ⟨hf.contDiffAt.mem_toOpenPartialHomeomorph_source hfa (by simp), haV⟩
  · rw [hsource]
    exact fun _ hx => hx.2.1
  · rw [hXeq]
    exact hf
  · intro y
    exact completedPotential_pairing u D Q hQ y
  · exact hfa.fderiv

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

open MeasureTheory Set Filter Topology

lemma measure_image_le_det
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    {f : E → E} {s : Set E} (hs : MeasurableSet s)
    (hf : ∀ x ∈ s, DifferentiableAt ℝ f x) (hinj : InjOn f s)
    {C : ℝ} (hC : ∀ x ∈ s, |(fderiv ℝ f x).det| ≤ C) :
    μ (f '' s) ≤ ENNReal.ofReal C * μ s := by
  rw [← lintegral_abs_det_fderiv_eq_addHaar_image μ hs
    (fun x hx => (hf x hx).hasFDerivAt.hasFDerivWithinAt) hinj]
  calc
    (∫⁻ x in s, ENNReal.ofReal |(fderiv ℝ f x).det| ∂μ) ≤
        ∫⁻ _ in s, ENNReal.ofReal C ∂μ :=
      setLIntegral_mono' hs (fun x hx => ENNReal.ofReal_le_ofReal (hC x hx))
    _ = _ := by simp

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_AttachedEndLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory Filter Topology
open scoped ENNReal

lemma lp_norm_le_sum_norm_of_ae {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    {μ : Measure X} {u : Lp ℝ 2 μ} {v : ι → Lp ℂ 2 μ} {C : ℝ} (hC : 0≤C)
    (h : ∀ᵐ x∂μ,‖u x‖≤C*∑ i,‖v i x‖) : ‖u‖≤C*∑ i,‖v i‖ := by
  let w : ι → Lp ℝ 2 μ := fun i => ((Lp.memLp (v i)).norm).toLp (fun x => ‖v i x‖)
  have he (i : ι) : w i=ᵐ[μ] (fun x => ‖v i x‖) := ((Lp.memLp (v i)).norm).coeFn_toLp
  have hn (i : ι) : ‖w i‖=‖v i‖ := by
    dsimp only [w]
    rw [Lp.norm_toLp,eLpNorm_norm (v i),Lp.norm_def]
  have hh : ‖u‖≤‖C • ∑ i,w i‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [h,Lp.coeFn_smul C (∑ i,w i),Lp.coeFn_fun_finsetSum Finset.univ w,
      ae_all_iff.mpr he] with x hx hs hsum hw
    rw [hs]
    simp only [Pi.smul_apply,smul_eq_mul,hsum,hw]
    simpa only [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hC (Finset.sum_nonneg (fun i _ => norm_nonneg (v i x))))] using hx
  calc
    ‖u‖ ≤ ‖C • ∑ i,w i‖ := hh
    _ = C*‖∑ i,w i‖ := by rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hC]
    _ ≤ C*∑ i,‖w i‖ := mul_le_mul_of_nonneg_left (norm_sum_le _ _) hC
    _ = C*∑ i,‖v i‖ := by simp only [hn]

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

local instance smoothCollarRateMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_AffineLayer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma affine_layer_interval {a b ε : ℝ} (ha : a≠0) (hε : 0≤ε) :
    let l := min b (b+ε/a)
    let r := max b (b+ε/a)
    r-l=ε/|a| ∧
    b-ε/|a|≤l ∧ r≤b+ε/|a| ∧
    (∀ t,t∈Icc l r ↔ a*(t-b)∈Icc 0 ε) ∧
    (∀ t∈Icc l r,|t-b|≤ε/|a|) := by
  dsimp only
  have hc : a*(ε/a)=ε := by field_simp
  rcases lt_or_gt_of_ne ha with hn|hp
  · have hd : ε/a≤0 := div_nonpos_of_nonneg_of_nonpos hε hn.le
    rw [min_eq_right (by linarith : b+ε/a≤b),max_eq_left (by linarith : b+ε/a≤b),abs_of_neg hn,div_neg]
    refine ⟨by ring,by linarith,by linarith,?_,?_⟩
    · intro t
      constructor
      · intro ht
        have h1 := mul_le_mul_of_nonpos_left ht.2 hn.le
        have h2 := mul_le_mul_of_nonpos_left ht.1 hn.le
        constructor <;> nlinarith
      · intro ht
        constructor
        · apply (mul_le_mul_left_of_neg hn).mp
          nlinarith [ht.2]
        · apply (mul_le_mul_left_of_neg hn).mp
          nlinarith [ht.1]
    · intro t ht
      apply abs_le.mpr
      constructor <;> linarith [ht.1,ht.2]
  · have hd : 0≤ε/a := div_nonneg hε hp.le
    rw [min_eq_left (by linarith : b≤b+ε/a),max_eq_right (by linarith : b≤b+ε/a),abs_of_pos hp]
    refine ⟨by ring,by linarith,le_refl _,?_,?_⟩
    · intro t
      constructor
      · intro ht
        have h1 := mul_le_mul_of_nonneg_left ht.1 hp.le
        have h2 := mul_le_mul_of_nonneg_left ht.2 hp.le
        constructor <;> nlinarith
      · intro ht
        constructor
        · apply (mul_le_mul_iff_right₀ hp).mp
          nlinarith [ht.1]
        · apply (mul_le_mul_iff_right₀ hp).mp
          nlinarith [ht.2]
    · intro t ht
      apply abs_le.mpr
      constructor <;> linarith [ht.1,ht.2]

lemma seamLayer_scaled_tendsto_of_cubic_pi {τ u : (Fin 3 → ℝ) → ℝ}
    {δ A : ℝ} (hδ : 0<δ)
    (hbound : ∀ ε,0<ε → ε≤δ → (∫ x in {x | 0<τ x ∧ τ x≤ε},u x^2)≤A*ε^3) :
    Tendsto (fun n : ℕ => ((n:ℝ)+1)^2*∫ x in {x | 0<τ x ∧ ((n:ℝ)+1)*τ x≤2},u x^2) atTop (𝓝 0) := by
  have hn (n : ℕ) : 0<(n:ℝ)+1 := by positivity
  have ht : Tendsto (fun n : ℕ => ((n:ℝ)+1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop (1:ℝ) tendsto_natCast_atTop_atTop)
  have he : ∀ᶠ n : ℕ in atTop,2/((n:ℝ)+1)≤δ := by
    have hh := ht.const_mul 2
    simp only [mul_zero] at hh
    simpa only [←div_eq_mul_inv] using (hh.eventually (gt_mem_nhds hδ)).mono (fun _ h => h.le)
  have hlim := ht.const_mul (8*A)
  simp only [mul_zero] at hlim
  apply squeeze_zero' (Eventually.of_forall (fun n => mul_nonneg (sq_nonneg _) (integral_nonneg (fun _ => sq_nonneg _)))) _ hlim
  filter_upwards [he] with n hnδ
  have hs : {x | 0<τ x ∧ ((n:ℝ)+1)*τ x≤2}={x | 0<τ x ∧ τ x≤2/((n:ℝ)+1)} := by
    ext x
    exact and_congr_right (fun _ => by rw [le_div_iff₀ (hn n),mul_comm])
  rw [hs]
  have hb := mul_le_mul_of_nonneg_left (hbound _ (div_pos (by norm_num) (hn n)) hnδ) (sq_nonneg ((n:ℝ)+1))
  apply hb.trans_eq
  field_simp
  ring

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_BoundedMultiplier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ScalarConductivity

theorem boundedMultiplier_memLp {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (μ : Measure α)
    (a : α → ℝ) (ha : AEStronglyMeasurable a μ)
    (C : ℝ) (haC : ∀ᵐ x ∂μ, |a x| ≤ C) (f : Lp E 2 μ) :
    MemLp (fun x => a x • f x) 2 μ :=
  (Lp.memLp f).of_le_mul (ha.smul (Lp.aestronglyMeasurable f)) (by
    filter_upwards [haC] with x hx
    simpa only [norm_smul, Real.norm_eq_abs] using
      mul_le_mul_of_nonneg_right hx (norm_nonneg (f x)))

def boundedMultiplier {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (μ : Measure α)
    (a : α → ℝ) (ha : AEStronglyMeasurable a μ)
    (C : ℝ) (_hC : 0 ≤ C) (haC : ∀ᵐ x ∂μ, |a x| ≤ C) :
    Lp E 2 μ →L[ℝ] Lp E 2 μ := by
  let hmem := boundedMultiplier_memLp (E := E) μ a ha C haC
  let T : Lp E 2 μ →ₗ[ℝ] Lp E 2 μ := {
    toFun := fun f => (hmem f).toLp _
    map_add' := by
      intro f g
      apply Lp.ext
      filter_upwards [(hmem (f + g)).coeFn_toLp, (hmem f).coeFn_toLp,
        (hmem g).coeFn_toLp, Lp.coeFn_add f g,
        Lp.coeFn_add ((hmem f).toLp _) ((hmem g).toLp _)] with x hfg hf hg hsum hsum'
      simp only [Pi.add_apply] at hsum hsum'
      rw [hfg, hsum', hf, hg, hsum, smul_add]
    map_smul' := by
      intro c f
      apply Lp.ext
      filter_upwards [(hmem (c • f)).coeFn_toLp, (hmem f).coeFn_toLp,
        Lp.coeFn_smul c f, Lp.coeFn_smul c ((hmem f).toLp _)] with x hcf hf hc hc'
      change ((hmem (c • f)).toLp _) x = (c • ((hmem f).toLp _)) x
      simp only [Pi.smul_apply] at hc hc'
      rw [hcf, hc', hf, hc]
      exact smul_comm _ _ _ }
  exact T.mkContinuous C (fun f => Lp.norm_le_mul_norm_of_ae_le_mul (by
    filter_upwards [(hmem f).coeFn_toLp, haC] with x hx hxC
    change ‖((hmem f).toLp _) x‖ ≤ C * ‖f x‖
    rw [hx, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right hxC (norm_nonneg _)))

def jetGradient : JetFiber →L[ℝ] R3 :=
  LinearMap.toContinuousLinearMap {
    toFun := fun z => WithLp.toLp 2 (fun i => z i.succ)
    map_add' := by intro x y; rfl
    map_smul' := by intro c x; rfl }

def weakGradientL : H1 →L[ℝ] Lp R3 2 ballMeasure :=
  (jetGradient.compLpL 2 ballMeasure).comp H1Space.subtypeL

def energyForm (a : R3 → ℝ) (ha : AEStronglyMeasurable a ballMeasure)
    (C : ℝ) (hC : 0 ≤ C) (haC : ∀ᵐ x ∂ballMeasure, |a x| ≤ C) :
    H1 →L[ℝ] H1 →L[ℝ] ℝ :=
  ((innerSL ℝ).comp (boundedMultiplier ballMeasure a ha C hC haC |>.comp weakGradientL))
    |>.flip.comp weakGradientL |>.flip

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_MatrixFiniteLaminate
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

open Set Filter Topology

instance H1_isClosed : IsClosed (H1Space : Set JetSpace) :=
  Submodule.isClosed_topologicalClosure _

instance H1_completeSpace : CompleteSpace H1 :=
  (H1_isClosed : IsClosed (H1Space : Set JetSpace)).completeSpace_coe

instance H10_completeSpace : CompleteSpace H10 :=
  (H10_isClosed : IsClosed (H10 : Set H1)).completeSpace_coe

def jetValue : JetFiber →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap {
    toFun := fun z => z 0
    map_add' := by intro x y; rfl
    map_smul' := by intro c x; rfl }

lemma smoothJet_zero : smoothJet (fun _ : R3 => (0 : ℝ)) = 0 := by
  ext x i
  refine Fin.cases ?_ (fun i => ?_) i <;> simp [smoothJet, gradient]

lemma smoothJet_add {f g : R3 → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    smoothJet (f + g) = smoothJet f + smoothJet g := by
  ext x i
  refine Fin.cases ?_ (fun i => ?_) i
  · rfl
  · simp [smoothJet, gradient, fderiv_add (hf x) (hg x)]

lemma smoothJet_smul (c : ℝ) {f : R3 → ℝ} (hf : Differentiable ℝ f) :
    smoothJet (c • f) = c • smoothJet f := by
  ext x i
  refine Fin.cases ?_ (fun i => ?_) i
  · rfl
  · simp [smoothJet, gradient, fderiv_const_smul (hf x)]

lemma compactSmoothJets_zero : (0 : JetSpace) ∈ compactSmoothJets := by
  refine ⟨fun _ => 0, contDiff_const, HasCompactSupport.zero, ?_, ?_, ?_⟩
  · simp
  · rw [smoothJet_zero]; exact MemLp.zero
  · simp only [smoothJet_zero, MemLp.toLp_zero]

def ballPoincareConstant : ℝ :=
  eLpNormLESNormFDerivOfLeConst ℝ (volume : Measure R3) ball 2 2

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_NonlinearLp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory Filter Topology
open scoped ENNReal

lemma unifIntegrable_of_norm_domination
    {X E F ι : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    {μ : Measure X} {p : ℝ≥0∞} {f : ι → X → E} {g : ι → X → F}
    (hf : UnifIntegrable f p μ) (hg : ∀ i, AEStronglyMeasurable (g i) μ)
    (hfg : ∀ i, ∀ᵐ x ∂μ, ‖g i x‖≤‖f i x‖) :
    UnifIntegrable g p μ := by
  intro ε hε
  obtain ⟨δ,hδ,hb⟩ := hf hε
  refine ⟨δ,hδ,fun index region hregion hμ => ?_⟩
  refine (eLpNorm_mono_ae ?_).trans (hb index region hregion hμ)
  filter_upwards [hfg index] with x hx
  by_cases h : x ∈ region
  · simpa [Set.indicator_of_mem h] using hx
  · simp [Set.indicator_of_notMem h]

lemma continuous_comp_tendstoInMeasure
    {X E F : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    {μ : Measure X} [IsFiniteMeasure μ]
    {f : ℕ → X → E} {g : X → E} (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (hfg : TendstoInMeasure μ f atTop g) {T : E → F} (hT : Continuous T) :
    TendstoInMeasure μ (fun n x => T (f n x)) atTop (fun x => T (g x)) := by
  apply (exists_seq_tendstoInMeasure_atTop_iff (fun n => hT.comp_aestronglyMeasurable (hf n))).mpr
  intro ns hns
  obtain ⟨ms,hms,hlim⟩ := (hfg.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨ms,hms,?_⟩
  filter_upwards [hlim] with x hx
  exact hT.continuousAt.tendsto.comp hx

lemma nonlinear_memLp
    {X E F : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (μ : Measure X) {T : E → F} (hT : Continuous T) {C : ℝ}
    (hC : 0≤C) (hb : ∀ z, ‖T z‖≤C*‖z‖) (f : Lp E 2 μ) :
    MemLp (fun x => T (f x)) 2 μ := by
  apply ((Lp.memLp f).const_smul C).mono (hT.comp_aestronglyMeasurable (Lp.aestronglyMeasurable f))
  filter_upwards [] with x
  simpa only [Pi.smul_apply,norm_smul,Real.norm_of_nonneg hC] using hb (f x)

def nonlinearLp
    {X E F : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (μ : Measure X) (T : E → F) (hT : Continuous T) (C : ℝ)
    (hC : 0≤C) (hb : ∀ z, ‖T z‖≤C*‖z‖) (f : Lp E 2 μ) : Lp F 2 μ :=
  (nonlinear_memLp μ hT hC hb f).toLp _

lemma nonlinearLp_coe_ae
    {X E F : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (μ : Measure X) (T : E → F) (hT : Continuous T) (C : ℝ)
    (hC : 0≤C) (hb : ∀ z, ‖T z‖≤C*‖z‖) (f : Lp E 2 μ) :
    nonlinearLp μ T hT C hC hb f =ᵐ[μ] fun x => T (f x) :=
  MemLp.coeFn_toLp _

theorem nonlinearLp_continuous
    {X E F : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (μ : Measure X) [IsFiniteMeasure μ] (T : E → F) (hT : Continuous T) (C : ℝ)
    (hC : 0≤C) (hb : ∀ z, ‖T z‖≤C*‖z‖) :
    Continuous (nonlinearLp μ T hT C hC hb) := by
  apply continuous_iff_seqContinuous.mpr
  intro f g hfg
  have hfI := continuous_comp_tendstoInMeasure (fun n => Lp.aestronglyMeasurable (f n))
    (tendstoInMeasure_of_tendsto_Lp hfg) hT
  have hCseq : Tendsto (fun n => C • f n) atTop (𝓝 (C • g)) := hfg.const_smul C
  have hUI := unifIntegrable_of_tendsto_Lp (p := (2:ℝ≥0∞)) (by norm_num) (by norm_num)
    (fun n => Lp.memLp (C • f n)) (Lp.memLp (C • g))
    ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mp hCseq)
  have hUI' : UnifIntegrable (fun n x => T (f n x)) 2 μ := by
    apply unifIntegrable_of_norm_domination hUI
      (fun n => hT.comp_aestronglyMeasurable (Lp.aestronglyMeasurable (f n)))
    intro n
    filter_upwards [Lp.coeFn_smul C (f n)] with x hx
    rw [hx,Pi.smul_apply,norm_smul,Real.norm_of_nonneg hC]
    exact hb (f n x)
  have hnorm := tendsto_Lp_finite_of_tendstoInMeasure (p := (2:ℝ≥0∞)) (by norm_num) (by norm_num)
    (fun n => hT.comp_aestronglyMeasurable (Lp.aestronglyMeasurable (f n)))
    (nonlinear_memLp μ hT hC hb g) hUI' hfI
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mpr
  apply hnorm.congr
  intro n
  apply eLpNorm_congr_ae
  filter_upwards [nonlinearLp_coe_ae μ T hT C hC hb (f n),
    nonlinearLp_coe_ae μ T hT C hC hb g] with x hx hy
  simp only [Function.comp_apply,Pi.sub_apply,hx,hy]

lemma smoothJets_zero : (0 : JetSpace) ∈ smoothJets := by
  obtain ⟨f,hf,_,_,hm,he⟩ := compactSmoothJets_zero
  exact ⟨f,hf,hm,he⟩

lemma smoothJets_add {z w : JetSpace} (hz : z∈smoothJets) (hw : w∈smoothJets) :
    z+w∈smoothJets := by
  obtain ⟨f,hf,hfm,rfl⟩ := hz
  obtain ⟨g,hg,hgm,rfl⟩ := hw
  have hj := smoothJet_add (hf.differentiable (by simp)) (hg.differentiable (by simp))
  have hm : MemLp (smoothJet (f+g)) 2 ballMeasure := by rw [hj]; exact hfm.add hgm
  refine ⟨f+g,hf.add hg,hm,?_⟩
  apply Lp.ext
  filter_upwards [Lp.coeFn_add (hfm.toLp _) (hgm.toLp _),hfm.coeFn_toLp,
    hgm.coeFn_toLp,hm.coeFn_toLp] with x ha hx hy hz
  rw [ha,hz,hj]
  simp only [Pi.add_apply,hx,hy]

lemma smoothJets_smul (c : ℝ) {z : JetSpace} (hz : z∈smoothJets) :
    c • z∈smoothJets := by
  obtain ⟨f,hf,hfm,rfl⟩ := hz
  have hj := smoothJet_smul c (hf.differentiable (by simp))
  have hm : MemLp (smoothJet (c • f)) 2 ballMeasure := by rw [hj]; exact hfm.const_smul c
  refine ⟨c • f,hf.const_smul c,hm,?_⟩
  apply Lp.ext
  filter_upwards [Lp.coeFn_smul c (hfm.toLp _),hfm.coeFn_toLp,hm.coeFn_toLp] with x ha hx hy
  rw [ha,hy,hj]
  simp only [Pi.smul_apply,hx]

lemma span_smoothJets : (Submodule.span ℝ smoothJets : Set JetSpace)=smoothJets := by
  let K : Submodule ℝ JetSpace := {
    carrier := smoothJets
    zero_mem' := smoothJets_zero
    add_mem' := smoothJets_add
    smul_mem' := smoothJets_smul }
  exact congrArg SetLike.coe (Submodule.span_eq K)

lemma H1Space_eq_closure : (H1Space : Set JetSpace)=closure smoothJets := by
  change closure (Submodule.span ℝ smoothJets : Set JetSpace)=closure smoothJets
  rw [span_smoothJets]

lemma nonlinear_closure_preservation {X : Type*} [TopologicalSpace X]
    {T : X → X} (hT : Continuous T) {S : Set X} (hS : MapsTo T S S) :
    MapsTo T (closure S) (closure S) := by
  intro x hx
  exact (image_closure_subset_closure_image hT).trans (closure_mono hS.image_subset) ⟨x,hx,rfl⟩

lemma gradient_comp_scalar {g dg : ℝ → ℝ} (hdg : ∀ r, HasDerivAt g (dg r) r)
    {f : R3 → ℝ} (hf : Differentiable ℝ f) (x : R3) :
    gradient (g ∘ f) x = dg (f x) • gradient f x := by
  unfold gradient
  rw [((hdg (f x)).comp_hasFDerivAt x (hf x).hasFDerivAt).fderiv]
  simp

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_SobolevSmoothOperations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory Filter Topology Real

structure SmoothLipZero where
  toFun : ℝ → ℝ
  smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) toFun
  at_zero : toFun 0=0
  bound : ℝ
  bound_nonneg : 0≤bound
  deriv_bound : ∀ r, ‖deriv toFun r‖≤bound

instance instCoeFunSmoothLipZeroForallReal : CoeFun SmoothLipZero (fun _ => ℝ → ℝ) := ⟨SmoothLipZero.toFun⟩

namespace SmoothLipZero

lemma growth (F : SmoothLipZero) (r : ℝ) : ‖F r‖≤F.bound*‖r‖ := by
  have hh := (convex_univ : Convex ℝ (univ : Set ℝ)).norm_image_sub_le_of_norm_deriv_le
    (fun x _ => F.smooth.differentiable (by simp) x) (fun x _ => F.deriv_bound x)
    (mem_univ (0:ℝ)) (mem_univ r)
  simpa [F.at_zero] using hh

lemma derivative (F : SmoothLipZero) (r : ℝ) : HasDerivAt F (deriv F r) r :=
  (F.smooth.differentiable (by simp) r).hasDerivAt

def ofCompact (g : ℝ → ℝ) (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g)
    (hc : HasCompactSupport g) (hg0 : g 0=0) : SmoothLipZero := by
  let he := hc.deriv.exists_bound_of_continuous (smooth_deriv_infty hg).continuous
  let C := Classical.choose he
  have hC : ∀ r, ‖deriv g r‖ ≤ C := Classical.choose_spec he
  exact ⟨g,hg,hg0,max 0 C,le_max_left _ _,fun r => (hC r).trans (le_max_right _ _)⟩

end SmoothLipZero

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_SobolevTraceChain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory Filter Topology

abbrev weakValue (u : H1) (x : R3) : ℝ := jetValue (u.val x)

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

lemma smoothH1_dense : Dense {u : H1 | u.val∈smoothJets} := by
  intro u
  rw [closure_subtype]
  have he : Subtype.val '' {u : H1 | u.val∈smoothJets}=smoothJets := by
    apply Set.ext; intro z; constructor
    · rintro ⟨u,hu,rfl⟩; exact hu
    · intro hz
      exact ⟨⟨z,(Submodule.le_topologicalClosure _) (Submodule.subset_span hz)⟩,hz,rfl⟩
  rw [he,←H1Space_eq_closure]
  exact u.property

open Set MeasureTheory Filter Topology Real

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

abbrev WeylSpace := EuclideanSpace ℝ (Fin 3)

def radialEta (χ : ℝ → ℝ) (s : ℝ) (x : WeylSpace) : ℝ :=
  χ (‖x‖^2/s^2)/s^3

end

open Set MeasureTheory Filter Topology InnerProductSpace Laplacian
open scoped RealInnerProductSpace

def radialOneBump : ContDiffBump (0:ℝ) :=
  { rIn := 1/2, rOut := 1, rIn_pos := by norm_num, rIn_lt_rOut := by norm_num }

def radialRaw (x : WeylSpace) : ℝ := radialOneBump (‖x‖^2)

def radialMass : ℝ := ∫ x, radialRaw x

def radialProfile (t : ℝ) : ℝ := radialOneBump t/radialMass

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

def WeaklyHarmonicOn (f : WeylSpace → ℝ) (U : Set WeylSpace) : Prop :=
  ∀ ψ : WeylSpace → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
    tsupport ψ⊆U → (∫ y, f y*Δ ψ y)=0

end

open Set MeasureTheory

lemma probability_integral_sq_le {X : Type*} [MeasurableSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ] {f : X → ℝ} (hf : MemLp f 2 μ) :
    (∫ x, f x ∂μ)^2 ≤ ∫ x, f x^2 ∂μ := by
  simpa using integral_sq_le_mass_mul (hf.integrable (by norm_num)) hf.integrable_sq

theorem memLp_probability_average {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [IsProbabilityMeasure μ] [SFinite ν]
    {f : X×Y → ℝ} (hf : MemLp f 2 (μ.prod ν)) :
    MemLp (fun y => ∫ x, f (x,y) ∂μ) 2 ν ∧
    (∫ y, (∫ x, f (x,y) ∂μ)^2 ∂ν) ≤ ∫ z, f z^2 ∂(μ.prod ν) := by
  have hm := hf.aestronglyMeasurable.prod_swap.integral_prod_right'
  have hi := hf.integrable_sq
  have hs : ∀ᵐ y ∂ν, (∫ x, f (x,y) ∂μ)^2 ≤ ∫ x, f (x,y)^2 ∂μ := by
    filter_upwards [hi.prod_left_ae,hf.aestronglyMeasurable.prodMk_right] with y hy hmy
    exact probability_integral_sq_le ((memLp_two_iff_integrable_sq hmy).mpr hy)
  have hia : Integrable (fun y => (∫ x, f (x,y) ∂μ)^2) ν := by
    apply hi.integral_prod_right.mono' (hm.pow 2)
    filter_upwards [hs] with y hy
    change ‖(∫ x, f (x,y) ∂μ)^2‖ ≤ ∫ x, f (x,y)^2 ∂μ
    simpa only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (∫ x, f (x,y) ∂μ))] using hy
  refine ⟨(memLp_two_iff_integrable_sq hm).mpr hia,?_⟩
  calc
    _ ≤ ∫ y, ∫ x, f (x,y)^2 ∂μ ∂ν := integral_mono_ae hia hi.integral_prod_right hs
    _ = _ := (integral_prod_symm _ hi).symm

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_L2TranslationAverage
attribute [-instance] _root_.OAI.ScalarConductivity.H10_completeSpace _root_.OAI.ScalarConductivity.H1_completeSpace _root_.OAI.ScalarConductivity.H1_isClosed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory Filter Topology

abbrev WholeL2 := Lp ℝ 2 (volume : Measure R3)

def translateL2 (y : R3) (f : WholeL2) : WholeL2 :=
  Lp.compMeasurePreserving (fun x => x-y) (measurePreserving_sub_right volume y) f

lemma translateL2_ae (y : R3) (f : WholeL2) :
    (translateL2 y f : R3 → ℝ) =ᵐ[volume] fun x => f (x-y) :=
  Lp.coeFn_compMeasurePreserving _ _

lemma translateL2_norm (y : R3) (f : WholeL2) : ‖translateL2 y f‖=‖f‖ :=
  Lp.norm_compMeasurePreserving _ _

lemma translateL2_zero (f : WholeL2) : translateL2 0 f=f := by
  apply Lp.ext
  filter_upwards [translateL2_ae 0 f] with x hx
  simpa using hx

lemma continuous_translateL2 (f : WholeL2) : Continuous (fun y => translateL2 y f) := by
  let T : C(R3,C(R3,R3)) := (⟨fun z : R3×R3 => z.2-z.1,continuous_snd.sub continuous_fst⟩ : C(R3×R3,R3)).curry
  exact continuous_const.compMeasurePreservingLp T.continuous
    (fun y => measurePreserving_sub_right volume y) (by norm_num)

lemma wholeL2_norm_sq (f : WholeL2) : ‖f‖^2=∫ x, f x^2 := by
  rw [←real_inner_self_eq_norm_sq,L2.inner_def]
  simp only [real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs]

lemma translate_difference_sq (f : WholeL2) (y : R3) :
    (∫ x, (f (x-y)-f x)^2)=‖translateL2 y f-f‖^2 := by
  rw [wholeL2_norm_sq]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (translateL2 y f) f,translateL2_ae y f] with x hx hy
  simp only [hx,Pi.sub_apply,hy]

lemma whole_translation_memLp {μ : Measure R3} [IsProbabilityMeasure μ] (f : WholeL2) :
    MemLp (fun z : R3×R3 => f (z.2-z.1)) 2 (μ.prod volume) := by
  have hm : StronglyMeasurable (fun z : R3×R3 => f (z.2-z.1)) :=
    (Lp.stronglyMeasurable f).comp_measurable (measurable_snd.sub measurable_fst)
  apply (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr
  apply (integrable_prod_iff (hm.pow 2).aestronglyMeasurable).mpr
  constructor
  · exact ae_of_all _ (fun y => ((Lp.memLp f).comp_measurePreserving (measurePreserving_sub_right volume y)).integrable_sq)
  · have he (y : R3) : (∫ x, ‖f (x-y)^2‖)=‖f‖^2 := by
      rw [←translateL2_norm y f,wholeL2_norm_sq]
      apply integral_congr_ae
      filter_upwards [translateL2_ae y f] with x hx
      simp [hx]
    change Integrable (fun y => ∫ x, ‖f (x-y)^2‖) μ
    simp_rw [he]
    exact integrable_const _

lemma whole_difference_memLp {μ : Measure R3} [IsProbabilityMeasure μ] (f : WholeL2) :
    MemLp (fun z : R3×R3 => f (z.2-z.1)-f z.2) 2 (μ.prod volume) := by
  have hm : StronglyMeasurable (fun z : R3×R3 => f z.2) :=
    (Lp.stronglyMeasurable f).comp_measurable measurable_snd
  have hf : MemLp (fun z : R3×R3 => f z.2) 2 (μ.prod volume) := by
    apply (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr
    apply (integrable_prod_iff (hm.pow 2).aestronglyMeasurable).mpr
    constructor
    · exact ae_of_all _ (fun _ => (Lp.memLp f).integrable_sq)
    · change Integrable (fun _ : R3 => ∫ y, ‖f y^2‖) μ
      exact integrable_const _
  exact (whole_translation_memLp f).sub hf

theorem translation_average_sq_le {μ : Measure R3} [IsProbabilityMeasure μ]
    (f : WholeL2) {ε : ℝ}
    (hε : ∀ᵐ y ∂μ, ‖translateL2 y f-f‖^2≤ε) :
    MemLp (fun x => ∫ y, (f (x-y)-f x) ∂μ) 2 volume ∧
    (∫ x, (∫ y, (f (x-y)-f x) ∂μ)^2) ≤ ε := by
  obtain ⟨hm,hbound⟩ := memLp_probability_average (whole_difference_memLp (μ := μ) f)
  refine ⟨hm,hbound.trans ?_⟩
  rw [integral_prod _ (whole_difference_memLp (μ := μ) f).integrable_sq]
  have hi := (whole_difference_memLp (μ := μ) f).integrable_sq.integral_prod_left
  calc
    _ ≤ ∫ _ : R3, ε ∂μ := by
      apply integral_mono_ae hi (integrable_const _)
      filter_upwards [hε] with y hy
      exact (translate_difference_sq f y).le.trans hy
    _ = ε := by simp

lemma small_translation_radius (f : WholeL2) {ε : ℝ} (hε : 0<ε) :
    ∃ δ : ℝ, 0<δ ∧ ∀ y : R3, ‖y‖<δ → ‖translateL2 y f-f‖^2<ε := by
  have hc : Continuous (fun y => ‖translateL2 y f-f‖^2) :=
    ((continuous_translateL2 f).sub continuous_const).norm.pow 2
  have he : (fun y => ‖translateL2 y f-f‖^2) 0=0 := by simp [translateL2_zero]
  have hn : ∀ᶠ y in 𝓝 (0:R3), ‖translateL2 y f-f‖^2<ε :=
    hc.continuousAt.eventually (gt_mem_nhds (by simpa [he] using hε))
  obtain ⟨δ,hδ,hd⟩ := Metric.eventually_nhds_iff.mp hn
  exact ⟨δ,hδ,fun y hy => hd (by simpa [dist_zero_right] using hy)⟩

open Set MeasureTheory Filter Topology
open scoped Convolution

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

section
open Set MeasureTheory Filter Topology
open scoped Convolution

abbrev SpatialBump := ContDiffBump (0:R3)

def bumpProbability (φ : SpatialBump) : Measure R3 :=
  volume.withDensity (fun x => ENNReal.ofReal (φ.normed volume x))

instance bumpProbability_isProbability (φ : SpatialBump) : IsProbabilityMeasure (bumpProbability φ) where
  measure_univ := by
    rw [bumpProbability,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
      ←ofReal_integral_eq_lintegral_ofReal φ.integrable_normed (ae_of_all _ φ.nonneg_normed),φ.integral_normed]
    simp

lemma bumpProbability_integral (φ : SpatialBump) (f : R3 → ℝ) :
    (∫ y, f y ∂bumpProbability φ)=∫ y, φ.normed volume y*f y := by
  rw [bumpProbability,integral_withDensity_eq_integral_toReal_smul
    φ.continuous_normed.measurable.ennreal_ofReal (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (φ.nonneg_normed _),smul_eq_mul]

lemma bumpProbability_ball (φ : SpatialBump) :
    ∀ᵐ y ∂bumpProbability φ, ‖y‖<φ.rOut := by
  rw [bumpProbability,ae_withDensity_iff φ.continuous_normed.measurable.ennreal_ofReal]
  filter_upwards with y hy
  have hne : φ.normed volume y≠0 := fun h => hy (by rw [h]; simp)
  have hs : y∈Function.support (φ.normed volume) := hne
  rw [φ.support_normed_eq] at hs
  simpa using hs

def mollifyReal (φ : SpatialBump) (f : R3 → ℝ) : R3 → ℝ :=
  (φ.normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ,volume] f

lemma mollifyReal_smooth (φ : SpatialBump) {f : R3 → ℝ} (hf : LocallyIntegrable f) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (mollifyReal φ f) :=
  φ.hasCompactSupport_normed.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    φ.contDiff_normed hf

lemma mollifyReal_eq_average (φ : SpatialBump) (f : R3 → ℝ) (x : R3) :
    mollifyReal φ f x=∫ y, f (x-y) ∂bumpProbability φ := by
  rw [bumpProbability_integral]
  rfl

lemma mollifyReal_sub (φ : SpatialBump) (f : WholeL2) (x : R3) :
    mollifyReal φ f x-f x=∫ y, (f (x-y)-f x) ∂bumpProbability φ := by
  rw [bumpProbability_integral]
  simp_rw [mul_sub]
  have hi : Integrable (fun y => φ.normed volume y*f (x-y)) :=
    φ.hasCompactSupport_normed.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ)
      φ.continuous_normed ((Lp.memLp f).locallyIntegrable (by norm_num)) x
  rw [integral_sub hi (φ.integrable_normed.mul_const _),integral_mul_const,φ.integral_normed,one_mul]
  rfl

lemma mollifyReal_memLp (φ : SpatialBump) (f : WholeL2) : MemLp (mollifyReal φ f) 2 volume := by
  obtain ⟨hm,_⟩ := memLp_probability_average (whole_translation_memLp (μ := bumpProbability φ) f)
  exact MemLp.ae_eq (ae_of_all _ (fun x => (mollifyReal_eq_average φ f x).symm)) hm

theorem mollifyReal_approx (f : WholeL2) {ε : ℝ} (hε : 0<ε) :
    ∃ δ : ℝ, 0<δ ∧ ∀ φ : SpatialBump, φ.rOut≤δ →
      (∫ x, (mollifyReal φ f x-f x)^2) ≤ ε := by
  obtain ⟨δ,hδ,hd⟩ := small_translation_radius f hε
  refine ⟨δ,hδ,fun φ hφ => ?_⟩
  obtain ⟨_,he⟩ := translation_average_sq_le (μ := bumpProbability φ) f
    (show ∀ᵐ y ∂bumpProbability φ, ‖translateL2 y f-f‖^2≤ε from by
      filter_upwards [bumpProbability_ball φ] with y hy
      exact (hd y (hy.trans_le hφ)).le)
  simpa only [mollifyReal_sub] using he

def WeakL2Direction (f g : R3 → ℝ) (v : R3) : Prop :=
  ∀ ψ : R3 → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
    (∫ x, f x*fderiv ℝ ψ x v) = -(∫ x, g x*ψ x)

lemma mollifyReal_fderiv_eq {f : R3 → ℝ} (hf : LocallyIntegrable f)
    (φ : SpatialBump) (x v : R3) :
    fderiv ℝ (mollifyReal φ f) x v=
      ∫ y, fderiv ℝ (φ.normed volume) (x-y) v*f y := by
  let L : (R3 →L[ℝ] ℝ) →L[ℝ] ℝ →L[ℝ] (R3 →L[ℝ] ℝ) := ContinuousLinearMap.precompL R3 (ContinuousLinearMap.lsmul ℝ ℝ)
  have hc : HasCompactSupport (fderiv ℝ (φ.normed volume)) :=
    φ.hasCompactSupport_normed.fderiv ℝ
  have hκ : ContDiff ℝ (↑(⊤ : ℕ∞)) (φ.normed volume) := φ.contDiff_normed
  have hd : Continuous (fderiv ℝ (φ.normed volume)) :=
    hκ.continuous_fderiv (by simp)
  have hi : Integrable (fun y => L (fderiv ℝ (φ.normed volume) (x-y)) (f y)) :=
    (hc.convolutionExists_left L hd hf x).integrable_swap
  have hder := φ.hasCompactSupport_normed.hasFDerivAt_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) (hκ.of_le (by simp)) hf x
  change fderiv ℝ ((φ.normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ,volume] f) x v=_
  rw [hder.fderiv,convolution_eq_swap,ContinuousLinearMap.integral_apply hi]
  rfl

lemma mollifyReal_direction {f g : R3 → ℝ} (hf : MemLp f 2 volume)
    (_ : MemLp g 2 volume) (v : R3) (hw : WeakL2Direction f g v)
    (φ : SpatialBump) (x : R3) :
    fderiv ℝ (mollifyReal φ f) x v=mollifyReal φ g x := by
  let κ := φ.normed volume
  have hκ : ContDiff ℝ (↑(⊤ : ℕ∞)) κ := φ.contDiff_normed
  have hκc : HasCompactSupport κ := φ.hasCompactSupport_normed
  have hψ : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun y : R3 => κ (x-y)) :=
    hκ.comp (contDiff_const.sub contDiff_id)
  have hψc : HasCompactSupport (fun y : R3 => κ (x-y)) :=
    hκc.comp_homeomorph (Homeomorph.subLeft x)
  have hdψ (y : R3) : fderiv ℝ (fun z : R3 => κ (x-z)) y v=
      -(fderiv ℝ κ (x-y) v) := by
    have hh := ((hκ.differentiable (by simp)) (x-y)).hasFDerivAt.comp y
      ((hasFDerivAt_const x y).sub (hasFDerivAt_id y))
    change fderiv ℝ (κ ∘ (fun z : R3 => x-z)) y v=_
    rw [hh.fderiv]
    simp
  have he := hw _ hψ hψc
  simp_rw [hdψ,mul_neg,integral_neg] at he
  have he' : (∫ y, fderiv ℝ κ (x-y) v*f y)=∫ y, g y*κ (x-y) := by
    simpa only [mul_comm,neg_inj] using he
  rw [mollifyReal_fderiv_eq (hf.locallyIntegrable (by norm_num)),he']
  unfold mollifyReal
  rw [convolution_eq_swap]
  congr 1
  ext y
  simp [κ,mul_comm]

lemma mollifyReal_zero_outside {f : R3 → ℝ} {R : ℝ}
    (hf : ∀ᵐ y, R<‖y‖ → f y=0) (φ : SpatialBump) {x : R3}
    (hx : R+φ.rOut<‖x‖) : mollifyReal φ f x=0 := by
  unfold mollifyReal
  rw [convolution_eq_swap]
  apply integral_eq_zero_of_ae
  filter_upwards [hf] with y hy
  change φ.normed volume (x-y)*f y=0
  by_cases hf' : f y=0
  · rw [hf',mul_zero]
  · have hR : ‖y‖≤R := le_of_not_gt (fun h => hf' (hy h))
    have hn : φ.rOut<‖x-y‖ := by
      have ht : ‖x‖≤‖x-y‖+‖y‖ := by simpa using norm_add_le (x-y) y
      linarith
    have hκ : φ.normed volume (x-y)=0 := by
      apply Function.notMem_support.mp
      rw [φ.support_normed_eq,Metric.mem_ball,dist_zero_right]
      exact not_lt.mpr hn.le
    rw [hκ,zero_mul]

lemma mollifyReal_support {f : R3 → ℝ} {R : ℝ}
    (hf : ∀ᵐ y, R<‖y‖ → f y=0) (φ : SpatialBump) :
    tsupport (mollifyReal φ f)⊆Metric.closedBall 0 (R+φ.rOut) := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  rw [Metric.mem_closedBall,dist_zero_right]
  exact le_of_not_gt (fun hn => hx (mollifyReal_zero_outside hf φ hn))

lemma mollifyReal_compact {f : R3 → ℝ} {R : ℝ}
    (hf : ∀ᵐ y, R<‖y‖ → f y=0) (φ : SpatialBump) :
    HasCompactSupport (mollifyReal φ f) :=
  (isCompact_closedBall (0:R3) (R+φ.rOut)).of_isClosed_subset (isClosed_tsupport _)
    (mollifyReal_support hf φ)

end

open Set MeasureTheory Filter Topology

def dyadicBump (n : ℕ) : SpatialBump where
  rIn := (1/2:ℝ)^(n+1)
  rOut := (1/2:ℝ)^n
  rIn_pos := by positivity
  rIn_lt_rOut := by
    rw [pow_succ]
    have h : 0<(1/2:ℝ)^n := by positivity
    linarith

lemma dyadicBump_radius : Tendsto (fun n => (dyadicBump n).rOut) atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

def mollifyL2 (φ : SpatialBump) (f : WholeL2) : WholeL2 :=
  (mollifyReal_memLp φ f).toLp _

lemma mollifyL2_ae (φ : SpatialBump) (f : WholeL2) :
    (mollifyL2 φ f : R3 → ℝ) =ᵐ[volume] mollifyReal φ f :=
  (mollifyReal_memLp φ f).coeFn_toLp

lemma mollifyL2_norm_sq (φ : SpatialBump) (f : WholeL2) :
    ‖mollifyL2 φ f-f‖^2=∫ x, (mollifyReal φ f x-f x)^2 := by
  rw [wholeL2_norm_sq]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (mollifyL2 φ f) f,mollifyL2_ae φ f] with x hx hy
  simp only [hx,Pi.sub_apply,hy]

lemma mollifyL2_tendsto (f : WholeL2) :
    Tendsto (fun n => mollifyL2 (dyadicBump n) f) atTop (𝓝 f) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨δ,hδ,hd⟩ := mollifyReal_approx f (show 0<ε^2/2 by positivity)
  have he : ∀ᶠ n in atTop, (dyadicBump n).rOut<δ :=
    dyadicBump_radius.eventually (gt_mem_nhds hδ)
  obtain ⟨N,hN⟩ := eventually_atTop.mp he
  refine ⟨N,fun n hn => ?_⟩
  have hh : ‖mollifyL2 (dyadicBump n) f-f‖^2≤ε^2/2 := by
    rw [mollifyL2_norm_sq]
    exact hd _ (hN n hn).le
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (mollifyL2 (dyadicBump n) f-f)]

abbrev WholeJetSpace := Lp JetFiber 2 (volume : Measure R3)

def jetCoordinateL (i : Fin 4) : ℝ →L[ℝ] JetFiber :=
  (ContinuousLinearMap.id ℝ ℝ).smulRight (EuclideanSpace.single i 1)

lemma jetCoordinateL_apply (i : Fin 4) (r : ℝ) (j : Fin 4) :
    jetCoordinateL i r j=if j=i then r else 0 := by
  simp [jetCoordinateL,eq_comm]

def wholeJet (F : Fin 4 → WholeL2) : WholeJetSpace :=
  ∑ i, (jetCoordinateL i).compLpL 2 volume (F i)

lemma wholeJet_ae (F : Fin 4 → WholeL2) :
    ∀ᵐ x, ∀ i, wholeJet F x i=F i x := by
  have hc : ∀ᵐ x, ∀ i, ((jetCoordinateL i).compLpL 2 volume (F i)) x=jetCoordinateL i (F i x) :=
    ae_all_iff.mpr (fun i => (jetCoordinateL i).coeFn_compLp (F i))
  filter_upwards [hc,Lp.coeFn_finsetSum Finset.univ
    (fun i => (jetCoordinateL i).compLpL 2 volume (F i))] with x hx hy
  intro j
  change (∑ i, (jetCoordinateL i).compLpL 2 volume (F i)) x j=F j x
  rw [hy]
  simp only [Finset.sum_apply,hx]
  change (∑ i, jetCoordinateL i (F i x) j)=F j x
  simp only [jetCoordinateL_apply]
  simp

lemma wholeJet_continuous : Continuous wholeJet := by
  unfold wholeJet
  apply continuous_finsetSum
  intro i _
  exact ((jetCoordinateL i).compLpL 2 volume).continuous.comp (continuous_apply i)

def ballJet (F : Fin 4 → WholeL2) : JetSpace :=
  LpToLpRestrictCLM R3 JetFiber ℝ volume 2 ball (wholeJet F)

lemma ballJet_ae (F : Fin 4 → WholeL2) :
    ∀ᵐ x ∂ballMeasure, ∀ i, ballJet F x i=F i x := by
  filter_upwards [LpToLpRestrictCLM_coeFn ℝ ball (wholeJet F),
    (wholeJet_ae F).filter_mono (ae_mono Measure.restrict_le_self)] with x hx hy
  intro i
  exact congrArg (fun z : JetFiber => z i) hx |>.trans (hy i)

lemma ballJet_continuous : Continuous ballJet :=
  (LpToLpRestrictCLM R3 JetFiber ℝ volume 2 ball).continuous.comp wholeJet_continuous

lemma ballJet_mollify_tendsto (F : Fin 4 → WholeL2) :
    Tendsto (fun n => ballJet (fun i => mollifyL2 (dyadicBump n) (F i))) atTop (𝓝 (ballJet F)) :=
  ballJet_continuous.continuousAt.tendsto.comp
    (tendsto_pi_nhds.mpr (fun i => mollifyL2_tendsto (F i)))

lemma zeroTraceAmbient_le_H1Space : zeroTraceAmbient≤H1Space := by
  apply Submodule.topologicalClosure_mono
  apply Submodule.span_mono
  rintro z ⟨f,hf,hc,hs,hm,hz⟩
  exact ⟨f,hf,hm,hz⟩

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_WholeWeakClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology
open scoped RealInnerProductSpace

lemma wholeL2_pair_integral (f : WholeL2) {g : R3 → ℝ} (hg : MemLp g 2 volume) :
    inner ℝ f (hg.toLp g)=∫ x,f x*g x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hg.coeFn_toLp] with x hx
  simp [hx,mul_comm]

lemma wholeL2_pair_tendsto {f : ℕ → WholeL2} {f₀ : WholeL2}
    (hf : Tendsto f atTop (𝓝 f₀)) {g : R3 → ℝ} (hg : MemLp g 2 volume) :
    Tendsto (fun n => ∫ x,f n x*g x) atTop (𝓝 (∫ x,f₀ x*g x)) := by
  simpa only [wholeL2_pair_integral _ hg] using
    (hf.inner (tendsto_const_nhds (x:=hg.toLp g)) :
      Tendsto (fun n => inner ℝ (f n) (hg.toLp g)) atTop (𝓝 (inner ℝ f₀ (hg.toLp g))))

lemma WeakL2Direction.closed {f g : ℕ → WholeL2} {f₀ g₀ : WholeL2} {v : R3}
    (hf : Tendsto f atTop (𝓝 f₀)) (hg : Tendsto g atTop (𝓝 g₀))
    (hw : ∀ n,WeakL2Direction (f n) (g n) v) :
    WeakL2Direction f₀ g₀ v := by
  intro ψ hψ hc
  have hm : MemLp ψ 2 volume := hψ.continuous.memLp_of_hasCompactSupport hc
  have hd : MemLp (fun x => fderiv ℝ ψ x v) 2 volume :=
    ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hc.fderiv_apply ℝ v)
  have hleft := wholeL2_pair_tendsto hf hd
  have hright := (wholeL2_pair_tendsto hg hm).neg
  exact tendsto_nhds_unique hleft (hright.congr' (Eventually.of_forall (fun n => (hw n ψ hψ hc).symm)))

lemma wholeL2_tendsto_of_sq {f : ℕ → WholeL2} {f₀ : WholeL2}
    (hf : Tendsto (fun n => ∫ x,(f n x-f₀ x)^2) atTop (𝓝 0)) :
    Tendsto f atTop (𝓝 f₀) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have he (n : ℕ) : ‖f n-f₀‖^2=∫ x,(f n x-f₀ x)^2 := by
    rw [wholeL2_norm_sq]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (f n) f₀] with x hx
    rw [hx]
    rfl
  have hsq : Tendsto (fun n => ‖f n-f₀‖^2) atTop (𝓝 0) := by
    simpa only [he] using hf
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using hh

lemma memLp_toLp_tendsto_of_sq {f : ℕ → R3 → ℝ} {f₀ : R3 → ℝ}
    (hm : ∀ n,MemLp (f n) 2 volume) (hm₀ : MemLp f₀ 2 volume)
    (hf : Tendsto (fun n => ∫ x,(f n x-f₀ x)^2) atTop (𝓝 0)) :
    Tendsto (fun n => (hm n).toLp (f n)) atTop (𝓝 (hm₀.toLp f₀)) := by
  apply wholeL2_tendsto_of_sq
  convert hf using 1
  all_goals try with_reducible_and_instances rfl
  ext n
  apply integral_congr_ae
  filter_upwards [(hm n).coeFn_toLp,hm₀.coeFn_toLp] with x hx hy
  rw [hx,hy]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_CompactLipschitzH1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory Filter Topology
open scoped NNReal

lemma lipschitz_weakDirection {C : ℝ≥0} {f : R3 → ℝ}
    (hf : LipschitzWith C f) (v : R3) :
    WeakL2Direction f (fun x => lineDeriv ℝ f x v) v := by
  intro ψ hψ hc
  obtain ⟨D,hD⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc hψ (by simp)
  have he := hf.integral_lineDeriv_mul_eq (μ := volume) hD hc v
  have hd (x : R3) : lineDeriv ℝ ψ x (-v)= -(fderiv ℝ ψ x v) := by
    rw [(hψ.differentiable (by simp)).differentiableAt.lineDeriv_eq_fderiv,map_neg]
  simp_rw [hd,neg_mul,integral_neg,mul_comm (fderiv ℝ ψ _ v)] at he
  linarith

lemma WeakL2Direction.congr {f g f' g' : R3 → ℝ} {v : R3}
    (hw : WeakL2Direction f g v) (hf : f'=ᵐ[volume] f) (hg : g'=ᵐ[volume] g) :
    WeakL2Direction f' g' v := by
  intro ψ hψ hc
  calc
    _ = ∫ x, f x*fderiv ℝ ψ x v := integral_congr_ae (by
      filter_upwards [hf] with x hx; rw [hx])
    _ = -(∫ x, g x*ψ x) := hw ψ hψ hc
    _ = _ := congrArg Neg.neg (integral_congr_ae (by
      filter_upwards [hg] with x hx; rw [hx]))

lemma lineDeriv_zero_outside {f : R3 → ℝ} {R : ℝ}
    (hs : ∀ x, R<‖x‖ → f x=0) {x : R3} (hx : R<‖x‖) (v : R3) :
    lineDeriv ℝ f x v=0 := by
  have he : f=ᶠ[𝓝 x] (fun _ => 0) := by
    filter_upwards [isOpen_lt continuous_const continuous_norm |>.mem_nhds hx] with y hy
    exact hs y hy
  rw [he.lineDeriv_eq]
  rw [(differentiableAt_const (0:ℝ)).lineDeriv_eq_fderiv]
  simp

lemma bounded_support_compact {f : R3 → ℝ} {R : ℝ}
    (hs : ∀ x, R<‖x‖ → f x=0) : HasCompactSupport f := by
  apply (isCompact_closedBall (0:R3) R).of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  simp only [Metric.mem_closedBall,dist_zero_right]
  exact le_of_not_gt (fun hn => hx (hs x hn))

lemma lipschitz_lineDeriv_memLp {C : ℝ≥0} {f : R3 → ℝ}
    (hf : LipschitzWith C f) {R : ℝ} (hs : ∀ x, R<‖x‖ → f x=0) (v : R3) :
    MemLp (fun x => lineDeriv ℝ f x v) 2 volume := by
  apply (hf.memLp_lineDeriv v).mono_exponent_of_measure_support_ne_top
    (s := Metric.closedBall 0 R) _ (measure_closedBall_lt_top.ne) le_top
  intro x hx
  apply lineDeriv_zero_outside hs _ v
  simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hx

lemma segment_meets_frontier {s : Set R3} {x y : R3} (hx : x∈s) (hy : y∉s) :
    ∃ z∈segment ℝ x y,z∈frontier s := by
  have hc : segment ℝ x y⊆closure s∪closure sᶜ := by
    intro z _
    by_cases hz : z∈s
    · exact Or.inl (subset_closure hz)
    · exact Or.inr (subset_closure hz)
  obtain ⟨z,hz,hb⟩ := isPreconnected_closed_iff.mp (convex_segment x y).isPreconnected
    (closure s) (closure sᶜ) isClosed_closure isClosed_closure hc
    ⟨x,left_mem_segment ℝ x y,subset_closure hx⟩
    ⟨y,right_mem_segment ℝ x y,subset_closure hy⟩
  exact ⟨z,hz,by rwa [frontier_eq_closure_inter_closure]⟩

lemma lipschitz_piecewise_frontier (s : Set R3) [DecidablePred (·∈s)]
    {f g : R3 → ℝ} {K L : ℝ≥0}
    (hf : LipschitzOnWith K f (closure s))
    (hg : LipschitzOnWith L g (closure sᶜ))
    (he : EqOn f g (frontier s)) :
    LipschitzWith (max K L) (s.piecewise f g) := by
  have hcross {x y : R3} (hx : x∈s) (hy : y∉s) :
      dist (f x) (g y) ≤ (max K L:ℝ≥0)*dist x y := by
    obtain ⟨z,hz,hb⟩ := segment_meets_frontier hx hy
    have hb' := frontier_eq_closure_inter_closure (s := s) ▸ hb
    calc
      dist (f x) (g y) ≤ dist (f x) (f z)+dist (f z) (g y) := dist_triangle _ _ _
      _ = dist (f x) (f z)+dist (g z) (g y) := by rw [he hb]
      _ ≤ K*dist x z+L*dist z y := add_le_add
        (hf.dist_le_mul x (subset_closure hx) z hb'.1)
        (hg.dist_le_mul z hb'.2 y (subset_closure hy))
      _ ≤ (max K L:ℝ≥0)*dist x z+(max K L:ℝ≥0)*dist z y := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_right (by exact_mod_cast le_max_left K L) dist_nonneg
        · exact mul_le_mul_of_nonneg_right (by exact_mod_cast le_max_right K L) dist_nonneg
      _ = (max K L:ℝ≥0)*dist x y := by rw [←mul_add,dist_add_dist_of_mem_segment hz]
  apply LipschitzWith.of_dist_le_mul
  intro x y
  by_cases hx : x∈s <;> by_cases hy : y∈s
  · simp only [piecewise_eq_of_mem s f g hx,piecewise_eq_of_mem s f g hy]
    exact (hf.dist_le_mul x (subset_closure hx) y (subset_closure hy)).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast le_max_left K L) dist_nonneg)
  · simpa only [piecewise_eq_of_mem s f g hx,piecewise_eq_of_notMem s f g hy] using hcross hx hy
  · rw [dist_comm,dist_comm x y]
    simpa only [piecewise_eq_of_mem s f g hy,piecewise_eq_of_notMem s f g hx] using hcross hy hx
  · simp only [piecewise_eq_of_notMem s f g hx,piecewise_eq_of_notMem s f g hy]
    exact (hg.dist_le_mul x (subset_closure hx) y (subset_closure hy)).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast le_max_right K L) dist_nonneg)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Walls_SeamCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology
open scoped NNReal

lemma LocalLipAt.mul {E : Type*} [PseudoMetricSpace E]
    {f g : E → ℝ} {x : E} (hf : LocalLipAt f x) (hg : LocalLipAt g x) :
    LocalLipAt (fun y => f y*g y) x := by
  exact (localLipAt_of_contDiffAt
    (show ContDiffAt ℝ 1 (fun p : ℝ×ℝ => p.1*p.2) (f x,g x) by fun_prop)).comp
    (f:=fun y => (f y,g y)) (x:=x) (hf.prodMk hg)

lemma compact_locallyLipschitz {f : R3 → ℝ}
    (hf : ∀ x,LocalLipAt f x) (hc : HasCompactSupport f) :
    ∃ K,LipschitzWith K f := by
  classical
  obtain ⟨R,hR,hzero⟩ := hc.exists_pos_le_norm
  have hlocal : LocallyLipschitz f := hf
  obtain ⟨K,hK⟩ := hlocal.locallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (isCompact_closedBall (0:R3) R)
  let S : Set R3 := Metric.closedBall 0 R
  have hclosure : closure S=S := Metric.isClosed_closedBall.closure_eq
  have hmatch : EqOn f (fun _ => (0:ℝ)) (frontier S) := by
    intro x hx
    have hs := Metric.frontier_closedBall_subset_sphere hx
    have hn : ‖x‖=R := by simpa only [Metric.mem_sphere,dist_zero_right] using hs
    exact hzero x hn.ge
  have hlip := lipschitz_piecewise_frontier S
    (show LipschitzOnWith K f (closure S) by rw [hclosure]; exact hK)
    (LipschitzWith.const (0:ℝ)).lipschitzOnWith hmatch
  have he : S.piecewise f (fun _ => 0)=f := by
    funext x
    by_cases hx : x∈S
    · simp only [piecewise_eq_of_mem S _ _ hx]
    · rw [piecewise_eq_of_notMem S _ _ hx]
      have hn : R<‖x‖ := by simpa only [S,Metric.mem_closedBall,dist_zero_right,not_le] using hx
      exact (hzero x hn.le).symm
  rw [he] at hlip
  exact ⟨max K 0,hlip⟩

lemma smoothTransition_lipschitz : ∃ K,LipschitzWith K Real.smoothTransition := by
  obtain ⟨K,hK⟩ := (Real.smoothTransition.contDiff (n:=1)).contDiffOn.exists_lipschitzOnWith
    (by simp) (convex_Icc (0:ℝ) 1) isCompact_Icc
  have hp := hK.comp (LipschitzWith.projIcc (show (0:ℝ)≤1 by norm_num)).lipschitzOnWith
    (s:=univ) (fun x _ => (projIcc (0:ℝ) 1 (by norm_num) x).property)
  refine ⟨K,?_⟩
  simpa only [Function.comp_def,Real.smoothTransition.projIcc,mul_one] using (lipschitzOnWith_univ.mp hp)

def seamCutoff (n : ℕ) (t : ℝ) : ℝ :=
  Real.smoothTransition (((n:ℝ)+1)*t-1)

lemma seamCutoff_smooth (n : ℕ) : ContDiff ℝ (↑(⊤ : ℕ∞)) (seamCutoff n) := by
  unfold seamCutoff
  exact (Real.smoothTransition.contDiff (n:=⊤)).comp (by fun_prop)

lemma seamCutoff_bounds (n : ℕ) (t : ℝ) : 0 ≤ seamCutoff n t ∧ seamCutoff n t≤1 :=
  ⟨Real.smoothTransition.nonneg _,Real.smoothTransition.le_one _⟩

lemma seamCutoff_zero (n : ℕ) {t : ℝ} (ht : ((n:ℝ)+1)*t≤1) : seamCutoff n t=0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

lemma seamCutoff_one (n : ℕ) {t : ℝ} (ht : 2≤((n:ℝ)+1)*t) : seamCutoff n t=1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

lemma seamCutoff_eventually_one {t : ℝ} (ht : 0<t) : ∀ᶠ n in atTop,seamCutoff n t=1 := by
  obtain ⟨N,hN⟩ := exists_nat_gt (2/t)
  filter_upwards [eventually_ge_atTop N] with n hn
  apply seamCutoff_one
  have hle : (N:ℝ)≤n := by exact_mod_cast hn
  have hmul := (div_lt_iff₀ ht).mp hN
  nlinarith

lemma seamCutoff_deriv (n : ℕ) (t : ℝ) :
    deriv (seamCutoff n) t=deriv Real.smoothTransition (((n:ℝ)+1)*t-1)*((n:ℝ)+1) := by
  have hs := ((Real.smoothTransition.contDiff (n:=1)).differentiable (by simp)).differentiableAt (x:=((n:ℝ)+1)*t-1) |>.hasDerivAt
  have ha : HasDerivAt (fun t : ℝ => ((n:ℝ)+1)*t-1) ((n:ℝ)+1) t := by
    convert! ((hasDerivAt_id t).const_mul ((n:ℝ)+1)).sub_const 1 using 1
    all_goals try with_reducible_and_instances rfl
    simp
  exact (hs.comp t ha).deriv

lemma seamCutoff_deriv_bound : ∃ D : ℝ,0≤D ∧ ∀ n t,
    |deriv (seamCutoff n) t|≤D*((n:ℝ)+1) := by
  obtain ⟨D,hD⟩ := smoothTransition_lipschitz
  refine ⟨D,D.coe_nonneg,?_⟩
  intro n t
  rw [seamCutoff_deriv,abs_mul,abs_of_nonneg (by positivity : 0≤(n:ℝ)+1)]
  exact mul_le_mul_of_nonneg_right (norm_deriv_le_of_lipschitz hD) (by positivity)

lemma seamCutoff_deriv_zero (n : ℕ) {t : ℝ} (ht : 2<((n:ℝ)+1)*t) :
    deriv (seamCutoff n) t=0 := by
  have he : seamCutoff n=ᶠ[𝓝 t] (fun _ => 1) := by
    filter_upwards [isOpen_lt continuous_const (by fun_prop : Continuous (fun t : ℝ => ((n:ℝ)+1)*t)) |>.mem_nhds ht] with t ht
    exact seamCutoff_one n ht.le
  rw [he.deriv_eq,deriv_const]

lemma seamCutoff_mul_lipschitz {u τ : R3 → ℝ}
    (hτ : LocallyLipschitz τ) (hu : ∀ x,0<τ x → LocalLipAt u x)
    (hc : HasCompactSupport u) (n : ℕ) :
    ∃ K,LipschitzWith K (fun x => seamCutoff n (τ x)*u x) := by
  have hlocal (x : R3) : LocalLipAt (fun x => seamCutoff n (τ x)*u x) x := by
    by_cases ht : 0<τ x
    · exact ((localLipAt_of_contDiffAt ((seamCutoff_smooth n).of_le (by simp)).contDiffAt).comp
        (hτ x)).mul (hu x ht)
    · have hx : ((n:ℝ)+1)*τ x<1 := by nlinarith [le_of_not_gt ht,Nat.cast_nonneg (α:=ℝ) n]
      have he : (fun _ : R3 => (0:ℝ))=ᶠ[𝓝 x] (fun x => seamCutoff n (τ x)*u x) := by
        filter_upwards [isOpen_lt (continuous_const.mul hτ.continuous) continuous_const |>.mem_nhds hx] with y hy
        rw [seamCutoff_zero n hy.le,zero_mul]
      exact (localLipAt_of_contDiffAt contDiffAt_const).congr he
  exact compact_locallyLipschitz hlocal (hc.mul_left)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Walls_SeamL2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory Filter Topology
open scoped NNReal

lemma seamCutoff_sq_error_bound (n : ℕ) (t a : ℝ) :
    (seamCutoff n t*a-a)^2 ≤ a^2 := by
  have hb := seamCutoff_bounds n t
  have h₁ : |seamCutoff n t-1|≤1 := abs_le.mpr ⟨by linarith,by linarith⟩
  have h₂ : |seamCutoff n t*a-a|≤|a| := by
    calc
      _ = |seamCutoff n t-1| *|a| := by rw [←abs_mul]; congr 1; ring
      _ ≤ 1*|a| := mul_le_mul_of_nonneg_right h₁ (abs_nonneg a)
      _ = |a| := one_mul _
  exact (sq_le_sq).mpr h₂

lemma seamCutoff_L2_approx {τ u : R3 → ℝ} (hτ : Continuous τ)
    (hu : MemLp u 2 volume) (hz : ∀ᵐ x,τ x≤0 → u x=0) :
    Tendsto (fun n => ∫ x,(seamCutoff n (τ x)*u x-u x)^2) atTop (𝓝 0) := by
  have hc (n : ℕ) : AEStronglyMeasurable (fun x => seamCutoff n (τ x)*u x-u x) volume :=
    (((seamCutoff_smooth n).continuous.comp hτ).aestronglyMeasurable.mul hu.aestronglyMeasurable).sub hu.aestronglyMeasurable
  have ht := tendsto_integral_of_dominated_convergence (F:=fun n x => (seamCutoff n (τ x)*u x-u x)^2) (fun x => u x^2)
    (fun n => (hc n).pow 2) hu.integrable_sq
    (fun n => ae_of_all _ (fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact seamCutoff_sq_error_bound n (τ x) (u x)))
    (f:=fun _ => (0:ℝ)) (by
      filter_upwards [hz] with x hx
      by_cases hp : 0<τ x
      · exact tendsto_const_nhds.congr' (by
          filter_upwards [seamCutoff_eventually_one hp] with n hn
          simp [hn])
      · have he := hx (le_of_not_gt hp)
        simpa only [he,mul_zero,sub_self,zero_pow (by norm_num : 2≠0)] using
          (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0)))
  simpa only [integral_zero] using ht

lemma seamCutoff_mul_lineDeriv {τ u : R3 → ℝ} {K : ℝ≥0}
    (hτ : LipschitzWith K τ) (v : R3) {g : R3 → ℝ}
    (hd : ∀ᵐ x,0<τ x → HasLineDerivAt ℝ u (g x) x v)
    (hz : ∀ᵐ x,τ x≤0 → u x=0 ∧ g x=0) (n : ℕ) :
    (fun x => lineDeriv ℝ (fun y => seamCutoff n (τ y)*u y) x v)=ᵐ[volume]
      (fun x => seamCutoff n (τ x)*g x+
        deriv (seamCutoff n) (τ x)*lineDeriv ℝ τ x v*u x) := by
  filter_upwards [hτ.ae_lineDifferentiableAt (μ:=volume) v,hd,hz] with x hx hu hzero
  by_cases hp : 0<τ x
  · have hc : HasDerivAt (seamCutoff n) (deriv (seamCutoff n) (τ x)) (τ x) :=
      ((seamCutoff_smooth n).differentiable (by simp)).differentiableAt.hasDerivAt
    have hdu := hu hp
    have hdt := hx.hasLineDerivAt
    change HasDerivAt (fun t : ℝ => u (x+t•v)) (g x) 0 at hdu
    change HasDerivAt (fun t : ℝ => τ (x+t•v)) (lineDeriv ℝ τ x v) 0 at hdt
    have hcc : HasDerivAt (seamCutoff n) (deriv (seamCutoff n) (τ x)) (τ (x+(0:ℝ)•v)) := by simpa using hc
    have hc' := hcc.comp (0:ℝ) hdt
    have hh := hc'.mul hdu
    have hh' : HasLineDerivAt ℝ (fun y => seamCutoff n (τ y)*u y)
        (seamCutoff n (τ x)*g x+deriv (seamCutoff n) (τ x)*lineDeriv ℝ τ x v*u x) x v := by
      change HasDerivAt (fun t : ℝ => seamCutoff n (τ (x+t•v))*u (x+t•v)) _ 0
      simpa only [Pi.mul_def,Function.comp_def,zero_smul,add_zero,add_comm] using hh
    exact hh'.lineDeriv
  · have hn := le_of_not_gt hp
    have he : (fun y => seamCutoff n (τ y)*u y)=ᶠ[𝓝 x] (fun _ => 0) := by
      have hx' : ((n:ℝ)+1)*τ x<1 := by nlinarith [Nat.cast_nonneg (α:=ℝ) n]
      filter_upwards [isOpen_lt (continuous_const.mul hτ.continuous) continuous_const |>.mem_nhds hx'] with y hy
      rw [seamCutoff_zero n hy.le,zero_mul]
    rw [he.lineDeriv_eq,(differentiableAt_const (0:ℝ)).lineDeriv_eq_fderiv]
    simp [(hzero hn).1,(hzero hn).2]

def seamLayer (τ : R3 → ℝ) (n : ℕ) : Set R3 :=
  {x | 0<τ x ∧ ((n:ℝ)+1)*τ x≤2}

lemma measurableSet_seamLayer {τ : R3 → ℝ} (hτ : Continuous τ) (n : ℕ) :
    MeasurableSet (seamLayer τ n) :=
  (isOpen_lt continuous_const hτ).measurableSet.inter
    (isClosed_le (continuous_const.mul hτ) continuous_const).measurableSet

lemma seamCutoff_remainder_sq_bound {τ u : R3 → ℝ} {K : ℝ≥0}
    (hτ : LipschitzWith K τ) (v : R3) {D : ℝ} (hD : 0≤D)
    (hb : ∀ n t,|deriv (seamCutoff n) t|≤D*((n:ℝ)+1))
    (hz : ∀ᵐ x,τ x≤0 → u x=0) (n : ℕ) :
    ∀ᵐ x,(deriv (seamCutoff n) (τ x)*lineDeriv ℝ τ x v*u x)^2 ≤
      (D^2*((K:ℝ)*‖v‖)^2)*((n:ℝ)+1)^2*(seamLayer τ n).indicator (fun x => u x^2) x := by
  filter_upwards [hz] with x hx
  by_cases hs : x∈seamLayer τ n
  · rw [indicator_of_mem hs]
    have hd : |lineDeriv ℝ τ x v|≤(K:ℝ)*‖v‖ := norm_lineDeriv_le_of_lipschitz ℝ hτ
    have hp : |deriv (seamCutoff n) (τ x)*lineDeriv ℝ τ x v|≤
        D*((n:ℝ)+1)*((K:ℝ)*‖v‖) := by
      rw [abs_mul]
      exact mul_le_mul (hb n (τ x)) hd (abs_nonneg _) (mul_nonneg hD (by positivity))
    have hsqr : (deriv (seamCutoff n) (τ x)*lineDeriv ℝ τ x v)^2≤
        (D*((n:ℝ)+1)*((K:ℝ)*‖v‖))^2 := by
      apply (sq_le_sq).mpr
      have hn : 0≤D*((n:ℝ)+1)*((K:ℝ)*‖v‖) := by positivity
      simpa only [abs_of_nonneg hn] using hp
    calc
      _ = (deriv (seamCutoff n) (τ x)*lineDeriv ℝ τ x v)^2*u x^2 := mul_pow _ _ _
      _ ≤ (D*((n:ℝ)+1)*((K:ℝ)*‖v‖))^2*u x^2 := mul_le_mul_of_nonneg_right hsqr (sq_nonneg _)
      _ = _ := by ring
  · rw [indicator_of_notMem hs,mul_zero]
    by_cases hp : 0<τ x
    · have ht : 2<((n:ℝ)+1)*τ x := lt_of_not_ge (fun ht => hs ⟨hp,ht⟩)
      rw [seamCutoff_deriv_zero n ht,zero_mul,zero_mul]
      norm_num
    · rw [hx (le_of_not_gt hp),mul_zero]
      norm_num

lemma seamCutoff_gradient_L2_approx {τ u g : R3 → ℝ} {K : ℝ≥0}
    (hτ : LipschitzWith K τ) (v : R3) (hu : MemLp u 2 volume) (hg : MemLp g 2 volume)
    (hd : ∀ᵐ x,0<τ x → HasLineDerivAt ℝ u (g x) x v)
    (hz : ∀ᵐ x,τ x≤0 → u x=0 ∧ g x=0)
    (hm : ∀ n,MemLp (fun x => lineDeriv ℝ (fun y => seamCutoff n (τ y)*u y) x v) 2 volume)
    (hthin : Tendsto (fun n : ℕ => ((n:ℝ)+1)^2*∫ x in seamLayer τ n,u x^2) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x,(lineDeriv ℝ (fun y => seamCutoff n (τ y)*u y) x v-g x)^2)
      atTop (𝓝 0) := by
  obtain ⟨D,hD,hDb⟩ := seamCutoff_deriv_bound
  let C : ℝ := D^2*((K:ℝ)*‖v‖)^2
  have hC : 0≤C := by dsimp [C]; positivity
  have hz₁ : ∀ᵐ x,τ x≤0 → u x=0 := hz.mono (fun x hx ht => (hx ht).1)
  have hz₂ : ∀ᵐ x,τ x≤0 → g x=0 := hz.mono (fun x hx ht => (hx ht).2)
  have hlim := (seamCutoff_L2_approx hτ.continuous hg hz₂).const_mul 2 |>.add (hthin.const_mul (2*C))
  simp only [mul_zero,add_zero] at hlim
  apply squeeze_zero (fun n => integral_nonneg (fun x => sq_nonneg _)) _ hlim
  intro n
  have hcut : MemLp (fun x => seamCutoff n (τ x)*g x-g x) 2 volume := by
    apply hg.mono (((seamCutoff_smooth n).continuous.comp hτ.continuous).aestronglyMeasurable.mul hg.aestronglyMeasurable |>.sub hg.aestronglyMeasurable)
    filter_upwards with x
    exact (sq_le_sq).mp (seamCutoff_sq_error_bound n (τ x) (g x))
  have hi := (hcut.integrable_sq.const_mul 2).add
    ((hu.integrable_sq.indicator (measurableSet_seamLayer hτ.continuous n)).const_mul (2*C*((n:ℝ)+1)^2))
  have hle := integral_mono_ae ((hm n).sub hg).integrable_sq hi (by
    filter_upwards [seamCutoff_mul_lineDeriv hτ v hd hz n,
      seamCutoff_remainder_sq_bound hτ v hD hDb hz₁ n] with x hx hb
    simp only [Pi.sub_apply,Pi.add_apply]
    rw [hx]
    dsimp only [C] at hb ⊢
    nlinarith [sq_nonneg (seamCutoff n (τ x)*g x-g x-
      deriv (seamCutoff n) (τ x)*lineDeriv ℝ τ x v*u x)])
  simp only [Pi.sub_apply,Pi.add_apply] at hle
  rw [integral_add (hcut.integrable_sq.const_mul 2)
    ((hu.integrable_sq.indicator (measurableSet_seamLayer hτ.continuous n)).const_mul (2*C*((n:ℝ)+1)^2)),
    integral_const_mul,integral_const_mul,integral_indicator (measurableSet_seamLayer hτ.continuous n)] at hle
  simpa only [mul_assoc] using hle

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

def cutMatchedValue (τ χ p : (Fin 3 → ℝ) → ℝ) (x : Fin 3 → ℝ) : ℝ :=
  if 0<τ x then χ x*p x else 0

def cutMatchedGradient (τ χ p : (Fin 3 → ℝ) → ℝ)
    (F : (Fin 3 → ℝ) → (Fin 3 → ℝ) →L[ℝ] ℝ) (i : Fin 3) (x : Fin 3 → ℝ) : ℝ :=
  if 0<τ x then fderiv ℝ χ x (Pi.single i 1)*p x+χ x*F x (Pi.single i 1) else 0

lemma cutMatchedValue_memLp {τ χ p : (Fin 3 → ℝ) → ℝ} {D : Set (Fin 3 → ℝ)}
    (hτ : Continuous τ) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hD : MeasurableSet D) (hp : MemLp p 2 (volume.restrict D))
    (hs : ∀ x∈tsupport χ,0<τ x → x∈D) :
    MemLp (cutMatchedValue τ χ p) 2 volume := by
  have hm := (memLp_indicator_iff_restrict hD).mpr hp
  have hm' : MemLp (χ*(D.indicator p)) 2 volume :=
    hm.mul (hχ.memLp_top_of_hasCompactSupport hc volume)
  have hh := hm'.indicator (isOpen_lt (continuous_const (y:=(0:ℝ))) hτ).measurableSet
  apply MemLp.ae_eq _ hh
  filter_upwards [] with x
  by_cases ht : 0<τ x
  · by_cases hx : x∈D
    · simp [cutMatchedValue,ht,hx]
    · have hn : x∉tsupport χ := fun h => hx (hs x h ht)
      simp [cutMatchedValue,ht,hx,image_eq_zero_of_notMem_tsupport hn]
  · simp [cutMatchedValue,ht]

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

lemma LocalLipAt.sub {E : Type*} [PseudoMetricSpace E] {p q : E → ℝ} {x : E}
    (hp : LocalLipAt p x) (hq : LocalLipAt q x) : LocalLipAt (fun y => p y-q y) x := by
  obtain ⟨K,t,ht,hK⟩ := hp
  obtain ⟨L,u,hu,hL⟩ := hq
  exact ⟨K+L,t∩u,inter_mem ht hu,(hK.mono inter_subset_left).sub (hL.mono inter_subset_right)⟩

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_SmoothCollarTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal

local instance smoothCollarTraceCircleMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance smoothCollarTraceCircleIsProbabilityMeasure :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_LpExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity

open Set MeasureTheory Filter Topology

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
  {χ : X → ℝ} {C : ℝ} (hχ : AEStronglyMeasurable χ μ) (hb : ∀ᵐ x∂μ,‖χ x‖≤C)

include hχ hb in
lemma lpMultiplier_mem (f : Lp ℝ 2 μ) : MemLp (fun x => χ x*f x) 2 μ := by
  apply (Lp.memLp f).of_le_mul (c:=C) (hχ.mul (Lp.memLp f).aestronglyMeasurable)
  filter_upwards [hb] with x hx
  change ‖χ x*f x‖≤C*‖f x‖
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)

def lpMultiplierL : Lp ℝ 2 μ →ₗ[ℝ] Lp ℝ 2 μ where
  toFun f := (lpMultiplier_mem hχ hb f).toLp _
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(lpMultiplier_mem hχ hb (f+g)).coeFn_toLp,
      (lpMultiplier_mem hχ hb f).coeFn_toLp,(lpMultiplier_mem hχ hb g).coeFn_toLp,
      Lp.coeFn_add f g,Lp.coeFn_add ((lpMultiplier_mem hχ hb f).toLp _)
        ((lpMultiplier_mem hχ hb g).toLp _)] with x hfg hf hg hi he
    rw [hfg,he]
    simp only [Pi.add_apply,hf,hg,hi,mul_add]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [(lpMultiplier_mem hχ hb (c•f)).coeFn_toLp,
      (lpMultiplier_mem hχ hb f).coeFn_toLp,Lp.coeFn_smul c f,
      Lp.coeFn_smul c ((lpMultiplier_mem hχ hb f).toLp _)] with x hcf hf hi he
    change _=(c • _ : Lp ℝ 2 μ) x
    rw [hcf,he]
    simp only [Pi.smul_apply,smul_eq_mul,hf,hi]
    ring

def lpMultiplierCLM : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  (lpMultiplierL hχ hb).mkContinuous C (by
    intro f
    change ‖(lpMultiplier_mem hχ hb f).toLp _‖≤C*‖f‖
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [(lpMultiplier_mem hχ hb f).coeFn_toLp,hb] with x hx hb
    rw [hx,norm_mul]
    exact mul_le_mul_of_nonneg_right hb (norm_nonneg _))

lemma lpMultiplierCLM_ae (f : Lp ℝ 2 μ) :
    lpMultiplierCLM hχ hb f=ᵐ[μ] (fun x => χ x*f x) :=
  (lpMultiplier_mem hχ hb f).coeFn_toLp

def compactMultiplierCLM [TopologicalSpace X] [BorelSpace X]
    (hχ : Continuous χ) (hc : HasCompactSupport χ) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  lpMultiplierCLM hχ.aestronglyMeasurable
    (Eventually.of_forall (hc.exists_bound_of_continuous hχ).choose_spec)

lemma compactMultiplierCLM_ae [TopologicalSpace X] [BorelSpace X]
    (hχ : Continuous χ) (hc : HasCompactSupport χ) (f : Lp ℝ 2 μ) :
    compactMultiplierCLM hχ hc f=ᵐ[μ] (fun x => χ x*f x) :=
  lpMultiplierCLM_ae _ _ f

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_LocalJoinedH1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma gradient_of_pi_function (q : (Fin 3 → ℝ) → ℝ) (x : R3) (i : Fin 3)
    (hq : DifferentiableAt ℝ q (WithLp.ofLp x)) :
    gradient (fun x : R3 => q (WithLp.ofLp x)) x i =
      fderiv ℝ q (WithLp.ofLp x) (Pi.single i 1) := by
  let E : R3 ≃L[ℝ] (Fin 3 → ℝ) := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)
  have he := (hq.hasFDerivAt.comp x E.hasFDerivAt).fderiv
  have hi := congrArg (fun F : R3 →L[ℝ] ℝ => F (EuclideanSpace.single i 1)) he
  rw [←toDual_gradient,InnerProductSpace.toDual_apply_apply,EuclideanSpace.inner_single_right] at hi
  have hEi : E.toContinuousLinearMap (EuclideanSpace.single i 1)=Pi.single i 1 := rfl
  simpa only [Function.comp_def,ContinuousLinearMap.comp_apply,hEi,mul_one,one_mul,starRingEnd_apply,star_trivial] using hi

def localJoinedValue (τ χ q p : (Fin 3 → ℝ) → ℝ) (x : Fin 3 → ℝ) : ℝ :=
  χ x*(if 0<τ x then p x else q x)

def localJoinedGradient (τ χ q p : (Fin 3 → ℝ) → ℝ)
    (i : Fin 3) (x : Fin 3 → ℝ) : ℝ :=
  fderiv ℝ χ x (Pi.single i 1)*(if 0<τ x then p x else q x)+
    χ x*(if 0<τ x then fderiv ℝ p x (Pi.single i 1) else fderiv ℝ q x (Pi.single i 1))

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_LpFourJet
attribute [-instance] _root_.OAI.ScalarConductivity.H10_completeSpace _root_.OAI.ScalarConductivity.H1_completeSpace _root_.OAI.ScalarConductivity.H1_isClosed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

def lpFourJetCLM : (Fin 4 → Lp ℝ 2 μ) →L[ℝ] Lp JetFiber 2 μ :=
  ∑ i : Fin 4, (((ContinuousLinearMap.id ℝ ℝ).smulRight (EuclideanSpace.single i (1:ℝ))).compLpL 2 μ).comp
    (ContinuousLinearMap.proj i)

lemma lpFourJetCLM_ae (f : Fin 4 → Lp ℝ 2 μ) :
    lpFourJetCLM μ f=ᵐ[μ] (fun x => WithLp.toLp 2 (fun i => f i x)) := by
  have he (i : Fin 4) := (((ContinuousLinearMap.id ℝ ℝ).smulRight (EuclideanSpace.single i (1:ℝ))).coeFn_compLpL (p:=2) (μ:=μ) (f i))
  simp only [lpFourJetCLM,sum_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply]
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
    (fun i : Fin 4 => (((ContinuousLinearMap.id ℝ ℝ).smulRight (EuclideanSpace.single i (1:ℝ))).compLpL 2 μ) (f i)),
    ae_all_iff.mpr he] with x hx hi
  rw [hx]
  simp only [hi,ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.id_apply]
  ext j
  simp [Pi.single_apply]

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

open Set MeasureTheory Filter Topology
open scoped ENNReal

variable {X Y E : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure X} {ν : Measure Y} (e : X ≃ᵐ Y) {c : ℝ≥0∞}
  (hc : c≠∞) (hmap : Measure.map e μ ≤ c • ν)

def lpBoundedPullbackCLM : Lp E 2 ν →L[ℝ] Lp E 2 μ :=
  (Lp.compMeasurePreservingₗᵢ ℝ e (show MeasurePreserving e μ (Measure.map e μ) from ⟨e.measurable,rfl⟩)).toContinuousLinearMap.comp
    (Lp.LpToLpOfMeasureLeSMul (c:=c) hc hmap)

lemma lpBoundedPullbackCLM_ae (f : Lp E 2 ν) :
    lpBoundedPullbackCLM e hc hmap f=ᵐ[μ] (fun x => f (e x)) := by
  apply (Lp.coeFn_compMeasurePreserving _ (show MeasurePreserving e μ (Measure.map e μ) from ⟨e.measurable,rfl⟩)).trans
  exact (show MeasurePreserving e μ (Measure.map e μ) from ⟨e.measurable,rfl⟩).quasiMeasurePreserving.ae_eq_comp
    (Lp.coeFn_LpToLpOfMeasureLeSMul hc hmap f)

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

def childAxis (i : Fin 3) : Fin 3 := ![1,0,2] i

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

def centralChildPatch (k : Fin 2) : Fin 4 := ⟨k.val+2,by omega⟩

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_WholeBallJet
attribute [-instance] _root_.OAI.ScalarConductivity.bumpProbability_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma smoothJet_zero_of_notMem_support {f : R3 → ℝ} {x : R3} (hx : x∉tsupport f) :
    smoothJet f x=0 := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · change f x=0
    exact image_eq_zero_of_notMem_tsupport hx
  · simp [smoothJet,gradient,fderiv_of_notMem_tsupport ℝ hx]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_CentralCylinderGreen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise

def flatCylinderMatrix (s : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  ![![1,0,0],![0,s 0,s 1],![0,s 1,s 2]]

lemma flatCylinderMatrix_energy (s v : Fin 3 → ℝ) :
    v ⬝ᵥ (flatCylinderMatrix s *ᵥ v)=
      (v 0)^2+s 0*(v 1)^2+2*s 1*v 1*v 2+s 2*(v 2)^2 := by
  simp [flatCylinderMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  ring

lemma flatCylinderMatrix_coercive (s : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (v : Fin 3 → ℝ) :
    (1/2)*(∑ k : Fin 3,(v k)^2)≤v ⬝ᵥ (flatCylinderMatrix s *ᵥ v) := by
  rw [flatCylinderMatrix_energy]
  simp only [Fin.sum_univ_succ,Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two,Fin.isValue,Finset.univ_eq_empty,Finset.sum_empty,add_zero]
  nlinarith [hs (v 1) (v 2),sq_nonneg (v 0)]

lemma inverse_congruence_energy (C K : Matrix (Fin 3) (Fin 3) ℝ)
    (hC : C.det≠0) (d : ℝ) (v w : Fin 3 → ℝ) :
    (C*ᵥv) ⬝ᵥ ((d • (C⁻¹ᵀ*K*C⁻¹))*ᵥ(C*ᵥw))=
      d*(v ⬝ᵥ (K*ᵥw)) := by
  have hi (u : Fin 3 → ℝ) : C⁻¹*ᵥ(C*ᵥu)=u := by
    rw [Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hC),Matrix.one_mulVec]
  rw [Matrix.smul_mulVec,dotProduct_smul]
  change d*((C*ᵥv) ⬝ᵥ ((C⁻¹ᵀ*K*C⁻¹)*ᵥ(C*ᵥw)))=_
  rw [←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec,hi,
    Matrix.dotProduct_transpose_mulVec,hi,dotProduct_comm]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_AttachedFlatTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma flat_inverse_congruence_positive (s : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (C : Matrix (Fin 3) (Fin 3) ℝ) (hC : C.det≠0) {d : ℝ} (hd : 0<d)
    {v : Fin 3 → ℝ} (hv : v≠0) :
    0<v ⬝ᵥ ((d • (C⁻¹ᵀ*flatCylinderMatrix s*C⁻¹))*ᵥv) := by
  let u := C⁻¹*ᵥv
  have hu : C*ᵥu=v := by
    change C*ᵥ(C⁻¹*ᵥv)=v
    rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hC),Matrix.one_mulVec]
  have hn : u≠0 := by
    intro h
    rw [h,Matrix.mulVec_zero] at hu
    exact hv hu.symm
  have hex : ∃ k,u k≠0 := by
    by_contra h
    push Not at h
    exact hn (funext h)
  obtain ⟨k,hk⟩ := hex
  have hsum : 0<∑ l : Fin 3,(u l)^2 :=
    (sq_pos_of_ne_zero hk).trans_le (Finset.single_le_sum
      (fun l _ => sq_nonneg (u l)) (Finset.mem_univ k))
  have he := inverse_congruence_energy C (flatCylinderMatrix s) hC d u u
  rw [hu] at he
  rw [he]
  exact mul_pos hd ((mul_pos (by norm_num : (0:ℝ)<1/2) hsum).trans_le
    (flatCylinderMatrix_coercive s hs u))

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
local instance attachedFaceTensorListMeasurableSpace :
    MeasurableSpace (Matrix (Fin 3) (Fin 3) ℝ) := borel _

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

def physicalTestCovector (φ : (Fin 3 → ℝ) → ℝ) (y : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun k => fderiv ℝ φ y (Pi.single k 1)

end ScalarConductivity

end


end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_PhysicalAttachedAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace ScalarConductivity
open Set MeasureTheory Filter Topology

def physicalJet (v : ℝ) (g : Fin 3 → ℝ) : JetFiber := WithLp.toLp 2 (Fin.cases v g)

def H1JetOn (u : H1) (D : Set (Fin 3 → ℝ)) (f : R3 → JetFiber) : Prop :=
  ∀ᵐ x∂ballMeasure,WithLp.ofLp x∈D → u.val x=f x

end ScalarConductivity
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_PiolaFluxContDiff
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
open Set MeasureTheory Filter Topology

lemma smooth_flux_integrable_pairing {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsFiniteMeasureOnCompacts μ] (F : E → E)
    (hF : Continuous F) (hc : HasCompactSupport F) (ψ : E → ℝ)
    (hψ : ContDiff ℝ (↑(⊤ : ℕ∞)) ψ) :
    Integrable (fun x => fderiv ℝ ψ x (F x)) μ := by
  apply (hψ.continuous_fderiv (by simp) |>.clm_apply hF).integrable_of_hasCompactSupport
  apply hc.mono
  intro x hx
  contrapose! hx
  simp only [Function.mem_support, not_not] at hx ⊢
  rw [hx, map_zero]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_FiniteMomentTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace ScalarConductivity
open Set

variable {ι E F : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem fixed_smooth_tests_bound (g : ι → E → F)
    (hg : ∀ i,ContDiff ℝ (↑(⊤ : ℕ∞)) (g i))
    (hs : ∀ i,HasCompactSupport (g i)) (m : ℕ) :
    ∃ B : ℝ,0<B ∧ ∀ (a : ι → ℝ) (A : ℝ),0≤A →
      (∀ i,‖a i‖≤A) → ∀ x : E,
        ‖iteratedFDeriv ℝ m (fun y => ∑ i,a i • g i y) x‖≤B*A := by
  have hmn : (m : WithTop ℕ∞)≤↑(⊤ : ℕ∞) := WithTop.coe_le_coe.mpr le_top
  have hn (i : ι) : ContDiff ℝ m (g i) := (hg i).of_le hmn
  choose C hC using fun i => (hs i).iteratedFDeriv m |>.exists_bound_of_continuous
    ((hg i).continuous_iteratedFDeriv hmn)
  have hC₀ (i : ι) : 0≤C i := (norm_nonneg _).trans (hC i 0)
  have hsum : 0≤∑ i,C i := Finset.sum_nonneg (fun i _ => hC₀ i)
  refine ⟨(∑ i,C i)+1,by linarith,?_⟩
  intro a A hA ha x
  rw [iteratedFDeriv_fun_sum_apply (fun i _ => ((hn i).const_smul (a i)).contDiffAt)]
  simp_rw [iteratedFDeriv_const_smul_apply' (hn _).contDiffAt]
  calc
    _≤∑ i,‖a i • iteratedFDeriv ℝ m (g i) x‖ := norm_sum_le _ _
    _≤∑ i,A*C i := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul]
      exact mul_le_mul (ha i) (hC i x) (norm_nonneg _) hA
    _≤((∑ i,C i)+1)*A := by
      rw [←Finset.mul_sum]
      nlinarith

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_BoxMomentRightInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory

lemma exists_unit_global_interval_bump {a b : ℝ} (hab : a<b) :
    ∃ η : ℝ → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) η ∧ HasCompactSupport η ∧
      tsupport η⊆Ioo a b ∧ (∫ t,η t)=1 := by
  obtain ⟨η,hη,hs,hv,hi⟩ := exists_unit_interval_bump hab
  refine ⟨η,hη,hs,hv,?_⟩
  rw [intervalIntegral.integral_of_le hab.le] at hi
  have he : (∫ t in Ioc a b,η t)=(∫ t,η t) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t ht
    exact image_eq_zero_of_notMem_tsupport (fun hh => ht ⟨(hv hh).1,(hv hh).2.le⟩)
  rwa [he] at hi

end ScalarConductivity



end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_ParametricDiffeomorph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology

section Slice
variable {P E : Type*} [TopologicalSpace P] [TopologicalSpace E]

lemma fiberInverse_fst (Y : OpenPartialHomeomorph (P×E) (P×E))
    (hY : ∀ p x,(Y (p,x)).1=p) {p : P} {y : E} (hy : (p,y)∈Y.target) :
    (Y.symm (p,y)).1=p := by
  have he := congrArg Prod.fst (Y.right_inv hy)
  rw [hY] at he
  exact he

def fiberSlice (Y : OpenPartialHomeomorph (P×E) (P×E))
    (hY : ∀ p x,(Y (p,x)).1=p) (p : P) : OpenPartialHomeomorph E E where
  toFun x := (Y (p,x)).2
  invFun y := (Y.symm (p,y)).2
  source := {x | (p,x)∈Y.source}
  target := {y | (p,y)∈Y.target}
  map_source' := by
    intro x hx
    have he : (p,(Y (p,x)).2)=Y (p,x) := Prod.ext (hY p x).symm rfl
    change (p,(Y (p,x)).2)∈Y.target
    rw [he]; exact Y.map_source hx
  map_target' := by
    intro y hy
    have he : (p,(Y.symm (p,y)).2)=Y.symm (p,y) := Prod.ext (fiberInverse_fst Y hY hy).symm rfl
    change (p,(Y.symm (p,y)).2)∈Y.source
    rw [he]; exact Y.map_target hy
  left_inv' := by
    intro x hx
    have he : (p,(Y (p,x)).2)=Y (p,x) := Prod.ext (hY p x).symm rfl
    rw [he,Y.left_inv hx]
  right_inv' := by
    intro y hy
    have he : (p,(Y.symm (p,y)).2)=Y.symm (p,y) := Prod.ext (fiberInverse_fst Y hY hy).symm rfl
    rw [he,Y.right_inv hy]
  open_source := Y.open_source.preimage (continuous_const.prodMk continuous_id)
  open_target := Y.open_target.preimage (continuous_const.prodMk continuous_id)
  continuousOn_toFun := continuous_snd.continuousOn.comp
    (Y.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ hx => hx))
    (fun _ _ => mem_univ _)
  continuousOn_invFun := continuous_snd.continuousOn.comp
    (Y.symm.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ hx => hx))
    (fun _ _ => mem_univ _)
end Slice

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

def spatialFDeriv (f : P×E → F) (q : P×E) : E →L[ℝ] F :=
  fderiv ℝ (fun x => f (q.1,x)) q.2

lemma spatialFDeriv_eq {f : P×E → F} {q : P×E} (hf : DifferentiableAt ℝ f q) :
    spatialFDeriv f q=(fderiv ℝ f q).comp (ContinuousLinearMap.inr ℝ P E) := by
  rcases q with ⟨p,x⟩
  have h := hf.hasFDerivAt.comp x ((hasFDerivAt_const p x).prodMk (hasFDerivAt_id x))
  exact h.fderiv

lemma spatialFDeriv_smoothOn {f : P×E → F} {U : Set (P×E)}
    (hU : IsOpen U) (hf : ContDiffOn ℝ (↑(⊤:ℕ∞)) f U) :
    ContDiffOn ℝ (↑(⊤:ℕ∞)) (spatialFDeriv f) U := by
  apply hU.contDiffOn_iff.mpr
  intro q hq
  have hd : ContDiffAt ℝ (↑(⊤:ℕ∞)) (fderiv ℝ f) q :=
    (hf.contDiffAt (hU.mem_nhds hq)).fderiv_right (by simp)
  have hc : ContDiffAt ℝ (↑(⊤:ℕ∞))
      (fun z => (fderiv ℝ f z).comp (ContinuousLinearMap.inr ℝ P E)) q :=
    hd.clm_comp contDiffAt_const
  apply hc.congr_of_eventuallyEq
  filter_upwards [hU.mem_nhds hq] with z hz
  exact spatialFDeriv_eq ((hf.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp))

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
open Set Filter Topology

variable {P E F : Type*} [TopologicalSpace P] [TopologicalSpace E]
  [NormedAddCommGroup F]

lemma compact_parametric_norm_small {f : P×E → F} {p : P} {K : Set E}
    (hK : IsCompact K) (hf : ∀ x∈K,ContinuousAt f (p,x))
    (hz : ∀ x∈K,f (p,x)=0) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ q in 𝓝 p,∀ x∈K,‖f (q,x)‖≤ε := by
  apply hK.eventually_forall_of_forall_eventually
  intro x hx
  have hn : ‖f (p,x)‖<ε := by rw [hz x hx,norm_zero]; exact hε
  exact ((hf x hx).norm.eventually_lt_const hn).mono (fun _ h => h.le)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_CompactParametricBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology
open scoped Manifold

variable {P E : Type*} [TopologicalSpace P] [TopologicalSpace E]

lemma exists_smooth_core_cutoff
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {K Ω : Set V} (hK : IsCompact K) (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hsub : K⊆Ω) :
    ∃ χ : V → ℝ,ContDiff ℝ (↑(⊤ : ℕ∞)) χ ∧ HasCompactSupport χ ∧
      tsupport χ⊆Ω ∧ (∀ x,χ x∈Icc 0 1) ∧
      (∀ x∈K,χ =ᶠ[𝓝 x] (fun _ => 1)) := by
  obtain ⟨χ,hχ₀,hχ₁,hχb⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed (𝓘(ℝ,V))
    hΩ.isClosed_compl hK.isClosed (disjoint_left.mpr (fun _ hx hxK => hx (hsub hxK))) (n:=⊤)
  have ht : tsupport (χ : V → ℝ)⊆Ω := by
    intro x hx
    by_contra hn
    exact (notMem_tsupport_iff_eventuallyEq.mpr (hχ₀.filter_mono (nhds_le_nhdsSet hn))) hx
  refine ⟨χ,contMDiff_iff_contDiff.mp χ.contMDiff,
    (hb.subset ht).isCompact_closure.of_isClosed_subset (isClosed_tsupport _) subset_closure,
    ht,hχb,?_⟩
  intro x hx
  exact hχ₁.filter_mono (nhds_le_nhdsSet hx)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_WeakWeyl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace ScalarConductivity
open Set MeasureTheory Filter Topology
open scoped Convolution

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

def radialAverageF (f : WeylSpace → F) (s : ℝ) : WeylSpace → F :=
  radialEta radialProfile s ⋆[ContinuousLinearMap.lsmul ℝ ℝ,volume] f

def RadialMeanOn (f : WeylSpace → F) (a : WeylSpace) (R : ℝ) : Prop :=
  ∀ s : ℝ, 0 < s → ∀ x : WeylSpace, dist x a+s<R → f x=radialAverageF f s x

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_MatrixPerturbInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Matrix Filter Topology
open scoped Matrix.Norms.Elementwise

variable {ι P : Type*} [Fintype ι] [DecidableEq ι] [TopologicalSpace P]

omit [DecidableEq ι] in
lemma matrix_pi_mulVec_bound (A : Matrix ι ι ℝ) (b : ι → ℝ) (i : ι) :
    ‖(A*ᵥb) i‖≤(Fintype.card ι:ℝ)*‖A‖*‖b‖ := by
  change ‖∑ j,A i j*b j‖≤_
  calc
    _≤∑ j,‖A i j*b j‖ := norm_sum_le _ _
    _≤∑ j,‖A‖*‖b‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul]
      exact mul_le_mul ((norm_le_pi_norm (A i) j).trans (norm_le_pi_norm A i))
        (norm_le_pi_norm b j) (norm_nonneg _) (norm_nonneg _)
    _=_ := by simp [mul_assoc]

theorem matrix_inverse_locally_bounded {M : P → Matrix ι ι ℝ} {p₀ : P}
    (hM : ContinuousAt M p₀) (h₀ : IsUnit (M p₀)) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ p in 𝓝 p₀,
      IsUnit (M p) ∧ (∀ b : ι → ℝ,
        M p*ᵥ((M p)⁻¹*ᵥb)=b ∧ ∀ i,‖((M p)⁻¹*ᵥb) i‖≤C*‖b‖) := by
  have hd₀ : (M p₀).det≠0 := isUnit_iff_ne_zero.mp ((isUnit_iff_isUnit_det _).mp h₀)
  have hdi : ContinuousAt Ring.inverse (M p₀).det := by
    simpa only [Ring.inverse_eq_inv'] using (continuousAt_inv₀ hd₀)
  have hi : ContinuousAt (fun p => (M p)⁻¹) p₀ :=
    (continuousAt_matrix_inv _ hdi).comp hM
  have hn : ∀ᶠ p in 𝓝 p₀,‖(M p)⁻¹‖<‖(M p₀)⁻¹‖+1 :=
    hi.norm.eventually (gt_mem_nhds (by linarith))
  have hd : ∀ᶠ p in 𝓝 p₀,(M p).det≠0 :=
    ((continuous_id.matrix_det).continuousAt.comp hM).tendsto.eventually (isOpen_ne.mem_nhds hd₀)
  let C := ((Fintype.card ι:ℝ)+1)*(‖(M p₀)⁻¹‖+1)
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  filter_upwards [hn,hd] with p hp hpd
  have hu : IsUnit (M p).det := isUnit_iff_ne_zero.mpr hpd
  refine ⟨(isUnit_iff_isUnit_det _).mpr hu,?_⟩
  intro b
  refine ⟨?_,?_⟩
  · rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ hu,Matrix.one_mulVec]
  · intro i
    apply (matrix_pi_mulVec_bound _ b i).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg b)
    have hn₀ : 0≤‖(M p₀)⁻¹‖+1 := by positivity
    dsimp only [C]
    have hh := mul_le_mul_of_nonneg_left hp.le (show (0:ℝ)≤Fintype.card ι by positivity)
    nlinarith

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_CompactMomentPerturbation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix Filter Topology

variable {ι P : Type*}
  [TopologicalSpace P] [FirstCountableTopology P] [LocallyCompactSpace P]

def compactCrossMoment (χ : ℝ → ℝ) (w v : ℝ → ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => ∫ s, χ s*w s j*v s i

lemma compactCrossMoment_restrict (χ : ℝ → ℝ) (w v : ℝ → ι → ℝ) (i j : ι) :
    compactCrossMoment χ w v i j=∫ s in tsupport χ, χ s*w s j*v s i := by
  dsimp only [compactCrossMoment]
  nth_rw 1 [←setIntegral_univ]
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero MeasurableSet.univ (subset_univ _)
  intro s hs
  simp only [image_eq_zero_of_notMem_tsupport hs.2,zero_mul]

lemma compactCrossMoment_continuous {χ : ℝ → ℝ} {w : ℝ → ι → ℝ}
    {v : P → ℝ → ι → ℝ} (hc : Continuous χ) (hs : HasCompactSupport χ)
    (hw : ∀ j,Continuous (fun s => w s j))
    (hv : ∀ i,Continuous (fun ps : P × ℝ => v ps.1 ps.2 i)) :
    Continuous (fun p => compactCrossMoment χ w (v p)) := by
  apply continuous_pi; intro i
  apply continuous_pi; intro j
  simp only [compactCrossMoment_restrict]
  apply continuous_parametric_integral_of_continuous (μ := volume) _ hs
  exact ((hc.comp continuous_snd).mul ((hw j).comp continuous_snd)).mul (hv i)

lemma compactCrossMoment_self (χ : ℝ → ℝ) (w : ℝ → ι → ℝ) :
    compactCrossMoment χ w w=compactMomentGram χ w := by
  ext i j
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun s => by dsimp; ring)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_HarmonicRankAffine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace ScalarConductivity
open Set MeasureTheory Filter Topology Laplacian InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} [Fintype ι]

def HarmonicPairRegularOn (u v : E → ℝ) (O : Set E) : Prop :=
  (∃ p q : E, ∀ x∈O, fderiv ℝ u x p*fderiv ℝ v x q-
    fderiv ℝ u x q*fderiv ℝ v x p ≠ 0) ∨
  (∃ w : E, ∃ α β : ℝ, ∀ x∈O, fderiv ℝ u x w ≠ 0 ∧ v x=α*u x+β) ∨
  (∃ w : E, ∃ α β : ℝ, ∀ x∈O, fderiv ℝ v x w ≠ 0 ∧ u x=α*v x+β) ∨
  (∃ α β : ℝ, ∀ x∈O, u x=α ∧ v x=β)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_WeakHarmonicClassical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace ScalarConductivity
open Set MeasureTheory Matrix Filter Topology
open scoped Matrix.Norms.Elementwise

variable {ι P : Type*} [Fintype ι] [DecidableEq ι]
  [TopologicalSpace P] [FirstCountableTopology P] [LocallyCompactSpace P]

omit [DecidableEq ι] in
lemma compactCrossMoment_eval {χ : ℝ → ℝ} {w v : ℝ → ι → ℝ}
    (hc : Continuous χ) (hs : HasCompactSupport χ)
    (hw : ∀ j,Continuous (fun s => w s j)) (hv : ∀ i,Continuous (fun s => v s i))
    (a : ι → ℝ) (i : ι) :
    (∫ s,χ s*(a ⬝ᵥ w s)*v s i)=(compactCrossMoment χ w v*ᵥa) i := by
  change (∫ s,χ s*(a ⬝ᵥ w s)*v s i)=∑ j,compactCrossMoment χ w v i j*a j
  calc
    _ = ∫ s,∑ j,(χ s*w s j*v s i)*a j := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun s => by
        simp only [dotProduct,Finset.mul_sum,Finset.sum_mul]
        apply Finset.sum_congr rfl; intro j _; ring
    _ = _ := by
      have hi (j : ι) : Integrable (fun s => (χ s*w s j*v s i)*a j) :=
        (((hc.mul (hw j)).mul (hv i)).integrable_of_hasCompactSupport
          (hs.mul_right.mul_right)).mul_const _
      rw [integral_finsetSum _ (fun j _ => hi j)]
      simp only [integral_mul_const,compactCrossMoment]

theorem compactMoment_uniform_inverse {χ : ℝ → ℝ} {w : ℝ → ι → ℝ}
    {v : P → ℝ → ι → ℝ} {p₀ : P}
    (hc : ContDiff ℝ (↑(⊤ : ℕ∞)) χ) (hs : HasCompactSupport χ)
    (hw : ∀ j,ContDiff ℝ (↑(⊤ : ℕ∞)) (fun s => w s j))
    (hv : ∀ i,Continuous (fun ps : P × ℝ => v ps.1 ps.2 i))
    (hlim : v p₀=w) (hG : (compactMomentGram χ w).PosDef) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ p in 𝓝 p₀, ∀ b : ι → ℝ,
      ∃ a : ι → ℝ, (∀ i,‖a i‖≤C*‖b‖) ∧
        ContDiff ℝ (↑(⊤ : ℕ∞)) (fun s => χ s*(a ⬝ᵥ w s)) ∧
        HasCompactSupport (fun s => χ s*(a ⬝ᵥ w s)) ∧
        tsupport (fun s => χ s*(a ⬝ᵥ w s))⊆tsupport χ ∧
        (∀ i,(∫ s,χ s*(a ⬝ᵥ w s)*v p s i)=b i) := by
  have hM := compactCrossMoment_continuous hc.continuous hs (fun j => (hw j).continuous) hv
  have hM₀ : IsUnit (compactCrossMoment χ w (v p₀)) := by
    rw [hlim,compactCrossMoment_self]
    exact hG.isUnit
  obtain ⟨C,hC,hne⟩ := matrix_inverse_locally_bounded hM.continuousAt hM₀
  refine ⟨C,hC,?_⟩
  filter_upwards [hne] with p hp
  intro b
  let a := (compactCrossMoment χ w (v p))⁻¹*ᵥb
  obtain ⟨ha,hb⟩ := hp.2 b
  refine ⟨a,hb,hc.mul (ContDiff.sum fun j _ => contDiff_const.mul (hw j)),
    hs.mul_right,tsupport_mul_subset_left,?_⟩
  intro i
  have hvp (j : ι) : Continuous (fun s => v p s j) :=
    (hv j).comp (continuous_const.prodMk continuous_id)
  rw [compactCrossMoment_eval hc.continuous hs (fun j => (hw j).continuous) hvp]
  exact congrFun ha i

theorem wall_moment_uniform_inverse {l r σ lam : ℝ} (hlr : l < r)
    (hσ : σ≠0) (hlam : lam≠0) {v : P → ℝ → Fin 3 → ℝ} {p₀ : P}
    (hv : ∀ i,Continuous (fun ps : P × ℝ => v ps.1 ps.2 i))
    (hlim : v p₀=wallMomentBasis σ lam) :
    ∃ χ : ℝ → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) χ ∧ HasCompactSupport χ ∧
      tsupport χ⊆Icc l r ∧ ∃ C : ℝ,0<C ∧ ∀ᶠ p in 𝓝 p₀,∀ b : Fin 3 → ℝ,
        ∃ a : Fin 3 → ℝ, (∀ i,‖a i‖≤C*‖b‖) ∧
          ContDiff ℝ (↑(⊤ : ℕ∞)) (fun s => χ s*(a ⬝ᵥ wallMomentBasis σ lam s)) ∧
          HasCompactSupport (fun s => χ s*(a ⬝ᵥ wallMomentBasis σ lam s)) ∧
          tsupport (fun s => χ s*(a ⬝ᵥ wallMomentBasis σ lam s))⊆Icc l r ∧
          (∀ i,(∫ s,χ s*(a ⬝ᵥ wallMomentBasis σ lam s)*v p s i)=b i) := by
  obtain ⟨χ,hc,hs,hn,hp,hsub⟩ := positive_interval_bump hlr
  have hG := compactMomentGram_posDef hc.continuous hs
    (fun i => (wallMomentBasis_smooth σ lam i).continuous) hn hp
    (wallMomentBasis_independent hlr hσ hlam)
  obtain ⟨C,hC,he⟩ := compactMoment_uniform_inverse hc hs (wallMomentBasis_smooth σ lam) hv hlim hG
  refine ⟨χ,hc,hs,hsub,C,hC,?_⟩
  filter_upwards [he] with p hpe
  intro b
  obtain ⟨a,ha,hsmo,hcs,ht,hi⟩ := hpe b
  exact ⟨a,ha,hsmo,hcs,ht.trans hsub,hi⟩

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Walls_WallSurfaceMomentInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix Filter Topology

variable {P : Type*} [TopologicalSpace P] [FirstCountableTopology P] [LocallyCompactSpace P]

def wallProjectedMoment (η : ℝ → ℝ) (w : P → (ℝ×ℝ) → Fin 3 → ℝ)
    (p : P) (s : ℝ) (i : Fin 3) : ℝ := ∫ y,η y*w p (s,y) i

lemma wallProjectedMoment_continuous {η : ℝ → ℝ} {w : P → (ℝ×ℝ) → Fin 3 → ℝ}
    (hη : Continuous η) (hs : HasCompactSupport η)
    (hw : ∀ i,Continuous (fun pq : P × (ℝ×ℝ) => w pq.1 pq.2 i)) (i : Fin 3) :
    Continuous (fun ps : P × ℝ => wallProjectedMoment η w ps.1 ps.2 i) := by
  have he (p : P) (s : ℝ) : wallProjectedMoment η w p s i=
      ∫ y in tsupport η,η y*w p (s,y) i := by
    dsimp [wallProjectedMoment]
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    simp only [image_eq_zero_of_notMem_tsupport hy,zero_mul]
  simp_rw [he]
  apply continuous_parametric_integral_of_continuous (μ := volume) _ hs
  exact (hη.comp continuous_snd).mul ((hw i).comp
    ((continuous_fst.fst).prodMk (continuous_fst.snd.prodMk continuous_snd)))

lemma surface_product_compact {f η : ℝ → ℝ} (hf : HasCompactSupport f)
    (hη : HasCompactSupport η) :
    HasCompactSupport (fun q : ℝ×ℝ => f q.1*η q.2) ∧
      tsupport (fun q : ℝ×ℝ => f q.1*η q.2)⊆tsupport f ×ˢ tsupport η := by
  have hv : Function.support (fun q : ℝ×ℝ => f q.1*η q.2)⊆tsupport f ×ˢ tsupport η := by
    intro q hq
    exact ⟨subset_tsupport f (mul_ne_zero_iff.mp hq).1,
      subset_tsupport η (mul_ne_zero_iff.mp hq).2⟩
  exact ⟨HasCompactSupport.of_support_subset_isCompact (hf.prod hη) hv,
    closure_minimal hv (hf.isClosed.prod hη.isClosed)⟩

lemma wallProjectedMoment_fubini {f η : ℝ → ℝ} {w : (ℝ×ℝ) → ℝ}
    (hf : Continuous f) (hsf : HasCompactSupport f)
    (hη : Continuous η) (hsη : HasCompactSupport η) (hw : Continuous w) :
    (∫ q : ℝ×ℝ,(f q.1*η q.2)*w q)=∫ s,f s*(∫ y,η y*w (s,y)) := by
  have hi : Integrable (fun q : ℝ×ℝ => (f q.1*η q.2)*w q) :=
    (((hf.comp continuous_fst).mul (hη.comp continuous_snd)).mul hw).integrable_of_hasCompactSupport
      (surface_product_compact hsf hsη).1.mul_right
  rw [Measure.volume_eq_prod] at hi ⊢
  rw [integral_prod _ hi]
  congr 1
  ext s
  simp_rw [mul_assoc]
  exact integral_const_mul _ _

theorem wall_surface_moment_uniform_inverse {l r a b σ lam : ℝ}
    (hlr : l < r) (hab : a<b) (hσ : σ≠0) (hlam : lam≠0)
    {w : P → (ℝ×ℝ) → Fin 3 → ℝ} {p₀ : P}
    (hw : ∀ i,Continuous (fun pq : P × (ℝ×ℝ) => w pq.1 pq.2 i))
    (hlim : ∀ q,w p₀ q=wallMomentBasis σ lam q.1) :
    ∃ χ η : ℝ → ℝ,
      ContDiff ℝ (↑(⊤ : ℕ∞)) χ ∧ ContDiff ℝ (↑(⊤ : ℕ∞)) η ∧
      HasCompactSupport χ ∧ HasCompactSupport η ∧
      tsupport χ⊆Icc l r ∧ tsupport η⊆Ioo a b ∧
      ∃ C : ℝ,0<C ∧ ∀ᶠ p in 𝓝 p₀,∀ m : Fin 3 → ℝ,
        ∃ c : Fin 3 → ℝ,(∀ i,‖c i‖≤C*‖m‖) ∧
          let f := fun q : ℝ×ℝ => (χ q.1*(c ⬝ᵥ wallMomentBasis σ lam q.1))*η q.2
          ContDiff ℝ (↑(⊤ : ℕ∞)) f ∧ HasCompactSupport f ∧
          tsupport f⊆Icc l r ×ˢ Ioo a b ∧
          (∀ i,(∫ q,f q*w p q i)=m i) := by
  obtain ⟨η,hη,hsη,hvη,hiη⟩ := exists_unit_global_interval_bump hab
  have hc := wallProjectedMoment_continuous hη.continuous hsη hw
  have he : wallProjectedMoment η w p₀=wallMomentBasis σ lam := by
    ext s i
    dsimp [wallProjectedMoment]
    simp_rw [hlim]
    rw [integral_mul_const,hiη,one_mul]
  obtain ⟨χ,hχ,hsχ,hvχ,C,hC,hne⟩ := wall_moment_uniform_inverse hlr hσ hlam hc he
  refine ⟨χ,η,hχ,hη,hsχ,hsη,hvχ,hvη,C,hC,?_⟩
  filter_upwards [hne] with p hp
  intro m
  obtain ⟨c,hc,hf,hsf,hvf,hif⟩ := hp m
  refine ⟨c,hc,((hf.comp contDiff_fst).mul (hη.comp contDiff_snd)),
    (surface_product_compact hsf hsη).1,
    (surface_product_compact hsf hsη).2.trans (prod_mono hvf hvη),?_⟩
  intro i
  rw [wallProjectedMoment_fubini (w := fun q => w p q i) hf.continuous hsf hη.continuous hsη
    ((hw i).comp (continuous_const.prodMk continuous_id))]
  exact hif i

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_CascadePeriodicity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory Matrix

def angularInteger (n : Fin 2 → ℤ) : Fin 3 → ℤ := ![0,n 0,n 1]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_ChangeOld
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

lemma fderiv_eq_of_eqOn_open {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] {O : Set E} (hO : IsOpen O)
    {u v : E → V} (he : EqOn u v O) {x : E} (hx : x ∈ O) :
    fderiv ℝ u x = fderiv ℝ v x := by
  apply Filter.EventuallyEq.fderiv_eq
  exact Filter.EventuallyEq.filter_mono (he.eventuallyEq_of_mem (hO.mem_nhds hx)) le_rfl

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

def axialPairScaling {k : ℝ} (hk : k≠0) : (Fin 2 → ℝ) ≃L[ℝ] (Fin 2 → ℝ) :=
  ContinuousLinearEquiv.piCongrRight (fun i : Fin 2 =>
    (LinearEquiv.smulOfNeZero ℝ ℝ (if i=0 then k⁻¹ else 1) (by split_ifs <;> simp_all)).toContinuousLinearEquiv)

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

def flatAxis (i : Fin 3) : Fin 3 → ℝ := Pi.single i 1

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_SmoothAngularCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory

def periodCutoff (T x : ℝ) : ℝ := smoothTransition (x/T+1)-smoothTransition (x/T)

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_SmoothNormalizedEndFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology

lemma smooth_mul_of_support_in_open {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f ρ : E→ℝ} {S : Set E} (hS : IsOpen S)
    (hf : ContDiffOn ℝ (↑(⊤:ℕ∞)) f S) (hρ : ContDiff ℝ (↑(⊤:ℕ∞)) ρ)
    (hs : tsupport ρ⊆S) : ContDiff ℝ (↑(⊤:ℕ∞)) (fun x => ρ x*f x) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x∈tsupport ρ
  · exact hρ.contDiffAt.mul (hf.contDiffAt (hS.mem_nhds (hs hx)))
  · have he : (fun y => ρ y*f y)=ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
      simp [hy]
    exact contDiffAt_const.congr_of_eventuallyEq he

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

abbrev TorusRealPlane := Fin 2 → ℝ

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

local instance angularCoefficientMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance angularCoefficientProbabilityMeasure :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

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
local instance angularJetFiniteCylinderMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance angularJetFiniteCylinderProbabilityMeasure :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_AngularGraph
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
local instance angularGraphMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_DelayedEndingRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

def axialAmplitudeEquiv (a : ℝ) (ha : a≠0) : (Fin 2 → ℝ) ≃L[ℝ] (Fin 2 → ℝ) :=
  ContinuousLinearEquiv.piCongrRight (fun i : Fin 2 =>
    (LinearEquiv.smulOfNeZero ℝ ℝ (if i=0 then 1 else a) (by split_ifs <;> simp_all)).toContinuousLinearEquiv)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_AngularFourierConjugacy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix

def angularInverseMatrix (A : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![A 1 1,-A 0 1;-A 1 0,A 0 0]

lemma angular_mul_inverse {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : A.det=1) :
    A*angularInverseMatrix A=1 := by
  have hd : A 0 0*A 1 1-A 0 1*A 1 0=1 := by simpa only [det_fin_two] using hA
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply,Fin.sum_univ_two,angularInverseMatrix] <;> nlinarith

lemma angular_inverse_mul {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : A.det=1) :
    angularInverseMatrix A*A=1 := by
  have hd : A 0 0*A 1 1-A 0 1*A 1 0=1 := by simpa only [det_fin_two] using hA
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply,Fin.sum_univ_two,angularInverseMatrix] <;> nlinarith

def angularFrequencyEquiv (A : Matrix (Fin 2) (Fin 2) ℤ) (hA : A.det=1) :
    (Fin 2 → ℤ) ≃ (Fin 2 → ℤ) where
  toFun h := h ᵥ* A
  invFun h := h ᵥ* angularInverseMatrix A
  left_inv h := by
    change (h ᵥ* A) ᵥ* angularInverseMatrix A=h
    rw [vecMul_vecMul,angular_mul_inverse hA,vecMul_one]
  right_inv h := by
    change (h ᵥ* angularInverseMatrix A) ᵥ* A=h
    rw [vecMul_vecMul,angular_inverse_mul hA,vecMul_one]

@[simp] lemma angularFrequencyEquiv_apply (A : Matrix (Fin 2) (Fin 2) ℤ)
    (hA : A.det=1) (h : Fin 2 → ℤ) : angularFrequencyEquiv A hA h=h ᵥ* A := rfl

@[simp] lemma angularFrequencyEquiv_symm_vecMul (A : Matrix (Fin 2) (Fin 2) ℤ)
    (hA : A.det=1) (h : Fin 2 → ℤ) :
    (angularFrequencyEquiv A hA).symm (h ᵥ* A)=h :=
  (angularFrequencyEquiv A hA).symm_apply_apply h

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

def angularShiftPhase (phase : (Fin 2 → ℤ) → ℝ) (v : Fin 2 → ℝ)
    (h : Fin 2 → ℤ) : ℝ := phase h+(h 0:ℝ)*v 0+(h 1:ℝ)*v 1

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_FieldVector
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
open Matrix Set MeasureTheory
open scoped BigOperators Matrix.Norms.Elementwise

abbrev FieldVector := EuclideanSpace ℝ (Fin 3 × Fin 2)

def fieldVector (E : Matrix (Fin 3) (Fin 2) ℝ) : FieldVector :=
  WithLp.toLp 2 (fun ij => E ij.1 ij.2)

lemma fieldVector_add (E F : Matrix (Fin 3) (Fin 2) ℝ) :
    fieldVector (E+F) = fieldVector E+fieldVector F := rfl

lemma fieldVector_smul (c : ℝ) (E : Matrix (Fin 3) (Fin 2) ℝ) :
    fieldVector (c • E) = c • fieldVector E := rfl

end ScalarConductivity

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

noncomputable def fieldVectorCLM : Matrix (Fin 3) (Fin 2) ℝ →L[ℝ] FieldVector :=
  ({ toFun := fieldVector
     map_add' := fieldVector_add
     map_smul' := fieldVector_smul } : Matrix (Fin 3) (Fin 2) ℝ →ₗ[ℝ] FieldVector).toContinuousLinearMap

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_BranchOutputNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix UnitAddTorus

variable {E : Type*} [AddCommGroup E]

def branchNormalize (i : Fin 3) (u : Fin 2 → E) : Fin 2 → E :=
  if i=0 then ![-u 0,u 1-u 0] else if i=1 then u else ![u 1,u 0]

lemma branchNormalize_involutive (i : Fin 3) : Function.Involutive (branchNormalize (E:=E) i) := by
  intro u
  ext j
  fin_cases i <;> fin_cases j <;> simp [branchNormalize]

lemma branchNormalize_add (i : Fin 3) (u v : Fin 2 → E) :
    branchNormalize i (u+v)=branchNormalize i u+branchNormalize i v := by
  ext j
  fin_cases i <;> fin_cases j <;> simp [branchNormalize] <;> abel

variable [Module ℝ E]

def branchNormalizeLinear (i : Fin 3) : (Fin 2 → E) →ₗ[ℝ] (Fin 2 → E) where
  toFun := branchNormalize i
  map_add' := branchNormalize_add i
  map_smul' c u := by
    ext j
    fin_cases i <;> fin_cases j <;> simp [branchNormalize,smul_sub]

def branchNormalizeEquiv (i : Fin 3) : (Fin 2 → ℝ) ≃L[ℝ] (Fin 2 → ℝ) :=
  ({ toLinearMap := branchNormalizeLinear i
     invFun := branchNormalize i
     left_inv := branchNormalize_involutive i
     right_inv := branchNormalize_involutive i } :
        (Fin 2 → ℝ) ≃ₗ[ℝ] (Fin 2 → ℝ)).toContinuousLinearEquiv

@[simp] lemma branchNormalizeEquiv_apply (i : Fin 3) (u : Fin 2 → ℝ) :
    branchNormalizeEquiv i u=branchNormalize i u := rfl

end ScalarConductivity



end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_BranchTerminalFluxIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix UnitAddTorus
open scoped ENNReal
local instance branchTerminalFluxIntegralMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_PhysicalBlockTensor
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

lemma childAxis_pi_norm (v : Fin 3 → ℝ) : ‖fun i => v (childAxis i)‖=‖v‖ := by
  apply le_antisymm
  · exact (pi_norm_le_iff_of_nonneg (norm_nonneg v)).mpr
      (fun i => norm_le_pi_norm v (childAxis i))
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg (fun i => v (childAxis i)))).mpr
    intro i
    have h := norm_le_pi_norm (fun j => v (childAxis j)) (childAxis i)
    have he : childAxis (childAxis i)=i := by fin_cases i <;> rfl
    simpa only [he] using h

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_AffineCylinderIntegral
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
local instance affineCylinderIntegralMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

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
local instance attachedPeriodicFluxMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_AttachedPeriodicGreen
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
local instance attachedPeriodicGreenMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

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

def WeightedAnnihilation (a : R3 → ℝ) (w u : H1) (c : ℝ) : Prop :=
  ∀ (f : R3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) f →
    HasCompactSupport f → tsupport f⊆ball →
      ∫ x, a x*inner ℝ (weakGradient w x)
        ((weakValue u x-c) • gradient f x+f x • weakGradient u x) ∂ballMeasure=0

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

lemma SmoothLipZero.lipschitz (F : SmoothLipZero) : LipschitzWith (⟨F.bound,F.bound_nonneg⟩ : ℝ≥0) F :=
  lipschitzWith_of_nnnorm_deriv_le (F.smooth.differentiable (by simp)) (fun x => F.deriv_bound x)

end ScalarConductivity

end
end

end OAI
end


