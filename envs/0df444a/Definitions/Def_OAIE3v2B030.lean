-- Prove2me | Definitions.Def_OAIE3v2B030
-- name    : OAIE3v2B030
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T09:59:39.786981+00:00
-- url     : https://prove2.me/theorems/710d82f0-aa7e-42d5-9ed8-59162e614647
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 31 of 311
-- statement:
--   Definitions bundle 31 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports no other bundle of this split.
--
--   Modules: `Dynamics/AdaptedMapGeometryBudget.lean`, `Dynamics/AllocatedCandidateStageScalarBudget.lean`, `Dynamics/AllocatedExternalCandidateCoveredBudget.lean`, `Dynamics/AllocatedExternalCandidateExponentialFreezingBudget.lean`, `Dynamics/CandidateFrontSourceLossBudget.lean`, `Dynamics/ImageCoverBudget.lean`, `Dynamics/JetOutputRadiusLogBudget.lean`, `Dynamics/LieSubalgebraRepresentativeBudget.lean`, `Dynamics/MarkedRefilteredModelBudget.lean`, `Dynamics/NativeParameterCoverBudget.lean`, `Dynamics/PartitionedRegularizationBudget.lean`, `Dynamics/ScalarCubeProductRiemannBudget.lean`, `Estimates/AdaptedMarkedMapHeight.lean`, `Estimates/AllocatedExternalCandidateRealThreshold.lean`, `Estimates/AllocatedExternalCandidateThresholdSuccessor.lean`, `Estimates/AllocatedProfileDimensions.lean`, `Estimates/AmplificationFinalCostGrowth.lean`, `Estimates/CoefficientRowReindex.lean`, `Estimates/FourSlicedProductSmoothing.lean`, `Estimates/FullTaggedRationalRetraction.lean`, `Estimates/InactiveShortLogBounds.lean`, `Estimates/McShaneEnvelope.lean`, `Estimates/NativeIteratedDifferencing.lean`, `Estimates/NativeOptionFixedSourceQuotientMarkStrong.lean`, `Estimates/NativeOrbitFreezing.lean`, `Estimates/NativeSampleModelFamily.lean`, `Estimates/NormalizedJetColumns.lean`, `Estimates/PreparedFiniteForwardTreeStorage.lean`, `Estimates/PreparedModularProductivityPrecision.lean`, `Estimates/ProductCutoffLipschitz.lean`, `Estimates/RawProductArrayNormalization.lean`, `Estimates/RealifiedTopQuotient.lean`, `Estimates/RepresentativeWindowPatch.lean`, `Estimates/SelectedCoefficientEvaluation.lean`, `Estimates/UniformFamilyMemberNet.lean`, `Fourier/AllocatedRecoveredTagTorusVariation.lean`, `Fourier/CharacterCoordinateScale.lean`, `Fourier/IntegerPolynomialTorusPeriod.lean`, `Fourier/PrimePowerCharacterScaling.lean`, `Geometry/AllocatedNarrowSpatialCanonicalComparison.lean`, `Geometry/BoxWindowAveraging.lean`, `Geometry/OptionProductMetric.lean`, `Geometry/PartitionedIdealSupport.lean`, `Geometry/PivotCoordinateChange.lean`, `Geometry/RationalModelCoordinates.lean`, `Geometry/SigmaAxisCoordinates.lean`, `Geometry/SpatialPivotNormalization.lean`, `Geometry/SpatialTwoBlockEquiv.lean`, `Lattices/AffineCoefficientLaw.lean`, `Lattices/AffineSampleAlphabet.lean`, `Lattices/AllocatedAffineCanonicalBackendBudget.lean`, `Lattices/AllocatedAffinePhysicalTerminalReset.lean`, `Lattices/AllocatedAffineScaleEnvelope.lean`, `Lattices/BoundedPrimeResidual.lean`, `Lattices/CertifiedAffineCutoffCost.lean`, `Lattices/IntegerRowInterpolationMixture.lean`, `Lattices/PartitionedAffineLogEnvelope.lean`, `Lattices/RefilteredResidueExpansionSpec.lean`, `Lattices/ResidueBoxSliceCoordinateDisintegration.lean`, `Lattices/ResidueCoefficientFamily.lean`, `Lattices/ResidueRefinedPeriod.lean`, `Lattices/ScalarResidueInteriorCell.lean`, `Lattices/SmoothAffinePairLaw.lean`, `Lattices/WeightedScalarResidueCell.lean`, `Linear/ActualCandidateSlowProjectionMass.lean`, `Linear/AllocatedFixedKernelReplacement.lean`, `Linear/AllocatedModularRankMixedUniform.lean`, `Linear/ExternalKernelPrecenterNativePointPartners.lean`, `Linear/FixedAdaptedSymbolFactorizationBasis.lean`, `Linear/KernelCoefficientLogBudget.lean`, `Linear/KernelJetAllowances.lean`, `Linear/KernelScalarEnvelope.lean`, `Linear/KernelScaleIndependence.lean`, `Linear/NativeMarkedKernelRepresentatives.lean`, `Linear/RationalTagProjectionComplement.lean`, `Linear/WeightedDualVector.lean`, `Nilpotent/NativeResetBracketGeometry.lean`, `Polynomial/CRTPolynomialChargeBound.lean`, `Polynomial/CRTPolynomialInputAffineLaw.lean`, `Polynomial/FullTaggedProjectionPolynomial.lean`, `Polynomial/JointPolynomialDilationGrid.lean`, `Polynomial/ProductPolynomialMaps.lean`, `Polynomial/RealPolynomialEvaluationMass.lean`, `Polynomial/RestrictedDegreeSupports.lean`, `Probability/DiagonalImageDensity.lean`, `Probability/SlicedRemainderDensityFamily.lean`, `Probability/SpatialProductDensity.lean`, `Probability/UniformSelectedCoefficientProductLaw.lean`, `Sampling/AllocatedIdealGridEnvelope.lean`, `Sampling/AveragedNormalizedTwistForecastJointModel.lean`, `Sampling/CanonicalSamplerTuple.lean`, `Sampling/ExternalNetMaskedScores.lean`, `Sampling/FixedSpatialKernelProgressionForecastIntegral.lean`, `Sampling/ForecastJointScaleNormalization.lean`, `Sampling/ForecastModularCutoff.lean`, `Sampling/ForecastNativePullbackBudget.lean`, `Sampling/MarkedKernelProjectionScoreRestoration.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.CandidateFrontSourceLossBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

def candidateFrontFamilyParameter (cap : ℝ) : ℝ := (cap + 3) ^ 4

theorem candidateFrontFamilyBounds (cap native : ℝ) (layers variableCount : ℕ)
    (hcap : 0 ≤ cap) (hnative : native ≤ cap)
    (hlayers : (layers : ℝ) ≤ cap) (hvariableCount : (variableCount : ℝ) ≤ cap) :
    0 ≤ candidateFrontFamilyParameter cap ∧
    cap ≤ candidateFrontFamilyParameter cap ∧
    2 * max native 3 ≤ candidateFrontFamilyParameter cap ∧
    Real.exp (max native 3) *
      (1 + (layers : ℝ) * (((layers + 1 : ℕ) : ℝ) *
        ((variableCount + 1 : ℕ) : ℝ) ^ layers)) ≤ Real.exp (candidateFrontFamilyParameter cap) := by
  have hbase : 1 ≤ cap + 3 := by linarith
  have hsq : (cap + 3) ^ 2 ≤ candidateFrontFamilyParameter cap :=
    pow_le_pow_right₀ hbase (by decide)
  have hcapFamily : cap ≤ candidateFrontFamilyParameter cap :=
    (by nlinarith [sq_nonneg cap] : cap ≤ (cap + 3) ^ 2).trans hsq
  have hmax : max native 3 ≤ cap + 3 := max_le (by linarith) (by linarith)
  have hperiod : 2 * max native 3 ≤ candidateFrontFamilyParameter cap :=
    (by nlinarith [sq_nonneg cap] : 2 * max native 3 ≤ (cap + 3) ^ 2).trans hsq
  have hplus : cap + 1 ≤ Real.exp cap := Real.add_one_le_exp cap
  have hLayerExp : (layers : ℝ) ≤ Real.exp cap := hlayers.trans (by linarith)
  have hLayerOneExp : ((layers + 1 : ℕ) : ℝ) ≤ Real.exp cap := by
    push_cast
    linarith
  have hVariableExp : ((variableCount + 1 : ℕ) : ℝ) ≤ Real.exp cap := by
    push_cast
    linarith
  have hpower : ((variableCount + 1 : ℕ) : ℝ) ^ layers ≤ Real.exp (cap ^ 2) := by
    calc
      _ ≤ (Real.exp cap) ^ layers := pow_le_pow_left₀ (Nat.cast_nonneg _) hVariableExp layers
      _ = Real.exp ((layers : ℝ) * cap) := (Real.exp_nat_mul cap layers).symm
      _ ≤ Real.exp (cap ^ 2) := Real.exp_le_exp.mpr (by nlinarith)
  have hproduct : (layers : ℝ) * (((layers + 1 : ℕ) : ℝ) *
      ((variableCount + 1 : ℕ) : ℝ) ^ layers) ≤ Real.exp (2 * cap + cap ^ 2) := by
    calc
      _ ≤ Real.exp cap * (Real.exp cap * Real.exp (cap ^ 2)) := by
        gcongr
      _ = Real.exp (2 * cap + cap ^ 2) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
  have hone : 1 ≤ Real.exp (2 * cap + cap ^ 2) := Real.one_le_exp (by positivity)
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hsum : 1 + (layers : ℝ) * (((layers + 1 : ℕ) : ℝ) *
      ((variableCount + 1 : ℕ) : ℝ) ^ layers) ≤ Real.exp (2 * cap + cap ^ 2 + 1) := by
    calc
      _ ≤ 2 * Real.exp (2 * cap + cap ^ 2) := by linarith
      _ ≤ Real.exp 1 * Real.exp (2 * cap + cap ^ 2) :=
        mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
      _ = Real.exp (2 * cap + cap ^ 2 + 1) := by
        rw [← Real.exp_add]
        congr 1
        ring
  refine ⟨by unfold candidateFrontFamilyParameter; positivity, hcapFamily, hperiod, ?_⟩
  calc
    _ ≤ Real.exp (max native 3) * Real.exp (2 * cap + cap ^ 2 + 1) :=
      mul_le_mul_of_nonneg_left hsum (Real.exp_nonneg _)
    _ = Real.exp (max native 3 + (2 * cap + cap ^ 2 + 1)) := (Real.exp_add _ _).symm
    _ ≤ Real.exp ((cap + 3) ^ 2) := Real.exp_le_exp.mpr (by nlinarith)
    _ ≤ Real.exp (candidateFrontFamilyParameter cap) := Real.exp_le_exp.mpr hsq

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.PrimePowerCharacterScaling
namespace OAI

section

namespace Erdos3

def zmodPiReduction {I : Type*} {n m : ℕ} (h : m ∣ n) :
    (I → ZMod n) →+ (I → ZMod m) :=
  AddMonoidHom.piMap fun _ => (ZMod.castHom h (ZMod m)).toAddMonoidHom

@[simp] theorem zmodPiReduction_apply {I : Type*} {n m : ℕ} (h : m ∣ n)
    (x : I → ZMod n) (i : I) :
    zmodPiReduction h x i = ZMod.castHom h (ZMod m) (x i) := rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueRefinedPeriod
namespace OAI

section

namespace Erdos3

open scoped Matrix

def integerResidueMatrix {I J : Type*} (A : Matrix I J ℤ) (m : ℕ) : Matrix I J (ZMod m) :=
  A.map (Int.castRingHom (ZMod m))

theorem integerResidueMatrix_eq_of_mod {I J : Type*} (A B : Matrix I J ℤ) (m : ℕ)
    (hAB : ∀ i j, A i j % (m : ℤ) = B i j % (m : ℤ)) :
    integerResidueMatrix A m = integerResidueMatrix B m := by
  ext i j
  exact (ZMod.intCast_eq_intCast_iff' (A i j) (B i j) m).mpr (hAB i j)

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

def reducedIntegerMatrix {I J : Type*} (A : Matrix I J ℤ) (M : ℕ) : Matrix I J ℤ :=
  fun i j => A i j % (M : ℤ)

theorem reducedIntegerMatrix_bounds {I J : Type*} (A : Matrix I J ℤ)
    (M : ℕ) [NeZero M] (i : I) (j : J) :
    0 ≤ reducedIntegerMatrix A M i j ∧ reducedIntegerMatrix A M i j < M := by
  have hM : (0 : ℤ) < M := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  exact ⟨Int.emod_nonneg _ hM.ne', Int.emod_lt_of_pos _ hM⟩

theorem integerResidueMatrix_reduced {I J : Type*} (A : Matrix I J ℤ) (M : ℕ) :
    integerResidueMatrix (reducedIntegerMatrix A M) M = integerResidueMatrix A M := by
  apply integerResidueMatrix_eq_of_mod
  intro i j
  exact Int.emod_emod _ _

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.CharacterCoordinateScale
namespace OAI

section

namespace Erdos3

abbrev TorsionLatticeCharacter (I : Type*) (a : ℕ) :=
  {χ : AddChar (I → ℤ) ℂ // χ ^ a = 1}

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RealPolynomialEvaluationMass
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def polynomialMonomial {K I : Type*}
    (a : K → MvPolynomial I ℝ) (m : K →₀ ℕ) : MvPolynomial I ℝ :=
  ∏ k ∈ m.support, a k ^ m k

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.BoxWindowAveraging
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

variable {ι : Type*} [Fintype ι]

noncomputable def boxWindowTranslationBound (ℓ : ι → ℝ) (hℓ : ∀ i, 0 < ℓ i) : ℝ≥0 :=
  ⟨∑ i, 2 / ℓ i, Finset.sum_nonneg (fun i _ => div_nonneg (by norm_num) (hℓ i).le)⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.DiagonalImageDensity
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

noncomputable def diagonalImageDensity (d : ι → ℝ)
    (f : (ι → ℝ) → ℝ) (x : ι → ℝ) : ℝ :=
  (∏ i, |d i|)⁻¹ * f (fun i => x i / d i)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SigmaAxisCoordinates
namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {D : Type*} [Fintype D] (I : D → Type*) [∀ d, Fintype (I d)]

noncomputable def sigmaAxisProjection (d : D) : ((Σ d, I d) → ℝ) →L[ℝ] (I d → ℝ) :=
  ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj ⟨d, i⟩)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PivotCoordinateChange
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped ENNReal

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def pivotCoordinateChange (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (B : (J → ℝ) →L[ℝ] (I → ℝ)) :
    ((J → ℝ) × (I → ℝ)) ≃ₜ ((J → ℝ) × (I → ℝ)) where
  toFun p := (p.1, A p.2 + B p.1)
  invFun p := (p.1, A.symm (p.2 - B p.1))
  left_inv p := by simp
  right_inv p := by simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProductCutoffLipschitz
namespace OAI

section

namespace Erdos3

noncomputable def progressionCellCorner {I : Type*} (N : I → ℕ) (u v : I → ℝ)
    {K : I → ℕ} (k : ∀ i, Fin (K i)) : I → ℝ :=
  fun i => u i + v i * (N i * (k i).val : ℕ)

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

noncomputable def scalarCubeCutoffLipschitzConstant (I : Type*) [Fintype I]
    (A : ℝ≥0) (r : ℝ≥0) : ℝ≥0 :=
  (2 * 2 ^ Fintype.card I : ℕ) * (A / r * (Fintype.card I + 1))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.CanonicalSamplerTuple
namespace OAI

section

namespace Erdos3

open scoped ContDiff NNReal

variable {D : Type*} [Fintype D] {I O : D → Type*}
  [∀ d, Fintype (I d)] [∀ d, Fintype (O d)]

noncomputable def sigmaAxisSampler (U : ∀ d, (I d → ℝ) → (O d → ℝ))
    (x : (Σ d, I d) → ℝ) (s : Σ d, O d) : ℝ :=
  U s.1 (sigmaAxisProjection I s.1 x) s.2

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FourSlicedProductSmoothing
namespace OAI

section

namespace Erdos3.SlicedProductBlock

open MeasureTheory
open scoped NNReal

variable {ι : Type*} [Fintype ι]

noncomputable def uniformCap (ι : Type*) [Fintype ι] (r : ℝ) (hr : 0 < r) : ℝ≥0 :=
  ⟨r⁻¹ * 4 ^ Fintype.card ι, mul_nonneg (inv_nonneg.mpr hr.le) (by positivity)⟩

end Erdos3.SlicedProductBlock

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.SpatialProductDensity
namespace OAI

section

namespace Erdos3.SlicedProductBlock

open MeasureTheory

variable {ι : Type*} [Fintype ι]

abbrev PairInput (ι : Type*) := ((ι → ℝ) × (ι → ℝ)) × (ℝ × ℝ)

abbrev FourInput (ι : Type*) := PairInput ι × PairInput ι

end Erdos3.SlicedProductBlock

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.SlicedRemainderDensityFamily
namespace OAI

section

namespace Erdos3.SlicedProductBlock

open MeasureTheory
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

def packPair (x : Fin 2 → (ι → ℝ) × ℝ) : PairInput ι :=
  (((x 0).1, (x 1).1), ((x 0).2, (x 1).2))

def packFour (x : Fin 4 → (ι → ℝ) × ℝ) : FourInput ι :=
  (packPair ![x 2, x 3], packPair ![x 0, x 1])

def fourBoxPacking (x : Fin 4 × Option ι → ℝ) : FourInput ι :=
  packFour (fun b => ((fun i => x (b, some i)), x (b, none)))

end Erdos3.SlicedProductBlock

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RawProductArrayNormalization
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {D K Z α : Type*} [Fintype α] [DecidableEq α]
  {B O L : D → Type*} [∀ d, Fintype (B d)]

def booleanConstantJet (sets : ∀ d, O d → Finset α) (constant : D → ℝ) (o : Σ d, O d) : ℝ :=
  if sets o.1 o.2 = ∅ then constant o.1 else 0

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SpatialPivotNormalization
namespace OAI

section

namespace Erdos3

open scoped Matrix

abbrev UnselectedColumn {I J : Type*} (s : I ↪ J) := {j : J // j ∉ Set.range s}

noncomputable instance unselectedColumnFintype {I J : Type*} [Fintype J] (s : I ↪ J) :
    Fintype (UnselectedColumn s) := Fintype.ofFinite _

noncomputable def selectedColumnEquiv {I J : Type*} [Fintype I] (s : I ↪ J) : I ⊕ UnselectedColumn s ≃ J := by
  classical
  exact (Equiv.sumCongr s.toEquivRange (Equiv.refl (UnselectedColumn s))).trans
    (Equiv.sumCompl (fun j => j ∈ Set.range s))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SelectedCoefficientEvaluation
namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {I J N : Type*} [Fintype I] [Fintype J] [Fintype N]

noncomputable def splitFreeProfile (f : (J → ℝ) × (I → ℝ) → ℝ)
    (g : (N → ℝ) → ℝ) (p : (J ⊕ N → ℝ) × (I → ℝ)) : ℝ :=
  f ((fun j => p.1 (.inl j)), p.2) * g (fun n => p.1 (.inr n))

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

noncomputable def selectedFreeFirstEquiv {I J : Type*} [Fintype I] (s : I ↪ J) :
    UnselectedColumn s ⊕ I ≃ J :=
  (Equiv.sumComm _ _).trans (selectedColumnEquiv s)

noncomputable def selectedCoefficientEquiv {I J : Type*} [Fintype I]
    (s : I ↪ J) (R : Type*) : (UnselectedColumn s → R) × (I → R) ≃ (J → R) :=
  (Equiv.sumPiEquivProdPi (fun _ : UnselectedColumn s ⊕ I => R)).symm.trans
    (Equiv.arrowCongr (selectedFreeFirstEquiv s) (Equiv.refl R))

noncomputable def selectedCoefficientProfile {I J : Type*} [Fintype I]
    (s : I ↪ J) (f : (J → ℝ) → ℝ) : (UnselectedColumn s → ℝ) × (I → ℝ) → ℝ :=
  f ∘ selectedCoefficientEquiv s ℝ

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.UniformSelectedCoefficientProductLaw
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

abbrev SelectedCoefficientComplement {A J : Type*} (e : A ↪ J) :=
  {j : J // j ∉ Set.range e}

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NormalizedJetColumns
namespace OAI

section

namespace Erdos3

open scoped NNReal BigOperators

noncomputable def frozenTupleCoordinate {Z P : Type*} (z : Z → ℝ) : Z ⊕ P → MvPolynomial P ℝ
  | .inl j => MvPolynomial.C (z j)
  | .inr i => MvPolynomial.X i

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SmoothAffinePairLaw
namespace OAI


namespace Erdos3

open scoped BigOperators

noncomputable def liftResidueMatrix {I N : Type*} {m : ℕ} (r : Matrix I N (ZMod m)) : Matrix I N ℤ :=
  fun i n => (ZMod.intCast_surjective (r i n)).choose

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.KernelJetAllowances
namespace OAI

section

namespace Erdos3

noncomputable def kernelJetInterpolationAllowance (q h : ℕ) (κ : ℝ) : ℝ :=
  (1 + (q : ℝ) * (2 * (q.factorial / κ))) ^ h

def kernelJetEntryAllowance (q h : ℕ) : ℝ := 2 ^ q * ((q : ℝ) + 1) ^ h

noncomputable def kernelJetMinorThreshold (q n j h : ℕ) (κ : ℝ) : ℝ :=
  1 / (((n : ℝ) + 1) ^ h * kernelJetInterpolationAllowance q h κ) ^ j

noncomputable def kernelJetInverseAllowance (q n j h : ℕ) (κ : ℝ) : ℝ :=
  (j : ℝ) * ((j.factorial * (kernelJetEntryAllowance q h) ^ (j - 1)) /
    kernelJetMinorThreshold q n j h κ)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.KernelScaleIndependence
namespace OAI


namespace Erdos3


open scoped Matrix

def remainingMatrixColumns {I J R : Type*} (A : Matrix I J R) (s : I ↪ J) :
    Matrix I (UnselectedColumn s) R := A.submatrix id Subtype.val

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientRowReindex
namespace OAI


namespace Erdos3

noncomputable def coefficientImageMultiplier {I J : Type*} [Fintype J]
    (A : Matrix I J ℤ) (v : I → ℤ) : ℝ := by
  classical
  exact if v ∈ A.mulVecLin.range then (A.mulVecLin.range.toAddSubgroup.index : ℝ) else 0

noncomputable def coefficientResidueMultiplier {I J N : Type*} [Fintype J] [Fintype N]
    (A : Matrix I J ℤ) {m : ℕ} (r : Matrix I N (ZMod m)) (v : I → ℤ) : ℝ :=
  coefficientImageMultiplier (Matrix.fromCols A (liftResidueMatrix r)) v


open MeasureTheory
open scoped BigOperators NNReal

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.CRTPolynomialChargeBound
namespace OAI


namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

noncomputable def modularRankDecayExponent (s : ℕ) (C : ℝ) : ℝ :=
  C / ((2 ^ s * s.factorial : ℕ) : ℝ) / (2 ^ s : ℕ)

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.JointPolynomialDilationGrid
namespace OAI


namespace Erdos3
open _root_.MvPolynomial
open scoped BigOperators

theorem abs_prod_sub_prod_unit_sum {ι : Type*} (S : Finset ι)
    (f g e : ι → ℝ) (he : ∀ i ∈ S, 0 ≤ e i)
    (hf : ∀ i ∈ S, |f i| ≤ 1) (hg : ∀ i ∈ S, |g i| ≤ 1)
    (hfg : ∀ i ∈ S, |f i - g i| ≤ e i) :
    |(∏ i ∈ S, f i) - ∏ i ∈ S, g i| ≤ ∑ i ∈ S, e i := by
  classical
  revert he hf hg hfg
  induction S using Finset.induction_on with
  | empty => intro _ _ _ _; simp
  | @insert a S ha ih =>
    intro he hf hg hfg
    have hrec := ih (fun i hi => he i (Finset.mem_insert_of_mem hi))
      (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      (fun i hi => hg i (Finset.mem_insert_of_mem hi))
      (fun i hi => hfg i (Finset.mem_insert_of_mem hi))
    have hprod : |∏ i ∈ S, g i| ≤ 1 := by
      rw [Finset.abs_prod]
      exact Finset.prod_le_one (fun _ _ => abs_nonneg _)
        (fun i hi => hg i (Finset.mem_insert_of_mem hi))
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
    calc
      _ = |f a * ((∏ i ∈ S, f i) - ∏ i ∈ S, g i) + (f a - g a) * ∏ i ∈ S, g i| := by
        congr 1
        ring
      _ ≤ |f a| * |(∏ i ∈ S, f i) - ∏ i ∈ S, g i| +
          |f a - g a| * |∏ i ∈ S, g i| := by
        simpa only [abs_mul] using abs_add_le
          (f a * ((∏ i ∈ S, f i) - ∏ i ∈ S, g i)) ((f a - g a) * ∏ i ∈ S, g i)
      _ ≤ 1 * (∑ i ∈ S, e i) + e a * 1 :=
        add_le_add (mul_le_mul (hf a (Finset.mem_insert_self _ _)) hrec
          (abs_nonneg _) zero_le_one)
          (mul_le_mul (hfg a (Finset.mem_insert_self _ _)) hprod
            (abs_nonneg _) (he a (Finset.mem_insert_self _ _)))
      _ = _ := by ring

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ImageCoverBudget
namespace OAI

section

namespace Erdos3

def imageLatticeLogBudget (K : ℕ) (p : ℝ) : ℝ :=
  K + (p + 2) ^ 4 + 2 * p + (p + 2) ^ 9

theorem imageLatticeLogBudget_nonneg (K : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ imageLatticeLogBudget K p := by unfold imageLatticeLogBudget; positivity

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AdaptedMarkedMapHeight
namespace OAI

section

namespace Erdos3

def adaptedMarkedMapHeightBudget (p : ℝ) : ℝ :=
  (p + (p + 4) ^ 5 + (p + 2) ^ 4 + 2) ^ 4

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AdaptedMapGeometryBudget
namespace OAI

section

namespace Erdos3

def adaptedMapGeometryBudget (p : ℝ) : ℝ :=
  (p + 3) ^ 11 + (p + 4) ^ 11 + adaptedMarkedMapHeightBudget (p + 1) + p + 2

theorem adaptedMapGeometryBudget_nonneg {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ adaptedMapGeometryBudget p := by
  unfold adaptedMapGeometryBudget adaptedMarkedMapHeightBudget
  positivity

theorem adaptedMapGeometryBudget_geometry {p : ℝ} (hp : 0 ≤ p) :
    (p + 3) ^ 11 ≤ adaptedMapGeometryBudget p := by
  have hinverse : 0 ≤ (p + 4) ^ 11 := by positivity
  have hmap : 0 ≤ adaptedMarkedMapHeightBudget (p + 1) := by
    unfold adaptedMarkedMapHeightBudget
    positivity
  unfold adaptedMapGeometryBudget
  linarith

theorem adaptedMapGeometryBudget_inverse {p : ℝ} (hp : 0 ≤ p) :
    (p + 4) ^ 11 ≤ adaptedMapGeometryBudget p := by
  have hgeometry : 0 ≤ (p + 3) ^ 11 := by positivity
  have hmap : 0 ≤ adaptedMarkedMapHeightBudget (p + 1) := by
    unfold adaptedMarkedMapHeightBudget
    positivity
  unfold adaptedMapGeometryBudget
  linarith

theorem adaptedMapGeometryBudget_markedMap {p : ℝ} (hp : 0 ≤ p) :
    adaptedMarkedMapHeightBudget (p + 1) ≤ adaptedMapGeometryBudget p := by
  have hgeometry : 0 ≤ (p + 3) ^ 11 := by positivity
  have hinverse : 0 ≤ (p + 4) ^ 11 := by positivity
  unfold adaptedMapGeometryBudget
  linarith

theorem adaptedMapGeometryBudget_parameter {p : ℝ} (hp : 0 ≤ p) :
    p + 2 ≤ adaptedMapGeometryBudget p := by
  have hgeometry : 0 ≤ (p + 3) ^ 11 := by positivity
  have hinverse : 0 ≤ (p + 4) ^ 11 := by positivity
  have hmap : 0 ≤ adaptedMarkedMapHeightBudget (p + 1) := by
    unfold adaptedMarkedMapHeightBudget
    positivity
  unfold adaptedMapGeometryBudget
  linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RepresentativeWindowPatch
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem bounded_weight_cutoff_lipschitz {E : Type*} [PseudoMetricSpace E]
    (w b : E → ℝ) {B K Q : ℝ≥0} (hw : ∀ x, |w x| ≤ B)
    (hb : ∀ x, |b x| ≤ 1) (hwl : LipschitzWith K w) (hbl : LipschitzWith Q b) :
    LipschitzWith (K + B * Q) (fun x => w x * b x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq]
  have hwxy := hwl.dist_le_mul x y
  have hbxy := hbl.dist_le_mul x y
  rw [Real.dist_eq] at hwxy hbxy
  calc
    _ = |(w x - w y) * b x + w y * (b x - b y)| := by congr 1; ring
    _ ≤ |(w x - w y) * b x| + |w y * (b x - b y)| := abs_add_le _ _
    _ ≤ (K : ℝ) * dist x y * 1 + B * ((Q : ℝ) * dist x y) := by
      simp only [abs_mul]
      exact add_le_add (mul_le_mul hwxy (hb x) (abs_nonneg _) (by positivity))
        (mul_le_mul (hw y) hbxy (abs_nonneg _) B.coe_nonneg)
    _ = _ := by simp only [NNReal.coe_add, NNReal.coe_mul]; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.NativeParameterCoverBudget
namespace OAI

section

namespace Erdos3

open scoped NNReal

noncomputable def externalNetMesh (L : ℝ≥0) (ε : ℝ) : ℝ := ε / (3 * (L + 1))

theorem externalNetMesh_pos (L : ℝ≥0) {ε : ℝ} (hε : 0 < ε) : 0 < externalNetMesh L ε := by
  unfold externalNetMesh
  positivity

theorem externalNetMesh_error (L M : ℝ≥0) {ε : ℝ} (hε : 0 ≤ ε) :
    ε / 3 + M * externalNetMesh M ε + L * externalNetMesh L ε ≤ ε := by
  have hterm (K : ℝ≥0) : K * externalNetMesh K ε ≤ ε / 3 := by
    unfold externalNetMesh
    rw [← mul_div_assoc, div_le_iff₀ (by positivity : (0 : ℝ) < 3 * (K + 1))]
    nlinarith [K.coe_nonneg]
  linarith [hterm M, hterm L]

theorem externalNetMesh_inverse_bound (L : ℝ≥0) {ε p : ℝ}
    (hε : 0 < ε) (hp : 0 ≤ p) (hL : (L : ℝ) ≤ Real.exp p) (hinv : 1 / ε ≤ Real.exp p) :
    1 / externalNetMesh L ε ≤ Real.exp (2 * p + 7) := by
  have hone : 1 ≤ Real.exp p := Real.one_le_exp hp
  have hseven : (6 : ℝ) ≤ Real.exp 7 := by linarith [Real.add_one_le_exp (7 : ℝ)]
  calc
    1 / externalNetMesh L ε = 3 * (L + 1) * (1 / ε) := by unfold externalNetMesh; field_simp
    _ ≤ 3 * (Real.exp p + Real.exp p) * Real.exp p := by gcongr
    _ = 6 * Real.exp (2 * p) := by rw [two_mul, Real.exp_add]; ring
    _ ≤ Real.exp 7 * Real.exp (2 * p) := mul_le_mul_of_nonneg_right hseven (Real.exp_nonneg _)
    _ = Real.exp (2 * p + 7) := by rw [← Real.exp_add, add_comm]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.McShaneEnvelope
namespace OAI

section

namespace Erdos3

open scoped NNReal

variable {X Y : Type*} [Nonempty X] [PseudoMetricSpace Y]
  (φ : X → Y) (L : ℝ≥0)

omit [Nonempty X] in
theorem mcShaneEnvelope_bddBelow (f : X → ℝ) (hf : ∀ x, 0 ≤ f x) (y : Y) :
    BddBelow (Set.range (fun x => f x + L * dist y (φ x))) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact add_nonneg (hf x) (mul_nonneg L.coe_nonneg dist_nonneg)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.WeightedDualVector
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]

omit [Nonempty Ω] in
theorem functional_eq_sum_coordinates (f : (Ω → ℂ) →ₗ[ℂ] ℂ) (v : Ω → ℂ) :
    f v = ∑ x, v x * f (Pi.single x 1) := by
  calc
    _ = f (∑ x, Pi.single x (v x)) := by rw [Finset.univ_sum_single]
    _ = ∑ x, f (Pi.single x (v x)) := map_sum f _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      have h : Pi.single x (v x) = v x • Pi.single x (1 : ℂ) := by
        ext y
        by_cases hy : y = x <;> simp [hy]
      rw [h, map_smul, smul_eq_mul]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineCoefficientLaw
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators ContDiff

noncomputable def profileWidthFactor {I : Type*} [Fintype I] (w : I → ℝ) : ℝ :=
  ∏ i, (w i)⁻¹

theorem profileWidthFactor_pos {I : Type*} [Fintype I] (w : I → ℝ) (hw : ∀ i, 0 < w i) :
    0 < profileWidthFactor w := Finset.prod_pos (fun i _ => inv_pos.mpr (hw i))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.InactiveShortLogBounds
namespace OAI

section

namespace Erdos3

noncomputable def coefficientReplacementErrorLog {A : Type*} [Semiring A] (D L : A) : A :=
  3 * (D + 1) * (L + 3)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerRowInterpolationMixture
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem affineProfile_sample_coordinate (c x : ℝ) {w S : ℝ} (hw : 0 < w) (hS : 0 < S) :
    (x / S - c) / w = (x - c*S) / (w*S) := by
  field_simp [hw.ne', hS.ne']

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AmplificationFinalCostGrowth
namespace OAI

section

open Filter

namespace Erdos3

def amplificationGain (κ H₀ : ℝ) : ℕ → ℝ
  | 0 => H₀
  | j + 1 => κ * amplificationGain κ H₀ j ^ 2

end Erdos3

end

section

namespace Erdos3

noncomputable def levelCoefficient (K : ℝ) : ℝ := 1 / (4 * Real.log K)

noncomputable def gainExponent (K : ℝ) : ℝ := levelCoefficient K * Real.log 2

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastModularCutoff
namespace OAI

section

namespace Erdos3

noncomputable def forecastJointGridError
    (dout dj dc cutoff : ℕ) (D L C K δ : ℝ) : ℝ :=
  (((cutoff : ℝ) ^ (dout + 1) * (2 * (8 : ℝ) ^ dj * (L + C * K) * δ) +
    (D / cutoff) * ((8 : ℝ) ^ dj * L * δ)) * (6 : ℝ) ^ dc) + 2 * (D / cutoff)

noncomputable def forecastJointGridMeshLog (d : ℕ) (P E : ℝ) : ℝ :=
  ((d : ℝ) + 1) * (P + E + 5) + 6 * d + 2 * P + E + 8

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ScalarResidueInteriorCell
namespace OAI

section

namespace Erdos3

noncomputable def residueCellLength (δ : ℝ) (L M : ℕ) : ℕ := ⌊δ * L / M⌋₊

end Erdos3

end

section

namespace Erdos3

noncomputable def paddedResidueOffset {I : Type*} (L : ℕ) (m : Option I → ℕ)
    (r : ∀ i, ZMod (m i)) : Option I → ℝ :=
  fun i => ((r i).val - (m i : ℝ) * L) / L

noncomputable def paddedResidueStep {I : Type*} (L : ℕ) (m : Option I → ℕ) : Option I → ℝ :=
  fun i => (m i : ℝ) / L

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ScalarCubeProductRiemannBudget
namespace OAI

section

namespace Erdos3
open MeasureTheory

def scalarCubeRiemannLog {A : Type*} [Semiring A] (D : A) : A :=
  (D + 1) ^ 2 + 4 * D + 2

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators

def progressionSliceLengthLog {A : Type*} [Semiring A] (D E F T : A) : A :=
  E + F + T + D + scalarCubeRiemannLog D + 5

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.WeightedScalarResidueCell
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

noncomputable def residueCellPosition {I : Type*} (L N K : ℕ)
    (m : Option I → ℕ) (res : ∀ i, ZMod (m i))
    (k : Option I → Fin K) (t : Option I → Fin N) : Option I → ℝ :=
  fun i => progressionCellCorner (fun _ => N) (paddedResidueOffset L m res)
    (paddedResidueStep L m) k i + paddedResidueStep L m i * (t i).val

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.JetOutputRadiusLogBudget
namespace OAI

section

namespace Erdos3

open scoped NNReal

def jetOutputRadiusLog (q n d : ℕ) (P : ℝ) : ℝ := 4*P+n+q+(d : ℝ)*q+2

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueCoefficientFamily
namespace OAI

section

namespace Erdos3

open scoped NNReal

noncomputable def coefficientLogAllowance (j d : ℕ) (b : ℝ) : ℝ :=
  2*(j : ℝ)^2 + (2*j+4)*b + (j+2*d)*(b+4) + 4

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueBoxSliceCoordinateDisintegration
namespace OAI

section

namespace Erdos3.ResidueBoxSlice

open scoped BigOperators Classical

variable {K : Type*} (oldKeep keep : K → Prop)

noncomputable def axisInsertion
    (fixed : {i : {i // oldKeep i} // ¬keep i.val} → ℤ)
    (u : {i // keep i} → ℤ) : {i // oldKeep i} → ℤ :=
  fun i => if hi : keep i.val then u ⟨i.val, hi⟩ else fixed ⟨i, hi⟩

end Erdos3.ResidueBoxSlice

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealifiedTopQuotient
namespace OAI

section

namespace Erdos3

open Module

def quotientInducedMapHeightBudget (p : ℝ) : ℝ :=
  let q := p + (p + 3) ^ 7 + 1
  ((q + 2) ^ 4 + q + 2) ^ 4

end Erdos3

end

section

namespace Erdos3
open Module

noncomputable def quotientInducedMarkHeightBudget (p : ℝ) : ℝ :=
  (p + (p + 3) ^ 7 + 3) ^ 4

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.OptionProductMetric
namespace OAI

section

namespace Erdos3

theorem piOptionEquivProd_isometry {ι : Type*} [Fintype ι] {X : Option ι → Type*}
    [∀ i, PseudoMetricSpace (X i)] :
    Isometry (Equiv.piOptionEquivProd : (∀ i, X i) → X none × (∀ i, X (some i))) := by
  apply Isometry.of_dist_eq
  intro x y
  change dist (x none, fun i => x (some i)) (y none, fun i => y (some i)) = dist x y
  rw [Prod.dist_eq]
  apply le_antisymm
  · apply max_le (dist_le_pi_dist x y none)
    exact (dist_pi_le_iff dist_nonneg).mpr (fun i => dist_le_pi_dist x y (some i))
  · apply (dist_pi_le_iff (le_trans dist_nonneg (le_max_left _ _))).mpr
    intro i
    cases i with
    | none => exact le_max_left _ _
    | some i => exact (dist_le_pi_dist (fun i => x (some i)) (fun i => y (some i)) i).trans (le_max_right _ _)

noncomputable def optionPiIsometryEquiv {ι : Type*} [Fintype ι] {X : Option ι → Type*}
    [∀ i, PseudoMetricSpace (X i)] : (∀ i, X i) ≃ᵢ X none × (∀ i, X (some i)) where
  toEquiv := Equiv.piOptionEquivProd
  isometry_toFun := piOptionEquivProd_isometry

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UniformFamilyMemberNet
namespace OAI

section

namespace Erdos3
open scoped NNReal

theorem exists_uniform_family_member_net {X Y I : Type*} [Nonempty X]
    (F : X → Y → ℂ) (centers : I → Y → ℂ) {ε : ℝ}
    (hnet : ∀ x, ∃ i, ∀ y, ‖F x y - centers i y‖ ≤ ε) :
    ∃ rep : I → X, ∀ x, ∃ i, ∀ y, ‖F x y - F (rep i) y‖ ≤ 2 * ε := by
  classical
  let occupied (i : I) : Prop := ∃ x, ∀ y, ‖F x y - centers i y‖ ≤ ε
  let rep (i : I) : X := if h : occupied i then h.choose else Classical.choice inferInstance
  have hrep (i : I) (hi : occupied i) : ∀ y, ‖F (rep i) y - centers i y‖ ≤ ε := by
    simp only [rep, dif_pos hi]
    exact hi.choose_spec
  refine ⟨rep, ?_⟩
  intro x
  obtain ⟨i, hi⟩ := hnet x
  refine ⟨i, fun y => ?_⟩
  calc
    ‖F x y - F (rep i) y‖ ≤ ‖F x y - centers i y‖ + ‖centers i y - F (rep i) y‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ε + ε := add_le_add (hi y) (by
      rw [norm_sub_rev]
      exact hrep i ⟨x, hi⟩ y)
    _ = 2 * ε := by ring

theorem exists_uniform_family_member_net_half {X Y I : Type*} [Nonempty X]
    (F : X → Y → ℂ) (centers : I → Y → ℂ) {ε : ℝ}
    (hnet : ∀ x, ∃ i, ∀ y, ‖F x y - centers i y‖ ≤ ε / 2) :
    ∃ rep : I → X, ∀ x, ∃ i, ∀ y, ‖F x y - F (rep i) y‖ ≤ ε := by
  simpa only [mul_div_cancel₀ _ (show (2 : ℝ) ≠ 0 by norm_num)] using
    exists_uniform_family_member_net F centers hnet

end Erdos3

end

section

namespace Erdos3

theorem uniformFamilyMemberNet_half_log_budget (E : ℕ) {p ε : ℝ}
    (hp : 0 ≤ p) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (p + Real.log (1 / (ε / 2)) + E) ^ E ≤
      (p + Real.log (1 / ε) + (E + 2 : ℕ)) ^ (E + 2) := by
  have hrecip : 1 ≤ 1 / ε := (le_div_iff₀ hε).mpr (by simpa using hε1)
  have hlogε : 0 ≤ Real.log (1 / ε) := Real.log_nonneg hrecip
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog2le : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hratio : 1 / (ε / 2) = (1 / ε) * 2 := by field_simp
  rw [hratio, Real.log_mul (by positivity) (by norm_num)]
  have hbase : 1 ≤ p + Real.log (1 / ε) + (E + 2 : ℕ) := by
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) E]
  apply (pow_le_pow_left₀ (by positivity)
    (show p + (Real.log (1 / ε) + Real.log 2) + (E : ℝ) ≤
      p + Real.log (1 / ε) + (E + 2 : ℕ) by push_cast; linarith) E).trans
  exact pow_le_pow_right₀ hbase (by omega)

theorem exists_uniform_family_member_net_of_polynomial_log
    {O Y : Type*} [Nonempty O] (F : O → Y → ℂ) {p : ℝ} (hp : 0 ≤ p) (E : ℕ)
    (hnet : ∀ η : ℝ, 0 < η → η ≤ 1 → ∃ n : ℕ,
      (n : ℝ) ≤ Real.exp ((p + Real.log (1 / η) + E) ^ E) ∧
      ∃ centers : Fin n → Y → ℂ, ∀ o, ∃ i, ∀ y, ‖F o y - centers i y‖ ≤ η)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ n : ℕ, (n : ℝ) ≤ Real.exp
      ((p + Real.log (1 / ε) + (E + 2 : ℕ)) ^ (E + 2)) ∧
      ∃ rep : Fin n → O, ∀ o, ∃ i, ∀ y, ‖F o y - F (rep i) y‖ ≤ ε := by
  obtain ⟨n, hn, centers, hcenters⟩ := hnet (ε / 2) (by positivity) (by linarith)
  obtain ⟨rep, hrep⟩ := exists_uniform_family_member_net_half F centers hcenters
  exact ⟨n, hn.trans (Real.exp_le_exp.mpr
    (uniformFamilyMemberNet_half_log_budget E hp hε hε1)), rep, hrep⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ExternalNetMaskedScores
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def externalNetIndex {X Y I : Type*}
    (F : X → Y → ℂ) (centers : I → Y → ℂ) {ε : ℝ}
    (hnet : ∀ x, ∃ i, ∀ y, ‖F x y - centers i y‖ ≤ ε) : X → I :=
  fun x => Classical.choose (hnet x)

theorem externalNetIndex_approx {X Y I : Type*}
    (F : X → Y → ℂ) (centers : I → Y → ℂ) {ε : ℝ}
    (hnet : ∀ x, ∃ i, ∀ y, ‖F x y - centers i y‖ ≤ ε) (x : X) (y : Y) :
    ‖F x y - centers (externalNetIndex F centers hnet x) y‖ ≤ ε :=
  Classical.choose_spec (hnet x) y

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RestrictedDegreeSupports
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable (I : Type*) [Fintype I] [DecidableEq I]

def lowDegreeCoordinateSets (b : ℕ) : Finset (Finset I) :=
  (Finset.range (b + 1)).biUnion (fun j => Finset.powersetCard j Finset.univ)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.MarkedKernelProjectionScoreRestoration
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {Ω Λ : Type*} [Fintype Ω] [MeasurableSpace Λ]

theorem integral_threshold_indicator_lower
    (μ : Measure Λ) [IsProbabilityMeasure μ] {f : Λ → ℝ} {B δ : ℝ}
    (hB : 0 < B) (hδ : 0 < δ) (hf : Measurable f) (hi : Integrable f μ)
    (hcap : ∀ l, f l ≤ B) (havg : δ ≤ ∫ l, f l ∂μ) :
    δ / (2 * B) ≤ ∫ l, {l | δ / 2 ≤ f l}.indicator (fun _ => (1 : ℝ)) l ∂μ := by
  let E : Set Λ := {l | δ / 2 ≤ f l}
  have hE : MeasurableSet E := measurableSet_le measurable_const hf
  have hg : Integrable (E.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const 1).indicator hE
  have hpoint : ∀ l, f l ≤ δ / 2 + B * E.indicator (fun _ => (1 : ℝ)) l := by
    intro l
    by_cases hl : l ∈ E
    · simp only [Set.indicator_of_mem hl]
      linarith [hcap l]
    · have hl' : f l < δ / 2 := lt_of_not_ge hl
      simp only [Set.indicator_of_notMem hl, mul_zero, add_zero]
      exact hl'.le
  have hbound := integral_mono hi ((integrable_const (δ / 2)).add (hg.const_mul B))
    hpoint
  change (∫ l, f l ∂μ) ≤ ∫ l, δ / 2 + B * E.indicator (fun _ => (1 : ℝ)) l ∂μ at hbound
  rw [integral_add (integrable_const (δ / 2)) (hg.const_mul B),
    integral_const_mul] at hbound
  simp only [integral_const, probReal_univ, one_smul] at hbound
  apply (div_le_iff₀ (by positivity : 0 < 2 * B)).2
  dsimp only [E] at hbound
  nlinarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeOptionFixedSourceQuotientMarkStrong
namespace OAI

section

universe u v

namespace Erdos3.RationalFilteredNilmanifold

open Module

noncomputable def nativeOptionFixedSourceQuotientMarkInput (p : ℝ) : ℝ :=
  (p + 3) ^ 2 + quotientInducedMarkHeightBudget p

theorem nativeOptionFixedSourceQuotientMarkInput_bounds {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ nativeOptionFixedSourceQuotientMarkInput p ∧
    (p + 3) ^ 2 ≤ nativeOptionFixedSourceQuotientMarkInput p ∧
    quotientInducedMarkHeightBudget p ≤ nativeOptionFixedSourceQuotientMarkInput p := by
  have hinduced : 0 ≤ quotientInducedMarkHeightBudget p := by
    unfold quotientInducedMarkHeightBudget
    positivity
  have hjoint : 0 ≤ (p + 3) ^ 2 := sq_nonneg _
  dsimp [nativeOptionFixedSourceQuotientMarkInput]
  constructor
  · exact add_nonneg hjoint hinduced
  constructor <;> linarith

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeOrbitFreezing
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem complex_expect_error_le {X : Type*} (A : Finset X) (f g : X → ℂ)
    {η : ℝ} (hη : 0 ≤ η) (herr : ∀ x ∈ A, ‖f x - g x‖ ≤ η) :
    ‖(𝔼 x ∈ A, f x) - (𝔼 x ∈ A, g x)‖ ≤ η := by
  rw [← Finset.expect_sub_distrib]
  by_cases hA : A.Nonempty
  · exact (RCLike.norm_expect_le (K := ℂ)).trans
      ((Finset.expect_le_expect herr).trans_eq (Finset.expect_const hA η))
  · have he := Finset.not_nonempty_iff_eq_empty.mp hA
    simpa only [he, Finset.expect_empty, norm_zero] using hη

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedModularProductivityPrecision
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def positiveProjectionAccuracy (p : ℝ) : ℝ := Real.exp (-(2 * p + 4))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PartitionedIdealSupport
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

noncomputable def partitionedIdealRadius (α : Type*) [Fintype α] (degree : ℕ) : ℝ :=
  1 / 4 + 2 ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ degree

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PartitionedRegularizationBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem dependentAxis_card_split {D : Type*} [Fintype D] (V : D → Type*)
    [∀ d, Fintype (V d)] (P : D → Prop) [DecidablePred P] :
    Fintype.card (Σ d : {d // P d}, V d.val) +
      Fintype.card (Σ d : {d // ¬P d}, V d.val) = Fintype.card (Σ d, V d) := by
  simp only [Fintype.card_sigma]
  exact Fintype.sum_subtype_add_sum_subtype P (fun d => Fintype.card (V d))

theorem dependentAxis_card_restrict_le {D : Type*} [Fintype D] (V : D → Type*)
    [∀ d, Fintype (V d)] (P : D → Prop) [DecidablePred P] :
    Fintype.card (Σ d : {d // P d}, V d.val) ≤ Fintype.card (Σ d, V d) := by
  have he := dependentAxis_card_split V P
  omega

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RationalModelCoordinates
namespace OAI

section

namespace Erdos3

open Module

abbrev RationalModelCoordinateIndex (s d : ℕ) :=
  (Fin d × Fin d × Fin d) ⊕ (Fin (s + 1) × Fin d × Fin d)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeSampleModelFamily
namespace OAI

section

open scoped TensorProduct BigOperators

namespace Erdos3.RationalFilteredNilmanifold

variable {ι σ : Type*}
  {L : ι → Type*}
  [∀ i, LieRing (L i)]
  [∀ i, LieAlgebra ℚ (L i)]
  {s : ℕ}
  {d : ι → ℕ}
  [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)]
  [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)]
  [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  {w : σ → ℕ}

noncomputable def selectedOrbitFrequencies (eta : ∀ i, L i →ₗ[ℚ] ℚ)
    (active : Finset ι) (i : ι) : L i →ₗ[ℚ] ℚ := by
  classical
  exact if i ∈ active then eta i else 0

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.LieSubalgebraRepresentativeBudget
namespace OAI

section

namespace Erdos3
open Module
open scoped Matrix

noncomputable def lieSubalgebraRepresentativeParameter (p : ℝ) : ℝ := (p + 2) ^ 12

variable {ι κ L : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] [LieRing L] [LieAlgebra ℚ L]

theorem lieSubalgebraRepresentativeParameter_pos {p : ℝ} (hp : 0 ≤ p) :
    0 < lieSubalgebraRepresentativeParameter p := by
  unfold lieSubalgebraRepresentativeParameter
  positivity

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.NativeMarkedKernelRepresentatives
namespace OAI

section

namespace Erdos3

open Module

noncomputable def markedKernelCommonHeight (p : ℝ) : ℕ :=
  ⌈Real.exp ((p + 3) ^ 7)⌉₊

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.RefilteredResidueExpansionSpec
namespace OAI

section

namespace Erdos3

theorem exists_residue_class_right_lattice_factors {σ G : Type*} [Group G]
    (Γ : Subgroup G) (f : (σ → ℤ) → G) (M : ℕ) (P : G → Prop)
    (hperiod : ∀ x y : σ → ℤ, (∀ j, (M : ℤ) ∣ x j - y j) →
      (QuotientGroup.mk (f x) : G ⧸ Γ) = QuotientGroup.mk (f y))
    (hrep : ∀ x : σ → ℤ, ∃ r : G, P r ∧ ∃ γ ∈ Γ, f x = r * γ) :
    ∃ r : (σ → ZMod M) → G,
      (∀ c, P (r c)) ∧
      ∀ x : σ → ℤ, ∃ γ ∈ Γ,
        f x = r (fun j => (x j : ZMod M)) * γ := by
  classical
  let lift : (σ → ZMod M) → σ → ℤ :=
    fun c j => Classical.choose (ZMod.intCast_surjective (c j))
  have hlift (c : σ → ZMod M) (j : σ) : (lift c j : ZMod M) = c j :=
    Classical.choose_spec (ZMod.intCast_surjective (c j))
  choose r hr γ hγ heq using fun c => hrep (lift c)
  refine ⟨r, hr, ?_⟩
  intro x
  let c := fun j => (x j : ZMod M)
  have hxy (j : σ) : (M : ℤ) ∣ x j - lift c j :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub (lift c j) (x j) M).mp (hlift c j)
  have hR : (QuotientGroup.mk (f x) : G ⧸ Γ) = QuotientGroup.mk (r c) := by
    apply (hperiod x (lift c) hxy).trans
    rw [heq c]
    exact QuotientGroup.mk_mul_of_mem _ (hγ c)
  refine ⟨(r c)⁻¹ * f x, QuotientGroup.eq.mp hR.symm, ?_⟩
  change f x = r c * ((r c)⁻¹ * f x)
  group

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FixedAdaptedSymbolFactorizationBasis
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

def fixedAdaptedSymbolTransferInput (p q : ℝ) : ℝ :=
  ((p + 3) ^ 5 + q + 1 + 2) ^ 4 + q + 1

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ProductPolynomialMaps
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial
open scoped TensorProduct

namespace RationalFilteredNilmanifold

variable {ι κ : Type*}
  [Fintype ι]
  [Fintype κ]
  {L : ι → Type*}
  [∀ i, LieRing (L i)]
  [∀ i, LieAlgebra ℚ (L i)]
  {s : ℕ}
  {d : ι → ℕ}
  (f : κ → ι)

noncomputable def productRestrictionIndex
    (k : Fin (Fintype.card (Σ j : κ, Fin (d (f j))))) :
    Fin (Fintype.card (Σ i, Fin (d i))) :=
  let z := (Fintype.equivFin (Σ j : κ, Fin (d (f j)))).symm k
  Fintype.equivFin (Σ i, Fin (d i)) ⟨f z.1, z.2⟩

end RationalFilteredNilmanifold
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.KernelCoefficientLogBudget
namespace OAI

section

namespace Erdos3

open scoped NNReal

def kernelInverseLog (q n j d : ℕ) (p : ℝ) : ℝ :=
  (j : ℝ) + (j : ℝ)^2 + (j - 1 : ℕ) * ((q : ℝ) * (d + 1)) +
    j * (d * n + d * ((q : ℝ)^2 + q + p + 2))

def kernelGeometryLog (q n j k d : ℕ) (p : ℝ) : ℝ :=
  p + j + k + (q : ℝ) * (d + 1) + kernelInverseLog q n j d p

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedFixedKernelReplacement
namespace OAI

section

namespace Erdos3

def layerKernelIndexBound (m B : ℕ) : ℕ := B^(m*2^(m+1))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix

noncomputable def allocatedKernelLog (G α : Type*) [Fintype G] [Fintype α]
    {m : ℕ} (O : Fin m → Type*) [∀ j, Fintype (O j)] (P : ℝ) : ℝ :=
  P + (m*2^(m+1) : ℕ)*P + (Fintype.card α : ℝ)*(m+1) +
    ∑ j, kernelInverseLog (Fintype.card α) (Fintype.card G) (Fintype.card (O j)) (j.val+1) P

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.KernelScalarEnvelope
namespace OAI

section

namespace Erdos3

def kernelInverseEnvelope {A : Type*} [Semiring A] (D p : A) : A :=
  D + D^2 + D*(D*(D+1)) + D*(D*D+D*(D^2+D+p+2))

def kernelGeometryEnvelope {A : Type*} [Semiring A] (D p : A) : A :=
  p+D+D+D*(D+1)+kernelInverseEnvelope D p

def kernelOutputEnvelope {A : Type*} [Semiring A] (D p : A) : A :=
  D^2+(D+1)*kernelGeometryEnvelope D p+(D+D+(D+1)*p)+
    D*(kernelGeometryEnvelope D p+1)+
    (4*kernelGeometryEnvelope D p+D+D+D*D+2)+1

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedProfileDimensions
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ}

variable {α : Type*} [Fintype α] {O : Fin m → Type*} [∀ j, Fintype (O j)] {D : ℝ}

section Envelopes

variable {A : Type*} [Semiring A]

def allocatedKernelEnvelope (m : ℕ) (D p : A) : A :=
  p+(m*2^(m+1) : ℕ)*p+D*(m+1)+m*kernelInverseEnvelope D p

def allocatedDensityEnvelope (m : ℕ) (D p : A) : A :=
  1+m*kernelOutputEnvelope D (4*(p+8))+p+m*(D+3*D*D+D*(D+1))

def allocatedSupportEnvelope (m : ℕ) (D p : A) : A :=
  allocatedDensityEnvelope m D p+p+m*(D+D*(D+1))

def allocatedFrontEnvelope (m : ℕ) (D p e : A) : A :=
  let C := allocatedKernelEnvelope m D p+D+(D+D+(D+1)*(4*(p+8)))
  2*D^2+(2*D+4)*C+(D+2*D)*(C+4)+4+e+1

end Envelopes

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedIdealGridEnvelope
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal

section Envelopes

variable {A : Type*} [Semiring A]

def allocatedIdealLipEnvelope (D p e : A) : A :=
  D * p + 2 * D + (D + 1) * e + p

end Envelopes

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeIteratedDifferencing
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem mean_mul_error_le_separate {X : Type*} [Fintype X]
    (u v U V : X → ℂ) {B ε δ : ℝ} (hB : 0 ≤ B)
    (hv : ∀ x, ‖v x‖ ≤ 1) (hU : ∀ x, ‖U x‖ ≤ B)
    (huerr : (𝔼 x, ‖u x - U x‖) ≤ ε) (hverr : (𝔼 x, ‖v x - V x‖) ≤ δ) :
    (𝔼 x, ‖u x * v x - U x * V x‖) ≤ ε + B * δ := by
  have hpoint (x : X) :
      ‖u x * v x - U x * V x‖ ≤ ‖u x - U x‖ + B * ‖v x - V x‖ := by
    calc
      _ = ‖(u x - U x) * v x + U x * (v x - V x)‖ := by congr 1; ring
      _ ≤ ‖u x - U x‖ * ‖v x‖ + ‖U x‖ * ‖v x - V x‖ := by
        simpa only [norm_mul] using norm_add_le ((u x - U x) * v x) (U x * (v x - V x))
      _ ≤ _ := add_le_add (mul_le_of_le_one_right (norm_nonneg _) (hv x))
        (mul_le_mul_of_nonneg_right (hU x) (norm_nonneg _))
  calc
    _ ≤ 𝔼 x, (‖u x - U x‖ + B * ‖v x - V x‖) :=
      Finset.expect_le_expect (fun x _ => hpoint x)
    _ = (𝔼 x, ‖u x - U x‖) + B * (𝔼 x, ‖v x - V x‖) := by
      rw [Finset.expect_add_distrib, ← Finset.mul_expect]
    _ ≤ _ := add_le_add huerr (mul_le_mul_of_nonneg_left hverr hB)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedFiniteForwardTreeStorage
namespace OAI

section

namespace Erdos3.VectorPolynomial

def allocatedCandidateForwardControlInput (s d : ℕ) (b : ℝ) : ℝ :=
  ((s : ℝ) + 3) * ((d : ℝ) + 1) * (b + 1)

theorem allocatedCandidateForwardControlInput_bounds (s d : ℕ) {b : ℝ}
    (hb : 0 ≤ b) :
    0 ≤ allocatedCandidateForwardControlInput s d b ∧
    b ≤ allocatedCandidateForwardControlInput s d b ∧
    3 * b ≤ allocatedCandidateForwardControlInput s d b := by
  have hs : (0 : ℝ) ≤ s := Nat.cast_nonneg _
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have hfactor : 3 ≤ ((s : ℝ) + 3) * ((d : ℝ) + 1) := by
    nlinarith only [hs, hd, mul_nonneg hs hd]
  have hthree : 3 * b ≤ allocatedCandidateForwardControlInput s d b := by
    calc
      3 * b ≤ (((s : ℝ) + 3) * ((d : ℝ) + 1)) * b :=
        mul_le_mul_of_nonneg_right hfactor hb
      _ ≤ (((s : ℝ) + 3) * ((d : ℝ) + 1)) * (b + 1) :=
        mul_le_mul_of_nonneg_left (by linarith only) (by positivity)
      _ = allocatedCandidateForwardControlInput s d b := rfl
  have hbthree : b ≤ 3 * b := by linarith only [hb]
  exact ⟨(mul_nonneg (by norm_num) hb).trans hthree, hbthree.trans hthree, hthree⟩

theorem allocatedCandidateForwardControlInput_power_bound
    (s d C A : ℕ) {b : ℝ} (hb : 0 ≤ b) (hd : (d : ℝ) ≤ b)
    (hA : 2 ≤ A) (hsA : s + 3 ≤ A) (hCA : 4 * C ≤ A) :
    (allocatedCandidateForwardControlInput s d b + C) ^ C ≤ (b + A) ^ A := by
  let K : ℝ := b + A
  have hKtwo : 2 ≤ K := by
    have hAreal : (2 : ℝ) ≤ A := Nat.cast_le.mpr hA
    dsimp only [K]
    linarith only [hb, hAreal]
  have hK : 0 ≤ K := by linarith only [hKtwo]
  have hsK : (s : ℝ) + 3 ≤ K := by
    have hsreal : (s : ℝ) + 3 ≤ A := by exact_mod_cast hsA
    dsimp only [K]
    linarith only [hb, hsreal]
  have hdK : (d : ℝ) + 1 ≤ K := by
    have hAreal : (2 : ℝ) ≤ A := Nat.cast_le.mpr hA
    dsimp only [K]
    linarith only [hd, hAreal]
  have hbK : b + 1 ≤ K := by
    have hAreal : (2 : ℝ) ≤ A := Nat.cast_le.mpr hA
    dsimp only [K]
    linarith only [hAreal]
  have hinput : allocatedCandidateForwardControlInput s d b ≤ K ^ 3 := by
    unfold allocatedCandidateForwardControlInput
    calc
      _ ≤ (K * K) * K :=
        mul_le_mul (mul_le_mul hsK hdK (by positivity) hK) hbK (by positivity)
          (mul_nonneg hK hK)
      _ = K ^ 3 := by ring
  have hCK : (C : ℝ) ≤ K := by
    have hCnat : C ≤ A := by omega
    have hCreal : (C : ℝ) ≤ A := Nat.cast_le.mpr hCnat
    dsimp only [K]
    linarith only [hb, hCreal]
  have hKcube : K ≤ K ^ 3 := by
    simpa only [pow_one] using pow_le_pow_right₀ (by linarith only [hKtwo] : 1 ≤ K)
      (by norm_num : (1 : ℕ) ≤ 3)
  have hbase : allocatedCandidateForwardControlInput s d b + C ≤ K ^ 4 := by
    calc
      _ ≤ K ^ 3 + K ^ 3 := add_le_add hinput (hCK.trans hKcube)
      _ = 2 * K ^ 3 := by ring
      _ ≤ K * K ^ 3 := mul_le_mul_of_nonneg_right hKtwo (pow_nonneg hK _)
      _ = K ^ 4 := by ring
  calc
    _ ≤ (K ^ 4) ^ C := pow_le_pow_left₀
      (add_nonneg (allocatedCandidateForwardControlInput_bounds s d hb).1 (Nat.cast_nonneg C)) hbase C
    _ = K ^ (4 * C) := (pow_mul _ _ _).symm
    _ ≤ K ^ A := pow_le_pow_right₀ (by linarith only [hKtwo]) hCA
    _ = (b + A) ^ A := rfl

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AveragedNormalizedTwistForecastJointModel
namespace OAI

section

namespace Erdos3

noncomputable def forecastAugmentedUnitThreshold (u p K C Fcap : ℝ) : ℝ :=
  (Real.exp (-(u + 3)) / Real.exp p ^ 2) /
    max 1 ((2 * K * C + Fcap) / Real.exp (-(u + 3)))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedNarrowSpatialCanonicalComparison
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical NNReal

def canonicalZeroSpatialKernelEmbedding (G N X : Type*) :
    Option G × X ↪ Option (G ⊕ N) × X where
  toFun := fun p => (Option.map Sum.inl p.1, p.2)
  inj' := by
    rintro ⟨a, x⟩ ⟨b, y⟩ h
    cases a <;> cases b <;> simp_all

@[simp] theorem canonicalZeroSpatialKernelEmbedding_apply (G N X : Type*)
    (p : Option G × X) :
    canonicalZeroSpatialKernelEmbedding G N X p = (Option.map Sum.inl p.1, p.2) := rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.CRTPolynomialInputAffineLaw
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

noncomputable def localPrimePowerIntegerPolynomialOutput
    {V : Type*} {s : ℕ} {J : Fin s → Type*}
    (p A e : ℕ) (F : ∀ j, J j → MvPolynomial V ℤ)
    (r x : V → ZMod (p ^ A)) (j : Sigma J) : ℤ :=
  eval (fun v => ((r v + (p : ZMod (p ^ A)) ^ e * x v).val : ℤ)) (F j.1 j.2)

@[simp] theorem localPrimePowerIntegerPolynomialOutput_reduce
    {V : Type*} {s : ℕ} {J : Fin s → Type*}
    (p A e : ℕ) [NeZero (p ^ A)] (F : ∀ j, J j → MvPolynomial V ℤ)
    (r x : V → ZMod (p ^ A)) (j : Sigma J) :
    (localPrimePowerIntegerPolynomialOutput p A e F r x j : ZMod (p ^ A)) =
      eval₂ (Int.castRingHom (ZMod (p ^ A)))
        (fun v => r v + (p : ZMod (p ^ A)) ^ e * x v) (F j.1 j.2) := by
  unfold localPrimePowerIntegerPolynomialOutput
  change (Int.castRingHom (ZMod (p ^ A))) (eval₂ (RingHom.id ℤ) _ _) = _
  rw [MvPolynomial.hom_eval₂, RingHom.comp_id]
  congr 1
  funext v
  simp only [Int.coe_castRingHom, Int.cast_natCast, ZMod.natCast_zmod_val]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastJointScaleNormalization
namespace OAI

section

namespace Erdos3

noncomputable def forecastJointGridSamplerLog (d : ℕ) (P E Q PR : ℝ) : ℝ :=
  Q + (P + E + 5) + PR + forecastJointGridMeshLog d P E

noncomputable def forecastJointGridSamplerFloor (d : ℕ) (P E Q PR : ℝ) : ℕ :=
  ⌈Real.exp (forecastJointGridSamplerLog d P E Q PR)⌉₊

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedModularRankMixedUniform
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped Classical

variable {m : ℕ}
  {G X : Type*}
  {I E : Fin m → Type*}
  {n : Fin m → ℕ}

abbrev AllocatedDeckRankCoefficientIndex (E : Fin m → Type*) (L : ℕ) :=
  Σ j : Fin m, E j × Fin L

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedAffineScaleEnvelope
namespace OAI

section

namespace Erdos3

noncomputable def affineReferenceCoefficientLog {A : Type*} [Semiring A] (D L : A) : A :=
  8 * (D + 1) * (L + 1)

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped BigOperators Classical NNReal

def allocatedAffineL1Log {A : Type*} [Semiring A] (m : ℕ) (D P Prho Pk : A) : A :=
  P + ((m * 2 ^ (m + 1) : ℕ) * Pk + allocatedDensityEnvelope m D P) +
    allocatedSupportEnvelope m D P + allocatedIdealLipEnvelope D P Prho +
    ((m + 1 : ℕ) * D + 2) + scalarCubeRiemannLog D

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

noncomputable def allocatedAffineCoefficientAccuracyLog {A : Type*} [Semiring A]
    (m : ℕ) (D P Prho Pk target : A) : A :=
  target + 1 + coefficientReplacementErrorLog D (allocatedAffineL1Log m D P Prho Pk)

noncomputable def allocatedAffineReferenceAccuracyLog {A : Type*} [Semiring A]
    (m : ℕ) (D P Prho Pk target : A) : A :=
  target + 1 + affineReferenceCoefficientLog D (allocatedAffineL1Log m D P Prho Pk) + 4

noncomputable def allocatedAffineLengthLog {A : Type*} [Semiring A]
    (m : ℕ) (D P Prho Pk target F T : A) : A :=
  m * allocatedFrontEnvelope m D P (allocatedAffineCoefficientAccuracyLog m D P Prho Pk target) +
    progressionSliceLengthLog D (allocatedAffineReferenceAccuracyLog m D P Prho Pk target) F T

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PartitionedAffineLogEnvelope
namespace OAI

section

namespace Erdos3
open scoped BigOperators NNReal Classical

section Definitions
variable {A : Type*} [Semiring A]
def affineProfileCoefficientEnvelope (D A₀ T₀ : A) : A := D * D + A₀ + T₀ + 7
end Definitions

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastNativePullbackBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Classical NNReal BigOperators

variable {X : Type*} [Fintype X]

noncomputable def forecastNormalizedSpatialCoordinates (base : X → ℤ) (N : X → ℕ)
    (τ : ℝ) (x : X → ℝ) : (Σ _ : X, Unit ⊕ Empty) → ℝ :=
  fun a => 8 * (x a.1 - (base a.1 : ℝ) / N a.1) / τ

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.FixedSpatialKernelProgressionForecastIntegral
namespace OAI

section

namespace Erdos3

theorem fixedSpatialKernelProgression_width_pos {S H : ℕ} {step : ℤ}
    (hS : 0 < S) (hstep : 0 < step) (hH : 2 ≤ H) :
    (0 : ℝ) < (step : ℝ) * ((H - 1 : ℕ) : ℝ) / S := by
  apply div_pos
  · apply mul_pos
    · exact_mod_cast hstep
    · exact_mod_cast (show 0 < H - 1 by omega)
  · exact_mod_cast hS

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SpatialTwoBlockEquiv
namespace OAI

section

namespace Erdos3
open scoped Classical

def twoKernelCopies (X : Type*) : X ⊕ X ≃ Fin 2 × X where
  toFun := Sum.elim (fun x => (0, x)) (fun x => (1, x))
  invFun z := if z.1 = 0 then Sum.inl z.2 else Sum.inr z.2
  left_inv := by intro z; cases z <;> simp
  right_inv := by rintro ⟨i, x⟩; fin_cases i <;> simp

def twoKernelEmbedding {X G : Type*} (blocks : Fin 2 × X ↪ G) : X ⊕ X ↪ G :=
  (twoKernelCopies X).toEmbedding.trans blocks

abbrev SpatialKernelRemainder {X G : Type*} (blocks : Fin 2 × X ↪ G) :=
  {g : G // g ∉ Set.range (twoKernelEmbedding blocks)}

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.IntegerPolynomialTorusPeriod
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

theorem integerPolynomial_eval_zmod_eq {K : Type*} (P : MvPolynomial K ℤ)
    (q : ℕ) (x y : K → ℤ) (hxy : ∀ k, (x k : ZMod q) = (y k : ZMod q)) :
    ((eval x P : ℤ) : ZMod q) = ((eval y P : ℤ) : ZMod q) := by
  change (Int.castRingHom (ZMod q)) (eval x P) = (Int.castRingHom (ZMod q)) (eval y P)
  rw [MvPolynomial.map_eval, MvPolynomial.map_eval]
  exact congrArg (fun z => eval z (MvPolynomial.map (Int.castRingHom (ZMod q)) P)) (funext hxy)

theorem integerPolynomial_eval_sub_dvd {K : Type*} (P : MvPolynomial K ℤ)
    (q : ℕ) (x y : K → ℤ) (hxy : ∀ k, (x k : ZMod q) = (y k : ZMod q)) :
    (q : ℤ) ∣ eval x P - eval y P := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp
  rw [Int.cast_sub, integerPolynomial_eval_zmod_eq P q x y hxy, sub_self]

theorem addCircle_int_div_eq_of_dvd_sub (q : ℕ) (a b : ℤ)
    (h : (q : ℤ) ∣ a - b) :
    (((a : ℝ) / q : ℝ) : AddCircle (1 : ℝ)) =
      (((b : ℝ) / q : ℝ) : AddCircle (1 : ℝ)) := by
  by_cases hq : q = 0
  · simp [hq]
  · let : NeZero q := ⟨hq⟩
    have hab : (a : ZMod q) = (b : ZMod q) := by
      apply sub_eq_zero.mp
      rw [← Int.cast_sub]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mpr h
    simpa only [ZMod.toAddCircle_intCast] using congrArg ZMod.toAddCircle hab

theorem integerPolynomial_eval_addCircle_div_eq {K : Type*} (P : MvPolynomial K ℤ)
    (q : ℕ) (x y : K → ℤ) (hxy : ∀ k, (x k : ZMod q) = (y k : ZMod q)) :
    ((((eval x P : ℤ) : ℝ) / q : ℝ) : AddCircle (1 : ℝ)) =
      ((((eval y P : ℤ) : ℝ) / q : ℝ) : AddCircle (1 : ℝ)) :=
  addCircle_int_div_eq_of_dvd_sub q _ _ (integerPolynomial_eval_sub_dvd P q x y hxy)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.AllocatedRecoveredTagTorusVariation
namespace OAI

section

namespace Erdos3

theorem unitCircle_dist_div_integer_parts {q : ℕ} (hq : 0 < q)
    (center r₀ r₁ : ℝ) (z₀ z₁ : ℤ)
    (hz : (((z₀ : ℝ) / q : ℝ) : UnitAddCircle) =
      (((z₁ : ℝ) / q : ℝ) : UnitAddCircle)) :
    dist (((center + r₀ + z₀) / q : ℝ) : UnitAddCircle)
      (((center + r₁ + z₁) / q : ℝ) : UnitAddCircle) ≤ |r₀ - r₁| / q := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  simp only [add_div, AddCircle.coe_add, hz, dist_add_right, dist_add_left]
  rw [dist_eq_norm, ← QuotientAddGroup.mk_sub]
  calc
    _ ≤ ‖r₀ / (q : ℝ) - r₁ / q‖ := QuotientAddGroup.norm_mk_le_norm
    _ = |r₀ - r₁| / q := by rw [← sub_div, Real.norm_eq_abs, abs_div, abs_of_pos hqR]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.MarkedRefilteredModelBudget
namespace OAI

section

namespace Erdos3

def markedRefilteredBasisInput (p : ℝ) : ℝ :=
  p + adaptedMarkedMapHeightBudget p + 1

def markedRefilteredMapInput (p : ℝ) : ℝ :=
  markedRefilteredBasisInput p + (markedRefilteredBasisInput p + 2) ^ 4

def markedRefilteredModelInput (A : ℕ) (p : ℝ) : ℝ :=
  p + markedRefilteredMapInput p + (markedRefilteredMapInput p + A) ^ A + 1

theorem markedRefilteredModelInput_bounds (A : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    let q := markedRefilteredBasisInput p
    let t := markedRefilteredMapInput p
    let r := markedRefilteredModelInput A p
    0 ≤ q ∧ p ≤ q ∧ adaptedMarkedMapHeightBudget p ≤ q ∧
      0 ≤ t ∧ q ≤ t ∧ (q + 2) ^ 4 ≤ t ∧
      0 ≤ r ∧ p ≤ r ∧ (t + A) ^ A ≤ r := by
  dsimp only
  have hb : 0 ≤ adaptedMarkedMapHeightBudget p := by
    unfold adaptedMarkedMapHeightBudget
    positivity
  have hq : 0 ≤ markedRefilteredBasisInput p := by
    unfold markedRefilteredBasisInput
    positivity
  have hpq : p ≤ markedRefilteredBasisInput p := by
    unfold markedRefilteredBasisInput
    linarith only [hb]
  have hbq : adaptedMarkedMapHeightBudget p ≤ markedRefilteredBasisInput p := by
    unfold markedRefilteredBasisInput
    linarith only [hp]
  have hpow : 0 ≤ (markedRefilteredBasisInput p + 2) ^ 4 := by positivity
  have ht : 0 ≤ markedRefilteredMapInput p := add_nonneg hq hpow
  have hqt : markedRefilteredBasisInput p ≤ markedRefilteredMapInput p :=
    le_add_of_nonneg_right hpow
  have hpowt : (markedRefilteredBasisInput p + 2) ^ 4 ≤ markedRefilteredMapInput p :=
    le_add_of_nonneg_left hq
  have hmodel : 0 ≤ (markedRefilteredMapInput p + A) ^ A := by positivity
  have hr : 0 ≤ markedRefilteredModelInput A p := by
    unfold markedRefilteredModelInput
    positivity
  have hpr : p ≤ markedRefilteredModelInput A p := by
    unfold markedRefilteredModelInput
    linarith only [ht, hmodel]
  have hmodelr : (markedRefilteredMapInput p + A) ^ A ≤ markedRefilteredModelInput A p := by
    unfold markedRefilteredModelInput
    linarith only [hp, ht]
  exact ⟨hq, hpq, hbq, ht, hqt, hpowt, hr, hpr, hmodelr⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ExternalKernelPrecenterNativePointPartners
namespace OAI

section

namespace Erdos3
open scoped BigOperators TensorProduct Classical

noncomputable def externalNetMaskFamily
    {Freq X Y I : Type*} (F : Freq → X → Y → ℂ)
    (centers : Freq → I → Y → ℂ) {ε : ℝ}
    (hnet : ∀ f x, ∃ i, ∀ y, ‖F f x y - centers f i y‖ ≤ ε)
    (input : X → ℂ) : (Freq × I) → X → ℂ :=
  fun b x => if externalNetIndex (F b.1) (centers b.1) (hnet b.1) x = b.2
    then input x else 0

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedCandidateStageScalarBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

def allocatedCandidateStageResetInput (s m : ℕ) (v : ℝ) : ℝ :=
  v + (v + 2) ^ 4 + ((s : ℝ) + 1) + s * (v + 1) +
    s * (((m : ℝ) + 1) + m * (v + 1))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedExternalCandidateExponentialFreezingBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem finiteFreezing_exp_mass (a b : ℝ) :
    Real.exp (-a) / (Real.exp b) ^ 2 = Real.exp (-(a + 2 * b)) := by
  rw [pow_two, ← Real.exp_add, ← Real.exp_sub]
  congr 1
  ring

theorem finiteFreezing_exp_mass_le {mass a b : ℝ} (hmass : Real.exp (-a) ≤ mass) :
    Real.exp (-(a + 2 * b)) ≤ mass / (Real.exp b) ^ 2 := by
  rw [← finiteFreezing_exp_mass]
  exact div_le_div_of_nonneg_right hmass (by positivity)

theorem finiteFreezing_exp_recursive_mass_le {mass a b pRec : ℝ}
    (hmass : Real.exp (-a) ≤ mass) (hpRec : a + 2 * b ≤ pRec) :
    Real.exp (-pRec) ≤ mass / (Real.exp b) ^ 2 := by
  exact (Real.exp_le_exp.mpr (neg_le_neg hpRec)).trans
    (finiteFreezing_exp_mass_le hmass)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedExternalCandidateCoveredBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

noncomputable def finiteFreezingInitialPrecision (p : ℝ) : ℝ :=
  Real.exp (-((p + 2) ^ 3))

noncomputable def finiteFreezingInitialDiscard (p : ℝ) : ℝ :=
  Real.exp (-(4 * p + 8))

noncomputable def finiteFreezingRecursiveParameter (C : ℕ) (p : ℝ) : ℝ :=
  12 * (p + C) ^ C + 32

theorem finiteFreezing_initial_precision_pos (p : ℝ) :
    0 < finiteFreezingInitialPrecision p := Real.exp_pos _

theorem finiteFreezing_initial_discard_pos (p : ℝ) :
    0 < finiteFreezingInitialDiscard p := Real.exp_pos _

theorem finiteFreezing_initial_le_polynomial {p : ℝ} (hp : 0 ≤ p)
    {C : ℕ} (hC : 2 ≤ C) : p ≤ (p + C) ^ C := by
  have hC' : (2 : ℝ) ≤ C := by exact_mod_cast hC
  have hbase : 1 ≤ p + C := by linarith
  calc
    p ≤ p + C := le_add_of_nonneg_right (Nat.cast_nonneg C)
    _ ≤ (p + C) ^ C := by
      simpa only [pow_one] using pow_le_pow_right₀ hbase (by omega : 1 ≤ C)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

noncomputable def candidateCoveredOuterParameter (A : ℕ) (p : ℝ) : ℝ :=
  (p + A) ^ A

noncomputable def candidateCoveredRightParameter (A B : ℕ) (p : ℝ) : ℝ :=
  (candidateCoveredOuterParameter A p + B) ^ B

noncomputable def candidateCoveredDictionaryParameter (A B R : ℕ) (p : ℝ) : ℝ :=
  (candidateCoveredRightParameter A B p + R) ^ R

noncomputable def candidateCoveredGeometryParameter (A B R : ℕ) (p : ℝ) : ℝ :=
  p + candidateCoveredOuterParameter A p + candidateCoveredRightParameter A B p +
    candidateCoveredDictionaryParameter A B R p + 1

noncomputable def candidateCoveredDiagramParameter (A B R Q : ℕ) (p : ℝ) : ℝ :=
  (candidateCoveredGeometryParameter A B R p + Q) ^ Q

theorem candidateCoveredGeometryParameter_bounds (A B R : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    1 ≤ candidateCoveredGeometryParameter A B R p ∧
      p ≤ candidateCoveredGeometryParameter A B R p ∧
      candidateCoveredOuterParameter A p ≤ candidateCoveredGeometryParameter A B R p ∧
      candidateCoveredRightParameter A B p ≤ candidateCoveredGeometryParameter A B R p ∧
      candidateCoveredDictionaryParameter A B R p ≤ candidateCoveredGeometryParameter A B R p := by
  have ho : 0 ≤ candidateCoveredOuterParameter A p := by
    unfold candidateCoveredOuterParameter
    positivity
  have hr : 0 ≤ candidateCoveredRightParameter A B p := by
    unfold candidateCoveredRightParameter
    positivity
  have hd : 0 ≤ candidateCoveredDictionaryParameter A B R p := by
    unfold candidateCoveredDictionaryParameter
    positivity
  unfold candidateCoveredGeometryParameter
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateRealThreshold
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical TensorProduct

noncomputable def candidateSideCutoff (bound : ℝ) : ℕ := Nat.ceil bound + 1

theorem candidateSideCutoff_pos (bound : ℝ) : 0 < candidateSideCutoff bound :=
  Nat.succ_pos _

theorem lt_candidateSideCutoff (bound : ℝ) : bound < (candidateSideCutoff bound : ℝ) := by
  have hceil := Nat.le_ceil bound
  simp only [candidateSideCutoff, Nat.cast_add, Nat.cast_one]
  linarith

theorem candidateSideCutoff_lt_max_add_two (bound : ℝ) :
    (candidateSideCutoff bound : ℝ) < max bound 0 + 2 := by
  have hmono : (Nat.ceil bound : ℝ) ≤ Nat.ceil (max bound 0) := by
    exact_mod_cast Nat.ceil_mono (le_max_left bound 0)
  have hceil := Nat.ceil_lt_add_one (le_max_right bound 0)
  simp only [candidateSideCutoff, Nat.cast_add, Nat.cast_one]
  linarith

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineSampleAlphabet
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def primeCoordinateObservation {ι σ : Type*} (q : ι → ℕ) (z : σ → ℤ) : ∀ i, σ → ZMod (q i) :=
  fun i j => (z j : ZMod (q i))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.BoundedPrimeResidual
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def residueTruncationCap (ι : Type*) [Fintype ι] [DecidableEq ι]
    (b : ℕ) (eta : ℝ) : ℝ :=
  ((lowDegreeCoordinateSets ι b).card : ℝ) * (2 : ℝ) ^ b * (1 + eta)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FullTaggedRationalRetraction
namespace OAI

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial
open scoped BigOperators Classical Matrix

variable {m : ℕ} {X : Type*} (J : Fin m → Type*) [∀ j, Fintype (J j)]

noncomputable def fullTaggedRealMatrixProjection
    (P : ∀ j, Matrix (J j) (J j) ℚ) (j : Fin m) :
    (J j → ℝ) →ₗ[ℝ] (J j → ℝ) :=
  Matrix.mulVecLin (fun i a => (P j i a : ℝ))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RationalTagProjectionComplement
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix Classical

variable {T : Type*} [Fintype T]

noncomputable def rationalTagProjectionComplement (P : Matrix T T ℚ) :
    (T → ℝ) →ₗ[ℝ] (T → ℝ) :=
  LinearMap.id - Matrix.mulVecLin (fun i j => (P i j : ℝ))

@[simp] theorem rationalTagProjectionComplement_apply (P : Matrix T T ℚ) (x : T → ℝ) :
    rationalTagProjectionComplement P x = x - (fun i j => (P i j : ℝ)) *ᵥ x := rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CertifiedAffineCutoffCost
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped BigOperators Classical TensorProduct

noncomputable def certifiedAffineCenterBudget (p : ℝ) : ℝ :=
  let q := p + ((p+2)^2+2)^63
  2*p + (q+2)^10 + (q+2)^8 + 1

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateThresholdSuccessor
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem finiteFreezing_floor_le_exp {densityCost budgetLog : ℝ}
    (hbudgetLog : 0 ≤ budgetLog) :
    Real.exp densityCost *
        max 2 (2 * Real.exp budgetLog * max 1 (Real.exp budgetLog)) ≤
      Real.exp (densityCost + 2 * budgetLog + 2) := by
  have he : 1 ≤ Real.exp budgetLog := Real.one_le_exp_iff.mpr hbudgetLog
  have he2 : 2 ≤ Real.exp (2 : ℝ) := by
    linarith [Real.add_one_le_exp (2 : ℝ)]
  have hpair : 2 ≤ 2 * Real.exp budgetLog * Real.exp budgetLog := by
    nlinarith [sq_nonneg (Real.exp budgetLog - 1)]
  rw [max_eq_right he, max_eq_right hpair]
  calc
    _ = 2 * Real.exp (densityCost + 2 * budgetLog) := by
      rw [show densityCost + 2 * budgetLog = densityCost + budgetLog + budgetLog by ring,
        Real.exp_add, Real.exp_add]
      ring
    _ ≤ Real.exp (2 : ℝ) * Real.exp (densityCost + 2 * budgetLog) :=
      mul_le_mul_of_nonneg_right he2 (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.FullTaggedProjectionPolynomial
namespace OAI

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {X J : Type*} [Fintype J]

theorem linearMap_pi_apply_eq_sum
    (P : (J → ℝ) →ₗ[ℝ] (J → ℝ)) (x : J → ℝ) (i : J) :
    P x i = ∑ a : J, P (Pi.single a 1) i * x a := by
  have hsum : ∑ a : J, x a • Pi.single a (1 : ℝ) = x := by
    ext a
    simp [Pi.smul_apply, Pi.single_apply]
  conv_lhs => rw [← hsum, map_sum]
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro a _
  exact mul_comm _ _

theorem sum_projection_C_eq
    (P : (J → ℝ) →ₗ[ℝ] (J → ℝ)) (U : Submodule ℝ (J → ℝ))
    (hP : ∀ x, x ∈ U → P x = x) (c : J → ℝ) (hc : c ∈ U) (i : J) :
    (∑ a : J, P (Pi.single a 1) i • C (c a) : MvPolynomial X ℝ) = C (c i) := by
  simp only [smul_eq_C_mul, ← C_mul, ← map_sum]
  rw [← linearMap_pi_apply_eq_sum, hP _ hc]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ActualCandidateSlowProjectionMass
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical Matrix

variable {m : ℕ} (J : Fin m → Type*) [∀ j, Fintype (J j)]

theorem fullTaggedRealMatrixProjection_single
    (P : ∀ j, Matrix (J j) (J j) ℚ) (j : Fin m) (a i : J j) :
    fullTaggedRealMatrixProjection J P j (Pi.single a 1) i = (P j i a : ℝ) :=
  congrFun (Matrix.mulVec_single_one (Matrix.of fun s t => (P j s t : ℝ)) a) i

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

noncomputable def actualCandidateSlowProjectionMassBudget (m nVars : ℕ) (d H : ℝ) : ℝ :=
  2 + d * Real.exp H * (((m + 1 : ℕ) : ℝ) * ((nVars + 1 : ℕ) : ℝ) ^ m)

theorem actualCandidateSlowProjectionMassBudget_two_le (m nVars : ℕ) {d H : ℝ}
    (hd : 0 ≤ d) : 2 ≤ actualCandidateSlowProjectionMassBudget m nVars d H := by
  unfold actualCandidateSlowProjectionMassBudget
  exact le_add_of_nonneg_right (by positivity)

theorem actualCandidateSlowProjectionMassBudget_one_le (m nVars : ℕ) {d H : ℝ}
    (hd : 0 ≤ d) : 1 ≤ actualCandidateSlowProjectionMassBudget m nVars d H :=
  (by norm_num : (1 : ℝ) ≤ 2).trans
    (actualCandidateSlowProjectionMassBudget_two_le m nVars hd)

theorem actualCandidateSlowProjectionMassBudget_max_le (m nVars : ℕ) {d H : ℝ}
    (hd : 0 ≤ d) :
    max 1 (d * Real.exp H) ≤ actualCandidateSlowProjectionMassBudget m nVars d H := by
  apply max_le (actualCandidateSlowProjectionMassBudget_one_le m nVars hd)
  have hm : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos m
  have hn : (1 : ℝ) ≤ ((nVars + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos nVars
  have hfactor : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) * ((nVars + 1 : ℕ) : ℝ) ^ m := by
    simpa only [one_mul] using mul_le_mul hm (one_le_pow₀ hn) (by norm_num) (by positivity)
  have h := mul_le_mul_of_nonneg_left hfactor (mul_nonneg hd (Real.exp_nonneg H))
  unfold actualCandidateSlowProjectionMassBudget
  rw [mul_one] at h
  linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedAffinePhysicalTerminalReset
namespace OAI

section

namespace Erdos3.VectorPolynomial

def affineResetNativeBudget (C : ℕ) (pFull pMap q : ℝ) : ℝ :=
  pFull + pMap + max q 0 + (pFull + C) ^ C + (pMap + 2) ^ 4

theorem affineResetNativeBudget_bounds (C : ℕ) {pFull pMap q : ℝ}
    (hFull : 0 ≤ pFull) (hMap : 0 ≤ pMap) :
    let pNative := affineResetNativeBudget C pFull pMap q
    0 ≤ pNative ∧ pFull ≤ pNative ∧ pMap ≤ pNative ∧ q ≤ pNative ∧
      (pFull + C) ^ C ≤ pNative ∧ (pMap + 2) ^ 4 ≤ pNative ∧
      (pMap + 2) ^ 3 + q ≤ pNative := by
  have hq0 : 0 ≤ max q 0 := le_max_right _ _
  have hq : q ≤ max q 0 := le_max_left _ _
  have hslow : 0 ≤ (pFull + C) ^ C := pow_nonneg (by positivity) _
  have hmap4 : 0 ≤ (pMap + 2) ^ 4 := pow_nonneg (by linarith) _
  have h34 : (pMap + 2) ^ 3 ≤ (pMap + 2) ^ 4 :=
    pow_le_pow_right₀ (by linarith) (by omega)
  dsimp only [affineResetNativeBudget]
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedAffineCanonicalBackendBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

def allocatedAffineResetHeightLog (p : ℝ) : ℝ := (p + 4) ^ 12

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NativeResetBracketGeometry
namespace OAI

section

namespace Erdos3

open Module

noncomputable def nativeResetBracketHeight (p : ℝ) : ℕ :=
  ⌈Real.exp ((p + 4) ^ 11)⌉₊

theorem nativeResetBracketLog_ge_input {p : ℝ} (hp : 0 ≤ p) :
    p ≤ (p + 4) ^ 11 := by
  have hpow : p + 4 ≤ (p + 4) ^ 11 := by
    simpa only [pow_one] using pow_le_pow_right₀ (by linarith : 1 ≤ p + 4)
      (by norm_num : (1 : ℕ) ≤ 11)
  linarith only [hpow]

end Erdos3

end

end OAI
end


