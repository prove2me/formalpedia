-- Prove2me | Definitions.Def_OAIHecke78B003
-- name    : OAIHecke78B003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-08T19:24:39.044976+00:00
-- url     : https://prove2.me/theorems/83c1f78b-0d3f-4e7a-8577-8d1c4170054f
-- title:
--   OpenAI Hecke 7/8 split, definitions bundle 4 of 16
-- statement:
--   Definitions bundle 4 of 16 of the split of OpenAI's proof that finite-order Hecke $L$-functions over $\mathbb{Q}(\zeta_3)$ do not vanish for $\operatorname{Re} s > 7/8$: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/NumberTheory/DirichletL` (OpenAI, *The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane $\operatorname{Re} s > 7/8$*, September 30, 2026, family 003 of [github.com/openai/math](https://github.com/openai/math), Apache License 2.0) and from the vendored library modules of rellich-kondrachov that OpenAI's development uses (with OpenAI's compatibility patches), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (definitions that choose witnesses of existence theorems or build structures carrying proofs need those proofs) and the instances and attribute-tagged lemmas of the same modules.
--
--   It imports no other bundle of this split. It also imports wurtle's published bundle `HeckeSevenEighths` (the comparator definitions of OpenAI's challenge statement: `Character`, `LFunction` and the theta-function pairs they are built from), which OpenAI's development defines identically.
--
--   Modules: `Compat2`, `CompatCircle`, `Supremum`, `Continuation`, `ContinuationInversion`, `ContinuationContour`, `ContinuationPolynomialContour`, `CubicDyadicDecay`, `CubicSieve.Algebra`, `CubicSieve.Operator`, `CubicSieve.Factorization`, `Mellin.CompactWeights`, `CubicSieve.SquarefreeTransfer`, `CubicSieve.QuantitativePassage`, `MeanSquare.ReflectedDyadicSeries`, `Vendor.RellichKondrachov.MeasureTheory.Function.LpSpace.Restrict`, `Vendor.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.Smoothing`, `Vendor.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.H1`, `Vendor.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.Translation`, `Vendor.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.Approximation`, `Vendor.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.Compactness`, `Vendor.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.ArzelaAscoli`, `Vendor.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.Transfer`, `Vendor.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.FrechetKolmogorov`, `Vendor.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.Kernels`, `Vendor.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.TranslationIntegral`, `Vendor.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.TranslationEstimate`, `Vendor.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.TranslationEstimateL2`, `Vendor.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.TranslationEstimateH1`, `Vendor.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.Rellich`, `GaussSum.CompletedDyadicRows`, `HeathBrownIteration`, `CubicSieve.ExponentImprovement`, `Descent.LocalReflection`, `Descent.SecondKernelMeasure`, `Descent.SlotAssignments`, `Descent.FirstNominal`, `Descent.FirstFreshMeasure`, `Descent.Basic`, `Descent.ActualDepthBudget`, `Moments.Basic`, `Moments.CRT`, `Moments.PrimePower`, `Hecke.ExceptionalRows`, `EulerFactors`, `Detector.Compensation`, `Detector.Gauss`, `Descent.RecursionParameters`, `Detector.Basic`, `Hecke.DetectorProfiles`, `LogarithmicControl`, `Hecke.MellinIdentity`, `Hecke.StripActual`, `Hecke.Logarithmic`, `Hecke.DetectorDyadicBridge`, `Hecke.DetectorRowCountCrossing`, `Hecke.DetectorBranchBudget`, `Hecke.PrimeScale`, `Hecke.PrimeAmplitudeActual`, `Hecke.InverseAmplificationBudget`, `Detector.Euler`, `Detector.Local`, `Detector.SpectralWeights`, `Detector.EulerMarked`, `Detector.RadialMellin`, `Hecke.SignalShift`, `Inversion.InitialOverlapSource`, `Dictionary.InverseRawGeometry`, `Moments.RayNonprincipal`, `Endpoint`, `Reflection.KernelWeights`, `Reflection.SourceSelection`, `Detector.InitialScales`, `Detector.MixedFubini`, `PrimeRows.Measurable`, `PrimeRows.SelectedFirstBounds`, `Hecke.DetectorAdaptiveCutoff`, `Hecke.DetectorRawBranches`, `Hecke.DetectorClassBudget`, `Detector.GaussianFlow`, `Detector.GramCommonLinear`, `Detector.LowCentralGeometry`, `Hecke.Dirichlet`, `ParametersHighData`, `Moments.OriginalReflectionErrorMass`, `Detector.DetectorInverseFields`, `Detector.SourceBatch`, `Detector.SourceAmplitudeClasses`, `Moments.FiniteProfileExceptionalNormalize`, `Moments.CommonMaskEnergy`, `Moments.NaturalFixedRaySourceInternal`, `Moments.PrimeGlobal`, `Moments.PrimeHeight`, `Moments.NaturalFixedRaySourceNaturalPrime`, `Moments.NaturalFixedRaySourceRayPrime`, `Moments.RayMaskedFloorSlots`, `Moments.RayMaskedFloorNatural`, `Moments.RayMaskedFloorShared`, `Moments.RayMaskedFloorSource`, `Moments.RayMaskedFloor`, `Moments.RayMaskedFloorState`, `Energy.ActiveChildRestoration`, `Moments.LiveCapacity`, `Energy.CapacityRemoval`, `Energy.PaidBands`, `Energy.PaidRemoval`, `Energy.AllocatedPaid`, `Moments.CommonSectorWindow`, `Moments.SecondExceptionalPairDictionary`, `Moments.SecondDivisorSupport`, `Energy.AllocatedHomogeneous`, `Moments.SourceInputFirstSectorTailUniform`, `Moments.SourceInputFirstSectorTailNatural`, `Moments.SourceInputZeroUniform`, `Moments.SourceInputFirstRemainder`, `Moments.FirstSecondLossParameters`, `Energy.CanonicalChildBound`, `Energy.CanonicalPaidSource`, `Energy.CanonicalCommonPaid`, `Energy.CanonicalReferencePaid`, `Energy.CanonicalUniformReference`, `Energy.CanonicalMainPaid`, `Energy.CanonicalNestedReference`, `Energy.CanonicalErrorUniform`, `Moments.SecondFrozenLiveSource`, `Moments.FiniteProfileExceptionalFixedQBlock`, `Moments.FiniteProfileExceptionalFixedQRows`, `Moments.FiniteProfileExceptionalFixedQDyadic`, `Moments.FiniteProfileExceptionalFixedQSaved`, `Moments.FiniteProfileExceptionalFixedQUniform`, `Moments.SecondExceptionalFixedQChosenBlock`, `Moments.SecondExceptionalFixedQSource`, `Moments.SecondExceptionalUniformSource`, `Moments.SecondSourceDiagonal`, `Moments.SecondSourceRemainder`, `Moments.SecondFrozenLiveDescent`, `Moments.SecondFrozenUniformSubset`, `Moments.SecondFrozenSeededPowerDescent`, `Moments.SecondFrozenReferenceSeededPowerDescent`, `Moments.FirstSeededGaussianPower`, `Moments.FirstNestedSeededGaussianPower`, `Moments.SecondInputCapacitySource`, `Energy.CanonicalErrorGaussian`, `Energy.CanonicalErrorAdmitted`, `Moments.FirstCommonReferencePower`, `Moments.SuccessorPaidParameters`, `Energy.CanonicalErrorPower`, `Energy.FirstGaussianProfileWeights`, `Energy.CanonicalErrorHomogeneous`, `Energy.CanonicalErrorSubsets`, `Energy.CanonicalMainUniform`, `Energy.CanonicalMainGaussian`, `Energy.CanonicalMainSeparated`, `Energy.CanonicalMainSeparatedPower`, `Energy.CanonicalMainHomogeneous`, `Energy.CanonicalMainSubsets`, `Energy.CanonicalAmplifiedUniform`, `Moments.FirstSecondCommonGates`, `Energy.CanonicalAnnularPower`, `Energy.CanonicalLowColumn`, `Energy.CanonicalHighColumn`, `Energy.FirstTwoSeedAdmission`, `Energy.CanonicalHighSource`, `Energy.FirstRightAdmission`, `Energy.CanonicalRightSourceColumn`, `Energy.CanonicalHighPhysical`, `Energy.CanonicalLowSource`, `Energy.CanonicalLowPhysical`, `Energy.WidthSchedule`, `Energy.StageReserveSchedule`, `Energy.CappedRequests`, `Energy.FirstStageLossBudget`, `Energy.StageMargins`, `Energy.FirstSourceParameters`, `Energy.NaturalSourceAdmission`, `Energy.ReferenceLowDirect`, `Energy.ReferenceLowMoments`, `Energy.ReferenceLowReflection`, `Energy.ReferenceLowReflectionError`, `Energy.OriginalHighReflectionDeleted`, `Energy.OriginalHighReflectionOriginal`, `Energy.OriginalHighReflectionBounded`, `Energy.OriginalHighReflectionPower`, `Energy.OriginalHighReflectionSymmetric`, `Energy.OriginalHighReflectionSymmetricBounded`, `Energy.ReferenceRobustDeletedEnergy`, `Energy.ReferenceRobustOriginal`, `Energy.ReferenceRobustPower`, `Energy.ReferenceLivePower`, `Energy.PositiveHighParameters`, `Energy.PositiveBalancedAdmission`, `Energy.PositiveHighAssembly`, `Energy.ReferenceRobustBounded`, `Energy.ReferenceLiveBounded`, `Energy.PositiveHighSourceBounded`, `Energy.PositiveHighAssemblyBounded`, `Energy.PositiveHighBound`, `Moments.DetectorPlainMomentParameters`, `Moments.DetectorPlainRelativeClass`, `PrimeRows.NonfloorSourceCount`, `PrimeRows.NonfloorDyadic`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission. Comments are removed; no statement of OpenAI's was changed.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths

/-!
# OpenAI Hecke 7/8 split: definitions bundle OAIHecke78B003

OpenAI, *The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane
Re s > 7/8*, OpenAI Math Release, September 30, 2026, https://github.com/openai/math (family 003;
Lean in `lean/OAI/NumberTheory/DirichletL`, Apache License 2.0; vendored modules of
PrimeNumberTheoremAnd and rellich-kondrachov). Carved from the port to Lean 4.33.1 / Mathlib
0df444a, comments removed. Modules:
  Compat2
  CompatCircle
  Supremum
  Continuation
  ContinuationInversion
  ContinuationContour
  ContinuationPolynomialContour
  CubicDyadicDecay
  CubicSieve.Algebra
  CubicSieve.Operator
  CubicSieve.Factorization
  Mellin.CompactWeights
  CubicSieve.SquarefreeTransfer
  CubicSieve.QuantitativePassage
  MeanSquare.ReflectedDyadicSeries
  Vendor.RellichKondrachov.MeasureTheory.Function.LpSpace.Restrict
  Vendor.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.Smoothing
  Vendor.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.H1
  Vendor.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.Translation
  Vendor.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.Approximation
  Vendor.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.Compactness
  Vendor.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.ArzelaAscoli
  Vendor.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.Transfer
  Vendor.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.FrechetKolmogorov
  Vendor.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.Kernels
  Vendor.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.TranslationIntegral
  Vendor.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.TranslationEstimate
  Vendor.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.TranslationEstimateL2
  Vendor.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.TranslationEstimateH1
  Vendor.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.Rellich
  GaussSum.CompletedDyadicRows
  HeathBrownIteration
  CubicSieve.ExponentImprovement
  Descent.LocalReflection
  Descent.SecondKernelMeasure
  Descent.SlotAssignments
  Descent.FirstNominal
  Descent.FirstFreshMeasure
  Descent.Basic
  Descent.ActualDepthBudget
  Moments.Basic
  Moments.CRT
  Moments.PrimePower
  Hecke.ExceptionalRows
  EulerFactors
  Detector.Compensation
  Detector.Gauss
  Descent.RecursionParameters
  Detector.Basic
  Hecke.DetectorProfiles
  LogarithmicControl
  Hecke.MellinIdentity
  Hecke.StripActual
  Hecke.Logarithmic
  Hecke.DetectorDyadicBridge
  Hecke.DetectorRowCountCrossing
  Hecke.DetectorBranchBudget
  Hecke.PrimeScale
  Hecke.PrimeAmplitudeActual
  Hecke.InverseAmplificationBudget
  Detector.Euler
  Detector.Local
  Detector.SpectralWeights
  Detector.EulerMarked
  Detector.RadialMellin
  Hecke.SignalShift
  Inversion.InitialOverlapSource
  Dictionary.InverseRawGeometry
  Moments.RayNonprincipal
  Endpoint
  Reflection.KernelWeights
  Reflection.SourceSelection
  Detector.InitialScales
  Detector.MixedFubini
  PrimeRows.Measurable
  PrimeRows.SelectedFirstBounds
  Hecke.DetectorAdaptiveCutoff
  Hecke.DetectorRawBranches
  Hecke.DetectorClassBudget
  Detector.GaussianFlow
  Detector.GramCommonLinear
  Detector.LowCentralGeometry
  Hecke.Dirichlet
  ParametersHighData
  Moments.OriginalReflectionErrorMass
  Detector.DetectorInverseFields
  Detector.SourceBatch
  Detector.SourceAmplitudeClasses
  Moments.FiniteProfileExceptionalNormalize
  Moments.CommonMaskEnergy
  Moments.NaturalFixedRaySourceInternal
  Moments.PrimeGlobal
  Moments.PrimeHeight
  Moments.NaturalFixedRaySourceNaturalPrime
  Moments.NaturalFixedRaySourceRayPrime
  Moments.RayMaskedFloorSlots
  Moments.RayMaskedFloorNatural
  Moments.RayMaskedFloorShared
  Moments.RayMaskedFloorSource
  Moments.RayMaskedFloor
  Moments.RayMaskedFloorState
  Energy.ActiveChildRestoration
  Moments.LiveCapacity
  Energy.CapacityRemoval
  Energy.PaidBands
  Energy.PaidRemoval
  Energy.AllocatedPaid
  Moments.CommonSectorWindow
  Moments.SecondExceptionalPairDictionary
  Moments.SecondDivisorSupport
  Energy.AllocatedHomogeneous
  Moments.SourceInputFirstSectorTailUniform
  Moments.SourceInputFirstSectorTailNatural
  Moments.SourceInputZeroUniform
  Moments.SourceInputFirstRemainder
  Moments.FirstSecondLossParameters
  Energy.CanonicalChildBound
  Energy.CanonicalPaidSource
  Energy.CanonicalCommonPaid
  Energy.CanonicalReferencePaid
  Energy.CanonicalUniformReference
  Energy.CanonicalMainPaid
  Energy.CanonicalNestedReference
  Energy.CanonicalErrorUniform
  Moments.SecondFrozenLiveSource
  Moments.FiniteProfileExceptionalFixedQBlock
  Moments.FiniteProfileExceptionalFixedQRows
  Moments.FiniteProfileExceptionalFixedQDyadic
  Moments.FiniteProfileExceptionalFixedQSaved
  Moments.FiniteProfileExceptionalFixedQUniform
  Moments.SecondExceptionalFixedQChosenBlock
  Moments.SecondExceptionalFixedQSource
  Moments.SecondExceptionalUniformSource
  Moments.SecondSourceDiagonal
  Moments.SecondSourceRemainder
  Moments.SecondFrozenLiveDescent
  Moments.SecondFrozenUniformSubset
  Moments.SecondFrozenSeededPowerDescent
  Moments.SecondFrozenReferenceSeededPowerDescent
  Moments.FirstSeededGaussianPower
  Moments.FirstNestedSeededGaussianPower
  Moments.SecondInputCapacitySource
  Energy.CanonicalErrorGaussian
  Energy.CanonicalErrorAdmitted
  Moments.FirstCommonReferencePower
  Moments.SuccessorPaidParameters
  Energy.CanonicalErrorPower
  Energy.FirstGaussianProfileWeights
  Energy.CanonicalErrorHomogeneous
  Energy.CanonicalErrorSubsets
  Energy.CanonicalMainUniform
  Energy.CanonicalMainGaussian
  Energy.CanonicalMainSeparated
  Energy.CanonicalMainSeparatedPower
  Energy.CanonicalMainHomogeneous
  Energy.CanonicalMainSubsets
  Energy.CanonicalAmplifiedUniform
  Moments.FirstSecondCommonGates
  Energy.CanonicalAnnularPower
  Energy.CanonicalLowColumn
  Energy.CanonicalHighColumn
  Energy.FirstTwoSeedAdmission
  Energy.CanonicalHighSource
  Energy.FirstRightAdmission
  Energy.CanonicalRightSourceColumn
  Energy.CanonicalHighPhysical
  Energy.CanonicalLowSource
  Energy.CanonicalLowPhysical
  Energy.WidthSchedule
  Energy.StageReserveSchedule
  Energy.CappedRequests
  Energy.FirstStageLossBudget
  Energy.StageMargins
  Energy.FirstSourceParameters
  Energy.NaturalSourceAdmission
  Energy.ReferenceLowDirect
  Energy.ReferenceLowMoments
  Energy.ReferenceLowReflection
  Energy.ReferenceLowReflectionError
  Energy.OriginalHighReflectionDeleted
  Energy.OriginalHighReflectionOriginal
  Energy.OriginalHighReflectionBounded
  Energy.OriginalHighReflectionPower
  Energy.OriginalHighReflectionSymmetric
  Energy.OriginalHighReflectionSymmetricBounded
  Energy.ReferenceRobustDeletedEnergy
  Energy.ReferenceRobustOriginal
  Energy.ReferenceRobustPower
  Energy.ReferenceLivePower
  Energy.PositiveHighParameters
  Energy.PositiveBalancedAdmission
  Energy.PositiveHighAssembly
  Energy.ReferenceRobustBounded
  Energy.ReferenceLiveBounded
  Energy.PositiveHighSourceBounded
  Energy.PositiveHighAssemblyBounded
  Energy.PositiveHighBound
  Moments.DetectorPlainMomentParameters
  Moments.DetectorPlainRelativeClass
  PrimeRows.NonfloorSourceCount
  PrimeRows.NonfloorDyadic
-/

section

instance OAIHeckeCompat.finite_quotient_of_neZero {S : Type*} [CommRing S] [IsDomain S]
    [Module.Free ℤ S] [Module.Finite ℤ S] {I : Ideal S} [NeZero I] : Finite (S ⧸ I) :=
  I.finiteQuotientOfFreeOfNeBot (NeZero.ne I)
end

section

namespace Circle

instance : MeasurableSpace Circle := inferInstanceAs <| MeasurableSpace <| Subtype _

instance : BorelSpace Circle :=
  inferInstanceAs <| BorelSpace <| Subtype (· ∈ Metric.sphere (0 : ℂ) 1)

end Circle

attribute [simp] Circle.norm_coe

@[simp] lemma Circle.nnnorm_coe (z : Circle) : ‖(z : ℂ)‖₊ = 1 := NNReal.coe_injective z.norm_coe
@[simp] lemma Circle.enorm_coe (z : Circle) : ‖(z : ℂ)‖ₑ = 1 := by simp [enorm_eq_nnnorm]

@[simp] protected lemma Circle.nnnorm_smul {E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℂ E] (u : Circle) (v : E) : ‖u • v‖₊ = ‖v‖₊ :=
  NNReal.coe_injective (u.norm_smul v)

@[simp] protected lemma Circle.enorm_smul {E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℂ E] (u : Circle) (v : E) : ‖u • v‖ₑ = ‖v‖ₑ := by
  simp [enorm_eq_nnnorm]
end

section

namespace OAI

namespace SevenEighths.Supremum

noncomputable section

def continuationMargin (β ω σ : ℝ) : ℝ := min (β - 7 / 8 - ω) σ

end

end SevenEighths.Supremum

end OAI
end

section

namespace OAI

noncomputable section
open Filter Asymptotics MeasureTheory
open scoped Topology
namespace SevenEighths.Continuation

def signalMellin (f : ℝ → ℂ) (c : ℝ) (s : ℂ) : ℂ :=
  mellin f (-(s + (c : ℂ)))

def RapidDecayAtZero (f : ℝ → ℂ) : Prop :=
  ∀ B : ℝ, f =O[𝓝[>] (0 : ℝ)] (fun x : ℝ => x ^ B)

def gaussianMultiplier (H : ℂ → ℂ) (s : ℂ) : ℂ :=
  Complex.exp ((s - 5 / 6) ^ 2) * H s

end SevenEighths.Continuation

end

end OAI
end

section

namespace OAI

noncomputable section
open MeasureTheory Set Filter Asymptotics
open scoped Topology FourierTransform
namespace SevenEighths.Continuation

def normalizedSignal (f : ℝ → ℂ) (c : ℝ) (x : ℝ) : ℂ :=
  (x : ℂ) ^ (-(c : ℂ)) • f x

end SevenEighths.Continuation

end

end OAI
end

section

namespace OAI

noncomputable section
open MeasureTheory Set Filter Asymptotics Complex
open scoped Topology
namespace SevenEighths.Continuation

def gaussianContourIntegrand (G : ℂ → ℂ) (c Z : ℝ) (s : ℂ) : ℂ :=
  (Z : ℂ) ^ (s + (c : ℂ)) * Complex.exp ((s - 5 / 6) ^ 2) * G s

end SevenEighths.Continuation

end

end OAI
end

section

namespace OAI

noncomputable section
open MeasureTheory Set Filter Asymptotics Complex
open scoped Topology
namespace SevenEighths.Continuation

def polynomialGaussian (n : ℕ) (y : ℝ) : ℝ :=
  (1+|y|^n)*Real.exp (-(y^2))

end SevenEighths.Continuation

end

end OAI
end

section

namespace OAI

namespace SevenEighths.CubicDyadicDecay
open scoped BigOperators
noncomputable section

def decayConstant (α : ℝ) : ℝ :=
  (2 : ℝ)^α / ((2 : ℝ)^α - 1) + (1 - (2 : ℝ)^(α - 3))⁻¹

end
end SevenEighths.CubicDyadicDecay

end OAI
end

section

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
noncomputable section

variable {R : Type*} [CommRing R] [Finite Rˣ]

omit [Finite Rˣ] in
theorem cubic_cube_eq_mask (χ : MulChar R ℂ) (hχ : χ ^ 3 = 1) (x : R) :
    χ (x ^ 3) = if IsUnit x then 1 else 0 := by
  classical
  rw [map_pow, ← MulChar.pow_apply' χ (by decide : (3 : ℕ) ≠ 0), hχ]
  by_cases hx : IsUnit x
  · rw [if_pos hx, MulChar.one_apply hx]
  · rw [if_neg hx, MulChar.map_nonunit _ hx]

end
end SevenEighths.CubicSieve

end OAI
end

section

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators
noncomputable section

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

def operator (A : Matrix m n ℂ) : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ m :=
  A.toEuclideanLin.toContinuousLinearMap

omit [DecidableEq m] in
@[simp] theorem operator_apply (A : Matrix m n ℂ) (x : EuclideanSpace ℂ n) (i : m) :
    operator A x i = ∑ j, A i j * x j := rfl

def squaredNorm (A : Matrix m n ℂ) : ℝ := ‖operator A‖ ^ 2

def conjugateVector (x : EuclideanSpace ℂ n) : EuclideanSpace ℂ n :=
  WithLp.toLp 2 (fun j => star (x j))

omit [Fintype n] [DecidableEq n] in
@[simp] theorem conjugateVector_apply (x : EuclideanSpace ℂ n) (j : n) :
    conjugateVector x j = star (x j) := rfl

omit [DecidableEq n] in
@[simp] theorem norm_conjugateVector (x : EuclideanSpace ℂ n) :
    ‖conjugateVector x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.norm_sq_eq, conjugateVector_apply, norm_star]

end
end SevenEighths.CubicSieve

end OAI
end

section

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open UniqueFactorizationMonoid
noncomputable section

variable {M : Type*} [CommMonoidWithZero M] [UniqueFactorizationMonoid M]
  [NormalizationMonoid M] [Subsingleton Mˣ]

def firstPart (x : M) : M :=
  ∏ p ∈ (normalizedFactors x).toFinset.filter
    (fun p => (normalizedFactors x).count p % 3 = 1), p

def secondPart (x : M) : M :=
  ∏ p ∈ (normalizedFactors x).toFinset.filter
    (fun p => (normalizedFactors x).count p % 3 = 2), p

def cubePart (x : M) : M :=
  ∏ p ∈ (normalizedFactors x).toFinset, p ^ ((normalizedFactors x).count p / 3)

end
end SevenEighths.CubicSieve

end OAI
end

section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open Filter
open Filter
open scoped Topology
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology

open Filter Asymptotics MeasureTheory
open scoped Topology

namespace ConcreteCompactWeight

noncomputable def positiveExtension (y : ℝ) : ℝ :=
  1 + (y - 1) * Real.smoothTransition (2 * y - 1)

theorem positiveExtension_smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) positiveExtension := by
  unfold positiveExtension
  have ht : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun y : ℝ => 2 * y - 1) := by fun_prop
  exact contDiff_const.add
    ((contDiff_id.sub contDiff_const).mul
      ((Real.smoothTransition.contDiff (n := ⊤)).comp ht))

theorem positiveExtension_pos (y : ℝ) : 0 < positiveExtension y := by
  unfold positiveExtension
  by_cases hhalf : y ≤ 1 / 2
  · have ht : 2 * y - 1 ≤ 0 := by linarith
    rw [Real.smoothTransition.zero_of_nonpos ht]
    norm_num
  · by_cases hone : 1 ≤ y
    · have ht : 1 ≤ 2 * y - 1 := by linarith
      rw [Real.smoothTransition.one_of_one_le ht]
      linarith
    · have hle := Real.smoothTransition.le_one (2 * y - 1)
      have hnonneg := Real.smoothTransition.nonneg (2 * y - 1)
      have hprod : (1 - y) * Real.smoothTransition (2 * y - 1) ≤ 1 - y := by
        exact (mul_le_mul_of_nonneg_left hle (by linarith)).trans_eq (mul_one _)
      nlinarith

theorem positiveExtension_eq (y : ℝ) (hy : 1 ≤ y) :
    positiveExtension y = y := by
  unfold positiveExtension
  rw [Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ 2 * y - 1)]
  ring

end ConcreteCompactWeight

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open Filter
open Filter
open scoped Topology
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open UniqueFactorizationMonoid
open scoped BigOperators

section

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
namespace SecondPassArithmetic

structure SquarefreeBudgetData where
  windows : Fin 7 → ℝ → ℂ
  arithmetic : ℝ
  smooth : ℝ
  windowBound : ℝ
  tail : ℝ
  arithmetic_pos : 0 < arithmetic
  smooth_nonneg : 0 ≤ smooth
  windowBound_nonneg : 0 ≤ windowBound
  tail_pos : 0 < tail

end SecondPassArithmetic

end

open scoped BigOperators Classical SchwartzMap

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open Filter
open Filter
open scoped Topology
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open UniqueFactorizationMonoid
open scoped BigOperators

open scoped BigOperators Classical SchwartzMap ContDiff

open scoped BigOperators Classical

open scoped BigOperators
namespace CompletedDyadic

def kernelTerm (t s A : ℝ) (n : ℕ) : ℝ := ((2:ℝ)^n)^s/(1+t*(2:ℝ)^n)^A

end CompletedDyadic

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open Filter
open Filter
open scoped Topology
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators

open scoped BigOperators Classical SchwartzMap ContDiff
namespace CompletedGauss

def completedShellWindow (x : ℝ) : ℂ :=
  if -Real.log 2≤x ∧ x≤0 then 1 else 0

open CompletedDyadic

end CompletedGauss

end

end OAI
end

section

namespace MeasureTheory

open scoped ENNReal

namespace Lp

noncomputable section

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {s : Set α} (hs : MeasurableSet s)

noncomputable def extendByZeroFun (f : Lp E p (μ.restrict s)) : Lp E p μ :=
  let hf : MemLp (fun x : α => f x) p (μ.restrict s) := Lp.memLp f
  let hfi : MemLp (s.indicator fun x : α => f x) p μ :=
    (memLp_indicator_iff_restrict (μ := μ) (p := p) (s := s) (f := fun x : α => f x) hs).2 hf
  hfi.toLp (s.indicator fun x : α => f x)

omit [NormedSpace ℝ E] [Fact (1 ≤ p)] in
lemma extendByZeroFun_coe (f : Lp E p (μ.restrict s)) :
    extendByZeroFun (μ := μ) (p := p) (s := s) hs f =ᵐ[μ] s.indicator fun x : α => f x := by
  dsimp [extendByZeroFun]
  exact MemLp.coeFn_toLp _

noncomputable def extendByZeroₗ : Lp E p (μ.restrict s) →ₗ[ℝ] Lp E p μ where
  toFun := extendByZeroFun (μ := μ) (p := p) (s := s) hs
  map_add' f g := by
    classical
    
    refine Lp.ext ?_
    have h_add_restrict :
        (fun x : α => (f + g) x) =ᵐ[μ.restrict s] fun x : α => f x + g x := by
      exact (Lp.coeFn_add (μ := μ.restrict s) f g)
    have h_add_on :
        ∀ᵐ x : α ∂μ, x ∈ s → (f + g) x = f x + g x :=
      (ae_restrict_iff' (μ := μ) (s := s) hs).1 h_add_restrict
    filter_upwards
      [ extendByZeroFun_coe (μ := μ) (p := p) (s := s) hs (f + g)
      , extendByZeroFun_coe (μ := μ) (p := p) (s := s) hs f
      , extendByZeroFun_coe (μ := μ) (p := p) (s := s) hs g
      , coeFn_add (extendByZeroFun (μ := μ) (p := p) (s := s) hs f)
          (extendByZeroFun (μ := μ) (p := p) (s := s) hs g)
      , h_add_on
      ] with x hfg hf hg hadd hsum
    by_cases hx : x ∈ s
    · have hsum' := hsum hx
      have hadd' :
          extendByZeroFun (μ := μ) (p := p) (s := s) hs f x +
              extendByZeroFun (μ := μ) (p := p) (s := s) hs g x =
            (extendByZeroFun (μ := μ) (p := p) (s := s) hs f +
              extendByZeroFun (μ := μ) (p := p) (s := s) hs g) x := by
        simpa [Pi.add_apply] using hadd.symm
      calc
        extendByZeroFun (μ := μ) (p := p) (s := s) hs (f + g) x
            = s.indicator (fun x : α => (f + g) x) x := hfg
        _ = (f + g) x := by simp [Set.indicator_of_mem, hx]
        _ = f x + g x := hsum'
        _ = s.indicator (fun x : α => f x) x + s.indicator (fun x : α => g x) x := by
            simp [Set.indicator_of_mem, hx]
        _ = extendByZeroFun (μ := μ) (p := p) (s := s) hs f x +
              extendByZeroFun (μ := μ) (p := p) (s := s) hs g x := by
            simp [hf, hg]
        _ = (extendByZeroFun (μ := μ) (p := p) (s := s) hs f +
              extendByZeroFun (μ := μ) (p := p) (s := s) hs g) x := hadd'
    · have hadd' :
          extendByZeroFun (μ := μ) (p := p) (s := s) hs f x +
              extendByZeroFun (μ := μ) (p := p) (s := s) hs g x =
            (extendByZeroFun (μ := μ) (p := p) (s := s) hs f +
              extendByZeroFun (μ := μ) (p := p) (s := s) hs g) x := by
        simpa [Pi.add_apply] using hadd.symm
      calc
        extendByZeroFun (μ := μ) (p := p) (s := s) hs (f + g) x
            = s.indicator (fun x : α => (f + g) x) x := hfg
        _ = 0 := by simp [Set.indicator_of_notMem, hx]
        _ = extendByZeroFun (μ := μ) (p := p) (s := s) hs f x +
              extendByZeroFun (μ := μ) (p := p) (s := s) hs g x := by
            
            simp [Set.indicator_of_notMem, hx, hf, hg]
        _ = (extendByZeroFun (μ := μ) (p := p) (s := s) hs f +
              extendByZeroFun (μ := μ) (p := p) (s := s) hs g) x := hadd'
  map_smul' c f := by
    classical
    refine Lp.ext ?_
    have h_smul_restrict :
        (fun x : α => (c • f) x) =ᵐ[μ.restrict s] fun x : α => c • f x := by
      exact (Lp.coeFn_smul (μ := μ.restrict s) c f)
    have h_smul_on :
        ∀ᵐ x : α ∂μ, x ∈ s → (c • f) x = c • f x :=
      (ae_restrict_iff' (μ := μ) (s := s) hs).1 h_smul_restrict
    filter_upwards
      [ extendByZeroFun_coe (μ := μ) (p := p) (s := s) hs (c • f)
      , extendByZeroFun_coe (μ := μ) (p := p) (s := s) hs f
      , coeFn_smul c (extendByZeroFun (μ := μ) (p := p) (s := s) hs f)
      , h_smul_on
      ] with x hcf hf hsmul hsum
    by_cases hx : x ∈ s
    · have hsum' := hsum hx
      have hsmul' :
          c • extendByZeroFun (μ := μ) (p := p) (s := s) hs f x =
            (c • extendByZeroFun (μ := μ) (p := p) (s := s) hs f) x := by
        simpa [Pi.smul_apply] using hsmul.symm
      calc
        extendByZeroFun (μ := μ) (p := p) (s := s) hs (c • f) x
            = s.indicator (fun x : α => (c • f) x) x := hcf
        _ = (c • f) x := by simp [Set.indicator_of_mem, hx]
        _ = c • f x := hsum'
        _ = c • s.indicator (fun x : α => f x) x := by simp [Set.indicator_of_mem, hx]
        _ = c • extendByZeroFun (μ := μ) (p := p) (s := s) hs f x := by simp [hf]
        _ = (c • extendByZeroFun (μ := μ) (p := p) (s := s) hs f) x := hsmul'
    · have hsmul' :
          c • extendByZeroFun (μ := μ) (p := p) (s := s) hs f x =
            (c • extendByZeroFun (μ := μ) (p := p) (s := s) hs f) x := by
        simpa [Pi.smul_apply] using hsmul.symm
      calc
        extendByZeroFun (μ := μ) (p := p) (s := s) hs (c • f) x
            = s.indicator (fun x : α => (c • f) x) x := hcf
        _ = 0 := by simp [Set.indicator_of_notMem, hx]
        _ = (c • extendByZeroFun (μ := μ) (p := p) (s := s) hs f) x := by
            have hf0 :
                extendByZeroFun (μ := μ) (p := p) (s := s) hs f x = 0 := by
              simpa [Set.indicator_of_notMem, hx] using hf
            have hcx :
                (c • extendByZeroFun (μ := μ) (p := p) (s := s) hs f) x = 0 := by
              calc
                (c • extendByZeroFun (μ := μ) (p := p) (s := s) hs f) x =
                    c • extendByZeroFun (μ := μ) (p := p) (s := s) hs f x := by
                      simpa [Pi.smul_apply] using hsmul
                _ = 0 := by simp [hf0]
            simpa using hcx.symm

noncomputable def extendByZeroₗᵢ : Lp E p (μ.restrict s) →ₗᵢ[ℝ] Lp E p μ where
  toLinearMap := extendByZeroₗ (μ := μ) (p := p) (s := s) hs
  norm_map' f := by
    classical
    
    have hfi :
        MemLp (s.indicator fun x : α => f x) p μ :=
      (memLp_indicator_iff_restrict (μ := μ) (p := p) (s := s)
        (f := fun x : α => f x) hs).2 (Lp.memLp f)
    
    have hnorm_out :
        ‖extendByZeroₗ (μ := μ) (p := p) (s := s) hs f‖ =
          ENNReal.toReal (eLpNorm (s.indicator fun x : α => f x) p μ) := by
      dsimp [extendByZeroₗ, extendByZeroFun]
      simp [norm_toLp (f := s.indicator (fun x : α => f x)) hfi]
    
    have hnorm_restrict :
        eLpNorm (s.indicator fun x : α => f x) p μ =
          eLpNorm (fun x : α => f x) p (μ.restrict s) := by
      simpa using (eLpNorm_indicator_eq_eLpNorm_restrict (μ := μ) (p := p) (s := s)
        (f := fun x : α => f x) hs)
    
    simp [hnorm_out, hnorm_restrict, norm_def]

lemma extendByZeroₗᵢ_ae_eq (f : Lp E p (μ.restrict s)) :
    ((extendByZeroₗᵢ (μ := μ) (p := p) (s := s) hs) f : α → E) =ᵐ[μ]
      s.indicator fun x : α => f x := by
  
  simpa [extendByZeroₗᵢ, extendByZeroₗ] using
    (extendByZeroFun_coe (μ := μ) (p := p) (s := s) hs f)

end

end Lp

end MeasureTheory
end

section

namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean
namespace L2Compactness

open scoped ENNReal MeasureTheory Topology Convolution Pointwise
open MeasureTheory Set

noncomputable section

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma tsupport_indicator_subset_closure (s : Set E) (f : E → ℝ) :
    tsupport (s.indicator f) ⊆ closure s := by
  
  
  simpa [tsupport] using closure_mono (Set.support_indicator_subset (s := s) (f := f))

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma hasCompactSupport_indicator_of_isCompact (s : Set E) (hs : IsCompact s) (f : E → ℝ) :
    HasCompactSupport (s.indicator f) := by
  have hs_closed : IsClosed s := hs.isClosed
  
  refine hs.of_isClosed_subset (isClosed_tsupport _) ?_
  have : tsupport (s.indicator f) ⊆ closure s := tsupport_indicator_subset_closure (E := E) s f
  simpa [hs_closed.closure_eq] using this

end

section Volume

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

local instance instMeasurableSpaceSmoothing1 : MeasurableSpace E := borel E
local instance instBorelSpaceSmoothing1 : BorelSpace E := ⟨rfl⟩
local instance instOpensMeasurableSpaceSmoothing1 : OpensMeasurableSpace E := by
  infer_instance

variable {K : Set E}

def extendByZeroFun (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) : E → ℝ :=
  K.indicator fun x : E => u x

lemma hasCompactSupport_extendByZeroFun (hK : IsCompact K)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) :
    HasCompactSupport (extendByZeroFun (K := K) u) := by
  classical
  
  simpa [extendByZeroFun] using
    (hasCompactSupport_indicator_of_isCompact (E := E) (s := K) hK (f := fun x => u x))

noncomputable def extendByZeroL2 (hKm : MeasurableSet K)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) :
    (E →₂[(volume : Measure E)] ℝ) := by
  classical
  have hu : MeasureTheory.MemLp (fun x : E => u x) (2 : ℝ≥0∞) (volume.restrict K) :=
    MeasureTheory.Lp.memLp u
  have hm :
      MeasureTheory.MemLp (extendByZeroFun (K := K) u) (2 : ℝ≥0∞) (volume : Measure E) := by
    simpa [extendByZeroFun] using
      (MeasureTheory.memLp_indicator_iff_restrict (μ := (volume : Measure E)) (p := (2 : ℝ≥0∞))
          (s := K) (f := fun x : E => u x) hKm).2 hu
  exact hm.toLp (extendByZeroFun (K := K) u)

lemma extendByZeroL2_ae_eq (hKm : MeasurableSet K)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) :
    (extendByZeroL2 (E := E) (K := K) hKm u : E → ℝ) =ᵐ[(volume : Measure E)]
      extendByZeroFun (E := E) (K := K) u := by
  classical
  simp [extendByZeroL2, MeasureTheory.MemLp.coeFn_toLp]

lemma extendByZeroL2_eq_extendByZeroₗᵢ (hKm : MeasurableSet K)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) :
    extendByZeroL2 (E := E) (K := K) hKm u =
      (MeasureTheory.Lp.extendByZeroₗᵢ (μ := (volume : Measure E)) (E := ℝ) (p := (2 : ℝ≥0∞))
        (s := K) hKm) u := by
  classical
  let : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  refine MeasureTheory.Lp.ext ?_
  have h1 :
      (extendByZeroL2 (E := E) (K := K) hKm u : E → ℝ) =ᵐ[(volume : Measure E)]
        extendByZeroFun (E := E) (K := K) u :=
    extendByZeroL2_ae_eq (E := E) (K := K) hKm u
  have h2 :
      ((MeasureTheory.Lp.extendByZeroₗᵢ (μ := (volume : Measure E)) (E := ℝ) (p := (2 : ℝ≥0∞))
        (s := K) hKm) u : E → ℝ) =ᵐ[(volume : Measure E)]
        extendByZeroFun (E := E) (K := K) u := by
    exact
      (MeasureTheory.Lp.extendByZeroₗᵢ_ae_eq (μ := (volume : Measure E)) (E := ℝ)
        (p := (2 : ℝ≥0∞)) (s := K) hKm u)
  exact h1.trans h2.symm

lemma norm_extendByZeroL2 (hKm : MeasurableSet K)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) :
    ‖extendByZeroL2 (E := E) (K := K) hKm u‖ = ‖u‖ := by
  classical
  let : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  calc
    ‖extendByZeroL2 (E := E) (K := K) hKm u‖ =
        ‖(MeasureTheory.Lp.extendByZeroₗᵢ (μ := (volume : Measure E)) (E := ℝ) (p := (2 : ℝ≥0∞))
          (s := K) hKm) u‖ := by
          simp [extendByZeroL2_eq_extendByZeroₗᵢ (E := E) (K := K) hKm u]
    _ = ‖u‖ :=
      (MeasureTheory.Lp.extendByZeroₗᵢ (μ := (volume : Measure E)) (E := ℝ) (p := (2 : ℝ≥0∞))
        (s := K) hKm).norm_map u
variable (ψ : E → ℝ)

def smoothFun (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) : E → ℝ :=
  (extendByZeroFun (K := K) u) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)] ψ

lemma continuous_smoothFun
    (hKm : MeasurableSet K) (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) :
    Continuous (smoothFun (K := K) ψ u) := by
  
  
  have hf_memLp :
      MeasureTheory.MemLp (extendByZeroFun (K := K) u)
        (2 : ℝ≥0∞) (volume : Measure E) := by
    have hu : MeasureTheory.MemLp (fun x : E => u x) (2 : ℝ≥0∞) (volume.restrict K) :=
      MeasureTheory.Lp.memLp u
    simpa [extendByZeroFun] using
      (MeasureTheory.memLp_indicator_iff_restrict (μ := (volume : Measure E)) (p := (2 : ℝ≥0∞))
          (s := K) (f := fun x : E => u x) hKm).2 hu
  have hf_loc :
      MeasureTheory.LocallyIntegrable (extendByZeroFun (K := K) u)
        (volume : Measure E) := by
    have h12 : (1 : ℝ≥0∞) ≤ (2 : ℝ≥0∞) := by norm_num
    exact hf_memLp.locallyIntegrable h12
  simpa [smoothFun] using
    (hψcs.continuous_convolution_right
      («L» := ContinuousLinearMap.lsmul ℝ ℝ)
      (μ := (volume : Measure E)) hf_loc hψc)

lemma hasCompactSupport_smoothFun (hK : IsCompact K) (hψcs : HasCompactSupport ψ)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) :
    HasCompactSupport (smoothFun (K := K) ψ u) := by
  have hf : HasCompactSupport (extendByZeroFun (K := K) u) :=
    hasCompactSupport_extendByZeroFun (K := K) hK u
  simpa [smoothFun] using
    (hf.convolution («L» := ContinuousLinearMap.lsmul ℝ ℝ)
      (μ := (volume : Measure E)) hψcs)

lemma support_smoothFun_subset_add_tsupport
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) :
    Function.support (smoothFun (E := E) (K := K) ψ u) ⊆ K + tsupport ψ := by
  classical
  have hsupp :
      Function.support (smoothFun (E := E) (K := K) ψ u) ⊆
        Function.support (extendByZeroFun (E := E) (K := K) u) + Function.support ψ := by
    simpa [smoothFun] using
      (support_convolution_subset («L» := ContinuousLinearMap.lsmul ℝ ℝ) (μ := (volume : Measure E))
        (f := extendByZeroFun (E := E) (K := K) u) (g := ψ))
  have h1 : Function.support (extendByZeroFun (E := E) (K := K) u) ⊆ K := by
    simp [extendByZeroFun]
  have h2 : Function.support ψ ⊆ tsupport ψ := by
    simpa [tsupport] using (subset_closure : Function.support ψ ⊆ closure (Function.support ψ))
  exact hsupp.trans (add_subset_add h1 h2)

noncomputable def smoothL2 (hK : IsCompact K) (hKm : MeasurableSet K) (hψc : Continuous ψ)
    (hψcs : HasCompactSupport ψ)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) : (E →₂[(volume : Measure E)] ℝ) :=
  let hs : HasCompactSupport (smoothFun (K := K) ψ u) :=
    hasCompactSupport_smoothFun (K := K) ψ hK hψcs u
  let hm : MeasureTheory.MemLp (smoothFun (K := K) ψ u) (2 : ℝ≥0∞) (volume : Measure E) := by
    have hc : Continuous (smoothFun (K := K) ψ u) := continuous_smoothFun (K := K) ψ hKm hψc hψcs u
    exact hc.memLp_of_hasCompactSupport (μ := (volume : Measure E)) hs
  hm.toLp (smoothFun (K := K) ψ u)

lemma smoothL2_ae_eq (hK : IsCompact K) (hKm : MeasurableSet K) (hψc : Continuous ψ)
    (hψcs : HasCompactSupport ψ)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) :
    (smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u : E → ℝ) =ᵐ[(volume : Measure E)]
      smoothFun (E := E) (K := K) ψ u := by
  classical
  simp [smoothL2, MeasureTheory.MemLp.coeFn_toLp]
end Volume

end

end L2Compactness
end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov
end

section

namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean

open scoped ENNReal MeasureTheory
open MeasureTheory

section

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local instance instMeasurableSpaceH1 : MeasurableSpace E := borel E
local instance instBorelSpaceH1 : BorelSpace E := ⟨rfl⟩
local instance instOpensMeasurableSpaceH1 : OpensMeasurableSpace E := by infer_instance

variable (μ : Measure E) [IsFiniteMeasureOnCompacts μ]

abbrev L2ℝ : Type _ := ↥(E →₂[μ] ℝ)

abbrev L2E : Type _ := ↥(E →₂[μ] E)

abbrev H1Target : Type _ := L2ℝ (μ := μ) × L2E (μ := μ)

def C1c : Submodule ℝ (E → ℝ) where
  carrier := {f | ContDiff ℝ 1 f ∧ HasCompactSupport f}
  zero_mem' := by
    refine ⟨contDiff_const, ?_⟩
    simpa using (HasCompactSupport.zero : HasCompactSupport (fun _ : E => (0 : ℝ)))
  add_mem' := by
    intro f g hf hg
    refine ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  smul_mem' := by
    intro c f hf
    refine ⟨hf.1.const_smul c, ?_⟩
    
    exact (HasCompactSupport.smul_left (f := fun _ : E => c) hf.2)

noncomputable def grad (f : E → ℝ) : E → E :=
  fun x => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x)

lemma continuous_grad {f : E → ℝ} (hf : ContDiff ℝ 1 f) : Continuous (grad (E := E) f) := by
  have hcont : Continuous (fderiv ℝ f) := hf.continuous_fderiv one_ne_zero
  have : Continuous fun x => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x) :=
    (InnerProductSpace.toDual ℝ E).symm.continuous.comp hcont
  exact this

lemma hasCompactSupport_grad {f : E → ℝ} (hf : HasCompactSupport f) :
    HasCompactSupport (grad (E := E) f) := by
  
  have hf' : HasCompactSupport (fderiv ℝ f) := hf.fderiv ℝ
  
  exact
    (HasCompactSupport.comp_left (f := fderiv ℝ f) (g := (InnerProductSpace.toDual ℝ E).symm)
      hf' (by simp))

omit [CompleteSpace E] in
lemma memLp_of_mem_C1c {f : E → ℝ} (hf : f ∈ C1c (E := E)) : MemLp f 2 μ := by
  exact (hf.1.continuous.memLp_of_hasCompactSupport (μ := μ) (p := (2 : ℝ≥0∞)) hf.2)

lemma memLp_grad_of_mem_C1c {f : E → ℝ} (hf : f ∈ C1c (E := E)) :
    MemLp (grad (E := E) f) 2 μ := by
  have hcont : Continuous (grad (E := E) f) := continuous_grad (E := E) (f := f) hf.1
  have hcs : HasCompactSupport (grad (E := E) f) := hasCompactSupport_grad (E := E) (f := f) hf.2
  exact hcont.memLp_of_hasCompactSupport (μ := μ) (p := (2 : ℝ≥0∞)) hcs

noncomputable def toL2 (f : ↥(C1c (E := E))) : L2ℝ (μ := μ) :=
  (memLp_of_mem_C1c (μ := μ) (E := E) f.2).toLp f.1

noncomputable def toL2Grad (f : ↥(C1c (E := E))) : L2E (μ := μ) :=
  (memLp_grad_of_mem_C1c (μ := μ) (E := E) f.2).toLp (grad (E := E) f.1)

omit [CompleteSpace E] in
lemma toL2_add (f g : ↥(C1c (E := E))) :
    toL2 (μ := μ) (E := E) (f + g) =
      toL2 (μ := μ) (E := E) f + toL2 (μ := μ) (E := E) g := by
  apply Lp.ext
  have hf : (toL2 (μ := μ) (E := E) f : E → ℝ) =ᵐ[μ] f.1 :=
    (memLp_of_mem_C1c (μ := μ) (E := E) f.2).coeFn_toLp
  have hg : (toL2 (μ := μ) (E := E) g : E → ℝ) =ᵐ[μ] g.1 :=
    (memLp_of_mem_C1c (μ := μ) (E := E) g.2).coeFn_toLp
  have hfg : (toL2 (μ := μ) (E := E) (f + g) : E → ℝ) =ᵐ[μ] (f.1 + g.1) :=
    (memLp_of_mem_C1c (μ := μ) (E := E) (f + g).2).coeFn_toLp
  
  refine hfg.trans ?_
  filter_upwards [Lp.coeFn_add (toL2 (μ := μ) (E := E) f) (toL2 (μ := μ) (E := E) g), hf, hg]
    with x hxadd hxf hxg
  
  calc
    f.1 x + g.1 x =
        (toL2 (μ := μ) (E := E) f : E → ℝ) x +
          (toL2 (μ := μ) (E := E) g : E → ℝ) x := by
      simp [hxf, hxg]
    _ = ((toL2 (μ := μ) (E := E) f + toL2 (μ := μ) (E := E) g : L2ℝ (μ := μ)) : E → ℝ) x := by
      simpa [Pi.add_apply] using hxadd.symm

omit [CompleteSpace E] in
lemma toL2_smul (c : ℝ) (f : ↥(C1c (E := E))) :
    toL2 (μ := μ) (E := E) (c • f) = c • toL2 (μ := μ) (E := E) f := by
  apply Lp.ext
  have hf : (toL2 (μ := μ) (E := E) f : E → ℝ) =ᵐ[μ] f.1 :=
    (memLp_of_mem_C1c (μ := μ) (E := E) f.2).coeFn_toLp
  have hcf : (toL2 (μ := μ) (E := E) (c • f) : E → ℝ) =ᵐ[μ] (c • f.1) :=
    (memLp_of_mem_C1c (μ := μ) (E := E) (c • f).2).coeFn_toLp
  refine hcf.trans ?_
  filter_upwards [Lp.coeFn_smul c (toL2 (μ := μ) (E := E) f), hf] with x hxsmul hxf
  simp [Pi.smul_apply, hxsmul, hxf]

noncomputable def toL2Linear : ↥(C1c (E := E)) →ₗ[ℝ] L2ℝ (μ := μ) where
  toFun := toL2 (μ := μ) (E := E)
  map_add' := by exact toL2_add (μ := μ) (E := E)
  map_smul' := by exact toL2_smul (μ := μ) (E := E)

lemma toL2Grad_add (f g : ↥(C1c (E := E))) :
    toL2Grad (μ := μ) (E := E) (f + g) =
      toL2Grad (μ := μ) (E := E) f + toL2Grad (μ := μ) (E := E) g := by
  apply Lp.ext
  have hf : (toL2Grad (μ := μ) (E := E) f : E → E) =ᵐ[μ] grad (E := E) f.1 :=
    (memLp_grad_of_mem_C1c (μ := μ) (E := E) f.2).coeFn_toLp
  have hg : (toL2Grad (μ := μ) (E := E) g : E → E) =ᵐ[μ] grad (E := E) g.1 :=
    (memLp_grad_of_mem_C1c (μ := μ) (E := E) g.2).coeFn_toLp
  have hfg :
      (toL2Grad (μ := μ) (E := E) (f + g) : E → E) =ᵐ[μ] grad (E := E) (f.1 + g.1) :=
    (memLp_grad_of_mem_C1c (μ := μ) (E := E) (f + g).2).coeFn_toLp
  refine hfg.trans ?_
  filter_upwards [Lp.coeFn_add (toL2Grad (μ := μ) (E := E) f) (toL2Grad (μ := μ) (E := E) g), hf,
    hg] with x hxadd hxf hxg
  have hdf : DifferentiableAt ℝ f.1 x :=
    (f.2.1.differentiable one_ne_zero).differentiableAt
  have hdg : DifferentiableAt ℝ g.1 x :=
    (g.2.1.differentiable one_ne_zero).differentiableAt
  
  have hgrad :
      grad (E := E) (f.1 + g.1) x = grad (E := E) f.1 x + grad (E := E) g.1 x := by
    simp [grad, fderiv_add hdf hdg, map_add]
  calc
    grad (E := E) (f.1 + g.1) x = grad (E := E) f.1 x + grad (E := E) g.1 x := hgrad
    _ =
        (toL2Grad (μ := μ) (E := E) f : E → E) x +
          (toL2Grad (μ := μ) (E := E) g : E → E) x := by
        simp [hxf, hxg]
    _ = ((toL2Grad (μ := μ) (E := E) f +
            toL2Grad (μ := μ) (E := E) g : L2E (μ := μ)) :
            E → E) x := by
        simpa [Pi.add_apply] using hxadd.symm

lemma toL2Grad_smul (c : ℝ) (f : ↥(C1c (E := E))) :
    toL2Grad (μ := μ) (E := E) (c • f) = c • toL2Grad (μ := μ) (E := E) f := by
  apply Lp.ext
  have hf : (toL2Grad (μ := μ) (E := E) f : E → E) =ᵐ[μ] grad (E := E) f.1 :=
    (memLp_grad_of_mem_C1c (μ := μ) (E := E) f.2).coeFn_toLp
  have hcf :
      (toL2Grad (μ := μ) (E := E) (c • f) : E → E) =ᵐ[μ] grad (E := E) (c • f.1) :=
    (memLp_grad_of_mem_C1c (μ := μ) (E := E) (c • f).2).coeFn_toLp
  refine hcf.trans ?_
  filter_upwards [Lp.coeFn_smul c (toL2Grad (μ := μ) (E := E) f), hf] with x hxsmul hxf
  have hdf : DifferentiableAt ℝ f.1 x :=
    (f.2.1.differentiable one_ne_zero).differentiableAt
  have hgrad : grad (E := E) (c • f.1) x = c • grad (E := E) f.1 x := by
    simp [grad, fderiv_const_smul hdf, map_smul]
  calc
    grad (E := E) (c • f.1) x = c • grad (E := E) f.1 x := hgrad
    _ = c • (toL2Grad (μ := μ) (E := E) f : E → E) x := by
      simp [hxf]
    _ = ((c • toL2Grad (μ := μ) (E := E) f : L2E (μ := μ)) : E → E) x := by
      
      simpa [Pi.smul_apply] using hxsmul.symm

noncomputable def toL2GradLinear : ↥(C1c (E := E)) →ₗ[ℝ] L2E (μ := μ) where
  toFun := toL2Grad (μ := μ) (E := E)
  map_add' := by exact toL2Grad_add (μ := μ) (E := E)
  map_smul' := by exact toL2Grad_smul (μ := μ) (E := E)

noncomputable def graph : ↥(C1c (E := E)) →ₗ[ℝ] H1Target (μ := μ) :=
  (toL2Linear (μ := μ) (E := E)).prod (toL2GradLinear (μ := μ) (E := E))

noncomputable def h1 : Submodule ℝ (H1Target (μ := μ)) :=
  (LinearMap.range (graph (μ := μ) (E := E))).topologicalClosure

noncomputable def h1ToL2 : (↥(h1 (μ := μ) (E := E))) →L[ℝ] L2ℝ (μ := μ) :=
  (ContinuousLinearMap.fst ℝ (L2ℝ (μ := μ)) (L2E (μ := μ))).comp
    (Submodule.subtypeL (h1 (μ := μ) (E := E)))

noncomputable def h1ToL2Grad : (↥(h1 (μ := μ) (E := E))) →L[ℝ] L2E (μ := μ) :=
  (ContinuousLinearMap.snd ℝ (L2ℝ (μ := μ)) (L2E (μ := μ))).comp
    (Submodule.subtypeL (h1 (μ := μ) (E := E)))

end

end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov
end

section

namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean

open scoped ENNReal MeasureTheory Topology
open MeasureTheory

section Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local instance instMeasurableSpaceTranslation : MeasurableSpace E := borel E
local instance instBorelSpaceTranslation : BorelSpace E := ⟨rfl⟩
local instance instMeasurableAddTranslation : MeasurableAdd E := by
  infer_instance

variable (μ : Measure E) [μ.IsAddRightInvariant]

noncomputable def translateL2 {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (a : E) :
    (E →₂[μ] F) →ₗᵢ[ℝ] (E →₂[μ] F) := by
  classical
  simpa using
    (MeasureTheory.Lp.compMeasurePreservingₗᵢ (𝕜 := ℝ) (E := F) (p := (2 : ENNReal))
      (μ := μ) (μb := μ) (f := fun x : E => x + a) (MeasureTheory.measurePreserving_add_right μ a))

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma translateL2_ae_eq {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (a : E)
    (g : E →₂[μ] F) :
    (translateL2 (μ := μ) (F := F) a g : E → F) =ᵐ[μ] fun x => (g : E → F) (x + a) := by
  classical
  
  exact
    (MeasureTheory.Lp.coeFn_compMeasurePreserving (g := (g : MeasureTheory.Lp F (2 : ENNReal) μ))
      (hf := MeasureTheory.measurePreserving_add_right μ a))

variable [IsFiniteMeasureOnCompacts μ]

end Measure

end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov
end

section

namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean
namespace L2Compactness

open scoped ENNReal MeasureTheory Topology Convolution
open MeasureTheory Set

noncomputable section

section Volume

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

local instance instMeasurableSpaceApproximation : MeasurableSpace E := borel E
local instance instBorelSpaceApproximation : BorelSpace E := ⟨rfl⟩
local instance instOpensMeasurableSpaceApproximation : OpensMeasurableSpace E := by
  infer_instance
local instance instMeasurableAddApproximation : MeasurableAdd E := by
  infer_instance
local instance instMeasurableNegApproximation : MeasurableNeg E := by
  infer_instance

variable {K : Set E} (hK : IsCompact K) (hKm : MeasurableSet K)
variable (ψ : E → ℝ)

noncomputable def kernelMeasure : Measure E :=
  (volume : Measure E).withDensity fun x => ENNReal.ofReal (ψ x)

lemma kernelMeasure_univ (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ) (hψ0 : ∀ x, 0 ≤ ψ x)
    (hψint : ∫ x, ψ x ∂(volume : Measure E) = 1) :
    kernelMeasure (E := E) ψ Set.univ = 1 := by
  have hψi : MeasureTheory.Integrable ψ (volume : Measure E) :=
    Continuous.integrable_of_hasCompactSupport (μ := (volume : Measure E)) hψc hψcs
  have hψae : (MeasureTheory.ae (volume : Measure E)).EventuallyLE 0 ψ :=
    Filter.Eventually.of_forall hψ0
  have hlin :
      (∫⁻ x, ENNReal.ofReal (ψ x) ∂(volume : Measure E)) =
        ENNReal.ofReal (∫ x, ψ x ∂(volume : Measure E)) := by
    symm
    exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hψi hψae
  
  have hwd :
      kernelMeasure (E := E) ψ Set.univ =
        ∫⁻ x, ENNReal.ofReal (ψ x) ∂(volume : Measure E) := by
    simp [kernelMeasure, MeasureTheory.withDensity_apply, MeasurableSet.univ]
  
  simpa [hψint] using (hwd.trans hlin)

lemma isProbabilityMeasure_kernelMeasure
    (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ)
    (hψ0 : ∀ x, 0 ≤ ψ x)
    (hψint : ∫ x, ψ x ∂(volume : Measure E) = 1) :
    MeasureTheory.IsProbabilityMeasure (kernelMeasure (E := E) ψ) :=
  ⟨kernelMeasure_univ (E := E) (ψ := ψ) hψc hψcs hψ0 hψint⟩

lemma integral_kernelMeasure_eq_integral_smul (hψc : Continuous ψ) (hψ0 : ∀ x, 0 ≤ ψ x)
    (g : E → ℝ) :
    (∫ x, g x ∂kernelMeasure (E := E) ψ) =
      ∫ x, (ψ x) • (g x) ∂(volume : Measure E) := by
  have hmeas : Measurable fun x => ENNReal.ofReal (ψ x) :=
    (hψc.measurable.ennreal_ofReal : Measurable fun x => ENNReal.ofReal (ψ x))
  have htop :
      (MeasureTheory.ae (volume : Measure E)).Eventually
        (fun x => ENNReal.ofReal (ψ x) < (⊤ : ℝ≥0∞)) :=
    Filter.Eventually.of_forall (fun _ => by simp)
  have hwd :=
    (integral_withDensity_eq_integral_toReal_smul (μ := (volume : Measure E))
      (f := fun x => ENNReal.ofReal (ψ x)) hmeas htop g)
  have hwd' :
      (∫ x, g x ∂kernelMeasure (E := E) ψ) =
        ∫ x, (ENNReal.ofReal (ψ x)).toReal • (g x) ∂(volume : Measure E) := by
    simpa [kernelMeasure] using hwd
  
  refine hwd'.trans ?_
  refine integral_congr_ae ?_
  refine ae_of_all _ (fun x => ?_)
  have hx : (ENNReal.ofReal (ψ x)).toReal = ψ x :=
    ENNReal.toReal_ofReal (hψ0 x)
  
  simp [hx]

lemma integral_kernelMeasure_eq_integral_mul (hψc : Continuous ψ) (hψ0 : ∀ x, 0 ≤ ψ x)
    (g : E → ℝ) :
    (∫ x, g x ∂kernelMeasure (E := E) ψ) =
      ∫ x, (ψ x) * (g x) ∂(volume : Measure E) := by
  simpa [smul_eq_mul] using integral_kernelMeasure_eq_integral_smul (E := E) (ψ := ψ) hψc hψ0 g

lemma smoothFun_eq_integral_kernelMeasure (hψc : Continuous ψ) (hψ0 : ∀ x, 0 ≤ ψ x)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) (x : E) :
    smoothFun (E := E) (K := K) ψ u x =
      ∫ t, extendByZeroFun (E := E) (K := K) u (x - t) ∂kernelMeasure (E := E) ψ := by
  have hconv :
      smoothFun (E := E) (K := K) ψ u x =
        ∫ t, (extendByZeroFun (E := E) (K := K) u) (x - t) • (ψ t) ∂(volume : Measure E) := by
    simp [smoothFun, convolution_lsmul_swap]
  have hconv' :
      smoothFun (E := E) (K := K) ψ u x =
        ∫ t, (ψ t) * extendByZeroFun (E := E) (K := K) u (x - t) ∂(volume : Measure E) := by
    refine hconv.trans ?_
    refine integral_congr_ae ?_
    refine ae_of_all _ (fun t => ?_)
    
    change
      extendByZeroFun (E := E) (K := K) u (x - t) • ψ t =
        ψ t * extendByZeroFun (E := E) (K := K) u (x - t)
    rw [smul_eq_mul]
    simp [mul_comm]
  
  have hwd :
      (∫ t, extendByZeroFun (E := E) (K := K) u (x - t) ∂kernelMeasure (E := E) ψ) =
        ∫ t, (ψ t) * extendByZeroFun (E := E) (K := K) u (x - t) ∂(volume : Measure E) := by
    exact integral_kernelMeasure_eq_integral_mul (E := E) (ψ := ψ) hψc hψ0
      (g := fun t => extendByZeroFun (E := E) (K := K) u (x - t))
  exact hconv'.trans hwd.symm

lemma sq_integral_le_integral_sq_of_isProbabilityMeasure {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [MeasureTheory.IsProbabilityMeasure μ] (f : α → ℝ)
    (hf : MeasureTheory.MemLp f 2 μ) :
    (∫ x, f x ∂μ) ^ 2 ≤ ∫ x, (f x) ^ 2 ∂μ := by
  have hvar := ProbabilityTheory.variance_nonneg (X := f) μ
  have hvar' :
      0 ≤ (∫ x, (f x) ^ 2 ∂μ) - (∫ x, f x ∂μ) ^ 2 := by
    simpa [ProbabilityTheory.variance_eq_sub (μ := μ) hf] using hvar
  linarith

lemma norm_sq_eq_integral_sq (v : (E →₂[(volume : Measure E)] ℝ)) :
    ‖v‖ ^ 2 = ∫ x, (v x) ^ 2 ∂(volume : Measure E) := by
  have hn : ‖v‖ ^ 2 = RCLike.re (inner ℝ v v) :=
    norm_sq_eq_re_inner (𝕜 := ℝ) v
  
  rw [hn]
  
  rw [MeasureTheory.L2.inner_def (𝕜 := ℝ) (μ := (volume : Measure E)) v v]
  
  simp [pow_two]

lemma norm_sq_translateL2_sub_extendByZeroL2_eq_integral_sq (t : E)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) :
    ‖(translateL2 (μ := (volume : Measure E)) (-t))
        (extendByZeroL2 (E := E) (K := K) hKm u)
        - extendByZeroL2 (E := E) (K := K) hKm u‖ ^ 2 =
      ∫ x,
        (extendByZeroFun (E := E) (K := K) u (x - t) - extendByZeroFun (E := E) (K := K) u x) ^ 2
          ∂(volume : Measure E) := by
  classical
  let F : (E →₂[(volume : Measure E)] ℝ) := extendByZeroL2 (E := E) (K := K) hKm u
  let f : E → ℝ := extendByZeroFun (E := E) (K := K) u
  have hF_ae : (F : E → ℝ) =ᵐ[(volume : Measure E)] f :=
    extendByZeroL2_ae_eq (E := E) (K := K) (hKm := hKm) u
  
  have hF_shift :
      (fun x : E => (F : E → ℝ) (x - t)) =ᵐ[(volume : Measure E)] fun x => f (x - t) := by
    have hmp :
        MeasureTheory.MeasurePreserving (fun x : E => x - t)
          (volume : Measure E) (volume : Measure E) :=
      MeasureTheory.measurePreserving_sub_right (μ := (volume : Measure E)) t
    exact (hmp.quasiMeasurePreserving.ae_eq_comp hF_ae)
  
  have htrans :
      ((translateL2 (μ := (volume : Measure E)) (-t)) F : E → ℝ) =ᵐ[(volume : Measure E)]
        fun x => (F : E → ℝ) (x - t) := by
    simpa [sub_eq_add_neg] using (translateL2_ae_eq (μ := (volume : Measure E)) (-t) F)
  have htrans' :
      ((translateL2 (μ := (volume : Measure E)) (-t)) F : E → ℝ) =ᵐ[(volume : Measure E)]
        fun x => f (x - t) := by
    exact htrans.trans hF_shift
  have hdiff :
      (fun x => ((translateL2 (μ := (volume : Measure E)) (-t)) F - F) x) =ᵐ[(volume : Measure E)]
        fun x => f (x - t) - f x := by
    filter_upwards [MeasureTheory.Lp.coeFn_sub ((translateL2 (μ := (volume : Measure E)) (-t)) F) F,
      htrans', hF_ae] with x hxsub hx1 hx2
    
    have hxsub' :
        ((translateL2 (μ := (volume : Measure E)) (-t)) F - F) x =
          ((translateL2 (μ := (volume : Measure E)) (-t)) F) x - F x := by
      simpa using hxsub
    
    rw [hxsub', hx1, hx2]
  have hcalc :
      ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ^ 2 =
        ∫ x, (f (x - t) - f x) ^ 2 ∂(volume : Measure E) := by
    have h1 :=
      norm_sq_eq_integral_sq (E := E) (v := ((translateL2 (μ := (volume : Measure E)) (-t)) F - F))
    have h2 :
        ∫ x, (((translateL2 (μ := (volume : Measure E)) (-t)) F - F) x) ^ 2
            ∂(volume : Measure E) =
          ∫ x, (f (x - t) - f x) ^ 2 ∂(volume : Measure E) := by
      refine MeasureTheory.integral_congr_ae ?_
      exact hdiff.pow_const 2
    exact h1.trans h2
  simpa [F, f] using hcalc

lemma kernelMeasure_le_smul_volume (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ)
    (hψ0 : ∀ x, 0 ≤ ψ x) :
    ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ kernelMeasure (E := E) ψ ≤ c • (volume : Measure E) := by
  classical
  obtain ⟨C, hC⟩ := hψcs.exists_bound_of_continuous hψc
  refine ⟨ENNReal.ofReal C, by simp, ?_⟩
  refine (Measure.le_iff).2 ?_
  intro s hs
  have hC0 : 0 ≤ C := le_trans (norm_nonneg (ψ 0)) (hC 0)
  have hψle : ∀ x, ENNReal.ofReal (ψ x) ≤ ENNReal.ofReal C := by
    intro x
    have hx : ψ x ≤ C := by
      have hx' : ‖ψ x‖ ≤ C := hC x
      
      simpa [Real.norm_eq_abs, abs_of_nonneg (hψ0 x)] using hx'
    exact ENNReal.ofReal_le_ofReal hx
  
  simp only [kernelMeasure, MeasureTheory.withDensity_apply, hs]
  have hle :
      (∫⁻ x in s, ENNReal.ofReal (ψ x) ∂(volume : Measure E)) ≤
        ∫⁻ x in s, ENNReal.ofReal C ∂(volume : Measure E) := by
    refine MeasureTheory.lintegral_mono ?_
    intro x
    exact hψle x
  refine hle.trans ?_
  simp

lemma smoothFun_sub_extendByZeroFun_sq_le_integral_sq
    (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ)
    (hψ0 : ∀ x, 0 ≤ ψ x) (hψint : ∫ x, ψ x ∂(volume : Measure E) = 1) (hKm : MeasurableSet K)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) (x : E) :
    (smoothFun (E := E) (K := K) ψ u x - extendByZeroFun (E := E) (K := K) u x) ^ 2 ≤
      ∫ t,
        (extendByZeroFun (E := E) (K := K) u (x - t) - extendByZeroFun (E := E) (K := K) u x) ^ 2
          ∂kernelMeasure (E := E) ψ := by
  classical
  let μ : Measure E := kernelMeasure (E := E) ψ
  have : MeasureTheory.IsProbabilityMeasure μ :=
    isProbabilityMeasure_kernelMeasure (E := E) (ψ := ψ) hψc hψcs hψ0 hψint
  have : MeasureTheory.IsFiniteMeasure μ := by infer_instance
  rcases kernelMeasure_le_smul_volume (E := E) (ψ := ψ) hψc hψcs hψ0 with ⟨c, hc_top, hμle⟩
  let f : E → ℝ := extendByZeroFun (E := E) (K := K) u
  have hf_vol : MeasureTheory.MemLp f (2 : ℝ≥0∞) (volume : Measure E) := by
    
    let F : (E →₂[(volume : Measure E)] ℝ) := extendByZeroL2 (E := E) (K := K) hKm u
    have hF : MeasureTheory.MemLp (fun x : E => (F : E → ℝ) x) (2 : ℝ≥0∞) (volume : Measure E) :=
      MeasureTheory.Lp.memLp F
    have hF_ae : (fun x : E => (F : E → ℝ) x) =ᵐ[(volume : Measure E)] f :=
      extendByZeroL2_ae_eq (E := E) (K := K) (hKm := hKm) u
    exact (MeasureTheory.memLp_congr_ae hF_ae).1 hF
  have hmp :
      MeasureTheory.MeasurePreserving (fun t : E => x - t)
        (volume : Measure E) (volume : Measure E) := by
    
    have hneg :
        MeasureTheory.MeasurePreserving (Neg.neg : E → E)
          (volume : Measure E) (volume : Measure E) :=
      (volume : Measure E).measurePreserving_neg
    have hadd :
        MeasureTheory.MeasurePreserving (fun y : E => y + x)
          (volume : Measure E) (volume : Measure E) :=
      MeasureTheory.measurePreserving_add_right
        (μ := (volume : Measure E)) x
    have hcomp : ((fun y : E => y + x) ∘ fun t : E => -t) = fun t : E => x - t := by
      funext t
      simp [sub_eq_add_neg, add_comm]
    have := hadd.comp hneg
    rwa [hcomp] at this
  have hf_shift_vol :
      MeasureTheory.MemLp (fun t : E => f (x - t))
        (2 : ℝ≥0∞) (volume : Measure E) :=
    hf_vol.comp_measurePreserving hmp
  have hf_shift :
      MeasureTheory.MemLp (fun t : E => f (x - t))
        (2 : ℝ≥0∞) μ := by
    exact MeasureTheory.MemLp.of_measure_le_smul
      (μ := (volume : Measure E)) (μ' := μ) (c := c)
      hc_top hμle hf_shift_vol
  have hf_const : MeasureTheory.MemLp (fun _ : E => f x) (2 : ℝ≥0∞) μ :=
    MeasureTheory.memLp_const (μ := μ) (c := f x)
  have hg : MeasureTheory.MemLp (fun t : E => f (x - t) - f x) (2 : ℝ≥0∞) μ :=
    hf_shift.sub hf_const
  have hsmooth :
      smoothFun (E := E) (K := K) ψ u x = ∫ t, f (x - t) ∂μ := by
    simpa [μ, f] using smoothFun_eq_integral_kernelMeasure (E := E) (K := K) (ψ := ψ) hψc hψ0 u x
  have hdiff :
      smoothFun (E := E) (K := K) ψ u x - f x = ∫ t, (f (x - t) - f x) ∂μ := by
    have hconst : (∫ _t : E, f x ∂μ) = f x := by
      simp [MeasureTheory.integral_const]
    have hint : MeasureTheory.Integrable (fun t : E => f (x - t)) μ :=
      hf_shift.integrable (by norm_num)
    have :
        (∫ t, f (x - t) ∂μ) - (∫ _t : E, f x ∂μ) =
          ∫ t, (f (x - t) - f x) ∂μ := by
      simpa using (MeasureTheory.integral_sub hint (MeasureTheory.integrable_const (f x))).symm
    simpa [hsmooth, hconst] using this
  
  have hJ :=
    sq_integral_le_integral_sq_of_isProbabilityMeasure
      (μ := μ) (f := fun t : E => f (x - t) - f x) hg
  simpa [hdiff, μ, f] using hJ

lemma norm_sq_smoothL2_sub_extendByZeroL2_le_integral_norm_sq_translateL2_sub_extendByZeroL2
    (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ) (hψ0 : ∀ x, 0 ≤ ψ x)
    (hψint : ∫ x, ψ x ∂(volume : Measure E) = 1)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) :
    ‖smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u - extendByZeroL2 (E := E) (K := K) hKm u‖ ^ 2 ≤
      ∫ t,
        ‖(translateL2 (μ := (volume : Measure E)) (-t)) (extendByZeroL2 (E := E) (K := K) hKm u)
            - extendByZeroL2 (E := E) (K := K) hKm u‖ ^ 2
          ∂kernelMeasure (E := E) ψ := by
  classical
  let μ : Measure E := kernelMeasure (E := E) ψ
  have : MeasureTheory.IsProbabilityMeasure μ :=
    isProbabilityMeasure_kernelMeasure (E := E) (ψ := ψ) hψc hψcs hψ0 hψint
  have : MeasureTheory.IsFiniteMeasure μ := by infer_instance
  have : MeasureTheory.SFinite μ := by infer_instance
  let F : (E →₂[(volume : Measure E)] ℝ) := extendByZeroL2 (E := E) (K := K) hKm u
  let f : E → ℝ := extendByZeroFun (E := E) (K := K) u
  let S : (E →₂[(volume : Measure E)] ℝ) := smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u
  have hS_ae :
      (S : E → ℝ) =ᵐ[(volume : Measure E)] smoothFun (E := E) (K := K) ψ u :=
    smoothL2_ae_eq (E := E) (K := K) (ψ := ψ) (hK := hK) (hKm := hKm) hψc hψcs u
  have hF_ae : (F : E → ℝ) =ᵐ[(volume : Measure E)] f :=
    extendByZeroL2_ae_eq (E := E) (K := K) (hKm := hKm) u
  have hSF_ae :
      (fun x : E => (S - F) x) =ᵐ[(volume : Measure E)] fun x =>
        smoothFun (E := E) (K := K) ψ u x - f x := by
    filter_upwards [MeasureTheory.Lp.coeFn_sub S F, hS_ae, hF_ae] with x hxsub hxS hxF
    have hxsub' : (S - F) x = S x - F x := by
      simpa using hxsub
    rw [hxsub', hxS, hxF]
  have hnorm_sq :
      ‖S - F‖ ^ 2 =
        ∫ x, (smoothFun (E := E) (K := K) ψ u x - f x) ^ 2 ∂(volume : Measure E) := by
    have h1 := norm_sq_eq_integral_sq (E := E) (v := (S - F))
    have h2 :
        (∫ x, ((S - F) x) ^ 2 ∂(volume : Measure E)) =
          ∫ x, (smoothFun (E := E) (K := K) ψ u x - f x) ^ 2 ∂(volume : Measure E) := by
      refine MeasureTheory.integral_congr_ae ?_
      exact hSF_ae.pow_const 2
    exact h1.trans h2
  have hLHS_int :
      MeasureTheory.Integrable (fun x : E => (smoothFun (E := E) (K := K) ψ u x - f x) ^ 2)
        (volume : Measure E) := by
    have hv_mem : MeasureTheory.MemLp (fun x : E => (S - F : E →₂[(volume : Measure E)] ℝ) x)
        (2 : ℝ≥0∞) (volume : Measure E) :=
      MeasureTheory.Lp.memLp (S - F)
    have hv_int :
        MeasureTheory.Integrable
          (fun x : E => ‖(S - F : E →₂[(volume : Measure E)] ℝ) x‖ ^ (2 : ℕ))
          (volume : Measure E) :=
      MeasureTheory.MemLp.integrable_norm_pow (μ := (volume : Measure E)) (f := fun x =>
        (S - F : E →₂[(volume : Measure E)] ℝ) x) (p := 2) hv_mem (by decide)
    
    have hv_sq :
        MeasureTheory.Integrable (fun x : E => ((S - F : E →₂[(volume : Measure E)] ℝ) x) ^ 2)
          (volume : Measure E) := by
      simpa [Real.norm_eq_abs, sq_abs] using hv_int
    exact hv_sq.congr (hSF_ae.pow_const 2)
  
  
  let h : E × E → ℝ := fun z => (f (z.1 - z.2) - f z.1) ^ 2
  have hf_mem : MeasureTheory.MemLp f (2 : ℝ≥0∞) (volume : Measure E) := by
    
    have hF : MeasureTheory.MemLp (fun x : E => (F : E → ℝ) x) (2 : ℝ≥0∞) (volume : Measure E) :=
      MeasureTheory.Lp.memLp F
    exact (MeasureTheory.memLp_congr_ae hF_ae).1 hF
  have hf_sq_int : MeasureTheory.Integrable (fun x : E => (f x) ^ 2) (volume : Measure E) := by
    have hf_int :
        MeasureTheory.Integrable (fun x : E => ‖f x‖ ^ (2 : ℕ)) (volume : Measure E) :=
      MeasureTheory.MemLp.integrable_norm_pow
        (μ := (volume : Measure E)) (f := f) (p := 2)
        hf_mem (by decide)
    simpa [Real.norm_eq_abs, sq_abs] using hf_int
  have hfst_map :
      MeasureTheory.Integrable (fun x : E => (f x) ^ 2)
        (Measure.map Prod.fst ((volume : Measure E).prod μ)) := by
    simpa [Measure.map_fst_prod] using hf_sq_int
  have hf_fst_sq_prod :
      MeasureTheory.Integrable (fun z : E × E => (f z.1) ^ 2) ((volume : Measure E).prod μ) :=
    (MeasureTheory.Integrable.comp_measurable (μ := (volume : Measure E).prod μ) (f := Prod.fst)
      (g := fun x : E => (f x) ^ 2) hfst_map measurable_fst)
  have hsub :
      MeasureTheory.MeasurePreserving
        (fun z : E × E => (z.1 - z.2, z.2))
        ((volume : Measure E).prod μ)
        ((volume : Measure E).prod μ) :=
    MeasureTheory.measurePreserving_sub_prod (μ := (volume : Measure E)) (ν := μ)
  have hf_shift_sq_prod :
      MeasureTheory.Integrable (fun z : E × E => (f (z.1 - z.2)) ^ 2)
        ((volume : Measure E).prod μ) := by
    have := (hsub.integrable_comp hf_fst_sq_prod.aestronglyMeasurable).2 hf_fst_sq_prod
    exact this
  have hdom :
      MeasureTheory.Integrable (fun z : E × E => (2 : ℝ) * ((f (z.1 - z.2)) ^ 2 + (f z.1) ^ 2))
        ((volume : Measure E).prod μ) := by
    simpa [mul_add, two_mul] using (hf_shift_sq_prod.add hf_fst_sq_prod).const_mul (2 : ℝ)
  have hf_fst_aesm :
      MeasureTheory.AEStronglyMeasurable (fun z : E × E => f z.1)
        ((volume : Measure E).prod μ) := by
    have hf_map :
        MeasureTheory.AEStronglyMeasurable f
          (Measure.map Prod.fst
            ((volume : Measure E).prod μ)) := by
      simpa [Measure.map_fst_prod] using hf_mem.aestronglyMeasurable
    exact MeasureTheory.AEStronglyMeasurable.comp_measurable
      (μ := (volume : Measure E).prod μ) (f := Prod.fst)
      (g := f) hf_map measurable_fst
  have hf_shift_aesm :
      MeasureTheory.AEStronglyMeasurable
        (fun z : E × E => f (z.1 - z.2))
        ((volume : Measure E).prod μ) := by
    have := MeasureTheory.AEStronglyMeasurable.comp_measurePreserving (g := fun z : E × E => f z.1)
      hf_fst_aesm hsub
    exact this
  have h_aesm :
      MeasureTheory.AEStronglyMeasurable h ((volume : Measure E).prod μ) := by
    
    have hsub' :
        MeasureTheory.AEStronglyMeasurable (fun z : E × E => f (z.1 - z.2) - f z.1)
          ((volume : Measure E).prod μ) :=
      hf_shift_aesm.sub hf_fst_aesm
    exact (hsub'.pow 2)
  have hint_h : MeasureTheory.Integrable h ((volume : Measure E).prod μ) := by
    refine MeasureTheory.Integrable.mono (μ := (volume : Measure E).prod μ) hdom h_aesm ?_
    refine Filter.Eventually.of_forall ?_
    rintro ⟨x, t⟩
    have hineq :
        (f (x - t) - f x) ^ 2 ≤ (2 : ℝ) * ((f (x - t)) ^ 2 + (f x) ^ 2) := by
      
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        (add_sq_le (a := f (x - t)) (b := -f x))
    have hnonneg : 0 ≤ (f (x - t) - f x) ^ 2 := by nlinarith
    have hsum_nonneg : 0 ≤ (f (x - t)) ^ 2 + (f x) ^ 2 := by nlinarith
    simpa [h, Real.norm_eq_abs, abs_of_nonneg hnonneg, abs_mul,
      abs_of_nonneg (show 0 ≤ (2 : ℝ) by norm_num),
      abs_of_nonneg hsum_nonneg] using hineq
  have hRHS_int :
      MeasureTheory.Integrable
        (fun x : E => ∫ t, (f (x - t) - f x) ^ 2 ∂μ) (volume : Measure E) := by
    simpa [h] using hint_h.integral_prod_left
  have hpoint :
      (fun x : E => (smoothFun (E := E) (K := K) ψ u x - f x) ^ 2)
        ≤ᶠ[MeasureTheory.ae (volume : Measure E)]
        fun x : E => ∫ t, (f (x - t) - f x) ^ 2 ∂μ := by
    refine Filter.Eventually.of_forall ?_
    intro x
    simpa [f, μ] using
      (smoothFun_sub_extendByZeroFun_sq_le_integral_sq (E := E) (K := K) (ψ := ψ)
        hψc hψcs hψ0 hψint hKm u x)
  have hinterm :
      ∫ x, (smoothFun (E := E) (K := K) ψ u x - f x) ^ 2 ∂(volume : Measure E) ≤
        ∫ x, (∫ t, (f (x - t) - f x) ^ 2 ∂μ) ∂(volume : Measure E) :=
    MeasureTheory.integral_mono_ae hLHS_int hRHS_int hpoint
  
  have hswap :
      (∫ x, (∫ t, (f (x - t) - f x) ^ 2 ∂μ) ∂(volume : Measure E)) =
        ∫ t, (∫ x, (f (x - t) - f x) ^ 2 ∂(volume : Measure E)) ∂μ := by
    simpa using (MeasureTheory.integral_integral_swap (μ := (volume : Measure E)) (ν := μ)
      (f := fun x t => (f (x - t) - f x) ^ 2) hint_h)
  
  have hinner :
      (fun t : E => ∫ x, (f (x - t) - f x) ^ 2 ∂(volume : Measure E)) =
        fun t : E =>
          ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ^ 2 := by
    funext t
    
    simpa [F, f] using
      (norm_sq_translateL2_sub_extendByZeroL2_eq_integral_sq
        (E := E) (K := K) (hKm := hKm) t u).symm
  have hRHS_rewrite :
      (∫ t, (∫ x, (f (x - t) - f x) ^ 2 ∂(volume : Measure E)) ∂μ) =
        ∫ t, ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ^ 2 ∂μ := by
    simp [hinner]
  
  have hmain :
      ‖S - F‖ ^ 2 ≤
        ∫ t, ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ^ 2 ∂μ := by
    
    have : ‖S - F‖ ^ 2 ≤ ∫ x, (∫ t, (f (x - t) - f x) ^ 2 ∂μ) ∂(volume : Measure E) := by
      simpa [hnorm_sq] using hinterm
    exact this.trans_eq (hswap.trans hRHS_rewrite)
  
  simpa [S, F, μ] using hmain

end Volume

end

end L2Compactness
end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov
end

section

namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean
namespace L2Compactness

open scoped ENNReal MeasureTheory Topology Convolution Pointwise
open MeasureTheory Set

noncomputable section

section Volume

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

local instance instMeasurableSpaceEL2CompactnessCompactness : MeasurableSpace E := borel E
local instance instBorelSpaceEL2CompactnessCompactness : BorelSpace E := ⟨rfl⟩

variable {K : Set E}
variable {ψ : E → ℝ}

def Kψ : Set E :=
  K + tsupport ψ

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma isCompact_Kψ (hK : IsCompact K) (hψcs : HasCompactSupport ψ) :
    IsCompact (Kψ (K := K) (ψ := ψ)) :=
  IsCompact.add hK hψcs.isCompact

def smoothOn (hKm : MeasurableSet K) (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) :
    C(↥(Kψ (K := K) (ψ := ψ)), ℝ) where
  toFun x := smoothFun (E := E) (K := K) ψ u x
  continuous_toFun := by
    have : Continuous (smoothFun (E := E) (K := K) ψ u) :=
      continuous_smoothFun (E := E) (K := K) (ψ := ψ) (hKm := hKm) hψc hψcs u
    exact this.comp continuous_subtype_val

def smoothBCF (hK : IsCompact K) (hKm : MeasurableSet K) (hψc : Continuous ψ)
    (hψcs : HasCompactSupport ψ)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) :
    BoundedContinuousFunction (↥(Kψ (K := K) (ψ := ψ))) ℝ :=
  letI : CompactSpace ↥(Kψ (K := K) (ψ := ψ)) :=
    isCompact_iff_compactSpace.1 (isCompact_Kψ (K := K) (ψ := ψ) hK hψcs)
  BoundedContinuousFunction.mkOfCompact (smoothOn (E := E) (K := K) (ψ := ψ) hKm hψc hψcs u)

@[simp] lemma smoothBCF_apply (hK : IsCompact K) (hKm : MeasurableSet K) (hψc : Continuous ψ)
    (hψcs : HasCompactSupport ψ)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K))
    (x : ↥(Kψ (K := K) (ψ := ψ))) :
    smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u x =
      smoothFun (E := E) (K := K) ψ u x := by
  rfl

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma uniformContinuous_ψ (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ) :
    UniformContinuous ψ := by
  classical
  
  refine
    Continuous.uniformContinuous_of_tendsto_cocompact (f := ψ) (x := (0 : ℝ)) hψc ?_
  
  refine (Metric.tendsto_nhds.2 ?_)
  intro ε hε
  refine Filter.mem_cocompact'.mpr ⟨tsupport ψ, hψcs, ?_⟩
  intro x hx
  
  
  have hx' : ¬ dist (ψ x) 0 < ε := by
    simpa [Set.mem_compl_iff, Set.mem_ofPred_eq] using hx
  have hxε : ε ≤ dist (ψ x) 0 := le_of_not_gt (by simpa [gt_iff_lt] using hx')
  have hx0 : ψ x ≠ 0 := by
    intro hψ0
    have : dist (ψ x) 0 = 0 := by simp [hψ0]
    have : ε ≤ 0 := by simpa [this] using hxε
    exact not_lt_of_ge this hε
  have hx_supp : x ∈ Function.support ψ := by
    simpa [Function.support] using hx0
  have hx_tsupp : x ∈ tsupport ψ := by
    have : x ∈ closure (Function.support ψ) := subset_closure hx_supp
    simpa [tsupport] using this
  exact hx_tsupp

end Volume

end

end L2Compactness
end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov
end

section

namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean
namespace L2Compactness

open scoped ENNReal MeasureTheory Topology Convolution Pointwise
open MeasureTheory Set

noncomputable section

section Volume

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

local instance instMeasurableSpaceEL2CompactnessArzelaAscoli : MeasurableSpace E := borel E
local instance instBorelSpaceEL2CompactnessArzelaAscoli : BorelSpace E := ⟨rfl⟩
local instance instOpensMeasurableSpaceEL2CompactnessArzelaAscoli : OpensMeasurableSpace E := by
  infer_instance

variable {K : Set E} {ψ : E → ℝ}

lemma smoothFun_eq_integral_restrict (hKm : MeasurableSet K)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) (x : E) :
    smoothFun (E := E) (K := K) ψ u x =
      ∫ t, u t * ψ (x - t) ∂(volume.restrict K) := by
  classical
  
  have :
      smoothFun (E := E) (K := K) ψ u x =
        ∫ t, (extendByZeroFun (E := E) (K := K) u t) • ψ (x - t) ∂(volume : Measure E) := by
    simp [smoothFun, MeasureTheory.convolution_lsmul]
  have h_ind :
      (fun t : E => extendByZeroFun (E := E) (K := K) u t * ψ (x - t)) =
        K.indicator (fun t : E => u t * ψ (x - t)) := by
    funext t
    by_cases ht : t ∈ K <;> simp [extendByZeroFun, ht]
  
  simp [this, h_ind, MeasureTheory.integral_indicator hKm]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma isCompact_diffSet (hK : IsCompact K) (hψcs : HasCompactSupport ψ) :
    IsCompact
      ((fun p : E × E => p.1 - p.2) '' ((Kψ (K := K) (ψ := ψ)) ×ˢ K)) := by
  have hKψ : IsCompact (Kψ (K := K) (ψ := ψ)) := isCompact_Kψ (K := K) (ψ := ψ) hK hψcs
  have hprod : IsCompact ((Kψ (K := K) (ψ := ψ)) ×ˢ K) := hKψ.prod hK
  refine hprod.image ?_
  exact (continuous_fst.sub continuous_snd)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma exists_norm_ψ_bound_on_diffSet (hK : IsCompact K) (hψc : Continuous ψ)
    (hψcs : HasCompactSupport ψ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x : ↥(Kψ (K := K) (ψ := ψ)), ∀ t : E, t ∈ K → ‖ψ ((x : E) - t)‖ ≤ C := by
  classical
  let diffSet : Set E :=
    (fun p : E × E => p.1 - p.2) '' ((Kψ (K := K) (ψ := ψ)) ×ˢ K)
  have hdiff : IsCompact diffSet := isCompact_diffSet (E := E) (K := K) (ψ := ψ) hK hψcs
  by_cases hne : diffSet.Nonempty
  · 
    have hcont : Continuous (fun z : E => ‖ψ z‖) := hψc.norm
    rcases hdiff.exists_isMaxOn hne (hcont.continuousOn) with ⟨z0, hz0, hzmax⟩
    refine ⟨‖ψ z0‖, norm_nonneg _, ?_⟩
    intro x t ht
    have hx : (x : E) ∈ Kψ (K := K) (ψ := ψ) := x.2
    have hx_t : (x : E) - t ∈ diffSet := by
      refine ⟨((x : E), t), ?_, rfl⟩
      exact ⟨hx, ht⟩
    exact (isMaxOn_iff.1 hzmax) _ hx_t
  · 
    refine ⟨0, le_rfl, ?_⟩
    intro x t ht
    exfalso
    have hx : (x : E) ∈ Kψ (K := K) (ψ := ψ) := x.2
    have : (x : E) - t ∈ diffSet := by
      refine ⟨((x : E), t), ?_, rfl⟩
      exact ⟨hx, ht⟩
    exact hne ⟨(x : E) - t, this⟩

lemma smoothFun_image_mem_closedBall (hK : IsCompact K)
    (hKm : MeasurableSet K) (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ) {R : ℝ}
    (hRpos : 0 < R) (Cψ : ℝ) (hCψ_nonneg : 0 ≤ Cψ)
    (hψ_bound : ∀ x : ↥(Kψ (K := K) (ψ := ψ)), ∀ t : E, t ∈ K → ‖ψ ((x : E) - t)‖ ≤ Cψ) :
    let mK : ℝ :=
      (MeasureTheory.measureUnivNNReal (volume.restrict K)) ^ ((2 : ℝ≥0∞).toReal⁻¹)
    ∀ (f : BoundedContinuousFunction (↥(Kψ (K := K) (ψ := ψ))) ℝ) (x : ↥(Kψ (K := K) (ψ := ψ))),
      f ∈ (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs ''
            Metric.closedBall (0 : _) R) →
        f x ∈ Metric.closedBall (0 : ℝ) (R * (mK * Cψ)) := by
  intro mK
  classical
  have hR : 0 ≤ R := hRpos.le
  have hμK : (volume : Measure E) K < (⊤ : ℝ≥0∞) := hK.measure_lt_top (μ := (volume : Measure E))
  have : Fact ((volume : Measure E) K < (⊤ : ℝ≥0∞)) := ⟨hμK⟩
  have : IsFiniteMeasure ((volume : Measure E).restrict K) := by infer_instance
  let μ : Measure E := (volume : Measure E).restrict K
  have hmK : 0 ≤ mK := by
    have : 0 ≤ (MeasureTheory.measureUnivNNReal (volume.restrict K)) := by simp
    exact Real.rpow_nonneg this _
  intro f x hfA
  rcases hfA with ⟨u, hu_ball, rfl⟩
  have hu_norm : ‖u‖ ≤ R := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hu_ball
  
  have hker :
      MemLp (fun t : E => ψ ((x : E) - t)) (2 : ℝ≥0∞) (volume.restrict K) := by
    refine MemLp.of_bound (μ := (volume.restrict K))
      (hf := (hψc.aestronglyMeasurable.comp_measurable
        (measurable_const.sub measurable_id))) Cψ ?_
    filter_upwards
      [MeasureTheory.ae_restrict_mem
        (μ := (volume : Measure E)) hKm] with t ht
    exact hψ_bound x t ht
  let kx : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) μ :=
    hker.toLp (fun t : E => ψ ((x : E) - t))
  have hkx_norm : ‖kx‖ ≤ mK * Cψ := by
    have h_ae :
        ∀ᵐ t ∂(volume.restrict K), ‖(fun t : E => ψ ((x : E) - t)) t‖ ≤ Cψ := by
      filter_upwards [MeasureTheory.ae_restrict_mem (μ := (volume : Measure E)) hKm] with t ht
      exact hψ_bound x t ht
    have := (MeasureTheory.Lp.norm_le_of_ae_bound
      (μ := (volume.restrict K)) (p := (2 : ℝ≥0∞))
      (f := kx) (hC := hCψ_nonneg) (by
        
        filter_upwards [h_ae,
          MeasureTheory.MemLp.coeFn_toLp
            (μ := (volume.restrict K)) (p := (2 : ℝ≥0∞))
            (f := fun t : E => ψ ((x : E) - t))
            hker] with t ht hrep
        simpa [kx, hrep] using ht))
    simpa [mK] using this
  
  have hsmooth :
      smoothFun (E := E) (K := K) ψ u (x : E) =
        ∫ t, u t * kx t ∂(volume.restrict K) := by
    have h_ae :
        (fun t : E => u t * kx t) =ᵐ[volume.restrict K] fun t : E => u t * ψ ((x : E) - t) := by
      filter_upwards [MeasureTheory.MemLp.coeFn_toLp
        (μ := (volume.restrict K)) (p := (2 : ℝ≥0∞))
        (f := fun t : E => ψ ((x : E) - t))
        hker] with t ht
      simp [kx, ht]
    
    rw [smoothFun_eq_integral_restrict
      (E := E) (K := K) (ψ := ψ) (hKm := hKm) u (x : E)]
    exact (MeasureTheory.integral_congr_ae h_ae.symm)
  have hsmooth' :
      smoothFun (E := E) (K := K) ψ u (x : E) =
        ∫ t, kx t * u t ∂(volume.restrict K) := by
    simp [hsmooth, mul_comm]
  have hinner :
      smoothFun (E := E) (K := K) ψ u (x : E) =
        inner ℝ (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) μ) kx := by
    erw [MeasureTheory.L2.inner_def]; exact hsmooth'
  have habs :
      |smoothFun (E := E) (K := K) ψ u (x : E)| ≤ ‖u‖ * ‖kx‖ := by
    simpa [hinner] using
      (abs_real_inner_le_norm (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) μ) kx)
  have habs' : |smoothFun (E := E) (K := K) ψ u (x : E)| ≤ R * (mK * Cψ) := by
    calc
      |smoothFun (E := E) (K := K) ψ u (x : E)|
          ≤ ‖u‖ * ‖kx‖ := habs
      _ ≤ R * (mK * Cψ) := by
        exact mul_le_mul hu_norm hkx_norm (norm_nonneg _) hR
  have : dist (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u x) 0 ≤ R * (mK * Cψ) := by
    simpa [smoothBCF_apply (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u x,
      dist_eq_norm, Real.norm_eq_abs] using habs'
  simpa [Metric.mem_closedBall, dist_eq_norm] using this

lemma uniformEquicontinuous_smoothBCF_closedBall (hK : IsCompact K)
    (hKm : MeasurableSet K) (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ) {R : ℝ}
    (hRpos : 0 < R) (Cψ : ℝ) (hCψ_nonneg : 0 ≤ Cψ)
    (hψ_bound : ∀ x : ↥(Kψ (K := K) (ψ := ψ)), ∀ t : E, t ∈ K → ‖ψ ((x : E) - t)‖ ≤ Cψ) :
    let A : Set (BoundedContinuousFunction (↥(Kψ (K := K) (ψ := ψ))) ℝ) :=
      smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs '' Metric.closedBall (0 : _) R
    UniformEquicontinuous ((↑) : A → ↥(Kψ (K := K) (ψ := ψ)) → ℝ) := by
  intro A
  classical
  have hR : 0 ≤ R := hRpos.le
  have hR0 : R ≠ 0 := ne_of_gt hRpos
  have hμK : (volume : Measure E) K < (⊤ : ℝ≥0∞) := hK.measure_lt_top (μ := (volume : Measure E))
  have : Fact ((volume : Measure E) K < (⊤ : ℝ≥0∞)) := ⟨hμK⟩
  have : IsFiniteMeasure ((volume : Measure E).restrict K) := by infer_instance
  let μ : Measure E := (volume : Measure E).restrict K
  let mK : ℝ :=
    (MeasureTheory.measureUnivNNReal (volume.restrict K)) ^ ((2 : ℝ≥0∞).toReal⁻¹)
  have hmK : 0 ≤ mK := Real.rpow_nonneg (by simp) _
  let s : Set ℝ := Metric.closedBall (0 : ℝ) (R * (mK * Cψ))
  have in_s :=
    smoothFun_image_mem_closedBall (K := K) (ψ := ψ) hK hKm hψc hψcs
      (R := R) hRpos Cψ hCψ_nonneg hψ_bound
  rw [Metric.uniformEquicontinuous_iff]
  intro ε hε
  
  by_cases hmK0 : mK = 0
  · refine ⟨1, by norm_num, ?_⟩
    intro x y _ f
    
    set F : BoundedContinuousFunction (↥(Kψ (K := K) (ψ := ψ))) ℝ :=
      (f : BoundedContinuousFunction (↥(Kψ (K := K) (ψ := ψ))) ℝ) with hF
    have hzero : ∀ z, F z = 0 := by
      intro z
      have hmem : F z ∈ s := in_s (f := F) z f.property
      have hle : dist (F z) 0 ≤ 0 := by
        have : dist (F z) 0 ≤ R * (mK * Cψ) := by simpa [s, Metric.mem_closedBall] using hmem
        simpa [hmK0] using this
      exact dist_eq_zero.1 (le_antisymm hle dist_nonneg)
    simpa [hzero x, hzero y] using hε
  · have hRmK_ne : R * mK ≠ 0 := mul_ne_zero hR0 hmK0
    let ε2 : ℝ := ε / 2
    have hε2pos : 0 < ε2 := by
      simpa [ε2] using half_pos hε
    let ε' : ℝ := ε2 / (R * mK)
    have hε'pos : 0 < ε' :=
      div_pos hε2pos (mul_pos hRpos (lt_of_le_of_ne hmK (Ne.symm hmK0)))
    have hε'lt : R * mK * ε' = ε2 := by
      dsimp [ε']
      field_simp [hRmK_ne, mul_assoc, mul_left_comm, mul_comm]
    
    have hUC : UniformContinuous ψ := uniformContinuous_ψ (E := E) (ψ := ψ) hψc hψcs
    rcases (Metric.uniformContinuous_iff.1 hUC) ε' hε'pos with ⟨deltaLoss, hδpos, hδ⟩
    refine ⟨deltaLoss, hδpos, ?_⟩
    intro x y hxy f
    
    rcases f.property with ⟨u, hu_ball, hu_eq⟩
    have hu_eq' :
        (f : BoundedContinuousFunction (↥(Kψ (K := K) (ψ := ψ))) ℝ) =
          smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u := by
      simpa using hu_eq.symm
    have hu_norm : ‖u‖ ≤ R := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hu_ball
    
    have hkerx :
        MemLp (fun t : E => ψ ((x : E) - t)) (2 : ℝ≥0∞) (volume.restrict K) := by
      refine MemLp.of_bound (μ := (volume.restrict K))
        (hf := (hψc.aestronglyMeasurable.comp_measurable
          (measurable_const.sub measurable_id))) Cψ ?_
      filter_upwards
        [MeasureTheory.ae_restrict_mem
          (μ := (volume : Measure E)) hKm] with t ht
      exact hψ_bound x t ht
    have hkery :
        MemLp (fun t : E => ψ ((y : E) - t)) (2 : ℝ≥0∞) (volume.restrict K) := by
      refine MemLp.of_bound (μ := (volume.restrict K))
        (hf := (hψc.aestronglyMeasurable.comp_measurable
          (measurable_const.sub measurable_id))) Cψ ?_
      filter_upwards [MeasureTheory.ae_restrict_mem (μ := (volume : Measure E)) hKm] with t ht
      exact hψ_bound y t ht
    let kx : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) μ :=
      hkerx.toLp (fun t : E => ψ ((x : E) - t))
    let ky : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) μ :=
      hkery.toLp (fun t : E => ψ ((y : E) - t))
    
    have h_ae :
        ∀ᵐ t ∂(volume.restrict K), ‖(kx - ky) t‖ ≤ ε' := by
      filter_upwards [MeasureTheory.ae_restrict_mem (μ := (volume : Measure E)) hKm,
        MeasureTheory.MemLp.coeFn_toLp (μ := (volume.restrict K)) (p := (2 : ℝ≥0∞))
          (f := fun t : E => ψ ((x : E) - t)) hkerx,
        MeasureTheory.MemLp.coeFn_toLp (μ := (volume.restrict K)) (p := (2 : ℝ≥0∞))
          (f := fun t : E => ψ ((y : E) - t)) hkery,
        (MeasureTheory.Lp.coeFn_sub (μ := (volume.restrict K)) (p := (2 : ℝ≥0∞)) kx ky)] with
        t ht hx_t hy_t hsub
      have hxy' : dist ((x : E) - t) ((y : E) - t) < deltaLoss := by
        rw [dist_sub_right]
        exact hxy
      have hψxy : dist (ψ ((x : E) - t)) (ψ ((y : E) - t)) < ε' :=
        hδ (a := (x : E) - t) (b := (y : E) - t) hxy'
      have : ‖ψ ((x : E) - t) - ψ ((y : E) - t)‖ ≤ ε' := by
        simpa [dist_eq_norm, sub_eq_add_neg] using le_of_lt hψxy
      have hx' : kx t = ψ ((x : E) - t) := by simpa [kx] using hx_t
      have hy' : ky t = ψ ((y : E) - t) := by simpa [ky] using hy_t
      have hnorm : ‖kx t - ky t‖ ≤ ε' := by
        simpa [hx', hy'] using this
      have hsub' : (kx - ky) t = kx t - ky t := by
        simpa [Pi.sub_apply] using hsub
      simpa [hsub'.symm] using hnorm
    have hkdiff : ‖kx - ky‖ ≤ mK * ε' := by
      have := (MeasureTheory.Lp.norm_le_of_ae_bound (μ := (volume.restrict K)) (p := (2 : ℝ≥0∞))
        (f := (kx - ky : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) μ)) (hC := le_of_lt hε'pos) h_ae)
      simpa [mK, mul_comm, mul_left_comm, mul_assoc] using this
    
    have hdist :
        dist (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u x)
            (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u y)
          ≤ ‖u‖ * ‖kx - ky‖ := by
      
      have hx_val :
          smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u x =
            inner ℝ (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) μ) kx := by
        have hsmooth :
            smoothFun (E := E) (K := K) ψ u (x : E) =
              ∫ t, u t * kx t ∂(volume.restrict K) := by
          have h_ae' :
              (fun t : E => u t * kx t) =ᵐ[volume.restrict K]
                fun t : E => u t * ψ ((x : E) - t) := by
            filter_upwards [MeasureTheory.MemLp.coeFn_toLp
              (μ := (volume.restrict K)) (p := (2 : ℝ≥0∞))
              (f := fun t : E => ψ ((x : E) - t))
              hkerx] with t ht
            simp [kx, ht]
          rw [smoothFun_eq_integral_restrict
            (E := E) (K := K) (ψ := ψ) (hKm := hKm)
            u (x : E)]
          exact (MeasureTheory.integral_congr_ae h_ae'.symm)
        have hsmooth' :
            smoothFun (E := E) (K := K) ψ u (x : E) =
              ∫ t, kx t * u t ∂(volume.restrict K) := by
          simp [hsmooth, mul_comm]
        erw [smoothBCF_apply (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u x,
          MeasureTheory.L2.inner_def]; exact hsmooth'
      have hy_val :
          smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u y =
            inner ℝ (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) μ) ky := by
        have hsmooth :
            smoothFun (E := E) (K := K) ψ u (y : E) =
              ∫ t, u t * ky t ∂(volume.restrict K) := by
          have h_ae' :
              (fun t : E => u t * ky t) =ᵐ[volume.restrict K]
                fun t : E => u t * ψ ((y : E) - t) := by
            filter_upwards [MeasureTheory.MemLp.coeFn_toLp
              (μ := (volume.restrict K)) (p := (2 : ℝ≥0∞))
              (f := fun t : E => ψ ((y : E) - t))
              hkery] with t ht
            simp [ky, ht]
          rw [smoothFun_eq_integral_restrict
            (E := E) (K := K) (ψ := ψ) (hKm := hKm)
            u (y : E)]
          exact (MeasureTheory.integral_congr_ae h_ae'.symm)
        have hsmooth' :
            smoothFun (E := E) (K := K) ψ u (y : E) =
              ∫ t, ky t * u t ∂(volume.restrict K) := by
          simp [hsmooth, mul_comm]
        erw [smoothBCF_apply (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u y,
          MeasureTheory.L2.inner_def]; exact hsmooth'
      have :
          ‖smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u x -
              smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u y‖ ≤
            ‖u‖ * ‖kx - ky‖ := by
        have :
            smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u x -
                smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u y =
              inner ℝ (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) μ) (kx - ky) := by
          simp [hx_val, hy_val, inner_sub_right]
        have this' :
            smoothFun (E := E) (K := K) ψ u (x : E) - smoothFun (E := E) (K := K) ψ u (y : E) =
              inner ℝ (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) μ) (kx - ky) := by
          simpa [smoothBCF_apply (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs] using this
        have hCS :=
          (abs_real_inner_le_norm (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) μ) (kx - ky))
        simpa [this', dist_eq_norm, Real.norm_eq_abs] using hCS
      simpa [dist_eq_norm] using this
    have hle :
        dist (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u x)
            (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u y)
          ≤ R * (mK * ε') := by
      calc
        dist (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u x)
            (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u y)
            ≤ ‖u‖ * ‖kx - ky‖ := hdist
        _ ≤ ‖u‖ * (mK * ε') := by
          exact mul_le_mul_of_nonneg_left hkdiff (norm_nonneg _)
        _ ≤ R * (mK * ε') := by
          have hmKε' : 0 ≤ mK * ε' := mul_nonneg hmK (le_of_lt hε'pos)
          exact mul_le_mul_of_nonneg_right hu_norm hmKε'
    have hRmkε' : R * (mK * ε') = ε2 := by
      have : R * mK * ε' = ε2 := by
        simpa [ε', mul_assoc] using hε'lt
      simpa [mul_assoc] using this
    have hle' :
        dist (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u x)
            (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u y) ≤ ε2 := by
      simpa [hRmkε'] using hle
    have hε2lt : ε2 < ε := by
      simpa [ε2] using half_lt_self hε
    have :
        dist (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u x)
            (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u y) < ε :=
      lt_of_le_of_lt hle' hε2lt
    simpa [hu_eq'] using this

theorem smoothBCF_image_closedBall_isCompact (hK : IsCompact K) (hKm : MeasurableSet K)
    (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ) {R : ℝ} (hR : 0 ≤ R) :
    IsCompact
        (closure
          (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs '' Metric.closedBall (0 : _)
            R)) := by
  classical
  
  by_cases hR0 : R = 0
  · subst hR0
    have hball :
        Metric.closedBall (0 : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) 0 = {0} := by
      ext u
      simp
    
    simp [hball]
  · have hRpos : 0 < R := lt_of_le_of_ne hR (Ne.symm hR0)
    
    let : CompactSpace ↥(Kψ (K := K) (ψ := ψ)) :=
      isCompact_iff_compactSpace.1 (isCompact_Kψ (K := K) (ψ := ψ) hK hψcs)
    let A :
        Set (BoundedContinuousFunction (↥(Kψ (K := K) (ψ := ψ))) ℝ) :=
      smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs '' Metric.closedBall (0 : _) R
    
    have hμK : (volume : Measure E) K < (⊤ : ℝ≥0∞) := hK.measure_lt_top (μ := (volume : Measure E))
    let : Fact ((volume : Measure E) K < (⊤ : ℝ≥0∞)) := ⟨hμK⟩
    have : IsFiniteMeasure (volume.restrict K) := by
      infer_instance
    let μ : Measure E := (volume : Measure E).restrict K
    let mK : ℝ :=
      (MeasureTheory.measureUnivNNReal (volume.restrict K)) ^ ((2 : ℝ≥0∞).toReal⁻¹)
    have hmK : 0 ≤ mK := by
      have : 0 ≤ (MeasureTheory.measureUnivNNReal (volume.restrict K)) := by simp
      exact Real.rpow_nonneg this _
    
    obtain ⟨Cψ, hCψ_nonneg, hψ_bound⟩ :=
      exists_norm_ψ_bound_on_diffSet (E := E) (K := K) (ψ := ψ) hK hψc hψcs
    
    let s : Set ℝ := Metric.closedBall (0 : ℝ) (R * (mK * Cψ))
    have hs : IsCompact s := by
      simpa [s] using isCompact_closedBall (0 : ℝ) (R * (mK * Cψ))
    
    have in_s :
        ∀ (f : BoundedContinuousFunction (↥(Kψ (K := K) (ψ := ψ))) ℝ) (x : ↥(Kψ (K := K) (ψ := ψ))),
          f ∈ A → f x ∈ s := by
      intro f x hfA
      rcases hfA with ⟨u, hu_ball, rfl⟩
      have hu_norm : ‖u‖ ≤ R := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hu_ball
      
      have hker :
          MemLp (fun t : E => ψ ((x : E) - t)) (2 : ℝ≥0∞) (volume.restrict K) := by
        refine MemLp.of_bound (μ := (volume.restrict K))
          (hf := (hψc.aestronglyMeasurable.comp_measurable
            (measurable_const.sub measurable_id))) Cψ ?_
        filter_upwards
          [MeasureTheory.ae_restrict_mem
            (μ := (volume : Measure E)) hKm] with t ht
        exact hψ_bound x t ht
      let kx : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) μ :=
        hker.toLp (fun t : E => ψ ((x : E) - t))
      have hkx_norm : ‖kx‖ ≤ mK * Cψ := by
        have h_ae :
            ∀ᵐ t ∂(volume.restrict K), ‖(fun t : E => ψ ((x : E) - t)) t‖ ≤ Cψ := by
          filter_upwards [MeasureTheory.ae_restrict_mem (μ := (volume : Measure E)) hKm] with t ht
          exact hψ_bound x t ht
        have := (MeasureTheory.Lp.norm_le_of_ae_bound
          (μ := (volume.restrict K)) (p := (2 : ℝ≥0∞))
          (f := kx) (hC := hCψ_nonneg) (by
            
            filter_upwards [h_ae,
              MeasureTheory.MemLp.coeFn_toLp
                (μ := (volume.restrict K)) (p := (2 : ℝ≥0∞))
                (f := fun t : E => ψ ((x : E) - t))
                hker] with t ht hrep
            simpa [kx, hrep] using ht))
        simpa [mK] using this
      
      have hsmooth :
          smoothFun (E := E) (K := K) ψ u (x : E) =
            ∫ t, u t * kx t ∂(volume.restrict K) := by
        have h_ae :
            (fun t : E => u t * kx t) =ᵐ[volume.restrict K] fun t : E => u t * ψ ((x : E) - t) := by
          filter_upwards [MeasureTheory.MemLp.coeFn_toLp
            (μ := (volume.restrict K)) (p := (2 : ℝ≥0∞))
            (f := fun t : E => ψ ((x : E) - t))
            hker] with t ht
          simp [kx, ht]
        
        rw [smoothFun_eq_integral_restrict
          (E := E) (K := K) (ψ := ψ) (hKm := hKm) u (x : E)]
        exact (MeasureTheory.integral_congr_ae h_ae.symm)
      have hsmooth' :
          smoothFun (E := E) (K := K) ψ u (x : E) =
            ∫ t, kx t * u t ∂(volume.restrict K) := by
        simp [hsmooth, mul_comm]
      have hinner :
          smoothFun (E := E) (K := K) ψ u (x : E) =
            inner ℝ (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) μ) kx := by
        erw [MeasureTheory.L2.inner_def]; exact hsmooth'
      have habs :
          |smoothFun (E := E) (K := K) ψ u (x : E)| ≤ ‖u‖ * ‖kx‖ := by
        simpa [hinner] using
          (abs_real_inner_le_norm (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) μ) kx)
      have habs' : |smoothFun (E := E) (K := K) ψ u (x : E)| ≤ R * (mK * Cψ) := by
        calc
          |smoothFun (E := E) (K := K) ψ u (x : E)|
              ≤ ‖u‖ * ‖kx‖ := habs
          _ ≤ R * (mK * Cψ) := by
            exact mul_le_mul hu_norm hkx_norm (norm_nonneg _) hR
      have : dist (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u x) 0 ≤ R * (mK * Cψ) := by
        simpa [smoothBCF_apply (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u x,
          dist_eq_norm, Real.norm_eq_abs] using habs'
      simpa [s, Metric.mem_closedBall, dist_eq_norm] using this
    
    have H' :
        UniformEquicontinuous ((↑) : A → ↥(Kψ (K := K) (ψ := ψ)) → ℝ) :=
      uniformEquicontinuous_smoothBCF_closedBall (K := K) (ψ := ψ) hK hKm hψc hψcs
        (R := R) hRpos Cψ hCψ_nonneg hψ_bound
    have H : Equicontinuous ((↑) : A → ↥(Kψ (K := K) (ψ := ψ)) → ℝ) := H'.equicontinuous
    
    simpa [A, s] using
      (BoundedContinuousFunction.arzela_ascoli (α := ↥(Kψ (K := K) (ψ := ψ))) (β := ℝ)
        (s := s) hs A (fun f x hf => in_s f x hf) H)

end Volume

end

end L2Compactness
end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov
end

section

namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean
namespace L2Compactness

open scoped ENNReal MeasureTheory Topology Convolution Pointwise
open MeasureTheory Set

noncomputable section

section Volume

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

local instance instMeasurableSpaceEL2CompactnessTransfer : MeasurableSpace E := borel E
local instance instBorelSpaceEL2CompactnessTransfer : BorelSpace E := ⟨rfl⟩
local instance instOpensMeasurableSpaceEL2CompactnessTransfer : OpensMeasurableSpace E := by
  infer_instance

variable {K : Set E} {ψ : E → ℝ}

lemma dist_smoothL2_le_mul_dist_smoothBCF (hK : IsCompact K) (hKm : MeasurableSet K)
    (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ) :
    ∀ u v : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K),
      dist (smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u)
          (smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs v) ≤
        (MeasureTheory.measureUnivNNReal ((volume : Measure E).restrict (Kψ (K := K) (ψ := ψ)))) ^
            ((2 : ℝ≥0∞).toReal⁻¹) *
          dist (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u)
              (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs v) := by
  classical
  let : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  let s : Set E := Kψ (K := K) (ψ := ψ)
  have hs_compact : IsCompact s := isCompact_Kψ (K := K) (ψ := ψ) hK hψcs
  have hs : MeasurableSet s := hs_compact.measurableSet
  have hs_lt_top : (volume : Measure E) s < (⊤ : ℝ≥0∞) :=
    hs_compact.measure_lt_top (μ := (volume : Measure E))
  let μs : Measure E := (volume : Measure E).restrict s
  have : Fact ((volume : Measure E) s < (⊤ : ℝ≥0∞)) := ⟨hs_lt_top⟩
  have : IsFiniteMeasure μs := by
    infer_instance
  let mS : ℝ := (MeasureTheory.measureUnivNNReal μs) ^ ((2 : ℝ≥0∞).toReal⁻¹)
  intro u v
  set Su :=
    smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u
  set Sv :=
    smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs v
  set Bu :=
    smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u
  set Bv :=
    smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs v
  have hBuBv : 0 ≤ ‖Bu - Bv‖ := norm_nonneg _
  
  let F : (E →₂[(volume : Measure E)] ℝ) := Su - Sv
  let g : E → ℝ := fun x => (F : E → ℝ) x
  have hg : MeasureTheory.MemLp g (2 : ℝ≥0∞) (volume : Measure E) := MeasureTheory.Lp.memLp F
  have hg_restrict : MeasureTheory.MemLp g (2 : ℝ≥0∞) μs := hg.restrict s
  let Fs : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) μs := hg_restrict.toLp g
  
  have hF_ae :
      (g =ᵐ[μs] fun x : E =>
        smoothFun (E := E) (K := K) ψ u x -
          smoothFun (E := E) (K := K) ψ v x) := by
    have hsub :
        (F : E → ℝ) =ᵐ[(volume : Measure E)] (Su : E → ℝ) - (Sv : E → ℝ) := by
      simpa [F, g, Su, Sv] using
        (MeasureTheory.Lp.coeFn_sub (μ := (volume : Measure E)) Su Sv)
    have hu :
        (Su : E → ℝ) =ᵐ[(volume : Measure E)] smoothFun (E := E) (K := K) ψ u :=
      smoothL2_ae_eq (E := E) (K := K) (ψ := ψ) (hK := hK) (hKm := hKm) hψc hψcs u
    have hv :
        (Sv : E → ℝ) =ᵐ[(volume : Measure E)] smoothFun (E := E) (K := K) ψ v :=
      smoothL2_ae_eq (E := E) (K := K) (ψ := ψ) (hK := hK) (hKm := hKm) hψc hψcs v
    have hF :
        (F : E → ℝ) =ᵐ[(volume : Measure E)]
          fun x : E =>
            smoothFun (E := E) (K := K) ψ u x - smoothFun (E := E) (K := K) ψ v x := by
      have h := hsub.trans (hu.sub hv)
      filter_upwards [h] with x hx
      simpa [Pi.sub_apply] using hx
    exact MeasureTheory.ae_restrict_of_ae (μ := (volume : Measure E)) (s := s) hF
  have hFs_ae : ((Fs : E → ℝ) =ᵐ[μs] g) := by
    simpa [Fs, g] using
      (MeasureTheory.MemLp.coeFn_toLp (μ := μs) (p := (2 : ℝ≥0∞)) (f := g) hg_restrict)
  have hbound :
      ∀ᵐ x ∂μs, ‖Fs x‖ ≤ ‖Bu - Bv‖ := by
    have hpoint :
        ∀ x : E, x ∈ s → ‖smoothFun (E := E) (K := K) ψ u x - smoothFun (E := E) (K := K) ψ v x‖ ≤
          ‖Bu - Bv‖ := by
      intro x hx
      let x' : ↥(Kψ (K := K) (ψ := ψ)) := ⟨x, hx⟩
      have hBu : Bu x' = smoothFun (E := E) (K := K) ψ u x := by
        simp [Bu, x']
      have hBv : Bv x' = smoothFun (E := E) (K := K) ψ v x := by
        simp [Bv, x']
      have : ‖(Bu - Bv) x'‖ ≤ ‖Bu - Bv‖ :=
        (Bu - Bv).norm_coe_le_norm x'
      simpa [hBu, hBv] using this
    filter_upwards
      [MeasureTheory.ae_restrict_mem (μ := (volume : Measure E)) hs,
        hFs_ae, hF_ae] with x hx hFs hF
    have := hpoint x hx
    
    simpa [hFs, hF] using this
  have hnorm_Fs : ‖Fs‖ ≤ mS * ‖Bu - Bv‖ := by
    have := (MeasureTheory.Lp.norm_le_of_ae_bound (μ := μs) (p := (2 : ℝ≥0∞))
      (f := Fs) (hC := hBuBv) hbound)
    simpa [mS] using this
  
  have hsupport :
      ∀ x : E, x ∉ s →
        smoothFun (E := E) (K := K) ψ u x -
          smoothFun (E := E) (K := K) ψ v x = 0 := by
    intro x hx
    have hu_supp : Function.support (smoothFun (E := E) (K := K) ψ u) ⊆ s := by
      exact
        (support_smoothFun_subset_add_tsupport (E := E) (K := K) (ψ := ψ) u)
    have hv_supp : Function.support (smoothFun (E := E) (K := K) ψ v) ⊆ s := by
      exact
        (support_smoothFun_subset_add_tsupport (E := E) (K := K) (ψ := ψ) v)
    have hu0 : smoothFun (E := E) (K := K) ψ u x = 0 := by
      have : x ∉ Function.support (smoothFun (E := E) (K := K) ψ u) := fun hx' => hx (hu_supp hx')
      simpa [Function.support] using this
    have hv0 : smoothFun (E := E) (K := K) ψ v x = 0 := by
      have : x ∉ Function.support (smoothFun (E := E) (K := K) ψ v) := fun hx' => hx (hv_supp hx')
      simpa [Function.support] using this
    simp [hu0, hv0]
  have hF0 :
      ∀ᵐ x ∂(volume : Measure E), x ∉ s → g x = 0 := by
    have hF_ae_full :
        (g =ᵐ[(volume : Measure E)]
          fun x : E =>
            smoothFun (E := E) (K := K) ψ u x -
              smoothFun (E := E) (K := K) ψ v x) := by
      have hsub :
          (F : E → ℝ) =ᵐ[(volume : Measure E)] (Su : E → ℝ) - (Sv : E → ℝ) := by
        simpa [F, g, Su, Sv] using
          (MeasureTheory.Lp.coeFn_sub (μ := (volume : Measure E)) Su Sv)
      have hu :
          (Su : E → ℝ) =ᵐ[(volume : Measure E)] smoothFun (E := E) (K := K) ψ u :=
        smoothL2_ae_eq (E := E) (K := K) (ψ := ψ) (hK := hK) (hKm := hKm) hψc hψcs u
      have hv :
          (Sv : E → ℝ) =ᵐ[(volume : Measure E)] smoothFun (E := E) (K := K) ψ v :=
        smoothL2_ae_eq (E := E) (K := K) (ψ := ψ) (hK := hK) (hKm := hKm) hψc hψcs v
      have hF :
          (F : E → ℝ) =ᵐ[(volume : Measure E)]
            fun x : E =>
              smoothFun (E := E) (K := K) ψ u x - smoothFun (E := E) (K := K) ψ v x := by
        have h := hsub.trans (hu.sub hv)
        filter_upwards [h] with x hx
        simpa [Pi.sub_apply] using hx
      simpa [g] using hF
    filter_upwards [hF_ae_full] with x hx
    intro hxnot
    have : smoothFun (E := E) (K := K) ψ u x - smoothFun (E := E) (K := K) ψ v x = 0 :=
      hsupport x hxnot
    simpa [hx] using this
  have hF_ind :
      (s.indicator g =ᵐ[(volume : Measure E)] g) := by
    filter_upwards [hF0] with x hx
    by_cases hxmem : x ∈ s
    · simp [g, hxmem]
    · have : g x = 0 := hx hxmem
      simp [g, hxmem, this]
  
  let Fext :
      MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume : Measure E) :=
    (MeasureTheory.Lp.extendByZeroₗᵢ (μ := (volume : Measure E)) (E := ℝ) (p := (2 : ℝ≥0∞))
      (s := s) hs) Fs
  have hFext_ae :
      ((Fext : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume : Measure E)) :
          E → ℝ) =ᵐ[(volume : Measure E)]
        s.indicator fun x : E => (Fs : E → ℝ) x := by
    simpa [Fext] using
      (MeasureTheory.Lp.extendByZeroₗᵢ_ae_eq
        (μ := (volume : Measure E)) (p := (2 : ℝ≥0∞))
        (s := s) hs Fs)
  have hFs_on :
      ∀ᵐ x ∂(volume : Measure E), x ∈ s → (Fs : E → ℝ) x = g x := by
    
    have := (MeasureTheory.ae_restrict_iff' (μ := (volume : Measure E)) (s := s) hs).1 hFs_ae
    simpa [g] using this
  have hindicator :
      (s.indicator (fun x : E => (Fs : E → ℝ) x) =ᵐ[(volume : Measure E)] s.indicator g) := by
    filter_upwards [hFs_on] with x hx
    by_cases hxmem : x ∈ s
    · simp [hxmem, hx hxmem]
    · simp [hxmem]
  have hFext_ae' :
      (Fext : E → ℝ) =ᵐ[(volume : Measure E)] g := by
    exact hFext_ae.trans (hindicator.trans hF_ind)
  have hFext_eq : Fext = F := by
    refine MeasureTheory.Lp.ext ?_
    simpa [g, F] using hFext_ae'
  have hnorm_F : ‖F‖ ≤ mS * ‖Bu - Bv‖ := by
    
    have hnorm_ext : ‖Fext‖ = ‖Fs‖ := by
      simp [Fext]
    
    have : ‖Fext‖ ≤ mS * ‖Bu - Bv‖ := by
      simpa [hnorm_ext] using hnorm_Fs
    simpa [hFext_eq] using this
  
  simpa [Su, Sv, Bu, Bv, F, dist_eq_norm, mS, mul_assoc] using hnorm_F

theorem smoothL2_image_closedBall_isCompact (hK : IsCompact K) (hKm : MeasurableSet K)
    (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ) {R : ℝ} (hR : 0 ≤ R) :
    IsCompact
        (closure
          (smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs '' Metric.closedBall (0 : _) R)) := by
  classical
  let : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  let s : Set E := Kψ (K := K) (ψ := ψ)
  have hs_compact : IsCompact s := isCompact_Kψ (K := K) (ψ := ψ) hK hψcs
  have hs : MeasurableSet s := hs_compact.measurableSet
  have hs_lt_top : (volume : Measure E) s < (⊤ : ℝ≥0∞) :=
    hs_compact.measure_lt_top (μ := (volume : Measure E))
  let μs : Measure E := (volume : Measure E).restrict s
  have : Fact ((volume : Measure E) s < (⊤ : ℝ≥0∞)) := ⟨hs_lt_top⟩
  have : IsFiniteMeasure μs := by
    infer_instance
  let mS : ℝ := (MeasureTheory.measureUnivNNReal μs) ^ ((2 : ℝ≥0∞).toReal⁻¹)
  have hmS : 0 ≤ mS := by
    have : 0 ≤ (MeasureTheory.measureUnivNNReal μs) := by simp
    exact Real.rpow_nonneg this _
  let U : Set (MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) :=
    Metric.closedBall (0 : _) R
  let A :
      Set (BoundedContinuousFunction (↥(Kψ (K := K) (ψ := ψ))) ℝ) :=
    smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs '' U
  let B : Set (E →₂[(volume : Measure E)] ℝ) :=
    smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs '' U
  have hA_compact : IsCompact (closure A) :=
    smoothBCF_image_closedBall_isCompact (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs (R := R) hR
  have hdist_smoothL2_le :=
    dist_smoothL2_le_mul_dist_smoothBCF (K := K) (ψ := ψ) hK hKm hψc hψcs
  have hTB_B : TotallyBounded B := by
    
    rw [Metric.totallyBounded_iff]
    intro ε hε
    by_cases hmS0 : mS = 0
    · let c : (E →₂[(volume : Measure E)] ℝ) :=
        smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs (0 : _)
      refine ⟨{c}, by simp [c], ?_⟩
      intro w hw
      rcases hw with ⟨u, huU, rfl⟩
      have hle :=
        hdist_smoothL2_le u (0 : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K))
      have hdist0 :
          dist (smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u)
              c = 0 := by
        have hmS0' :
            (MeasureTheory.measureUnivNNReal ((volume : Measure E).restrict s) : ℝ) ^
              ((2 : ℝ≥0∞).toReal⁻¹) = 0 := hmS0
        have :
            dist (smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u) c ≤ 0 := by
          have hle' := hle
          simp only [s] at hmS0'
          rw [hmS0', zero_mul] at hle'
          simpa [c] using hle'
        exact le_antisymm this dist_nonneg
      refine mem_iUnion.2 ?_
      refine ⟨c, mem_iUnion.2 ?_⟩
      refine ⟨by simp, ?_⟩
      
      simpa [Metric.mem_ball, hdist0] using hε
    · have hmSpos : 0 < mS := lt_of_le_of_ne hmS (Ne.symm hmS0)
      let deltaLoss : ℝ := ε / mS
      have hδpos : 0 < deltaLoss := div_pos hε hmSpos
      obtain ⟨t, htAsub, htFin, htCover⟩ :=
        exists_finite_cover_balls_of_isCompact_closure (s := A) (ε := deltaLoss) hA_compact hδpos
      let tFin : Finset (BoundedContinuousFunction (↥(Kψ (K := K) (ψ := ψ))) ℝ) :=
        htFin.toFinset
      have htFin_mem :
          ∀ {f : BoundedContinuousFunction (↥(Kψ (K := K) (ψ := ψ))) ℝ}, f ∈ tFin ↔ f ∈ t := by
        intro f
        simp [tFin, htFin.mem_toFinset (a := f)]
      let ι : Type _ := { f // f ∈ tFin }
      have hrep :
          ∀ f : ι,
            ∃ u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K),
              u ∈ U ∧
                smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u = f.1 := by
        intro f
        have hf_t : f.1 ∈ t := (htFin_mem (f := f.1)).1 f.2
        have hfA : f.1 ∈ A := htAsub hf_t
        rcases hfA with ⟨u, huU, huEq⟩
        exact ⟨u, huU, huEq⟩
      choose uOf huOfU huOfEq using hrep
      let tL2 : Set (E →₂[(volume : Measure E)] ℝ) :=
        Set.range fun f : ι => smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs (uOf f)
      have htL2_fin : tL2.Finite := Set.finite_range _
      refine ⟨tL2, htL2_fin, ?_⟩
      intro w hw
      rcases hw with ⟨u, huU, rfl⟩
      have hBu : (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u) ∈ A := by
        exact ⟨u, huU, rfl⟩
      have : smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u ∈ ⋃ x ∈ t, Metric.ball x deltaLoss :=
        htCover hBu
      rcases mem_iUnion.1 this with ⟨f, hf⟩
      rcases mem_iUnion.1 hf with ⟨hf_t, hf_ball⟩
      have hf_tFin : f ∈ tFin := (htFin_mem (f := f)).2 hf_t
      let f' : ι := ⟨f, hf_tFin⟩
      have hf_ball' :
          dist (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u) f < deltaLoss := hf_ball
      have hdist :
          dist (smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u)
              (smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs (uOf f')) < ε := by
        have hle := hdist_smoothL2_le u (uOf f')
        have hf_eq :
            smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs (uOf f') = f := by
          simpa [f'] using huOfEq f'
        have hdist' :
            dist (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u)
                (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs (uOf f')) < deltaLoss := by
          simpa [hf_eq] using hf_ball'
        have : mS * dist (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u)
                (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs (uOf f')) < ε := by
          have : mS * dist (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u)
                  (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs (uOf f')) < mS * deltaLoss := by
            exact mul_lt_mul_of_pos_left hdist' hmSpos
          have hmul : mS * deltaLoss = ε := by
            have hmS_ne : mS ≠ 0 := ne_of_gt hmSpos
            calc
              mS * deltaLoss = mS * (ε / mS) := by simp [deltaLoss]
              _ = mS * ε / mS := (mul_div_assoc mS ε mS).symm
              _ = ε := by simpa using (mul_div_cancel_left₀ ε hmS_ne)
          simpa [hmul] using this
        exact lt_of_le_of_lt hle this
      refine mem_iUnion.2 ?_
      refine ⟨smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs (uOf f'), ?_⟩
      refine mem_iUnion.2 ?_
      refine ⟨?_, hdist⟩
      
      exact ⟨f', rfl⟩
  
  have hTB_closure : TotallyBounded (closure B) := hTB_B.closure
  have hcomplete : IsComplete (closure B) := isClosed_closure.isComplete
  have hcompact_closure : IsCompact (closure B) :=
    isCompact_iff_totallyBounded_isComplete.2 ⟨hTB_closure, hcomplete⟩
  simpa [B, U] using hcompact_closure

end Volume

end

end L2Compactness
end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov
end

section

namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean
namespace L2Compactness

open scoped ENNReal MeasureTheory Topology Convolution Pointwise
open MeasureTheory Set

noncomputable section

section Volume

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

local instance instMeasurableSpaceEL2CompactnessFrechetKolmogorov : MeasurableSpace E := borel E
local instance instBorelSpaceEL2CompactnessFrechetKolmogorov : BorelSpace E := ⟨rfl⟩

variable {K : Set E} {ψ : E → ℝ}

lemma norm_smoothL2_sub_extendByZeroL2_le_of_integral_translateL2_sub_extendByZeroL2_le
    (hK : IsCompact K) (hKm : MeasurableSet K)
    (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ) (hψ0 : ∀ x, 0 ≤ ψ x)
    (hψint : ∫ x, ψ x ∂(volume : Measure E) = 1) {η : ℝ} (hη : 0 ≤ η)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K))
    (htrans :
      ∫ t,
          ‖(translateL2 (μ := (volume : Measure E)) (-t))
                (extendByZeroL2 (E := E) (K := K) hKm u)
              - extendByZeroL2 (E := E) (K := K) hKm u‖ ^ 2
        ∂kernelMeasure (E := E) ψ ≤ η ^ 2) :
    ‖smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u
        - extendByZeroL2 (E := E) (K := K) hKm u‖ ≤ η := by
  have hsq :
      ‖smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u
            - extendByZeroL2 (E := E) (K := K) hKm u‖ ^ 2 ≤ η ^ 2 := by
    refine (le_trans ?_ htrans)
    simpa using
      norm_sq_smoothL2_sub_extendByZeroL2_le_integral_norm_sq_translateL2_sub_extendByZeroL2
        (E := E) (K := K) (ψ := ψ) (hK := hK) (hKm := hKm) hψc hψcs hψ0 hψint u
  exact (sq_le_sq₀ (norm_nonneg _) hη).1 hsq

theorem totallyBounded_extendByZeroL2_image_of_forall_exists_translationIntegral_small
    (hK : IsCompact K) (hKm : MeasurableSet K) {R : ℝ} (hR : 0 ≤ R)
    {A : Set (MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K))}
    (hA : A ⊆ Metric.closedBall (0 : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) R)
    (hApprox :
      ∀ ε : ℝ, 0 < ε →
        ∃ ψ : E → ℝ, Continuous ψ ∧ HasCompactSupport ψ ∧ (∀ x, 0 ≤ ψ x) ∧
          (∫ x, ψ x ∂(volume : Measure E) = 1) ∧
          ∀ u ∈ A,
            ∫ t,
                ‖(translateL2 (μ := (volume : Measure E)) (-t))
                      (extendByZeroL2 (E := E) (K := K) hKm u)
                    - extendByZeroL2 (E := E) (K := K) hKm u‖ ^ 2
              ∂kernelMeasure (E := E) ψ ≤ (ε / 2) ^ 2) :
    TotallyBounded (extendByZeroL2 (E := E) (K := K) hKm '' A) := by
  classical
  
  refine (Metric.totallyBounded_iff).2 ?_
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  rcases hApprox ε hε with ⟨ψ, hψc, hψcs, hψ0, hψint, htrans⟩
  let B : Set (E →₂[(volume : Measure E)] ℝ) :=
    smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs '' Metric.closedBall (0 : _) R
  have hB_compact : IsCompact (closure B) :=
    smoothL2_image_closedBall_isCompact (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs (R := R) hR
  have hB_tot : TotallyBounded B :=
    (totallyBounded_closure).1 hB_compact.totallyBounded
  rcases Metric.finite_approx_of_totallyBounded hB_tot (ε / 2) hε2 with ⟨t, htB, htfin, hBcover⟩
  refine ⟨t, htfin, ?_⟩
  intro x hx
  rcases hx with ⟨u, huA, rfl⟩
  have huR : u ∈ Metric.closedBall (0 : _) R := hA huA
  have hSu_mem : smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u ∈ B := ⟨u, huR, rfl⟩
  have hSu_cover :
      smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u ∈
        ⋃ y, ⋃ (_ : y ∈ t), Metric.ball y (ε / 2) :=
    hBcover hSu_mem
  rcases Set.mem_iUnion.1 hSu_cover with ⟨y, hy⟩
  rcases Set.mem_iUnion.1 hy with ⟨hyT, hyBall⟩
  have hyDist : dist (smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u) y < ε / 2 := by
    simpa [Metric.ball, Set.mem_ofPred_eq] using hyBall
  have hdist_smooth_ext :
      dist (extendByZeroL2 (E := E) (K := K) hKm u)
          (smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u) ≤ ε / 2 := by
    have hη : 0 ≤ ε / 2 := le_of_lt hε2
    have hnorm :
        ‖smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u
            - extendByZeroL2 (E := E) (K := K) hKm u‖ ≤ ε / 2 :=
      norm_smoothL2_sub_extendByZeroL2_le_of_integral_translateL2_sub_extendByZeroL2_le
        (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs hψ0 hψint (η := ε / 2) hη u (htrans u huA)
    
    have hdist :
        dist (smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u)
            (extendByZeroL2 (E := E) (K := K) hKm u) ≤ ε / 2 := by
      simpa [dist_eq_norm] using hnorm
    simpa [dist_comm] using hdist
  have hxDist : dist (extendByZeroL2 (E := E) (K := K) hKm u) y < ε := by
    have htri :=
      dist_triangle (extendByZeroL2 (E := E) (K := K) hKm u)
        (smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u) y
    have hlt :
        dist (extendByZeroL2 (E := E) (K := K) hKm u)
              (smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u)
            + dist (smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u) y
          < ε / 2 + ε / 2 :=
      add_lt_add_of_le_of_lt hdist_smooth_ext hyDist
    have htmp :
        dist (extendByZeroL2 (E := E) (K := K) hKm u) y < ε / 2 + ε / 2 :=
      lt_of_le_of_lt htri hlt
    simpa [add_halves ε] using htmp
  have hxBall : extendByZeroL2 (E := E) (K := K) hKm u ∈ Metric.ball y ε := by
    simpa [Metric.ball, Set.mem_ofPred_eq] using hxDist
  exact Set.mem_iUnion.2 ⟨y, Set.mem_iUnion.2 ⟨hyT, hxBall⟩⟩

theorem isCompact_closure_extendByZeroL2_image_of_forall_exists_translationIntegral_small
    (hK : IsCompact K) (hKm : MeasurableSet K) {R : ℝ} (hR : 0 ≤ R)
    {A : Set (MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K))}
    (hA : A ⊆ Metric.closedBall (0 : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) R)
    (hApprox :
      ∀ ε : ℝ, 0 < ε →
        ∃ ψ : E → ℝ, Continuous ψ ∧ HasCompactSupport ψ ∧ (∀ x, 0 ≤ ψ x) ∧
          (∫ x, ψ x ∂(volume : Measure E) = 1) ∧
          ∀ u ∈ A,
            ∫ t,
                ‖(translateL2 (μ := (volume : Measure E)) (-t))
                      (extendByZeroL2 (E := E) (K := K) hKm u)
                    - extendByZeroL2 (E := E) (K := K) hKm u‖ ^ 2
              ∂kernelMeasure (E := E) ψ ≤ (ε / 2) ^ 2) :
    IsCompact (closure (extendByZeroL2 (E := E) (K := K) hKm '' A)) := by
  have ht :
      TotallyBounded (extendByZeroL2 (E := E) (K := K) hKm '' A) :=
    totallyBounded_extendByZeroL2_image_of_forall_exists_translationIntegral_small
      (E := E) (K := K) hK hKm hR hA hApprox
  exact (ht.closure).isCompact_of_isClosed isClosed_closure

end Volume

end

end L2Compactness
end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov
end

section

namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean
namespace L2Compactness

open scoped ENNReal MeasureTheory Topology
open MeasureTheory Set

noncomputable section

section Volume

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

local instance instMeasurableSpaceEL2CompactnessKernels : MeasurableSpace E := borel E
local instance instBorelSpaceEL2CompactnessKernels : BorelSpace E := ⟨rfl⟩
local instance instOpensMeasurableSpaceEL2CompactnessKernels : OpensMeasurableSpace E := by
  infer_instance

theorem exists_kernel_tsupport_subset_ball_integral_eq_one {deltaLoss : ℝ} (hδ : 0 < deltaLoss) :
    ∃ ψ : E → ℝ, Continuous ψ ∧ HasCompactSupport ψ ∧ (∀ x, 0 ≤ ψ x) ∧
      (∫ x, ψ x ∂(volume : Measure E) = 1) ∧ tsupport ψ ⊆ Metric.ball (0 : E) deltaLoss := by
  classical
  
  have hs : (Metric.ball (0 : E) deltaLoss) ∈ 𝓝 (0 : E) := Metric.ball_mem_nhds _ hδ
  rcases exists_contDiff_tsupport_subset (n := ⊤)
    (E := E) (s := Metric.ball (0 : E) deltaLoss) (x := (0 : E)) hs with
    ⟨f, hf_tsupp, hf_cs, hf_smooth, hf_range, hf0⟩
  have hf_cont : Continuous f := hf_smooth.continuous
  have hf_nonneg : ∀ x, 0 ≤ f x := by
    intro x
    have hx : f x ∈ Set.Icc (0 : ℝ) 1 := hf_range ⟨x, rfl⟩
    exact hx.1
  have hf0_ne : f (0 : E) ≠ 0 := by
    
    simp [hf0]
  
  have hIpos :
      0 < ∫ x, f x ∂(volume : Measure E) := by
    simpa using
      (Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := (volume : Measure E))
        hf_cont hf_cs hf_nonneg hf0_ne)
  set I : ℝ := ∫ x, f x ∂(volume : Measure E)
  have hI0 : I ≠ 0 := ne_of_gt hIpos
  have hIpos' : 0 < I := by simpa [I] using hIpos
  
  let ψ : E → ℝ := fun x => I⁻¹ * f x
  have hψc : Continuous ψ := by
    exact (continuous_const.mul hf_cont)
  have hψcs : HasCompactSupport ψ := by
    exact
      (HasCompactSupport.smul_left (f := fun _x : E => I⁻¹) (f' := f) hf_cs)
  have hψ0 : ∀ x, 0 ≤ ψ x := by
    intro x
    have hInv : 0 ≤ I⁻¹ := by
      have : 0 ≤ I := le_of_lt hIpos'
      simpa using inv_nonneg.2 this
    simpa [ψ] using mul_nonneg hInv (hf_nonneg x)
  have hψint : ∫ x, ψ x ∂(volume : Measure E) = 1 := by
    have : (∫ x, ψ x ∂(volume : Measure E)) = I⁻¹ * I := by
      
      simpa [ψ, I] using
        (MeasureTheory.integral_const_mul (μ := (volume : Measure E)) (r := I⁻¹) (f := f))
    simp [this, hI0]
  have hψ_tsupp : tsupport ψ ⊆ Metric.ball (0 : E) deltaLoss := by
    
    have hsub : tsupport ψ ⊆ tsupport f := by
      simpa [ψ, smul_eq_mul] using (tsupport_smul_subset_right (f := fun _x : E => I⁻¹) (g := f))
    exact hsub.trans hf_tsupp
  exact ⟨ψ, hψc, hψcs, hψ0, hψint, hψ_tsupp⟩

end Volume

end

end L2Compactness
end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov
end

section

namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean
namespace L2Compactness

open scoped ENNReal MeasureTheory Topology
open MeasureTheory Set

noncomputable section

section Volume

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

local instance instMeasurableSpaceEL2CompactnessTranslationIntegral : MeasurableSpace E := borel E
local instance instBorelSpaceEL2CompactnessTranslationIntegral : BorelSpace E := ⟨rfl⟩
local instance instOpensMeasurableSpaceEL2CompactnessTranslationIntegral :
    OpensMeasurableSpace E := by infer_instance

variable {ψ : E → ℝ}

lemma kernelMeasure_compl_ball_eq_zero_of_tsupport_subset {deltaLoss : ℝ}
    (hψsupp : tsupport ψ ⊆ Metric.ball (0 : E) deltaLoss) :
    kernelMeasure (E := E) ψ ((Metric.ball (0 : E) deltaLoss)ᶜ) = 0 := by
  classical
  have hψzero : ∀ x : E, x ∈ (Metric.ball (0 : E) deltaLoss)ᶜ → ψ x = 0 := by
    intro x hx
    have hx' : x ∉ tsupport ψ := by
      intro hx_ts
      exact hx (hψsupp hx_ts)
    exact image_eq_zero_of_notMem_tsupport (f := ψ) hx'
  have hmeas : MeasurableSet ((Metric.ball (0 : E) deltaLoss)ᶜ) :=
    (measurableSet_ball : MeasurableSet (Metric.ball (0 : E) deltaLoss)).compl
  have hEq :
      Set.EqOn (fun x : E => ENNReal.ofReal (ψ x)) 0 ((Metric.ball (0 : E) deltaLoss)ᶜ) := by
    intro x hx
    simp [hψzero x hx]
  
  simp [kernelMeasure, MeasureTheory.withDensity_apply, hmeas,
    MeasureTheory.setLIntegral_eq_zero
      (μ := (volume : Measure E))
      (s := (Metric.ball (0 : E) deltaLoss)ᶜ) hmeas hEq]

theorem integral_norm_sq_translateL2_sub_le_sq_of_tsupport_subset_ball
    (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ) (hψ0 : ∀ x, 0 ≤ ψ x)
    (hψint : ∫ x, ψ x ∂(volume : Measure E) = 1)
    {deltaLoss η : ℝ} (hη : 0 ≤ η) (hψsupp : tsupport ψ ⊆ Metric.ball (0 : E) deltaLoss)
    (F : (E →₂[(volume : Measure E)] ℝ))
    (hmod :
      ∀ t : E, t ∈ Metric.ball (0 : E) deltaLoss →
        ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ≤ η) :
    ∫ t,
        ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ^ 2
      ∂kernelMeasure (E := E) ψ ≤ η ^ 2 := by
  classical
  let μ : Measure E := kernelMeasure (E := E) ψ
  have : MeasureTheory.IsProbabilityMeasure μ :=
    ⟨kernelMeasure_univ (E := E) (ψ := ψ) hψc hψcs hψ0 hψint⟩
  have hμzero : μ ((Metric.ball (0 : E) deltaLoss)ᶜ) = 0 := by
    simpa [μ] using kernelMeasure_compl_ball_eq_zero_of_tsupport_subset (E := E) (ψ := ψ) hψsupp
  have hAE_ball : (Metric.ball (0 : E) deltaLoss) ∈ MeasureTheory.ae μ :=
    (MeasureTheory.mem_ae_iff.2 hμzero)
  
  have hAE_bound :
      ∀ᵐ t : E ∂μ,
        ‖‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ^ 2‖ ≤ η ^ 2 := by
    filter_upwards [hAE_ball] with t ht
    have hle : ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ≤ η := hmod t ht
    have hsq :
        ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ^ 2 ≤ η ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) hη).2 hle
    have hnonneg : 0 ≤ ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ^ 2 :=
      sq_nonneg _
    have hηnonneg : 0 ≤ η ^ 2 := sq_nonneg _
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg, abs_of_nonneg hηnonneg] using hsq
  have hnorm_int :
      ‖∫ t,
            ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ^ 2
          ∂μ‖ ≤ η ^ 2 * μ.real Set.univ := by
    simpa using
      (MeasureTheory.norm_integral_le_of_norm_le_const (μ := μ)
        (f := fun t : E => ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ^ 2)
        (C := η ^ 2) hAE_bound)
  have hμreal : μ.real Set.univ = 1 := by
    
    simp [MeasureTheory.measureReal_def]
  have hnonneg_int :
      0 ≤ ∫ t,
            ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ^ 2
          ∂μ := by
    refine MeasureTheory.integral_nonneg ?_
    intro t
    exact sq_nonneg _
  
  have habs :
      |∫ t,
            ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ^ 2
          ∂μ| ≤ η ^ 2 := by
    have := hnorm_int
    
    simpa [Real.norm_eq_abs, hμreal, mul_one] using this
  simpa [abs_of_nonneg hnonneg_int, μ] using habs

end Volume

end

end L2Compactness
end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov
end

section

namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean

open scoped ENNReal MeasureTheory Topology
open MeasureTheory Set

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local instance instMeasurableSpaceTranslationEstimate :
    MeasurableSpace E := borel E
local instance instBorelSpaceTranslationEstimate :
    BorelSpace E := ⟨rfl⟩
local instance instOpensMeasurableSpaceTranslationEstimate :
    OpensMeasurableSpace E := by
  infer_instance

def line (x a : E) (t : ℝ) : E :=
  x + t • a

lemma hasDerivAt_line (x a : E) (t : ℝ) :
    HasDerivAt (line (x := x) (a := a)) a t := by
  
  have hsmul : HasDerivAt (fun t : ℝ => t • a) a t := by
    simpa [one_smul] using (hasDerivAt_id t).smul_const a
  exact HasDerivAt.const_add x hsmul

lemma hasDerivAt_comp_line
    {f : E → ℝ} (hf : ContDiff ℝ 1 f) (x a : E) (t : ℝ) :
    HasDerivAt (fun t => f (line (x := x) (a := a) t))
      (fderiv ℝ f (line (x := x) (a := a) t) a) t := by
  have hf' : HasFDerivAt f (fderiv ℝ f (line (x := x) (a := a) t)) (line (x := x) (a := a) t) :=
    (hf.differentiable one_ne_zero).differentiableAt.hasFDerivAt
  exact
    HasFDerivAt.comp_hasDerivAt_of_eq t hf' (hasDerivAt_line (x := x) (a := a) t) rfl

lemma deriv_comp_line {f : E → ℝ} (hf : ContDiff ℝ 1 f) (x a : E) (t : ℝ) :
    deriv (fun t => f (line (x := x) (a := a) t)) t =
      fderiv ℝ f (line (x := x) (a := a) t) a :=
  (hasDerivAt_comp_line (hf := hf) (x := x) (a := a) t).deriv

section

variable [CompleteSpace E]

lemma enorm_fderiv_apply_le_enorm_grad_mul (f : E → ℝ) (x a : E) :
    ‖fderiv ℝ f x a‖ₑ ≤ ‖grad (E := E) f x‖ₑ * ‖a‖ₑ := by
  
  have h₁ :
      ‖fderiv ℝ f x a‖ₑ ≤ ‖fderiv ℝ f x‖ₑ * ‖a‖ₑ :=
    (ContinuousLinearMap.le_opENorm (f := fderiv ℝ f x) a)
  have h₂ : ‖grad (E := E) f x‖ₑ = ‖fderiv ℝ f x‖ₑ := by
    
    simp only [grad]
    exact
      (LinearIsometry.enorm_map
        (f := (InnerProductSpace.toDual ℝ E).symm.toLinearIsometry)
        (fderiv ℝ f x))
  
  simpa [h₂, mul_assoc, mul_left_comm, mul_comm] using h₁

lemma enorm_deriv_comp_line_le (x a : E) {f : E → ℝ} (hf : ContDiff ℝ 1 f) (t : ℝ) :
    ‖deriv (fun t => f (line (x := x) (a := a) t)) t‖ₑ ≤
      ‖a‖ₑ * ‖grad (E := E) f (line (x := x) (a := a) t)‖ₑ := by
  
  have :=
    enorm_fderiv_apply_le_enorm_grad_mul
      (E := E) (f := f) (x := line (x := x) (a := a) t) (a := a)
  
  simpa [deriv_comp_line (hf := hf) (x := x) (a := a) t,
    mul_comm, mul_left_comm, mul_assoc] using this

lemma enorm_sub_le_enorm_mul_lintegral_grad (x a : E) {f : E → ℝ} (hf : ContDiff ℝ 1 f) :
    ‖f (x + a) - f x‖ₑ ≤
      ‖a‖ₑ * ∫⁻ t in Set.Icc (0 : ℝ) 1, ‖grad (E := E) f (x + t • a)‖ₑ := by
  
  have hCont :
      ContDiffOn ℝ 1 (fun t : ℝ => f (x + t • a)) (Set.Icc (0 : ℝ) 1) := by
    
    have hInner : ContDiff ℝ ⊤ (fun t : ℝ => x + t • a) := by
      simpa [line] using
        (contDiff_const.add (contDiff_id.smul (contDiff_const : ContDiff ℝ ⊤ (fun _ : ℝ => a))))
    have hInner' : ContDiff ℝ 1 (fun t : ℝ => x + t • a) := hInner.of_le (by simp)
    exact (hf.comp hInner').contDiffOn
  have hFTC :
      ‖f (x + a) - f x‖ₑ ≤ ∫⁻ t in Set.Icc (0 : ℝ) 1, ‖deriv (fun t : ℝ => f (x + t • a)) t‖ₑ := by
    simpa using
      (enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc (f := fun t : ℝ => f (x + t • a))
        (a := (0 : ℝ)) (b := 1) hCont (by exact zero_le_one))
  refine hFTC.trans ?_
  have hDerivBound :
      (fun t : ℝ => ‖deriv (fun t : ℝ => f (x + t • a)) t‖ₑ)
        ≤ᵐ[Measure.restrict volume (Set.Icc (0 : ℝ) 1)]
          fun t : ℝ => ‖a‖ₑ * ‖grad (E := E) f (x + t • a)‖ₑ := by
    
    refine (ae_of_all _ fun t => ?_)
    
    simpa [line, mul_assoc, mul_left_comm, mul_comm] using
      (enorm_deriv_comp_line_le (x := x) (a := a) (f := f) hf (t := t))
  
  have :
      (∫⁻ t in Set.Icc (0 : ℝ) 1, ‖deriv (fun t : ℝ => f (x + t • a)) t‖ₑ) ≤
        ∫⁻ t in Set.Icc (0 : ℝ) 1, ‖a‖ₑ * ‖grad (E := E) f (x + t • a)‖ₑ := by
    exact lintegral_mono_ae hDerivBound
  refine this.trans ?_
  
  have hMeas :
      Measurable fun t : ℝ => ‖grad (E := E) f (x + t • a)‖ₑ := by
    
    have hgradCont : Continuous (grad (E := E) f) := continuous_grad (E := E) (f := f) (by
      
      exact hf)
    
    exact (hgradCont.comp (by
      have : Continuous (fun t : ℝ => x + t • a) := by
        fun_prop
      exact this)).measurable.enorm
  
  exact le_of_eq <| by
    simpa [mul_assoc] using
      (MeasureTheory.lintegral_const_mul (μ := volume.restrict (Set.Icc (0 : ℝ) 1)) (r := ‖a‖ₑ)
        (f := fun t : ℝ => ‖grad (E := E) f (x + t • a)‖ₑ) hMeas)

end

end

end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov
end

section

namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean

open scoped ENNReal MeasureTheory Topology
open MeasureTheory Set

noncomputable section

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local instance instMeasurableSpaceTranslationEstimateL2 :
    MeasurableSpace E := borel E
local instance instBorelSpaceTranslationEstimateL2 :
    BorelSpace E := ⟨rfl⟩
local instance instOpensMeasurableSpaceTranslationEstimateL2 :
    OpensMeasurableSpace E := by
  infer_instance
local instance instMeasurableAddTranslationEstimateL2 : MeasurableAdd E := by
  infer_instance

variable (μ : Measure E) [μ.IsAddRightInvariant] [IsFiniteMeasureOnCompacts μ] [SFinite μ]

abbrev μI : Measure ℝ := (volume.restrict (Set.Icc (0 : ℝ) 1))

lemma holderConj_two_two : (2 : ℝ).HolderConjugate (2 : ℝ) := by
  refine (Real.holderConjugate_iff).2 ?_
  constructor
  · linarith
  · norm_num

lemma lintegral_rpow_two_le_lintegral_rpow_two
    {g : ℝ → ℝ≥0∞} (hg : AEMeasurable g (μI : Measure ℝ)) :
    (∫⁻ t, g t ∂(μI : Measure ℝ)) ^ (2 : ℝ) ≤ ∫⁻ t, g t ^ (2 : ℝ) ∂(μI : Measure ℝ) := by
  
  have hHolder :
      (∫⁻ t, g t ∂(μI : Measure ℝ)) ≤
        (∫⁻ t, g t ^ (2 : ℝ) ∂(μI : Measure ℝ)) ^ (1 / (2 : ℝ)) *
          (∫⁻ _t : ℝ, (1 : ℝ≥0∞) ^ (2 : ℝ) ∂(μI : Measure ℝ)) ^ (1 / (2 : ℝ)) := by
    simpa [Pi.mul_apply] using
      (ENNReal.lintegral_mul_le_Lp_mul_Lq (μ := (μI : Measure ℝ)) holderConj_two_two
        hg (aemeasurable_const : AEMeasurable (fun _t : ℝ => (1 : ℝ≥0∞)) (μI : Measure ℝ)))
  have h1 : (∫⁻ _t : ℝ, (1 : ℝ≥0∞) ^ (2 : ℝ) ∂(μI : Measure ℝ)) ^ (1 / (2 : ℝ)) = (1 : ℝ≥0∞) := by
    
    simp
  have h :
      (∫⁻ t, g t ∂(μI : Measure ℝ)) ≤
        (∫⁻ t, g t ^ (2 : ℝ) ∂(μI : Measure ℝ)) ^ (1 / (2 : ℝ)) := by
    simpa [h1, mul_one] using hHolder
  
  have h' :=
    ENNReal.rpow_le_rpow h (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)
  
  simpa [ENNReal.rpow_mul] using (h'.trans_eq (by
    have : (1 / (2 : ℝ)) * (2 : ℝ) = (1 : ℝ) := by norm_num
    simpa [this] using
      (ENNReal.rpow_mul
        (∫⁻ t, g t ^ (2 : ℝ) ∂(μI : Measure ℝ))
        (1 / (2 : ℝ)) (2 : ℝ)).symm))

omit [IsFiniteMeasureOnCompacts μ] in

lemma lintegral_enorm_sub_sq_le (a : E) (f : ↥(C1c (E := E))) :
    (∫⁻ x, ‖f.1 (x + a) - f.1 x‖ₑ ^ (2 : ℝ) ∂μ) ≤
      ‖a‖ₑ ^ (2 : ℝ) * (∫⁻ x, ‖grad (E := E) f.1 x‖ₑ ^ (2 : ℝ) ∂μ) := by
  
  have hpt :
      ∀ x : E,
        ‖f.1 (x + a) - f.1 x‖ₑ ^ (2 : ℝ) ≤
          ‖a‖ₑ ^ (2 : ℝ) *
            ∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ) ∂(μI : Measure ℝ) := by
    intro x
    have h0 := enorm_sub_le_enorm_mul_lintegral_grad (E := E) (x := x) (a := a) (f := f.1)
      (hf := f.2.1)
    
    have h1 :
        ‖f.1 (x + a) - f.1 x‖ₑ ^ (2 : ℝ) ≤
          (‖a‖ₑ * ∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ∂(μI : Measure ℝ)) ^ (2 : ℝ) := by
      exact ENNReal.rpow_le_rpow h0 (by norm_num)
    have hcs :
        (∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ∂(μI : Measure ℝ)) ^ (2 : ℝ) ≤
          ∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ) ∂(μI : Measure ℝ) := by
      refine lintegral_rpow_two_le_lintegral_rpow_two (g := fun t : ℝ =>
        ‖grad (E := E) f.1 (x + t • a)‖ₑ) ?_
      
      have hgrad : Continuous (grad (E := E) f.1) := continuous_grad (E := E) (f := f.1) f.2.1
      have hline : Continuous fun t : ℝ => x + t • a := by
        fun_prop
      exact (hgrad.comp hline).measurable.enorm.aemeasurable
    
    calc
      ‖f.1 (x + a) - f.1 x‖ₑ ^ (2 : ℝ)
          ≤ (‖a‖ₑ * ∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ∂(μI : Measure ℝ)) ^ (2 : ℝ) := h1
      _ = ‖a‖ₑ ^ (2 : ℝ) *
          (∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ
            ∂(μI : Measure ℝ)) ^ (2 : ℝ) := by
          simpa using
            (ENNReal.mul_rpow_of_nonneg ‖a‖ₑ
              (∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ
                ∂(μI : Measure ℝ))
              (show (0 : ℝ) ≤ (2 : ℝ) by norm_num))
      _ ≤ ‖a‖ₑ ^ (2 : ℝ) *
          ∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ)
            ∂(μI : Measure ℝ) := by
          gcongr
      _ = ‖a‖ₑ ^ (2 : ℝ) *
          ∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ)
            ∂(μI : Measure ℝ) := rfl
  
  let F : E × ℝ → ℝ≥0∞ :=
    fun z => ‖grad (E := E) f.1 (z.1 + z.2 • a)‖ₑ ^ (2 : ℝ)
  have hmeas :
      AEMeasurable
        F (μ.prod (μI : Measure ℝ)) := by
    have hgrad : Continuous (grad (E := E) f.1) := continuous_grad (E := E) (f := f.1) f.2.1
    have hcont : Continuous fun z : E × ℝ => z.1 + z.2 • a := by
      fun_prop
    have hbase : Measurable fun z : E × ℝ => ‖grad (E := E) f.1 (z.1 + z.2 • a)‖ₑ := by
      exact (hgrad.comp hcont).measurable.enorm
    have hpow : Measurable fun r : ℝ≥0∞ => r ^ (2 : ℝ) :=
      (ENNReal.continuous_rpow_const (y := (2 : ℝ))).measurable
    exact (hpow.comp hbase).aemeasurable
  have hTonelli :
      (∫⁻ x, ∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ) ∂(μI : Measure ℝ) ∂μ) =
        ∫⁻ t, ∫⁻ x, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ) ∂μ ∂(μI : Measure ℝ) := by
    
    have hprod :
        (∫⁻ z, F z ∂μ.prod (μI : Measure ℝ)) =
          ∫⁻ x, ∫⁻ t, F (x, t) ∂(μI : Measure ℝ) ∂μ :=
      MeasureTheory.lintegral_prod (μ := μ) (ν := (μI : Measure ℝ)) F hmeas
    have hprod_symm :
        (∫⁻ z, F z ∂μ.prod (μI : Measure ℝ)) =
          ∫⁻ t, ∫⁻ x, F (x, t) ∂μ ∂(μI : Measure ℝ) :=
      MeasureTheory.lintegral_prod_symm (μ := μ) (ν := (μI : Measure ℝ)) F hmeas
    calc
      (∫⁻ x, ∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ) ∂(μI : Measure ℝ) ∂μ)
          = ∫⁻ z, F z ∂μ.prod (μI : Measure ℝ) := by
              simpa [F] using hprod.symm
      _ = ∫⁻ t, ∫⁻ x, F (x, t) ∂μ ∂(μI : Measure ℝ) := hprod_symm
      _ = ∫⁻ t, ∫⁻ x, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ) ∂μ ∂(μI : Measure ℝ) := by
              simp [F]
  
  have hShift :
      (∫⁻ t, ∫⁻ x, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ) ∂μ ∂(μI : Measure ℝ)) =
        ∫⁻ t, (∫⁻ x, ‖grad (E := E) f.1 x‖ₑ ^ (2 : ℝ) ∂μ) ∂(μI : Measure ℝ) := by
    refine MeasureTheory.lintegral_congr fun t => ?_
    
    have hmeas' : Measurable fun x : E => ‖grad (E := E) f.1 x‖ₑ ^ (2 : ℝ) := by
      have hgrad : Continuous (grad (E := E) f.1) := continuous_grad (E := E) (f := f.1) f.2.1
      have hbase : Measurable fun x : E => ‖grad (E := E) f.1 x‖ₑ := hgrad.measurable.enorm
      have hpow : Measurable fun r : ℝ≥0∞ => r ^ (2 : ℝ) :=
        (ENNReal.continuous_rpow_const (y := (2 : ℝ))).measurable
      exact hpow.comp hbase
    simpa [Function.comp, add_assoc] using
      (MeasureTheory.measurePreserving_add_right μ (t • a)).lintegral_comp (μ := μ) (ν := μ)
        (f := fun x : E => ‖grad (E := E) f.1 x‖ₑ ^ (2 : ℝ)) hmeas'
  have hEval :
      (∫⁻ t, (∫⁻ x, ‖grad (E := E) f.1 x‖ₑ ^ (2 : ℝ) ∂μ) ∂(μI : Measure ℝ)) =
        (∫⁻ x, ‖grad (E := E) f.1 x‖ₑ ^ (2 : ℝ) ∂μ) := by
    
    simp [μI, Measure.restrict_apply, Real.volume_Icc]
  
  have hInt :
      (∫⁻ x, ‖f.1 (x + a) - f.1 x‖ₑ ^ (2 : ℝ) ∂μ) ≤
        ‖a‖ₑ ^ (2 : ℝ) * (∫⁻ x, ‖grad (E := E) f.1 x‖ₑ ^ (2 : ℝ) ∂μ) := by
    calc
      (∫⁻ x, ‖f.1 (x + a) - f.1 x‖ₑ ^ (2 : ℝ) ∂μ)
          ≤ ∫⁻ x, ‖a‖ₑ ^ (2 : ℝ) *
                ∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ) ∂(μI : Measure ℝ) ∂μ := by
            refine MeasureTheory.lintegral_mono ?_
            intro x
            exact hpt x
      _ = ‖a‖ₑ ^ (2 : ℝ) *
            (∫⁻ x, ∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ) ∂(μI : Measure ℝ) ∂μ) := by
            
            have hInner :
                AEMeasurable
                  (fun x : E =>
                    ∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ) ∂(μI : Measure ℝ)) μ := by
              
              
              
              simpa [F] using (hmeas.lintegral_prod_right' (μ := μ) (ν := (μI : Measure ℝ)))
            simpa [mul_assoc] using
              (MeasureTheory.lintegral_const_mul'' (μ := μ) (r := ‖a‖ₑ ^ (2 : ℝ))
                (f := fun x : E =>
                  ∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ) ∂(μI : Measure ℝ)) hInner)
      _ = ‖a‖ₑ ^ (2 : ℝ) *
            (∫⁻ t, ∫⁻ x, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ) ∂μ ∂(μI : Measure ℝ)) := by
            exact congrArg (fun z => ‖a‖ₑ ^ (2 : ℝ) * z) hTonelli
      _ = ‖a‖ₑ ^ (2 : ℝ) *
            (∫⁻ t, (∫⁻ x, ‖grad (E := E) f.1 x‖ₑ ^ (2 : ℝ) ∂μ) ∂(μI : Measure ℝ)) := by
            exact congrArg (fun z => ‖a‖ₑ ^ (2 : ℝ) * z) hShift
      _ = ‖a‖ₑ ^ (2 : ℝ) * (∫⁻ x, ‖grad (E := E) f.1 x‖ₑ ^ (2 : ℝ) ∂μ) := by
            exact congrArg (fun z => ‖a‖ₑ ^ (2 : ℝ) * z) hEval
  exact hInt

lemma enorm_translateL2_sub_toL2_le (a : E) (f : ↥(C1c (E := E))) :
    ‖translateL2 (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f) -
        toL2 (μ := μ) (E := E) f‖ₑ ≤
      ‖a‖ₑ * ‖toL2Grad (μ := μ) (E := E) f‖ₑ := by
  classical
  
  have hL2 :
      (‖translateL2 (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f) -
          toL2 (μ := μ) (E := E) f‖ₑ : ℝ≥0∞) =
        MeasureTheory.eLpNorm (fun x : E => (f.1 (x + a) - f.1 x)) (2 : ℝ≥0∞) μ := by
    
    have h₁ :
        (translateL2 (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f) : E → ℝ) =ᵐ[μ]
          fun x => f.1 (x + a) := by
      have hf :
          (toL2 (μ := μ) (E := E) f : E → ℝ) =ᵐ[μ] f.1 :=
        (memLp_of_mem_C1c (μ := μ) (E := E) f.2).coeFn_toLp
      have hf' :
          (fun x => (toL2 (μ := μ) (E := E) f : E → ℝ) (x + a)) =ᵐ[μ] fun x => f.1 (x + a) := by
        exact
          (Measure.QuasiMeasurePreserving.ae_eq_comp
            (MeasureTheory.measurePreserving_add_right μ a).quasiMeasurePreserving hf)
      exact (translateL2_ae_eq (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f)).trans hf'
    have h₂ : (toL2 (μ := μ) (E := E) f : E → ℝ) =ᵐ[μ] fun x => f.1 x :=
      (memLp_of_mem_C1c (μ := μ) (E := E) f.2).coeFn_toLp
    have hsub :
        ((translateL2 (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f) -
              toL2 (μ := μ) (E := E) f : E →₂[μ] ℝ) : E → ℝ) =ᵐ[μ]
          fun x => f.1 (x + a) - f.1 x := by
      filter_upwards [Lp.coeFn_sub
        (translateL2 (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f))
        (toL2 (μ := μ) (E := E) f), h₁, h₂] with x hxsub hx1 hx2
      simpa [hx1, hx2, Pi.sub_apply] using hxsub
    
    let d : E →₂[μ] ℝ :=
      translateL2 (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f) - toL2 (μ := μ) (E := E) f
    have hd0 : (‖d‖ₑ : ℝ≥0∞) = MeasureTheory.eLpNorm (fun x : E => (d : E → ℝ) x) (2 : ℝ≥0∞) μ := by
      simp [MeasureTheory.Lp.enorm_def]
    have hd1 :
        MeasureTheory.eLpNorm (fun x : E => (d : E → ℝ) x) (2 : ℝ≥0∞) μ =
          MeasureTheory.eLpNorm (fun x : E => f.1 (x + a) - f.1 x) (2 : ℝ≥0∞) μ :=
      MeasureTheory.eLpNorm_congr_ae (μ := μ) (p := (2 : ℝ≥0∞)) (by simpa [d] using hsub)
    simpa [d] using hd0.trans hd1
  have hGrad :
      (‖toL2Grad (μ := μ) (E := E) f‖ₑ : ℝ≥0∞) =
        MeasureTheory.eLpNorm (fun x : E => grad (E := E) f.1 x) (2 : ℝ≥0∞) μ := by
    have h₁ :
        (toL2Grad (μ := μ) (E := E) f : E → E) =ᵐ[μ] fun x => grad (E := E) f.1 x :=
      (memLp_grad_of_mem_C1c (μ := μ) (E := E) f.2).coeFn_toLp
    have h0 :
        (‖toL2Grad (μ := μ) (E := E) f‖ₑ : ℝ≥0∞) =
          MeasureTheory.eLpNorm (fun x : E => (toL2Grad (μ := μ) (E := E) f : E → E) x)
            (2 : ℝ≥0∞) μ := by
      simp [MeasureTheory.Lp.enorm_def]
    have h1 :
        MeasureTheory.eLpNorm (fun x : E => (toL2Grad (μ := μ) (E := E) f : E → E) x)
            (2 : ℝ≥0∞) μ =
          MeasureTheory.eLpNorm (fun x : E => grad (E := E) f.1 x) (2 : ℝ≥0∞) μ :=
      MeasureTheory.eLpNorm_congr_ae (μ := μ) (p := (2 : ℝ≥0∞)) h₁
    exact h0.trans h1
  
  have hCore :
      MeasureTheory.eLpNorm (fun x : E => f.1 (x + a) - f.1 x) (2 : ℝ≥0∞) μ ≤
        ‖a‖ₑ * MeasureTheory.eLpNorm (fun x : E => grad (E := E) f.1 x) (2 : ℝ≥0∞) μ := by
    
    have h2_ne0 : (2 : ℝ≥0∞) ≠ 0 := by simp
    have h2_netop : (2 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞) := by simp
    have hf_meas : MeasureTheory.AEStronglyMeasurable (fun x : E => f.1 x) μ :=
      (memLp_of_mem_C1c (μ := μ) (E := E) f.2).aestronglyMeasurable
    have hshift_meas :
        MeasureTheory.AEStronglyMeasurable (fun x : E => f.1 (x + a) - f.1 x) μ := by
      have hshift : MeasureTheory.AEStronglyMeasurable (fun x : E => f.1 (x + a)) μ :=
        hf_meas.comp_quasiMeasurePreserving
          (MeasureTheory.measurePreserving_add_right μ a).quasiMeasurePreserving
      exact hshift.sub hf_meas
    have hgrad_meas :
        MeasureTheory.AEStronglyMeasurable (fun x : E => grad (E := E) f.1 x) μ :=
      (memLp_grad_of_mem_C1c (μ := μ) (E := E) f.2).aestronglyMeasurable
    rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal h2_ne0 h2_netop,
      MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal h2_ne0 h2_netop,
      ENNReal.toReal_ofNat]
    
    have hsq := lintegral_enorm_sub_sq_le (μ := μ) a f
    
    have hsq' :
        (∫⁻ x, ‖f.1 (x + a) - f.1 x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) ≤
          (‖a‖ₑ ^ (2 : ℝ) * ∫⁻ x, ‖grad (E := E) f.1 x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
      exact ENNReal.rpow_le_rpow hsq (by norm_num)
    
    have hsq'' :
        (∫⁻ x, ‖f.1 (x + a) - f.1 x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) ≤
          (‖a‖ₑ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
            (∫⁻ x, ‖grad (E := E) f.1 x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
      simpa [ENNReal.mul_rpow_of_nonneg, show (0 : ℝ) ≤ (1 / (2 : ℝ)) by nlinarith,
        mul_assoc, mul_left_comm, mul_comm] using hsq'
    have hroot : (‖a‖ₑ ^ (2 : ℕ)) ^ ((2 : ℝ)⁻¹) = ‖a‖ₑ := by
      
      have hnat : (‖a‖ₑ ^ (2 : ℕ)) = ‖a‖ₑ ^ (2 : ℝ) := by
        simp
      calc
        (‖a‖ₑ ^ (2 : ℕ)) ^ ((2 : ℝ)⁻¹) = (‖a‖ₑ ^ (2 : ℝ)) ^ ((2 : ℝ)⁻¹) :=
          congrArg (fun r : ℝ≥0∞ => r ^ ((2 : ℝ)⁻¹)) hnat
        _ = ‖a‖ₑ := by
          have := (ENNReal.rpow_mul ‖a‖ₑ (2 : ℝ) ((2 : ℝ)⁻¹)).symm
          have hmul : (2 : ℝ) * ((2 : ℝ)⁻¹) = (1 : ℝ) := by norm_num
          simpa [hmul, ENNReal.rpow_one] using this
    simpa [hroot, mul_assoc, mul_left_comm, mul_comm] using hsq''
  
  
  simpa [hL2, hGrad] using hCore

lemma norm_translateL2_sub_toL2_le (a : E) (f : ↥(C1c (E := E))) :
    ‖translateL2 (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f) -
        toL2 (μ := μ) (E := E) f‖ ≤
      ‖a‖ * ‖toL2Grad (μ := μ) (E := E) f‖ := by
  have h := enorm_translateL2_sub_toL2_le (μ := μ) (E := E) a f
  have hA_ne_top :
      (‖translateL2 (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f) -
            toL2 (μ := μ) (E := E) f‖ₑ : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞) := by
    simp [enorm]
  have hGrad_ne_top :
      (‖toL2Grad (μ := μ) (E := E) f‖ₑ : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞) := by
    simp [enorm]
  have hB_ne_top : (‖a‖ₑ * ‖toL2Grad (μ := μ) (E := E) f‖ₑ : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞) := by
    refine ENNReal.mul_ne_top ?_ hGrad_ne_top
    simp [enorm]
  have h' :
      (‖translateL2 (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f) -
            toL2 (μ := μ) (E := E) f‖ₑ).toReal ≤
        (‖a‖ₑ * ‖toL2Grad (μ := μ) (E := E) f‖ₑ).toReal := by
    exact (ENNReal.toReal_le_toReal hA_ne_top hB_ne_top).2 h
  simpa only [ENNReal.toReal_mul, toReal_enorm] using h'

end

end

end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov
end

section

namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean

open scoped ENNReal MeasureTheory Topology
open MeasureTheory Set

noncomputable section

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local instance instMeasurableSpaceTranslationEstimateH1 :
    MeasurableSpace E := borel E

variable (μ : Measure E) [μ.IsAddRightInvariant] [IsFiniteMeasureOnCompacts μ] [SFinite μ]

theorem norm_translateL2_sub_h1ToL2_le (a : E) (u : ↥(h1 (μ := μ) (E := E))) :
    ‖translateL2 (μ := μ) (F := ℝ) a (h1ToL2 (μ := μ) (E := E) u) -
        h1ToL2 (μ := μ) (E := E) u‖ ≤
      ‖a‖ * ‖h1ToL2Grad (μ := μ) (E := E) u‖ := by
  classical
  
  let V : Type _ := (E →₂[μ] ℝ) × (E →₂[μ] E)
  let S : Set V :=
    {v |
      ‖translateL2 (μ := μ) (F := ℝ) a v.1 - v.1‖ ≤
        ‖a‖ * ‖v.2‖}
  have hS_closed : IsClosed S := by
    
    have hf :
        Continuous fun v : V =>
          ‖translateL2 (μ := μ) (F := ℝ) a v.1 - v.1‖ := by
      
      
      have hfst : Continuous fun v : V => v.1 := continuous_fst
      have htr :
          Continuous fun v : V =>
            translateL2 (μ := μ) (F := ℝ) a v.1 := by
        
        exact (translateL2 (μ := μ) (F := ℝ) a).toContinuousLinearMap.continuous.comp hfst
      have hsub :
          Continuous fun v : V =>
            translateL2 (μ := μ) (F := ℝ) a v.1 - v.1 := by
        exact htr.sub hfst
      exact (continuous_norm.comp hsub)
    have hg :
        Continuous fun v : V =>
          ‖a‖ * ‖v.2‖ := by
      have hsnd : Continuous fun v : V => v.2 := continuous_snd
      have hnorm : Continuous fun v : V => ‖v.2‖ := continuous_norm.comp hsnd
      exact (continuous_const.mul hnorm)
    exact isClosed_le hf hg
  have hRange : (LinearMap.range (graph (μ := μ) (E := E)) : Set V) ⊆ S := by
    rintro v ⟨f, rfl⟩
    
    simpa [S, graph, toL2Linear, toL2GradLinear] using
      norm_translateL2_sub_toL2_le (μ := μ) (E := E) a f
  have hClosure :
      closure (LinearMap.range (graph (μ := μ) (E := E)) : Set V) ⊆ S :=
    closure_minimal hRange hS_closed
  have hu :
      (u : V) ∈ closure (LinearMap.range (graph (μ := μ) (E := E)) : Set V) := by
    
    have hu0 :
        (u : V) ∈
          ((LinearMap.range (graph (μ := μ) (E := E))).topologicalClosure :
            Set V) := by
      have hu0 : (u : V) ∈ h1 (μ := μ) (E := E) := u.2
      dsimp [h1] at hu0
      exact hu0
    have hu1 :
        (u : V) ∈
          ((LinearMap.range (graph (μ := μ) (E := E))).topologicalClosure :
            Set V) := hu0
    rw [Submodule.topologicalClosure_coe] at hu1
    exact hu1
  have huS : (u : V) ∈ S := hClosure hu
  
  simpa [S, V, h1ToL2, h1ToL2Grad] using huS

end

end

end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov
end

section

namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean

open scoped ENNReal MeasureTheory Topology
open MeasureTheory Set

noncomputable section

section Volume

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]

local instance instMeasurableSpaceRellich : MeasurableSpace E := borel E
local instance instBorelSpaceRellich : BorelSpace E := ⟨rfl⟩
local instance instFactOneLeTwoSobolevEuclideanRellich : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩

noncomputable def h1On (K : Set E) (hKm : MeasurableSet K) :
    Submodule ℝ (↥(h1 (μ := (volume : Measure E)) (E := E))) :=
  Submodule.comap
    (h1ToL2 (μ := (volume : Measure E)) (E := E)).toLinearMap
    (LinearMap.range
      ((MeasureTheory.Lp.extendByZeroₗᵢ
          (μ := (volume : Measure E)) (E := ℝ) (p := (2 : ℝ≥0∞)) (s := K) hKm).toLinearMap))

noncomputable def h1OnToL2 (K : Set E) (hKm : MeasurableSet K) :
    ↥(h1On K hKm) →L[ℝ] (E →₂[(volume : Measure E)] ℝ) :=
  (h1ToL2 (μ := (volume : Measure E)) (E := E)).comp (h1On K hKm).subtypeL

theorem isCompactOperator_h1OnToL2 {K : Set E} (_hK : IsCompact K) (hKm : MeasurableSet K) :
    IsCompactOperator (h1OnToL2 (E := E) K hKm) := by
  classical
  have hr : (0 : ℝ) < 1 := by norm_num
  let H1vol : Type _ := ↥(h1 (μ := (volume : Measure E)) (E := E))
  let T : ↥(h1On (E := E) K hKm) →L[ℝ] (E →₂[(volume : Measure E)] ℝ) :=
    h1OnToL2 (E := E) K hKm
  let A : Set (MeasureTheory.Lp ℝ (2 : ℝ≥0∞) ((volume : Measure E).restrict K)) :=
    {u |
      L2Compactness.extendByZeroL2 (E := E) (K := K) hKm u ∈
        T '' Metric.closedBall (0 : ↥(h1On (E := E) K hKm)) 1}
  let C : ℝ :=
    ‖h1ToL2 (μ := (volume : Measure E)) (E := E)‖
  have hCnonneg : 0 ≤ C := by
    exact norm_nonneg (h1ToL2 (μ := (volume : Measure E)) (E := E))
  have hA_ball :
      A ⊆
        Metric.closedBall
          (0 : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) ((volume : Measure E).restrict K))
          C := by
    intro u hu
    rcases hu with ⟨x, hx, hxEq⟩
    have hx' : ‖(x : H1vol)‖ ≤ (1 : ℝ) := by
      
      change ‖x‖ ≤ (1 : ℝ)
      simpa only [Metric.mem_closedBall,dist_zero_right x] using hx
    have hTx' : ‖T x‖ ≤ C := by
      have hTx : ‖T x‖ ≤ C * ‖(x : H1vol)‖ := by
        have h :=
          (h1ToL2 (μ := (volume : Measure E)) (E := E)).le_opNorm (x : H1vol)
        simpa [T, h1OnToL2, C] using h
      refine hTx.trans ?_
      have : C * ‖(x : H1vol)‖ ≤ C * (1 : ℝ) := mul_le_mul_of_nonneg_left hx' hCnonneg
      simpa [mul_one] using this
    have hnorm_ext :
        ‖L2Compactness.extendByZeroL2 (E := E) (K := K) hKm u‖ = ‖u‖ :=
      L2Compactness.norm_extendByZeroL2 (E := E) (K := K) hKm u
    have hu' : ‖u‖ ≤ C := by
      have : ‖L2Compactness.extendByZeroL2 (E := E) (K := K) hKm u‖ ≤ C := by
        simpa [hxEq] using hTx'
      simpa [hnorm_ext] using this
    simpa [Metric.closedBall, dist_eq_norm] using hu'
  have hApprox :
      ∀ ε : ℝ, 0 < ε →
        ∃ ψ : E → ℝ, Continuous ψ ∧ HasCompactSupport ψ ∧ (∀ x, 0 ≤ ψ x) ∧
          (∫ x, ψ x ∂(volume : Measure E) = 1) ∧
          ∀ u ∈ A,
            ∫ t,
                ‖(translateL2 (μ := (volume : Measure E)) (-t))
                      (L2Compactness.extendByZeroL2 (E := E) (K := K) hKm u)
                    - L2Compactness.extendByZeroL2 (E := E) (K := K) hKm u‖ ^ 2
              ∂L2Compactness.kernelMeasure (E := E) ψ ≤ (ε / 2) ^ 2 := by
    intro ε hε
    have hδ : 0 < ε / 2 := by linarith
    rcases
        L2Compactness.exists_kernel_tsupport_subset_ball_integral_eq_one
          (E := E) (deltaLoss := ε / 2) hδ with
      ⟨ψ, hψc, hψcs, hψ0, hψint, hψsupp⟩
    refine ⟨ψ, hψc, hψcs, hψ0, hψint, ?_⟩
    intro u huA
    rcases huA with ⟨x, hx, hxEq⟩
    have hxH1 : ‖(x : H1vol)‖ ≤ (1 : ℝ) := by
      change ‖x‖ ≤ (1 : ℝ)
      simpa only [Metric.mem_closedBall,dist_zero_right x] using hx
    have hmod :
        ∀ t : E, t ∈ Metric.ball (0 : E) (ε / 2) →
          ‖(translateL2 (μ := (volume : Measure E)) (-t)) (T x) - T x‖ ≤ ε / 2 := by
      intro t ht
      have ht' : ‖t‖ ≤ ε / 2 := le_of_lt (by
        simpa [Metric.ball, dist_eq_norm, mem_ofPred_eq] using ht)
      have hgrad_le :
          ‖h1ToL2Grad (μ := (volume : Measure E)) (E := E) (x : H1vol)‖ ≤ ‖(x : H1vol)‖ := by
        let V : Type _ := (E →₂[(volume : Measure E)] ℝ) × (E →₂[(volume : Measure E)] E)
        simpa [h1ToL2Grad, V] using (norm_snd_le (x := ((x : H1vol) : V)))
      have hgrad_le_one :
          ‖h1ToL2Grad (μ := (volume : Measure E)) (E := E) (x : H1vol)‖ ≤ (1 : ℝ) :=
        hgrad_le.trans hxH1
      have htr :=
        norm_translateL2_sub_h1ToL2_le (μ := (volume : Measure E)) (E := E) (-t) (x : H1vol)
      have htr' :
          ‖(translateL2 (μ := (volume : Measure E)) (-t))
                (h1ToL2 (μ := (volume : Measure E)) (E := E) (x : H1vol))
              - h1ToL2 (μ := (volume : Measure E)) (E := E) (x : H1vol)‖ ≤
            ‖t‖ * ‖h1ToL2Grad (μ := (volume : Measure E)) (E := E) (x : H1vol)‖ := by
        simpa [neg_neg] using htr
      have hle :
          ‖(translateL2 (μ := (volume : Measure E)) (-t)) (T x) - T x‖ ≤
            ‖t‖ * ‖h1ToL2Grad (μ := (volume : Measure E)) (E := E) (x : H1vol)‖ := by
        simpa [T, h1OnToL2, hxEq] using htr'
      refine hle.trans ?_
      have :
          ‖t‖ * ‖h1ToL2Grad (μ := (volume : Measure E)) (E := E) (x : H1vol)‖ ≤ (ε / 2) * 1 := by
        refine (mul_le_mul_of_nonneg_right ht' (norm_nonneg _)).trans ?_
        refine mul_le_mul_of_nonneg_left hgrad_le_one (by linarith)
      simpa [mul_one] using this
    have hη : 0 ≤ ε / 2 := le_of_lt hδ
    have hbound :=
      L2Compactness.integral_norm_sq_translateL2_sub_le_sq_of_tsupport_subset_ball
        (E := E) (ψ := ψ) hψc hψcs hψ0 hψint (deltaLoss := ε / 2) (η := ε / 2) hη hψsupp (T x) hmod
    simpa [hxEq] using hbound
  have hcomp : IsCompact (closure (T '' Metric.closedBall (0 : ↥(h1On (E := E) K hKm)) 1)) := by
    have hR : 0 ≤ C := hCnonneg
    have hA_eq :
        T '' Metric.closedBall (0 : ↥(h1On (E := E) K hKm)) 1 =
          L2Compactness.extendByZeroL2 (E := E) (K := K) hKm '' A := by
      ext y
      constructor
      · intro hy
        rcases hy with ⟨x, hx, rfl⟩
        have hxRange :
            (h1ToL2 (μ := (volume : Measure E)) (E := E) (x : H1vol)) ∈
              LinearMap.range
                ((MeasureTheory.Lp.extendByZeroₗᵢ
                      (μ := (volume : Measure E)) (E := ℝ)
                      (p := (2 : ℝ≥0∞)) (s := K) hKm).toLinearMap) := by
          
          
          
          have hxmem :
              (x : H1vol) ∈ h1On (E := E) K hKm := x.property
          dsimp [h1On] at hxmem
          change
              ((h1ToL2 (μ := (volume : Measure E)) (E := E)).toLinearMap
                    (x : H1vol)) ∈
                LinearMap.range
                  ((MeasureTheory.Lp.extendByZeroₗᵢ
                        (μ := (volume : Measure E)) (E := ℝ)
                        (p := (2 : ℝ≥0∞))
                        (s := K) hKm).toLinearMap)
          exact hxmem
        rcases hxRange with ⟨u, hu⟩
        have hu0 :
            (MeasureTheory.Lp.extendByZeroₗᵢ
                  (μ := (volume : Measure E)) (E := ℝ) (p := (2 : ℝ≥0∞)) (s := K) hKm) u =
              h1ToL2 (μ := (volume : Measure E)) (E := E) (x : H1vol) := by
          simpa using hu
        have hTx : T x = L2Compactness.extendByZeroL2 (E := E) (K := K) hKm u := by
          calc
            T x = h1ToL2 (μ := (volume : Measure E)) (E := E) (x : H1vol) := by
                  simp [T, h1OnToL2]
            _ = (MeasureTheory.Lp.extendByZeroₗᵢ
                  (μ := (volume : Measure E)) (E := ℝ) (p := (2 : ℝ≥0∞)) (s := K) hKm) u := by
                  simpa using hu0.symm
            _ = L2Compactness.extendByZeroL2 (E := E) (K := K) hKm u := by
                  simpa using
                    (L2Compactness.extendByZeroL2_eq_extendByZeroₗᵢ (E := E) (K := K) hKm u).symm
        refine ⟨u, ?_, hTx.symm⟩
        exact ⟨x, hx, hTx⟩
      · intro hy
        rcases hy with ⟨u, huA, rfl⟩
        exact huA
    have : IsCompact
        (closure (L2Compactness.extendByZeroL2 (E := E) (K := K) hKm '' A)) :=
    L2Compactness.isCompact_closure_extendByZeroL2_image_of_forall_exists_translationIntegral_small
      (E := E) (K := K) (hK := (_hK : IsCompact K))
      (hKm := hKm) hR hA_ball hApprox
    simpa [hA_eq] using this
  
  
  refine ⟨closure (T '' Metric.closedBall (0 : ↥(h1On (E := E) K hKm)) 1), hcomp, ?_⟩
  have hball :
      Metric.ball (0 : ↥(h1On (E := E) K hKm)) 1 ⊆
        T ⁻¹' closure (T '' Metric.closedBall (0 : ↥(h1On (E := E) K hKm)) 1) := by
    intro x hx
    refine subset_closure ?_
    refine ⟨x, ?_, rfl⟩
    exact Metric.ball_subset_closedBall hx
  exact Filter.mem_of_superset
    (Metric.ball_mem_nhds (x := (0 : ↥(h1On (E := E) K hKm))) (ε := (1 : ℝ)) hr) hball

end Volume

end

end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov
end

section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open Filter
open Filter
open scoped Topology
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap

open scoped BigOperators Classical
namespace CompletedGauss

section

open CompletedDyadic

def completedRamifiedStep : ℝ := (3:ℝ)^(1/3:ℝ)

end

end CompletedGauss

open scoped BigOperators Classical SchwartzMap

open MeasureTheory
open scoped BigOperators Classical

end

end OAI
end

section

namespace OAI

namespace SevenEighths.HeathBrownIteration

noncomputable section

def step (x : ℝ) : ℝ := (6 * x - 4) / (3 * x - 1)

def exponent : ℕ → ℝ
  | 0 => 2
  | n + 1 => step (exponent n)

end

end SevenEighths.HeathBrownIteration

end OAI
end

section

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
noncomputable section

def enlargementExponent (ξ : ℝ) : ℝ := (6*ξ-5)/(3*ξ-1)

end
end SevenEighths.CubicSieve

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseMoment

open scoped BigOperators Classical

noncomputable section

variable {F : Type*} [Field F] [Fintype F]

def zeroMark (x : F) : ℂ := if x = 0 then 1 else 0

def localFourier (f : F → ℂ) (ψ : AddChar F ℂ) (h : F) : ℂ :=
  ∑ t : F, f t * ψ (-(h * t))

def localReflectionActive (f : F → ℂ) (χ : MulChar F ℂ)
    (ψ : AddChar F ℂ) (σ ε : Fˣ) (x : F) : ℂ :=
  (Fintype.card F : ℂ)⁻¹ * ∑ h : Fˣ,
    localFourier f ψ h * ((χ⁻¹) ^ 2) (σ * h) *
      ψ (((ε : F) * x) * ((h⁻¹ : Fˣ) : F))

end

end SevenEighths.InverseMoment

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory
noncomputable section

def secondRelativeNorm (q : Fin 6 → ℝ) (G E V K X : ℝ) : Fin 6 → ℝ :=
  ![q 0/G,q 1/E,q 2/V,q 3/K,q 4/X,q 5/X]

def secondRelativeLog (q : Fin 6 → ℝ) (G E V K X : ℝ) (i : Fin 6) : ℝ :=
  Real.log (secondRelativeNorm q G E V K X i)

end
end SevenEighths.InverseMoment

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
noncomputable section
variable {σ ι : Type*} [DecidableEq σ] [DecidableEq ι]

def slotAssignmentWeight (I : Finset σ) (a : σ → ι → ℂ)
    (q : ∀ i ∈ I, ι) : ℂ := ∏ i ∈ I.attach, a i.val (q i.val i.property)

def indexedSlotAssignment (I : Finset σ) (q : ∀ i ∈ I, ι) : Fin I.card → ι :=
  fun j => q ((I.equivFin).symm j).val ((I.equivFin).symm j).property

end
end SevenEighths.InverseMoment

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
noncomputable section

def firstRootScale (s : Fin 9 → ℝ) : ℝ :=
  s 3 * Real.sqrt (s 4) * s 5 * Real.sqrt (s 7) * Real.sqrt (s 8)

end
end SevenEighths.InverseMoment

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
noncomputable section

def firstRelativeLog (q s : Fin 9 → ℝ) (i : Fin 9) : ℝ := Real.log (q i/s i)

end
end SevenEighths.InverseMoment

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseMoment

def CanonicalMargins (F M Q z c : ℝ) : Prop :=
  c ≤ F - M - Q - z ∧ c ≤ 4 * F - 3 * M - 6 * z

def decrease (ell A t g theta V : ℝ) : ℝ := ell + A + t + g - theta + V

def childF (F ell A t g theta V j delta : ℝ) : ℝ :=
  F - decrease ell A t g theta V - 2 * ell + j + delta

def childM (M ell A t g theta V j eta : ℝ) : ℝ :=
  M - 2 * decrease ell A t g theta V - 2 * ell + j + eta

def initialF (r z G P delta : ℝ) : ℝ := r + z - 2 * G - P + delta

def initialM (m r z G P eta tau : ℝ) : ℝ :=
  2 * (r + z - 2 * G) - m - 2 * P + 6 * eta + tau

end SevenEighths.InverseMoment

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMoment

def actualDepth (Mmax cutoff : ℝ) : ℕ := ⌈2*Mmax/(3*cutoff)⌉₊+1

end SevenEighths.InverseMoment
end

end OAI
end

section

namespace OAI

open scoped BigOperators NNReal
namespace SevenEighths.CenteredMoment
noncomputable section

variable {M R : Type*} [CommMonoid M] [CommRing R]

structure MaskedCharacter (M R : Type*) [CommMonoid M] [CommRing R] where
  residue : M →* R
  character : MulChar R ℂ
  keep : M → Prop
  keep_mul : ∀ a b, keep (a * b) ↔ keep a ∧ keep b

def volumeTerm (c I : ℂ) (t X : ℝ) : ℂ :=
  c * (X : ℂ) ^ (1 + Complex.I * t) * I

end
end SevenEighths.CenteredMoment

end OAI
end

section

namespace OAI

open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentCorrelation
noncomputable section
variable {A B : Type*} [CommRing A] [CommRing B] [Fintype A] [Fintype B]

def crtCharacter {S ι : Type*} [CommRing S] [Fintype ι] {R : ι → Type*}
    [∀ i, CommRing (R i)] (e : S ≃+* (∀ i, R i)) (χ : ∀ i, MulChar (R i) ℂ) :
    MulChar S ℂ where
  toFun x := ∏ i, χ i (e x i)
  map_one' := by simp
  map_mul' := by intro x y; simp [map_mul, Finset.prod_mul_distrib]
  map_nonunit' := by
    intro x hx
    have hn : ¬IsUnit (e x) := fun h => hx ((isUnit_map_iff e x).mp h)
    have hsome : ∃ i, ¬IsUnit (e x i) := by
      by_contra h
      apply hn
      exact Pi.isUnit_iff.mpr (by simpa only [not_exists, not_not] using h)
    obtain ⟨i, hi⟩ := hsome
    exact Finset.prod_eq_zero (Finset.mem_univ i) ((χ i).map_nonunit hi)

@[simp] theorem crtCharacter_apply {S ι : Type*} [CommRing S] [Fintype ι] {R : ι → Type*}
    [∀ i, CommRing (R i)] (e : S ≃+* (∀ i, R i)) (χ : ∀ i, MulChar (R i) ℂ) (x : S) :
    crtCharacter e χ x = ∏ i, χ i (e x i) := rfl

end
end SevenEighths.CenteredMomentCorrelation

end OAI
end

section

namespace OAI

open scoped BigOperators Classical
open NumberField
namespace SevenEighths.CenteredMomentCorrelation
noncomputable section
variable {K : Type*} [Field K] [NumberField K]

def primePowerReduction (P : Ideal (𝓞 K)) {c : ℕ} (hc : 1 ≤ c) :
    (𝓞 K ⧸ P ^ c) →+* (𝓞 K ⧸ P) :=
  Ideal.Quotient.factor (by simpa using Ideal.pow_le_pow_right (I := P) hc)

def primePowerCharacter (P : Ideal (𝓞 K)) {c : ℕ} (hc : 1 ≤ c)
    (χ : MulChar (𝓞 K ⧸ P) ℂ) : MulChar (𝓞 K ⧸ P ^ c) ℂ where
  __ := χ.toMonoidHom.comp (primePowerReduction P hc).toMonoidHom
  map_nonunit' := by
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    change χ (Ideal.Quotient.mk P a) = 0
    apply χ.map_nonunit
    intro ha
    exact hx ((Ideal.Quotient.isUnit_mk_pow_iff_isUnit_mk P (by omega)).mpr ha)

omit [NumberField K] in
@[simp] theorem primePowerCharacter_apply (P : Ideal (𝓞 K)) {c : ℕ} (hc : 1 ≤ c)
    (χ : MulChar (𝓞 K ⧸ P) ℂ) (x : 𝓞 K ⧸ P ^ c) :
    primePowerCharacter P hc χ x = χ (primePowerReduction P hc x) := rfl

section Local
variable (P : Ideal (𝓞 K)) [P.IsMaximal] {c : ℕ} (hc : 1 ≤ c)
variable [Fintype (𝓞 K ⧸ P ^ c)] [Fintype (𝓞 K ⧸ P)]
local instance : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P

end Local
end
end SevenEighths.CenteredMomentCorrelation

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeExceptionalRows
open HeckeFamily UniqueFactorizationMonoid

def rows (S : Finset (Ideal O)) : Set O :=
  {u | u ≠ 0 ∧ ∀ P ∈ normalizedFactors (Ideal.span {u}),
    P ∈ S ∧ (normalizedFactors (Ideal.span {u})).count P < 6}

def bound (S : Finset (Ideal O)) : ℕ := ((∏ P ∈ S, P)^5).absNorm

end SevenEighths.HeckeExceptionalRows

end

end OAI
end

section

namespace OAI

namespace SevenEighths.EulerFactors

noncomputable section

def factor (N : ℝ) (a s : ℂ) : ℂ := 1 - a * (N : ℂ) ^ (-s)

def deletedProduct {ι : Type*} (S : Finset ι) (N : ι → ℝ) (a : ι → ℂ)
    (s : ℂ) : ℂ := ∏ p ∈ S, factor (N p) (a p) s

end

end SevenEighths.EulerFactors

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.ProbeCompensation

def tupleOperation {α : Type*} [CommMonoid α] {K : ℕ}
    (p : Fin K → α) (q : α → ℝ) (η : α → ℂ)
    (F : α → ℝ → ℝ → ℝ → ℂ) (X Y Z : ℝ) : ℂ :=
  ∑ J ∈ (Finset.univ : Finset (Fin K)).powerset,
    (-1 : ℂ) ^ J.card * ((q (∏ i ∈ J, p i) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
      star (η (∏ i ∈ Finset.univ \ J, p i)) *
      F (∏ i ∈ Finset.univ \ J, p i)
        (X / q (∏ i ∈ J, p i)) (Y / q (∏ i ∈ J, p i))
        (Z * q (∏ i ∈ Finset.univ \ J, p i))

end SevenEighths.ProbeCompensation
end

end OAI
end

section

namespace OAI

namespace SevenEighths.ProbeGauss
open scoped BigOperators Classical
noncomputable section

def frequencyGauss {F : Type*} [Field F] [Fintype F]
    (ξ : MulChar F ℂ) (ψ : AddChar F ℂ) (h : F) : ℂ :=
  ∑ v : F, ξ v * ψ (h * v)

def normalizedGauss {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) : ℂ :=
  gaussSum χ ψ / (Real.sqrt (Fintype.card F) : ℂ)

end
end SevenEighths.ProbeGauss

end OAI
end

section

namespace OAI

noncomputable section

namespace SevenEighths.InverseMoment

def firstPassEpsilon (F eta:ℝ):ℝ:=eta/(10*F+32)
def sourceMassEpsilon (F eta:ℝ):ℝ:=2*eta/(20*(3*F+16)+30)

end SevenEighths.InverseMoment

end

end OAI
end

section

namespace OAI

namespace SevenEighths.Probe
noncomputable section

def principalScalar {ι : Type*} (slots : Finset ι) (Z ℓ : ℝ) (S : ι → ℝ) : ℝ :=
  (-1) ^ slots.card * Z ^ (-ℓ / 6) * ∏ i ∈ slots, S i

end
end SevenEighths.Probe

end OAI
end

section

namespace OAI

namespace SevenEighths.HeckeDetectorProfiles
open scoped BigOperators Classical ContDiff FourierTransform SchwartzMap
noncomputable section

def expNeg (x : ℝ) : ℂ := Complex.exp (-(x : ℂ))

lemma expNeg_smooth : ContDiff ℝ ∞ expNeg := by
  exact Complex.ofRealCLM.contDiff.neg.cexp

def logSourceFun (Ω V T : ℝ → ℂ) (A B C y : ℝ) : ℂ :=
  Ω y*(1-V (A*Real.exp y))*expNeg (B*Real.exp y)*T (C*Real.exp y)

lemma logSource_smooth (Ω V T : ℝ → ℂ) (hΩ : ContDiff ℝ ∞ Ω)
    (hV : ContDiff ℝ ∞ V) (hT : ContDiff ℝ ∞ T) (A B C : ℝ) :
    ContDiff ℝ ∞ (logSourceFun Ω V T A B C) := by
  unfold logSourceFun
  have hE := expNeg_smooth
  fun_prop

lemma logSource_compact (Ω V T : ℝ → ℂ) (hΩ : HasCompactSupport Ω) (A B C : ℝ) :
    HasCompactSupport (logSourceFun Ω V T A B C) :=
  ((hΩ.mul_right).mul_right).mul_right

def logSource (Ω V T : ℝ → ℂ) (hΩc : HasCompactSupport Ω)
    (hΩ : ContDiff ℝ ∞ Ω) (hV : ContDiff ℝ ∞ V) (hT : ContDiff ℝ ∞ T)
    (A B C : ℝ) : SchwartzMap ℝ ℂ :=
  (logSource_compact Ω V T hΩc A B C).toSchwartzMap (logSource_smooth Ω V T hΩ hV hT A B C)

@[simp] lemma logSource_apply (Ω V T : ℝ → ℂ) (hΩc : HasCompactSupport Ω)
    (hΩ : ContDiff ℝ ∞ Ω) (hV : ContDiff ℝ ∞ V) (hT : ContDiff ℝ ∞ T)
    (A B C y : ℝ) :
    logSource Ω V T hΩc hΩ hV hT A B C y =
      Ω y*(1-V (A*Real.exp y))*expNeg (B*Real.exp y)*T (C*Real.exp y) := rfl

end
end SevenEighths.HeckeDetectorProfiles

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical Topology
open Set Filter Metric Complex

namespace SevenEighths.LogarithmicControl

def uniformTheta (e : ℝ) : ℝ := 1 - Real.log (1 + e) / Real.log (200 / 49)

def outerConstant (e A M : ℝ) : ℝ := (4 * M + 4 * A) / e

end SevenEighths.LogarithmicControl

end

end OAI
end

section

namespace OAI

noncomputable section
open Set Filter
open scoped Topology
namespace SevenEighths.HeckeMellinIdentity

def regularized (P : WeakFEPair ℂ) (s : ℂ) : ℂ :=
  s * (s - 1) * P.Λ₀ s - (s - 1) * P.f₀ + s * P.ε * P.g₀

theorem regularized_entire (P : WeakFEPair ℂ) : Differentiable ℂ (regularized P) := by
  unfold regularized
  have hd := P.differentiable_Λ₀
  fun_prop

theorem regularized_eq (P : WeakFEPair ℂ) (hk : P.k = 1) {s : ℂ}
    (h0 : s ≠ 0) (h1 : s ≠ 1) : regularized P s = s * (s-1) * P.Λ s := by
  unfold regularized WeakFEPair.Λ
  rw [hk]
  simp only [smul_eq_mul, Complex.ofReal_one]
  have h1' : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  field_simp
  ring

end SevenEighths.HeckeMellinIdentity

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical Topology BigOperators
open Set MeasureTheory
namespace SevenEighths.HeckeStripActual
open HeckeFamily

variable (c : O) [NeZero c]

instance : Fintype (O ⧸ Ideal.span {c}) := by
  letI : Finite (O ⧸ Ideal.span {c}) := Ring.HasFiniteQuotients.finiteQuotient
    (by simpa only [ne_eq, Ideal.span_singleton_eq_bot] using NeZero.ne c)
  exact Fintype.ofFinite _

def conductor : ℝ := Ideal.absNorm (Ideal.span {c})

end SevenEighths.HeckeStripActual

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical Topology
open Set Metric
namespace SevenEighths.HeckeLogarithmic
open HeckeFamily

def complexity (η : Character) (t : ℝ) : ℝ :=
  2*(η.modulus.absNorm : ℝ)*(3+|t|)^2

end SevenEighths.HeckeLogarithmic

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped Classical BigOperators Topology
open Set Complex
namespace SevenEighths.HeckeDetectorDyadicBridge
open HeckeFamily

def inverseProfile (V W : ℝ→ℂ) (Dstar D : ℝ) (x : ℝ) : ℂ :=
  V (D*x/Dstar)*W x

end SevenEighths.HeckeDetectorDyadicBridge

end

end OAI
end

section

namespace OAI

noncomputable section
namespace SevenEighths.HeckeDetectorRowCount

def denominator (x : ℝ) : ℝ := 3-17*x/9

def primeWeight (x : ℝ) : ℝ := (2-8*x/9)*(1-x)

def crossing (x t : ℝ) : ℝ := ((2-8*x/9)*t-5*x/9)/denominator x

def inverseExponent (δ x r : ℝ) : ℝ := 1-δ*(x+(1-x)*r)

def plainExponent (δ x t r : ℝ) : ℝ := 1-δ*(4*x/9+(2-8*x/9)*(t-r))

def shortExponent (δ x t : ℝ) : ℝ := 1-δ+δ*primeWeight x/denominator x*(3/2-t)

def longExponent (δ t : ℝ) : ℝ := 1-δ+(5/6-δ)*(t-1)

end SevenEighths.HeckeDetectorRowCount

end

end OAI
end

section

namespace OAI

noncomputable section
namespace SevenEighths.HeckeDetectorBranchBudget
open HeckeDetectorRowCount

def commonLoss (ε εm mesh ν : ℝ) : ℝ := 154*ε+εm+mesh+ν

end SevenEighths.HeckeDetectorBranchBudget

end

end OAI
end

section

namespace OAI

noncomputable section
open Filter
open scoped Topology
namespace SevenEighths.HeckePrimeScale
open HeckeFamily

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ)

end SevenEighths.HeckePrimeScale

end

end OAI
end

section

namespace OAI

noncomputable section
open Filter Set
open scoped Topology ContDiff
namespace SevenEighths.HeckePrimeAmplitudeActual
open HeckeFamily
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ)

end SevenEighths.HeckePrimeAmplitudeActual

end

end OAI
end

section

namespace OAI

noncomputable section
open Filter
namespace SevenEighths.HeckeInverseAmplification

def amplificationPower (c r : ℝ) : ℝ := max 0 (((1+c)*r-1)/6)
def sourceExponent (r : ℝ) : ℝ := max 1 ((1+5*r)/6)

end SevenEighths.HeckeInverseAmplification

end

end OAI
end

section

namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler

def markedFactor (R V qInv K J : ℂ) (a : ℕ) : ℂ :=
  ((R * (1 - qInv) - K * V ^ a) / (1 - V) + J) / (1 - R)

end SevenEighths.ProbeEuler
end

end OAI
end

section

namespace OAI

namespace SevenEighths.ProbeLocal
noncomputable section

def localFactor (V W Pstar : ℂ) : ℂ := 1 / (1 - V) + W / (1 - W) + Pstar

def localCorrection (V W D Pstar : ℂ) : ℂ :=
  localFactor V W Pstar * ((1 - V) * (1 - W)) / (1 - D)

def continuedCorrection (V W D Pstar : ℂ) : ℂ :=
  (1 - V * W + (1 - V) * (1 - W) * Pstar) / (1 - D)

def compensatedReplacement (V W D Pstar B q : ℂ) : ℂ :=
  ((B - q) * (1 - V) * (1 - W) * Pstar - q * (1 - V * W)) / (1 - D)

end
end SevenEighths.ProbeLocal

end OAI
end

section

namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler

def sourceWeightedScalar (Q : ℝ) (eta a gamma1 C omega x w z scalar : ℂ)
    (e l k m : ℕ) : ℂ :=
  (-1:ℂ)^e * gamma1^(-(e:ℤ)) * eta^e * (a*C)^l *
    omega^((((e+3*l)*k:ℕ):ℤ)-(e*l+l.choose 2:ℕ)) * scalar *
    (Q:ℂ)^(-(x+1/2)*(e:ℂ)-(1+3*x)*(l:ℂ)-w*(k:ℂ)-6*z*(m:ℂ))

open CompletedGauss

end SevenEighths.ProbeEuler
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open Filter
namespace SevenEighths.ProbeEulerFinsupp
variable {α β : Type*} [AddCommMonoid β]

def markedArray (T : Finset α) (m f : α→β→ℂ) (v : α→₀β) : ℂ :=
  (∏a∈T,m a (v a))*v.prod f

def markedLocal (T : Finset α) (m f : α→β→ℂ) (a : α) (b : β) : ℂ :=
  (if a∈T then m a b else 1)*f a b

end SevenEighths.ProbeEulerFinsupp
end

end OAI
end

section

namespace OAI

noncomputable section
open MeasureTheory Set Filter Asymptotics
open scoped FourierTransform RealInnerProductSpace Topology
namespace SevenEighths.ProbeRadialMellin

def laplace (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ r : ℝ in Ioi 0, f r * Complex.exp (-(t*r : ℝ))

def paperConstant : ℝ := 2*Real.pi/Real.sqrt 3

end SevenEighths.ProbeRadialMellin

end

end OAI
end

section

namespace OAI

noncomputable section
open MeasureTheory Set Filter Asymptotics Complex
open scoped Topology
namespace SevenEighths.HeckeSignalShift
open HeckeFamily Continuation

def infinityConstant (a C : ℝ) (n : ℕ) : ℝ :=
  ‖(1/(2*Real.pi) : ℂ)‖*Real.exp ((a-5/6)^2)*((3/2)*C)*
    ∫ y : ℝ, polynomialGaussian n y

end SevenEighths.HeckeSignalShift

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap ContDiff
namespace SevenEighths.InverseInitialOverlapSource
variable {σ ι : Type*} [DecidableEq σ] [DecidableEq ι]

def tupleCoordinate (I : Finset σ) (y : σ→ι→ℝ) (q : ∀i∈I,ι) (i : σ) : ℝ :=
  if hi:i∈I then y i (q i hi) else 1

end SevenEighths.InverseInitialOverlapSource

end

end OAI
end

section

namespace OAI

noncomputable section
namespace SevenEighths.DetectorDictionaryInverseRawGeometry
open InverseMoment

def capacityGap (c : ℝ) : ℝ:=c/(1+c)

end SevenEighths.DetectorDictionaryInverseRawGeometry

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentRayNonprincipal
open HeckeFamily
local notation "O" => HeckeFamily.O

variable (M:Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)

end SevenEighths.CenteredMomentRayNonprincipal

end

end OAI
end

section

namespace OAI

namespace SevenEighths.Endpoint

noncomputable section

def denominator (y : ℝ) : ℝ := (37 + 34 * y) / 18

def primeWeight (y : ℝ) : ℝ := (7 + 18 * y + 8 * y ^ 2) / 9

def balanceDenominator (δ y : ℝ) : ℝ :=
  (5 / 6 - δ) * denominator y + δ * primeWeight y

def certificateWeight (y : ℝ) : ℝ := 51 + 41 * y

def balancedCutoff (δ y : ℝ) : ℝ :=
  1 + δ * primeWeight y / (2 * balanceDenominator δ y)

def balancedRowCount (δ y : ℝ) : ℝ :=
  1 - 5 / 6 + (5 / 6 - δ) * balancedCutoff δ y

def balancedExponent (δ y : ℝ) : ℝ :=
  -(1 / 48) + (2 / 3) * δ + δ * (1 / 2 - y) / 6 -
    (13 / 16) * (1 - balancedRowCount δ y)

end

end SevenEighths.Endpoint

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open MeasureTheory
noncomputable section

def reciprocalWindow (w : ℝ→ℂ) (α M : ℝ) (y : ℝ) : ℂ :=
  (Real.exp (-α*M):ℂ)*(w y*(Real.exp (-α*y):ℂ))

def reciprocalKernelWindows (windows : Fin 4→ℝ→ℂ) (M : Fin 4→ℝ) : Fin 4→ℝ→ℂ :=
  ![windows 0,windows 1,reciprocalWindow (windows 2) (1/2) (M 2),
    reciprocalWindow (windows 3) 1 (M 3)]

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
noncomputable section

def sourceDependentExtension {X Y : Type*} {D : Y→Type*}
    (f : X→Y) (C : ∀ x, D (f x)) (fallback : ∀ y, D y) (y : Y) : D y :=
  if h : ∃ x, f x=y then h.choose_spec ▸ C h.choose else fallback y

variable {α β γ σ : Type*} [Fintype α] [Fintype β] [Fintype σ]

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section

namespace OAI

noncomputable section
open MeasureTheory
namespace SevenEighths.ProbePhysical

def sourceScale (X Y Z : ℝ) (x w z : ℂ) : ℂ :=
  (X:ℂ)^(1/2-z)*(Z:ℂ)^(x+z-1)*(Y:ℂ)^(w-1)

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open MeasureTheory
namespace SevenEighths.ProbePhysical

def quadShuffle {A B C D : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [MeasurableSpace D] : (A×B)×(C×D) ≃ᵐ (A×C)×(B×D) where
  toFun p := ((p.1.1,p.2.1),(p.1.2,p.2.2))
  invFun p := ((p.1.1,p.2.1),(p.1.2,p.2.2))
  left_inv p := rfl
  right_inv p := rfl
  measurable_toFun := by change Measurable (fun p : (A×B)×(C×D)=>((p.1.1,p.2.1),(p.1.2,p.2.2)));fun_prop
  measurable_invFun := by change Measurable (fun p : (A×C)×(B×D)=>((p.1.1,p.2.1),(p.1.2,p.2.2)));fun_prop

def physicalNestingEquiv {A B C D E F : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [MeasurableSpace D] [MeasurableSpace E] [MeasurableSpace F] :
    (A×(B×C))×((D×E)×F) ≃ᵐ A×(F×(D×(B×(E×C)))) where
  toFun p := (p.1.1,(p.2.2,(p.2.1.1,(p.1.2.1,(p.2.1.2,p.1.2.2)))))
  invFun p := ((p.1,(p.2.2.2.1,p.2.2.2.2.2)),((p.2.2.1,p.2.2.2.2.1),p.2.1))
  left_inv p := rfl
  right_inv p := rfl
  measurable_toFun := by
    change Measurable (fun p : (A×(B×C))×((D×E)×F)=>
      (p.1.1,(p.2.2,(p.2.1.1,(p.1.2.1,(p.2.1.2,p.1.2.2))))))
    fun_prop
  measurable_invFun := by
    change Measurable (fun p : A×(F×(D×(B×(E×C))))=>
      ((p.1,(p.2.2.2.1,p.2.2.2.2.2)),((p.2.2.1,p.2.2.2.2.1),p.2.1)))
    fun_prop

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler
open CompletedGauss
local notation "O" => HeckeFamily.O

@[fun_prop] lemma measurable_const_cpow {α : Type*} [MeasurableSpace α]
    (Q : ℂ) (hQ : Q≠0) (f : α→ℂ) (hf : Measurable f) : Measurable (fun t=>Q^(f t)) :=
  ((continuous_id.const_cpow (Or.inl hQ)).measurable).comp hf

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler

def selectedFirstBound (Q R : ℝ) : ℝ :=
  2*((Q^R+Q^(1/100:ℝ))*2*(1+Q^(1/100:ℝ))*388+Q^(1/100:ℝ)*(1+Q^(1/100:ℝ)))

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeDetectorAdaptiveCutoff
open HeckeFamily HeckeDetectorRowCount

def cutoff (δ q : ℝ) : ℝ :=
  if δ≤5/6 then Endpoint.balancedCutoff δ (1/2-min (1/2) (max 0 (q/δ))) else 3/2

end SevenEighths.HeckeDetectorAdaptiveCutoff

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeDetectorRawFiber
open HeckeFamily
variable {M : Ideal O} {H : Subgroup (O ⧸ M)ˣ} {Label Slot : Type*}
  {U a ε tstar T allowance : ℝ} {i : ℕ}

def fiberConstant (C height K : ℝ) : ℝ := (192*(1+height)*C)*max 1 K

end SevenEighths.HeckeDetectorRawFiber

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter
namespace SevenEighths.HeckeDetectorClassBudget

def alphabetBound (mesh : ℝ) : ℕ := 2+(⌈(1/2 : ℝ)/mesh⌉+1 : ℤ).toNat

end SevenEighths.HeckeDetectorClassBudget

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical ContDiff Topology
open Filter Set Metric
namespace SevenEighths.ProbePhysical

def gaussianFlow (R : ℝ) (z : ℂ) : ℂ :=
  ((1/(2*Real.pi):ℝ):ℂ)*(Real.pi:ℂ)^(1/2:ℂ)*
    Complex.exp (-((Real.log R:ℂ)+z)^2/4)
lemma gaussianFlow_analytic (R : ℝ) (z : ℂ) : AnalyticAt ℂ (gaussianFlow R) z := by
  unfold gaussianFlow
  fun_prop

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open CenteredMomentCorrelation
variable {R : Type*} [CommRing R]

def bezoutPairEquiv (n₁ n₂ a b : R) (hab : a*n₁+b*n₂=1) : R×R≃R×R where
  toFun p := (b*p.2+n₁*p.1,-a*p.2+n₂*p.1)
  invFun p := (a*p.1+b*p.2,n₂*p.1-n₁*p.2)
  left_inv p := by
    apply Prod.ext
    · dsimp only
      linear_combination p.1*hab
    · dsimp only
      linear_combination p.2*hab
  right_inv p := by
    apply Prod.ext
    · dsimp only
      linear_combination p.1*hab
    · dsimp only
      linear_combination p.2*hab

end SevenEighths.ProbeGramCommon
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical

def lowCentralShift (Z T ell0 : ℝ) : ℝ := Real.logb Z T-1-ell0

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeDirichlet
open HeckeFamily

variable {q : ℕ}

def modulus (q : ℕ) : Ideal O := Ideal.span {(q : O)}

variable [NeZero q]

end SevenEighths.HeckeDirichlet

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators
namespace SevenEighths.Parameters

structure HighData (Δ : ℝ) where
  t : ℝ
  N : ℕ
  ell : Fin N→ℝ
  rmin : ℝ
  ε : ℝ
  e : ℝ
  κ : ℝ
  cost : ℝ
  eps : ℝ
  sigma : ℝ
  t_pos : 0<t
  t_delta : t<Δ/4
  t_small : t≤1/100000000
  slots_pos : 0<N
  slots_injective : Function.Injective ell
  slots_sum : (∑j,ell j)=1/6
  slots_bounds : ∀j,0<ell j ∧ (7/8)*rmin≤ell j ∧ ell j≤(1/200)*t
  rmin_pos : 0< rmin
  epsilon_pos : 0<ε
  epsilon_small : ε≤1/1000
  epsilon_gap : ε< rmin*t
  e_pos : 0<e
  e_small : e<1/1000
  kappa_pos : 0<κ
  kappa_small : κ≤1
  cost_pos : 0<cost
  eps_pos : 0<eps
  eps_small : eps≤1
  sigma_pos : 0<sigma
  detector_budget : 288*e+8*κ+2*cost≤ε/2
  phase_budget : 8*e*t+κ≤ε
  count_budget : 159*ε+t+t+7*t≤1/32
  central_budget : (13/16)*(159*ε+t+t+7*t)+2*t+(3/2)*(2*t)+
    (26*e+(N+8)*eps+t+t/6)+(t+t+t)+t≤49/440640
  geometric_budget : sigma+8*e+t/8≤63/800
  principal_budget : sigma+t/8≤17/48000
  window_budget : sigma+e≤(7/8)*((7/8)*rmin)
  floor_budget : 2*t+26*e+(N+8)*eps+t+t/6+t/8+sigma≤7/1200
  high_saving : sigma+t/8+t/8≤t
  height_choice : ∀J : ℝ,0≤J → ∃τ : ℝ,0<τ ∧ τ<(1/200)/2 ∧
    4*τ<(1/200)*cost ∧ τ<t ∧ 2*τ*(1+J)≤t ∧ τ*(2+4*eps)<t

end SevenEighths.Parameters

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentOriginalReflectionErrorMass
open HeckeFamily
local notation "O" => HeckeFamily.O

def errorConstant {α : Type*} (F : Finset α) (bshort Bshort : ℝ) (b B : α→ℝ) : ℝ :=
  (1+(128*max 1 bshort*Bshort)^2)*∏j∈F,max 1 ((128*max 1 (b j)*B j)^2)

end SevenEighths.CenteredMomentOriginalReflectionErrorMass

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped Classical BigOperators Topology
namespace SevenEighths.ProbeDetectorInverseFields
open HeckeFamily HeckeInverseAmplification InverseMoment
open HeckeDetectorRawFiber
open ProbeHighRowFamily Filter
local notation "O"=>HeckeFamily.O
variable (M:Ideal O)[NeZero M]
local instance:Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)

end SevenEighths.ProbeDetectorInverseFields

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ)

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ)

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentFiniteProfileExceptional
open HeckeFamily

def sourceControl (S : Finset (ℕ×ℕ)) (W : 𝓢(ℝ,ℂ)) : ℝ :=
  S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W

def normalizedProfile (S : Finset (ℕ×ℕ)) (W : 𝓢(ℝ,ℂ)) : 𝓢(ℝ,ℂ) :=
  (sourceControl S W)⁻¹ • W

end SevenEighths.CenteredMomentFiniteProfileExceptional

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentCommonMaskEnergy
open HeckeFamily
local notation "O" => HeckeFamily.O

def heightCoefficient (β : Ideal O→ℂ) (t : ℝ) (I : Ideal O) : ℂ :=
  β I*(I.absNorm:ℂ)^(Complex.I*t)

end SevenEighths.CenteredMomentCommonMaskEnergy

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily
open UniqueFactorizationMonoid
local notation "O" => HeckeFamily.O

def internalQ (Q : Ideal O) (η₀ : Character) : Ideal O := Q⊓η₀.modulus

variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O⧸M)ˣ)

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical ContDiff
open Set
namespace SevenEighths.CenteredMomentPrimeGlobal
open HeckeFamily

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ)

end SevenEighths.CenteredMomentPrimeGlobal

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Set
namespace SevenEighths.CenteredMomentPrimeHeight
open HeckeFamily
local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ)

end SevenEighths.CenteredMomentPrimeHeight
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff Topology
open Filter

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ)

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff Topology
open Filter

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ)

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Filter
namespace SevenEighths.CenteredMomentRayMaskedFloor
open HeckeFamily CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonMaskEnergy
local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ)

end SevenEighths.CenteredMomentRayMaskedFloor

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace SevenEighths.CenteredMomentRayMaskedFloor
open HeckeFamily
open CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonMaskEnergy
local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ)

end SevenEighths.CenteredMomentRayMaskedFloor

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace SevenEighths.CenteredMomentRayMaskedFloor
open HeckeFamily
open CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonMaskEnergy
local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ)

end SevenEighths.CenteredMomentRayMaskedFloor

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace SevenEighths.CenteredMomentRayMaskedFloor
open HeckeFamily
open CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonMaskEnergy
local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ)

end SevenEighths.CenteredMomentRayMaskedFloor

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace SevenEighths.CenteredMomentRayMaskedFloor
open HeckeFamily
open CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonMaskEnergy
local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ)

end SevenEighths.CenteredMomentRayMaskedFloor

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace SevenEighths.CenteredMomentRayMaskedFloor
open HeckeFamily
open CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource
local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ)

end SevenEighths.CenteredMomentRayMaskedFloor

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyActiveChildRestoration
open HeckeFamily
open CenteredMomentCommonMaskEnergy
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α]
local instance {β:Type*}:DecidableEq β:=Classical.decEq _

end SevenEighths.CenteredMomentEnergyActiveChildRestoration

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.CenteredMomentLiveCapacity

 def excess {ι:Type*} (J:Finset ι) (w:ι→ℝ) (n₁ n₂ M κ:ℝ) : ℝ :=
  max (n₁+n₂+6*κ*(∑i∈J,w i)-M) 0

end SevenEighths.CenteredMomentLiveCapacity

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace SevenEighths.CenteredMomentEnergyCapacityRemoval
open HeckeFamily
open CenteredMomentNaturalFixedRaySource
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ)

end SevenEighths.CenteredMomentEnergyCapacityRemoval

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyPaidBands
open HeckeFamily
open CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource
local notation "O" => HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)

end SevenEighths.CenteredMomentEnergyPaidBands

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyPaidRemoval
open HeckeFamily
open CenteredMomentEnergyPaidBands CenteredMomentEnergyCapacityRemoval
open CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource
local notation "O" => HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)

end SevenEighths.CenteredMomentEnergyPaidRemoval

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyAllocatedPaid
open HeckeFamily
open CenteredMomentEnergyPaidRemoval
open CenteredMomentFiniteProfileExceptional CenteredMomentNaturalFixedRaySource
local notation "O" => HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)

end SevenEighths.CenteredMomentEnergyAllocatedPaid

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentCommonSectorWindow
open HeckeFamily CompletedGauss
local notation "O" => HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
variable {ι:Type*}[Fintype ι][DecidableEq ι]

end SevenEighths.CenteredMomentCommonSectorWindow

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentSecondExceptionalPairDictionary
open HeckeFamily CompletedGauss UniqueFactorizationMonoid
open CenteredMomentCommonSectorWindow
local notation "O" => HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
variable {ι:Type*}[Fintype ι][DecidableEq ι]

end SevenEighths.CenteredMomentSecondExceptionalPairDictionary

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.CenteredMomentSecondDivisorSupport
open HeckeFamily CompletedGauss
local notation "O"=>HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _

end SevenEighths.CenteredMomentSecondDivisorSupport

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyAllocatedHomogeneous
open HeckeFamily
open CenteredMomentEnergyAllocatedPaid
open CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]

variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)

end SevenEighths.CenteredMomentEnergyAllocatedHomogeneous

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace SevenEighths.CenteredMomentSourceInputFirstSectorTail
open HeckeFamily
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

end SevenEighths.CenteredMomentSourceInputFirstSectorTail

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace SevenEighths.CenteredMomentSourceInputFirstSectorTail
open HeckeFamily
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

end SevenEighths.CenteredMomentSourceInputFirstSectorTail

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentSourceInputZeroUniform
open HeckeFamily
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

end SevenEighths.CenteredMomentSourceInputZeroUniform

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace SevenEighths.CenteredMomentSourceInputFirstRemainder
open HeckeFamily
open CenteredMomentSourceInputZeroUniform CenteredMomentSourceInputFirstSectorTail
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

end SevenEighths.CenteredMomentSourceInputFirstRemainder

end

end OAI
end

section

namespace OAI

noncomputable section

namespace SevenEighths.CenteredMomentFirstSecondLossParameters

def depth (Mcap σ:ℝ):ℕ:=⌈2*Mcap/σ⌉₊+1

end SevenEighths.CenteredMomentFirstSecondLossParameters

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalChildBound
open CenteredMomentEnergyAllocatedHomogeneous
open HeckeFamily
open CenteredMomentEnergyAllocatedPaid
open CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]

variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)

end SevenEighths.CenteredMomentEnergyCanonicalChildBound

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalPaidSource
open HeckeFamily
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]

open CenteredMomentEnergyAllocatedHomogeneous
open HeckeFamily
open CenteredMomentEnergyAllocatedPaid
open CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource

open CenteredMomentEnergyCanonicalChildBound
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)

end SevenEighths.CenteredMomentEnergyCanonicalPaidSource

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalCommonPaid
open HeckeFamily
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]

open CenteredMomentEnergyCanonicalPaidSource
open CenteredMomentEnergyAllocatedHomogeneous
open HeckeFamily
open CenteredMomentEnergyAllocatedPaid
open CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource

open CenteredMomentEnergyCanonicalChildBound
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)

end SevenEighths.CenteredMomentEnergyCanonicalCommonPaid

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalReferencePaid
open HeckeFamily
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]

open CenteredMomentEnergyCanonicalPaidSource CenteredMomentEnergyCanonicalCommonPaid
open CenteredMomentEnergyAllocatedHomogeneous
open HeckeFamily
open CenteredMomentEnergyAllocatedPaid
open CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource

open CenteredMomentEnergyCanonicalChildBound
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)

end SevenEighths.CenteredMomentEnergyCanonicalReferencePaid

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalUniformReference
open HeckeFamily
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]

open CenteredMomentEnergyCanonicalPaidSource CenteredMomentEnergyCanonicalCommonPaid
open CenteredMomentEnergyCanonicalReferencePaid
open CenteredMomentEnergyAllocatedHomogeneous
open HeckeFamily
open CenteredMomentEnergyAllocatedPaid
open CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource

open CenteredMomentEnergyCanonicalChildBound
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)

end SevenEighths.CenteredMomentEnergyCanonicalUniformReference

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalMainPaid
open HeckeFamily
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]

open CenteredMomentEnergyCanonicalPaidSource CenteredMomentEnergyCanonicalCommonPaid
open CenteredMomentEnergyCanonicalReferencePaid
open CenteredMomentEnergyAllocatedHomogeneous
open HeckeFamily
open CenteredMomentEnergyAllocatedPaid
open CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource

open CenteredMomentEnergyCanonicalChildBound
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)

open CenteredMomentEnergyCanonicalUniformReference
open CompletedGauss

end SevenEighths.CenteredMomentEnergyCanonicalMainPaid

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalNestedReference
open HeckeFamily
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]

open CenteredMomentEnergyCanonicalPaidSource CenteredMomentEnergyCanonicalCommonPaid
open CenteredMomentEnergyCanonicalReferencePaid
open CenteredMomentEnergyAllocatedHomogeneous
open HeckeFamily
open CenteredMomentEnergyAllocatedPaid
open CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource

open CenteredMomentEnergyCanonicalChildBound
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)

end SevenEighths.CenteredMomentEnergyCanonicalNestedReference

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalErrorUniform
open HeckeFamily
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]

open CenteredMomentEnergyCanonicalPaidSource CenteredMomentEnergyCanonicalCommonPaid
open CenteredMomentEnergyCanonicalReferencePaid
open CenteredMomentEnergyAllocatedHomogeneous
open HeckeFamily
open CenteredMomentEnergyAllocatedPaid
open CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource

open CenteredMomentEnergyCanonicalChildBound
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)

open CenteredMomentEnergyCanonicalUniformReference
open CompletedGauss

open CenteredMomentEnergyCanonicalMainPaid CenteredMomentEnergyCanonicalNestedReference
open CenteredMomentEnergyActiveChildRestoration

end SevenEighths.CenteredMomentEnergyCanonicalErrorUniform

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentSecondFrozenLiveSource
open HeckeFamily CompletedGauss
local notation "O" => HeckeFamily.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

end SevenEighths.CenteredMomentSecondFrozenLiveSource

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory

namespace SevenEighths.CenteredMomentFiniteProfileExceptionalFixedQ
open HeckeFamily CompletedGauss UniqueFactorizationMonoid
open CenteredMomentCommonSectorWindow
open CenteredMomentFiniteProfileExceptional
open CenteredMomentSecondDivisorSupport
local notation "O" => HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

end SevenEighths.CenteredMomentFiniteProfileExceptionalFixedQ

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory

namespace SevenEighths.CenteredMomentFiniteProfileExceptionalFixedQ
open HeckeFamily CompletedGauss UniqueFactorizationMonoid
open CenteredMomentCommonSectorWindow
open CenteredMomentFiniteProfileExceptional
open CenteredMomentSecondDivisorSupport
local notation "O" => HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

end SevenEighths.CenteredMomentFiniteProfileExceptionalFixedQ

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory

namespace SevenEighths.CenteredMomentFiniteProfileExceptionalFixedQ
open HeckeFamily CompletedGauss UniqueFactorizationMonoid
open CenteredMomentCommonSectorWindow
open CenteredMomentFiniteProfileExceptional
open CenteredMomentSecondDivisorSupport
local notation "O" => HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

end SevenEighths.CenteredMomentFiniteProfileExceptionalFixedQ

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory

namespace SevenEighths.CenteredMomentFiniteProfileExceptionalFixedQ
open HeckeFamily CompletedGauss UniqueFactorizationMonoid
open CenteredMomentCommonSectorWindow
open CenteredMomentFiniteProfileExceptional
open CenteredMomentSecondDivisorSupport
local notation "O" => HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

end SevenEighths.CenteredMomentFiniteProfileExceptionalFixedQ

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory

namespace SevenEighths.CenteredMomentFiniteProfileExceptionalFixedQ
open HeckeFamily CompletedGauss UniqueFactorizationMonoid
open CenteredMomentCommonSectorWindow
open CenteredMomentFiniteProfileExceptional
open CenteredMomentSecondDivisorSupport
local notation "O" => HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

end SevenEighths.CenteredMomentFiniteProfileExceptionalFixedQ

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory

namespace SevenEighths.CenteredMomentSecondExceptionalFixedQChosenBlock
open HeckeFamily CompletedGauss UniqueFactorizationMonoid
open CenteredMomentCommonSectorWindow
open CenteredMomentFiniteProfileExceptional
open CenteredMomentSecondDivisorSupport
local notation "O" => HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

end SevenEighths.CenteredMomentSecondExceptionalFixedQChosenBlock

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory

namespace SevenEighths.CenteredMomentSecondExceptionalFixedQSource
open HeckeFamily CompletedGauss UniqueFactorizationMonoid
open CenteredMomentCommonSectorWindow
open CenteredMomentFiniteProfileExceptional
open CenteredMomentSecondDivisorSupport
local notation "O" => HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

open CenteredMomentSecondExceptionalFixedQChosenBlock

end SevenEighths.CenteredMomentSecondExceptionalFixedQSource

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory

namespace SevenEighths.CenteredMomentSecondExceptionalUniformSource
open HeckeFamily CompletedGauss UniqueFactorizationMonoid
open CenteredMomentCommonSectorWindow
open CenteredMomentFiniteProfileExceptional
open CenteredMomentSecondDivisorSupport
local notation "O" => HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

open CenteredMomentSecondExceptionalFixedQChosenBlock

end SevenEighths.CenteredMomentSecondExceptionalUniformSource

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentSecondSourceDiagonal
open HeckeFamily
open CenteredMomentFiniteProfileExceptional
local notation "O"=>HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _

end SevenEighths.CenteredMomentSecondSourceDiagonal

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory

namespace SevenEighths.CenteredMomentSecondSourceRemainder
open HeckeFamily CompletedGauss UniqueFactorizationMonoid
open CenteredMomentCommonSectorWindow
open CenteredMomentFiniteProfileExceptional
open CenteredMomentSecondDivisorSupport
local notation "O" => HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

open CenteredMomentSecondExceptionalFixedQChosenBlock

end SevenEighths.CenteredMomentSecondSourceRemainder

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentSecondFrozenLiveDescent
open HeckeFamily CompletedGauss
local notation "O" => HeckeFamily.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

open CenteredMomentFiniteProfileExceptional

end SevenEighths.CenteredMomentSecondFrozenLiveDescent

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentSecondFrozenUniformSubset
open HeckeFamily CompletedGauss
local notation "O" => HeckeFamily.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

open CenteredMomentFiniteProfileExceptional
open MeasureTheory UniqueFactorizationMonoid

end SevenEighths.CenteredMomentSecondFrozenUniformSubset

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentSecondFrozenSeededPowerDescent
open HeckeFamily CompletedGauss
local notation "O" => HeckeFamily.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

open CenteredMomentFiniteProfileExceptional
open MeasureTheory UniqueFactorizationMonoid

end SevenEighths.CenteredMomentSecondFrozenSeededPowerDescent

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentSecondFrozenReferenceSeededPowerDescent
open HeckeFamily CompletedGauss
local notation "O" => HeckeFamily.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

open CenteredMomentFiniteProfileExceptional
open MeasureTheory UniqueFactorizationMonoid

end SevenEighths.CenteredMomentSecondFrozenReferenceSeededPowerDescent

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentFirstSeededGaussianPower
open HeckeFamily CompletedGauss
local notation "O" => HeckeFamily.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

open CenteredMomentFiniteProfileExceptional
open MeasureTheory UniqueFactorizationMonoid

end SevenEighths.CenteredMomentFirstSeededGaussianPower

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentFirstNestedSeededGaussianPower
open HeckeFamily CompletedGauss
local notation "O" => HeckeFamily.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

open CenteredMomentFiniteProfileExceptional
open MeasureTheory UniqueFactorizationMonoid

open CenteredMomentFirstSeededGaussianPower

abbrev NestedIndex (α:Type*) := ΣT:Finset α,Finset T

def emptyIndex : NestedIndex ι := ⟨∅,∅⟩

end SevenEighths.CenteredMomentFirstNestedSeededGaussianPower

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentSecondInputCapacitySource
open HeckeFamily CompletedGauss
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι]
local instance {κ:Type*}:DecidableEq κ:=Classical.decEq _

def lowerFactor (N:ℕ)(slotLower plainLower:ℝ):ℝ:=
  (min 1 slotLower)^N*plainLower^2

end SevenEighths.CenteredMomentSecondInputCapacitySource

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalErrorGaussian
open HeckeFamily
local notation "O"=>HeckeFamily.O
local instance {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _
variable {α:Type*}[Fintype α][DecidableEq α]

open CenteredMomentEnergyCanonicalPaidSource CenteredMomentEnergyCanonicalCommonPaid
open CenteredMomentEnergyCanonicalReferencePaid
open CenteredMomentEnergyAllocatedHomogeneous
open HeckeFamily
open CenteredMomentEnergyAllocatedPaid
open CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource

open CenteredMomentEnergyCanonicalChildBound
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)

open CenteredMomentEnergyCanonicalUniformReference
open CompletedGauss
open Filter
open CenteredMomentFirstNestedSeededGaussianPower

end SevenEighths.CenteredMomentEnergyCanonicalErrorGaussian

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalErrorAdmitted
open HeckeFamily
local notation "O"=>HeckeFamily.O
local instance {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _
variable {α:Type*}[Fintype α][DecidableEq α]

open CenteredMomentEnergyCanonicalPaidSource CenteredMomentEnergyCanonicalCommonPaid
open CenteredMomentEnergyCanonicalReferencePaid
open CenteredMomentEnergyAllocatedHomogeneous
open HeckeFamily
open CenteredMomentEnergyAllocatedPaid
open CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource

open CenteredMomentEnergyCanonicalChildBound
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)

open CenteredMomentEnergyCanonicalUniformReference
open CompletedGauss
open Filter
open CenteredMomentFirstNestedSeededGaussianPower

end SevenEighths.CenteredMomentEnergyCanonicalErrorAdmitted

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstCommonReferencePower
open HeckeFamily
local notation "O"=>HeckeFamily.O

def normalizedPower (b V C q Z allowance ε E:ℝ)(N:ℕ)(α:ℝ):ℝ:=
  C^ε*(b^N)^α*E/q*(V/C)^(α-1)*Z^(-allowance)

end SevenEighths.CenteredMomentFirstCommonReferencePower

end

end OAI
end

section

namespace OAI

noncomputable section

namespace SevenEighths.CenteredMomentSuccessorPaidParameters
open CenteredMomentFirstSecondLossParameters

def edge (epsChild epsRemove delta epsilon delta1 delta2 theta kappa mesh : ℝ) : ℝ :=
  epsChild+epsRemove+2*delta+epsilon+delta2+delta1/6+kappa*mesh+7*theta/3

def exceptional (sigma deltafr epsilon delta B theta : ℝ) : ℝ :=
  3*sigma+5*deltafr/6+2*epsilon+2*delta+2*(5*B+1)*theta

def diagonal (sigma delta reserve epsilon A : ℝ) : ℝ :=
  2*sigma+delta+reserve+epsilon*A

end SevenEighths.CenteredMomentSuccessorPaidParameters

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalErrorPower
open HeckeFamily
local notation "O"=>HeckeFamily.O
local instance {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _
variable {α:Type*}[Fintype α][DecidableEq α]

open CenteredMomentEnergyCanonicalPaidSource CenteredMomentEnergyCanonicalCommonPaid
open CenteredMomentEnergyCanonicalReferencePaid
open CenteredMomentEnergyAllocatedHomogeneous
open HeckeFamily
open CenteredMomentEnergyAllocatedPaid
open CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource

open CenteredMomentEnergyCanonicalChildBound
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)

open CenteredMomentEnergyCanonicalUniformReference
open CompletedGauss
open Filter
open CenteredMomentFirstNestedSeededGaussianPower

end SevenEighths.CenteredMomentEnergyCanonicalErrorPower

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyFirstGaussianProfileWeights
open HeckeFamily CenteredMomentFiniteProfileExceptional
local notation "O"=>HeckeFamily.O

def losses (epsilon delta theta B:ℝ):Fin 4→ℝ:=
  ![2*delta+epsilon,2*epsilon+2*delta+2*(5*B+1)*theta,0,0]

end SevenEighths.CenteredMomentEnergyFirstGaussianProfileWeights

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalErrorHomogeneous
open HeckeFamily
local notation "O"=>HeckeFamily.O
local instance {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _
variable {α:Type*}[Fintype α][DecidableEq α]

open CenteredMomentEnergyCanonicalPaidSource CenteredMomentEnergyCanonicalCommonPaid
open CenteredMomentEnergyCanonicalReferencePaid
open CenteredMomentEnergyAllocatedHomogeneous
open HeckeFamily
open CenteredMomentEnergyAllocatedPaid
open CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource

open CenteredMomentEnergyCanonicalChildBound
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)

open CenteredMomentEnergyCanonicalUniformReference
open CompletedGauss
open Filter
open CenteredMomentFirstNestedSeededGaussianPower

end SevenEighths.CenteredMomentEnergyCanonicalErrorHomogeneous

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalErrorSubsets
open HeckeFamily
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]

open CenteredMomentEnergyCanonicalPaidSource CenteredMomentEnergyCanonicalCommonPaid
open CenteredMomentEnergyCanonicalReferencePaid
open CenteredMomentEnergyAllocatedHomogeneous
open HeckeFamily
open CenteredMomentEnergyAllocatedPaid
open CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource

open CenteredMomentEnergyCanonicalChildBound
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)

open CenteredMomentEnergyCanonicalUniformReference
open CompletedGauss
open Filter
open CenteredMomentFirstNestedSeededGaussianPower

end SevenEighths.CenteredMomentEnergyCanonicalErrorSubsets

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalMainUniform
open HeckeFamily
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]

open CenteredMomentEnergyCanonicalPaidSource CenteredMomentEnergyCanonicalCommonPaid
open CenteredMomentEnergyCanonicalReferencePaid
open CenteredMomentEnergyAllocatedHomogeneous
open HeckeFamily
open CenteredMomentEnergyAllocatedPaid
open CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource

open CenteredMomentEnergyCanonicalChildBound
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)

open CenteredMomentEnergyCanonicalUniformReference
open CompletedGauss

end SevenEighths.CenteredMomentEnergyCanonicalMainUniform

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalMainGaussian
open HeckeFamily
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
local instance {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

open CenteredMomentEnergyCanonicalPaidSource CenteredMomentEnergyCanonicalCommonPaid
open CenteredMomentEnergyCanonicalReferencePaid
open CenteredMomentEnergyAllocatedHomogeneous
open HeckeFamily
open CenteredMomentEnergyAllocatedPaid
open CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource

open CenteredMomentEnergyCanonicalChildBound
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)

open CenteredMomentEnergyCanonicalUniformReference
open CompletedGauss
open Filter
open CenteredMomentFirstSeededGaussianPower

end SevenEighths.CenteredMomentEnergyCanonicalMainGaussian

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalMainSeparated
open HeckeFamily
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
local instance {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

open CenteredMomentEnergyCanonicalPaidSource CenteredMomentEnergyCanonicalCommonPaid
open CenteredMomentEnergyCanonicalReferencePaid
open CenteredMomentEnergyAllocatedHomogeneous
open HeckeFamily
open CenteredMomentEnergyAllocatedPaid
open CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource

open CenteredMomentEnergyCanonicalChildBound
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)

open CenteredMomentEnergyCanonicalUniformReference
open CompletedGauss
open Filter
open CenteredMomentFirstSeededGaussianPower

end SevenEighths.CenteredMomentEnergyCanonicalMainSeparated

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalMainSeparatedPower
open HeckeFamily
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
local instance {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

open CenteredMomentEnergyCanonicalPaidSource CenteredMomentEnergyCanonicalCommonPaid
open CenteredMomentEnergyCanonicalReferencePaid
open CenteredMomentEnergyAllocatedHomogeneous
open HeckeFamily
open CenteredMomentEnergyAllocatedPaid
open CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource

open CenteredMomentEnergyCanonicalChildBound
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)

open CenteredMomentEnergyCanonicalUniformReference
open CompletedGauss
open Filter
open CenteredMomentFirstSeededGaussianPower

end SevenEighths.CenteredMomentEnergyCanonicalMainSeparatedPower

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalMainHomogeneous
open HeckeFamily
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
local instance {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

open CenteredMomentEnergyCanonicalPaidSource CenteredMomentEnergyCanonicalCommonPaid
open CenteredMomentEnergyCanonicalReferencePaid
open CenteredMomentEnergyAllocatedHomogeneous
open HeckeFamily
open CenteredMomentEnergyAllocatedPaid
open CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource

open CenteredMomentEnergyCanonicalChildBound
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)

open CenteredMomentEnergyCanonicalUniformReference
open CompletedGauss
open Filter
open CenteredMomentFirstSeededGaussianPower

end SevenEighths.CenteredMomentEnergyCanonicalMainHomogeneous

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalMainSubsets
open HeckeFamily
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
open CenteredMomentEnergyCanonicalPaidSource CenteredMomentEnergyCanonicalCommonPaid
open CenteredMomentEnergyCanonicalReferencePaid
open CenteredMomentEnergyAllocatedHomogeneous
open HeckeFamily
open CenteredMomentEnergyAllocatedPaid
open CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource

open CenteredMomentEnergyCanonicalChildBound
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)

open CenteredMomentEnergyCanonicalUniformReference
open CompletedGauss
open Filter
open CenteredMomentFirstSeededGaussianPower

end SevenEighths.CenteredMomentEnergyCanonicalMainSubsets

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalAmplifiedUniform
open HeckeFamily
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
open CenteredMomentEnergyCanonicalPaidSource CenteredMomentEnergyCanonicalCommonPaid
open CenteredMomentEnergyCanonicalReferencePaid
open CenteredMomentEnergyAllocatedHomogeneous
open HeckeFamily
open CenteredMomentEnergyAllocatedPaid
open CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource

open CenteredMomentEnergyCanonicalChildBound
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)

open CenteredMomentEnergyCanonicalUniformReference
open CompletedGauss
open Filter
open CenteredMomentFirstSeededGaussianPower

end SevenEighths.CenteredMomentEnergyCanonicalAmplifiedUniform

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentFirstSecondInputGates
open HeckeFamily
local notation "O"=>HeckeFamily.O

def commonExponent (A D P C q ε ξ:ℝ):ℝ:=
  max (A+ε) (max (2*A+D+ε+ξ/2) (max (P+C) q))

end SevenEighths.CenteredMomentFirstSecondInputGates

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalAnnularPower
open HeckeFamily
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
open CenteredMomentEnergyCanonicalPaidSource CenteredMomentEnergyCanonicalCommonPaid
open CenteredMomentEnergyCanonicalReferencePaid
open CenteredMomentEnergyAllocatedHomogeneous
open HeckeFamily
open CenteredMomentEnergyAllocatedPaid
open CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource

open CenteredMomentEnergyCanonicalChildBound
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)

open CenteredMomentEnergyCanonicalUniformReference
open CompletedGauss
open Filter
open CenteredMomentFirstSeededGaussianPower CenteredMomentFirstSecondInputGates

open CenteredMomentEnergyCanonicalAmplifiedUniform

end SevenEighths.CenteredMomentEnergyCanonicalAnnularPower

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalLowColumn
open HeckeFamily
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
open CenteredMomentEnergyCanonicalPaidSource CenteredMomentEnergyCanonicalCommonPaid
open CenteredMomentEnergyCanonicalReferencePaid
open CenteredMomentEnergyAllocatedHomogeneous
open HeckeFamily
open CenteredMomentEnergyAllocatedPaid
open CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource

open CenteredMomentEnergyCanonicalChildBound
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)

open CenteredMomentEnergyCanonicalUniformReference
open CompletedGauss
open Filter
open CenteredMomentFirstSeededGaussianPower CenteredMomentFirstSecondInputGates

open CenteredMomentEnergyCanonicalAmplifiedUniform

open CenteredMomentEnergyCanonicalAnnularPower
open CenteredMomentFirstCommonReferencePower

end SevenEighths.CenteredMomentEnergyCanonicalLowColumn

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalHighColumn
open HeckeFamily
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
open CenteredMomentEnergyCanonicalPaidSource CenteredMomentEnergyCanonicalCommonPaid
open CenteredMomentEnergyCanonicalReferencePaid
open CenteredMomentEnergyAllocatedHomogeneous
open HeckeFamily
open CenteredMomentEnergyAllocatedPaid
open CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource

open CenteredMomentEnergyCanonicalChildBound
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)

open CenteredMomentEnergyCanonicalUniformReference
open CompletedGauss
open Filter
open CenteredMomentFirstSeededGaussianPower CenteredMomentFirstSecondInputGates

open CenteredMomentEnergyCanonicalAmplifiedUniform

open CenteredMomentEnergyCanonicalAnnularPower
open CenteredMomentFirstCommonReferencePower

open CenteredMomentEnergyCanonicalLowColumn

end SevenEighths.CenteredMomentEnergyCanonicalHighColumn

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyFirstTwoSeedAdmission
open HeckeFamily
open CenteredMomentFirstSecondInputGates
open CenteredMomentSecondInputCapacitySource
open CompletedGauss
local notation "O" => HeckeFamily.O
local instance {ι : Type*} : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

end SevenEighths.CenteredMomentEnergyFirstTwoSeedAdmission

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalHighSource
open HeckeFamily
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
local instance {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

open CenteredMomentEnergyCanonicalPaidSource CenteredMomentEnergyCanonicalCommonPaid
open CenteredMomentEnergyCanonicalReferencePaid
open CenteredMomentEnergyAllocatedHomogeneous
open HeckeFamily
open CenteredMomentEnergyAllocatedPaid
open CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource

open CenteredMomentEnergyCanonicalChildBound
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)

open CenteredMomentEnergyCanonicalUniformReference
open CompletedGauss
open Filter
open CenteredMomentFirstSeededGaussianPower CenteredMomentFirstSecondInputGates

open CenteredMomentEnergyCanonicalAmplifiedUniform

open CenteredMomentEnergyCanonicalAnnularPower
open CenteredMomentFirstCommonReferencePower
open CenteredMomentEnergyCanonicalLowColumn CenteredMomentEnergyCanonicalHighColumn

end SevenEighths.CenteredMomentEnergyCanonicalHighSource

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyFirstRightAdmission
open HeckeFamily
open CenteredMomentFirstSecondInputGates
open CenteredMomentSecondInputCapacitySource
open CompletedGauss
local notation "O" => HeckeFamily.O
local instance {ι : Type*} : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

end SevenEighths.CenteredMomentEnergyFirstRightAdmission

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalRightSourceColumn
open HeckeFamily
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
local instance {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

open CenteredMomentEnergyCanonicalPaidSource CenteredMomentEnergyCanonicalCommonPaid
open CenteredMomentEnergyCanonicalReferencePaid
open CenteredMomentEnergyAllocatedHomogeneous
open HeckeFamily
open CenteredMomentEnergyAllocatedPaid
open CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource

open CenteredMomentEnergyCanonicalChildBound
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)

open CenteredMomentEnergyCanonicalUniformReference
open CompletedGauss
open Filter
open CenteredMomentFirstSeededGaussianPower CenteredMomentFirstSecondInputGates

open CenteredMomentEnergyCanonicalAmplifiedUniform

open CenteredMomentEnergyCanonicalAnnularPower
open CenteredMomentFirstCommonReferencePower
open CenteredMomentEnergyCanonicalLowColumn
open CenteredMomentEnergyFirstRightAdmission

end SevenEighths.CenteredMomentEnergyCanonicalRightSourceColumn

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalHighPhysical
open HeckeFamily
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
open CenteredMomentEnergyCanonicalPaidSource CenteredMomentEnergyCanonicalCommonPaid
open CenteredMomentEnergyCanonicalReferencePaid
open CenteredMomentEnergyAllocatedHomogeneous
open HeckeFamily
open CenteredMomentEnergyAllocatedPaid
open CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource

open CenteredMomentEnergyCanonicalChildBound
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)

open CenteredMomentEnergyCanonicalUniformReference
open CompletedGauss
open Filter
open CenteredMomentFirstSeededGaussianPower CenteredMomentFirstSecondInputGates

open CenteredMomentEnergyCanonicalAmplifiedUniform

open CenteredMomentEnergyCanonicalAnnularPower
open CenteredMomentFirstCommonReferencePower
open CenteredMomentEnergyCanonicalLowColumn

end SevenEighths.CenteredMomentEnergyCanonicalHighPhysical

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalLowSource
open HeckeFamily
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
local instance {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

open CenteredMomentEnergyCanonicalPaidSource CenteredMomentEnergyCanonicalCommonPaid
open CenteredMomentEnergyCanonicalReferencePaid
open CenteredMomentEnergyAllocatedHomogeneous
open HeckeFamily
open CenteredMomentEnergyAllocatedPaid
open CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource

open CenteredMomentEnergyCanonicalChildBound
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)

open CenteredMomentEnergyCanonicalUniformReference
open CompletedGauss
open Filter
open CenteredMomentFirstSeededGaussianPower CenteredMomentFirstSecondInputGates

open CenteredMomentEnergyCanonicalAmplifiedUniform

open CenteredMomentEnergyCanonicalAnnularPower
open CenteredMomentFirstCommonReferencePower
open CenteredMomentEnergyCanonicalLowColumn

end SevenEighths.CenteredMomentEnergyCanonicalLowSource

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalLowPhysical
open HeckeFamily
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
open CenteredMomentEnergyCanonicalPaidSource CenteredMomentEnergyCanonicalCommonPaid
open CenteredMomentEnergyCanonicalReferencePaid
open CenteredMomentEnergyAllocatedHomogeneous
open HeckeFamily
open CenteredMomentEnergyAllocatedPaid
open CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource

open CenteredMomentEnergyCanonicalChildBound
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)

open CenteredMomentEnergyCanonicalUniformReference
open CompletedGauss
open Filter
open CenteredMomentFirstSeededGaussianPower CenteredMomentFirstSecondInputGates

open CenteredMomentEnergyCanonicalAmplifiedUniform

open CenteredMomentEnergyCanonicalAnnularPower
open CenteredMomentFirstCommonReferencePower
open CenteredMomentEnergyCanonicalLowColumn

end SevenEighths.CenteredMomentEnergyCanonicalLowPhysical

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyWidthSchedule
open CenteredMomentSuccessorPaidParameters CenteredMomentFirstSecondLossParameters

def amplification (ε:ℝ):ℝ := min 1 (ε/16000)
def count (M ε:ℝ):ℕ := depth M (amplification ε)
def scale (M B ε:ℝ):ℝ := (count M ε:ℝ)+M+10*B+30
def reserve (M B ε:ℝ):ℝ :=
  min (amplification ε/100) (ε/(1000000*scale M B ε))
def mesh (M B κ ε:ℝ):ℝ := reserve M B ε/(κ+1)
def width (M B ε:ℝ)(k:ℕ):ℝ := reserve M B ε/16+(k:ℝ)*amplification ε/2
def loss (M B ε:ℝ)(k:ℕ):ℝ := reserve M B ε+64*(k:ℝ)*reserve M B ε

end SevenEighths.CenteredMomentEnergyWidthSchedule

end

end OAI
end

section

namespace OAI

noncomputable section

namespace SevenEighths.CenteredMomentEnergyStageReserveSchedule
open CenteredMomentEnergyWidthSchedule CenteredMomentSuccessorPaidParameters

def stageLoss (M B ε:ℝ)(k:ℕ):ℝ:=ε/1000+loss M B ε k

end SevenEighths.CenteredMomentEnergyStageReserveSchedule

end

end OAI
end

section

namespace OAI

noncomputable section

namespace SevenEighths.CenteredMomentEnergyCappedRequests
open CenteredMomentEnergyWidthSchedule

def requestLength (M B L:ℝ):ℝ:=max L (2*M+B+2)+1

end SevenEighths.CenteredMomentEnergyCappedRequests

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyFirstStageLossBudget
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyStageReserveSchedule
open CenteredMomentSuccessorPaidParameters
open CenteredMomentEnergyFirstGaussianProfileWeights

def sourcePaid (Bcap emask ell er delta reserveAmp thetaSource thetaClip κ mesh:ℝ):ℝ:=
  (Bcap+Bcap)*emask+ell+er+(delta+reserveAmp+thetaSource)/6+thetaClip/3+κ*mesh

end SevenEighths.CenteredMomentEnergyFirstStageLossBudget

end

end OAI
end

section

namespace OAI

noncomputable section

namespace SevenEighths.CenteredMomentEnergyStageMargins
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyStageReserveSchedule

def physicalLoss (M B ε:ℝ)(k:ℕ):ℝ:=stageLoss M B ε (k+1)-2*reserve M B ε
def reflectedLoss (M B ε:ℝ)(k:ℕ):ℝ:=physicalLoss M B ε k+reserve M B ε

end SevenEighths.CenteredMomentEnergyStageMargins

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter

namespace SevenEighths.CenteredMomentEnergyFirstSourceParameters
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyStageReserveSchedule
open CenteredMomentEnergyFirstStageLossBudget
open CenteredMomentEnergyFirstGaussianProfileWeights

def sourceEpsilon (M A B ε:ℝ):ℝ:=reserve M B ε/(4*((A+1)+A+1))
def maskEpsilon (M B ε:ℝ):ℝ:=reserve M B ε/(B+B+1)
def columnLoss (M B ε:ℝ)(k:ℕ):ℝ:=
  stageLoss M B ε (k+1)-2*reserve M B ε-reserve M B ε/4

end SevenEighths.CenteredMomentEnergyFirstSourceParameters

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyNaturalSourceAdmission
open HeckeFamily
open CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

def lowerProduct (N : ℕ) (aslot a : ℝ) : ℝ := (min 1 aslot)^N*a*a

end SevenEighths.CenteredMomentEnergyNaturalSourceAdmission

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyReferenceLowDirect
open HeckeFamily
open CenteredMomentNaturalFixedRaySource
open CenteredMomentFiniteProfileExceptional
open CenteredMomentCommonMaskEnergy
local notation "O"=>HeckeFamily.O

variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)

end SevenEighths.CenteredMomentEnergyReferenceLowDirect

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyReferenceLowMoments
open HeckeFamily
open CenteredMomentNaturalFixedRaySource
open CenteredMomentFiniteProfileExceptional
open CenteredMomentCommonMaskEnergy
local notation "O"=>HeckeFamily.O

variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)

end SevenEighths.CenteredMomentEnergyReferenceLowMoments

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyReferenceLowReflection
open HeckeFamily
open CenteredMomentEnergyReferenceLowMoments
open CenteredMomentNaturalFixedRaySource
open CenteredMomentFiniteProfileExceptional
open CenteredMomentCommonMaskEnergy
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)

end SevenEighths.CenteredMomentEnergyReferenceLowReflection

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyReferenceLowReflectionError
open HeckeFamily
open CenteredMomentEnergyReferenceLowMoments
open CenteredMomentNaturalFixedRaySource
open CenteredMomentFiniteProfileExceptional
open CenteredMomentCommonMaskEnergy
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)

open CenteredMomentEnergyReferenceLowReflection

end SevenEighths.CenteredMomentEnergyReferenceLowReflectionError

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyOriginalHighReflectionDeleted
open HeckeFamily
open CenteredMomentEnergyReferenceLowReflectionError
open CenteredMomentEnergyReferenceLowDirect
open CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonMaskEnergy
open CenteredMomentFiniteProfileExceptional
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)

end SevenEighths.CenteredMomentEnergyOriginalHighReflectionDeleted

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyOriginalHighReflectionOriginal
open HeckeFamily
open CenteredMomentEnergyReferenceLowReflectionError
open CenteredMomentEnergyReferenceLowDirect
open CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonMaskEnergy
open CenteredMomentFiniteProfileExceptional
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)

open CenteredMomentEnergyOriginalHighReflectionDeleted

end SevenEighths.CenteredMomentEnergyOriginalHighReflectionOriginal

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyOriginalHighReflectionBounded
open HeckeFamily
open CenteredMomentEnergyOriginalHighReflectionOriginal
open CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonMaskEnergy
open CenteredMomentFiniteProfileExceptional
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)

end SevenEighths.CenteredMomentEnergyOriginalHighReflectionBounded

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyOriginalHighReflectionPower
open HeckeFamily
open CenteredMomentEnergyOriginalHighReflectionOriginal
open CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonMaskEnergy
open CenteredMomentFiniteProfileExceptional
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)

end SevenEighths.CenteredMomentEnergyOriginalHighReflectionPower

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyOriginalHighReflectionSymmetric
open HeckeFamily
open CenteredMomentEnergyOriginalHighReflectionPower
open CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonMaskEnergy
open CenteredMomentFiniteProfileExceptional
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]

variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)

end SevenEighths.CenteredMomentEnergyOriginalHighReflectionSymmetric

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyOriginalHighReflectionSymmetricBounded
open HeckeFamily
open CenteredMomentEnergyOriginalHighReflectionBounded
open CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonMaskEnergy
open CenteredMomentFiniteProfileExceptional
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]

open CenteredMomentEnergyOriginalHighReflectionSymmetric

variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)

end SevenEighths.CenteredMomentEnergyOriginalHighReflectionSymmetricBounded

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyReferenceRobustDeletedEnergy
open HeckeFamily
open CenteredMomentEnergyReferenceLowReflectionError
open CenteredMomentEnergyReferenceLowDirect
open CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonMaskEnergy
open CenteredMomentFiniteProfileExceptional
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)

end SevenEighths.CenteredMomentEnergyReferenceRobustDeletedEnergy

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyReferenceRobustOriginal
open HeckeFamily
open CenteredMomentEnergyReferenceLowReflectionError
open CenteredMomentEnergyReferenceLowDirect
open CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonMaskEnergy
open CenteredMomentFiniteProfileExceptional
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)

open CenteredMomentEnergyReferenceRobustDeletedEnergy

end SevenEighths.CenteredMomentEnergyReferenceRobustOriginal

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyReferenceRobustPower
open HeckeFamily
open CenteredMomentEnergyReferenceRobustOriginal
open CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonMaskEnergy
open CenteredMomentFiniteProfileExceptional
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)

end SevenEighths.CenteredMomentEnergyReferenceRobustPower

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyReferenceLivePower
open HeckeFamily
open CenteredMomentEnergyReferenceRobustOriginal
open CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonMaskEnergy
open CenteredMomentFiniteProfileExceptional
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)

end SevenEighths.CenteredMomentEnergyReferenceLivePower

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyPositiveHighParameters
open HeckeFamily
open CenteredMomentEnergyReferenceLivePower
open CenteredMomentEnergyOriginalHighReflectionSymmetric
open CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)
variable (η₀:Character)
variable (W:ℝ→ ℂ)(hW:Continuous W)(aslot bslot lo hi:ℝ)(haslot:0<aslot)
variable (hWs:Function.support W⊆Set.Icc aslot bslot)
variable (w σ freq:α→ ℝ)(hσ:∀i,σ i∈Set.Icc lo hi)
variable {Z Bmask bΦ a b:ℝ}
  (ha:0<a)
variable (t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)

end SevenEighths.CenteredMomentEnergyPositiveHighParameters

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyPositiveBalancedAdmission
open HeckeFamily
open CenteredMomentEnergyReferenceLivePower
open CenteredMomentEnergyOriginalHighReflectionSymmetric
open CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)
variable (η₀:Character)
variable (W:ℝ→ ℂ)(hW:Continuous W)(aslot bslot lo hi:ℝ)(haslot:0<aslot)
variable (hWs:Function.support W⊆Set.Icc aslot bslot)
variable (w σ freq:α→ ℝ)(hσ:∀i,σ i∈Set.Icc lo hi)
variable {Z Bmask bΦ a b:ℝ}
  (ha:0<a)
variable (t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)

open CenteredMomentEnergyPositiveHighParameters

end SevenEighths.CenteredMomentEnergyPositiveBalancedAdmission

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyPositiveHighAssembly
open HeckeFamily
open CenteredMomentEnergyOriginalHighReflectionSymmetric
open CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)

end SevenEighths.CenteredMomentEnergyPositiveHighAssembly

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyReferenceRobustBounded
open HeckeFamily
open CenteredMomentEnergyReferenceRobustOriginal
open CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonMaskEnergy
open CenteredMomentFiniteProfileExceptional
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)

end SevenEighths.CenteredMomentEnergyReferenceRobustBounded

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyReferenceLiveBounded
open HeckeFamily
open CenteredMomentEnergyReferenceRobustOriginal
open CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonMaskEnergy
open CenteredMomentFiniteProfileExceptional
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)

end SevenEighths.CenteredMomentEnergyReferenceLiveBounded

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyPositiveHighSourceBounded
open HeckeFamily
open CenteredMomentEnergyReferenceLiveBounded
open CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)
variable (η₀:Character)
variable (W:ℝ→ ℂ)(hW:Continuous W)(aslot bslot lo hi:ℝ)(haslot:0<aslot)
variable (hWs:Function.support W⊆Set.Icc aslot bslot)
variable (w σ freq:α→ ℝ)(hσ:∀i,σ i∈Set.Icc lo hi)
variable {Z Bmask bΦ a b:ℝ}
  (ha:0<a)
variable (t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)

end SevenEighths.CenteredMomentEnergyPositiveHighSourceBounded

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyPositiveHighAssemblyBounded
open HeckeFamily
open CenteredMomentEnergyPositiveHighSourceBounded CenteredMomentEnergyOriginalHighReflectionSymmetricBounded
open CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)

end SevenEighths.CenteredMomentEnergyPositiveHighAssemblyBounded

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyPositiveHighBound
open HeckeFamily
open CenteredMomentEnergyPositiveHighSourceBounded CenteredMomentEnergyOriginalHighReflectionSymmetricBounded
open CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)

open CenteredMomentEnergyPositiveHighAssemblyBounded CenteredMomentEnergyPositiveHighParameters

end SevenEighths.CenteredMomentEnergyPositiveHighBound

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentDetectorPlainMomentParameters
open HeckeFamily HeckeDetectorRawFiber ProbeHighRowFamily
open CenteredMomentNaturalFixedRaySource
local notation "O" => HeckeFamily.O

variable {Δ:ℝ}

def delta (D:Parameters.HighData Δ):ℝ := D.t/4
def stageError (D:Parameters.HighData Δ):ℝ := D.t/4
def kappaPlain (_D:Parameters.HighData Δ):ℝ := 3/4+2*Δ

theorem fixed_parameters (D:Parameters.HighData Δ):
    0<delta D ∧ delta D≤1/4 ∧ 0<stageError D ∧
    delta D+stageError D≤D.t ∧ 3/4<kappaPlain D ∧ 0<kappaPlain D := by
  have hΔ:0<Δ:=by linarith [D.t_pos,D.t_delta]
  dsimp [delta,stageError,kappaPlain]
  constructor
  · exact div_pos D.t_pos (by norm_num)
  constructor
  · linarith [D.t_small]
  constructor
  · exact div_pos D.t_pos (by norm_num)
  constructor
  · linarith [D.t_pos]
  constructor <;> linarith

variable {M:Ideal O}[NeZero M]{H:Subgroup (O⧸M)ˣ}{Label:Type*}
variable {U a tstar T heightAllowance:ℝ}{i:ℕ}

end SevenEighths.CenteredMomentDetectorPlainMomentParameters

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentDetectorPlainRelativeClass
open HeckeFamily CenteredMomentNaturalFixedRaySource
local notation "O"=>HeckeFamily.O
variable (M:Ideal O)[NeZero M]
local instance:Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)

variable {ι:Type*}[Fintype ι][DecidableEq ι]

end SevenEighths.CenteredMomentDetectorPlainRelativeClass

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber
open HeckeDetectorRowCount HeckeDetectorAdaptiveCutoff

def adaptiveRowExponent (δ q Δ ε εm slotMesh ν : ℝ) : ℝ :=
  if δ≤5/6 then Endpoint.balancedRowCount δ (1/2-q/δ)+Δ/4+159*ε+εm+slotMesh+7*ν
  else 1-δ+78*ε+εm

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical

def sourceDyadExponent (Z : ℝ) (k : ℕ) : ℝ := Real.logb Z ((2:ℝ)^k)
def sourceDyadConductor (Z margin : ℝ) (k : ℕ) : ℝ := sourceDyadExponent Z k+2*margin

end SevenEighths.ProbeHighRowFamily

end

end OAI
end


