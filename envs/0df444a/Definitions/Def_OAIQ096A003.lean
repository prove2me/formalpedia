-- Prove2me | Definitions.Def_OAIQ096A003
-- name    : OAIQ096A003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T03:27:23.519833+00:00
-- url     : https://prove2.me/theorems/ee9e29d5-10e3-4b65-8703-57a19c4bbd78
-- title:
--   Definitions bundle OAIQ096A003 of the split of OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 360 declarations of OpenAI's Lean: 182 definitions, 1 inductive type or structure, 15 instances and 162 theorems. The definitions and types are `OAI.CubicFirstMoment.SemiprimeTailParameters`, `OAI.CubicFirstMoment.cubicThetaArithmeticModelEnergyMeasureSpace`, `OAI.CubicFirstMoment.cubicThetaArithmeticModelTorusMeasureSpace`, `OAI.CubicFirstMoment.cubicThetaArithmeticTorusMeasureSpace`, `OAI.CubicFirstMoment.cubicThetaAveragedHeat`, `OAI.CubicFirstMoment.cubicThetaCellFourierSeparationMeasureSpace`, `OAI.CubicFirstMoment.cubicThetaCircleDualDirection`, `OAI.CubicFirstMoment.cubicThetaCircleDualHeight`, `OAI.CubicFirstMoment.cubicThetaCircleLinear`, `OAI.CubicFirstMoment.cubicThetaCircleMultiplier`, `OAI.CubicFirstMoment.cubicThetaCircleOrder`, `OAI.CubicFirstMoment.cubicThetaCirclePhase`, `OAI.CubicFirstMoment.cubicThetaCirclePower`, `OAI.CubicFirstMoment.cubicThetaCircleSeries`, `OAI.CubicFirstMoment.cubicThetaCircleTaylor`, `OAI.CubicFirstMoment.cubicThetaComplexHeightHeat`, `OAI.CubicFirstMoment.cubicThetaComplexHeightIntegral`, `OAI.CubicFirstMoment.cubicThetaFullEisensteinFourierMeasureSpace`, `OAI.CubicFirstMoment.cubicThetaHeightMajorant`, `OAI.CubicFirstMoment.cubicThetaHorizontalCoefficientMeasureSpace`, `OAI.CubicFirstMoment.cubicThetaHorizontalEnergyMeasureSpace`, `OAI.CubicFirstMoment.cubicThetaInverseUnitIndex`, `OAI.CubicFirstMoment.cubicThetaInvertedScatteringFactor`, `OAI.CubicFirstMoment.cubicThetaInvertedTorusMeasureSpace`, `OAI.CubicFirstMoment.cubicThetaLinearHeat`, `OAI.CubicFirstMoment.cubicThetaMassEulerPrefactor`, `OAI.CubicFirstMoment.cubicThetaMassPushforward`, `OAI.CubicFirstMoment.cubicThetaNormalizedHeat`, `OAI.CubicFirstMoment.cubicThetaPositiveAveragedHeat`, `OAI.CubicFirstMoment.cubicThetaPositiveRadialWeightMass`, `OAI.CubicFirstMoment.cubicThetaPositiveZeroWindowMeasureSpace`, `OAI.CubicFirstMoment.cubicThetaPrimaryBoxBound`, `OAI.CubicFirstMoment.cubicThetaPrimitiveMellinTailMass`, `OAI.CubicFirstMoment.cubicThetaRadialEuler`, `OAI.CubicFirstMoment.cubicThetaRadialMellinIntegrand`, `OAI.CubicFirstMoment.cubicThetaRadialWeightMass`, `OAI.CubicFirstMoment.cubicThetaRadiusProfile`, `OAI.CubicFirstMoment.cubicThetaRamifiedBoxBound`, `OAI.CubicFirstMoment.cubicThetaRamifiedCubeFactor`, `OAI.CubicFirstMoment.cubicThetaRamifiedRatio` and 143 more.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `CubicGram_CubicOperator`, `CubicGram_GramDyad`, `CubicGram_QuantitativeRecurrence`, `CubicGram_SieveExponent`, `CubicGram_SieveImprovement`, `CubicMoment_Decomposition_PrimeProductPolynomialBounds`, `CubicMoment_Decomposition_StoppedDyadPartition`, `CubicMoment_Estimates_AnalyticDiskLogDerivative`, `CubicMoment_Estimates_CellGeometry`, `CubicMoment_Estimates_CubicBesselSymmetricSlope`, `CubicMoment_Estimates_CubicWhittakerBounds`, `CubicMoment_Estimates_DispersionCutoff`, `CubicMoment_Estimates_DyadicMellinTail`, `CubicMoment_Estimates_DyadicReconstruction`, `CubicMoment_Estimates_DyadicScaleBounds`, `CubicMoment_Estimates_EndpointKernel`, `CubicMoment_Estimates_FiniteMellinContour`, `CubicMoment_Estimates_FlatTripleCount`, `CubicMoment_Estimates_FullPrimeMellin`, `CubicMoment_Estimates_GaussianMellin`, `CubicMoment_Estimates_GramOperator`, `CubicMoment_Estimates_HeckeNormalizedDisk`, `CubicMoment_Estimates_HeckePrimeScales`, `CubicMoment_Estimates_HeckeSymmetry`, `CubicMoment_Estimates_HeightAveraging`, `CubicMoment_Estimates_HeightEndpointProfile`, `CubicMoment_Estimates_HuxleyCoordinateGeometry`, `CubicMoment_Estimates_HuxleyGaussianCoordinates`, `CubicMoment_Estimates_HuxleyGaussianKernel`, `CubicMoment_Estimates_IdealMangoldtContour`, `CubicMoment_Estimates_IdealMangoldtTail`, `CubicMoment_Estimates_IdealPrimePowerError`, `CubicMoment_Estimates_IndependentMellinTail`, `CubicMoment_Estimates_InverseLogWeight`, `CubicMoment_Estimates_KernelScaling`, `CubicMoment_Estimates_KernelTail`, `CubicMoment_Estimates_LogCellMajorant`, `CubicMoment_Estimates_LogSchwartzWeight`, `CubicMoment_Estimates_LogSmoothWeights`, `CubicMoment_Estimates_LogarithmicLoss`, `CubicMoment_Estimates_MeanValueGaussianEnergy`, `CubicMoment_Estimates_MeanValueGaussianKernel`, `CubicMoment_Estimates_MellinFiniteSeminorm`, `CubicMoment_Estimates_MellinHeckeContour`, `CubicMoment_Estimates_MellinSmooth`, `CubicMoment_Estimates_ModelPartialSummation`, `CubicMoment_Estimates_MontgomeryVaughanProof`, `CubicMoment_Estimates_NoncubeExponents`, `CubicMoment_Estimates_NoncubePowerBounds`, `CubicMoment_Estimates_NormProfileOperator`, `CubicMoment_Estimates_OuterDyadicSum`, `CubicMoment_Estimates_OuterPrimalScale`, `CubicMoment_Estimates_PrimaryPrimePNTProofLogCount`, `CubicMoment_Estimates_PrimaryPrimePNTProofTheta`, `CubicMoment_Estimates_PrimeDyadicMajorant`, `CubicMoment_Estimates_PrimeDyadicWeight`, `CubicMoment_Estimates_PrimeGroupingGap`, `CubicMoment_Estimates_PrimeLogWindow`, `CubicMoment_Estimates_PrimeSmoothTransition`, `CubicMoment_Estimates_PrimeTailMellinMean`, `CubicMoment_Estimates_PrimeWeightExpansion`, `CubicMoment_Estimates_PrimitiveResidueConductorKernel`, `CubicMoment_Estimates_PrimitiveResidueFourier`, `CubicMoment_Estimates_RealScaleLargeMoment`, `CubicMoment_Estimates_RieszFubini`, `CubicMoment_Estimates_ScaleFirstMiddleRange`, `CubicMoment_Estimates_SemiprimeGaussTailWeights`, `CubicMoment_Estimates_ShiftedThetaCompletion`, `CubicMoment_Estimates_ShortConvolutionExpansion`, `CubicMoment_Estimates_SmoothLogDenominator`, `CubicMoment_Estimates_SmoothShortContinuity`, `CubicMoment_Estimates_ThinCellCutoff`, `CubicMoment_Estimates_ThinCellPowerScale`, `CubicMoment_Estimates_TripleIndexCount`, `CubicMoment_Estimates_TripleScaleLogRange`, `CubicMoment_Estimates_TripleScaleSpread`, `CubicMoment_Estimates_TwistedShortProducts`, `CubicMoment_Estimates_UpperNoStopParameters`, `CubicMoment_Estimates_WeightedGram`, `CubicMoment_Estimates_WideLogDenominator`, `CubicMoment_Theta_CubicThetaArithmeticModelEnergy`, `CubicMoment_Theta_CubicThetaArithmeticModelTorus`, `CubicMoment_Theta_CubicThetaArithmeticPoleIsolation`, `CubicMoment_Theta_CubicThetaArithmeticTorus`, `CubicMoment_Theta_CubicThetaAveragedHeat`, `CubicMoment_Theta_CubicThetaCellFourierSeparation`, `CubicMoment_Theta_CubicThetaCircleActual`, `CubicMoment_Theta_CubicThetaCircleExtraction`, `CubicMoment_Theta_CubicThetaCircleInversion`, `CubicMoment_Theta_CubicThetaCircleLimit`, `CubicMoment_Theta_CubicThetaCircleNormalized`, `CubicMoment_Theta_CubicThetaCirclePlane`, `CubicMoment_Theta_CubicThetaCirclePolynomial`, `CubicMoment_Theta_CubicThetaCircleSeries`, `CubicMoment_Theta_CubicThetaCircleTaylor`, `CubicMoment_Theta_CubicThetaCircleUniform`, `CubicMoment_Theta_CubicThetaComplexHeight`, `CubicMoment_Theta_CubicThetaCoordinateProfile`, `CubicMoment_Theta_CubicThetaCuspFourierNormalization`, `CubicMoment_Theta_CubicThetaFiniteConductor`, `CubicMoment_Theta_CubicThetaFiniteCoordinateBox`, `CubicMoment_Theta_CubicThetaFrequencyContinuation`, `CubicMoment_Theta_CubicThetaFullEisensteinFourier`, `CubicMoment_Theta_CubicThetaHeatMellinBounds`, `CubicMoment_Theta_CubicThetaHeatScaling`, `CubicMoment_Theta_CubicThetaHeatSmallHeight`, `CubicMoment_Theta_CubicThetaHighHeatNonzero`, `CubicMoment_Theta_CubicThetaHorizontalCoefficient`, `CubicMoment_Theta_CubicThetaHorizontalEnergy`, `CubicMoment_Theta_CubicThetaInvertedFourierObservable`, `CubicMoment_Theta_CubicThetaInvertedResidue`, `CubicMoment_Theta_CubicThetaInvertedTorus`, `CubicMoment_Theta_CubicThetaMassEuler`, `CubicMoment_Theta_CubicThetaMassPushforward`, `CubicMoment_Theta_CubicThetaMeromorphicIdentity`, `CubicMoment_Theta_CubicThetaNormalizedRamified`, `CubicMoment_Theta_CubicThetaPositiveAveragedHeat`, `CubicMoment_Theta_CubicThetaPositiveFourierMass`, `CubicMoment_Theta_CubicThetaPositiveRadialWindow`, `CubicMoment_Theta_CubicThetaPositiveZeroWindow`, `CubicMoment_Theta_CubicThetaPrimeCubeResidueEigenvalue`, `CubicMoment_Theta_CubicThetaProjectedPlane`, `CubicMoment_Theta_CubicThetaRadialEulerScaling`, `CubicMoment_Theta_CubicThetaRadialMellinIntegrability`, `CubicMoment_Theta_CubicThetaRadialProfileEquation`, `CubicMoment_Theta_CubicThetaRadialRealPositive`, `CubicMoment_Theta_CubicThetaRadialTent`, `CubicMoment_Theta_CubicThetaRadialTestMass`, `CubicMoment_Theta_CubicThetaRamifiedLowContinuation`, `CubicMoment_Theta_CubicThetaRamifiedMassSeries`, `CubicMoment_Theta_CubicThetaRamifiedPrimaryContinuation`, `CubicMoment_Theta_CubicThetaRamifiedSeries`, `CubicMoment_Theta_CubicThetaRamifiedTopPhase`, `CubicMoment_Theta_CubicThetaRamifiedTopRow`, `CubicMoment_Theta_CubicThetaRegularizedFourier`, `CubicMoment_Theta_CubicThetaRemovableResidue`, `CubicMoment_Theta_CubicThetaScalarHeightSeed`, `CubicMoment_Theta_CubicThetaScatteringRegular`, `CubicMoment_Theta_CubicThetaShiftedModelSeries`, `CubicMoment_Theta_CubicThetaShiftedPeriodMeasure`, `CubicMoment_Theta_CubicThetaShiftedTorus`, `CubicMoment_Theta_CubicThetaSquareDecomposition`, `CubicMoment_Theta_CubicThetaTorusCellIntegral`, `CubicMoment_Theta_CubicThetaTorusCellTransport`, `CubicMoment_Theta_CubicThetaTorusModes`, `CubicMoment_Theta_CubicThetaUnitLifting`, `CubicMoment_Theta_CubicThetaZeroObservable`, `CubicMoment_Transform_MetaplecticCoefficientDecay`, `CubicMoment_Transform_MetaplecticHeight`, `CubicMoment_Transform_MetaplecticNaturalCutoff`, `CubicMoment_Transform_MetaplecticNormDyads`, `CubicMoment_Transform_MetaplecticPoleContour`, `CubicMoment_Transform_MetaplecticRadialLattice`, `CubicMoment_Transform_MetaplecticTransformBounds`, `CubicMoment_Transform_MetaplecticTransformDecay`, `CubicMoment_Transform_MetaplecticVoronoi`, `DirichletL_CubicDyadicDecay`, `Fourier`, `SmoothExistence`, `Sobolev`, `Wiener`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ096A006`; the statement `OAI.CubicFirstMoment.SieveExponent.recurrence`.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 7ef5c0c

import Mathlib
import Batteries.Tactic.Lemma

section
-- module Solutions.OAIQ096_CM.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434

/-- Mathlib's newer `TensorProduct.inductionOn` (no `zero` case: it is the `tmul` case at
`0 ⊗ₜ 0`); ours has only `TensorProduct.induction_on`, which asks for one. Not named
`TensorProduct.inductionOn`: inside `namespace OAI` that would make `open TensorProduct` open
`OAI.TensorProduct` instead of Mathlib's. -/
@[elab_as_elim]
theorem tensorInductionOn {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {motive : TensorProduct R M N → Prop} (z : TensorProduct R M N)
    (tmul : ∀ x y, motive (TensorProduct.tmul R x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z (by simpa using tmul 0 0) tmul add
/-- Mathlib's newer case names for `FreeGroup.induction_on` (`one`, where ours says `C1`). -/
@[elab_as_elim]
theorem freeGroupInductionOn {α : Type*} {C : FreeGroup α → Prop} (z : FreeGroup α) (one : C 1)
    (of : ∀ x, C (FreeGroup.of x)) (inv_of : ∀ x, C (FreeGroup.of x) → C (FreeGroup.of x)⁻¹)
    (mul : ∀ x y, C x → C y → C (x * y)) : C z :=
  FreeGroup.induction_on z one of inv_of mul
/-- The first projection of a probability measure on a product: found by instance search in d13f23b
(total `Measure.map`), here a measurable map. -/
instance isProbabilityMeasure_map_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.fst) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
instance isProbabilityMeasure_map_snd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.snd) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
instance isProbabilityMeasure_map_subtype_val {α : Type*} [MeasurableSpace α] {p : α → Prop}
    {μ : MeasureTheory.Measure {a // p a}} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Subtype.val) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable
/-- Mathlib d13f23b's `YoungDiagram.card_transpose`. -/
@[simp]
theorem _root_.YoungDiagram.card_transpose (μ : YoungDiagram) : μ.transpose.card = μ.card := by
  unfold YoungDiagram.card
  apply Finset.card_bij (fun c _ => c.swap)
  · intro c hc
    have : c ∈ μ.transpose := hc
    rw [YoungDiagram.mem_transpose] at this
    exact this
  · intro a _ b _ h
    simpa using h
  · intro b hb
    refine ⟨b.swap, ?_, by simp⟩
    show b.swap ∈ μ.transpose
    rw [YoungDiagram.mem_transpose]
    simpa using hb
/-- For a measurable equivalence `e`, `IsProbabilityMeasure (μ.map e)` is found by instance search
(Mathlib d13f23b finds it for every map `f`: there `Measure.map` of a non-measurable map is a Dirac
mass, here it is `0`, so only the measurable case can be shimmed). -/
instance isProbabilityMeasure_map_measurableEquiv {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
    (e : α ≃ᵐ β) : MeasureTheory.IsProbabilityMeasure (μ.map e) :=
  MeasureTheory.Measure.isProbabilityMeasure_map e.measurable.aemeasurable
section Y
instance closedSubmoduleNormedAddCommGroup {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : NormedAddCommGroup K :=
  inferInstanceAs (NormedAddCommGroup K.toSubmodule)
instance closedSubmoduleNormedSpace {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : NormedSpace 𝕜 K :=
  inferInstanceAs (NormedSpace 𝕜 K.toSubmodule)
instance closedSubmoduleInner {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : InnerProductSpace 𝕜 K :=
  inferInstanceAs (InnerProductSpace 𝕜 K.toSubmodule)
end Y

/-- The underlying ⋆-subalgebra of a von Neumann algebra is norm closed, found by instance search in
d13f23b (Kadison similarity, oaiq-075). -/
instance vonNeumannToStarSubalgebraIsClosed {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (P : VonNeumannAlgebra H) : IsClosed (P.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  have := Set.isClosed_centralizer (Set.centralizer (P.carrier))
  rw [P.centralizer_centralizer'] at this
  exact this
/-- A closed commutative ⋆-subalgebra of a C⋆-algebra is a commutative C⋆-algebra, found by instance search
in d13f23b (Kadison similarity, oaiq-075). -/
noncomputable instance starSubalgebraCommCStarAlgebra {B : Type*} [CStarAlgebra B] (A : StarSubalgebra ℂ B)
    [IsClosed (A : Set B)] [IsMulCommutative A] : CommCStarAlgebra A :=
  { StarSubalgebra.cstarAlgebra A with
    mul_comm := fun a b => IsMulCommutative.is_comm.comm a b }
section OAIVecLookup
variable {α : Type _}
@[simp] theorem vecCons3_one (a b c : α) : (![a, b, c] : Fin 3 → α) 1 = b := rfl
@[simp] theorem vecCons3_two (a b c : α) : (![a, b, c] : Fin 3 → α) 2 = c := rfl
@[simp] theorem vecCons4_one (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 1 = b := rfl
@[simp] theorem vecCons4_two (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 2 = c := rfl
@[simp] theorem vecCons4_three (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 3 = d := rfl
end OAIVecLookup
section OAIVecTail
variable {α : Type _}
@[simp] theorem vecConsTail1_1 (x : α) (f : Fin 1 → α) : (Matrix.vecCons x f : Fin 2 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail2_1 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail2_2 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_1 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail3_2 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_3 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_1 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail4_2 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail4_3 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_4 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 4 = f 3 := rfl
end OAIVecTail
@[simp] theorem fin3_mk_0 (h : 0 < 3) : (⟨0, h⟩ : Fin 3) = 0 := rfl
@[simp] theorem fin3_mk_1 (h : 1 < 3) : (⟨1, h⟩ : Fin 3) = 1 := rfl
@[simp] theorem fin3_mk_2 (h : 2 < 3) : (⟨2, h⟩ : Fin 3) = 2 := rfl
@[simp] theorem fin4_mk_0 (h : 0 < 4) : (⟨0, h⟩ : Fin 4) = 0 := rfl
@[simp] theorem fin4_mk_1 (h : 1 < 4) : (⟨1, h⟩ : Fin 4) = 1 := rfl
@[simp] theorem fin4_mk_2 (h : 2 < 4) : (⟨2, h⟩ : Fin 4) = 2 := rfl
@[simp] theorem fin4_mk_3 (h : 3 < 4) : (⟨3, h⟩ : Fin 4) = 3 := rfl
@[simp] theorem fin5_mk_0 (h : 0 < 5) : (⟨0, h⟩ : Fin 5) = 0 := rfl
@[simp] theorem fin5_mk_1 (h : 1 < 5) : (⟨1, h⟩ : Fin 5) = 1 := rfl
@[simp] theorem fin5_mk_2 (h : 2 < 5) : (⟨2, h⟩ : Fin 5) = 2 := rfl
@[simp] theorem fin5_mk_3 (h : 3 < 5) : (⟨3, h⟩ : Fin 5) = 3 := rfl
@[simp] theorem fin5_mk_4 (h : 4 < 5) : (⟨4, h⟩ : Fin 5) = 4 := rfl
/-- `norm_num` cannot decide equalities of `Fin` literals here (oaiq-091). -/
@[simp] theorem fin3_lit_0_1 : ((0 : Fin 3) = 1) ↔ False := by decide
@[simp] theorem fin3_lit_0_2 : ((0 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_1_0 : ((1 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin3_lit_1_2 : ((1 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_2_0 : ((2 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin3_lit_2_1 : ((2 : Fin 3) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_0_1 : ((0 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_0_2 : ((0 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin4_lit_0_3 : ((0 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_1_0 : ((1 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_1_2 : ((1 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin4_lit_1_3 : ((1 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_2_0 : ((2 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_2_1 : ((2 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_2_3 : ((2 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_3_0 : ((3 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_3_1 : ((3 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_3_2 : ((3 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_0_1 : ((0 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_0_2 : ((0 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_0_3 : ((0 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_0_4 : ((0 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_1_0 : ((1 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_1_2 : ((1 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_1_3 : ((1 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_1_4 : ((1 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_2_0 : ((2 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_2_1 : ((2 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_2_3 : ((2 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_2_4 : ((2 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_3_0 : ((3 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_3_1 : ((3 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_3_2 : ((3 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_3_4 : ((3 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_4_0 : ((4 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_4_1 : ((4 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_4_2 : ((4 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_4_3 : ((4 : Fin 5) = 3) ↔ False := by decide
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_CubicOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite cubic sieve operators, bilinear norms and coprime completion. -/

section

noncomputable section
open scoped BigOperators ContDiff
open Set Filter MeasureTheory Topology
attribute [local instance] Classical.propDecidable

open UniqueFactorizationMonoid

namespace CubicFirstMoment

def euclideanConj {ι : Type*} [Fintype ι] (v : EuclideanSpace ℂ ι) :
    EuclideanSpace ℂ ι := WithLp.toLp 2 (fun i => star (v i))

def matrixHilbertOperator {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℂ) : EuclideanSpace ℂ κ →L[ℂ] EuclideanSpace ℂ ι :=
  A.toEuclideanLin.toContinuousLinearMap

end CubicFirstMoment

end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_SieveExponent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative cube and dual bounds under a sieve exponent. -/

section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def decayConstant (α : ℝ) : ℝ := 4*2^α/(2^α-1)

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_QuantitativeRecurrence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform quantitative recurrence and exponent monotonicity. -/

section

noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def sieveRecurrenceShape (ξ M N : ℝ) : ℝ :=
  M+(M*N)^(2/3 : ℝ)+N+M^(1-ξ)*N^(2*ξ-1)

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_SieveImprovement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Amplification, iteration to exponent four-thirds and the cubic large sieve. -/

section

noncomputable section
namespace CubicFirstMoment

def sieveImprove (ξ : ℝ) : ℝ := (6*ξ-4)/(3*ξ-1)
def sieveAmplify (ξ : ℝ) : ℝ := (6*ξ-5)/(3*ξ-1)

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_GramDyad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted dyadic row summation and explicit coprime Gram bounds. -/

section

noncomputable section
open scoped BigOperators ContDiff
open Set Filter MeasureTheory Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def gramDyadConstant (p : ℝ) : ℝ := 4*2^p/(2^p-1)

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MellinSmooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Analytic properties of the actual compactly supported smooth norm
weights. Passing to logarithmic coordinates realizes every vertical
Mellin line as a Schwartz Fourier transform. -/

noncomputable section
open MeasureTheory Set Filter Asymptotics
open scoped Topology SchwartzMap ContDiff FourierTransform

namespace CubicFirstMoment

lemma mellin_frequency_growth :
    ∃ (k : ℕ) (C : ℝ), ∀ t : ℝ, ‖t‖ ≤ C*(1+‖t/(2*Real.pi)‖)^k := by
  refine ⟨1,2*Real.pi,?_⟩
  intro t
  rw [pow_one, norm_div, Real.norm_of_nonneg (by positivity : 0 ≤ 2*Real.pi)]
  have hp : 0 < 2*Real.pi := by positivity
  calc
    ‖t‖ = (2*Real.pi) * (‖t‖/(2*Real.pi)) := by field_simp
    _ ≤ _ := by gcongr; linarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticHeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The zero-angular metaplectic inputs, stated for the literal Gauss series.

Sources: Heath-Brown, *Kummer's conjecture for cubic Gauss sums* (2000),
§3 Lemma 3 (author manuscript p.9), with angular index zero; Dunn–Radziwiłł,
*Bias in cubic Gauss sums* (2024), arXiv:2109.07463v3, Proposition 5.2,
pp.29–30. No Type-I estimate or Mellin contour identity is an input here. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def metaplecticA0 : ℝ :=
  (2*Real.pi)^(5/3:ℝ)/(3^(7/2:ℝ)*Real.Gamma (2/3:ℝ))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeckeSymmetry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar factors on the symmetry line in the primitive Hecke
functional equation. These identities apply also to fixed infinity type.
They keep conductor-dependent phases outside the dual polynomial. -/

noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def heckeGammaRatio (k t : ℝ) : ℂ :=
  Complex.Gamma ((k+1/2:ℝ) - (t:ℂ)*Complex.I) /
    Complex.Gamma ((k+1/2:ℝ) + (t:ℂ)*Complex.I)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MellinHeckeContour
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The contour step for the full smooth character sum. Polynomial
vertical growth is an analytic property of the L-function; the decay,
integrability and vanishing edges are derived for the actual weight. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace CubicFirstMoment

def mellinEdgeMajorant (C t : ℝ) : ℝ := C/(1+|t|)^2

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticVoronoi
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal level/angular Voronoi input of Dunn--Radziwill,
arXiv:2109.07463v3, Proposition 5.3, equations (5.79)--(5.82), pp.33--34.
The raw formula is kept separate from its proved Gauss/phase normalization.
The index `n` below denotes the actual frequency `n / lambda`; zero is excluded.
No estimate for a completed sum is assumed. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def metaplecticGammaQuotient (ℓ : ℤ) (s : ℂ) : ℂ :=
  (Complex.Gamma (5/6+(|ℓ|:ℤ)/2-s)*Complex.Gamma (7/6+(|ℓ|:ℤ)/2-s))/
    (Complex.Gamma (s+(|ℓ|:ℤ)/2-1/6)*Complex.Gamma (s+(|ℓ|:ℤ)/2+1/6))

/-- Equation (5.81), parameterized on the vertical line `Re s = -sigma`. -/
def metaplecticTransform (ℓ : ℤ) (W : ℝ → ℂ) (σ v : ℝ) : ℂ :=
  ((1/(2*Real.pi):ℝ):ℂ)*∫ t : ℝ,
    (v:ℂ)^(((-σ:ℝ):ℂ)+(t:ℂ)*Complex.I)*
      metaplecticGammaQuotient ℓ (((-σ:ℝ):ℂ)+(t:ℂ)*Complex.I)*
      mellin W (((-σ:ℝ):ℂ)+(t:ℂ)*Complex.I)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticTransformBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounds for the literal angular Voronoi transform. Its Gamma quotient
is a product of two ordinary shifted Hecke quotients, so the only
special-function input is the same precise DLMF bounded-strip estimate. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

def metaplecticAngularShift (ℓ : ℤ) : ℝ := (|ℓ|:ℤ)/2

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticTransformDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact far-left height bound for the shifted metaplectic transform.
The power of the height is 4m, proved by finite Gamma recurrence. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

def metaplecticShiftTransform (ℓ : ℤ) (W : ℝ → ℂ) (b v t : ℝ) : ℂ :=
  ((1/(2*Real.pi):ℝ):ℂ)*∫ τ : ℝ,
    (v:ℂ)^((b:ℂ)+(τ:ℂ)*Complex.I)*
      metaplecticGammaQuotient ℓ ((b:ℂ)+((τ-t:ℝ):ℂ)*Complex.I)*
      mellin W ((b:ℂ)+(τ:ℂ)*Complex.I)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_GramOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# From Gram row sums to character-polynomial bounds

Finite duality turns the row-sum bound into an operator estimate. This is
the Cauchy/Gram step used after the multiplicity argument in the exceptional-character-moment argument.
-/

noncomputable section
open scoped BigOperators

namespace CubicFirstMoment

def finiteGram {ι κ : Type*} (N : Finset κ) (T : ι → κ → ℂ) (p q : ι) : ℂ :=
  ∑ n ∈ N, T p n * star (T q n)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_RieszFubini
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute convergence for the Gaussian representation of the Riesz pairing. -/

noncomputable section
open scoped SchwartzMap
open MeasureTheory Set
namespace CubicFirstMoment

def rieszGaussianWeight (a : ℝ) (z : ℂ) (t : ℝ) : ℝ :=
  t^(a-1)*Real.exp (-‖z‖^2*t)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_GaussianMellin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Mellin change of variables for the Gaussian Riesz identity. -/

noncomputable section
open scoped SchwartzMap
open MeasureTheory Set
namespace CubicFirstMoment

lemma inverse_mellin_change (H : ℝ → ℂ) (a : ℝ) {c : ℝ} (hc : 0 < c) :
    (∫ t in Ioi (0:ℝ), (t^(a-2):ℝ)*H (c/t)) =
      (c^(a-1):ℝ)*(∫ v in Ioi (0:ℝ), (v^(-a):ℝ)*H v) := by
  have hi := integral_comp_rpow_Ioi (fun u : ℝ => (u^(-a):ℝ)*H (c*u))
    (show (-1:ℝ) ≠ 0 by norm_num)
  have hs : (∫ t in Ioi (0:ℝ), (t^(a-2):ℝ)*H (c/t)) =
      ∫ u in Ioi (0:ℝ), (u^(-a):ℝ)*H (c*u) := by
    rw [← hi]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    have hp : t^(a-2) = t^((-1:ℝ)-1)*(t^(-1:ℝ))^(-a) := by
      rw [← Real.rpow_mul ht.le,← Real.rpow_add ht]
      congr 1
      ring
    rw [hp]
    simp only [abs_neg,abs_one,one_mul,Real.rpow_neg_one,Complex.real_smul]
    push_cast
    rw [div_eq_mul_inv]
    ring
  rw [hs]
  have hscale := integral_comp_mul_left_Ioi (fun v : ℝ => (v^(-a):ℝ)*H v) 0 hc
  simp only [mul_zero] at hscale
  have hpow (u : ℝ) (hu : u ∈ Ioi (0:ℝ)) :
      ((u^(-a):ℝ):ℂ)*H (c*u) = ((c^a:ℝ):ℂ)*(((c*u)^(-a):ℝ):ℂ)*H (c*u) := by
    rw [Real.mul_rpow hc.le hu.le,Complex.ofReal_mul]
    have he : c^a*c^(-a) = (1:ℝ) := by rw [← Real.rpow_add hc]; simp
    rw [← mul_assoc,← Complex.ofReal_mul (c^a) (c^(-a)),he]
    simp
  calc
    _ = ((c^a:ℝ):ℂ)*(∫ u in Ioi (0:ℝ), ((c*u)^(-a):ℝ)*H (c*u)) := by
      rw [← integral_const_mul]
      exact setIntegral_congr_fun measurableSet_Ioi (fun u hu => by
        simpa only [mul_assoc] using hpow u hu)
    _ = _ := by
      rw [hscale,Complex.real_smul]
      have he : c^a*c⁻¹ = c^(a-1) := by
        simpa only [Real.rpow_one,div_eq_mul_inv] using (Real.rpow_sub hc a 1).symm
      rw [← mul_assoc,← Complex.ofReal_mul,he]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticRadialLattice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual area term in primary radial lattice summation. The
nonzero dual frequencies are bounded by the existing Schwartz estimate. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators SchwartzMap
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def primaryRadialMain (W : ℝ → ℂ) (Y : ℝ) : ℂ :=
  ((2*Real.pi*Y/(9*Real.sqrt 3):ℝ):ℂ)*(∫ x in Ioi (0:ℝ), W x)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_EndpointKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Summing the sharp-cutoff endpoint kernel

The Fourier truncation argument sums rapidly decaying endpoint errors over
integer norms. These bounds supply the quantitative lattice step in
`eq:perron-error`, uniformly in the location of the endpoint.
-/

noncomputable section
open scoped BigOperators

namespace CubicFirstMoment

def endpointKernel (h d : ℝ) : ℝ := h ^ 2 / (h + |d|) ^ 2

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_KernelTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Quantitative kernel tails

A finite weighted L¹ moment gives a uniform bound for the two endpoint
tails. Scaling the kernel will make the moment independent of the
truncation height, as required for a sharp cutoff.
-/

noncomputable section
open MeasureTheory

namespace CubicFirstMoment

def kernelMoment (k : ℝ → ℂ) (T : ℝ) : ℝ :=
  ∫ y, ‖k y‖ * (1 + T * |y|) ^ 2

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_KernelScaling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Scaling a cutoff kernel

The normalization and weighted L¹ moment are preserved under `T k(Tx)`.
Thus a single Schwartz kernel gives a uniform family of interval
approximations at all positive truncation heights.
-/

noncomputable section
open MeasureTheory

namespace CubicFirstMoment

def scaledKernel (k : ℝ → ℂ) (T y : ℝ) : ℂ := (T : ℂ) * k (T*y)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_WeightedGram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A smooth majorant in the Gram bound

The majorant needs to be at least one only on the coefficient support.
It may vanish elsewhere. This is the weighted Cauchy step used to pass
from smooth character Gram estimates to finite Dirichlet polynomials.
-/

noncomputable section
open scoped BigOperators

namespace CubicFirstMoment

def weightedFiniteGram {ι κ : Type*} (N : Finset κ) (w : κ → ℝ)
    (T : ι → κ → ℂ) (p q : ι) : ℂ :=
  ∑ n ∈ N, (w n : ℂ) * T p n * star (T q n)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LogarithmicLoss
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit loss in logarithmic pigeonholing has exponent zero. -/
noncomputable section
open Filter
open scoped Topology
namespace CubicFirstMoment

def logarithmicBoxLoss (t : ℕ) (H K Y : ℝ) : ℝ :=
  ((⌊Real.log (Y^H/Y^(-K))⌋₊+1:ℕ)^t:ℝ)*(Real.exp 1)^(2*t)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LogSmoothWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Logarithmic full factors are exact linear combinations of two smooth
weights. No logarithmic coefficient is silently discarded. -/
noncomputable section
open Set Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def logSmoothWeight (W : ℝ → ℂ) (x : ℝ) : ℂ := (Real.log x:ℂ)*W x

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SmoothShortContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuity and Mellin weights for actual finite smooth short sums. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace CubicFirstMoment

def zeroLineMellinMass (V : ℝ → ℂ) : ℝ :=
  (1/(2*Real.pi))*(∫ τ : ℝ, ‖mellin V ((τ:ℂ)*Complex.I)‖)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SmoothLogDenominator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth, globally defined extensions of the logarithmic denominator
weights. The extension equals the literal reciprocal on the application
range, so no pole can interfere with parameter-uniform differentiation. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace CubicFirstMoment

def positiveSmoothExtension (c x : ℝ) : ℝ :=
  Real.smoothTransition (2*x/c-1)*x +
    (1-Real.smoothTransition (2*x/c-1))*c

lemma positiveSmoothExtension_pos {c : ℝ} (hc : 0 < c) (x : ℝ) :
    0 < positiveSmoothExtension c x := by
  by_cases hx : x ≤ c/2
  · have h : 2*x/c-1 ≤ 0 := by
      have hh : 2*x ≤ c := by linarith
      have hd := (div_le_one hc).mpr hh
      linarith
    simpa [positiveSmoothExtension,Real.smoothTransition.zero_of_nonpos h] using hc
  · have hx0 : 0 < x := by linarith
    have h0 := Real.smoothTransition.nonneg (2*x/c-1)
    have h1 := Real.smoothTransition.le_one (2*x/c-1)
    dsimp [positiveSmoothExtension]
    by_cases he : Real.smoothTransition (2*x/c-1) = 0
    · simpa [he] using hc
    · exact add_pos_of_pos_of_nonneg (mul_pos (lt_of_le_of_ne h0 (Ne.symm he)) hx0)
        (mul_nonneg (by linarith) hc.le)

lemma positiveSmoothExtension_smooth (c : ℝ) :
    ContDiff ℝ ∞ (positiveSmoothExtension c) := by
  unfold positiveSmoothExtension
  fun_prop

def smoothReciprocal (c x : ℝ) : ℝ := (positiveSmoothExtension c x)⁻¹

lemma smoothReciprocal_smooth {c : ℝ} (hc : 0 < c) :
    ContDiff ℝ ∞ (smoothReciprocal c) :=
  (positiveSmoothExtension_smooth c).inv (fun x => (positiveSmoothExtension_pos hc x).ne')

def smoothLog (x : ℝ) : ℝ := Real.log (positiveSmoothExtension 1 x)

lemma smoothLog_smooth : ContDiff ℝ ∞ smoothLog :=
  (positiveSmoothExtension_smooth 1).log
    (fun x => (positiveSmoothExtension_pos (by norm_num) x).ne')

/-- Parameters are the normalized scale logarithm and inverse logarithm
of the outer length. Both range over a compact rectangle. -/
def logDenominatorWeight (c : ℝ) (w : ℝ → ℂ) (p : ℝ × ℝ) (x : ℝ) : ℂ :=
  (smoothReciprocal c (p.1+p.2*smoothLog x):ℂ)*w x

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_NoncubeExponents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Strict exponent gaps away from the two exceptional conductor shapes.
These are the normalized exponents of the two cubic-sieve bounds and
of the ordinary character large sieve, respectively. -/

noncomputable section

namespace CubicFirstMoment

def pSieveExponent (p q : ℝ) : ℝ :=
  max ((2*p+q)/3-1) (max ((q-p)/3) ((p+q-1)/3))

def qSieveExponent (p q : ℝ) : ℝ :=
  max ((2*p+q)/3-1) (max (2*(p-q)/3) ((2*p-1)/3))

def ordinarySieveExponent (p q : ℝ) : ℝ :=
  max (-(p+2*q)/3) ((5*p+4*q)/3-1)

def noncubeSieveExponent (p q : ℝ) : ℝ :=
  min (pSieveExponent p q) (min (qSieveExponent p q) (ordinarySieveExponent p q))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_NoncubePowerBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact normalization of the three numerical sieve bounds, and a quantitative
uniform power saving away from the exceptional configurations. -/

noncomputable section
namespace CubicFirstMoment

/-- The actual cubic-sieve bound, divided by the dispersion benchmark. -/
def pSieveRatio (B P Q : ℝ) : ℝ :=
  Q*(P+B+(P*B)^(2/3:ℝ))/(B*(P*Q^2)^(1/3:ℝ))

def qSieveRatio (B P Q : ℝ) : ℝ :=
  P*(Q+B+(Q*B)^(2/3:ℝ))/(B*(P*Q^2)^(1/3:ℝ))

def ordinarySieveRatio (B P Q : ℝ) : ℝ :=
  (B+(P*Q)^2)/(B*(P*Q^2)^(1/3:ℝ))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_PrimeProductPolynomialBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Height-independent bounds for the actual two full prime convolutions.
These are used only beyond the power range of the published height mean. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def primeCoefficientMassConstant (R : ℝ) (n : ℕ) : ℝ := 18*R^n*(n^n:ℕ)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticPoleContour
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The pole crossed by the Type-I Mellin contour. These are calculus
lemmas: no analytic continuation or arithmetic estimate is assumed. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace CubicFirstMoment

def poleRegularPart (M g : ℂ → ℂ) (ρ c : ℂ) (s : ℂ) : ℂ :=
  M s*g s+ρ*dslope M c s

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticCoefficientDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual dual coefficient bound becomes a product of a geometric
ramified factor and convergent norm powers. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def metaplecticRamifiedRatio (σ : ℝ) : ℝ := (3:ℝ)^(-2/3-σ)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticNormDyads
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Canonical finite norm-dyad partition of the retained Voronoi pairs.
The integral frequency d³n has norm exactly three times N(d³ν). -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def metaplecticNormDyadLength (j : ℕ) : ℝ := 2*(2:ℝ)^j/3

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedDyadPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sharp dyads with the strict lower endpoint used by stopped rows.
The partition is finite and its count depends only on the norm envelope. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def stoppedNormDyadLength (j : ℕ) : ℝ := (2:ℝ)^(j+1)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_AnalyticDiskLogDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The local logarithmic-derivative estimate at the fixed radii needed
for the Hecke zero-free argument. -/
noncomputable section
open Filter Set
open scoped Topology BigOperators
namespace CubicFirstMoment

def diskLogDerivativeConstant : ℝ :=
  16*(2/3:ℝ)^2/((2/3:ℝ)-1/2)^3+
    1/(((7/8:ℝ)^2/(3/4:ℝ)-3/4)*Real.log ((7/8:ℝ)/(3/4:ℝ)))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CellGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Geometry of the product-boundary cells

After scaling log-norm by the cell width, the two norm cells are unit
intervals. A pair meeting a width-one strip around the product boundary
can lie on only five integer diagonals. This proves the bounded-neighbor
claim used in `eq:near-cell-diagonal` rather than postulating it.
-/

noncomputable section
open scoped BigOperators

namespace CubicFirstMoment

def nearCellOffsets (c : ℝ) : Finset ℤ := Finset.Icc (⌊c⌋ - 3) (⌊c⌋ + 1)

@[simp] theorem nearCellOffsets_card (c : ℝ) : (nearCellOffsets c).card = 5 := by
  simp only [nearCellOffsets, Int.card_Icc]
  omega

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubicWhittakerBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local regularity and explicit majorants of the cubic theta Fourier kernel. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

def cubicWhittakerPowerConstant (k : ℕ) : ℝ :=
  ((k.factorial:ℝ)*Real.Gamma ((k:ℝ)-1/3)/2)*(2*Real.pi)^(1/3-2*(k:ℝ))

lemma cubicWhittakerPowerConstant_pos {k : ℕ} (hk : 1 ≤ k) :
    0 < cubicWhittakerPowerConstant k := by
  have hkR : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hg := Real.Gamma_pos_of_pos (show 0 < (k:ℝ)-1/3 by linarith)
  unfold cubicWhittakerPowerConstant
  positivity

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubicBesselSymmetricSlope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An even real integral for the negative Whittaker slope. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

def cubicWhittakerNegativeSlope (v u : ℝ) : ℝ :=
  (4*Real.pi*v*Real.cosh u-1)*Real.exp (-4*Real.pi*v*Real.cosh u)*Real.cosh (u/3)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DispersionCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed nonnegative majorant for the outer norm interval. -/
noncomputable section
open Set
open scoped ContDiff
namespace CubicFirstMoment

def dispersionCutoff (R x : ℝ) : ℝ :=
  Real.smoothTransition (2*x-1)*Real.smoothTransition (R+1-x)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DyadicMellinTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A weighted Mellin tail from actual dyadic height means. -/
noncomputable section
open Set Filter MeasureTheory
namespace CubicFirstMoment

def mellinHeightDyad (T : ℝ) (n : ℕ) : Set ℝ := Ico ((2:ℝ)^n*T) ((2:ℝ)^(n+1)*T)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DyadicReconstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact telescoping on contracting dyads. Functions that vanish below
one have a finite, hence unambiguous, dyadic reconstruction. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def dyadicDifference (F : ℝ → ℂ) (X : ℝ) : ℂ := F X-F (X/2)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ModelPartialSummation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The elementary prime model from the ordinary prime ideal theorem

The only number-theoretic hypothesis used here is the ordinary asymptotic
for the number of primary prime elements.  The power-weighted consequence
is derived by Abel summation.
-/

noncomputable section

open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology

namespace CubicFirstMoment

/-- The derivative of the scale appearing in the first moment. -/
def firstMomentScaleDerivative (X : ℝ) : ℝ :=
  X ^ (-1 / 6 : ℝ) / Real.log X * (5 / 6 - 1 / Real.log X)

/-- Cumulative count of an arithmetic sequence collected by integer norm. -/
def normCountingSum (c : ℕ → ℝ) (X : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 0 ⌊X⌋₊, c n

/-- Its power-weighted cumulative sum. -/
def normWeightedSum (c : ℕ → ℝ) (X : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 0 ⌊X⌋₊, (n : ℝ) ^ (-1 / 6 : ℝ) * c n

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DyadicScaleBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A summable majorant for first-moment scales along contracting dyads. -/
noncomputable section
open Filter Asymptotics
namespace CubicFirstMoment

def regularizedMomentScale (X : ℝ) : ℝ := X^(5/6:ℝ)/(1+Real.log X)

def dyadicMomentRatio (j : ℕ) : ℝ :=
  (1+(j:ℝ)*Real.log 2)*((2:ℝ)^(-(5/6:ℝ)))^j

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FiniteMellinContour
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite contour displacement with an explicit horizontal-edge error.
Only holomorphy on the finite rectangle is required. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

def finiteMellinBox (a b T : ℝ) : Set ℂ := Icc a b ×ℂ Icc (-T) T

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TripleIndexCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Counting the three smooth norm indices near the balanced
configuration. The bound is independent of their common large offset. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def tripleIndexCluster (M N C D : ℕ) : Finset (Fin 3 → Fin M) :=
  Finset.univ.filter (fun f => N ≤ ∑ i, (f i).val ∧
    (∑ i, (f i).val) ≤ N+C ∧ ∀ i j, (f i).val ≤ (f j).val+D)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TripleScaleSpread
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A triple with a small bilinear ratio has only logarithmic spread in
its three smooth norm indices. This is the counting input for flat
exceptional boxes. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def tripleNormScale (k : Fin 3 → ℕ) (i : Fin 3) : ℝ := (4/3:ℝ)^(k i)/2

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TripleScaleLogRange
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A product envelope fixes the sum of the three smooth norm indices
up to an absolute interval. Its location may grow with X; its length
is independent of X. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def tripleIndexEnvelopeWidth : ℕ := ⌈20/Real.log (4/3:ℝ)⌉₊+1

def tripleIndexEnvelopeStart (X : ℝ) : ℕ :=
  ⌊Real.log X/Real.log (4/3:ℝ)⌋₊-tripleIndexEnvelopeWidth

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FlatTripleCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite set of flat three-prime norm boxes has only a
fixed power of log log X elements. The large common index offset does
not enter this count. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def flatTripleIndexSet (M G : ℕ) (X : ℝ) : Finset (Fin 3 → Fin M) :=
  Finset.univ.filter (fun f =>
    X/16 ≤ ∏ i, tripleNormScale (fun j => (f j).val) i ∧
    (∏ i, tripleNormScale (fun j => (f j).val) i) ≤ 3*X ∧
    ∃ B : ℝ, (∀ i, tripleNormScale (fun j => (f j).val) i ≤ B) ∧
      B^3 ≤ (∏ i, tripleNormScale (fun j => (f j).val) i)*(1+Real.log X)^G)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FullPrimeMellin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact Mellin separation on the literal full prime-convolution support.
The compact log-norm range follows from the coordinate supports. -/
noncomputable section
open scoped BigOperators ContDiff
open Set MeasureTheory
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def primeConvolutionLogRadius (R : ℝ) (n : ℕ) : ℝ := 1+2*Real.log (R^n)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeckeNormalizedDisk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalize a complete Hecke function at 2+it on a disk of radius 3.
The resulting bound is explicit in the finite and archimedean conductor. -/
noncomputable section
open scoped Topology
namespace CubicFirstMoment

def normalizedHeckeDisk (L : ℂ → ℂ) (t : ℝ) (z : ℂ) : ℂ :=
  L (2+(t:ℂ)*Complex.I+3*z)/L (2+(t:ℂ)*Complex.I)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeckePrimeScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concrete height and conductor scales for the prime contour. -/
noncomputable section
namespace CubicFirstMoment

def primeContourHeight (X : ℝ) : ℝ := Real.exp (Real.sqrt (Real.log X))
def primeContourSize (Q X : ℝ) : ℝ := 32*Q*primeContourHeight X
def primeContourDenominator (Q X : ℝ) : ℝ := Real.log Q+Real.sqrt (Real.log X)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeightAveraging
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive, normalized two-sided height averaging. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

def dyadicHeightMean (f : ℝ → ℝ) (T : ℝ) : ℝ :=
  ((∫ t in T..2*T, f t)+(∫ t in -2*T..-T, f t))/T

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeightEndpointProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed compact profile removes the reciprocal singularity. Dilating
this profile gives the normalized endpoint weights used in localization. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace CubicFirstMoment

def secondDerivativeBudget (f : SchwartzMap ℝ ℂ) : ℝ :=
  1+∑ i ∈ Finset.range 3, SchwartzMap.seminorm ℝ 0 i f

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HuxleyCoordinateGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinates for the Gaussian majorant in the additive large sieve. -/
noncomputable section
namespace CubicFirstMoment

def huxleyXi₀ (x : ℂ) : ℝ := 2*x.im/Real.sqrt 3
def huxleyXi₁ (x : ℂ) : ℝ := x.re-x.im/Real.sqrt 3

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HuxleyGaussianCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute convergence and the two-coordinate theta identity. -/
noncomputable section
namespace CubicFirstMoment

def huxleyGaussianFactor (a ξ : ℝ) (n : ℤ) : ℂ :=
  Complex.exp ((-Real.pi*a*(n:ℝ)^2:ℝ):ℂ)*
    Complex.exp (((2*Real.pi*ξ*(n:ℝ):ℝ):ℂ)*Complex.I)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HuxleyGaussianKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Gaussian Fourier kernel and its periodized majorant. -/
noncomputable section
namespace CubicFirstMoment

def huxleyCoordinateWeight (a : ℝ) (p : ℤ × ℤ) : ℝ :=
  Real.exp (-Real.pi*a*((p.1:ℝ)^2+(p.2:ℝ)^2))

def huxleyGaussianKernel (a : ℝ) (x : ℂ) : ℂ :=
  ∑' p : ℤ × ℤ,
    huxleyGaussianFactor a (huxleyXi₀ x) p.1 *
      huxleyGaussianFactor a (huxleyXi₁ x) p.2

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealMangoldtContour
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite contour identity for the actual ideal von Mangoldt
Mellin integrand. Nonvanishing on the box is supplied by the proved
Hecke zero-free region, before estimating its edges. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

def idealMangoldtMellinIntegrand (L : ℂ → ℂ) (W : ℝ → ℂ) (X : ℝ) (s : ℂ) : ℂ :=
  mellin W s*(X:ℂ)^s*(-logDeriv L s)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealMangoldtTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative tails of the actual prime Mellin integral. Constants are
uniform over a bounded real strip; the principal pole controls all twists. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

def mellinScaledWeight (W : ℝ → ℂ) (X σ t : ℝ) : ℂ :=
  mellin W ((σ:ℂ)+(t:ℂ)*Complex.I)*(X:ℂ)^((σ:ℂ)+(t:ℂ)*Complex.I)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LogSchwartzWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A compact logarithmic Schwartz profile gives an actual smooth norm
weight supported away from zero, with no loss in its logarithmic seminorms. -/
noncomputable section
open Set Filter
open scoped ContDiff SchwartzMap Topology
namespace CubicFirstMoment

def logSchwartzWeight (H : 𝓢(ℝ,ℂ)) (x : ℝ) : ℂ :=
  if 0 < x then H (-Real.log x) else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MellinFiniteSeminorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite seminorm control of vertical Mellin transforms. This keeps the
cost of a varying smooth cutoff visible instead of hiding it in a constant. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff SchwartzMap FourierTransform
namespace CubicFirstMoment

def mellinVerticalCLM : 𝓢(ℝ,ℂ) →L[ℝ] 𝓢(ℝ,ℂ) :=
  (SchwartzMap.compCLM ℝ (by
    simp only [div_eq_mul_inv]
    fun_prop : (fun t : ℝ => t/(2*Real.pi)).HasTemperateGrowth)
    mellin_frequency_growth).comp (SchwartzMap.fourierTransformCLM ℝ)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_NormProfileOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed radial lift and trace Fourier transform form a continuous
linear operator. Thus the finite profile cost is controlled by finitely
many seminorms of the original one-dimensional cutoff. -/
noncomputable section
open scoped BigOperators ContDiff SchwartzMap FourierTransform
namespace CubicFirstMoment

lemma normSq_hasTemperateGrowth : Function.HasTemperateGrowth Complex.normSq := by
  have he : (Complex.normSq : ℂ → ℝ) = fun z => ‖z‖^2 := funext Complex.normSq_eq_norm_sq
  rw [he]
  exact Function.hasTemperateGrowth_norm_sq ℂ

lemma normSq_polynomial_growth : ∃ (k : ℕ) (C : ℝ),
    ∀ z : ℂ, ‖z‖ ≤ C*(1+‖Complex.normSq z‖)^k := by
  refine ⟨1,1,?_⟩
  intro z
  rw [pow_one,one_mul,Real.norm_of_nonneg (Complex.normSq_nonneg z),Complex.normSq_eq_norm_sq]
  nlinarith [sq_nonneg (‖z‖-1)]

def normProfileLiftCLM : 𝓢(ℝ,ℂ) →L[ℂ] 𝓢(ℂ,ℂ) :=
  SchwartzMap.compCLM ℂ normSq_hasTemperateGrowth normSq_polynomial_growth

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeSmoothTransition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded derivatives of the fixed smooth step, before narrowing the
transition in the logarithmic prime cutoff. -/
noncomputable section
open Set
open scoped ContDiff SchwartzMap
namespace CubicFirstMoment

def primeSmoothStep (x : ℝ) : ℂ := (Real.smoothTransition x:ℂ)

lemma primeSmoothStep_smooth : ContDiff ℝ ∞ primeSmoothStep :=
  Complex.ofRealCLM.contDiff.comp Real.smoothTransition.contDiff

lemma primeSmoothStep_deriv_zero {x : ℝ} (hx : x ∉ Icc (0:ℝ) 1) :
    deriv primeSmoothStep x=0 := by
  by_cases hlo : x < 0
  · have he : EqOn primeSmoothStep (fun _ : ℝ => (0:ℂ)) (Iio 0) := by
      intro y hy
      simp only [primeSmoothStep,Real.smoothTransition.zero_of_nonpos hy.le,Complex.ofReal_zero]
    simpa only [deriv_const] using he.deriv isOpen_Iio hlo
  · have hhi : 1 < x := by
      have hh : ¬(0 ≤ x ∧ x ≤ 1) := hx
      have : 0 ≤ x := le_of_not_gt hlo
      exact lt_of_not_ge (fun h => hh ⟨this,h⟩)
    have he : EqOn primeSmoothStep (fun _ : ℝ => (1:ℂ)) (Ioi 1) := by
      intro y hy
      simp only [primeSmoothStep,Real.smoothTransition.one_of_one_le hy.le,Complex.ofReal_one]
    simpa only [deriv_const] using he.deriv isOpen_Ioi hhi

lemma primeSmoothStep_deriv_compact : HasCompactSupport (deriv primeSmoothStep) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := (0:ℝ)) (b := 1))
  intro x hx
  by_contra hn
  exact hx (primeSmoothStep_deriv_zero hn)

def primeSmoothStepDerivative : 𝓢(ℝ,ℂ) :=
  primeSmoothStep_deriv_compact.toSchwartzMap (contDiff_infty_iff_deriv.mp primeSmoothStep_smooth).2

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeLogWindow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A genuine smooth approximation to the dyadic interval in logarithmic
coordinates. The two endpoint transitions have width exactly 1/J. -/
noncomputable section
open Set
open scoped ContDiff SchwartzMap
namespace CubicFirstMoment

def primeLogWindow (J u : ℝ) : ℂ :=
  primeSmoothStep (J*(u+Real.log 2)+1)-primeSmoothStep (J*u)

lemma primeLogWindow_smooth (J : ℝ) : ContDiff ℝ ∞ (primeLogWindow J) :=
  (primeSmoothStep_smooth.comp (by fun_prop)).sub (primeSmoothStep_smooth.comp (by fun_prop))

lemma primeLogWindow_zero_left {J u : ℝ} (hJ : 0 < J)
    (hu : u ≤ -Real.log 2-1/J) : primeLogWindow J u=0 := by
  have hlo : J*(u+Real.log 2)+1 ≤ 0 := by
    have hh := mul_le_mul_of_nonneg_left hu hJ.le
    have he : J*(-Real.log 2-1/J) = -J*Real.log 2-1 := by field_simp
    rw [he] at hh
    nlinarith
  have hhi : J*u ≤ 0 := by
    have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    nlinarith
  simp only [primeLogWindow,primeSmoothStep,Real.smoothTransition.zero_of_nonpos hlo,
    Real.smoothTransition.zero_of_nonpos hhi,Complex.ofReal_zero,sub_self]

lemma primeLogWindow_zero_right {J u : ℝ} (hJ : 0 < J)
    (hu : 1/J ≤ u) : primeLogWindow J u=0 := by
  have hhi : 1 ≤ J*u := by
    have hh := mul_le_mul_of_nonneg_left hu hJ.le
    have he : J*(1/J)=1 := by field_simp
    rwa [he] at hh
  have hlo : 1 ≤ J*(u+Real.log 2)+1 := by
    have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    nlinarith
  simp only [primeLogWindow,primeSmoothStep,Real.smoothTransition.one_of_one_le hlo,
    Real.smoothTransition.one_of_one_le hhi,Complex.ofReal_one,sub_self]

lemma primeLogWindow_support {J : ℝ} (hJ : 0 < J) :
    Function.support (primeLogWindow J) ⊆ Icc (-Real.log 2-1/J) (1/J) := by
  intro u hu
  constructor
  · by_contra h
    exact hu (primeLogWindow_zero_left hJ (le_of_lt (lt_of_not_ge h)))
  · by_contra h
    exact hu (primeLogWindow_zero_right hJ (le_of_lt (lt_of_not_ge h)))

lemma primeLogWindow_compact {J : ℝ} (hJ : 0 < J) : HasCompactSupport (primeLogWindow J) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc (primeLogWindow_support hJ)

def primeLogWindowSchwartz (J : ℝ) (hJ : 0 < J) : 𝓢(ℝ,ℂ) :=
  (primeLogWindow_compact hJ).toSchwartzMap (primeLogWindow_smooth J)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeDyadicWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual smooth dyadic norm cutoff, with a polynomial bound on all
Mellin quantities needed in the prime contour argument. -/
noncomputable section
open Set
open scoped ContDiff SchwartzMap
namespace CubicFirstMoment

def primeDyadicWeight (J : ℝ) (hJ : 1 ≤ J) : ℝ → ℂ :=
  logSchwartzWeight (primeLogWindowSchwartz J (by linarith))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealPrimePowerError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact prime-power deletion error has the classical square-root
size with two logarithms. -/
noncomputable section
namespace CubicFirstMoment

def idealPrimePowerErrorConstant : ℝ := 18*(1+1/Real.log 2)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IndependentMellinTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The high-coordinate tail of the genuine product Mellin weight is bounded
by its explicit finite sum of coordinate moments. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def mellinHeightBox (T : ℝ) : Set (ι → ℝ) := {τ | ∀ i, |τ i| ≤ T}

def mellinHeightPower (A : ℕ) (τ : ι → ℝ) : ℝ := ∑ i, |τ i|^A

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_InverseLogWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The inverse logarithm weight used to remove von Mangoldt's prime
logarithm. Its endpoint and total-variation cost is explicit. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

def inverseLogWeight (t : ℝ) : ℂ := ((Real.log t)⁻¹:ℝ)
def inverseLogDerivative (t : ℝ) : ℝ := -t⁻¹/(Real.log t)^2

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.DirichletL_CubicDyadicDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShortConvolutionExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Each term of the short Möbius product expansion is an actual finite
family of the three permitted arithmetic factors. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev shortBranchIndex (S : Finset ι) := (↥S × Fin 4) ⊕ (↥(Finset.univ\S) × Fin 2)

instance shortBranchIndex_fintype (S : Finset ι) : Fintype (shortBranchIndex S) :=
  inferInstanceAs (Fintype ((↥S × Fin 4) ⊕ (↥(Finset.univ\S) × Fin 2)))

instance shortBranchIndex_decidableEq (S : Finset ι) : DecidableEq (shortBranchIndex S) :=
  inferInstanceAs (DecidableEq ((↥S × Fin 4) ⊕ (↥(Finset.univ\S) × Fin 2)))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeWeightExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact short-factor decomposition of the original finite von Mangoldt
convolution, including its global norm weight and arbitrary character. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def shortBranchScalar (S : Finset ι) : ℂ :=
  (-1)^S.card * 2^(Fintype.card ι-S.card)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TwistedShortProducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Short inversion with a different residue character and Mellin height
on each original prime factor. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def shortBranchSource (S : Finset ι) : shortBranchIndex S → ι
  | Sum.inl (i,_) => i
  | Sum.inr (i,_) => i

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_WideLogDenominator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A quadratic coordinate range accommodates the fixed dilations in
an output norm partition. The denominator identities need no upper range. -/
noncomputable section
open Set
open scoped ContDiff BigOperators
namespace CubicFirstMoment

def wideLogWeightParameters (c : ℝ) : Set (ℝ × ℝ) := Icc c 2 ×ˢ Icc 0 1

lemma wideLogWeightParameters_compact (c : ℝ) : IsCompact (wideLogWeightParameters c) :=
  isCompact_Icc.prod isCompact_Icc

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_RealScaleLargeMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The large-conductor estimate in the actual real dyadic scales.
The exponents are constructed from logarithms, not supplied as extra data. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

def momentScaleExponent (L U : ℝ) : ℝ := Real.log U/Real.log L

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_OuterDyadicSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summation of all three outer-sieve powers at the true Poisson scale. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
open SevenEighths.CubicDyadicDecay

def outerDyadicBound (ε N t : ℝ) : ℝ :=
  SevenEighths.CubicDyadicDecay.decayConstant (ε+1)*t^(-(ε+1))+
  N^(2/3:ℝ)*SevenEighths.CubicDyadicDecay.decayConstant (ε+2/3)*t^(-(ε+2/3))+
  N*SevenEighths.CubicDyadicDecay.decayConstant (ε+1/3)*t^(-(ε+1/3))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_OuterPrimalScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Recover the three primal powers from the exact summed Poisson bound.
The epsilon loss does not multiply the separate unit zero-frequency term. -/
noncomputable section
namespace CubicFirstMoment

def outerPowerConstant (ε R : ℝ) : ℝ :=
  2*(4*R)^ε*(SevenEighths.CubicDyadicDecay.decayConstant (ε+1)*27^(ε+1) +
    R^(2/3:ℝ)*SevenEighths.CubicDyadicDecay.decayConstant (ε+2/3)*27^(ε+2/3) +
    R*SevenEighths.CubicDyadicDecay.decayConstant (ε+1/3)*27^(ε+1/3))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ThinCellCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An actual nonnegative cutoff supported in a cell of width 1/J,
with a plateau on the central half of that cell. -/
noncomputable section
open Set Metric
open scoped ContDiff SchwartzMap
namespace CubicFirstMoment

def thinBaseBump : ContDiffBump (0 : ℝ) :=
  { rIn := 1/4, rOut := 1/2, rIn_pos := by norm_num, rIn_lt_rOut := by norm_num }

def thinBaseSchwartz : 𝓢(ℝ,ℂ) :=
  (thinBaseBump.hasCompactSupport.comp_left (g := Complex.ofReal) (by simp)).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp thinBaseBump.contDiff)

@[simp] lemma thinBaseSchwartz_apply (x : ℝ) :
    thinBaseSchwartz x = (thinBaseBump x : ℂ) := rfl

def thinCellCutoff (J x : ℝ) : ℝ :=
  thinBaseBump (J*(x-(1+1/(2*J))))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LogCellMajorant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete dispersion majorant for each actual log-norm cell. The
cell is contained in the plateau of a cutoff at a comparable scale. -/
noncomputable section
namespace CubicFirstMoment

def logCellScale (J A : ℝ) (i : ℤ) : ℝ :=
  A*Real.exp ((i:ℝ)/J)/(1+2/J)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MeanValueGaussianKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Gaussian Fourier kernel for the mean value of the actual integer
norm Dirichlet polynomial. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment

def meanValueGaussianPhase (L u t : ℝ) : ℂ :=
  Complex.exp (-((t/L:ℝ):ℂ)^2)*Complex.exp (((u*t:ℝ):ℂ)*Complex.I)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MeanValueGaussianEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gaussian mean square of the actual integer-frequency polynomial. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def meanValueGaussianWeight (L t : ℝ) : ℝ := Real.exp (-(t/L)^2)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MontgomeryVaughanProof
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The required ordinary mean value bound, proved by a Gaussian majorant. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

def ordinaryMeanValueConstant : ℝ :=
  Real.exp 1*Real.sqrt Real.pi*(2/(1-Real.exp (-(1/4:ℝ))))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimaryPrimePNTProofLogCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unweight a prime logarithmic mean using a moving power cutoff. -/
noncomputable section
open scoped BigOperators
open Filter Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def selectedRationalPrimes (P : ℕ → Prop) (X : ℝ) : Finset ℕ :=
  (Nat.primesLE ⌊X⌋₊).filter P

def selectedRationalTheta (P : ℕ → Prop) (X : ℝ) : ℝ :=
  ∑ p ∈ selectedRationalPrimes P X, Real.log p

def selectedRationalCount (P : ℕ → Prop) (X : ℝ) : ℝ :=
  (selectedRationalPrimes P X).card

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.Sobolev
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open Real Complex MeasureTheory Filter Topology BoundedContinuousFunction SchwartzMap  BigOperators
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

structure W1 (n : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  toFun : ℝ → E
  smooth : ContDiff ℝ n toFun
  integrable : ∀ ⦃k⦄, k ≤ n → Integrable (iteratedDeriv k toFun)

abbrev W21 := W1 2 ℂ

namespace W1

instance instCoeFunForallReal : CoeFun (W1 n E) (fun _ => ℝ → E) where coe := W1.toFun

end W1

namespace W21

variable {f : W21}

noncomputable def norm (f : ℝ → ℂ) : ℝ :=
    (∫ v, ‖f v‖) + (4 * π ^ 2)⁻¹ * (∫ v, ‖deriv (deriv f) v‖)

noncomputable instance instNorm : Norm W21 where norm := norm ∘ W1.toFun

end W21
end

section
-- module Solutions.OAIQ096_CM.Fourier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open FourierTransform Real Complex MeasureTheory Filter Topology BoundedContinuousFunction
  SchwartzMap VectorFourier BigOperators

section lemmas

@[simp]
theorem nnnorm_eq_of_mem_circle (z : Circle) : ‖z.val‖₊ = 1 :=
  NNReal.coe_eq_one.mp (Circle.norm_coe z)

@[simp]
theorem nnnorm_circle_smul (z : Circle) (s : ℂ) : ‖z • s‖₊ = ‖s‖₊ := by
  simp [show z • s = z.val * s from rfl]

end lemmas
end

section
-- module Solutions.OAIQ096_CM.SmoothExistence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


open MeasureTheory Set Real
open scoped ContDiff

lemma smooth_urysohn_support_Ioo {a b c d : ℝ} (h1 : a < b) (h3 : c < d) :
    ∃ Ψ : ℝ → ℝ, (ContDiff ℝ ∞ Ψ) ∧ (HasCompactSupport Ψ) ∧
    Set.indicator (Set.Icc b c) 1 ≤ Ψ ∧ Ψ ≤ Set.indicator (Set.Ioo a d) 1 ∧
    (Function.support Ψ = Set.Ioo a d) := by
  have := exists_contMDiff_zero_iff_one_iff_of_isClosed (n := ⊤)
    (modelWithCornersSelf ℝ ℝ) (s := Set.Iic a ∪ Set.Ici d) (t := Set.Icc b c)
    (IsClosed.union isClosed_Iic isClosed_Ici) isClosed_Icc
    (by
      simp_rw [Set.disjoint_union_left, Set.disjoint_iff, Set.subset_def,
        Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc, Set.mem_empty_iff_false,
        and_imp, imp_false, not_le, Set.mem_Ici]
      constructor <;> intros <;> linarith)
  obtain ⟨Ψ, hΨSmooth, hΨrange, hΨ0, hΨ1⟩ := this
  simp only [Set.mem_union, Set.mem_Iic, Set.mem_Ici, Set.mem_Icc] at *
  use Ψ
  simp only [range_subset_iff, mem_Icc] at hΨrange
  refine ⟨ContMDiff.contDiff hΨSmooth, ?_, ?_, ?_, ?_⟩
  · apply HasCompactSupport.of_support_subset_isCompact (K := Set.Icc a d) isCompact_Icc
    simp only [Function.support_subset_iff, ne_eq, mem_Icc, ← hΨ0, not_or]
    bound
  · apply Set.indicator_le'
    · intro x hx
      rw [hΨ1 x |>.mp, Pi.one_apply]
      simpa using hx
    · exact fun x _ ↦ (hΨrange x).1
  · intro x
    apply Set.le_indicator_apply
    · exact fun _ ↦ (hΨrange x).2
    · intro hx
      rw [← hΨ0 x |>.mp]
      simpa [-not_and, mem_Ioo, not_and_or, not_lt] using hx
  · ext x
    simp only [Function.mem_support, ne_eq, mem_Ioo, ← hΨ0, not_or, not_le]
end

section
-- module Solutions.OAIQ096_CM.Wiener
private local instance wienerCoeRealComplex {E : Type*} : Coe (E → ℝ) (E → ℂ) := ⟨fun f n => f n⟩
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option linter.style.header false

-- note: the opening of ArithmeticFunction introduces a notation σ that seems
-- impossible to hide, and hence parameters that are traditionally called σ will
-- have to be called σ' instead in this file.

open Real BigOperators ArithmeticFunction MeasureTheory Filter Set FourierTransform LSeries
  Asymptotics SchwartzMap
open Complex hiding log
open scoped Topology
open scoped ContDiff
open scoped ComplexConjugate

variable {n : ℕ} {A a b c d u x y t σ' : ℝ} {ψ Ψ : ℝ → ℂ} {F G : ℂ → ℂ} {f : ℕ → ℂ} {𝕜 : Type}
  [RCLike 𝕜]


noncomputable
def nterm (f : ℕ → ℂ) (σ' : ℝ) (n : ℕ) : ℝ := if n = 0 then 0 else ‖f n‖ / n ^ σ'

instance instMeasurableSpace : MeasurableSpace Circle :=
  inferInstanceAs <| MeasurableSpace <| Subtype _
instance instBorelSpace : BorelSpace Circle :=
  inferInstanceAs <| BorelSpace <| Subtype (· ∈ Metric.sphere (0 : ℂ) 1)

-- TODO - add to mathlib
attribute [fun_prop] Real.continuous_fourierChar



@[continuity]
lemma continuous_multiplicative_ofAdd : Continuous (⇑Multiplicative.ofAdd : ℝ → ℝ) := ⟨fun _ ↦ id⟩

attribute [fun_prop] measurable_coe_nnreal_ennreal

section nabla

variable {α E : Type*} [OfNat α 1] [Add α] [Sub α] {u : α → ℂ}

def cumsum [AddCommMonoid E] (u : ℕ → E) (n : ℕ) : E := ∑ i ∈ Finset.range n, u i

def nabla [Sub E] (u : α → E) (n : α) : E := u (n + 1) - u n

/- `nnabla` is the backward difference `u n - u (n+1)`; kept alongside `nabla`
   for summation-by-parts identities that prefer that orientation. -/
def nnabla [Sub E] (u : α → E) (n : α) : E := u n - u (n + 1)

def shift (u : α → E) (n : α) : E := u (n + 1)

@[simp] lemma cumsum_zero [AddCommMonoid E] {u : ℕ → E} : cumsum u 0 = 0 := by simp [cumsum]

@[simp] lemma nabla_cumsum [AddCommGroup E] {u : ℕ → E} : nabla (cumsum u) = u := by
  ext n ; simp [nabla, cumsum, Finset.range_add_one]

omit [Sub α] in
@[simp] lemma nabla_mul [Ring E] {u : α → E} {c : E} : nabla (fun n => c * u n) = c • nabla u := by
  ext n ; simp [nabla, mul_sub]

omit [Sub α] in
@[simp] lemma nnabla_mul [Ring E] {u : α → E} {c : E} :
    nnabla (fun n => c * u n) = c • nnabla u := by
  ext n ; simp [nnabla, mul_sub]

end nabla

/-- Should this be a gcongr lemma? -/
@[local gcongr]
theorem norm_lt_norm_of_nonneg (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) :
    ‖x‖ ≤ ‖y‖ := by
  simp_rw [Real.norm_eq_abs]
  apply abs_le_abs hxy
  linarith

def chebyWith (C : ℝ) (f : ℕ → ℂ) : Prop := ∀ n, cumsum (‖f ·‖) n ≤ C * n

def cheby (f : ℕ → ℂ) : Prop := ∃ C, chebyWith C f





lemma smooth_urysohn (a b c d : ℝ) (h1 : a < b) (h3 : c < d) : ∃ Ψ : ℝ → ℝ,
    (ContDiff ℝ ∞ Ψ) ∧ (HasCompactSupport Ψ) ∧
      Set.indicator (Set.Icc b c) 1 ≤ Ψ ∧ Ψ ≤ Set.indicator (Set.Ioo a d) 1 := by

  obtain ⟨ψ, l1, l2, l3, l4, -⟩ := smooth_urysohn_support_Ioo h1 h3
  refine ⟨ψ, l1, l2, l3, l4⟩



noncomputable def pp (a x : ℝ) : ℝ := a ^ 2 * (x + 1) ^ 2 + (1 - a) * (1 + a)

noncomputable def hh (a t : ℝ) : ℝ := (t * (1 + (a * log t) ^ 2))⁻¹

noncomputable def hh' (a t : ℝ) : ℝ := - pp a (log t) * hh a t ^ 2

noncomputable def gg (x i : ℝ) : ℝ := 1 / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹




noncomputable def toSchwartz (f : ℝ → ℂ) (h1 : ContDiff ℝ ∞ f)
    (h2 : HasCompactSupport f) : 𝓢(ℝ, ℂ) where
  toFun := f
  smooth' := h1
  decay' k n := by
    have l1 : Continuous (fun x => ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖) := by
      have : ContDiff ℝ ∞ (iteratedFDeriv ℝ n f) := h1.iteratedFDeriv_right (mod_cast le_top)
      exact Continuous.mul (by continuity) this.continuous.norm
    have l2 : HasCompactSupport (fun x ↦ ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖) :=
      (h2.iteratedFDeriv _).norm.mul_left
    simpa using l1.bounded_above_of_compact_support l2

@[simp] lemma toSchwartz_apply (f : ℝ → ℂ) {h1 h2 x} : SchwartzMap.mk f h1 h2 x = f x := rfl

@[norm_cast]
theorem set_integral_ofReal {f : ℝ → ℝ} {s : Set ℝ} : ∫ x in s, (f x : ℂ) = ∫ x in s, f x :=
  integral_ofReal

noncomputable def S (f : ℕ → 𝕜) (ε : ℝ) (N : ℕ) : 𝕜 := (∑ n ∈ Finset.Ico ⌈ε * N⌉₊ N, f n) / N
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimaryPrimePNTProofTheta
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Prime-power removal for the mod-three von Mangoldt mean. -/
noncomputable section
open scoped BigOperators
open ArithmeticFunction Filter Topology MeasureTheory
namespace CubicFirstMoment

/-- Rational primes in one residue class, with the literal real cutoff. -/
def rationalProgressionPrimes (a : ℕ) (X : ℝ) : Finset ℕ :=
  (Nat.primesLE ⌊X⌋₊).filter (fun p => p % 3 = a)

def rationalProgressionCount (a : ℕ) (X : ℝ) : ℝ :=
  (rationalProgressionPrimes a X).card

def rationalProgressionTheta (a : ℕ) (X : ℝ) : ℝ :=
  ∑ p ∈ rationalProgressionPrimes a X, Real.log p

def modThreePsi (a : ZMod 3) (X : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 0 ⌊X⌋₊, vonMangoldt.residueClass a n

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeDyadicMajorant
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Comparison of the prime contour majorant over the upper half of a
contracting dyadic partition. -/
noncomputable section
namespace CubicFirstMoment

def primeCancellationWeight (c Q X : ℝ) : ℝ :=
  X*(Real.log (X*Q))^2*Real.exp (-c*Real.log X/primeContourDenominator Q X)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeGroupingGap
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The uniform ordinary-block grouping gap away from the exceptional
three-prime configuration. All bounds come from finite-dimensional
compactness applied to the proved subset-sum alternative. -/
noncomputable section
open Set
open scoped BigOperators
namespace CubicFirstMoment

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def primeGroupingGap (a : ι → ℝ) : ℝ :=
  (Finset.univ.powerset).sup' ⟨∅,by simp⟩
    (fun s => min ((∑ i ∈ s, a i)-1/3) (2/3-∑ i ∈ s, a i))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeTailMellinMean
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full Mellin envelope preserves a translated height mean.
Only a bounded shift range is needed; the complement uses an actual moment
of the smooth Mellin weight and the coarse polynomial bound. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace CubicFirstMoment

noncomputable def zeroLineMellinMoment (W : ℝ → ℂ) (n : ℕ) : ℝ :=
  (1/(2*Real.pi))*(∫ s : ℝ, |s|^n*‖mellin W ((s:ℂ)*Complex.I)‖)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimitiveResidueFourier
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The perfect codifferent pairing on every Eisenstein residue ring.
Unlike the trace pairing without the different, this includes ramified moduli. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma fourierChar_eq_one_integer {t : ℝ} :
    (Real.fourierChar t : ℂ) = 1 ↔ ∃ n : ℤ, t = n := by
  rw [Real.fourierChar_apply, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, Complex.ofReal_injective ?_⟩
    apply mul_right_cancel₀ Complex.two_pi_I_ne_zero
    convert hn using 1
    all_goals try with_reducible_and_instances rfl
    push_cast
    ring
  · rintro ⟨n, rfl⟩
    refine ⟨n, ?_⟩
    push_cast
    ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimitiveResidueConductorKernel
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Primitivity detects the kernel of every proper residue reduction. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma finite_monoid_idempotent_power {R : Type*} [Monoid R] [Finite R] (x : R) :
    ∃ n : ℕ, 0 < n ∧ x^n * x^n = x^n := by
  classical
  let : TopologicalSpace R := ⊥
  let : DiscreteTopology R := ⟨rfl⟩
  let S : Set R := {y | ∃ n : ℕ, 0 < n ∧ y = x^n}
  obtain ⟨y,hy,he⟩ := exists_idempotent_in_compact_subsemigroup
    (fun r : R => continuous_of_discreteTopology) S
    ⟨x, 1, by norm_num, by simp⟩ (Set.toFinite S).isCompact (by
      rintro a ⟨m,hm,rfl⟩ b ⟨n,hn,rfl⟩
      exact ⟨m+n, by omega, (pow_add _ _ _).symm⟩)
  obtain ⟨n,hn,rfl⟩ := hy
  exact ⟨n,hn,he⟩

/-- A surjection of finite commutative rings is surjective on units.
The proof lifts an arbitrary element and corrects its zero components using
an idempotent power; no local or unramified hypothesis is imposed. -/
lemma finite_ring_units_surjective {R S : Type*} [CommRing R] [CommRing S] [Finite R]
    (f : R →+* S) (hf : Function.Surjective f) :
    Function.Surjective (Units.map f.toMonoidHom) := by
  intro u
  obtain ⟨x,hx⟩ := hf (u : S)
  obtain ⟨n,hn,he⟩ := finite_monoid_idempotent_power x
  let e := x^n
  have he2 : e*e=e := he
  have hfe : f e = 1 := by
    have hu : IsUnit (f e) := by simpa only [e,map_pow,hx] using u.isUnit.pow n
    exact (IsIdempotentElem.iff_eq_one_of_isUnit hu).mp
      (by simpa only [IsIdempotentElem, map_mul] using congrArg f he2)
  have hp : x*x^(n-1) = e := by
    rw [← pow_succ', Nat.sub_add_cancel hn]
  let w := x*e+(1-e)
  let v := x^(n-1)*e+(1-e)
  have hwv : w*v=1 := by
    calc
      _ = (x*x^(n-1))*e^2 + (x+x^(n-1))*(e-e^2) + (1-e)^2 := by
        dsimp only [w,v]
        ring
      _ = 1 := by
        rw [pow_two e,he2,hp,he2,sub_self,mul_zero,add_zero]
        linear_combination he2
  refine ⟨⟨w,v,hwv,by simpa only [mul_comm] using hwv⟩,?_⟩
  apply Units.ext
  change f w = (u:S)
  simp only [w,map_add,map_mul,map_sub,map_one,hfe,hx,mul_one,sub_self,add_zero]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticNaturalCutoff
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One height-independent cutoff serves both the rapid-tail estimate
and the retained mean, with all polynomial scale bounds derived. -/
noncomputable section
namespace CubicFirstMoment

def metaplecticNaturalCutoff (Y R T X δ : ℝ) : ℝ :=
  max 1 (Y^δ*(R^2*T^4/X))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ScaleFirstMiddleRange
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! In the new middle range, the distinguished coordinates themselves
are the shorter group. Their fixed exponent gap supplies the full
bilinear length conditions without a configuration-dependent choice. -/
noncomputable section
open Filter
open scoped BigOperators
namespace CubicFirstMoment

def distinguishedCoordinateSet (i j : ℕ) : Finset (Fin i ⊕ Fin j) :=
  Finset.univ.map ⟨Sum.inl,Sum.inl_injective⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ThinCellPowerScale
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete positive cell exponent absorbs the finite derivative cost. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def thinCellExponent (d : ℕ) : ℝ := 1/(240000*((d:ℝ)+1))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SemiprimeGaussTailWeights
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Both analytic height ranges on the original smooth rough-prime weights.
The parameter families retain their actual transition ratios. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

abbrev SemiprimeTailParameters := (Ici (0:ℝ) × Ici (1:ℝ)) × (Ici (0:ℝ) × Ici (1:ℝ))
def semiTailLeft (z : SemiprimeTailParameters) : ℝ := z.1.2
def semiTailRight (z : SemiprimeTailParameters) : ℝ := z.2.2

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShiftedThetaCompletion
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Decompletion with the fixed angular Gamma shift. The normalized heat
kernel has symmetry weight one, so the functional equation remains s ↦ 1-s. -/
noncomputable section
namespace CubicFirstMoment

def shiftedThetaHeckeL (A κ : ℝ) (Λ : ℂ → ℂ) (s : ℂ) : ℂ :=
  (A:ℂ)^(-s)*(Complex.Gamma (s+(κ:ℂ)))⁻¹*Λ s

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_UpperNoStopParameters
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal no-stop thresholds in the two height ranges. The upper
range uses the smaller stopping level required by the Type-I exponent. -/
noncomputable section
open Filter
namespace CubicFirstMoment

def heightNoStopThreshold (κ X T : ℝ) : ℝ :=
  if T ≤ X^(1/100:ℝ) then X^(38/100:ℝ) else X^(1/3-κ)

def heightNoStopOuterBound (κ X T : ℝ) : ℝ :=
  if T ≤ X^(1/100:ℝ) then X^(39/100:ℝ) else X^(1/3-κ/2)/2

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaUnitLifting
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unit lifting through powers of an Eisenstein modulus. The cardinality
factor is obtained from the actual additive and multiplicative kernels. -/
noncomputable section
namespace CubicFirstMoment

def unitKernelEquivAddKernel {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (h : ∀ x, IsUnit x ↔ IsUnit (f x)) :
    (Units.map f.toMonoidHom).ker ≃ f.toAddMonoidHom.ker where
  toFun u := ⟨(u.val:R)-1,by
    change f ((u.val:R)-1)=0
    rw [map_sub,map_one]
    have he := congrArg (fun v : Sˣ => (v:S)) u.property
    change f (u.val:R)=1 at he
    rw [he,sub_self]⟩
  invFun x :=
    let hu : IsUnit (1+x.val) := (h _).mpr (by
      have hx : f x.val=0 := x.property
      rw [map_add,map_one,hx,add_zero]
      exact isUnit_one)
    ⟨hu.unit,by
      apply Units.ext
      change f (hu.unit:R)=1
      rw [hu.unit_spec,map_add,map_one,show f x.val=0 from x.property,add_zero]⟩
  left_inv u := by
    apply Subtype.ext
    apply Units.ext
    dsimp only
    rw [IsUnit.unit_spec]
    ring
  right_inv x := by
    apply Subtype.ext
    dsimp only
    rw [IsUnit.unit_spec]
    ring

lemma unit_card_mul_of_reflect {R S : Type*} [CommRing R] [CommRing S]
    [Finite R] (f : R →+* S) (hf : Function.Surjective f)
    (h : ∀ x, IsUnit x ↔ IsUnit (f x)) :
    Nat.card Rˣ*Nat.card S=Nat.card R*Nat.card Sˣ := by
  have ha := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup f.toAddMonoidHom.ker
  rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective
    f.toAddMonoidHom hf).toEquiv] at ha
  have hu := Subgroup.card_eq_card_quotient_mul_card_subgroup (Units.map f.toMonoidHom).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective
    (Units.map f.toMonoidHom) (finite_ring_units_surjective f hf)).toEquiv,
    Nat.card_congr (unitKernelEquivAddKernel f h)] at hu
  rw [ha,hu]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedSeries
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact ramified local factor of the normalized totient series. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicTheta_ramified_denominator_ne_zero {s : ℂ} (hs : 1 < s.re) :
    1-(3:ℂ)^(-(s+1))≠0 := by
  have hn : ‖(3:ℂ)^(-(s+1))‖<1 := by
    change ‖((3:ℝ):ℂ)^(-(s+1))‖<1
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0:ℝ)<3)]
    apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    simp only [Complex.neg_re,Complex.add_re,Complex.one_re]
    linarith
  intro he
  have hpow := (sub_eq_zero.mp he).symm
  rw [hpow,norm_one] at hn
  exact lt_irrefl 1 hn

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaTorusModes
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual trace frequencies are the full Fourier basis of the
three-Eisenstein period cell. This fixes the lattice index and Parseval
normalization for the cusp Hilbert space. -/
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
namespace CubicFirstMoment

lemma cubicTheta_torus_fourier_real (n : Fin 2 → ℤ) (x : Fin 2 → ℝ) :
    UnitAddTorus.mFourier n (fun i => (x i:UnitAddCircle))=
      (Real.fourierChar (∑ i, x i*(n i:ℝ)):ℂ) := by
  simp only [UnitAddTorus.mFourier,ContinuousMap.coe_mk,Fin.prod_univ_two,
    fourier_coe_apply,Fin.sum_univ_two,Real.fourierChar_apply]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaTorusCellIntegral
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Haar integration on the cusp torus agrees with the actual half-open
level-three cell, including its boundary convention and Jacobian. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaCube_halfOpen_measure :
    (volume : Measure (Fin 2 → ℝ)).restrict {x | ∀ i, x i∈Ico (0:ℝ) 1}=
      (volume : Measure (Fin 2 → ℝ)).restrict {x | ∀ i, x i∈Ioc (0:ℝ) 1} := by
  have hco := Measure.restrict_pi_pi (fun _ : Fin 2 => (volume : Measure ℝ))
    (fun _ => Ico (0:ℝ) 1)
  have hoc := Measure.restrict_pi_pi (fun _ : Fin 2 => (volume : Measure ℝ))
    (fun _ => Ioc (0:ℝ) 1)
  have he : (fun _ : Fin 2 => (volume : Measure ℝ).restrict (Ico (0:ℝ) 1))=
      (fun _ : Fin 2 => (volume : Measure ℝ).restrict (Ioc (0:ℝ) 1)) := by
    funext i
    exact restrict_Ico_eq_restrict_Ioc
  have hm := hco.trans ((congrArg Measure.pi he).trans hoc.symm)
  have hcoSet : (univ.pi (fun _ : Fin 2 => Ico (0:ℝ) 1))=
      {x | ∀ i, x i∈Ico (0:ℝ) 1} := by ext x; simp
  have hocSet : (univ.pi (fun _ : Fin 2 => Ioc (0:ℝ) 1))=
      {x | ∀ i, x i∈Ioc (0:ℝ) 1} := by ext x; simp
  rw [hcoSet,hocSet] at hm
  exact hm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaHorizontalCoefficient
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact Fourier coefficient normalization for the physical cusp cell. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

local instance cubicThetaHorizontalCoefficientMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance cubicThetaHorizontalCoefficientProbability :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaArithmeticTorus
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal arithmetic remainder on each high-cusp torus, with its
nonzero coefficient computed from the initial arithmetic series. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

local instance cubicThetaArithmeticTorusMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance cubicThetaArithmeticTorusProbability :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCuspFourierNormalization
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalization of the actual weighted arithmetic Fourier coefficient. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaPeriod_fourier_constant :
    ((9*Real.sqrt 3/2:ℝ):ℂ)*(2*Real.pi/(9*Real.sqrt 3):ℂ)=(Real.pi:ℂ) := by
  have hr : (Real.sqrt 3:ℂ)≠0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr (by norm_num : (0:ℝ)<3))
  push_cast
  field_simp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaHeatScaling
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A height dilation turns the weighted heat coefficient into one
Mellin kernel, independent of the spectral parameter. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

def cubicThetaLinearHeat (v A u : ℝ) : ℂ :=
  (Real.exp (-v*u-A*v/u):ℂ)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRadialTestMass
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An integrable scalar majorant for the fixed radial testing weights. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaRadialWeight_bounded (W : C_c(ℝ,ℂ)) :
    ∃ C : ℝ, 0≤C ∧ ∀ v, ‖W v‖≤C := by
  obtain ⟨C,hC⟩ := W.hasCompactSupport.exists_bound_of_continuousOn W.continuous.continuousOn
  refine ⟨max C 0,le_max_right _ _,fun v => ?_⟩
  by_cases hv : v∈tsupport W
  · exact (hC v hv).trans (le_max_left _ _)
  · rw [image_eq_zero_of_notMem_tsupport hv,norm_zero]
    exact le_max_right _ _

lemma cubicThetaRadialWeight_integrable (W : C_c(ℝ,ℂ)) :
    IntegrableOn (fun v : ℝ => ‖W v‖/v^2) (Ioi (2:ℝ)) := by
  obtain ⟨C,hC,hW⟩ := cubicThetaRadialWeight_bounded W
  have hp : IntegrableOn (fun v : ℝ => v^(-2:ℝ)) (Ioi (2:ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)
  apply (hp.const_mul C).mono'
    ((W.continuous.measurable.norm.div (measurable_id.pow_const 2)).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  change 2<v at hv
  change ‖‖W v‖/v^2‖≤C*v^(-2:ℝ)
  rw [Real.norm_of_nonneg (div_nonneg (_root_.norm_nonneg _) (sq_nonneg _))]
  have he : v^(-2:ℝ)=(v^2)⁻¹ := by
    rw [Real.rpow_neg (by linarith : 0≤v),Real.rpow_two]
  rw [he,← div_eq_mul_inv]
  exact div_le_div_of_nonneg_right (hW v) (sq_nonneg _)

def cubicThetaRadialWeightMass (W : C_c(ℝ,ℂ)) : ℝ :=
  ∫ v in Ioi (2:ℝ), ‖W v‖/v^2

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaAveragedHeat
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Averaging the dilated heat kernel against a fixed radial test preserves
exponential decay at both endpoints of its Mellin variable. -/
noncomputable section
open Set MeasureTheory Filter Asymptotics
open scoped CompactlySupported Topology
namespace CubicFirstMoment

def cubicThetaAveragedHeat (W : C_c(ℝ,ℂ)) (A u : ℝ) : ℂ :=
  ∫ v in Ioi (2:ℝ), star (W v)/(v:ℂ)^2*cubicThetaLinearHeat v A u

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRadialMellinIntegrability
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute convergence for the radial-test Mellin interchange. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

def cubicThetaRadialMellinIntegrand (W : C_c(ℝ,ℂ)) (A : ℝ) (s : ℂ)
    (p : ℝ × ℝ) : ℂ :=
  star (W p.1)/(p.1:ℂ)^2*(p.2:ℂ)^(s-2)*cubicThetaLinearHeat p.1 A p.2

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRadialTent
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete nonnegative radial test supported in [2,4]. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaPositive_setIntegral {a x : ℝ} {f : ℝ → ℝ}
    (hc : ContinuousOn f (Ioi a)) (hi : IntegrableOn f (Ioi a))
    (hn : ∀ t∈Ioi a, 0≤f t) (hx : a<x) (hp : 0<f x) :
    0<∫ t in Ioi a, f t := by
  apply (setIntegral_pos_iff_support_of_nonneg_ae
    ((ae_restrict_mem measurableSet_Ioi).mono (fun t ht => hn t ht)) hi).mpr
  have ho := hc.isOpen_inter_preimage isOpen_Ioi (isOpen_Ioi : IsOpen (Ioi (0:ℝ)))
  have hpos := ho.measure_pos (μ:=volume) ⟨x,hx,hp⟩
  apply lt_of_lt_of_le hpos
  apply measure_mono
  intro t ht
  exact ⟨ne_of_gt ht.2,ht.1⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFrequencyContinuation
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Meromorphic continuation of the literal nonzero arithmetic Fourier
Dirichlet coefficients, obtained from the actual automorphic resolvent. -/
noncomputable section
open Set Filter Topology
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

lemma cubicThetaGamma_analytic_right {s : ℂ} (hs : 0 < s.re) : AnalyticAt ℂ Complex.Gamma s := by
  have hd : DifferentiableOn ℂ Complex.Gamma {z : ℂ | 0<z.re} := by
    intro z hz
    apply (Complex.differentiableAt_Gamma z ?_).differentiableWithinAt
    intro m hm
    have he := congrArg Complex.re hm
    simp only [Complex.neg_re,Complex.natCast_re] at he
    have hn : 0≤(m:ℝ) := Nat.cast_nonneg m
    change 0<z.re at hz
    linarith
  exact hd.analyticAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaMeromorphicIdentity
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identity propagation for the actual meromorphic coefficient observations. -/
noncomputable section
open Set Filter Topology
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaMeromorphic_identity {f g : ℂ → ℂ} {U : Set ℂ} {z₀ z : ℂ}
    (hf : MeromorphicOn f U) (hg : MeromorphicOn g U) (hU : IsPreconnected U)
    (h₀ : z₀∈U) (hz : z∈U) (he : f =ᶠ[𝓝[≠] z₀] g) :
    f =ᶠ[𝓝[≠] z] g := by
  have hd : MeromorphicOn (f-g) U := hf.sub hg
  have hzero : (f-g) =ᶠ[𝓝[≠] z₀] 0 := by
    filter_upwards [he] with x hx
    exact sub_eq_zero.mpr hx
  have htop := meromorphicOrderAt_eq_top_iff.mpr hzero
  have hzTop : meromorphicOrderAt (f-g) z = ⊤ := by
    by_contra hne
    exact (hd.meromorphicOrderAt_ne_top_of_isPreconnected hU hz h₀ hne) htop
  have hez := meromorphicOrderAt_eq_top_iff.mp hzTop
  filter_upwards [hez] with x hx
  exact sub_eq_zero.mp hx

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaZeroObservable
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The genuine zero-frequency observation retains the explicit
arithmetic scattering coefficient. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

local instance cubicThetaZeroObservableMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance cubicThetaZeroObservableProbability :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRadialRealPositive
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The chosen test has no real zeros, throughout the spectral line. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaRadialMellin_real_part (σ : ℝ) {u : ℝ} (hu : 0<u) (z : ℂ) :
    ((u:ℂ)^((σ:ℂ)-2)*z).re=u^(σ-2)*z.re := by
  rw [show (σ:ℂ)-2=((σ-2:ℝ):ℂ) by push_cast; rfl,
    ← Complex.ofReal_cpow hu.le,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaScatteringRegular
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! In Re(s)>1 the explicit scattering coefficient has no possible pole
except s=4/3. The denominator is controlled by its convergent Euler product. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaScattering_local_denominator {s : ℂ} (hs : 1 < s.re) :
    1-(3:ℂ)^(2-3*s)≠0 := by
  have hn : ‖(3:ℂ)^(2-3*s)‖<1 := by
    rw [show (3:ℂ)=((3:ℝ):ℂ) by norm_num]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0:ℝ)<3)]
    apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    simp only [Complex.sub_re,Complex.mul_re,Complex.re_ofNat,Complex.im_ofNat,
      zero_mul,sub_zero,Complex.ofReal_ofNat]
    linarith
  intro hz
  have he : (3:ℂ)^(2-3*s)=1 := (sub_eq_zero.mp hz).symm
  rw [he,norm_one] at hn
  exact (lt_irrefl 1) hn

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaArithmeticModelTorus
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuous torus realization of the explicit arithmetic theta series.
The nonconstant scalar is retained while its normalization is established. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment
local instance cubicThetaArithmeticModelTorusMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance cubicThetaArithmeticModelTorusProbability :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFiniteConductor
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Additive conductors of the actual finite Fourier pairing. A function
that factors through a smaller residue ring has Fourier support in the
annihilator of the reduction kernel. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma finiteFourier_translation_support {R : Type*} [CommRing R] [Fintype R]
    (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) (f : R → ℂ) (a m : R)
    (hf : ∀ x b : R, f (x+m*b)=f x)
    (hF : (∑ x : R, f x*ψ (a*x))≠0) : m*a=0 := by
  classical
  by_contra hma
  have hn : ψ.mulShift (m*a)≠1 := hψ hma
  obtain ⟨b,hb⟩ : ∃ b : R, ψ ((m*a)*b)≠1 := by
    by_contra he
    push Not at he
    apply hn
    ext b
    simpa only [AddChar.mulShift_apply,AddChar.one_apply] using he b
  let F : ℂ := ∑ x : R, f x*ψ (a*x)
  have he : F=ψ ((m*a)*b)*F := by
    calc
      F = ∑ x : R, f (x+m*b)*ψ (a*(x+m*b)) :=
        (Equiv.sum_comp (Equiv.addRight (m*b)) _).symm
      _ = ψ ((m*a)*b)*F := by
        simp_rw [hf,mul_add,ψ.map_add_eq_mul]
        dsimp only [F]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        rw [show a*(m*b)=(m*a)*b by ring]
        ring
  exact hF (eq_zero_of_mul_eq_self_left hb he.symm)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRemovableResidue
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The proved vanishing residues give actual analytic extensions,
not only vanishing scalar observations. -/
noncomputable section
open Filter Topology
namespace CubicFirstMoment

lemma cubicThetaSimpleResidue_removable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℂ → E} {a : ℂ} (hf : MeromorphicAt f a)
    (hlim : Tendsto (fun z : ℂ => (z-a) • f z) (𝓝[≠] a) (𝓝 0)) :
    ∃ g : ℂ → E, AnalyticAt ℂ g a ∧ f =ᶠ[𝓝[≠] a] g := by
  have hsub : AnalyticAt ℂ (fun z : ℂ => z-a) a := analyticAt_id.sub analyticAt_const
  have hm : MeromorphicAt (fun z : ℂ => (z-a) • f z) a := hsub.meromorphicAt.smul hf
  have ho := (tendsto_zero_iff_meromorphicOrderAt_pos hm).mp hlim
  change 0 < meromorphicOrderAt ((fun z : ℂ => z-a) • f) a at ho
  rw [meromorphicOrderAt_smul hsub.meromorphicAt hf,meromorphicOrderAt_id_sub_const] at ho
  apply hf.meromorphicOrderAt_nonneg_iff.mp
  cases h : meromorphicOrderAt f a with
  | top => simp
  | coe n =>
    rw [h] at ho
    have hp : (0:ℤ)<1+n := by exact_mod_cast ho
    have hn : (0:ℤ)≤n := by omega
    exact_mod_cast hn

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaArithmeticPoleIsolation
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual arithmetic family has an analytic germ throughout Re(s)>1,
except for its already proved nonzero pole at 4/3. The representative supplied
by the inverse operator can differ at an isolated singular parameter. -/
noncomputable section
open Filter Topology
namespace CubicFirstMoment

lemma analytic_apply {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {A : ℂ → E →L[ℂ] F} {u : ℂ → E} {s : ℂ}
    (hA : AnalyticAt ℂ A s) (hu : AnalyticAt ℂ u s) :
    AnalyticAt ℂ (fun z => A z (u z)) s := by
  have hb := (ContinuousLinearMap.id ℂ (E →L[ℂ] F)).analyticAt_bilinear (A s,u s)
  exact hb.comp (f:=fun z => (A z,u z)) (x:=s) (hA.prod hu)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaComplexHeight
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Holomorphic dependence of the Fourier heat integral on a complex
height with positive real part. All majorants are actual heat integrals. -/
noncomputable section
open Set Filter MeasureTheory Topology
namespace CubicFirstMoment

def cubicThetaComplexHeightHeat (s : ℂ) (A : ℝ) (z : ℂ) (t : ℝ) : ℂ :=
  (t:ℂ)^(s-2)*Complex.exp (-z*((t+A/t:ℝ):ℂ))

def cubicThetaHeightMajorant (s : ℂ) (A d t : ℝ) : ℝ :=
  t^(s.re-2)*Real.exp (-d*(t+A/t))

lemma cubicThetaComplexHeightHeat_norm (s z : ℂ) (A : ℝ) {t : ℝ} (ht : 0<t) :
    ‖cubicThetaComplexHeightHeat s A z t‖=cubicThetaHeightMajorant s A z.re t := by
  rw [cubicThetaComplexHeightHeat,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos ht,
    Complex.norm_exp]
  simp [cubicThetaHeightMajorant,Complex.mul_re]

lemma cubicThetaComplexHeightHeat_bound (s : ℂ) {A d : ℝ} (hA : 0<A) (_hd : 0<d)
    {z : ℂ} (hz : d≤z.re) {t : ℝ} (ht : 0<t) :
    ‖cubicThetaComplexHeightHeat s A z t‖ ≤ cubicThetaHeightMajorant s A d t := by
  rw [cubicThetaComplexHeightHeat_norm s z A ht]
  unfold cubicThetaHeightMajorant
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (Real.rpow_nonneg ht.le _)
  have hm : 0≤t+A/t := by positivity
  simpa only [neg_mul] using neg_le_neg (mul_le_mul_of_nonneg_right hz hm)

lemma cubicThetaComplexHeightHeat_deriv (s z : ℂ) (A t : ℝ) :
    HasDerivAt (fun w => cubicThetaComplexHeightHeat s A w t)
      (-((t+A/t:ℝ):ℂ)*cubicThetaComplexHeightHeat s A z t) z := by
  have h := (((hasDerivAt_id z).neg.mul_const ((t+A/t:ℝ):ℂ)).cexp).const_mul
    ((t:ℂ)^(s-2))
  refine h.congr_deriv ?_
  · dsimp only [cubicThetaComplexHeightHeat,Pi.neg_apply,id_eq]
    ring

def cubicThetaComplexHeightIntegral (s : ℂ) (A : ℝ) (z : ℂ) : ℂ :=
  ∫ t in Ioi (0:ℝ), cubicThetaComplexHeightHeat s A z t

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaHeatSmallHeight
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! At small height the normalized nonzero-frequency heat integral tends
to the ordinary Gamma integral. This supplies nonvanishing without any
assumption on special-function zeros. -/
noncomputable section
open Set Filter MeasureTheory Topology
namespace CubicFirstMoment

def cubicThetaNormalizedHeat (s : ℂ) (A v t : ℝ) : ℂ :=
  (Real.exp (-t):ℂ)*(t:ℂ)^(s-2)*(Real.exp (-A*v^2/t):ℂ)

lemma cubicThetaNormalizedHeat_bound (s : ℂ) {A : ℝ} (hA : 0≤A)
    (v : ℝ) {t : ℝ} (ht : 0<t) :
    ‖cubicThetaNormalizedHeat s A v t‖≤‖(Real.exp (-t):ℂ)*(t:ℂ)^(s-2)‖ := by
  unfold cubicThetaNormalizedHeat
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  exact mul_le_of_le_one_right (_root_.norm_nonneg _)
    (Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hA) (sq_nonneg v)) ht.le))

theorem cubicThetaNormalizedHeat_gamma_limit {s : ℂ} (hs : 1 < s.re)
    {A : ℝ} (hA : 0≤A) :
    Tendsto (fun v : ℝ => ∫ t in Ioi (0:ℝ), cubicThetaNormalizedHeat s A v t)
      (𝓝 0) (𝓝 (Complex.Gamma (s-1))) := by
  have hg : IntegrableOn (fun t : ℝ => (Real.exp (-t):ℂ)*(t:ℂ)^(s-2)) (Ioi 0) := by
    simpa only [show s-1-1=s-2 by ring] using
      Complex.GammaIntegral_convergent (s:=s-1) (by simp; linarith)
  have hl := tendsto_integral_filter_of_dominated_convergence
    (μ:=volume.restrict (Ioi (0:ℝ)))
    (fun t : ℝ => ‖(Real.exp (-t):ℂ)*(t:ℂ)^(s-2)‖)
    (Filter.Eventually.of_forall (fun v : ℝ => show
      AEStronglyMeasurable (cubicThetaNormalizedHeat s A v) (volume.restrict (Ioi 0)) from by
        apply Measurable.aestronglyMeasurable
        unfold cubicThetaNormalizedHeat
        fun_prop))
    (Filter.Eventually.of_forall (fun v : ℝ => by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact cubicThetaNormalizedHeat_bound s hA v ht)) hg.norm
    (show ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)), Tendsto
        (fun v : ℝ => cubicThetaNormalizedHeat s A v t) (𝓝 0)
        (𝓝 ((Real.exp (-t):ℂ)*(t:ℂ)^(s-2))) from by
      filter_upwards with t
      have hc : ContinuousAt (fun v : ℝ => cubicThetaNormalizedHeat s A v t) 0 := by
        unfold cubicThetaNormalizedHeat
        fun_prop
      simpa only [cubicThetaNormalizedHeat,zero_pow (by norm_num : (2:ℕ)≠0),
        mul_zero,zero_div,Real.exp_zero,Complex.ofReal_one,mul_one] using hc.tendsto)
  convert hl using 1
  all_goals try with_reducible_and_instances rfl
  rw [Complex.Gamma_eq_integral (by simp; linarith),Complex.GammaIntegral]
  simp only [show s-1-1=s-2 by ring]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaHighHeatNonzero
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! For each parameter in Re(s)>1, the genuine Fourier heat kernel is
nonzero at some height above two. This removes the possible common-zero
obstruction for compact radial tests. -/
noncomputable section
open Set Filter MeasureTheory Topology
namespace CubicFirstMoment

lemma cubicThetaComplexHeightIntegral_real (s : ℂ) (A v : ℝ) :
    cubicThetaComplexHeightIntegral s A (v:ℂ)=
      ∫ t in Ioi (0:ℝ), (t:ℂ)^(s-2)*cubicThetaLinearHeat v A t := by
  unfold cubicThetaComplexHeightIntegral
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  dsimp only [cubicThetaComplexHeightHeat,cubicThetaLinearHeat]
  congr 1
  rw [show -(v:ℂ)*((t+A/t:ℝ):ℂ)=((-v*t-A*v/t:ℝ):ℂ) by push_cast; ring]
  exact (Complex.ofReal_exp _).symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRegularizedFourier
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single holomorphic representative of the pole-cleared arithmetic
Fourier coefficient on Re(s)>1, including its actual residue value. -/
noncomputable section
open Set Filter Topology
namespace CubicFirstMoment

lemma regularized_analytic {f : ℂ → ℂ} {U : Set ℂ}
    (hf : MeromorphicOn f U)
    (hg : ∀ s∈U, ∃ g : ℂ → ℂ, AnalyticAt ℂ g s ∧ f=ᶠ[𝓝[≠] s] g) :
    AnalyticOnNhd ℂ (toMeromorphicNFOn f U) U := by
  intro s hs
  have hn : 0 ≤ meromorphicOrderAt f s := (hf s hs).meromorphicOrderAt_nonneg_iff.mpr (hg s hs)
  have ha := (hf s hs).meromorphicOrderAt_nonneg_iff_analyticAt_toMeromorphicNFAt.mp hn
  rw [analyticAt_congr (toMeromorphicNFOn_eq_toMeromorphicNFAt_on_nhds hf hs)]
  exact ha

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPositiveFourierMass
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! All positive-cutoff Fourier profiles lie in the actual mass closure.
Their pairings are the full positive-height Fourier integrals. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported ContDiff
namespace CubicFirstMoment

lemma cubicThetaPositiveRadialIntegral_zero_extension (W : C_c(ℝ,ℂ))
    {ε : ℝ} (hε : 0≤ε) (hW : ∀ v≤ε,W v=0) (f : ℝ → ℂ) :
    (∫ v in Ioi ε,star (W v)/(v:ℂ)^3*f v)=
      ∫ v in Ioi (0:ℝ),star (W v)/(v:ℂ)^3*f v := by
  have he (a : ℝ) (ha : a≤ε) :
      (∫ v in Ioi a,star (W v)/(v:ℂ)^3*f v)=
        ∫ v : ℝ,star (W v)/(v:ℂ)^3*f v := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro v hv
    rw [hW v ((le_of_not_gt hv).trans ha),star_zero,zero_div,zero_mul]
  rw [he ε le_rfl,he 0 hε]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFullEisensteinFourier
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual initial Eisenstein Fourier coefficient on every positive
horosphere, including below the injective cusp. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

local instance cubicThetaFullEisensteinFourierMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance cubicThetaFullEisensteinFourierProbability :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPositiveAveragedHeat
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The radial Mellin kernel at an arbitrary positive cutoff. Its
endpoint decay follows from the same double heat kernel, with rescaled parameters. -/
noncomputable section
open Set MeasureTheory Filter Asymptotics Topology
open scoped CompactlySupported
namespace CubicFirstMoment

def cubicThetaPositiveAveragedHeat (W : C_c(ℝ,ℂ)) (ε A u : ℝ) : ℂ :=
  ∫ v in Ioi ε,star (W v)/(v:ℂ)^2*cubicThetaLinearHeat v A u

def cubicThetaPositiveRadialWeightMass (W : C_c(ℝ,ℂ)) (ε : ℝ) : ℝ :=
  ∫ v in Ioi ε,‖W v‖/v^2

lemma cubicThetaPositiveRadialWeight_integrable (W : C_c(ℝ,ℂ)) {ε : ℝ} (hε : 0<ε) :
    IntegrableOn (fun v : ℝ => ‖W v‖/v^2) (Ioi ε) := by
  have hi : Integrable (fun v : ℝ => ‖W v‖) :=
    (W.continuous.integrable_of_hasCompactSupport W.hasCompactSupport).norm
  apply (hi.div_const (ε^2)).integrableOn.mono' (by
    apply Measurable.aestronglyMeasurable
    fun_prop)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  have hv' : ε<v := hv
  rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg (_root_.norm_nonneg _) (sq_nonneg _))]
  apply div_le_div_of_nonneg_left (_root_.norm_nonneg _) (sq_pos_of_pos hε)
  nlinarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRadialProfileEquation
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The pointwise Euler equation of a compact radial profile is preserved
by the actual locally finite arithmetic sum. -/
noncomputable section
open Set Filter Topology
open scoped ContDiff CompactlySupported
namespace CubicFirstMoment

def cubicThetaRadialEuler (f : ℝ → ℂ) (v : ℝ) : ℂ :=
  (v:ℂ)^2*deriv (deriv f) v-(v:ℂ)*deriv f v

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRadialEulerScaling
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The radial Euler operator commutes with positive changes of height. -/
noncomputable section
open Set
open scoped ContDiff
namespace CubicFirstMoment

lemma cubicThetaRadialEuler_const_mul (c : ℂ) (f : ℝ → ℂ) (v : ℝ) :
    cubicThetaRadialEuler (fun t => c*f t) v=c*cubicThetaRadialEuler f v := by
  simp only [cubicThetaRadialEuler,deriv_const_mul_field']
  ring

lemma cubicThetaRadialEuler_sub {f g : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (v : ℝ) :
    cubicThetaRadialEuler (fun t => f t-g t) v=
      cubicThetaRadialEuler f v-cubicThetaRadialEuler g v := by
  have hd : deriv (fun t => f t-g t)=(fun t => deriv f t-deriv g t) := by
    funext t
    exact deriv_sub (hf.differentiable (by simp) t) (hg.differentiable (by simp) t)
  have hf' : Differentiable ℝ (deriv f) :=
    ((contDiff_infty_iff_deriv.mp hf).2).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hg' : Differentiable ℝ (deriv g) :=
    ((contDiff_infty_iff_deriv.mp hg).2).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  unfold cubicThetaRadialEuler
  have hdd : deriv (fun t => deriv f t-deriv g t) v=
      deriv (deriv f) v-deriv (deriv g) v := deriv_sub (hf' v) (hg' v)
  rw [hd,hdd]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeResidueEigenvalue
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual arithmetic residue is a cubed-prime Hecke eigenvector.
The proof uses its two computed moments and self-adjointness. -/
noncomputable section
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaSelfAdjoint_two_moments {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (T : E →L[ℂ] E)
    (hsym : ∀ u v, inner ℂ u (T v)=inner ℂ (T u) v)
    (R : E) (lam : ℂ) (hlam : star lam=lam)
    (h1 : inner ℂ (T R) R=lam*inner ℂ R R)
    (h2 : inner ℂ (T (T R)) R=lam^2*inner ℂ R R) : T R=lam • R := by
  have h1' : inner ℂ R (T R)=lam*inner ℂ R R :=
    (hsym R R).trans h1
  have h2' : inner ℂ (T R) (T R)=lam^2*inner ℂ R R :=
    (hsym (T R) R).trans h2
  have hs1 : inner ℂ (T R) (lam • R)=lam*inner ℂ (T R) R :=
    inner_smul_right (𝕜:=ℂ) (E:=E) (T R) R lam
  have hs2 : inner ℂ (lam • R) (T R)=lam*inner ℂ R (T R) := by
    simpa only [starRingEnd_apply,hlam] using
      (inner_smul_left (𝕜:=ℂ) (E:=E) R (T R) lam)
  have hs3 : inner ℂ (lam • R) (lam • R)=lam^2*inner ℂ R R := by
    rw [inner_smul_left (𝕜:=ℂ) (E:=E),
      inner_smul_right (𝕜:=ℂ) (E:=E)]
    simp only [starRingEnd_apply,hlam]
    ring
  have hz : inner ℂ (T R-lam • R) (T R-lam • R)=0 := by
    rw [inner_sub_left,inner_sub_right,inner_sub_right,hs1,hs2,hs3,h1,h1',h2']
    ring
  exact sub_eq_zero.mp ((inner_self_eq_zero (𝕜:=ℂ)).mp hz)


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaInvertedResidue
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The inverted-cusp scalar coefficient has the same residue as the
principal cusp. This assertion concerns scalar scattering coefficients;
it does not identify the nonconstant automorphic residues. -/
noncomputable section
open Filter
open scoped Topology
namespace CubicFirstMoment

def cubicThetaInvertedScatteringFactor (s : ℂ) : ℂ :=
  ((3:ℂ)^(3*s-3)-1)/2

lemma cubicThetaInvertedScatteringFactor_analytic (s : ℂ) :
    AnalyticAt ℂ cubicThetaInvertedScatteringFactor s := by
  let _ : NeZero (3:ℂ) := ⟨by norm_num⟩
  have ha : AnalyticAt ℂ (fun z : ℂ => 3*z-3) s := by fun_prop
  exact (((differentiable_const_cpow_of_neZero (3:ℂ)).analyticAt _).comp ha).sub
    analyticAt_const |>.div analyticAt_const (by norm_num)

lemma cubicThetaInvertedScatteringFactor_pole :
    cubicThetaInvertedScatteringFactor (4/3:ℂ)=1 := by
  norm_num [cubicThetaInvertedScatteringFactor]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedLowContinuation
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continue the literal three low ramified rows by the cubic
identity. Their value at the pole is kept as a residue difference. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaRamifiedCubeFactor (s : ℂ) : ℂ := 27*(27:ℂ)^(-s)

lemma cubicThetaRamifiedCubeFactor_analytic (s : ℂ) :
    AnalyticAt ℂ cubicThetaRamifiedCubeFactor s := by
  let _ : NeZero (27:ℂ) := ⟨by norm_num⟩
  exact analyticAt_const.mul
    (((differentiable_const_cpow_of_neZero (27:ℂ)).analyticAt _).comp
      (f:=fun z : ℂ => -z) (x:=s) analyticAt_id.neg)

lemma cubicThetaRamifiedCubeFactor_pole :
    cubicThetaRamifiedCubeFactor (4/3)=(1/3:ℂ) := by
  unfold cubicThetaRamifiedCubeFactor
  have hp : (27:ℂ)^(-(4/3:ℂ))=(3:ℂ)^(-(4:ℂ)) := by
    rw [show (27:ℂ)=((3:ℕ):ℂ)^(3:ℕ) by norm_num,
      ← Complex.natCast_cpow_natCast_mul]
    congr 1
    norm_num
  rw [hp,Complex.cpow_neg,show (4:ℂ)=((4:ℕ):ℂ) by rfl,Complex.cpow_natCast]
  norm_num

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedPrimaryContinuation
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continue the actual middle primary twist by dividing the explicit
ramified correction. Its residue is derived from actual Fourier residues. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaRamifiedCubeFactor_ne_zero (s : ℂ) :
    cubicThetaRamifiedCubeFactor s≠0 := by
  unfold cubicThetaRamifiedCubeFactor
  exact mul_ne_zero (by norm_num)
    (Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num)))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaInvertedTorus
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The continuous inverted-cusp Fourier series and its physical mean.
The constant term is obtained by an actual torus projection. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace CubicFirstMoment
local instance cubicThetaInvertedTorusMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance cubicThetaInvertedTorusProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
attribute [local instance] Classical.propDecidable

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaInvertedFourierObservable
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Nonzero Fourier observations at the inverted cusp retain the exact
primary Dirichlet coefficient and the original radial normalization. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment
local instance instMeasureSpaceUnitAddCircle_solutions_5 : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance instIsProbabilityMeasureUnitAddCircleVolume_solutions_1 : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedTopRow
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact scale of the top surviving ramified row at the theta pole. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaRamifiedTopScale :
    (81:ℂ)*(81:ℂ)^(-(4/3:ℂ))=(1/3:ℂ)*(3:ℂ)^(-(1/3:ℂ)) := by
  have hp : (81:ℂ)^(-(4/3:ℂ))=(3:ℂ)^(-(16/3:ℂ)) := by
    rw [show (81:ℂ)=((3:ℕ):ℂ)^4 by norm_num,←Complex.natCast_cpow_natCast_mul]
    congr 1
    norm_num
  calc
    _ = (3:ℂ)^(4:ℂ)*(3:ℂ)^(-(16/3:ℂ)) := by rw [hp]; norm_num [Complex.cpow_natCast]
    _ = (3:ℂ)^(-(4/3:ℂ)) := by rw [←Complex.cpow_add _ _ (by norm_num)]; congr 1; norm_num
    _ = (3:ℂ)^(-(1:ℂ))*(3:ℂ)^(-(1/3:ℂ)) := by
      rw [←Complex.cpow_add _ _ (by norm_num)]
      congr 1
      norm_num
    _ = _ := by rw [Complex.cpow_neg,Complex.cpow_one]; norm_num

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedTopPhase
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The selected top-row contribution has the same explicit phase as
the middle-row eigenvector. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def cubicThetaInverseUnitIndex (j : Fin 3) : Fin 3 :=
  if j=0 then 0 else if j=1 then 2 else 1

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaNormalizedRamified
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit ramified residue solution in the normalized Whittaker
coefficient used by the Patterson theta expansion. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaRamifiedWhittaker_scale :
    (Complex.ofReal ((9:ℝ)^(-(1/3:ℝ))))*(3:ℂ)^(-(1/3:ℂ))=(1/3:ℂ) := by
  rw [Complex.ofReal_cpow (by norm_num)]
  norm_num only [Complex.ofReal_neg,Complex.ofReal_div,Complex.ofReal_ofNat]
  rw [show (9:ℂ)=((3:ℕ):ℂ)^2 by norm_num,←Complex.natCast_cpow_natCast_mul]
  norm_num only [Nat.cast_ofNat]
  rw [←Complex.cpow_add _ _ (by norm_num)]
  norm_num [Complex.cpow_neg,Complex.cpow_one]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaTorusCellTransport
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact measurable transport between the arithmetic period cell and
the torus. This also applies to measurable L2 representatives. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment
local instance cubicThetaTorusCellTransportMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCellFourierSeparation
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual horizontal characters separate square-integrable functions
on the half-open arithmetic cell. No periodic representative is assumed. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment
local instance cubicThetaCellFourierSeparationMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaArithmeticModelEnergy
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact horizontal energy of the arithmetic residue model.
This retains the common scalar for its remaining normalization. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment
local instance cubicThetaArithmeticModelEnergyMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance cubicThetaArithmeticModelEnergyProbability :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCirclePolynomial
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite Fourier polynomial underlying higher angular extraction.
Its highest Fourier mode is a pure power of the complex frequency. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

local instance instFactLtRealOfNat_solutions : Fact (0<(1:ℝ)) := ⟨by norm_num⟩

def cubicThetaCirclePower (w : ℂ) (m : ℕ) (t : AddCircle (1:ℝ)) : ℂ :=
  (w*fourier 1 t+star w*fourier (-1) t)^m

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCircleTaylor
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform angular Taylor extraction for one Fourier character. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

local instance instFactLtRealOfNat_solutions_1 : Fact (0<(1:ℝ)) := ⟨by norm_num⟩

def cubicThetaCircleLinear (w : ℂ) (t : AddCircle (1:ℝ)) : ℂ :=
  w*fourier 1 t+star w*fourier (-1) t

def cubicThetaCirclePhase (w : ℂ) (r : ℝ) (t : AddCircle (1:ℝ)) : ℂ :=
  Complex.exp ((2*Real.pi*Complex.I*(r:ℂ))*cubicThetaCircleLinear w t)

def cubicThetaCircleTaylor (w : ℂ) (r : ℝ) (k : ℕ) (t : AddCircle (1:ℝ)) : ℂ :=
  ∑ j∈Finset.range (k+1),
    ((2*Real.pi*Complex.I*(r:ℂ))^j/(j.factorial:ℂ))*cubicThetaCirclePower w j t

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCircleExtraction
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fourier coefficient estimates for the small-circle character expansion. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment

local instance instFactLtRealOfNat_solutions_2 : Fact (0<(1:ℝ)) := ⟨by norm_num⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCircleSeries
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small-circle coefficient extraction for an absolutely convergent Fourier series.
Only the zeroth, selected and next absolute frequency moments are used. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment

local instance instFactLtRealOfNat_solutions_3 : Fact (0<(1:ℝ)) := ⟨by norm_num⟩
variable {ι : Type*}

def cubicThetaCircleSeries (a w : ι→ℂ) (r : ℝ) (t : AddCircle (1:ℝ)) : ℂ :=
  ∑' n, a n*cubicThetaCirclePhase (w n) r t

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCircleNormalized
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Radius-normalized coefficient extraction, with a linear error in the radius. -/
noncomputable section
open Filter
open scoped Topology
namespace CubicFirstMoment

local instance instFactLtRealOfNat_solutions_4 : Fact (0<(1:ℝ)) := ⟨by norm_num⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCircleActual
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small-circle coefficients of the actual fixed-height theta series.
Both orientations retain their precise signed angular coefficients. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment

def cubicThetaCircleOrder (rev : Bool) (k : ℕ) : ℤ := if rev then -(k:ℤ) else (k:ℤ)
def cubicThetaCircleMultiplier (rev : Bool) (d : ℂ) : ℂ := if rev then star d else d
def cubicThetaSignedCircle (rev : Bool) (d : ℂ) (r : ℝ) (t : AddCircle (1:ℝ)) : ℂ :=
  (r:ℂ)*d*fourier (if rev then -1 else 1) t

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCircleInversion
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Inversion takes every horizontal circle to a reversed horizontal circle.
Its transformed height depends only on the radius. -/
noncomputable section
open Filter
open scoped Topology
namespace CubicFirstMoment

def cubicThetaCircleDualDirection (q : ℂ) (v r : ℝ) : ℂ :=
  -1/(q^2*((r^2+v^2:ℝ):ℂ))

def cubicThetaCircleDualHeight (q : ℂ) (v r : ℝ) : ℝ :=
  v/(Complex.normSq q*(r^2+v^2))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCircleUniform
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform small-circle extraction above a fixed positive height. -/
noncomputable section
namespace CubicFirstMoment

local instance instFactLtRealOfNat_solutions_6 : Fact (0<(1:ℝ)) := ⟨by norm_num⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCircleLimit
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Angular extraction survives continuous changes of height and direction. -/
noncomputable section
open Filter
open scoped Topology
namespace CubicFirstMoment

local instance instFactLtRealOfNat_solutions_7 : Fact (0<(1:ℝ)) := ⟨by norm_num⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPositiveRadialWindow
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Mellin windows at an arbitrary strictly positive height cutoff. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaPositiveWindow_support (W : C_c(ℝ,ℂ)) {ε : ℝ}
    (hε : 0<ε) (hW : ∀ v≤ε,W v=0) : tsupport (star W)⊆Ioi (0:ℝ) := by
  have hs : tsupport (star W)⊆Ici ε := by
    apply closure_minimal ?_ isClosed_Ici
    intro v hv
    by_contra hn
    apply hv
    change star (W v)=0
    rw [hW v (le_of_not_ge hn),star_zero]
  intro v hv
  exact lt_of_lt_of_le hε (hs hv)

lemma cubicThetaPositiveWindow_power (W : C_c(ℝ,ℂ)) {ε : ℝ}
    (hε : 0<ε) (hW : ∀ v≤ε,W v=0) (a : ℂ) :
    (∫ v in Ioi ε,star (W v)*(v:ℂ)^a/(v:ℂ)^3)=mellin (star W) (a-2) := by
  have he : (∫ v in Ioi ε,star (W v)*(v:ℂ)^a/(v:ℂ)^3)=
      ∫ v in Ioi (0:ℝ),star (W v)*(v:ℂ)^a/(v:ℂ)^3 := by
    simpa only [div_mul_eq_mul_div] using
      cubicThetaPositiveRadialIntegral_zero_extension W hε.le hW (fun v => (v:ℂ)^a)
  rw [he]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v hv
  dsimp only
  have hv0 : (v:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hv.ne'
  have hp : (v:ℂ)^a/(v:ℂ)^3=(v:ℂ)^(a-2-1) := by
    rw [←Complex.cpow_natCast,←Complex.cpow_sub _ _ hv0]
    congr 1
    ring
  change star (W v)*(v:ℂ)^a/(v:ℂ)^3=(v:ℂ)^(a-2-1)*star (W v)
  rw [mul_div_assoc,hp,mul_comm]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPositiveZeroWindow
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The zero Fourier mode at every positive cutoff. The incoming Mellin
term is entire and therefore contributes no residue. -/
noncomputable section
open Set MeasureTheory Filter Topology
open scoped CompactlySupported
namespace CubicFirstMoment
local instance cubicThetaPositiveZeroWindowMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance cubicThetaPositiveZeroWindowProbability :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCirclePlane
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The constant mode disappears from every positive small-circle coefficient. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace CubicFirstMoment

local instance instFactLtRealOfNat_solutions_8 : Fact (0<(1:ℝ)) := ⟨by norm_num⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCoordinateProfile
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pointwise geometric majorants beyond the finite coordinate boxes. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

def cubicThetaRadiusProfile (κ r : ℝ) : ℝ := r^2*Real.exp (-κ*r)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFiniteCoordinateBox
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal finite coordinate boxes are bounded by rational certificates. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def cubicThetaPrimaryBoxBound (n : ℕ) : ℝ :=
  match n with
  | 4 => (20167/2500000:ℝ)
  | 7 => (8523/5000000:ℝ)
  | 13 => (843/5000000:ℝ)
  | 16 => (651/10000000:ℝ)
  | 19 => (11/400000:ℝ)
  | 25 => (59/10000000:ℝ)
  | 28 => (29/10000000:ℝ)
  | 31 => (3/2000000:ℝ)
  | 37 => (1/2000000:ℝ)
  | 43 => (1/5000000:ℝ)
  | 49 => (1/10000000:ℝ)
  | 52 => (1/10000000:ℝ)
  | 61 => (1/10000000:ℝ)
  | 64 => (1/10000000:ℝ)
  | 67 => (1/10000000:ℝ)
  | 73 => (1/10000000:ℝ)
  | 76 => (1/10000000:ℝ)
  | 79 => (1/10000000:ℝ)
  | 91 => (1/10000000:ℝ)
  | 97 => (1/10000000:ℝ)
  | 100 => (1/10000000:ℝ)
  | 103 => (1/10000000:ℝ)
  | 127 => (1/10000000:ℝ)
  | 133 => (1/10000000:ℝ)
  | 139 => (1/10000000:ℝ)
  | 148 => (1/10000000:ℝ)
  | 151 => (1/10000000:ℝ)
  | 193 => (1/10000000:ℝ)
  | 196 => (1/10000000:ℝ)
  | 217 => (1/10000000:ℝ)
  | 271 => (1/10000000:ℝ)
  | _ => 0

def cubicThetaRamifiedBoxBound (n : ℕ) : ℝ :=
  match n with
  | 1 => (28407/40000000:ℝ)
  | 3 => (3521/1000000000:ℝ)
  | 4 => (101/200000000:ℝ)
  | 7 => (1/200000000:ℝ)
  | 12 => (1/1000000000:ℝ)
  | _ => 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaShiftedTorus
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual continuous Fourier expansion at a translated cusp,
parametrized by its period-nine torus. All frequencies, including zero,
are retained until the explicit arithmetic support is applied. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment
local instance instMeasureSpaceUnitAddCircle_solutions_6 : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance instIsProbabilityMeasureUnitAddCircleVolume_solutions_2 : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaShiftedPeriodMeasure
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual period-nine cell and its exact volume normalization. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

local instance instMeasureSpaceUnitAddCircle_solutions_7 : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance instIsProbabilityMeasureUnitAddCircleVolume_solutions_3 : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaShiftedModelSeries
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The absolutely convergent arithmetic series determined by the proved
other-cusp coefficients. Its constant coefficient is explicitly zero. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable
local instance instMeasureSpaceUnitAddCircle_solutions_8 : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance instIsProbabilityMeasureUnitAddCircleVolume_solutions_4 : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaProjectedPlane
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual projected cusp expansion supports the same angular
extraction as the original theta series, with its own literal coefficients. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology MatrixGroups
namespace CubicFirstMoment

local instance instFactLtRealOfNat_solutions_9 : Fact (0<(1:ℝ)) := ⟨by norm_num⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedMassSeries
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ramified coefficient mass is an explicit geometric series. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def cubicThetaRamifiedRatio (σ : ℝ) : ℝ := 3^(-2-3*σ)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaHeatMellinBounds
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integrable small- and large-time majorants for the primitive heat kernel. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

def cubicThetaPrimitiveMellinTailMass : ℝ :=
  ∫ t in Ioi (1:ℝ),t^2*Real.exp (-t/2)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaHorizontalEnergy
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normalized Fourier energy is the literal squared modulus integrated
over the physical level-three horizontal cell, with its exact area. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment
local instance cubicThetaHorizontalEnergyMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance cubicThetaHorizontalEnergyProbability :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaSquareDecomposition
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The unique primary squarefree-times-square decomposition, used only
for the coefficient-energy Euler quotient. -/
noncomputable section
namespace CubicFirstMoment

theorem exists_sq_mul_squarefree {α : Type*} [CommMonoidWithZero α]
    [UniqueFactorizationMonoid α] (a : α) : ∃ d c : α, d ^ 2 * c = a ∧ Squarefree c := by
  induction a using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact ⟨0, 1, by simp, squarefree_one⟩
  | h₂ a ha => exact ⟨1, a, by simp, ha.squarefree⟩
  | h₃ a p ha hp ih =>
    obtain ⟨d, c, he, hc⟩ := ih
    by_cases hpc : p ∣ c
    · obtain ⟨c', rfl⟩ := hpc
      refine ⟨p * d, c', ?_, hc.of_mul_right⟩
      rw [← he]
      simp only [pow_two]
      ac_rfl
    · refine ⟨d, p * c, ?_, ?_⟩
      · rw [← he]
        simp only [pow_two]
        ac_rfl
      · exact squarefree_mul_iff.2 ⟨(hp.irreducible.isRelPrime_iff_not_dvd).2 hpc,
          hp.irreducible.squarefree, hc⟩


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaMassEuler
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An explicit zeta expression for the squared arithmetic theta coefficients. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaMassEulerPrefactor (s : ℂ) : ℂ :=
  (6*3^(8:ℂ)*((1-(3:ℂ)^(-2-3*s))⁻¹-1) +
    2*(3:ℂ)^(8-s)*(1-(3:ℂ)^(-2-3*s))⁻¹) *
  (1-(3:ℂ)^(-(1+s))) * (1-(3:ℂ)^(-(2+3*s))) /
  (1-(3:ℂ)^(-(2+2*s)))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaMassPushforward
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summable nonnegative coordinate masses pushed to the actual Fourier lattice. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace CubicFirstMoment

def cubicThetaMassPushforward {ι κ : Type*} (g : ι → κ) (w : ι → ℝ) (n : κ) : ℝ :=
  ∑' p,if g p=n then w p else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaScalarHeightSeed
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The sharp scalar height cutoff has an actual half-open strip seed. -/
noncomputable section
open Set
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

def cubicThetaScalarHeightWeight (s v : ℝ) : ℝ := if v≤1 then v^s else 0

end CubicFirstMoment

end

end OAI
end


