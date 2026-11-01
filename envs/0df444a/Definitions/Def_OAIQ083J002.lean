-- Prove2me | Definitions.Def_OAIQ083J002
-- name    : OAIQ083J002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T20:15:28.67509+00:00
-- url     : https://prove2.me/theorems/cf863be7-7fae-46df-b5b9-ef2bfcf2ff28
-- title:
--   Definitions bundle OAIQ083J002 of the split of OpenAI, The joint Dickman law for consecutive integers
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.JointDickmanPaper.joint_law`, `OAI.JointDickmanPaper.increasing_order` and `OAI.JointDickmanPaper.decreasing_order`, carved from OpenAI's openai/math development (OpenAI, *The joint Dickman law for consecutive integers*, OpenAI Math Release, September 24, 2026, result family 12, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 202 declarations of OpenAI's Lean: 167 definitions, 1 inductive type or structure, 10 instances and 24 theorems. The definitions and types are `Erdos970.Mertens.LogZetaInteg.c`, `Erdos970.Mertens.LogZetaInteg.f`, `OAI.JointDickman.residueEquiv`, `OAI.JointDickman.roughSieveRate`, `OAI.JointDickman.roughSieveTheta`, `OAI.JointDickman.roughTruncation`, `OAI.JointDickman.samplingDegreeEnvelope`, `OAI.JointDickman.samplingEntropyEnvelope`, `OAI.JointDickman.samplingError`, `OAI.JointDickman.samplingRateEnvelope`, `OAI.JointDickman.samplingSquareEnvelope`, `OAI.JointDickman.samplingTau`, `OAI.JointDickman.sdPolynomial`, `OAI.JointDickman.selectedPrimeSubset`, `OAI.JointDickman.shortWindowEnergy`, `OAI.JointDickman.singularSeriesTail`, `OAI.JointDickman.siteColumnResponse`, `OAI.JointDickman.smoothMixtureKernel`, `OAI.JointDickman.subsetCardWindow`, `OAI.JointDickman.subsetPartitionEquiv`, `OAI.JointDickman.supportPolynomialMap`, `OAI.JointDickman.tailSaving`, `OAI.JointDickman.tensorIntervalLower`, `OAI.JointDickman.tensorIntervalUpper`, `OAI.JointDickman.tensorParameterBox`, `OAI.JointDickman.tiltedPrimeWeight`, `OAI.JointDickman.tiltedSieveTheta`, `OAI.JointDickman.totientSquareSum`, `OAI.JointDickman.tupleDiagonal`, `OAI.JointDickman.uncorrectedPrimeProductMass`, `OAI.JointDickman.uncorrectedSubsetMass`, `OAI.JointDickman.weightedMean`, `OAI.JointDickman.zetaOpenRectangle`, `OAI.JointDickman.zetaPoleFactor`, `OAI.LargePrimeGaps.PrimePowerEq`, `OAI.LargePrimeGaps.biquadraticCoefficients`, `OAI.LargePrimeGaps.characterMean`, `OAI.LargePrimeGaps.characterRegular`, `OAI.LargePrimeGaps.discrepancyTail`, `OAI.LargePrimeGaps.positiveCoefficients` and 128 more.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `EgyptianFractions_CorrelationPhase`, `EgyptianFractions_DiscreteFirstDerivative`, `EgyptianFractions_ForwardDifference`, `EgyptianFractions_IteratedDifferencing`, `EgyptianFractions_MonotoneBlocks`, `EgyptianFractions_PhaseExtension`, `Erdos970_MertensClassical`, `Fourier`, `JointDickman_Amplification_DyadicTailSum`, `JointDickman_Amplification_FiniteStatistics`, `JointDickman_Amplification_ParameterEstimates`, `JointDickman_Amplification_SingularSeriesApproximation`, `JointDickman_Amplification_SingularSeriesTail`, `JointDickman_Amplification_SubsetPartition`, `JointDickman_Analysis_ZetaPoleFactor`, `JointDickman_Analysis_ZetaRectangleLog`, `JointDickman_Arithmetic_PrimeHarmonicWeights`, `JointDickman_Arithmetic_PrimeMassApproximation`, `JointDickman_Arithmetic_PrimeSiteBridge`, `JointDickman_Arithmetic_PrimeTupleDiagonals`, `JointDickman_Arithmetic_RoughCutoffTruncation`, `JointDickman_Arithmetic_RoughSelbergDelange`, `JointDickman_Arithmetic_SieveSingleDensity`, `JointDickman_Counting_PeriodicAverages`, `JointDickman_Counting_SamplingConcentration`, `JointDickman_Counting_SamplingRateEnvelope`, `JointDickman_Counting_SamplingTransfer`, `JointDickman_Counting_ShortWindowEnergy`, `JointDickman_Counting_SubsetWindowEntropy`, `JointDickman_Counting_TiltedCoefficient`, `JointDickman_Probability_CoarseChannel`, `JointDickman_Probability_CompactTensorApproximation`, `JointDickman_Probability_TensorBoxRegularity`, `JointDickman_Probability_UniformTensorApproximation`, `PerronFormula`, `PrimeGaps_DirichletGrowth`, `PrimeGaps_EqualityPatterns`, `PrimeGaps_PatternMoments`, `PrimeGaps_SiegelBounds`, `PrimeGaps_TaylorBounds`, `PrimeGaps_ZeroFreeBounds`, `Rectangle`, `ResidueCalcOnRectangles`, `TwoPointCorrelations_Basic`, `TwoPointCorrelations_Bonferroni`, `TwoPointCorrelations_CRTComparison`, `TwoPointCorrelations_CenterBandExpansion`, `TwoPointCorrelations_FiniteAverages`, `TwoPointCorrelations_FinitePrimePhases`, `TwoPointCorrelations_FiniteProbability`, `TwoPointCorrelations_HalaszBandPartition`, `TwoPointCorrelations_HalaszDenominatorCalculus`, `TwoPointCorrelations_HalaszDoubleMean`, `TwoPointCorrelations_HalaszFrequencyRows`, `TwoPointCorrelations_HalaszGroupedBounds`, `TwoPointCorrelations_HalaszHyperbola`, `TwoPointCorrelations_HalaszInnerApproximation`, `TwoPointCorrelations_HalaszNearDiscrepancy`, `TwoPointCorrelations_HalaszPerronWindowKernel`, `TwoPointCorrelations_HalaszPhaseCells`, `TwoPointCorrelations_HalaszPositiveLog`, `TwoPointCorrelations_HalaszPrimeConvolution`, `TwoPointCorrelations_HalaszPrimeMass`, `TwoPointCorrelations_HalaszPrimePartialSummation`, `TwoPointCorrelations_HalaszPrimePowerLogBound`, `TwoPointCorrelations_HalaszPrimePowers`, `TwoPointCorrelations_HalaszPrimeTruncation`, `TwoPointCorrelations_HalaszSmoothSeries`, `TwoPointCorrelations_HalaszTwistedMean`, `TwoPointCorrelations_HalaszUnitCorrection`, `TwoPointCorrelations_HalaszUnitEuler`, `TwoPointCorrelations_HalaszUnitRenormalization`, `TwoPointCorrelations_HalaszUnsmoothing`, `TwoPointCorrelations_LocalFactors`, `TwoPointCorrelations_MRTBoundaryMean`, `TwoPointCorrelations_MRTCoarseBins`, `TwoPointCorrelations_MRTCoarseFactorization`, `TwoPointCorrelations_MRTCoarseMean`, `TwoPointCorrelations_MRTCorrectionSummability`, `TwoPointCorrelations_MRTCountMask`, `TwoPointCorrelations_MRTCountMean`, `TwoPointCorrelations_MRTDivisorPairs`, `TwoPointCorrelations_MRTEulerProducts`, `TwoPointCorrelations_MRTFactoredReciprocal`, `TwoPointCorrelations_MRTFrequencyPartition`, `TwoPointCorrelations_MRTGeneralFactorization`, `TwoPointCorrelations_MRTGeneralPrimeError`, `TwoPointCorrelations_MRTMeanSquareKernel`, `TwoPointCorrelations_MRTMixedCoefficients`, `TwoPointCorrelations_MRTMixedThreshold`, `TwoPointCorrelations_MRTMultiplicativeReduction`, `TwoPointCorrelations_MRTPrimeMoments`, `TwoPointCorrelations_MRTPrimeSquareMean`, `TwoPointCorrelations_MRTRamareMeanError`, `TwoPointCorrelations_MRTRamareWeights`, `TwoPointCorrelations_MRTTypicalCoarse`, `TwoPointCorrelations_MRTTypicalFactors`, `TwoPointCorrelations_ModFiveContourKernel`, `TwoPointCorrelations_ModFivePerronInversion`, `TwoPointCorrelations_PretentiousDistance`, `TwoPointCorrelations_PrimePartialSummation`, `TwoPointCorrelations_ResidueBox`, `TwoPointCorrelations_ResidueCounts`, `TwoPointCorrelations_ResidueSampling`, `TwoPointCorrelations_RoughShiftBoundary`, `TwoPointCorrelations_SieveModel`, `ZetaBounds`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ083J003`; the statements `OAI_JointDickman_auxiliary_power_energy`, `OAI.JointDickman.auxiliary_power_energy_jd`, `OAI_JointDickman_bin_auxiliary_cofactor`, `OAI.JointDickman.bin_auxiliary_cofactor_jd`, `OAI_JointDickman_bounded_box_coarse_comparison`, `OAI.JointDickman.bounded_box_coarse_comparison_jd`, `OAI_JointDickman_canonical_full_energy`, `OAI.JointDickman.canonical_full_energy_jd`, `OAI_JointDickman_characterPerron_estimate`, `OAI.JointDickman.characterPerron_estimate_jd`, `OAI_JointDickman_counting_sampling`, `OAI_JointDickman_counting_sampling_actual_scale`, `OAI.JointDickman.counting_sampling_actual_scale_jd`, `OAI.JointDickman.counting_sampling_jd`, `OAI_JointDickman_finite_graph_arithmetic_fluctuation`, `OAI.JointDickman.finite_graph_arithmetic_fluctuation_jd`, `OAI_JointDickman_finite_graph_centered_mean_proved`, `OAI.JointDickman.finite_graph_centered_mean_proved_jd`, `OAI_JointDickman_finite_ramp_approximation`, `OAI.JointDickman.finite_ramp_approximation_jd`, `OAI_JointDickman_high_frequency_count_window`, `OAI.JointDickman.high_frequency_count_window_jd`, `OAI_JointDickman_masked_arithmetic_fluctuation_bound`, `OAI.JointDickman.masked_arithmetic_fluctuation_bound_jd`, `OAI_JointDickman_ramare_product_sparse_integral`, `OAI.JointDickman.ramare_product_sparse_integral_jd`, `OAI_TwoPointCorrelations_halasz_prime_window_middle` and `OAI.TwoPointCorrelations.halasz_prime_window_middle_jd`; the proofs of `OAI_JointDickman_characterDistanceDivergence`, `OAI.JointDickman.characterDistanceDivergence_jd`, `OAI_JointDickman_character_agreement_distance_polynomial`, `OAI.JointDickman.character_agreement_distance_polynomial_jd`, `OAI_JointDickman_finiteBinDistributionInput`, `OAI.JointDickman.finiteBinDistributionInput_jd`, `OAI_JointDickman_mellin_prime_sampling_arithmetic`, `OAI.JointDickman.mellin_prime_sampling_arithmetic_jd`, `OAI_JointDickman_primeProductMertensInput`, `OAI.JointDickman.primeProductMertensInput_jd`, `OAI_JointDickman_prime_agreement_distance_polynomial`, `OAI.JointDickman.prime_agreement_distance_polynomial_jd`, `OAI_JointDickman_ramare_product_sparse_integral` and `OAI.JointDickman.ramare_product_sparse_integral_jd`.
-- source:
--   OpenAI, The joint Dickman law for consecutive integers, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 12; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-joint-Dickman-law-for-consecutive-integers-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 7ef5c0c

import Mathlib
import Batteries.Tactic.Lemma

section
-- module Solutions.OAIQ083_JD.Compat
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
/-- `simp` closes `2 ≤ ∞` in `WithTop ℕ∞` (the smoothness order) in Mathlib d13f23b; ours has the
lemma only for `1` and casts (AffineBernstein, `isSymmSndFDerivAt (by simp)`, 2026-10-26). -/
@[simp]
theorem ofNat_le_infty (n : ℕ) [n.AtLeastTwo] : (no_index (OfNat.ofNat n) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
  ENat.LEInfty.out
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
in d13f23b (Kadison similarity, oaiq-075). A def, made a local instance by the port only in modules naming
`CommCStarAlgebra` or `IsMulCommutative` (`oaiport.comm_cstar_line`): as a global instance it made `whnf` time out in
FactorGeneration modules with their own `CStarAlgebra` instances on a subalgebra (oaiq-122). -/
@[reducible]
noncomputable def starSubalgebraCommCStarAlgebra {B : Type*} [CStarAlgebra B] (A : StarSubalgebra ℂ B)
    [IsClosed (A : Set B)] [IsMulCommutative A] : CommCStarAlgebra A :=
  { StarSubalgebra.cstarAlgebra A with
    mul_comm := fun a b => IsMulCommutative.is_comm.comm a b }
/-- Mathlib d13f23b's `MeasurableSpace Circle` (Mathlib.MeasureTheory.Group.Circle): the subtype structure. A def,
turned on as a local instance in the modules that use the characters `𝐞`/`fourierChar`/`probChar` (q141). -/
@[reducible] def circleMeasurableSpace : MeasurableSpace Circle :=
  inferInstanceAs <| MeasurableSpace <| Subtype (· ∈ Submonoid.unitSphere ℂ)
/-- d13f23b's `BorelSpace Circle`, for `circleMeasurableSpace`. -/
theorem circleBorelSpace : @BorelSpace Circle _ circleMeasurableSpace :=
  inferInstanceAs <| BorelSpace <| Subtype (· ∈ Metric.sphere (0 : ℂ) 1)
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ083_JD.EgyptianFractions_ForwardDifference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open Set
open scoped ContDiff Topology

namespace Problem337

/-- Iterated forward differences, with the shifts in list order. -/
def forwardDifference : List ℝ → (ℝ → ℝ) → ℝ → ℝ
  | [], f => f
  | h :: hs, f => fun x => forwardDifference hs f (x + h) - forwardDifference hs f x

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ083_JD.EgyptianFractions_IteratedDifferencing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
open ComplexConjugate
namespace Problem337

/-- A single multiplicative difference of a complex sequence. -/
def correlationShift (a : ℤ → ℂ) (h : ℤ) : ℤ → ℂ :=
  fun n => a (n + h) * conj (a n)

/-- Successive multiplicative differences, in their order of application. -/
def iteratedCorrelation (a : ℤ → ℂ) : List ℤ → ℤ → ℂ
  | [] => a
  | h :: hs => iteratedCorrelation (correlationShift a h) hs

/-- The elementary square-root budget obtained from repeated differencing. -/
def differencingBudget (H : ℕ) : ℕ → ℝ → ℝ
  | 0, B => B
  | r + 1, B => Real.sqrt (2 / (H : ℝ) + 2 * differencingBudget H r B)

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ083_JD.EgyptianFractions_CorrelationPhase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
open ComplexConjugate
namespace Problem337

/-- The unit complex phase with frequency one. -/
def differencingPhase (x : ℝ) : ℂ :=
  Complex.exp ((2 * Real.pi * x : ℝ) * Complex.I)

@[simp] theorem differencingPhase_norm (x : ℝ) : ‖differencingPhase x‖ = 1 := by
  simp [differencingPhase, Complex.norm_exp]

/-- A phase sequence with zero extension outside a closed integer interval. -/
def intervalPhase (f : ℝ → ℝ) (L U : ℤ) : ℤ → ℂ :=
  fun n => if L ≤ n ∧ n ≤ U then differencingPhase (f n) else 0

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ083_JD.EgyptianFractions_DiscreteFirstDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped BigOperators

namespace Problem337.ExponentialSum

noncomputable def phase (x : ℝ) : ℂ := Complex.exp ((2 * Real.pi * x : ℝ) * Complex.I)

noncomputable def phaseWeight (x : ℝ) : ℂ :=
  -(1 : ℂ) / 2 - (Real.cot (Real.pi * x) : ℂ) * Complex.I / 2

end Problem337.ExponentialSum

end OAI
end

section
-- module Solutions.OAIQ083_JD.EgyptianFractions_MonotoneBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped BigOperators

namespace Problem337

/-- Good derivative indices in the integer cell labelled by `k`. -/
noncomputable def phaseGoodBlock (d : ℕ → ℝ) (N : ℕ) (β : ℝ) (k : ℤ) : Finset ℕ := by
  classical
  exact (Finset.range N).filter (fun j => (k : ℝ) + β ≤ d j ∧ d j ≤ (k : ℝ) + 1 - β)

noncomputable def nearIntegerIndices (d : ℕ → ℝ) (N : ℕ) (β : ℝ) : Finset ℕ := by
  classical
  exact (Finset.range N).filter (fun j => ∃ k : ℤ, |d j - (k : ℝ)| < β)

end Problem337

end OAI
end

section
-- module Solutions.OAIQ083_JD.EgyptianFractions_PhaseExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337

/-- Extend a finite phase by keeping its final increment constant. -/
def affineTailPhase (f : ℕ → ℝ) (N n : ℕ) : ℝ :=
  f 0 + ∑ j ∈ Finset.range n,
    (f (min j (N - 1) + 1) - f (min j (N - 1)))

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ083_JD.Erdos970_MertensClassical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Erdos970

namespace Mertens

open _root_.Real _root_.Finset _root_.Filter _root_.Asymptotics _root_.Topology
open _root_.ArithmeticFunction hiding log

attribute [fun_prop] measurable_from_top

section
open _root_.MeasureTheory _root_.Set

namespace LogZetaInteg

noncomputable def c (d : ℕ) : ℝ := Λ d / (d * Real.log d)

noncomputable def f (s : ℝ) (d : ℕ) (x : ℝ) : ℝ :=
    c d * (Set.Ici (d:ℝ)).indicator (fun x => x ^ (-s)) x

@[simp] lemma c_zero : c 0 = 0 := by simp [c]
@[simp] lemma c_one : c 1 = 0 := by simp [c, vonMangoldt_apply_one]

end LogZetaInteg
end

end Mertens

end Erdos970
end

section
-- module Solutions.OAIQ083_JD.Fourier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.circleMeasurableSpace OAI.circleBorelSpace

open FourierTransform Real Complex MeasureTheory Filter Topology BoundedContinuousFunction
  SchwartzMap VectorFourier BigOperators

section lemmas

local instance instCoeForallRealForallComplex_solutions_rbc3bf4_1 {E : Type*} : Coe (E → ℝ) (E → ℂ) := ⟨fun f n => f n⟩
@[simp]
theorem nnnorm_eq_of_mem_circle (z : Circle) : ‖z.val‖₊ = 1 :=
  NNReal.coe_eq_one.mp (by simp [Circle.norm_coe])

@[simp]
theorem nnnorm_circle_smul (z : Circle) (s : ℂ) : ‖z • s‖₊ = ‖s‖₊ := by
  simp [show z • s = z.val * s from rfl]

end lemmas
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ParameterEstimates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Compatible parameters and elementary asymptotics

The strict inequalities here are the weight margins of `arithmetic.tex`.
The subsequent limits account for the sampling entropy and the logarithmic
factors in the prime cutoff and amplification parameters.
-/

namespace JointDickman

open Filter Asymptotics
open scoped Topology

/-- One concrete choice satisfying all three weight margins. -/
noncomputable def samplingTau : ℝ := 1 / 1000

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeMassApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Removing the local odds correction from prime-product masses

For every event, the independent-subset mass differs from the uncorrected
Euler weight by at most the sum of squared selection probabilities.
The resulting prime-tail error is uniform over events.
-/

namespace JointDickman

open Finset

noncomputable def uncorrectedSubsetMass (P : Finset ℕ) (q : ℕ → ℝ) (S : Finset ℕ) : ℝ :=
  (∏ p ∈ P, (1 - q p)) * ∏ p ∈ S, q p

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeHarmonicWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact harmonic weights of squarefree prime products

The uncorrected independent-prime mass is the harmonic rough coefficient,
including the empty product. This identifies the weight used in partial summation.
-/

namespace JointDickman

open Finset ArithmeticFunction

noncomputable def uncorrectedPrimeProductMass (P : Finset ℕ) (z : ℝ) (n : ℕ) : ℝ :=
  ∑ S ∈ P.powerset, if (∏ p ∈ S, p) = n then
    uncorrectedSubsetMass P (fun p => z / p) S else 0

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RoughSelbergDelange
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Applying the published expansion inside the roughness convolution

The expansion is inserted only below the truncation, where its endpoint
and logarithmic hypotheses hold. The complementary terms remain the
actual convolution tail, already controlled by Rankin's bound.
-/

namespace JointDickman

open Finset

noncomputable def sdPolynomial (c : ℕ → ℝ) (z : ℝ) (H : ℕ) (L : ℝ) : ℝ :=
  ∑ j ∈ range (H + 1), c j * L ^ (z - 1 - j)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RoughCutoffTruncation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Choosing the roughness truncation

An integer square-root truncation turns the remaining Rankin error into
an explicit exponential in the endpoint logarithm.
-/

namespace JointDickman

open Finset Filter
open scoped Topology

noncomputable def roughTruncation (Y : ℝ) : ℕ := ⌊Real.exp (Real.log Y / 2)⌋₊

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SieveSingleDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The single-form Euler product at the roughness cutoff -/

namespace JointDickman

open Filter Finset
open scoped Topology

noncomputable def roughSieveTheta (P p : ℕ) : ℝ := if p ≤ P then 0 else 1 / 2

noncomputable def roughSieveRate (P p : ℕ) : ℝ := (1 - roughSieveTheta P p) / p

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_PeriodicAverages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite periodic averages and coprime residue factorization

Integer averages of a function on `ZMod q` converge to its uniform residue
mean. The proof is the exact complete-block/remainder identity. The Chinese
remainder equivalence then gives factorization for fixed coprime moduli.
-/

namespace JointDickman

open Filter
open scoped Topology BigOperators

def residueEquiv (q : ℕ) [NeZero q] : Fin q ≃ ZMod q where
  toFun i := (i.val : ZMod q)
  invFun a := ⟨a.val, ZMod.val_lt a⟩
  left_inv i := by ext; exact ZMod.val_natCast_of_lt i.isLt
  right_inv a := ZMod.natCast_zmod_val a

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_DyadicTailSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Summing the lower-tail Chernoff bounds over dyadic endpoints -/

namespace JointDickman

open Finset

noncomputable def tailSaving : ℝ := (1 / 2 : ℝ) * (1 - Real.exp (-(1 / 10 : ℝ))) - (2 / 5 : ℝ) * (1 / 10)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_FiniteStatistics
attribute [-simp] _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite character tests determine joint statistics

This is the finite Fourier inversion step in `sections/distribution.tex`.
It is an algebraic transfer lemma, not an assumed arithmetic decorrelation
result. The arithmetic correlation limits still have to be established.
-/

open Filter Finset Module
open scoped Topology

namespace JointDickman

/-- A finite weighted mean, as a linear statistic. -/
noncomputable def weightedMean {G : Type*} [Fintype G] (μ : G → ℂ) :
    (G → ℂ) →ₗ[ℂ] ℂ where
  toFun f := ∑ a, μ a * f a
  map_add' f g := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c f := by simp [Finset.mul_sum, mul_left_comm]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_SingularSeriesTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A lag-independent error for the truncated singular series -/

namespace JointDickman
open Finset Filter
open scoped Topology

noncomputable def singularSeriesTail (Q : ℕ) : ℝ :=
  ∑' k : ℕ, 1/((k+Q).totient : ℝ)^2

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_SingularSeriesApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Periodic approximation of the singular series in arithmetic mean -/
namespace JointDickman
open Finset Filter Classical
open scoped Topology

noncomputable def totientSquareSum : ℝ := ∑' q : ℕ, 1/(q.totient : ℝ)^2

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_SubsetPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact splitting of independent prime choices into two ranges -/

namespace JointDickman

open Finset

noncomputable def subsetPartitionEquiv {α : Type*} [DecidableEq α]
    (P Q : Finset α) (hd : Disjoint P Q) :
    (P ∪ Q).powerset ≃ P.powerset × Q.powerset where
  toFun S := (⟨S.val ∩ P, mem_powerset.mpr inter_subset_right⟩,
    ⟨S.val ∩ Q, mem_powerset.mpr inter_subset_right⟩)
  invFun AB := ⟨AB.1.val ∪ AB.2.val, mem_powerset.mpr
    (union_subset_union (mem_powerset.mp AB.1.property) (mem_powerset.mp AB.2.property))⟩
  left_inv S := by
    apply Subtype.ext
    ext p
    have hs := mem_powerset.mp S.property
    simp only [mem_union, mem_inter]
    constructor
    · tauto
    · intro hp
      exact (mem_union.mp (hs hp)).elim (fun h => Or.inl ⟨hp, h⟩) (fun h => Or.inr ⟨hp, h⟩)
  right_inv AB := by
    apply Prod.ext <;> apply Subtype.ext <;> ext p
    · have ha := mem_powerset.mp AB.1.property
      have hb := mem_powerset.mp AB.2.property
      simp only [mem_union, mem_inter]
      constructor
      · rintro ⟨hp | hp, hP⟩
        · exact hp
        · exact False.elim (disjoint_left.mp hd hP (hb hp))
      · intro hp
        exact ⟨Or.inl hp, ha hp⟩
    · have ha := mem_powerset.mp AB.1.property
      have hb := mem_powerset.mp AB.2.property
      simp only [mem_union, mem_inter]
      constructor
      · rintro ⟨hp | hp, hQ⟩
        · exact False.elim (disjoint_left.mp hd (ha hp) hQ)
        · exact hp
      · intro hp
        exact ⟨Or.inr hp, hb hp⟩

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_ZetaPoleFactor
attribute [-simp] _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing the simple pole of zeta at one -/
namespace JointDickman
open Filter
open scoped Topology

noncomputable def zetaPoleFactor (s : ℂ) : ℂ :=
  if s = 1 then 1 else (s-1)*riemannZeta s

@[simp] theorem zetaPoleFactor_one : zetaPoleFactor 1 = 1 := by simp [zetaPoleFactor]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.Rectangle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open Complex Set Topology

open scoped Interval

variable {z w : ℂ} {c : ℝ}


/-- A `RectangleBorder` has corners `z` and `w`. -/
def RectangleBorder (z w : ℂ) : Set ℂ :=
  [[z.re, w.re]] ×ℂ {z.im} ∪ {z.re} ×ℂ [[z.im, w.im]] ∪
    [[z.re, w.re]] ×ℂ {w.im} ∪ {w.re} ×ℂ [[z.im, w.im]]

def Square (p : ℂ) (c : ℝ) : Set ℂ := Rectangle (-c - c * I + p) (c + c * I + p)
end

section
-- module Solutions.OAIQ083_JD.ResidueCalcOnRectangles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open Complex BigOperators Nat Classical Real Topology Filter
open Set MeasureTheory intervalIntegral Asymptotics

open scoped Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : ℂ → E} {z w p c A : ℂ}
  {x x₁ x₂ y y₁ y₂ σ : ℝ}

noncomputable def VIntegral (f : ℂ → E) (x y₁ y₂ : ℝ) : E :=
    I • ∫ y in y₁..y₂, f (x + y * I)

noncomputable def VerticalIntegral (f : ℂ → E) (σ : ℝ) : E :=
    I • ∫ t : ℝ, f (σ + t * I)

noncomputable abbrev VerticalIntegral' (f : ℂ → E) (σ : ℝ) : E :=
    (1 / (2 * π * I)) • VerticalIntegral f σ

def RectangleBorderIntegrable (f : ℂ → E) (z w : ℂ) : Prop :=
    IntervalIntegrable (fun x => f (x + z.im * I)) volume z.re w.re ∧
    IntervalIntegrable (fun x => f (x + w.im * I)) volume z.re w.re ∧
    IntervalIntegrable (fun y => f (w.re + y * I)) volume z.im w.im ∧
    IntervalIntegrable (fun y => f (z.re + y * I)) volume z.im w.im

/-! ## Residue calculus: residues, simple poles, and the rectangle residue theorem

The simple-pole `residue`, `sumResiduesIn`, the `HasSimplePolesOn` scaffold, and the rectangle
residue theorem `RectangleIntegral'_eq_sumResiduesIn`. Extracted from `CH2.lean` as general,
reusable contour-integration lemmas (see issue #1537). -/
end

section
-- module Solutions.OAIQ083_JD.ZetaBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


open Complex Topology Filter Interval Set Asymptotics

local notation (name := riemannzeta) "ζ" => riemannZeta

noncomputable def riemannZeta0 (N : ℕ) (s : ℂ) : ℂ :=
  (∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s) +
  (- N ^ (1 - s)) / (1 - s) + (- N ^ (-s)) / 2
      + s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)

noncomputable def ζ₀' (N : ℕ) (s : ℂ) : ℂ :=
    ∑ n ∈ Finset.range (N + 1), -1 / (n : ℂ) ^ s * Real.log n +
    (-N ^ (1 - s) / (1 - s) ^ 2 + Real.log N * N ^ (1 - s) / (1 - s)) +
    Real.log N * N ^ (-s) / 2 +
    (1 * (∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (- s - 1)) +
    s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (- s - 1) * (- Real.log x))


def ZetaZeroFreeGenProp (n : ℝ) : Prop := ∃ (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2)),
    ∀ (σ : ℝ) (t : ℝ) (_ : 3 < |t|) (_ : σ ∈ Ico (1 - A / (Real.log |t|) ^ n) 1),
    ζ (σ + t * I) ≠ 0

open ArithmeticFunction (vonMangoldt)
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_ZetaRectangleLog
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Normalized logarithms on the finite zero-free rectangles -/
namespace JointDickman
open Set

def zetaOpenRectangle (δ T : ℝ) : Set ℂ :=
  (Complex.re ⁻¹' Ioo (1-δ) 2) ∩ (Complex.im ⁻¹' Ioo (-T) T)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeSiteBridge
attribute [-simp] _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact equivalence of prime-site and prime-subset probabilities -/

namespace JointDickman

open Finset

noncomputable def selectedPrimeSubset (Q : Finset ℕ) (x : Q → Bool) : Finset ℕ :=
  Q.filter (fun p => if hp : p ∈ Q then x ⟨p, hp⟩ = true else False)

@[simp] theorem selectedPrimeSubset_mem (Q : Finset ℕ) (x : Q → Bool) (p : Q) :
    p.val ∈ selectedPrimeSubset Q x ↔ x p = true := by
  simp [selectedPrimeSubset, p.property]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeTupleDiagonals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Repeated-prime tuples have vanishing reciprocal weight -/
namespace JointDickman
open Finset Filter MeasureTheory
open scoped Topology NNReal ENNReal

noncomputable def tupleDiagonal (n : ℕ) : Set (Fin n → ℝ) :=
  {t | ¬Function.Injective t}

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_SamplingConcentration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Concentration after restriction to a common good event

The extension used in the manuscript's sampling argument is constructed
explicitly from a finite good set. The only concentration hypothesis below
is the uniform-constant finite-product specialization of McDiarmid's
published bounded-differences inequality.
-/

open Finset
open scoped BigOperators

namespace JointDickman

section SparseKernel

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable {A : Type*} [DecidableEq A]

/-- The unnormalized residual column response for fixed single-site tests. -/
noncomputable def siteColumnResponse (E : ι → ι → A → A → ℝ)
    (g : ι → A → ℝ) (x : ι → A) : ℝ :=
  ∑ j, |∑ i, E i j (x i) (x j) * g i (x i)|

end SparseKernel

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_SamplingTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Quantitative finite sampling transfer

The finite family consists of sampled column sequences and one sign per
sampled occurrence. Its cardinal is `(2 * N)^m`, including repeated columns.
The common bad event is paid once. Moment and tail obligations are explicit
mathematical hypotheses, not additional published inputs.
-/

open Finset
open scoped BigOperators

namespace JointDickman

section CutFamily

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def samplingError (d Q : ℝ) (m : ℕ) : ℝ :=
  (2 * Real.sqrt ((Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) / m * Q)) +
    2 * m * d) / Fintype.card ι

end CutFamily

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_SamplingRateEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A vanishing error envelope for the adaptive cut comparison -/

namespace JointDickman
open Filter
open scoped Topology

noncomputable def samplingDegreeEnvelope (U q K B : ℝ) : ℝ :=
  (4*U*q/K^2)*(B^(0.11 : ℝ)/B^(0.14 : ℝ))

noncomputable def samplingSquareEnvelope (q B : ℝ) : ℝ :=
  q*(B^(0.20 : ℝ)/B^(0.21 : ℝ))

noncomputable def samplingEntropyEnvelope (c K a B : ℝ) : ℝ :=
  Real.exp (2*(B^(0.14 : ℝ)*Real.log B) - (a^2*c/(8*K^2))*B^(0.18 : ℝ))

noncomputable def samplingRateEnvelope (C q c U K a B : ℝ) : ℝ :=
  2*Real.sqrt (U*(B^(0.12 : ℝ)/B^(0.14 : ℝ))) +
    (4*K/c)*(B^(0.21 : ℝ)/B^(0.32 : ℝ)) +
    Real.sqrt ((C^2+q*B^(-0.21 : ℝ))*(samplingDegreeEnvelope U q K B +
      samplingSquareEnvelope q B + samplingEntropyEnvelope c K a B))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_ShortWindowEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Mean-square control of short windows by a nonnegative long mean -/
namespace JointDickman
open Finset Filter MeasureTheory Classical

noncomputable def shortWindowEnergy (E : ℕ → ℝ) (H : ℝ) (N : ℕ) (z : ℝ) : ℝ :=
  ∑ n ∈ range N, (Set.Ico ((n : ℝ)-H) n).indicator (fun _ => E n) z

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_SubsetWindowEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Counting omission subsets in a regularity window -/

namespace JointDickman
open Finset Classical

noncomputable def subsetCardWindow (P : Finset ℕ) (ℓ g r τ : ℝ) : Finset (Finset ℕ) :=
  P.powerset.filter (fun A => |(A.card : ℝ)/ℓ-g*r| ≤ 3*τ)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_TiltedCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exponential prime-count tilts of the actual coefficient -/

namespace JointDickman

open Finset

noncomputable def tiltedPrimeWeight (Q : Finset ℕ) (s : ℝ) (p : ℕ) : ℝ :=
  if p ∈ Q then (1 / 2 : ℝ) * Real.exp s else 1 / 2

noncomputable def tiltedSieveTheta (P : ℕ) (Q : Finset ℕ) (s : ℝ) (p : ℕ) : ℝ :=
  if p ≤ P then 0 else tiltedPrimeWeight Q s p

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_CoarseChannel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Coarse centering of a smooth mixture kernel

A bounded Lipschitz profile changes little inside each coarse cell. Its
common-variable mixture is consequently close to a kernel depending only
on the coarse indices. Combining this fact with a discarded row bound
gives the finite coarse-channel estimate.
-/

namespace JointDickman

open scoped BigOperators NNReal

noncomputable def smoothMixtureKernel {C A : Type*} [Fintype C]
    (w : C → ℝ) (f : C → ℝ → ℝ) (location : A → ℝ) (a b : A) : ℝ :=
  ∑ c, w c * f c (location a) * f c (location b)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_CompactTensorApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite tensor approximation on the four-variable smooth support -/

namespace JointDickman
open scoped Topology

noncomputable def supportPolynomialMap (K : Set (Fin 4 → ℝ)) :
    MvPolynomial (Fin 4) ℝ →ₐ[ℝ] C(K,ℝ) :=
  MvPolynomial.aeval (fun i => ⟨fun x => (x : Fin 4 → ℝ) i,
    (continuous_apply i).comp continuous_subtype_val⟩)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_UniformTensorApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform tensor approximation with its positive arithmetic error measure -/

namespace JointDickman
open Finset
open scoped Topology

def tensorParameterBox : Set (Fin 4 → ℝ) :=
  Set.Icc ![1/4,1/4,1/4,-3] ![17/4,17/4,17/4,3]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_TensorBoxRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Published regularity loss on the actual compact tensor boxes -/

namespace JointDickman
open Finset Filter
open scoped Topology

noncomputable def tensorIntervalLower (X : ℝ) : ℕ := ⌊(1/4 : ℝ)*X⌋₊+1
noncomputable def tensorIntervalUpper (X : ℝ) : ℕ := ⌊(17/4 : ℝ)*X⌋₊+1

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.PerronFormula
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


open Asymptotics Complex ComplexConjugate Topology Filter Real MeasureTheory Set

open scoped Interval



/- TODO: move to general section. -/

namespace Perron

variable {x σ σ' σ'' T : ℝ}

noncomputable abbrev f (x : ℝ) := fun (s : ℂ) ↦ x ^ s / (s * (s + 1))



end Perron
end

section
-- module Solutions.OAIQ083_JD.PrimeGaps_EqualityPatterns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

noncomputable instance finiteSetoidFintype (ι : Type*) [Fintype ι] : Fintype (Setoid ι) :=
  Fintype.ofInjective (fun r : Setoid ι => r.r) (fun _ _ h => Setoid.ext (by intro i j; exact Iff.of_eq (congrFun (congrFun h i) j)))

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIQ083_JD.PrimeGaps_PatternMoments
attribute [-simp] _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

@[simp] theorem append_ker_left {n p : ℕ} {α : Type*}
    (b : Fin n → α) (c : Fin p → α) :
    Setoid.comap (Fin.castAdd p) (Setoid.ker (Fin.append b c))=Setoid.ker b := by
  apply Setoid.ext
  intro i j
  change Fin.append b c (i.castAdd p)=Fin.append b c (j.castAdd p) ↔ b i=b j
  simp only [Fin.append_left]

@[simp] theorem append_ker_right {n p : ℕ} {α : Type*}
    (b : Fin n → α) (c : Fin p → α) :
    Setoid.comap (Fin.natAdd n) (Setoid.ker (Fin.append b c))=Setoid.ker c := by
  apply Setoid.ext
  intro i j
  change Fin.append b c (i.natAdd n)=Fin.append b c (j.natAdd n) ↔ c i=c j
  simp only [Fin.append_right]

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIQ083_JD.PrimeGaps_DirichletGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

open scoped ComplexConjugate

open Filter Topology

open Complex Filter Topology

open Complex Filter Topology Set MeasureTheory Asymptotics

noncomputable def discrepancyTail (A : ℝ → ℂ) (u : ℝ) (s : ℂ) : ℂ :=
  ∫ t in Ioi u, A t * (t:ℂ)^(-(s+1))

open Finset

noncomputable def seriesDiscrepancy (f : ℕ → ℂ) (c : ℂ) (t : ℝ) : ℂ :=
  (∑ n ∈ Icc 1 ⌊t⌋₊, f n) - c*t

noncomputable def regularSeries (f : ℕ → ℂ) (c : ℂ) (s : ℂ) : ℂ :=
  c+s*discrepancyTail (seriesDiscrepancy f c) 1 s

def positiveCoefficients (f : ℕ → ℂ) (n : ℕ) : ℂ := if n = 0 then 0 else f n

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIQ083_JD.PrimeGaps_TaylorBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

open scoped ComplexConjugate

open Filter Topology

open Complex Filter Topology

open Complex Filter Topology Set MeasureTheory Asymptotics

open Finset

open Complex Filter Topology Finset

noncomputable def signedTaylorCoeff (H : ℂ → ℂ) (n : ℕ) : ℝ :=
  (((-1:ℂ)^n)*(n.factorial:ℂ)⁻¹*iteratedDeriv n H 2).re

open Complex Filter Topology Finset Set MeasureTheory

noncomputable def zetaRegular : ℂ → ℂ :=
  regularSeries (positiveCoefficients (fun _ => 1)) 1

noncomputable def regularizedZetaProduct (P : ℂ → ℂ) (s : ℂ) : ℂ :=
  zetaRegular s*P s+dslope P 1 s

open Complex Finset ArithmeticFunction

open scoped ComplexOrder

def PrimePowerEq (p : ℕ) (f g : ArithmeticFunction ℂ) : Prop :=
  ∀ k : ℕ, f (p^k) = g (p^k)

noncomputable def biquadraticCoefficients {q r : ℕ}
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) : ArithmeticFunction ℂ :=
  ArithmeticFunction.zeta * toArithmeticFunction (χ ·) * toArithmeticFunction (ψ ·) *
    (toArithmeticFunction (χ ·)).pmul (toArithmeticFunction (ψ ·))

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIQ083_JD.PrimeGaps_SiegelBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

section

open Complex Finset ArithmeticFunction

noncomputable def productCharacter {q r : ℕ} (χ : DirichletCharacter ℂ q)
    (ψ : DirichletCharacter ℂ r) : DirichletCharacter ℂ (q*r) :=
  χ.changeLevel (dvd_mul_right q r) * ψ.changeLevel (dvd_mul_left r q)

end

open Complex Filter Topology Set MeasureTheory Finset ArithmeticFunction

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIQ083_JD.PrimeGaps_ZeroFreeBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

section

open Complex Filter Topology Set MeasureTheory Finset

noncomputable def characterMean {q : ℕ} (χ : DirichletCharacter ℂ q) : ℂ :=
  (∑ n∈range q,χ (n : ZMod q))/(q:ℂ)

noncomputable def characterRegular {q : ℕ} (χ : DirichletCharacter ℂ q) : ℂ → ℂ :=
  regularSeries (positiveCoefficients (fun n => χ (n : ZMod q))) (characterMean χ)

end

open Complex Filter Topology Finset

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_Basic
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Ordinary two-point correlations: concrete sums and affine transfer

Definitions follow the introduction of the supplied manuscript
*Ordinary two-point correlations of multiplicative functions* (September 24, 2026).
The exact Liouville identities below are the algebraic part of §8.
No cancellation estimate is assumed or asserted here.
-/

open scoped BigOperators

namespace TwoPointCorrelations

/-- Ordinary multiplicativity is required only for coprime positive arguments;
this also permits the identically zero function, as does the manuscript. -/
def Multiplicative (f : ℕ → ℂ) : Prop :=
  ∀ m n : ℕ, 0 < m → 0 < n → m.Coprime n → f (m * n) = f m * f n

def OneBounded (f : ℕ → ℂ) : Prop := ∀ n : ℕ, 0 < n → ‖f n‖ ≤ 1

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_FiniteProbability
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite weighted sampling for the random-prime rank argument

The prime labels in the rank argument have a nonuniform reciprocal law.
Finite-sum probability identities describe the resulting sampling law.
-/

namespace TwoPointCorrelations

open Finset

structure FiniteLaw (α : Type*) [Fintype α] where
  weight : α → ℝ
  nonneg : ∀ x, 0 ≤ weight x
  total : ∑ x, weight x = 1

namespace FiniteLaw

variable {α β ι : Type*} [Fintype α] [Fintype β] [Fintype ι]

noncomputable def average (μ : FiniteLaw α) (f : α → ℝ) : ℝ :=
  ∑ x, μ.weight x * f x

noncomputable def probability (μ : FiniteLaw α) (E : α → Prop) : ℝ := by
  classical
  exact μ.average (fun x => if E x then 1 else 0)

@[simp] lemma average_const (μ : FiniteLaw α) (c : ℝ) : μ.average (fun _ => c) = c := by
  simp [average, ← sum_mul, μ.total]

end FiniteLaw

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_Bonferroni
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite even-order sieve, before any independence or prime estimates. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

def avoidsEvents {ι α : Type*} (P : Finset ι) (E : ι → α → Prop) (x : α) : Prop :=
  ∀ i ∈ P, ¬E i x

def eventIntersection {ι α : Type*} (E : ι → α → Prop) (S : Finset ι) (x : α) : Prop :=
  ∀ i ∈ S, E i x

noncomputable def eventIntersectionCount {ι α : Type*}
    (P : Finset ι) (E : ι → α → Prop) (j : ℕ) (x : α) : ℝ :=
  ∑ S ∈ P.powersetCard j, if eventIntersection E S x then 1 else 0

noncomputable def truncatedEventCount {ι α : Type*}
    (P : Finset ι) (E : ι → α → Prop) (r : ℕ) (x : α) : ℝ :=
  ∑ j ∈ range (r + 1), (-1 : ℝ) ^ j * eventIntersectionCount P E j x

noncomputable def eventIntersectionMass {ι α : Type*} [Fintype α]
    (μ : FiniteLaw α) (P : Finset ι) (E : ι → α → Prop) (j : ℕ) : ℝ :=
  ∑ S ∈ P.powersetCard j, μ.probability (eventIntersection E S)

noncomputable def truncatedEventMass {ι α : Type*} [Fintype α]
    (μ : FiniteLaw α) (P : Finset ι) (E : ι → α → Prop) (r : ℕ) : ℝ :=
  ∑ j ∈ range (r + 1), (-1 : ℝ) ^ j * eventIntersectionMass μ P E j

/-- Total error in the finitely many intersection counts used by a sieve
truncation. Each subset appears just once. -/
noncomputable def sieveIntersectionError {ι : Type*}
    (P : Finset ι) (err : Finset ι → ℝ) (r : ℕ) : ℝ :=
  ∑ j ∈ range (r + 1), ∑ S ∈ P.powersetCard j, err S

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_ResidueCounts
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Residue counts on arbitrary finite consecutive intervals

An interval is represented by its starting residue `A` and its length `N`.
Thus this includes arbitrary translates, including intervals starting at
negative integers. We prove the exact quotient-and-remainder count, the
one-count discrepancy, and the total-variation estimate used by the finite
residue comparison in the manuscript.
-/

namespace TwoPointCorrelations

open Finset

/-- Number of offsets `0 ≤ j < N` whose translated residue equals `r`. -/
def residueCount {D : ℕ} [NeZero D] (A : ZMod D) (N : ℕ) (r : ZMod D) : ℕ :=
  ∑ j ∈ Finset.range N, if A + (j : ZMod D) = r then 1 else 0

/-- The residue law of a uniformly selected origin from an interval. -/
noncomputable def residueProbability {D : ℕ} [NeZero D] (A : ZMod D)
    (N : ℕ) (r : ZMod D) : ℝ := (residueCount A N r : ℝ) / N

lemma residueCount_sum {D : ℕ} [NeZero D] (A : ZMod D) (N : ℕ) :
    ∑ r : ZMod D, residueCount A N r = N := by
  unfold residueCount
  rw [Finset.sum_comm]
  simp

lemma residueProbability_sum {D : ℕ} [NeZero D] (A : ZMod D) (N : ℕ) (hN : 0 < N) :
    ∑ r : ZMod D, residueProbability A N r = 1 := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  simp only [residueProbability, ← Finset.sum_div, ← Nat.cast_sum, residueCount_sum]
  exact div_self hN'

/-- Half the ℓ¹ difference from the uniform residue law. -/
noncomputable def residueTotalVariation {D : ℕ} [NeZero D] (A : ZMod D) (N : ℕ) : ℝ :=
  (∑ r : ZMod D, |residueProbability A N r - 1 / (D : ℝ)|) / 2

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_CRTComparison
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite CRT marginals and contraction under independent randomization

A selected finite set of pairwise coprime residue coordinates has the law
of one residue modulo their product. The exact interval count from
`ResidueCounts` gives total variation at most `D / (2N)`. Applying any
finite stochastic kernel preserves this bound; in particular one may add
independent finite randomness and project to any selected encoded bits.
These are the finite arithmetic and data-processing steps in `q:crt-bits`.
-/

open Finset

namespace TwoPointCorrelations

/-- Total variation between two finite real mass functions. -/
noncomputable def finiteTotalVariation {α : Type*} [Fintype α] (f g : α → ℝ) : ℝ :=
  (∑ x, |f x - g x|) / 2

instance modulusProduct_neZero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → ℕ) [∀ i, NeZero (s i)] : NeZero (∏ i, s i) :=
  ⟨Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (s i))⟩

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_CenterBandExpansion
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact expansion of the center-band factors. Each nonempty choice of
constant factors leaves an ordinary divisibility condition for the retained
prime product, and carries precisely one reciprocal removed-prime product. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def natDivisibilityIndicator (d n : ℕ) : ℂ := if d ∣ n then 1 else 0

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_FiniteAverages
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Elementary finite averaging identities used to assemble encoded marginals. -/

namespace TwoPointCorrelations

open Finset

noncomputable def uniformAverage {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  (∑ x, f x) / Fintype.card α

@[simp] lemma uniformAverage_const {α : Type*} [Fintype α] [Nonempty α] (c : ℝ) :
    uniformAverage (fun _ : α => c) = c := by simp [uniformAverage]

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_PretentiousDistance
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The pretentious distance used in ordinary two-point correlations

These definitions use the prime cutoff and the twist-height cutoff at the same
integer scale.  The finite-prime perturbation estimate below is Lemma
`lem:finite-prime-stability` of *Ordinary two-point correlations of
multiplicative functions* (24 September 2026).  It is elementary and does not
assume any analytic input.
-/

namespace TwoPointCorrelations

open scoped ComplexConjugate
open Filter Finset

/-- The primes not exceeding an integer cutoff. -/
def primesUpTo (N : ℕ) : Finset ℕ := (Finset.range (N + 1)).filter Nat.Prime

/-- The square of the pretentious distance; the second sequence can be any twist. -/
noncomputable def squaredDistance (f g : ℕ → ℂ) (N : ℕ) : ℝ :=
  ∑ p ∈ primesUpTo N, (1 - (f p * conj (g p)).re) / (p : ℝ)

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_FinitePrimePhases
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Fourier twists used in qualitative analytic centering count distinct
prime divisors, rather than their multiplicities. Their multiplicativity is
therefore asserted only for coprime arguments. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

def finitePrimeDivisorCount (P : Finset ℕ) (n : ℕ) : ℕ :=
  ∑ p ∈ P, if p ∣ n then 1 else 0

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTEulerProducts
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite Euler-product estimate needed in Halász's method.  The
pretentious-distance saving is obtained from the actual prime coefficients;
no mean-value theorem is assumed here. -/

namespace TwoPointCorrelations

open Complex Finset
open scoped BigOperators ComplexConjugate

noncomputable def mrtArchimedeanTwist (t : ℝ) (n : ℕ) : ℂ :=
  Complex.exp (((t * Real.log (n : ℝ) : ℝ) : ℂ) * Complex.I)

noncomputable def mrtPrimeEulerTerm (b : ℕ → ℂ) (t : ℝ) (p : ℕ) : ℂ :=
  (b p * conj (mrtArchimedeanTwist t p)) / (p : ℂ)

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_RoughShiftBoundary
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The endpoint error in the rough-shift averaging argument

These are finite identities and bounds from the proof of (q:rough-shifts)
in quantitative/03-analytic.tex. No short-sum or sieve estimate is assumed.
The averages below use the positive integers `1,...,Y` and translations
`1,...,D`; the resulting error is at most `2D/Y` times the total weight.
-/

namespace TwoPointCorrelations

open scoped BigOperators

/-- A positive prefix, also when its length is zero. -/
def positivePrefix (u : ℕ → ℂ) (Y : ℕ) : ℂ :=
  ∑ v ∈ Finset.range Y, u (v + 1)

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTTypicalFactors
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite typical-factorization masks used by MRT.  The prime bands
are kept arbitrary here; scale and sieve bounds are separate analytic steps. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical BigOperators

def mrtPrimeAvoids (P : Finset ℕ) (n : ℕ) : Prop := ∀ p ∈ P, ¬ p ∣ n

noncomputable def mrtPrimeMask (P : Finset ℕ) (n : ℕ) : ℝ :=
  if mrtPrimeAvoids P n then 1 else 0

def mrtTypical {ι : Type*} (J : Finset ι) (P : ι → Finset ℕ) (n : ℕ) : Prop :=
  ∀ j ∈ J, ∃ p ∈ P j, p ∣ n

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_ResidueBox
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact residue laws for one interval and three independent intervals.
The box discrepancy is derived by tensoring the one-dimensional count,
without estimating each individual three-dimensional residue atom. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def uniformZModLaw (D : ℕ) [NeZero D] : FiniteLaw (ZMod D) where
  weight _ := 1 / D
  nonneg _ := by positivity
  total := by simp [ZMod.card, nsmul_eq_mul, NeZero.ne D]

noncomputable def intervalResidueLaw {D : ℕ} [NeZero D]
    (A : ZMod D) (N : ℕ) (hN : 0 < N) : FiniteLaw (ZMod D) where
  weight := residueProbability A N
  nonneg _ := by unfold residueProbability; positivity
  total := residueProbability_sum A N hN

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_HalaszPrimeMass
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Mertens' first theorem, in the prime-band convention needed for the
small- and large-prime truncations in the Halasz convolution. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def halaszMertensConstant : ℝ := Real.log 4 + 4

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_HalaszBandPartition
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite geometric partition of log(X/p), using base-two bands. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def halaszBandIndex (y : ℝ) : ℕ := Nat.log 2 ⌊y / Real.log 2⌋₊

noncomputable def halaszBandScale (j : ℕ) : ℝ := Real.log 2 * 2 ^ j

noncomputable def halaszPrimeBandPart (P : Finset ℕ) (X : ℝ) (j : ℕ) : Finset ℕ :=
  P.filter (fun p : ℕ => halaszBandIndex (Real.log (X / p)) = j)

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_PrimePartialSummation
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact partial summation, with the prime-count error retained inside the
integral. This is an internal deduction, not an additional published input. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

noncomputable def partialCoefficientSum (c : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ n ∈ Icc 0 ⌊x⌋₊, c n

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_HalaszPrimePartialSummation
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Partial summation centered at Mertens' logarithmic main term. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

noncomputable def halaszPrimeWeight (n : ℕ) : ℝ :=
  if n.Prime then Real.log (n : ℝ) / n else 0

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_HalaszDenominatorCalculus
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Calculus for the variable denominator in the second prime convolution. -/

namespace TwoPointCorrelations

open MeasureTheory

noncomputable def halaszDenominatorWeight (X x : ℝ) : ℝ :=
  (Real.log X - Real.log x)⁻¹

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_HalaszHyperbola
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact finite hyperbola decomposition underlying Halász's
logarithmic mean-value identity. All endpoints are positive integers. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

def halaszHyperbola (N : ℕ) : Finset (ℕ × ℕ) :=
  ((Icc 1 N).product (Icc 1 N)).filter (fun p => p.1 * p.2 ≤ N)

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_HalaszPrimePowers
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The total reciprocal contribution of higher prime powers is finite.
The convergence theorem is already in Mathlib; only its modulus-one
specialization and the finite hyperbola error are needed here. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def halaszPrimePowerWeight (n : ℕ) : ℝ :=
  if n.Prime then 0 else ArithmeticFunction.vonMangoldt n

noncomputable def halaszPrimePowerConstant : ℝ :=
  ∑' n : ℕ, halaszPrimePowerWeight n / (n : ℝ)

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_HalaszPrimeConvolution
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Prime-only convolution and its explicit O(N) error. This is the first
step of the Granville--Harper--Soundararajan double-convolution argument. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def halaszPrimeConvolution (f : ℕ → ℂ) (N : ℕ) : ℂ :=
  ∑ p ∈ (Icc 1 N).filter Nat.Prime,
    (Real.log (p : ℝ) : ℂ) * f p * (∑ m ∈ Icc 1 (N / p), f m)

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_HalaszInnerApproximation
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A complex-valued approximation, not just a norm bound, permits a second
application of the prime convolution inside the first one. -/

namespace TwoPointCorrelations

open Finset

noncomputable def halaszInnerErrorConstant : ℝ :=
  halaszPrimePowerConstant + 1 + Real.log 2

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_HalaszPrimeTruncation
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The small- and large-prime deletion in the double-convolution argument.
All errors are uniform over one-bounded coefficients. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def halaszPrimeTerm (f : ℕ → ℂ) (N p : ℕ) : ℂ :=
  (Real.log (p : ℝ) : ℂ) * f p * (∑ m ∈ Icc 1 (N / p), f m)

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_HalaszDoubleMean
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ordinary mean reduces to the adaptive double prime convolution,
with an explicit N log log N error. -/

namespace TwoPointCorrelations

open Finset

noncomputable def halaszDenominatorConstant : ℝ :=
  -Real.log (Real.log 2) + 2 * halaszMertensConstant / Real.log 2

noncomputable def halaszDoubleErrorConstant : ℝ :=
  4 + (Real.log 2 + 3 * halaszMertensConstant + halaszPrimePowerConstant + 1) +
    halaszInnerErrorConstant * (1 + |halaszDenominatorConstant|)

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTMeanSquareKernel
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exponential majorant for Dirichlet-polynomial mean squares

This is the elementary kernel behind the mean-value estimate used at the
start of corrected MRT, Appendix A, Proposition A.3.  Its Fourier transform
has quadratic decay, so the ensuing row sum loses no logarithm.
-/

namespace TwoPointCorrelations

open Complex MeasureTheory Set

/-- The integrable exponential time weight, with angular frequency `ω`. -/
noncomputable def mrtMeanSquareKernel (T ω t : ℝ) : ℂ :=
  (Real.exp (-|t| / T) : ℂ) * Complex.exp ((ω * t : ℝ) * Complex.I)

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_HalaszFrequencyRows
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A local frequency-mass estimate controls the entire quadratic-decay row.
This keeps the prime-counting input separate from the finite harmonic-analysis
argument, and applies to the actual finite Dirichlet polynomial. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped BigOperators Classical

noncomputable def halaszFrequencyShell {ι : Type*} (S : Finset ι)
    (freq : ι → ℝ) (T u : ℝ) (k : ℕ) : Finset ι :=
  S.filter (fun i => Nat.floor (T * |freq i - u|) = k)

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_ModFiveContourKernel
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Elementary kernel estimates for the finite Perron rectangle.
The vertical side has an integrable quadratic majorant, while each
horizontal side has the explicit inverse-square height saving.
-/

namespace TwoPointCorrelations

open Complex

noncomputable def modFivePerronKernel (x : ℝ) (s : ℂ) : ℂ :=
  (x : ℂ) ^ s / (s * (s + 1))

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_ModFivePerronInversion
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Triangular Perron inversion from Mathlib's proved Mellin inversion.
The triangular function is a difference of two elementary Mellin transforms;
no additional analytic input or dependency source is needed.
-/

namespace TwoPointCorrelations

open Complex Set MeasureTheory
open scoped Classical

noncomputable def modFiveTriangle (x : ℝ) : ℂ :=
  ((max (1 - x) 0 : ℝ) : ℂ)

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_HalaszSmoothSeries
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The smooth Euler series used in the triple-convolution Perron formula.
The finite prime factors and the smooth factor are absolutely convergent
on the line Re(s)=1. -/

namespace TwoPointCorrelations

open Finset Complex MeasureTheory _root_.Erdos970
open scoped Classical LSeries.notation

noncomputable def halaszSmoothFunction (f : ℕ → ℂ) (N n : ℕ) : ℂ :=
  if n ∈ Nat.smoothNumbers (N + 1) then f n else 0

noncomputable def halaszFiniteCoefficient (P : Finset ℕ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  if n ∈ P then a n else 0

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_HalaszPerronWindowKernel
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A short multiplicative smoothing of Perron's kernel. The difference
has both the first-order bound and an integrable inverse-square tail. -/

namespace TwoPointCorrelations

open Complex

noncomputable def halaszPerronWindowKernel (x δ : ℝ) (s : ℂ) : ℂ :=
  (((1 + δ : ℝ) : ℂ) * modFivePerronKernel ((1 + δ) * x) s -
    modFivePerronKernel x s) / (δ : ℂ)

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_HalaszUnsmoothing
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unsmoothing the triple convolution by a finite difference. Only the
coefficients in the short boundary interval contribute to the error. -/

namespace TwoPointCorrelations

open Finset Complex

noncomputable def halaszTriangularSum (a : ℕ → ℂ) (x : ℝ) : ℂ :=
  ∑ n ∈ Icc 1 ⌊x⌋₊, a n * ((1 - (n : ℝ) / x : ℝ) : ℂ)

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_HalaszGroupedBounds
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complementary trivial estimate for a logarithmic prime band.
Together with the Perron estimate it produces the minimum summed later. -/

namespace TwoPointCorrelations

open Finset Complex
open scoped Classical

noncomputable def halaszGroupedDouble (f : ℕ → ℂ) (N : ℕ) (P : Finset ℕ) : ℂ :=
  ∑ p ∈ P, (Real.log (p : ℝ) : ℂ) * f p *
    (halaszPrimeConvolution f (N / p) / (Real.log ((N : ℝ) / p) : ℂ))

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_LocalFactors
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Multiplicative functions from local prime-power factors

The finite local expansions in Part III of the manuscript replace values at
primes dividing a fixed dilation. The resulting functions are ordinary
multiplicative functions; complete multiplicativity is not required.
-/

namespace TwoPointCorrelations

/-- Multiply local factors over the positive exponents in the prime factorization. -/
noncomputable def fromPrimePowers (F : ℕ → ℕ → ℂ) (n : ℕ) : ℂ :=
  n.factorization.prod F

@[simp] theorem fromPrimePowers_one (F : ℕ → ℕ → ℂ) : fromPrimePowers F 1 = 1 := by
  simp [fromPrimePowers]

@[simp] theorem fromPrimePowers_prime (F : ℕ → ℕ → ℂ) {p : ℕ} (hp : Nat.Prime p) :
    fromPrimePowers F p = F p 1 := by
  simp [fromPrimePowers, hp.factorization, Finsupp.prod]

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTMultiplicativeReduction
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The general-multiplicative reduction in corrected MRT §3.  The completely
multiplicative part keeps the original values at primes; the convolution
correction vanishes at primes and is bounded by two at higher prime powers. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def mrtCompletePart (f : ℕ → ℂ) : ℕ → ℂ :=
  fromPrimePowers (fun p k => f p ^ k)

noncomputable def mrtCorrectionLocal (f : ℕ → ℂ) (p k : ℕ) : ℂ :=
  if k = 0 then 1 else f (p ^ k) - f p * f (p ^ (k - 1))

noncomputable def mrtCorrection (f : ℕ → ℂ) : ℕ → ℂ :=
  fromPrimePowers (mrtCorrectionLocal f)

@[simp] lemma mrtCorrectionLocal_zero (f : ℕ → ℂ) (p : ℕ) :
    mrtCorrectionLocal f p 0 = 1 := by
  simp [mrtCorrectionLocal]

@[simp] lemma mrtCorrectionLocal_one (f : ℕ → ℂ) (h1 : f 1 = 1) (p : ℕ) :
    mrtCorrectionLocal f p 1 = 0 := by
  simp [mrtCorrectionLocal, h1]

noncomputable def mrtArithmetic (f : ℕ → ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n => if n = 0 then 0 else f n, by simp⟩

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTCorrectionSummability
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute summability of the prime-power correction in MRT's reduction
from multiplicative to completely multiplicative functions. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical BigOperators

noncomputable def mrtCorrectionWeight (f : ℕ → ℂ) (n : ℕ) : ℝ :=
  ‖mrtArithmetic (mrtCorrection f) n‖ * (n : ℝ) ^ (-(3 / 4 : ℝ))

noncomputable def mrtCorrectionEulerConstant : ℝ :=
  2 / (1 - (2 : ℝ) ^ (-(3 / 4 : ℝ)))

noncomputable def mrtCorrectionBound : ℝ :=
  Real.exp (mrtCorrectionEulerConstant * ∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ)))

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_HalaszTwistedMean
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Height translation for the ordinary mean estimate. This is the
form applied to Dirichlet polynomials on a vertical line. -/

namespace TwoPointCorrelations

open Complex Finset
open scoped ComplexConjugate

noncomputable def halaszTwistedFunction (f : ℕ → ℂ) (t : ℝ) (n : ℕ) : ℂ :=
  f n * conj (mrtArchimedeanTwist t n)

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTCountMask
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reciprocal prime-count weights as an integral of multiplicative
soft masks.  This is the exact cofactor-weight reduction used in MRT
Appendix A, Lemma A.5. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

noncomputable def mrtCountMask (P : Finset ℕ) (u : ℝ) (n : ℕ) : ℝ :=
  u ^ finitePrimeDivisorCount P n

noncomputable def mrtCountMaskedCoefficient (F : ℕ → ℂ) (P : Finset ℕ)
    (u : ℝ) (n : ℕ) : ℂ := F n * (mrtCountMask P u n : ℂ)

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTCountMean
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ordinary mean cancellation with the literal reciprocal prime-count
weight. Integrating multiplicative soft masks gives the cofactor weight
exactly, while the missing-band and count masks lose only one factor two
in pretentious distance. -/

namespace TwoPointCorrelations

open Finset
open scoped ComplexConjugate Classical

noncomputable def mrtMissingCoefficient (F : ℕ → ℂ) (Q : Finset ℕ)
    (n : ℕ) : ℂ := F n * (mrtPrimeMask Q n : ℂ)

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_HalaszNearDiscrepancy
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Prime discrepancy for the near-minimizing twist in MRT Appendix A.
The deleted-prime contribution is kept separate in Cauchy--Schwarz; this
retains the strict exponent needed by the renormalization error. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped ComplexConjugate Classical

noncomputable def halaszPrimeDiscrepancy (F : ℕ → ℂ) (t : ℝ) (N : ℕ) : ℝ :=
  ∑ p ∈ primesUpTo N, ‖1 - F p * conj (mrtArchimedeanTwist t p)‖ / p

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_HalaszPhaseCells
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unit cells for the elementary power-sum approximation. Centering the
cells cancels the linear phase error, leaving a summable quadratic error. -/

namespace TwoPointCorrelations

open MeasureTheory Finset

noncomputable def halaszPowerPhase (t x : ℝ) : ℂ :=
  Complex.exp (((-t * Real.log x : ℝ) : ℂ) * Complex.I)

@[simp] lemma halasz_power_phase_norm (t x : ℝ) : ‖halaszPowerPhase t x‖ = 1 := by
  simp [halaszPowerPhase, Complex.norm_exp, Complex.mul_re]

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_HalaszUnitCorrection
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact convolution with the constant-one function used for the
near-twist renormalization. Its prime coefficients are the actual deviation
from one, including missing-prime masks. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def halaszUnitCorrectionLocal (F : ℕ → ℂ) (p k : ℕ) : ℂ :=
  if k = 0 then 1 else F (p ^ k) - F (p ^ (k - 1))

noncomputable def halaszUnitCorrection (F : ℕ → ℂ) : ℕ → ℂ :=
  fromPrimePowers (halaszUnitCorrectionLocal F)

@[simp] lemma halaszUnitCorrectionLocal_zero (F : ℕ → ℂ) (p : ℕ) :
    halaszUnitCorrectionLocal F p 0 = 1 := by simp [halaszUnitCorrectionLocal]

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_HalaszPositiveLog
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Logarithmic majorization of the absolute constant-one correction.
Only its bound by two on positive prime powers is used. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def halaszPrimePowerLog (n : ℕ) : ℝ :=
  if IsPrimePow n then 2 * Real.log n else 0

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_HalaszPrimePowerLogBound
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A Chebyshev bound for the prime-power logarithmic kernel appearing in
the positive correction mean. Higher prime powers cost only an absolute
constant times the cutoff. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def halaszPrimePowerLogConstant : ℝ :=
  2 * Real.log 4 + 32 / Real.log 2

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_HalaszUnitEuler
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute Euler control of the constant-one convolution correction.
The first-order exponent is the actual prime discrepancy. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def halaszUnitReciprocal (F : ℕ → ℂ) (n : ℕ) : ℝ :=
  ‖mrtArithmetic (halaszUnitCorrection F) n‖ / (n : ℝ)

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_HalaszUnitRenormalization
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Elementary near-twist renormalization using the absolute unit correction.
The power-sum error is uniform in the summation cutoff and linear in the twist. -/

namespace TwoPointCorrelations

open Finset

noncomputable def halaszPhaseMean (F : ℕ → ℂ) (t : ℝ) (N : ℕ) : ℂ :=
  ∑ n ∈ Icc 1 N, F n * halaszPowerPhase t n

noncomputable def halaszUnitMain (F : ℕ → ℂ) (N : ℕ) : ℂ :=
  (N : ℂ) * ∑ d ∈ Icc 1 N, halaszUnitCorrection F d / (d : ℂ)

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTBoundaryMean
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two boundary strips created by replacing prime-dependent
cofactor cutoffs with endpoints of a multiplicative prime bin. -/

namespace TwoPointCorrelations

open Finset MeasureTheory

noncomputable def mrtBoundarySet (N : ℕ) (δ : ℝ) : Finset ℕ :=
  Ioc N ⌊δ * (N : ℝ)⌋₊ ∪ Ioc (2 * N) ⌊δ * (2 * N : ℕ)⌋₊

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTRamareWeights
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive coefficient weights in the uncorrected Ramaré polynomial.
They have total mass at most one, even at integers divisible by prime
squares.  This is the contraction needed for logarithmic-bin cutoffs. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def mrtRamareWeight (P : Finset ℕ) (n p : ℕ) : ℝ :=
  if p ∣ n then 1 / ((finitePrimeDivisorCount P (n / p) + 1 : ℕ) : ℝ) else 0

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTCoarseBins
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coarse cofactor windows for a multiplicative prime bin.  The weights
are the actual Ramaré weights, and moving all primes in a bin to its
lower endpoint changes coefficients only in two short boundary strips. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def mrtCoarseRamareWeight (P : Finset ℕ) (L : ℕ → ℝ)
    (N n : ℕ) : ℝ :=
  ∑ p ∈ P, mrtRamareWeight P n p *
    if (N : ℝ) < L p * (n / p : ℕ) ∧ L p * (n / p : ℕ) ≤ 2 * N then 1 else 0

noncomputable def mrtCoarseBoundaryCoefficient (P : Finset ℕ) (L : ℕ → ℝ)
    (N n : ℕ) : ℝ :=
  (if N < n ∧ n ≤ 2 * N then ∑ p ∈ P, mrtRamareWeight P n p else 0) -
    mrtCoarseRamareWeight P L N n

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTPrimeSquareMean
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The prime-square error in the corrected Ramaré decomposition has a
small mean square.  The count is evaluated by pairing prime-square
divisibility tests; distinct primes give the product modulus exactly. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

noncomputable def mrtPrimeSquareCount (P : Finset ℕ) (n : ℕ) : ℝ :=
  ∑ p ∈ P, if p ^ 2 ∣ n then 1 else 0

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTRamareMeanError
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual coefficient error made by replacing the corrected Ramaré
denominator with `ω_P(m)+1`.  The pointwise error is supported on prime
squares, so the preceding second-moment count applies directly. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

noncomputable def mrtRamareCorrection (P : Finset ℕ) (F : ℕ → ℂ) (n : ℕ) : ℂ :=
  (if finitePrimeDivisorCount P n = 0 then 0 else F n) -
    ∑ p ∈ P, if p ∣ n then
      F n / ((finitePrimeDivisorCount P (n / p) + 1 : ℕ) : ℂ) else 0

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTCoarseMean
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal coarse-bin polynomial differs from the supported dyadic
polynomial by the prime-square correction and the two short boundary
strips.  Both errors are estimated before any sum over prime bins. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

noncomputable def mrtWeightedRamareCoefficient (P : Finset ℕ) (F : ℕ → ℂ)
    (n : ℕ) : ℂ := F n * ((∑ p ∈ P, mrtRamareWeight P n p : ℝ) : ℂ)

noncomputable def mrtSupportedCoefficient (P : Finset ℕ) (F : ℕ → ℂ)
    (n : ℕ) : ℂ := if finitePrimeDivisorCount P n = 0 then 0 else F n

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTCoarseFactorization
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact factorization of the coarse Ramaré polynomial into short prime
polynomials and cofactor polynomials with fixed multiplicative windows. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def mrtDirichletAtom (F : ℕ → ℂ) (n : ℕ) (t : ℝ) : ℂ :=
  F n / (n : ℂ) * Complex.exp (((-Real.log (n : ℝ)) * t : ℝ) * Complex.I)

noncomputable def mrtCofactorPolynomial (P : Finset ℕ) (F : ℕ → ℂ)
    (N : ℕ) (a t : ℝ) : ℂ :=
  ∑ m ∈ Icc 1 (4 * N),
    if (N : ℝ) < a * m ∧ a * m ≤ 2 * N then
      mrtDirichletAtom F m t / ((finitePrimeDivisorCount P m + 1 : ℕ) : ℂ)
    else 0

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTDivisorPairs
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The divisor-square estimate in the mixed prime/cofactor moment.
The map `(d,e) ↦ (gcd(d,e), d/gcd(d,e), e/gcd(d,e))` bounds a pair of
supported divisors by three supported factors whose product divides the
integer. Summing the divisibility tests gives a finite Euler majorant. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

def mrtGcdTriple (v : ℕ × ℕ) : ℕ × (ℕ × ℕ) :=
  (Nat.gcd v.1 v.2, (v.1 / Nat.gcd v.1 v.2, v.2 / Nat.gcd v.1 v.2))

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTFactoredReciprocal
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite reciprocal mass of integers supported on a prime band. Together
with the gcd-triple injection this supplies the divisor-square mean bound
in MR's mixed prime/cofactor moment without an additional sieve input. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def mrtFactoredUpTo (P : Finset ℕ) (N : ℕ) : Finset ℕ :=
  (Icc 1 N).filter (fun n => n ∈ Nat.factoredNumbers P)

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTPrimeMoments
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High even moments of a prime Dirichlet polynomial.  Expanding the
power produces ordered prime tuples; unique factorization bounds each
coefficient fiber by the factorial, and the ordinary mean-square theorem
then applies to a polynomial of length `N ^ r`. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped BigOperators Classical

noncomputable def mrtPrimePowerCoefficient (P : Finset ℕ) (a : ℕ → ℂ)
    (r n : ℕ) : ℂ :=
  ∑ v ∈ (Fintype.piFinset fun _ : Fin r => P).filter
    (fun v => (∏ i, v i) = n), ∏ i, a (v i)

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTMixedCoefficients
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coefficients of a prime-polynomial power times a cofactor polynomial.
The cofactor may carry arbitrary bounded masks. Unique factorization costs
only the prime-tuple factorial; the remaining multiplicity is the literal
number of supported divisors, controlled by its second moment. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def mrtMixedPrimeFiber (P M : Finset ℕ) (r n : ℕ) :
    Finset ((Fin r → ℕ) × ℕ) :=
  ((Fintype.piFinset (fun _ : Fin r => P)) ×ˢ M).filter
    (fun v => (∏ i, v.1 i) * v.2 = n)

noncomputable def mrtMixedPrimeCoefficient (P M : Finset ℕ)
    (a b : ℕ → ℂ) (r n : ℕ) : ℂ :=
  ∑ v ∈ mrtMixedPrimeFiber P M r n, (∏ i, a (v.1 i)) * b v.2

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTTypicalCoarse
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coarse Ramaré factorization on the actual typical-factorization set.
Removing a prime from the selected band leaves precisely the other-band
mask; the square and endpoint errors retain their uniform finite bounds. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

noncomputable def mrtTypicalCoefficient {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (F : ℕ → ℂ) (n : ℕ) : ℂ :=
  if mrtTypical J P n then F n else 0

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTFrequencyPartition
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The first-small-band frequency partition. Every later class supplies
an actual large polynomial in the preceding band; the exceptional set is
exactly the set on which every band has a large polynomial. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

noncomputable def mrtSmallFrequencyBand {κ : Type*} (K : ℕ → Finset κ)
    (Q : ℕ → κ → ℝ → ℂ) (A : ℕ → κ → ℝ) (j : ℕ) : Set ℝ :=
  {t | ∀ k ∈ K j, ‖Q j k t‖ ≤ A j k}

noncomputable def mrtFirstSmallBand {κ : Type*} (K : ℕ → Finset κ)
    (Q : ℕ → κ → ℝ → ℂ) (A : ℕ → κ → ℝ) (j : ℕ) : Set ℝ :=
  mrtSmallFrequencyBand K Q A j \ ⋃ i ∈ range j, mrtSmallFrequencyBand K Q A i

noncomputable def mrtNoSmallBand {κ : Type*} (K : ℕ → Finset κ)
    (Q : ℕ → κ → ℝ → ℂ) (A : ℕ → κ → ℝ) (J : ℕ) : Set ℝ :=
  (⋃ j ∈ range J, mrtSmallFrequencyBand K Q A j)ᶜ

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTGeneralPrimeError
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The general-multiplicative discrepancy in extracting a prime factor.
It vanishes unless that prime divides the cofactor, and hence has the
same prime-square support as the corrected Ramaré denominator error. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

noncomputable def mrtPrimeProductError (P : Finset ℕ)
    (active : ℕ → ℕ → Prop) (C A B : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ p ∈ P, if p ∣ n ∧ active p n then
    (C n - A p * B (n / p)) / ((finitePrimeDivisorCount P (n / p) + 1 : ℕ) : ℂ)
  else 0

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTGeneralFactorization
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact coarse prime extraction with its prime-square discrepancy.
Only coprime multiplicativity is needed when the discrepancy is bounded. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

noncomputable def mrtPrimeExtractionError (P : Finset ℕ) (L : ℕ → ℝ)
    (N : ℕ) (C A B : ℕ → ℂ) : ℕ → ℂ :=
  mrtPrimeProductError P
    (fun p n => (N : ℝ) < L p * (n / p : ℕ) ∧ L p * (n / p : ℕ) ≤ 2 * N)
    C A B

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTMixedThreshold
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The factorial and support growth in the amplified cofactor moment
are paid from half of the gap between successive prime thresholds. -/

namespace TwoPointCorrelations

noncomputable def mrtAmplificationCost (r : ℕ) (y a : ℝ) : ℝ :=
  ((r : ℝ) + 1) * Real.log 2 + y +
    2 * (r : ℝ) * Real.log (max 1 (r : ℝ)) + 2 * a * y

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_SieveModel
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact independent model and a generating-function bound for its
Bonferroni remainder. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

namespace FiniteLaw

noncomputable def dependentIndependent {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Type*} [∀ i, Fintype (A i)] (μ : ∀ i, FiniteLaw (A i)) :
    FiniteLaw (∀ i, A i) where
  weight x := ∏ i, (μ i).weight (x i)
  nonneg x := prod_nonneg (fun i _ => (μ i).nonneg (x i))
  total := by
    rw [← Fintype.prod_sum (fun i x => (μ i).weight x)]
    simp only [FiniteLaw.total, prod_const_one]

end FiniteLaw

noncomputable def elementarySymmetric {ι : Type*} (P : Finset ι) (a : ι → ℝ) (j : ℕ) : ℝ :=
  ∑ S ∈ P.powersetCard j, ∏ i ∈ S, a i

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_ResidueSampling
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed finite interval sample space for every sieve intersection.
The modulus may vary with the selected primes, but the actual sample law
in these identities never changes. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def uniformFiniteLaw (α : Type*) [Fintype α] [Nonempty α] : FiniteLaw α where
  weight _ := 1 / Fintype.card α
  nonneg _ := by positivity
  total := by simp [Fintype.card_ne_zero]

end TwoPointCorrelations

end OAI
end


