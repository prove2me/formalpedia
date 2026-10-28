-- Prove2me | Definitions.Def_OAIQ041D000
-- name    : OAIQ041D000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T07:52:04.118054+00:00
-- url     : https://prove2.me/theorems/d9a2f715-25bf-4b6a-bbde-b15ab311de0a
-- title:
--   Definitions bundle OAIQ041D000 of the split of OpenAI, The Mézard–Parisi formula for diluted spin glasses (result family 221)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DilutedSpinGlass.mezard_parisi`, carved from OpenAI's openai/math development (OpenAI, *The Mézard–Parisi formula for diluted spin glasses (result family 221)*, OpenAI Math Release, September 23, 2026, result family 221, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 851 declarations of OpenAI's Lean: 645 definitions, 9 inductive types or structures, 41 instances and 156 theorems. The definitions and types are `OAI.DilutedSpinGlass.AtomicWeights`, `OAI.DilutedSpinGlass.BooleanPolynomial.coefficient`, `OAI.DilutedSpinGlass.BooleanPolynomial.monomial`, `OAI.DilutedSpinGlass.BooleanPolynomial.truth`, `OAI.DilutedSpinGlass.BoundedDistance`, `OAI.DilutedSpinGlass.CavityGood`, `OAI.DilutedSpinGlass.CavityIndex`, `OAI.DilutedSpinGlass.ConcreteReservoir.Bond`, `OAI.DilutedSpinGlass.ConcreteReservoir.Site`, `OAI.DilutedSpinGlass.ConcreteReservoir.bondLaw`, `OAI.DilutedSpinGlass.ConcreteReservoir.boundedPotential`, `OAI.DilutedSpinGlass.ConcreteReservoir.clipParameters`, `OAI.DilutedSpinGlass.ConcreteReservoir.increment`, `OAI.DilutedSpinGlass.ConcreteReservoir.markLaw`, `OAI.DilutedSpinGlass.ConcreteReservoir.observableAt`, `OAI.DilutedSpinGlass.ConcreteReservoir.physicalBase`, `OAI.DilutedSpinGlass.ConcreteReservoir.physicalCoefficient`, `OAI.DilutedSpinGlass.ConcreteReservoir.readSpin`, `OAI.DilutedSpinGlass.ConcreteReservoir.scoreError`, `OAI.DilutedSpinGlass.ConcreteReservoir.siteLaw`, `OAI.DilutedSpinGlass.ConcreteReservoir.siteObservable`, `OAI.DilutedSpinGlass.ConcreteReservoir.spinFactor`, `OAI.DilutedSpinGlass.DepthAverage.Regular`, `OAI.DilutedSpinGlass.DepthAverage.average`, `OAI.DilutedSpinGlass.DepthAverage.conditionalScheduledMeanDepthDecidable`, `OAI.DilutedSpinGlass.DepthAverage.coordinateProjection`, `OAI.DilutedSpinGlass.DepthAverage.depthChildMomentDecidable`, `OAI.DilutedSpinGlass.DepthAverage.depthLaw`, `OAI.DilutedSpinGlass.DepthAverage.finiteEncodingAverageDecidable`, `OAI.DilutedSpinGlass.DepthAverage.insertCoordinate`, `OAI.DilutedSpinGlass.DepthAverage.instDecidable_solutions`, `OAI.DilutedSpinGlass.DepthAverage.normalized`, `OAI.DilutedSpinGlass.DepthAverage.overlapDepthAveragePropDecidable`, `OAI.DilutedSpinGlass.DepthAverage.physicalOverlapConcentrationAverageDecidable`, `OAI.DilutedSpinGlass.DepthAverage.projectionShiftAveragePropDecidable`, `OAI.DilutedSpinGlass.DepthAverage.regularBadMassDecidable`, `OAI.DilutedSpinGlass.DepthAverage.rootProjectionShiftErrorDecidable`, `OAI.DilutedSpinGlass.DepthAverage.shiftPath`, `OAI.DilutedSpinGlass.DepthAverage.shiftPathFlag`, `OAI.DilutedSpinGlass.DepthAverage.shiftPerm` and 614 more.
--
--   **Sources.** They come from these modules of lean/OAI/Probability/DilutedSpin, in whole or in part: `DilutedSpin_ActualCharging`, `DilutedSpin_ActualLowIncrement`, `DilutedSpin_ActualNegligible`, `DilutedSpin_ActualPrefix`, `DilutedSpin_ActualTreeSelector`, `DilutedSpin_AnchorExtension`, `DilutedSpin_AveragedEnergyRoot`, `DilutedSpin_BranchingEvaluation`, `DilutedSpin_CavityAllocatedMean`, `DilutedSpin_CavityAllocation`, `DilutedSpin_CavityBounds`, `DilutedSpin_CavityDatumProjection`, `DilutedSpin_CavityIndex`, `DilutedSpin_CavityInsertionAlgebra`, `DilutedSpin_CavityMaskEnergy`, `DilutedSpin_CavityPack`, `DilutedSpin_CavityProxy`, `DilutedSpin_CavityRateLimits`, `DilutedSpin_CavitySeparable`, `DilutedSpin_CavitySplit`, `DilutedSpin_CavityTrialIdentity`, `DilutedSpin_CenteredPressure`, `DilutedSpin_ClippedCavityProxy`, `DilutedSpin_ClippedModelFacts`, `DilutedSpin_ColorIterate`, `DilutedSpin_ColoredAnchor`, `DilutedSpin_CommonTreeSample`, `DilutedSpin_CompoundPhysicalMean`, `DilutedSpin_CompoundPoisson`, `DilutedSpin_CompoundSuperposition`, `DilutedSpin_ConcentrationRate`, `DilutedSpin_ConcreteHistory`, `DilutedSpin_ConcreteReservoir`, `DilutedSpin_ConcreteSelection`, `DilutedSpin_ConditionalScheduledMean`, `DilutedSpin_ConditionalSpatialContinuity`, `DilutedSpin_CoordinateFiber`, `DilutedSpin_CountArrayBridge`, `DilutedSpin_CountableFullSupport`, `DilutedSpin_CountedSpinMean`, `DilutedSpin_CountedSteps`, `DilutedSpin_DepthChildMoment`, `DilutedSpin_DictionaryAnalytic`, `DilutedSpin_DoubledStemProjection`, `DilutedSpin_EarliestChildDepth`, `DilutedSpin_EnergyInsertionMean`, `DilutedSpin_ExternalCovariance`, `DilutedSpin_ExternalRoot`, `DilutedSpin_ExternalTaylor`, `DilutedSpin_FiniteEncoding`, `DilutedSpin_FiniteHierarchyDense`, `DilutedSpin_FiniteLaw`, `DilutedSpin_FiniteLogExpansion`, `DilutedSpin_FinitePiInjective`, `DilutedSpin_FinitePoissonSplit`, `DilutedSpin_FiniteProducts`, `DilutedSpin_FiniteProjection`, `DilutedSpin_FiniteTowerPi`, `DilutedSpin_FullCubeConditionalContinuity`, `DilutedSpin_FullPalm`, `DilutedSpin_FullRegularSelection`, `DilutedSpin_FullRootIncrement`, `DilutedSpin_FullRootPalm`, `DilutedSpin_FullSelectedError`, `DilutedSpin_FullSelectedRawConcentration`, `DilutedSpin_FullSelectedRegularity`, `DilutedSpin_FullSelectedThermal`, `DilutedSpin_FullThermalAverage`, `DilutedSpin_FunctionalContinuity`, `DilutedSpin_FunctionalStability`, `DilutedSpin_GeneralRootArrayLaw`, `DilutedSpin_GlobalSelectedAverage`, `DilutedSpin_GlobalSelectedError`, `DilutedSpin_GridIncrementSupport`, `DilutedSpin_HeightTransport`, `DilutedSpin_HeterogeneousMarks`, `DilutedSpin_HeterogeneousProjection`, `DilutedSpin_HierarchyBasic`, `DilutedSpin_HistoryDistinct`, `DilutedSpin_HistoryGeometry`, `DilutedSpin_IncrementCavityProxy`, `DilutedSpin_InsertionCoefficient`, `DilutedSpin_InsertionPoint`, `DilutedSpin_InsertionPoissonAlgebra`, `DilutedSpin_JointRootLaw`, `DilutedSpin_KernelTower`, `DilutedSpin_LabeledColorHistory`, `DilutedSpin_MarkInsertion`, `DilutedSpin_MarkMeanProjection`, `DilutedSpin_MarkSiteCoupling`, `DilutedSpin_MarkedPoisson`, `DilutedSpin_MarkerConcrete`, `DilutedSpin_MarkerGeometry`, `DilutedSpin_MarkerJointHistory`, `DilutedSpin_MarkerNormalization`, `DilutedSpin_MarkerPhysicalBridge`, `DilutedSpin_MarkerRootIdentity`, `DilutedSpin_MarkerVariance`, `DilutedSpin_MatrixHistory`, `DilutedSpin_MatrixNormalization`, `DilutedSpin_MatrixPair`, `DilutedSpin_MatrixPhysical`, `DilutedSpin_MatrixRoot`, `DilutedSpin_MatrixTriple`, `DilutedSpin_MeasurableEncoding`, `DilutedSpin_MeasureHierarchy`, `DilutedSpin_MixedDeviation`, `DilutedSpin_MixedEnergy`, `DilutedSpin_MixedPatterns`, `DilutedSpin_MixtureMeasures`, `DilutedSpin_MultileafMatrixPointwise`, `DilutedSpin_NormalizationSymmetry`, `DilutedSpin_NormalizedCutoff`, `DilutedSpin_OldEnergyEmbedding`, `DilutedSpin_OneNewLaw`, `DilutedSpin_OverlapDepthAverage`, `DilutedSpin_PairSquare`, `DilutedSpin_ParameterProduct`, `DilutedSpin_ParameterRate`, `DilutedSpin_PatternComparison`, `DilutedSpin_Perturbations`, `DilutedSpin_PerturbedSizeCoupling`, `DilutedSpin_PhysicalAverages`, `DilutedSpin_PhysicalFieldOrder`, `DilutedSpin_PhysicalIndex`, `DilutedSpin_PhysicalInsertionComparison`, `DilutedSpin_PhysicalMarkerControl`, `DilutedSpin_PhysicalOverlapAverage`, `DilutedSpin_PhysicalOverlapConcentration`, `DilutedSpin_PhysicalOverlapLimit`, `DilutedSpin_PhysicalPairConnection`, `DilutedSpin_PhysicalPairEnergy`, `DilutedSpin_PhysicalReservoirIncrement`, `DilutedSpin_PhysicalScheduledStep`, `DilutedSpin_PhysicalShapeError`, `DilutedSpin_PhysicalSingleton`, `DilutedSpin_PhysicalSubtreeConcentration`, `DilutedSpin_PhysicalTreeMatrix`, `DilutedSpin_PoissonCountThinning`, `DilutedSpin_PoissonMoments`, `DilutedSpin_PoissonSiteThinning`, `DilutedSpin_PoissonVariance`, `DilutedSpin_Polarization`, `DilutedSpin_PrefixProjection`, `DilutedSpin_ProductEvaluationContinuity`, `DilutedSpin_ProductPatterns`, `DilutedSpin_ProductTower`, `DilutedSpin_ProductTowers`, `DilutedSpin_ProfileHistory`, `DilutedSpin_ProjectionShiftError`, `DilutedSpin_ProperChildScheduleContinuity`, `DilutedSpin_QSubsetDeviation`, `DilutedSpin_QSubtreePotential`, `DilutedSpin_QTopologyBound`, `DilutedSpin_QTreeLaw`, `DilutedSpin_RealEncoding`, `DilutedSpin_RegularBadMass`, `DilutedSpin_RegularCovarianceLimit`, `DilutedSpin_RegularDepth`, `DilutedSpin_RegularNodeAverage`, `DilutedSpin_RegularNodeEstimates`, `DilutedSpin_RegularNodeGeometry`, `DilutedSpin_RegularNodeProducer`, `DilutedSpin_RegularOverlapGeometry`, `DilutedSpin_RegularPhysicalShift`, `DilutedSpin_ReservoirInsertionOnEnergy`, `DilutedSpin_ReservoirRate`, `DilutedSpin_ReservoirSiteTransport`, `DilutedSpin_ReservoirVariance`, `DilutedSpin_RootChildMoment`, `DilutedSpin_RootChildSumIntegrability`, `DilutedSpin_RootCoefficients`, `DilutedSpin_RootEncoding`, `DilutedSpin_RootMatrixTriple`, `DilutedSpin_RootMultileafMatrix`, `DilutedSpin_RootOverlapDeviation`, `DilutedSpin_RootOverlapVariance`, `DilutedSpin_RootPatternComparison`, `DilutedSpin_RootPatternProduct`, `DilutedSpin_RootProjectionIntegrability`, `DilutedSpin_RootProjectionShiftError`, `DilutedSpin_SameInsertionAverage`, `DilutedSpin_ScheduledContinuity`, `DilutedSpin_ScheduledCovariance`, `DilutedSpin_ScheduledEvaluationContinuity`, `DilutedSpin_ScheduledFrameError`, `DilutedSpin_ScheduledFrameGeometry`, `DilutedSpin_ScheduledMarkerEstimate`, `DilutedSpin_ScheduledRootMultileaf`, `DilutedSpin_ScheduledTopology`, `DilutedSpin_SelectedPalm`, `DilutedSpin_SelectedTree`, `DilutedSpin_SelectorPolarization`, `DilutedSpin_ShapeEmbedding`, `DilutedSpin_ShapeMarginal`, `DilutedSpin_ShapeMatrix`, `DilutedSpin_ShapeMatrixPhysical`, `DilutedSpin_ShapeMean`, `DilutedSpin_ShapeProjectionEnergy`, `DilutedSpin_ShapeRoot`, `DilutedSpin_ShiftedFrameGeometry`, `DilutedSpin_ShiftedTree`, `DilutedSpin_SimultaneousShift`, `DilutedSpin_SingletonRoot`, `DilutedSpin_SizeSpinRoot`, `DilutedSpin_SpatialScheduledContinuity`, `DilutedSpin_SpinBaseComparison`, `DilutedSpin_SpinMarginal`, `DilutedSpin_SpinRootData`, `DilutedSpin_SplitDepthContinuity`, `DilutedSpin_StemCoupling`, `DilutedSpin_SubsetTree`, `DilutedSpin_TargetEvaluationContinuity`, `DilutedSpin_TargetScheduleContinuity`, `DilutedSpin_TerminalMeanField`, `DilutedSpin_TopologyDecay`, `DilutedSpin_TowerArraySplit`, `DilutedSpin_TowerPadding`, `DilutedSpin_TreeDerivatives`, `DilutedSpin_TreeMarkLaw`, `DilutedSpin_TreeMeasurable`, `DilutedSpin_TreeSampleProjection`, `DilutedSpin_TreeSampling`, `DilutedSpin_TripleMarginal`, `DilutedSpin_UniformIndexCoupling`, `DilutedSpin_UniformRootDecorrelation`, `DilutedSpin_UniversalDictionary`, `DilutedSpin_UpperCommonCoefficient`, `DilutedSpin_UpperCountMean`, `DilutedSpin_UpperCountState`, `DilutedSpin_UpperDatum`, `DilutedSpin_UpperFreshLocal`, `DilutedSpin_UpperInsertion`, `DilutedSpin_UpperMoments`, `DilutedSpin_UpperRegularized`, `DilutedSpin_UpperReplicaPatterns`, `DilutedSpin_UpperRootInsertion`, `DilutedSpin_UpperTrial`, `DilutedSpin_VertexContinuity`, `DilutedSpin_ZeroShape`.
--
--   **Imports.** It imports the published bundle `Def_DilutedSpin`.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ041D002`; the statements `OAI.DilutedSpinGlass.ConcreteReservoir.integrable_scoreError`, `OAI.DilutedSpinGlass.ConcreteReservoir.physical_coefficients_tendsto`, `OAI.DilutedSpinGlass.ConcreteReservoir.scoreError_tendsto`, `OAI.DilutedSpinGlass.PhysicalRoot.spin_selected_concentration`, `OAI.DilutedSpinGlass.PrescribedTree.finiteTrial_upper_fixedField`, `OAI_DilutedSpinGlass_PrescribedTree_upperPoissonCount_bound_firstMoment`, `OAI_DilutedSpinGlass_ReducedTopology_scheduled_root_multileaf`, `OAI_DilutedSpinGlass_SizeCoupling_perturbedMean_cavity_split`, `OAI_DilutedSpinGlass_UniversalDictionary_FullShapeControl_matrix`, `OAI.DilutedSpinGlass.UniversalDictionary.clippedPhysicalMean_reservoir_bound`, `OAI_DilutedSpinGlass_UniversalDictionary_complete_shape_selection`, `OAI.DilutedSpinGlass.UniversalDictionary.full_regular_covariance_selection`, `OAI.DilutedSpinGlass.UniversalDictionary.increment_cavityProxy_bound`, `OAI.DilutedSpinGlass.UniversalDictionary.physicalOverlapLimsup_bound`, `OAI.DilutedSpinGlass.UniversalDictionary.physicalShapeLimsup_tendsto`, `OAI.DilutedSpinGlass.UniversalDictionary.physicalSubtree_limsup_tendsto`, `OAI.DilutedSpinGlass.UniversalDictionary.physical_grid_scheduled_step`, `OAI.DilutedSpinGlass.UniversalDictionary.poissonInsertionOn_comparison_tendsto_ae` and `OAI.DilutedSpinGlass.UniversalDictionary.universal_analytic_selection`; the proofs of `OAI.DilutedSpinGlass.ConcreteReservoir.integrable_scoreError`, `OAI.DilutedSpinGlass.ConcreteReservoir.physical_coefficients_tendsto`, `OAI.DilutedSpinGlass.ConcreteReservoir.scoreError_tendsto`, `OAI.DilutedSpinGlass.PhysicalRoot.spin_selected_concentration`, `OAI.DilutedSpinGlass.PrescribedTree.finiteTrial_upper_fixedField`, `OAI_DilutedSpinGlass_ReducedTopology_scheduled_root_multileaf`, `OAI.DilutedSpinGlass.UniversalDictionary.clippedPhysicalMean_reservoir_bound`, `OAI.DilutedSpinGlass.UniversalDictionary.full_regular_covariance_selection`, `OAI.DilutedSpinGlass.UniversalDictionary.increment_cavityProxy_bound`, `OAI.DilutedSpinGlass.UniversalDictionary.physicalOverlapLimsup_bound`, `OAI.DilutedSpinGlass.UniversalDictionary.physicalShapeLimsup_tendsto`, `OAI.DilutedSpinGlass.UniversalDictionary.physicalSubtree_limsup_tendsto`, `OAI.DilutedSpinGlass.UniversalDictionary.physical_grid_scheduled_step`, `OAI.DilutedSpinGlass.UniversalDictionary.poissonInsertionOn_comparison_tendsto_ae`, `OAI.DilutedSpinGlass.UniversalDictionary.universal_analytic_selection` and `OAI.DilutedSpinGlass.mezard_parisi`.
-- source:
--   OpenAI, The Mézard–Parisi formula for diluted spin glasses (result family 221), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 221; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Mezard-Parisi-formula-for-diluted-spin-glasses-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability/DilutedSpin at commit adc7f12

import Mathlib
import Definitions.Def_DilutedSpin

section
-- module Solutions.OAIQ041_DS.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
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
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_FiniteLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
attribute [local instance] DilutedSpinGlass.instMeasurableSpaceCarrier_challenge DilutedSpinGlass.instBorelSpaceCarrier_challenge
namespace DilutedSpinGlass

/-- A finite conditional path law. Used only for the finite-kernel proof steps. -/
structure FiniteLaw (Ω : Type*) [Fintype Ω] where
  weight : Ω → ℝ
  nonneg : ∀ x, 0 ≤ weight x
  total : ∑ x, weight x = 1

namespace FiniteLaw

variable {Ω : Type*} [Fintype Ω] (P : FiniteLaw Ω)

noncomputable def expect (f : Ω → ℝ) : ℝ := ∑ x, P.weight x * f x

@[simp] theorem expect_const (c : ℝ) : P.expect (fun _ => c) = c := by
  simp [expect, ← Finset.sum_mul, P.total]

@[simp] theorem expect_add (f g : Ω → ℝ) :
    P.expect (fun x => f x + g x) = P.expect f + P.expect g := by
  simp [expect, mul_add, Finset.sum_add_distrib]

@[simp] theorem expect_sub (f g : Ω → ℝ) :
    P.expect (fun x => f x - g x) = P.expect f - P.expect g := by
  simp [expect, mul_sub, Finset.sum_sub_distrib]

@[simp] theorem expect_mul_left (c : ℝ) (f : Ω → ℝ) :
    P.expect (fun x => c * f x) = c * P.expect f := by
  simp [expect, ← Finset.mul_sum, mul_left_comm]

@[simp] theorem expect_mul_right (f : Ω → ℝ) (c : ℝ) :
    P.expect (fun x => f x * c) = P.expect f * c := by
  simp only [expect, Finset.sum_mul, mul_assoc]

@[simp] theorem expect_div (f : Ω → ℝ) (c : ℝ) :
    P.expect (fun x => f x / c) = P.expect f / c := by
  simp [div_eq_mul_inv]

@[simp] theorem expect_neg (f : Ω → ℝ) :
    P.expect (fun x => -f x) = -P.expect f := by
  simp only [expect, mul_neg, Finset.sum_neg_distrib]

@[simp] theorem expect_sum {ι : Type*} (s : Finset ι) (f : ι → Ω → ℝ) :
    P.expect (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, P.expect (f i) := by
  simp only [expect, Finset.mul_sum]
  exact Finset.sum_comm

@[simp] theorem expect_fintype_sum {ι : Type*} [Fintype ι] (f : ι → Ω → ℝ) :
    P.expect (fun x => ∑ i, f i x) = ∑ i, P.expect (f i) := by
  simp only [expect, Finset.mul_sum]
  exact Finset.sum_comm

theorem expect_nonneg {f : Ω → ℝ} (h : ∀ x, 0 ≤ f x) : 0 ≤ P.expect f := by
  exact Finset.sum_nonneg (fun x _ => mul_nonneg (P.nonneg x) (h x))

noncomputable def covariance (f g : Ω → ℝ) : ℝ :=
  P.expect (fun x => f x * g x) - P.expect f * P.expect g

/-- The normalized site contraction used in sections/decorrelation.tex. -/
noncomputable def dot {n : ℕ} (x y : Fin n → ℝ) : ℝ :=
  (∑ i, x i * y i) / n

variable {n : ℕ}

/-- Squared conditional covariance density. -/
noncomputable def covarianceEnergy (X : Ω → Fin n → ℝ) : ℝ :=
  (∑ i, ∑ j, P.covariance (fun x => X x i) (fun x => X x j)^2) / (n : ℝ)^2

noncomputable def l2 (f : Ω → ℝ) : ℝ := Real.sqrt (P.expect (fun x => f x^2))

@[simp] theorem l2_sq (f : Ω → ℝ) : P.l2 f ^ 2 = P.expect (fun x => f x^2) :=
  Real.sq_sqrt (P.expect_nonneg (fun _ => sq_nonneg _))

@[simp] theorem l2_zero : P.l2 (fun _ => 0) = 0 := by simp [l2]

/-- A finite mixture, to represent the root and the independent kernels exactly. -/
noncomputable def bind {Λ : Type*} [Fintype Λ] (Q : Ω → FiniteLaw Λ) : FiniteLaw (Ω × Λ) where
  weight x := P.weight x.1 * (Q x.1).weight x.2
  nonneg x := mul_nonneg (P.nonneg x.1) ((Q x.1).nonneg x.2)
  total := by
    simp only [Fintype.sum_prod_type, ← Finset.mul_sum, (Q _).total, mul_one, P.total]

@[simp] theorem expect_bind {Λ : Type*} [Fintype Λ] (Q : Ω → FiniteLaw Λ)
    (f : Ω × Λ → ℝ) :
    (P.bind Q).expect f = P.expect (fun x => (Q x).expect (fun y => f (x, y))) := by
  simp only [expect, bind, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]


/-- Positive functions have positive finite expectation, without a full-support
assumption on the kernel. -/
theorem expect_pos {f : Ω → ℝ} (hf : ∀ x, 0 < f x) : 0 < P.expect f := by
  have hw : ∃ x, 0 < P.weight x := by
    by_contra! h
    have hz : (∑ x, P.weight x) ≤ ∑ _x : Ω, (0 : ℝ) :=
      Finset.sum_le_sum (fun x _ => h x)
    simp only [P.total, Finset.sum_const_zero] at hz
    linarith
  obtain ⟨x, hx⟩ := hw
  exact Finset.sum_pos' (fun y _ => mul_nonneg (P.nonneg y) (hf y).le)
    ⟨x, Finset.mem_univ _, mul_pos hx (hf x)⟩

noncomputable def expMoment (m : ℝ) (f : Ω → ℝ) : ℝ :=
  P.expect (fun x => Real.exp (m * f x))

@[simp] theorem expMoment_pos (m : ℝ) (f : Ω → ℝ) : 0 < P.expMoment m f :=
  P.expect_pos (fun _ => Real.exp_pos _)

/-- One tilted path kernel (trees.tex, original-tilt). -/
noncomputable def tilt (m : ℝ) (f : Ω → ℝ) : FiniteLaw Ω where
  weight x := P.weight x * Real.exp (m * f x) / P.expMoment m f
  nonneg x := div_nonneg (mul_nonneg (P.nonneg x) (Real.exp_pos _).le)
    (P.expMoment_pos _ _).le
  total := by
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt (P.expMoment_pos _ _))

noncomputable def logMean (m : ℝ) (f : Ω → ℝ) : ℝ :=
  Real.log (P.expMoment m f) / m

theorem tilt_expect (m : ℝ) (f g : Ω → ℝ) :
    (P.tilt m f).expect g =
      P.expect (fun x => Real.exp (m * f x) * g x) / P.expMoment m f := by
  simp only [expect, tilt, div_mul_eq_mul_div, ← Finset.sum_div, mul_assoc]

@[simp] theorem expMoment_add (m c : ℝ) (f : Ω → ℝ) :
    P.expMoment m (fun x => f x + c) = P.expMoment m f * Real.exp (m * c) := by
  simp only [expMoment, mul_add, Real.exp_add, expect_mul_right]

@[simp] theorem logMean_add {m : ℝ} (hm : m ≠ 0) (c : ℝ) (f : Ω → ℝ) :
    P.logMean m (fun x => f x + c) = P.logMean m f + c := by
  simp only [logMean, expMoment_add,
    Real.log_mul (ne_of_gt (P.expMoment_pos _ _)) (ne_of_gt (Real.exp_pos _)),
    Real.log_exp, add_div]
  field_simp


@[ext] theorem weights_ext {P Q : FiniteLaw Ω} (h : ∀ x, P.weight x = Q.weight x) : P = Q := by
  cases P
  cases Q
  congr
  exact funext h

@[simp] theorem logMean_const {m : ℝ} (hm : m ≠ 0) (c : ℝ) :
    P.logMean m (fun _ => c) = c := by
  simp only [logMean, expMoment, expect_const, Real.log_exp]
  field_simp

/-- Independent product of finitely many finite conditional laws. -/
noncomputable def pi {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*} [∀ i, Fintype (α i)]
    (Q : (i : ι) → FiniteLaw (α i)) : FiniteLaw ((i : ι) → α i) where
  weight x := ∏ i, (Q i).weight (x i)
  nonneg x := Finset.prod_nonneg (fun i _ => (Q i).nonneg _)
  total := by rw [← Fintype.prod_sum]; simp only [(Q _).total, Finset.prod_const_one]

end FiniteLaw
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_KernelTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
attribute [local instance] DilutedSpinGlass.instMeasurableSpaceCarrier_challenge DilutedSpinGlass.instBorelSpaceCarrier_challenge
namespace DilutedSpinGlass

/-- A finite path space. All probability kernels in the bounded auxiliary
perturbation construction are finite, conditional on the physical root. -/
def FinitePath (Ω : Type) : ℕ → Type
  | 0 => Unit
  | n + 1 => Ω × FinitePath Ω n

instance finitePathFintype (Ω : Type) [Fintype Ω] : (n : ℕ) → Fintype (FinitePath Ω n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n + 1 => by
    letI := finitePathFintype Ω n
    exact inferInstanceAs (Fintype (Ω × FinitePath Ω n))

/-- Finite kernels depending on the full preceding path, before tilting. -/
def KernelTower (Ω : Type) [Fintype Ω] : ℕ → Type
  | 0 => Unit
  | n + 1 => FiniteLaw Ω × (Ω → KernelTower Ω n)

namespace KernelTower

variable {Ω : Type} [Fintype Ω]

noncomputable def unitLaw : FiniteLaw Unit where
  weight _ := 1
  nonneg _ := by norm_num
  total := by simp

noncomputable def law : (n : ℕ) → KernelTower Ω n → FiniteLaw (FinitePath Ω n)
  | 0, _ => unitLaw
  | n+1, T => T.1.bind (fun x => law n (T.2 x))

noncomputable def backwardLog : (n : ℕ) → KernelTower Ω n →
    (Fin n → ℝ) → (FinitePath Ω n → ℝ) → ℝ
  | 0, _, _, f => f ()
  | n+1, T, m, f => T.1.logMean (m 0)
      (fun x => backwardLog n (T.2 x) (fun j => m j.succ) (fun y => f (x,y)))

noncomputable def tilt : (n : ℕ) → KernelTower Ω n →
    (Fin n → ℝ) → (FinitePath Ω n → ℝ) → KernelTower Ω n
  | 0, _, _, _ => ()
  | n+1, T, m, f =>
    (T.1.tilt (m 0) (fun x => backwardLog n (T.2 x)
        (fun j => m j.succ) (fun y => f (x,y))),
      fun x => tilt n (T.2 x) (fun j => m j.succ) (fun y => f (x,y)))

@[simp] theorem expect_unitLaw (f : Unit → ℝ) : unitLaw.expect f = f () := by
  simp [FiniteLaw.expect, unitLaw]

@[simp] theorem law_zero_expect (T : KernelTower Ω 0) (f : FinitePath Ω 0 → ℝ) :
    (law 0 T).expect f = f () := expect_unitLaw f

@[simp] theorem law_succ_expect (n : ℕ) (T : KernelTower Ω (n+1))
    (f : FinitePath Ω (n+1) → ℝ) :
    (law (n+1) T).expect f = T.1.expect (fun x => (law n (T.2 x)).expect (fun y => f (x,y))) :=
  T.1.expect_bind (fun x => law n (T.2 x)) f



noncomputable def varianceEnergy : (n : ℕ) → KernelTower Ω n →
    (Fin n → ℝ) → (FinitePath Ω n → ℝ) → ℝ
  | 0, _, _, _ => 0
  | n+1, T, m, f =>
      m 0 * T.1.covariance
        (fun x => (law n (T.2 x)).expect (fun y => f (x,y)))
        (fun x => (law n (T.2 x)).expect (fun y => f (x,y))) +
      T.1.expect (fun x => varianceEnergy n (T.2 x) (fun j => m j.succ)
        (fun y => f (x,y)))

end KernelTower
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_TreeSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
attribute [local instance] DilutedSpinGlass.instMeasurableSpaceCarrier_challenge DilutedSpinGlass.instBorelSpaceCarrier_challenge
namespace DilutedSpinGlass

/-- Prescribed trees include a vertex at every depth, including unary vertices.
Every internal vertex has at least one child; every leaf has the given height. -/
inductive PrescribedTree : ℕ → Type
  | leaf : PrescribedTree 0
  | node {n : ℕ} (k : ℕ+) (children : Fin k → PrescribedTree n) : PrescribedTree (n+1)

namespace PrescribedTree

noncomputable def leaves : {n : ℕ} → PrescribedTree n → ℕ
  | 0, .leaf => 1
  | _+1, .node _ T => ∑ i, leaves (T i)

end PrescribedTree
end DilutedSpinGlass

namespace DilutedSpinGlass.PrescribedTree

/-- Samples at separate sibling vertices are independent; repeated values are
allowed. The full unary parts of each prescribed tree are retained. -/
def Sample (Ω : Type) : {n : ℕ} → PrescribedTree n → Type
  | 0, .leaf => Unit
  | _+1, .node k C => (i : Fin k) → Ω × Sample Ω (C i)

instance sampleFintype (Ω : Type) [Fintype Ω] : {n : ℕ} →
    (S : PrescribedTree n) → Fintype (Sample Ω S)
  | 0, .leaf => inferInstanceAs (Fintype Unit)
  | _+1, .node k C => by
      letI : ∀ i, Fintype (Sample Ω (C i)) := fun i => sampleFintype Ω (C i)
      exact inferInstanceAs (Fintype ((i : Fin k) → Ω × Sample Ω (C i)))

variable {Ω : Type} [Fintype Ω]

noncomputable def sampleLaw : {n : ℕ} → (S : PrescribedTree n) →
    KernelTower Ω n → FiniteLaw (Sample Ω S)
  | 0, .leaf, _ => KernelTower.unitLaw
  | _+1, .node _ C, T => FiniteLaw.pi (fun i => T.1.bind (fun x => sampleLaw (C i) (T.2 x)))

/-- The logarithm of the vertex product in tree:density. The first entry of
m is the incoming edge exponent (zero at the root); the final entry equals
one in the manuscript applications. -/
noncomputable def vertexPotential : {n : ℕ} → (S : PrescribedTree n) →
    KernelTower Ω n → (Fin (n+1) → ℝ) → (FinitePath Ω n → ℝ) → Sample Ω S → ℝ
  | 0, .leaf, _, m, f, _ => m 0 * f ()
  | n+1, .node k C, T, m, f, x =>
      (m 0 - (k : ℝ) * m 1) * KernelTower.backwardLog (n+1) T (fun j => m j.succ) f +
      ∑ i, vertexPotential (C i) (T.2 (x i).1) (fun j => m j.succ)
        (fun y => f ((x i).1,y)) (x i).2

/-- First variation of the vertex product: one score for every uncontracted
leaf, and gamma_beta times the score of a fresh path at every internal vertex. -/
noncomputable def vertexScore : {n : ℕ} → (S : PrescribedTree n) →
    KernelTower Ω n → (Fin (n+1) → ℝ) → (FinitePath Ω n → ℝ) →
      (FinitePath Ω n → ℝ) → Sample Ω S → ℝ
  | 0, .leaf, _, m, _, f', _ => m 0 * f' ()
  | n+1, .node k C, T, m, f, f', x =>
      (m 0 - (k : ℝ) * m 1) *
        (KernelTower.law (n+1) (KernelTower.tilt (n+1) T (fun j => m j.succ) f)).expect f' +
        ∑ i, vertexScore (C i) (T.2 (x i).1) (fun j => m j.succ)
          (fun y => f ((x i).1,y)) (fun y => f' ((x i).1,y)) (x i).2

/-- A leaf label is a vertex, not its sampled spin value. -/
def Leaf : {n : ℕ} → PrescribedTree n → Type
  | 0, .leaf => Unit
  | _+1, .node k C => (i : Fin k) × Leaf (C i)

instance leafFintype : {n : ℕ} → (S : PrescribedTree n) → Fintype (Leaf S)
  | 0, .leaf => inferInstanceAs (Fintype Unit)
  | _+1, .node k C => by
    letI : ∀ i, Fintype (Leaf (C i)) := fun i => leafFintype (C i)
    exact inferInstanceAs (Fintype ((i : Fin k) × Leaf (C i)))

/-- Recover a whole path from a labeled leaf in a sampled tree. -/
def pathAt : {n : ℕ} → (S : PrescribedTree n) → Leaf S → Sample Ω S → FinitePath Ω n
  | 0, .leaf, _, _ => ()
  | _+1, .node _ C, a, x => ((x a.1).1, pathAt (C a.1) a.2 (x a.1).2)

/-- Exactly the denominator cancellation at the selected protected leaves,
written in logarithmic form. -/
noncomputable def protectedLog {n : ℕ} (S : PrescribedTree n) (C : Finset (Leaf S))
    (f : FinitePath Ω n → ℝ) (x : Sample Ω S) : ℝ :=
  ∑ a ∈ C, f (pathAt S a x)

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.PrescribedTree

/-- Internal vertices refer to labeled genealogy, not coincident sampled values. -/
def Internal : {n : ℕ} → PrescribedTree n → Type
  | 0, .leaf => Empty
  | _+1, .node _ C => Option ((i : _) × Internal (C i))

instance internalFintype : {n : ℕ} → (S : PrescribedTree n) → Fintype (Internal S)
  | 0, .leaf => inferInstanceAs (Fintype Empty)
  | _+1, .node k C => by
    letI : ∀ i, Fintype (Internal (C i)) := fun i => internalFintype (C i)
    exact inferInstanceAs (Fintype (Option ((i : Fin k) × Internal (C i))))

/-- The signed coefficient at the exact uncontracted divergence vertex. -/
noncomputable def gamma : {n : ℕ} → (S : PrescribedTree n) →
    (Fin (n+1) → ℝ) → Internal S → ℝ
  | 0, .leaf, _, v => nomatch v
  | _+1, .node k C, m, v =>
      match (v : Option ((i : Fin k) × Internal (C i))) with
      | none => m 0 - (k : ℝ) * m 1
      | some ⟨i,v⟩ => gamma (C i) (fun j => m j.succ) v

variable {Ω : Type} [Fintype Ω]

/-- Conditional expectation on a completely new path below the chosen vertex.
Old sampled descendants are NOT reused, even if their values happen to agree. -/
noncomputable def freshEval : {n : ℕ} → (S : PrescribedTree n) →
    KernelTower Ω n → Internal S → (FinitePath Ω n → ℝ) → Sample Ω S → ℝ
  | 0, .leaf, _, v, _, _ => nomatch v
  | n+1, .node k C, T, v, D, x =>
      match (v : Option ((i : Fin k) × Internal (C i))) with
      | none => (KernelTower.law (n+1) T).expect D
      | some ⟨i,v⟩ => freshEval (C i) (T.2 (x i).1) v (fun y => D ((x i).1,y)) (x i).2

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.PrescribedTree

def single : (n : ℕ) → PrescribedTree n
  | 0 => .leaf
  | n+1 => .node 1 (fun _ => single n)

/-- Attach a genuinely new child at the divergence vertex; keep every old
child and every unary level. Child 0 is the new child for root attachment. -/
def grow : {n : ℕ} → (S : PrescribedTree n) → Internal S → PrescribedTree n
  | 0, .leaf, v => nomatch v
  | n+1, .node k C, v =>
    match (v : Option ((i : Fin k) × Internal (C i))) with
    | none => .node (k+1) (Fin.cases (single n) C)
    | some ⟨i,v⟩ => .node k (Function.update C i (grow (C i) v))

variable {Ω : Type}

def singlePath : (n : ℕ) → Sample Ω (single n) → FinitePath Ω n
  | 0, _ => ()
  | n+1, x => ((x 0).1, singlePath n (x 0).2)

/-- The projection forgets the new branch but preserves every old value. -/
def oldSample : {n : ℕ} → (S : PrescribedTree n) → (v : Internal S) →
    Sample Ω (grow S v) → Sample Ω S
  | 0, .leaf, v => nomatch v
  | n+1, .node k C, v => by
    change Option ((i : Fin k) × Internal (C i)) at v
    cases v with
    | none =>
      intro x i
      exact x i.succ
    | some v =>
      obtain ⟨i,v⟩ := v
      intro x j
      by_cases h : j = i
      · subst j
        have y : Ω × Sample Ω (grow (C i) v) := by
          simpa only [grow, Function.update_self] using x i
        exact (y.1, oldSample (C i) v y.2)
      · have y : Ω × Sample Ω (C j) := by
          simpa only [grow, Function.update_of_ne h] using x j
        exact y

/-- The new path shares just its prescribed prefix, even for repeated values. -/
def newPath : {n : ℕ} → (S : PrescribedTree n) → (v : Internal S) →
    Sample Ω (grow S v) → FinitePath Ω n
  | 0, .leaf, v => nomatch v
  | n+1, .node k C, v => by
    change Option ((i : Fin k) × Internal (C i)) at v
    cases v with
    | none =>
      intro x
      exact ((x 0).1, singlePath n (x 0).2)
    | some v =>
      obtain ⟨i,v⟩ := v
      intro x
      have y : Ω × Sample Ω (grow (C i) v) := by
        simpa only [grow, Function.update_self] using x i
      exact (y.1, newPath (C i) v y.2)

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_FiniteProducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
attribute [local instance] DilutedSpinGlass.instMeasurableSpaceCarrier_challenge DilutedSpinGlass.instBorelSpaceCarrier_challenge

namespace DilutedSpinGlass.FiniteLaw
open scoped BigOperators

noncomputable def delta {α : Type*} (x y : α) : ℝ := by
  classical
  exact if x = y then 1 else 0

end DilutedSpinGlass.FiniteLaw

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_TreeDerivatives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
attribute [local instance] DilutedSpinGlass.instMeasurableSpaceCarrier_challenge DilutedSpinGlass.instBorelSpaceCarrier_challenge

namespace DilutedSpinGlass.PrescribedTree
variable {Ω : Type}

/-- Sum of the terminal marks, retaining multiplicity of equal sampled paths. -/
noncomputable def leafSum : {n : ℕ} → (S : PrescribedTree n) →
    (FinitePath Ω n → ℝ) → Sample Ω S → ℝ
  | 0, .leaf, f, _ => f ()
  | _+1, .node _ C, f, x => ∑ i, leafSum (C i) (fun y => f ((x i).1,y)) (x i).2

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.PrescribedTree

noncomputable def trivialSample : {n : ℕ} → (S : PrescribedTree n) → Sample Unit S
  | 0, .leaf => ()
  | _+1, .node _ C => fun i => ((),trivialSample (C i))

variable {Ω : Type} [Fintype Ω]

/-- All sampled terminal leaves are canceled, with no diagonal contraction. -/
noncomputable def fullyProtected {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (D : FinitePath Ω n → ℝ) (G : Sample Ω S → ℝ) (t : ℝ) : ℝ :=
  (sampleLaw S (KernelTower.tilt n T (fun j => m j.succ)
    (fun y => Real.log (1+t*D y)))).expect (fun x => G x *
      Real.exp (-leafSum S (fun y => Real.log (1+t*D y)) x))

/-- Sum over all sequential genuine fresh-extension histories, with their
signed products. This is not a law chosen to force the expansion. -/
noncomputable def extensionIterate {n : ℕ} (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (D : FinitePath Ω n → ℝ) :
    ℕ → (S : PrescribedTree n) → (Sample Ω S → ℝ) → ℝ → ℝ
  | 0, S, G, t => fullyProtected S T m D G t
  | k+1, S, G, t => ∑ v : Internal S, gamma S m v *
      extensionIterate T m D k (grow S v) (fun x => G (oldSample S v x) * D (newPath S v x)) t

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_PoissonMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
attribute [local instance] DilutedSpinGlass.instMeasurableSpaceCarrier_challenge DilutedSpinGlass.instBorelSpaceCarrier_challenge

namespace DilutedSpinGlass

universe u

/-- A finite independent block sequence, with no finiteness assumption on a block. -/
abbrev RootPath (Ω : Type u) : ℕ → Type u
  | 0 => PUnit
  | n+1 => Ω × RootPath Ω n

@[reducible] instance rootPathMeasurable (Ω : Type*) [MeasurableSpace Ω] :
    (n : ℕ) → MeasurableSpace (RootPath Ω n)
  | 0 => inferInstanceAs (MeasurableSpace PUnit)
  | n+1 => by
    letI := rootPathMeasurable Ω n
    exact inferInstanceAs (MeasurableSpace (Ω × RootPath Ω n))

noncomputable def rootLaw {Ω : Type*} [MeasurableSpace Ω] :
    (n : ℕ) → (Fin n → Measure Ω) → Measure (RootPath Ω n)
  | 0, _ => Measure.dirac PUnit.unit
  | n+1, μ => (μ 0).prod (rootLaw n (fun i => μ i.succ))

instance rootLawProbability {Ω : Type*} [MeasurableSpace Ω] (n : ℕ)
    (μ : Fin n → Measure Ω) [hμ : ∀ i, IsProbabilityMeasure (μ i)] :
    IsProbabilityMeasure (rootLaw n μ) := by
  induction n with
  | zero => exact Measure.dirac.isProbabilityMeasure
  | succ n ih =>
    have : ∀ i : Fin n, IsProbabilityMeasure (μ i.succ) := fun i => hμ i.succ
    have := ih (fun i => μ i.succ)
    change IsProbabilityMeasure ((μ 0).prod (rootLaw n (fun i => μ i.succ)))
    first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)

def replaceRoot {Ω : Type*} : (n : ℕ) → RootPath Ω n → Fin n → Ω → RootPath Ω n
  | 0, x, _, _ => x
  | n+1, x, i, y => Fin.cases (y,x.2) (fun j => (x.1,replaceRoot n x.2 j y)) i

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_MarkedPoisson
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
attribute [local instance] DilutedSpinGlass.instMeasurableSpaceCarrier_challenge DilutedSpinGlass.instBorelSpaceCarrier_challenge
namespace DilutedSpinGlass

/-- The archival Mathlib Poisson weights, not a replacement count model. -/
noncomputable def poissonWeight (r : ℝ≥0) (n : ℕ) : ℝ :=
  Real.exp (-(r : ℝ)) * (r : ℝ)^n / (n.factorial : ℝ)

@[simp] theorem poissonWeight_nonneg (r : ℝ≥0) (n : ℕ) : 0 ≤ poissonWeight r n := by
  unfold poissonWeight
  positivity

end DilutedSpinGlass

namespace DilutedSpinGlass

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

noncomputable def rootAverage (F : (n : ℕ) → RootPath Ω n → ℝ) (n : ℕ) : ℝ :=
  ∫ x, F n x ∂rootLaw n (fun _ => μ)

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ProductTowers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
attribute [local instance] DilutedSpinGlass.instMeasurableSpaceCarrier_challenge DilutedSpinGlass.instBorelSpaceCarrier_challenge
namespace DilutedSpinGlass.FiniteLaw
variable {Ω Λ : Type*} [Fintype Ω] [Fintype Λ]

/-- Relabeling outcomes does not change a finite conditional probability law. -/
noncomputable def transport (e : Ω ≃ Λ) (P : FiniteLaw Ω) : FiniteLaw Λ where
  weight y := P.weight (e.symm y)
  nonneg y := P.nonneg _
  total := by
    exact (Fintype.sum_equiv e.symm _ _ (fun _ => rfl)).trans P.total

@[simp] theorem expect_transport (e : Ω ≃ Λ) (P : FiniteLaw Ω) (f : Λ → ℝ) :
    (P.transport e).expect f = P.expect (f ∘ e) := by
  unfold expect transport
  exact Fintype.sum_equiv e.symm _ _ (fun y => by
    simp only [Function.comp_apply, Equiv.apply_symm_apply])

@[simp] theorem expMoment_transport (e : Ω ≃ Λ) (P : FiniteLaw Ω)
    (m : ℝ) (f : Λ → ℝ) :
    (P.transport e).expMoment m f = P.expMoment m (f ∘ e) := by
  exact expect_transport e P _

@[simp] theorem logMean_transport (e : Ω ≃ Λ) (P : FiniteLaw Ω)
    (m : ℝ) (f : Λ → ℝ) :
    (P.transport e).logMean m f = P.logMean m (f ∘ e) := by
  simp only [logMean, expMoment_transport]

end DilutedSpinGlass.FiniteLaw

namespace DilutedSpinGlass.KernelTower
variable {Ω Λ : Type} [Fintype Ω] [Fintype Λ]

def pathEquiv (e : Ω ≃ Λ) : (n : ℕ) → FinitePath Ω n ≃ FinitePath Λ n
  | 0 => Equiv.refl _
  | n+1 => e.prodCongr (pathEquiv e n)

omit [Fintype Ω] [Fintype Λ] in
@[simp] theorem pathEquiv_cons (e : Ω ≃ Λ) (n : ℕ) (a : Ω) (x : FinitePath Ω n) :
    pathEquiv e (n+1) (a,x) = (e a, pathEquiv e n x) := rfl

noncomputable def transport (e : Ω ≃ Λ) : (n : ℕ) → KernelTower Ω n → KernelTower Λ n
  | 0, _ => ()
  | n+1, T => (T.1.transport e, fun a => transport e n (T.2 (e.symm a)))

end DilutedSpinGlass.KernelTower

namespace DilutedSpinGlass.PrescribedTree
variable {Ω Λ : Type} [Fintype Ω] [Fintype Λ]

/-- Relabel every sampled vertex without identifying distinct replica paths. -/
def sampleEquiv (e : Ω ≃ Λ) : {n : ℕ} → (S : PrescribedTree n) → Sample Ω S ≃ Sample Λ S
  | 0, .leaf => Equiv.refl _
  | _+1, .node _ C => Equiv.piCongrRight (fun i => e.prodCongr (sampleEquiv e (C i)))

omit [Fintype Ω] [Fintype Λ] in
@[simp] theorem sampleEquiv_node (e : Ω ≃ Λ) {n : ℕ} (k : ℕ+)
    (C : Fin k → PrescribedTree n) (x : Sample Ω (.node k C)) (j : Fin k) :
    sampleEquiv e (.node k C) x j = (e (x j).1, sampleEquiv e (C j) (x j).2) := rfl

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.FiniteLaw
variable {Ω Λ : Type*} [Fintype Ω] [Fintype Λ]

@[ext] theorem ext {P Q : FiniteLaw Ω} (h : ∀ x, P.weight x = Q.weight x) : P = Q := by
  cases P
  cases Q
  congr
  exact funext h

end DilutedSpinGlass.FiniteLaw

namespace DilutedSpinGlass.KernelTower
variable {Ω Λ : Type} [Fintype Ω] [Fintype Λ]

/-- Independent auxiliary mark kernels are joined at each depth, not added
as separately normalized replicas. -/
noncomputable def prod : (n : ℕ) → KernelTower Ω n → KernelTower Λ n →
    KernelTower (Ω × Λ) n
  | 0, _, _ => ()
  | n+1, T, U => (T.1.bind (fun _ => U.1), fun z => prod n (T.2 z.1) (U.2 z.2))

def pathFst : (n : ℕ) → FinitePath (Ω × Λ) n → FinitePath Ω n
  | 0, _ => ()
  | n+1, x => (x.1.1, pathFst n x.2)

def pathSnd : (n : ℕ) → FinitePath (Ω × Λ) n → FinitePath Λ n
  | 0, _ => ()
  | n+1, x => (x.1.2, pathSnd n x.2)

end DilutedSpinGlass.KernelTower

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_PoissonVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
attribute [local instance] DilutedSpinGlass.instMeasurableSpaceCarrier_challenge DilutedSpinGlass.instBorelSpaceCarrier_challenge

namespace DilutedSpinGlass
variable {Ω A : Type} [Fintype Ω] [Fintype A]

/-- An independent mark prior with no physical state. -/
noncomputable def markPrior : (L : ℕ) → (Fin L → FiniteLaw A) → KernelTower A L
  | 0, _ => ()
  | L+1, Q => (Q 0, fun _ => markPrior L (fun j => Q j.succ))

end DilutedSpinGlass

namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

/-- The recursive independent-root product and the finite indexed root array
are the same labeled data. No exchangeability is needed here. -/
def rootArray {I : Type*} : (n : ℕ) → RootPath I n → Fin n → I
  | 0, _ => Fin.elim0
  | n+1, x => Fin.cons x.1 (rootArray n x.2)

instance rootPathCountable (I : Type*) [Countable I] : (n : ℕ) → Countable (RootPath I n)
  | 0 => inferInstanceAs (Countable PUnit)
  | n+1 => by
    let := rootPathCountable I n
    exact inferInstanceAs (Countable (I × RootPath I n))

instance rootPathSingleton (I : Type*) [MeasurableSpace I] [MeasurableSingletonClass I] :
    (n : ℕ) → MeasurableSingletonClass (RootPath I n)
  | 0 => inferInstanceAs (MeasurableSingletonClass PUnit)
  | n+1 => by
    let := rootPathSingleton I n
    exact inferInstanceAs (MeasurableSingletonClass (I × RootPath I n))

end DilutedSpinGlass

namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace FiniteLaw
variable {Ω X : Type*} [Fintype Ω] [MeasurableSpace X]

theorem measurable_expect (P : FiniteLaw Ω) {f : X → Ω → ℝ}
    (hf : ∀ a, Measurable (fun x => f x a)) : Measurable (fun x => P.expect (f x)) := by
  unfold expect
  exact Finset.measurable_sum _ (fun a _ => (hf a).const_mul _)

theorem measurable_logMean (P : FiniteLaw Ω) (m : ℝ) {f : X → Ω → ℝ}
    (hf : ∀ a, Measurable (fun x => f x a)) : Measurable (fun x => P.logMean m (f x)) := by
  unfold logMean expMoment
  exact (P.measurable_expect (fun a => ((hf a).const_mul m).exp)).log.div_const m

end FiniteLaw

namespace KernelTower
variable {Ω X : Type} [Fintype Ω] [MeasurableSpace X]

theorem measurable_backwardLog (L : ℕ) (T : KernelTower Ω L) (m : Fin L → ℝ)
    {f : X → FinitePath Ω L → ℝ} (hf : ∀ a, Measurable (fun x => f x a)) :
    Measurable (fun x => backwardLog L T m (f x)) := by
  induction L with
  | zero => exact hf ()
  | succ L ih =>
    apply FiniteLaw.measurable_logMean
    intro a
    exact ih (T.2 a) (fun j => m j.succ) (fun b => hf (a,b))

end KernelTower

/-- Coordinate evaluation is measurable for the genuine independent root
product, including arbitrary (not necessarily discrete) interaction marks. -/
theorem measurable_rootArray {I : Type*} [MeasurableSpace I] (n : ℕ) (j : Fin n) :
    Measurable (fun x : RootPath I n => rootArray n x j) := by
  induction n with
  | zero => exact Fin.elim0 j
  | succ n ih =>
    refine Fin.cases ?_ (fun q => ?_) j
    · exact measurable_fst
    · exact (ih q).comp measurable_snd

end DilutedSpinGlass

namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- Root averaging followed by the genuine Poisson count average. -/
noncomputable def poissonRootAverage (r : ℝ≥0)
    (F : (n : ℕ) → RootPath Ω n → ℝ) : ℝ :=
  ∫ n, rootAverage μ F n ∂poissonMeasure r

end DilutedSpinGlass

namespace DilutedSpinGlass
open scoped BigOperators

namespace FiniteLaw
variable {Ω : Type*} [Fintype Ω]

noncomputable def point (a : Ω) : FiniteLaw Ω := by
  classical
  exact { weight := fun x => if x = a then 1 else 0
          nonneg := fun x => by split_ifs <;> norm_num
          total := by simp }

@[simp] theorem expect_point (a : Ω) (f : Ω → ℝ) : (point a).expect f = f a := by
  classical
  simp [expect,point]

@[simp] theorem logMean_point (a : Ω) (m : ℝ) (hm : m ≠ 0) (f : Ω → ℝ) :
    (point a).logMean m f = f a := by
  simp [logMean,expMoment,hm]

noncomputable def uniform [Nonempty Ω] : FiniteLaw Ω where
  weight _ := (Fintype.card Ω : ℝ)⁻¹
  nonneg _ := inv_nonneg.mpr (Nat.cast_nonneg _)
  total := by simp [ne_of_gt (Fintype.card_pos : 0 < Fintype.card Ω)]

end FiniteLaw

namespace KernelTower
variable {Ω : Type} [Fintype Ω]

/-- Auxiliary levels contain no physical spin randomness. The last level is
exactly the Gibbs sum under its uniform spin prior. -/
noncomputable def terminalTower (a : Ω) (P : FiniteLaw Ω) : (r : ℕ) → KernelTower Ω (r+1)
  | 0 => (P, fun _ => ())
  | r+1 => (FiniteLaw.point a, fun _ => terminalTower a P r)

def terminalState : (r : ℕ) → FinitePath Ω (r+1) → Ω
  | 0, x => x.1
  | r+1, x => terminalState r x.2

end KernelTower

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_Perturbations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
attribute [local instance] DilutedSpinGlass.instMeasurableSpaceCarrier_challenge DilutedSpinGlass.instBorelSpaceCarrier_challenge
namespace DilutedSpinGlass.KernelTower
variable {Ω : Type} [Fintype Ω]

/-- Actual log weight after a finite family of perturbations of one type.
The base includes the physical Hamiltonian and every other fixed type. -/
noncomputable def perturbLog {L n : ℕ} (base : FinitePath Ω L → ℝ)
    (D E : Fin n → FinitePath Ω L → ℝ) (t u : ℝ) (y : FinitePath Ω L) : ℝ :=
  base y + ∑ q, Real.log (1+t*D q y+u*E q y)

noncomputable def perturbScore {L n : ℕ} (D E : Fin n → FinitePath Ω L → ℝ)
    (t u : ℝ) (y : FinitePath Ω L) : ℝ :=
  ∑ q, E q y / (1+t*D q y+u*E q y)

noncomputable def perturbCurvature {L n : ℕ} (D E : Fin n → FinitePath Ω L → ℝ)
    (t u : ℝ) (y : FinitePath Ω L) : ℝ :=
  -∑ q, (E q y / (1+t*D q y+u*E q y))^2

end DilutedSpinGlass.KernelTower

namespace DilutedSpinGlass.KernelTower
variable {Ω : Type} [Fintype Ω]

/-- The manuscript's random convex correction, still before any root
expectation is taken. -/
noncomputable def correctedPerturbLog {L n : ℕ} (T : KernelTower Ω L) (m : Fin L → ℝ)
    (base : FinitePath Ω L → ℝ) (D E : Fin n → FinitePath Ω L → ℝ) (t u : ℝ) : ℝ :=
  backwardLog L T m (perturbLog base D E t u) + 2*n*u^2

noncomputable def correctedPerturbScore {L n : ℕ} (T : KernelTower Ω L) (m : Fin L → ℝ)
    (base : FinitePath Ω L → ℝ) (D E : Fin n → FinitePath Ω L → ℝ) (t u : ℝ) : ℝ :=
  (law L (tilt L T m (perturbLog base D E t u))).expect (perturbScore D E t u) + 4*n*u

end DilutedSpinGlass.KernelTower

namespace DilutedSpinGlass.FiniteLaw
variable {Ω X : Type} [Fintype Ω] [MeasurableSpace X]

theorem measurable_tilt_expect (P : FiniteLaw Ω) (m : ℝ) {f g : X → Ω → ℝ}
    (hf : ∀ a, Measurable (fun x => f x a))
    (hg : ∀ a, Measurable (fun x => g x a)) :
    Measurable (fun x => (P.tilt m (f x)).expect (g x)) := by
  simp_rw [tilt_expect]
  exact (P.measurable_expect (fun a => ((hf a).const_mul m).exp.mul (hg a))).div
    (P.measurable_expect (fun a => ((hf a).const_mul m).exp))

end DilutedSpinGlass.FiniteLaw

namespace DilutedSpinGlass.KernelTower
variable {Ω X : Type} [Fintype Ω] [MeasurableSpace X]

/-- The L1 thermal defect for the literal score of all selected marks. -/
noncomputable def thermalDefect {L n : ℕ} (T : KernelTower Ω L) (m : Fin L → ℝ)
    (base : FinitePath Ω L → ℝ) (D E : Fin n → FinitePath Ω L → ℝ) (t u : ℝ) : ℝ :=
  let P := law L (tilt L T m (perturbLog base D E t u))
  P.expect (fun y => |perturbScore D E t u y-P.expect (perturbScore D E t u)|)

end DilutedSpinGlass.KernelTower

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_MixtureMeasures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
attribute [local instance] DilutedSpinGlass.instMeasurableSpaceCarrier_challenge DilutedSpinGlass.instBorelSpaceCarrier_challenge
namespace DilutedSpinGlass

variable {I : Type*} {X : I → Type*} [MeasurableSpace I]
  [∀ i, MeasurableSpace (X i)]

omit [MeasurableSpace I] in
theorem measurable_sigmaMk (i : I) : Measurable (Sigma.mk i : X i → Sigma X) := by
  rw [measurable_iff_le_map]
  exact iInf_le _ i

variable [DiscreteMeasurableSpace I]

noncomputable def familyKernel (ν : ∀ i, Measure (X i)) : Kernel I (Sigma X) :=
  ⟨fun i => (ν i).map (Sigma.mk i), Measurable.of_discrete⟩

instance familyKernel_markov (ν : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (ν i)] :
    IsMarkovKernel (familyKernel ν) := by
  constructor
  intro i
  change IsProbabilityMeasure ((ν i).map (Sigma.mk i))
  first | exact Measure.isProbabilityMeasure_map (measurable_sigmaMk i).aemeasurable | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)

noncomputable def familyLaw (μ : Measure I) (ν : ∀ i, Measure (X i)) : Measure (Sigma X) :=
  (familyKernel ν) ∘ₘ μ

instance familyLaw_prob (μ : Measure I) [IsProbabilityMeasure μ]
    (ν : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (ν i)] :
    IsProbabilityMeasure (familyLaw μ ν) := by
  unfold familyLaw
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ReservoirVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
attribute [local instance] DilutedSpinGlass.instMeasurableSpaceCarrier_challenge DilutedSpinGlass.instBorelSpaceCarrier_challenge
open Set
namespace DilutedSpinGlass
open _root_.MeasureTheory Set

theorem measurableEmbedding_sigmaMk {I : Type*} {X : I → Type*}
    [∀ i, MeasurableSpace (X i)] (i : I) :
    MeasurableEmbedding (Sigma.mk i : X i → Sigma X) where
  injective := sigma_mk_injective
  measurable := measurable_sigmaMk i
  measurableSet_image' := by
    intro s hs
    change MeasurableSet[⨅ j, (inferInstance : MeasurableSpace (X j)).map (Sigma.mk j)] _
    rw [MeasurableSpace.measurableSet_iInf]
    intro j
    change MeasurableSet ((Sigma.mk j) ⁻¹' (Sigma.mk i '' s))
    by_cases h : j = i
    · subst j
      rw [Set.preimage_image_eq _ sigma_mk_injective]
      exact hs
    · have he : ((Sigma.mk j) ⁻¹' (Sigma.mk i '' s)) = ∅ := by
        ext x
        simp only [mem_preimage,mem_image,mem_empty_iff_false,iff_false,not_exists]
        intro y hy
        exact h (congrArg Sigma.fst hy.2).symm
      rw [he]
      exact MeasurableSet.empty

/-- Countable disjoint root laws retain joint parameter measurability. -/
theorem measurable_sigmaProd {I : Type*} [Countable I] {X : I → Type*}
    [∀ i, MeasurableSpace (X i)] {A Y : Type*} [MeasurableSpace A] [MeasurableSpace Y]
    {f : (i : I) → X i → A → Y}
    (hf : ∀ i, Measurable (fun z : X i × A => f i z.1 z.2)) :
    Measurable (fun z : Sigma X × A => f z.1.1 z.1.2 z.2) := by
  intro s hs
  have he : (fun z : Sigma X × A => f z.1.1 z.1.2 z.2) ⁻¹' s =
      ⋃ i, (Prod.map (Sigma.mk i) id) '' ((fun z : X i × A => f i z.1 z.2) ⁻¹' s) := by
    ext z
    rcases z with ⟨⟨i,x⟩,a⟩
    constructor
    · intro h
      exact mem_iUnion.mpr ⟨i, ⟨(x,a),h,rfl⟩⟩
    · intro h
      rcases mem_iUnion.mp h with ⟨j,w,hw,he⟩
      have hh : (fun z : Sigma X × A => f z.1.1 z.1.2 z.2) (Prod.map (Sigma.mk j) id w) ∈ s := hw
      rw [he] at hh
      exact hh
  rw [he]
  apply MeasurableSet.iUnion
  intro i
  exact ((measurableEmbedding_sigmaMk i).prodMap MeasurableEmbedding.id).measurableSet_image'
    (hf i hs)

end DilutedSpinGlass

namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

noncomputable def rootDeviation (f : X → ℝ) : ℝ := ∫ x, |f x-∫ y, f y ∂μ| ∂μ

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_HeterogeneousMarks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
attribute [local instance] DilutedSpinGlass.instMeasurableSpaceCarrier_challenge DilutedSpinGlass.instBorelSpaceCarrier_challenge
open Set
namespace DilutedSpinGlass.HeterogeneousMarks
open scoped BigOperators
variable {Ω I : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]

/-- The independent auxiliary mark row for the actually realized type list. -/
abbrev Row {k : ℕ} (roots : Fin k → I) := (j : Fin k) → A (roots j)

/-- A product-prior tower on the physical state and all realized marks. -/
noncomputable def tower {k : ℕ} (roots : Fin k → I) : (L : ℕ) →
    KernelTower Ω L → ((i : I) → Fin L → FiniteLaw (A i)) →
    KernelTower (Ω × Row (A := A) roots) L
  | 0, _, _ => ()
  | L+1, T, Q => (T.1.bind (fun _ => FiniteLaw.pi (fun j => Q (roots j) 0)),
      fun y => tower roots L (T.2 y.1) (fun i j => Q i j.succ))

/-- Forget all auxiliary marks. -/
def physical {k : ℕ} (roots : Fin k → I) : (L : ℕ) →
    FinitePath (Ω × Row (A := A) roots) L → FinitePath Ω L
  | 0, _ => ()
  | L+1, y => (y.1.1, physical roots L y.2)

/-- The path of the q-th realized mark, in that mark's own finite space. -/
def mark {k : ℕ} {roots : Fin k → I} (q : Fin k) : (L : ℕ) →
    FinitePath (Ω × Row (A := A) roots) L → FinitePath (A (roots q)) L
  | 0, _ => ()
  | L+1, y => (y.1.2 q, mark q L y.2)

/-- Move one distinguished mark out of the dependent row. -/
def split {k : ℕ} (roots : Fin k → I) (i : I) :
    (Ω × Row (A := A) (Fin.cons i roots)) ≃ ((Ω × Row (A := A) roots) × A i) where
  toFun y := ((y.1, Fin.tail y.2), y.2 0)
  invFun z := (z.1.1, Fin.cons z.2 z.1.2)
  left_inv y := by simp only [Fin.cons_self_tail]
  right_inv z := by
    rcases z with ⟨⟨x, row⟩, a⟩
    rfl

variable {k L : ℕ}

/-- A finite realized row in the full countable-type model. -/
noncomputable def logWeight (base : FinitePath Ω L → ℝ) (roots : Fin k → I)
    (factor : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (y : FinitePath (Ω × Row (A := A) roots) L) : ℝ :=
  base (physical roots L y) + ∑ q, Real.log (factor (roots q) (physical roots L y) (mark q L y))

/-- The insertion keeps the complete original mark row in the base law. -/
noncomputable def insertedLog (base : FinitePath Ω L → ℝ) (roots : Fin k → I)
    (factor : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ) (i : I)
    (y : FinitePath ((Ω × Row (A := A) roots) × A i) L) : ℝ :=
  logWeight base roots factor (KernelTower.pathFst L y) +
    Real.log (factor i (physical roots L (KernelTower.pathFst L y)) (KernelTower.pathSnd L y))

/-- The quenched logarithmic root energy in the actual dependent mark row. -/
noncomputable def root (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i))
    (m : Fin L → ℝ) (base : FinitePath Ω L → ℝ) (roots : Fin k → I)
    (factor : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ) : ℝ :=
  KernelTower.backwardLog L (tower roots L T Q) m (logWeight base roots factor)

end DilutedSpinGlass.HeterogeneousMarks

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_MarkInsertion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
attribute [local instance] DilutedSpinGlass.instMeasurableSpaceCarrier_challenge DilutedSpinGlass.instBorelSpaceCarrier_challenge
open Set
namespace DilutedSpinGlass.HeterogeneousMarks
open scoped BigOperators
variable {Ω I : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]

/-- A relabeling of heterogeneous marks, without identification of their alphabets. -/
def rowPerm {k : ℕ} (roots : Fin k → I) (σ : Equiv.Perm (Fin k)) :
    (Ω × Row (A := A) roots) ≃ (Ω × Row (A := A) (roots ∘ σ)) :=
  (Equiv.refl Ω).prodCongr (Equiv.piCongrLeft (fun q => A (roots q)) σ).symm

variable {k L : ℕ}

/-- The exact tree-score summand for one term of the full reservoir. -/
noncomputable def treeScore (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : FinitePath Ω L → ℝ) (roots : Fin k → I)
    (factor numerator : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ) (q : Fin k) : ℝ :=
  (S.sampleLaw (KernelTower.tilt L (tower roots L T Q) m
    (logWeight base roots factor))).expect (fun x =>
      f (fun b => physical roots L (S.pathAt b x)) *
        (numerator (roots q) (physical roots L (S.pathAt a x)) (mark q L (S.pathAt a x)) /
          factor (roots q) (physical roots L (S.pathAt a x)) (mark q L (S.pathAt a x))))

end DilutedSpinGlass.HeterogeneousMarks



namespace DilutedSpinGlass.HeterogeneousMarks
variable {Ω I : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)] {k L : ℕ}

/-- Add-one score on an old n-factor model with an independent mark process.
The old Gibbs tower includes every one of its original selected-type terms. -/
noncomputable def insertedTreeScore (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : FinitePath Ω L → ℝ) (roots : Fin k → I) (i : I)
    (factor numerator : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ) : ℝ :=
  (S.sampleLaw (KernelTower.tilt L
    (KernelTower.prod L (KernelTower.tilt L (tower roots L T Q) m
      (logWeight base roots factor)) (markPrior L (Q i))) m
    (fun y => Real.log (factor i (physical roots L (KernelTower.pathFst L y))
      (KernelTower.pathSnd L y))))).expect (fun x =>
        f (fun b => physical roots L (KernelTower.pathFst L (S.pathAt b x))) *
          (numerator i (physical roots L (KernelTower.pathFst L (S.pathAt a x)))
            (KernelTower.pathSnd L (S.pathAt a x)) /
            factor i (physical roots L (KernelTower.pathFst L (S.pathAt a x)))
              (KernelTower.pathSnd L (S.pathAt a x))))

end DilutedSpinGlass.HeterogeneousMarks

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_HistoryGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped BigOperators

namespace DilutedSpinGlass.PrescribedTree

/-- The unique labeled position in a unary tree. -/
def singleLeaf : (n : ℕ) → Leaf (single n)
  | 0 => ()
  | n+1 => ⟨0, singleLeaf n⟩

/-- The old paths keep their separate labels when a genuine fresh branch is added. -/
def oldLeaf : {n : ℕ} → (S : PrescribedTree n) → (v : Internal S) →
    Leaf S → Leaf (grow S v)
  | 0, .leaf, v, _ => nomatch v
  | n+1, .node k C, v, a => by
    change Option ((i : Fin k) × Internal (C i)) at v
    cases v with
    | none => exact ⟨a.1.succ, a.2⟩
    | some v =>
      obtain ⟨i,v⟩ := v
      refine ⟨a.1, ?_⟩
      by_cases h : a.1 = i
      · have b : Leaf (C i) := h ▸ a.2
        simpa only [grow, h, Function.update_self] using oldLeaf (C i) v b
      · simpa only [grow, Function.update_of_ne h] using a.2

/-- The single distinguished newly added replica position. -/
def newLeaf : {n : ℕ} → (S : PrescribedTree n) → (v : Internal S) → Leaf (grow S v)
  | 0, .leaf, v => nomatch v
  | n+1, .node k C, v => by
    change Option ((i : Fin k) × Internal (C i)) at v
    cases v with
    | none => exact ⟨0, singleLeaf n⟩
    | some v =>
      obtain ⟨i,v⟩ := v
      refine ⟨i, ?_⟩
      simpa only [grow, Function.update_self] using newLeaf (C i) v

/-- Split depth compares positions, never the sampled spin values. Equal
positions have split depth n; distinct positions split strictly before n. -/
def splitDepth : {n : ℕ} → (S : PrescribedTree n) → Leaf S → Leaf S → ℕ
  | 0, .leaf, _, _ => 0
  | _+1, .node _ C, a, b => if h : a.1 = b.1 then
      1 + splitDepth (C a.1) a.2 (h.symm ▸ b.2) else 0

@[simp] theorem splitDepth_self {n : ℕ} (S : PrescribedTree n) (a : Leaf S) :
    splitDepth S a a = n := by
  induction S with
  | leaf => rfl
  | @node n k C ih => simp [splitDepth, ih, Nat.add_comm]

theorem splitDepth_le {n : ℕ} (S : PrescribedTree n) (a b : Leaf S) :
    splitDepth S a b ≤ n := by
  induction S with
  | leaf => rfl
  | @node n k C ih =>
    rcases a with ⟨i,a⟩
    rcases b with ⟨j,b⟩
    change (if h : i = j then 1 + splitDepth (C i) a (h.symm ▸ b) else 0) ≤ n+1
    split_ifs with h
    · have := ih i a (h.symm ▸ b)
      omega
    · exact Nat.zero_le _

theorem splitDepth_eq_height {n : ℕ} (S : PrescribedTree n) (a b : Leaf S) :
    splitDepth S a b = n ↔ a = b := by
  induction S with
  | leaf => cases a; cases b; exact ⟨fun _ => rfl, fun _ => rfl⟩
  | @node n k C ih =>
    rcases a with ⟨i,a⟩
    rcases b with ⟨j,b⟩
    constructor
    · intro h
      change (if hij : i = j then 1 + splitDepth (C i) a (hij.symm ▸ b) else 0) = n+1 at h
      by_cases hij : i = j
      · subst j
        rw [dite_eq_left rfl] at h
        change 1 + splitDepth (C i) a b = n+1 at h
        have hsub : a = b := (ih i a b).mp (by omega)
        subst b
        rfl
      · rw [dite_eq_right hij] at h
        omega
    · intro hab
      rw [hab]
      exact splitDepth_self _ _

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
noncomputable local instance instDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- The deepest reference prefix and its forbidden reference-containing
children. This describes the whole compatible choice set, including both old
unused leaves and fresh divergences in reference-free subtrees. -/
inductive Divergence : {n : ℕ} → PrescribedTree n → Type
  | here {n : ℕ} {k : ℕ+} {C : Fin k → PrescribedTree n}
      (excluded : Finset (Fin k)) : Divergence (.node k C)
  | descend {n : ℕ} {k : ℕ+} {C : Fin k → PrescribedTree n}
      (i : Fin k) (next : Divergence (C i)) : Divergence (.node k C)

namespace Divergence

def oldAllowed : {n : ℕ} → {S : PrescribedTree n} → Divergence S → Leaf S → Prop
  | _+1, .node _ _, .here J, a => a.1 ∉ J
  | _+1, .node _ _, .descend i D, a => ∃ h : a.1 = i, oldAllowed D (h ▸ a.2)

def freshAllowed : {n : ℕ} → {S : PrescribedTree n} → Divergence S → Internal S → Prop
  | _+1, .node k C, .here J, v =>
      match (v : Option ((i : Fin k) × Internal (C i))) with
      | none => True
      | some ⟨i,_⟩ => i ∉ J
  | _+1, .node k C, .descend i D, v =>
      match (v : Option ((j : Fin k) × Internal (C j))) with
      | none => False
      | some ⟨j,v⟩ => ∃ h : j = i, freshAllowed D (h ▸ v)

noncomputable def coefficient : {n : ℕ} → {S : PrescribedTree n} →
    Divergence S → (Fin (n+1) → ℝ) → ℝ
  | _+1, .node _ _, .here J, m => m 0 - (J.card : ℝ)*m 1
  | _+1, .node _ _, .descend _ D, m => coefficient D (fun j => m j.succ)

end Divergence

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.PrescribedTree
noncomputable local instance instDecidable_1 (p : Prop) : Decidable p := Classical.propDecidable p

/-- Positional split depth of a genuinely fresh branch from an old reference. -/
def freshSplitDepth : {n : ℕ} → (S : PrescribedTree n) → Internal S → Leaf S → ℕ
  | 0, .leaf, v, _ => nomatch v
  | _+1, .node k C, v, a =>
    match (v : Option ((i : Fin k) × Internal (C i))) with
    | none => 0
    | some ⟨i,v⟩ => if h : a.1 = i then 1 + freshSplitDepth (C i) v (h ▸ a.2) else 0

noncomputable def childRefs {n : ℕ} {k : ℕ+} {C : Fin k → PrescribedTree n}
    (R : Finset (Leaf (.node k C))) (i : Fin k) : Finset (Leaf (C i)) :=
  Finset.univ.filter (fun a => (⟨i,a⟩ : Leaf (.node k C)) ∈ R)

@[simp] theorem mem_childRefs {n : ℕ} {k : ℕ+} {C : Fin k → PrescribedTree n}
    (R : Finset (Leaf (.node k C))) (i : Fin k) (a : Leaf (C i)) :
    a ∈ childRefs R i ↔ (⟨i,a⟩ : Leaf (.node k C)) ∈ R := by
  simp [childRefs]

/-- A proposed fresh split at depth d along a reference path. Every child
containing any reference through the chosen prefix is forbidden. -/
noncomputable def referenceDivergence : {n : ℕ} → (S : PrescribedTree n) →
    (a : Leaf S) → (d : ℕ) → d < n → Finset (Leaf S) → Divergence S
  | 0, .leaf, _, d, hd, _ => (Nat.not_lt_zero d hd).elim
  | _+1, .node _ _, _, 0, _, R => .here (R.image (fun a => a.1))
  | n+1, .node _ C, a, d+1, hd, R => .descend a.1
      (referenceDivergence (C a.1) a.2 d (by omega) (childRefs R a.1))

/-- Shared-prefix equations determine the same allowed old-or-fresh set as
references; this positional definition does not examine any spin values. -/
def matchesOldProfile {n : ℕ} (S : PrescribedTree n) (R : Finset (Leaf S))
    (a : Leaf S) (d : ℕ) (b : Leaf S) : Prop :=
  ∀ r ∈ R, splitDepth S b r = min d (splitDepth S a r)

def matchesFreshProfile {n : ℕ} (S : PrescribedTree n) (R : Finset (Leaf S))
    (a : Leaf S) (d : ℕ) (v : Internal S) : Prop :=
  ∀ r ∈ R, freshSplitDepth S v r = min d (splitDepth S a r)

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.PrescribedTree
noncomputable local instance instDecidable_2 (p : Prop) : Decidable p := Classical.propDecidable p

theorem splitDepth_same_child {n : ℕ} {k : ℕ+} (C : Fin k → PrescribedTree n)
    (i : Fin k) (a b : Leaf (C i)) :
    splitDepth (.node k C) ⟨i,a⟩ ⟨i,b⟩ = 1 + splitDepth (C i) a b := by
  change (if h : i = i then 1 + splitDepth (C i) a (h.symm ▸ b) else 0) = _
  simp

theorem splitDepth_diff_child {n : ℕ} {k : ℕ+} (C : Fin k → PrescribedTree n)
    (i j : Fin k) (hij : i ≠ j) (a : Leaf (C i)) (b : Leaf (C j)) :
    splitDepth (.node k C) ⟨i,a⟩ ⟨j,b⟩ = 0 := by
  change (if h : i = j then 1 + splitDepth (C i) a (h.symm ▸ b) else 0) = 0
  rw [dite_eq_right hij]

theorem splitDepth_node_zero {n : ℕ} {k : ℕ+} (C : Fin k → PrescribedTree n)
    (a b : Leaf (.node k C)) :
    splitDepth (.node k C) a b = 0 ↔ a.1 ≠ b.1 := by
  obtain ⟨i,a⟩ := a
  obtain ⟨j,b⟩ := b
  by_cases h : i = j
  · subst j
    rw [splitDepth_same_child]
    simp
  · rw [splitDepth_diff_child C i j h]
    simp [h]

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.PrescribedTree
noncomputable local instance instDecidable_3 (p : Prop) : Decidable p := Classical.propDecidable p

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
noncomputable local instance instDecidable_5 (p : Prop) : Decidable p := Classical.propDecidable p

/-- Reference labels in a particular child, preserving their identities. -/
abbrev ChildLabels {n : ℕ} {k : ℕ+} {C : Fin k → PrescribedTree n}
    {ι : Type} (r : ι → Leaf (.node k C)) (i : Fin k) := {l : ι // (r l).1 = i}

def childLabelLeaf {n : ℕ} {k : ℕ+} {C : Fin k → PrescribedTree n}
    {ι : Type} (r : ι → Leaf (.node k C)) (i : Fin k) (l : ChildLabels r i) : Leaf (C i) :=
  l.property ▸ (r l.val).2

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.PrescribedTree

noncomputable local instance instDecidable_6_rf13f56_1 (p : Prop) : Decidable p := Classical.propDecidable p
theorem splitDepth_lt_of_ne {n : ℕ} (S : PrescribedTree n) (a b : Leaf S) (hab : a ≠ b) :
    splitDepth S a b < n := by
  have hle := splitDepth_le S a b
  have hne : splitDepth S a b ≠ n := fun h => hab ((splitDepth_eq_height S a b).mp h)
  omega

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
noncomputable local instance instDecidable_7 (p : Prop) : Decidable p := Classical.propDecidable p

/-- Full ancestry selector for using an old unused path as the next color. -/
def labeledOldMatch {n : ℕ} (S T : PrescribedTree n) {ι : Type}
    (r : ι → Leaf S) (s : ι → Leaf T) (b : Leaf T) (x : Leaf S) : Prop :=
  ∀ i, splitDepth S x (r i) = splitDepth T b (s i)

/-- Full ancestry selector for a genuinely fresh path as the next color. -/
def labeledFreshMatch {n : ℕ} (S T : PrescribedTree n) {ι : Type}
    (r : ι → Leaf S) (s : ι → Leaf T) (b : Leaf T) (v : Internal S) : Prop :=
  ∀ i, freshSplitDepth S v (r i) = splitDepth T b (s i)

end DilutedSpinGlass.PrescribedTree

end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ActualCharging
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.MarkSelector
open scoped BigOperators

/-- Each mark coordinate is a genuine independent fair Rademacher variable. -/
noncomputable def rademacher : FiniteLaw Bool where
  weight _ := 1 / 2
  nonneg _ := by norm_num
  total := by rw [Fintype.sum_bool]; norm_num

def sign (b : Bool) : ℝ := if b then 1 else -1

@[simp] theorem sign_sq (b : Bool) : sign b * sign b = 1 := by cases b <;> norm_num [sign]
@[simp] theorem abs_sign (b : Bool) : |sign b| = 1 := by cases b <;> norm_num [sign]
@[simp] theorem mean_sign : rademacher.expect sign = 0 := by
  rw [FiniteLaw.expect,Fintype.sum_bool]
  norm_num [rademacher,sign]

end DilutedSpinGlass.MarkSelector

end

end

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
noncomputable local instance (priority := 2000) instDecidableEqLeaf_1 {n : ℕ} (S : PrescribedTree n) : DecidableEq (Leaf S) := Classical.decEq _

/-- The local product of reference factors for k represented children. The
empty and unary induced vertices contribute no factor. -/
noncomputable def branchProduct (x y : ℝ) (k : ℕ) : ℝ :=
  ∏ j ∈ Finset.range (k-1), (x-((j:ℝ)+1)*y)

@[simp] theorem branchProduct_zero (x y : ℝ) : branchProduct x y 0 = 1 := by
  classical
  simp [branchProduct]
@[simp] theorem branchProduct_one (x y : ℝ) : branchProduct x y 1 = 1 := by
  classical
  simp [branchProduct]


noncomputable def partialKappa : {n : ℕ} → (S : PrescribedTree n) →
    (Fin (n+1) → ℝ) → Finset (Leaf S) → ℝ
  | 0, .leaf, _, _ => 1
  | _+1, .node _ C, m, R =>
      branchProduct (m 0) (m 1) (R.image (fun a => a.1)).card *
        ∏ i, partialKappa (C i) (fun j => m j.succ) (childRefs R i)

@[simp] theorem childRefs_empty {n : ℕ} {k : ℕ+} {C : Fin k → PrescribedTree n}
    (i : Fin k) : childRefs (∅ : Finset (Leaf (.node k C))) i = ∅ := by
  classical
  ext a
  rw [mem_childRefs]
  exact iff_of_false (Finset.notMem_empty _) (Finset.notMem_empty _)

@[simp] theorem childRefs_insert_same {n : ℕ} {k : ℕ+} {C : Fin k → PrescribedTree n}
    (R : Finset (Leaf (.node k C))) (i : Fin k) (a : Leaf (C i)) :
    childRefs (insert (⟨i,a⟩ : Leaf (.node k C)) R) i = insert a (childRefs R i) := by
  classical
  ext b
  constructor
  · intro h
    have hh := (mem_childRefs _ i b).mp h
    rcases ((Finset.mem_insert (α := Leaf (.node k C))).mp hh) with hab | hb
    · exact Finset.mem_insert.mpr (Or.inl (eq_of_heq ((Sigma.mk.inj_iff.mp hab).2)))
    · exact Finset.mem_insert.mpr (Or.inr ((mem_childRefs R i b).mpr hb))
  · intro h
    apply (mem_childRefs _ i b).mpr
    rcases Finset.mem_insert.mp h with hab | hb
    · subst b
      exact Finset.mem_insert_self (α := Leaf (.node k C)) _ _
    · exact Finset.mem_insert_of_mem (α := Leaf (.node k C)) ((mem_childRefs R i b).mp hb)

noncomputable local instance (priority := 2000) instDecidableEqSigma_rf13f56_1 {α : Type*} (β : α → Type*) : DecidableEq (Sigma β) := Classical.decEq _
@[simp] theorem childRefs_singleton_same {n : ℕ} {k : ℕ+} {C : Fin k → PrescribedTree n}
    (i : Fin k) (a : Leaf (C i)) :
    childRefs (C := C) ({⟨i,a⟩} : Finset (Leaf (.node k C))) i = {a} := by
  classical
  ext b
  constructor
  · intro h
    have hh := Finset.mem_singleton.mp ((mem_childRefs _ i b).mp h)
    exact Finset.mem_singleton.mpr (eq_of_heq ((Sigma.mk.inj_iff.mp hh).2))
  · intro h
    have hb := Finset.mem_singleton.mp h
    subst b
    exact (mem_childRefs _ i a).mpr (Finset.mem_singleton_self _)

@[simp] theorem partialKappa_empty {n : ℕ} (S : PrescribedTree n)
    (m : Fin (n+1) → ℝ) : partialKappa S m ∅ = 1 := by
  classical
  induction S with
  | leaf => rfl
  | @node n k C ih => simp [partialKappa,ih]

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
noncomputable local instance (priority := 2000) instDecidableEqLeaf_2 {n : ℕ} (S : PrescribedTree n) : DecidableEq (Leaf S) := Classical.decEq _

end DilutedSpinGlass.PrescribedTree

end

end

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
noncomputable local instance instDecidable_10 (p : Prop) : Decidable p := Classical.propDecidable p

/-- Depth and arity refer to the genuine internal vertices, not their sampled values. -/
def vertexDepth : {n : ℕ} → (S : PrescribedTree n) → Internal S → ℕ
  | 0, .leaf, v => nomatch v
  | _+1, .node _ C, v =>
    match (v : Option ((i : _) × Internal (C i))) with
    | none => 0
    | some ⟨i,v⟩ => vertexDepth (C i) v + 1

def vertexArity : {n : ℕ} → (S : PrescribedTree n) → Internal S → ℕ
  | 0, .leaf, v => nomatch v
  | _+1, .node k C, v =>
    match (v : Option ((i : _) × Internal (C i))) with
    | none => k
    | some ⟨i,v⟩ => vertexArity (C i) v

noncomputable def branchingCount : {n : ℕ} → PrescribedTree n → (ℕ → Prop) → ℕ
  | 0, .leaf, _ => 0
  | _+1, .node k C, P => by
      classical
      exact (if P 0 ∧ 1 < (k:ℕ) then 1 else 0) +
        ∑ i, branchingCount (C i) (fun d => P (d+1))

-- Predicates in the count are decidable by classical logic, not extra model data.

@[simp] theorem leaves_single (n : ℕ) : leaves (single n) = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (∑ _i : Fin (1:ℕ+), leaves (single n)) = 1
    simp only [ih, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    rfl

@[simp] theorem branchingCount_single (n : ℕ) (P : ℕ → Prop) :
    branchingCount (single n) P = 0 := by
  classical
  induction n generalizing P with
  | zero => rfl
  | succ n ih =>
    change (if P 0 ∧ 1 < (1:ℕ) then 1 else 0) +
      (∑ _i : Fin (1:ℕ+), branchingCount (single n) (fun d => P (d+1))) = 0
    simp [ih]

/-- Count of vertices at one depth, including unary vertices. -/
noncomputable def depthCount : {n : ℕ} → PrescribedTree n → ℕ → ℕ
  | 0, .leaf, _ => 0
  | _+1, .node _ _, 0 => 1
  | _+1, .node _ C, d+1 => ∑ i, depthCount (C i) d

/-- Equally spaced exponents, with an arbitrary incoming depth. -/
noncomputable def grid (n d L : ℕ) : Fin (n+1) → ℝ := fun i => (d+i.val:ℕ) / (L:ℝ)

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
noncomputable local instance instDecidable_11 (p : Prop) : Decidable p := Classical.propDecidable p

/-- A charged step is precisely the first branching at a designated depth. -/
def charged {n : ℕ} (S : PrescribedTree n) (Q : Finset ℕ) (v : Internal S) : Prop :=
  vertexDepth S v ∈ Q ∧ vertexArity S v = 1

/-- The absolute history sum with a terminal test. The old-leaf multiplier is
exactly the number of eligible leaves (each contributes coefficient one).
Fresh histories keep the genuine grow operation and coefficient at every step. -/
noncomputable def historyMass {L : ℕ} (F : PrescribedTree L → ℝ) :
    ℕ → (S : PrescribedTree L) → ℕ → ℝ
  | 0, S, _ => F S
  | k+1, S, a => (a:ℝ) * historyMass F k S (a-1) +
      ∑ v : Internal S, |gamma S (grid L 0 L) v| * historyMass F k (grow S v) a

/-- Histories having at least b charged steps, preserving their multiplicities. -/
noncomputable def chargeMass {L : ℕ} (Q : Finset ℕ) :
    ℕ → (S : PrescribedTree L) → ℕ → ℕ → ℝ
  | 0, _, _, b => if b = 0 then 1 else 0
  | k+1, S, a, b => (a:ℝ) * chargeMass Q k S (a-1) b +
      ∑ v : Internal S, |gamma S (grid L 0 L) v| *
        chargeMass Q k (grow S v) a (b - if charged S Q v then 1 else 0)

noncomputable def chargeBound (C D : ℝ) : ℕ → ℕ → ℝ
  | 0, b => if b = 0 then 1 else 0
  | k+1, 0 => C * chargeBound C D k 0
  | k+1, b+1 => C * chargeBound C D k (b+1) + D * chargeBound C D k b

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_CavityIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open scoped BigOperators

/-- Keep precisely the bonds meeting the new site at most once. -/
def CavityGood {q N : ℕ} (x : Fin (q+1) → Fin (N+1)) : Prop :=
  ∀ i j, x i=0 → x j=0 → i=j

abbrev CavityIndex (q N : ℕ) :=
  (Fin (q+1) → Fin N) ⊕ (Fin (q+1) × (Fin q → Fin N))

def cavityIndexMap {q N : ℕ} : CavityIndex q N → (Fin (q+1) → Fin (N+1))
  | .inl x => fun i => (x i).succ
  | .inr z => z.1.insertNth 0 (fun i => (z.2 i).succ)

lemma cavityIndexMap_inr_zero_iff {q N : ℕ} (j : Fin (q+1)) (x : Fin q → Fin N)
    (i : Fin (q+1)) : cavityIndexMap (.inr (j,x)) i=0 ↔ i=j := by
  classical
  by_cases h : i=j
  · subst i
    simp [cavityIndexMap]
  · have hh : i ∈ Set.range j.succAbove := by rw [Fin.range_succAbove]; exact h
    obtain ⟨k,rfl⟩ := hh
    simp [cavityIndexMap,Fin.succAbove_ne]

lemma cavityIndexMap_good {q N : ℕ} (z : CavityIndex q N) : CavityGood (cavityIndexMap z) := by
  cases z with
  | inl x => intro i j hi; simp [cavityIndexMap] at hi
  | inr z =>
    intro i j hi hj
    exact (cavityIndexMap_inr_zero_iff _ _ _).mp hi |>.trans
      ((cavityIndexMap_inr_zero_iff _ _ _).mp hj).symm

lemma cavityIndexMap_injective {q N : ℕ} : Function.Injective (@cavityIndexMap q N) := by
  intro a b h
  cases a with
  | inl x =>
    cases b with
    | inl y =>
      congr 1
      funext i
      exact Fin.succ_injective N (congrFun h i)
    | inr z =>
      have hh := congrFun h z.1
      simp [cavityIndexMap] at hh
  | inr z =>
    cases b with
    | inl y =>
      have hh := congrFun h z.1
      simp only [cavityIndexMap,Fin.insertNth_apply_same] at hh
      exact (Fin.succ_ne_zero _ hh.symm).elim
    | inr w =>
      rcases z with ⟨j,x⟩
      rcases w with ⟨k,y⟩
      have hjk : j=k := by
        apply (cavityIndexMap_inr_zero_iff k y j).mp
        rw [← h]
        simp [cavityIndexMap]
      subst k
      congr 2
      funext i
      have hh := congrFun h (j.succAbove i)
      simpa [cavityIndexMap] using hh

lemma cavityIndexMap_surjective_good {q N : ℕ} (x : Fin (q+1) → Fin (N+1))
    (hx : CavityGood x) : ∃ z : CavityIndex q N, cavityIndexMap z=x := by
  classical
  by_cases h : ∃ i,x i=0
  · obtain ⟨j,hj⟩ := h
    have hn (i : Fin q) : x (j.succAbove i)≠0 := by
      intro hi
      exact Fin.succAbove_ne j i (hx _ _ hi hj)
    refine ⟨.inr (j,fun i => (x (j.succAbove i)).pred (hn i)),?_⟩
    funext i
    by_cases he : i=j
    · subst i
      simpa [cavityIndexMap] using hj.symm
    · have hh : i ∈ Set.range j.succAbove := by rw [Fin.range_succAbove]; exact he
      obtain ⟨k,rfl⟩ := hh
      simp [cavityIndexMap]
  · have hn (i : Fin (q+1)) : x i≠0 := fun hi => h ⟨i,hi⟩
    exact ⟨.inl (fun i => (x i).pred (hn i)),funext (fun i => Fin.succ_pred (x i) (hn i))⟩

noncomputable def cavityGoodEquiv (q N : ℕ) : CavityIndex q N ≃ {x // @CavityGood q N x} :=
  Equiv.ofBijective (fun z => ⟨cavityIndexMap z,cavityIndexMap_good z⟩) ⟨
    fun _ _ h => cavityIndexMap_injective (congrArg Subtype.val h),
    fun x => by
      obtain ⟨z,hz⟩ := cavityIndexMap_surjective_good x.val x.property
      exact ⟨z,Subtype.ext hz⟩⟩

noncomputable instance cavityGoodFintype (q N : ℕ) : Fintype {x // @CavityGood q N x} :=
  Fintype.ofFinite _

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_AnchorExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree

variable {Ω : Type} [Fintype Ω]

/-- Unused old positions are a finite family of genuine path projections.
In a canceled-anchor application these are all old leaves except the anchor.
Every already selected color is canceled. -/
noncomputable def anchorEval {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (m : Fin (n+1) → ℝ) (D : FinitePath Ω n → ℝ)
    {ι : Type} (A : Finset ι) (U : ι → Sample Ω S → FinitePath Ω n)
    (G : Sample Ω S → ℝ) (t : ℝ) : ℝ :=
  fullyProtected S T m D (fun x => G x * ∏ i ∈ A, (1+t*D (U i x))) t

/-- Ordered histories for all orders of the canceled-anchor expansion. The
state records precisely which OLD positions remain eligible. -/
noncomputable def anchorIterate {n : ℕ} (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (D : FinitePath Ω n → ℝ) {ι : Type} [DecidableEq ι] :
    ℕ → (S : PrescribedTree n) → (A : Finset ι) →
      (ι → Sample Ω S → FinitePath Ω n) → (Sample Ω S → ℝ) → ℝ → ℝ
  | 0, S, A, U, G, t => anchorEval S T m D A U G t
  | k+1, S, A, U, G, t =>
      (∑ i ∈ A, anchorIterate T m D k S (A.erase i) U (fun x => G x * D (U i x)) t) +
      ∑ v : Internal S, gamma S m v * anchorIterate T m D k (grow S v) A
        (fun i x => U i (oldSample S v x))
        (fun x => G (oldSample S v x) * D (newPath S v x)) t

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.FiniteLaw
variable {Ω : Type} [Fintype Ω]
@[simp] theorem tilt_const (P : FiniteLaw Ω) (m c : ℝ) :
    P.tilt m (fun _ => c) = P := by
  apply weights_ext
  intro x
  simp [tilt, expMoment, expect_const, Real.exp_ne_zero]
end DilutedSpinGlass.FiniteLaw

namespace DilutedSpinGlass.PrescribedTree

/-- A depth-independent bound on derivative order `k`; the total absolute
one-step extension coefficient is the count of eligible old positions plus
all sampled leaves. -/
noncomputable def derivativeBound : ℕ → ℕ → ℝ
  | q, 0 => (2:ℝ)^q
  | q, k+1 => (q:ℝ) * derivativeBound (q+1) k

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.PrescribedTree

@[simp] theorem card_leaf {n : ℕ} (S : PrescribedTree n) : Fintype.card (Leaf S) = leaves S := by
  induction S with
  | leaf =>
    change Fintype.card Unit = 1
    exact Fintype.card_unit
  | @node n k C ih =>
    change Fintype.card ((i : Fin k) × Leaf (C i)) = leaves (.node k C)
    simp [Fintype.card_sigma, leaves, ih]

noncomputable instance leafDecidableEq {n : ℕ} (S : PrescribedTree n) : DecidableEq (Leaf S) :=
  Classical.decEq _

variable {Ω : Type} [Fintype Ω]

/-- The actual anchor expectation in pert:palm-expression, with the prior
kernels updated by the new insertion. `G` includes the numerator score mark. -/
noncomputable def anchorInsertion {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (m : Fin (n+1) → ℝ) (a : Leaf S)
    (G : Sample Ω S → ℝ) (A : FinitePath Ω n → ℝ) : ℝ :=
  (sampleLaw S (KernelTower.tilt n T (fun j => m j.succ) (fun y => Real.log (A y)))).expect
    (fun x => G x / A (pathAt S a x))

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.PrescribedTree
variable {Ω : Type} [Fintype Ω]

/-- The derivative of a canceled-anchor insertion, retaining the actual tree
score and the correction from the canceled denominator. -/
noncomputable def anchorDerivative {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (m : Fin (n+1) → ℝ) (a : Leaf S)
    (G : Sample Ω S → ℝ) (A E : FinitePath Ω n → ℝ) : ℝ :=
  (sampleLaw S (KernelTower.tilt n T (fun j => m j.succ) (fun y => Real.log (A y)))).expect
    (fun x => G x / A (pathAt S a x) *
      (vertexScore S T m (fun y => Real.log (A y)) (fun y => E y / A y) x -
        E (pathAt S a x) / A (pathAt S a x)))

end DilutedSpinGlass.PrescribedTree

open Filter Set
open scoped Topology BigOperators

namespace DilutedSpinGlass.PrescribedTree
variable {Ω : Type} [Fintype Ω]

/-- The literal ordered-history Taylor coefficient of the single anchor.
Only the anchor is initially protected. -/
noncomputable def anchorCoefficient {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (m : Fin (n+1) → ℝ) (D : FinitePath Ω n → ℝ)
    (a : Leaf S) (G : Sample Ω S → ℝ) (k : ℕ) : ℝ :=
  anchorIterate T m D k S (Finset.univ.erase a) (pathAt S) G 0 / (k.factorial:ℝ)

end DilutedSpinGlass.PrescribedTree
end

end

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω Λ : Type}

def sampleFst : {n : ℕ} → (S : PrescribedTree n) → Sample (Ω × Λ) S → Sample Ω S
  | 0, .leaf, _ => ()
  | _+1, .node _ C, x => fun i => ((x i).1.1, sampleFst (C i) (x i).2)

def sampleSnd : {n : ℕ} → (S : PrescribedTree n) → Sample (Ω × Λ) S → Sample Λ S
  | 0, .leaf, _ => ()
  | _+1, .node _ C, x => fun i => ((x i).1.2, sampleSnd (C i) (x i).2)

def samplePair : {n : ℕ} → (S : PrescribedTree n) → Sample Ω S → Sample Λ S → Sample (Ω × Λ) S
  | 0, .leaf, _, _ => ()
  | _+1, .node _ C, x, y => fun i => (((x i).1,(y i).1), samplePair (C i) (x i).2 (y i).2)

@[simp] lemma sampleFst_pair {n : ℕ} (S : PrescribedTree n) (x : Sample Ω S) (y : Sample Λ S) :
    sampleFst S (samplePair S x y) = x := by
  induction S with
  | leaf => change () = x; exact Subsingleton.elim _ _
  | node k C ih =>
    funext i
    change ((x i).1, sampleFst (C i) (samplePair (C i) (x i).2 (y i).2)) = x i
    rw [ih]

@[simp] lemma sampleSnd_pair {n : ℕ} (S : PrescribedTree n) (x : Sample Ω S) (y : Sample Λ S) :
    sampleSnd S (samplePair S x y) = y := by
  induction S with
  | leaf => change () = y; exact Subsingleton.elim _ _
  | node k C ih =>
    funext i
    change ((y i).1, sampleSnd (C i) (samplePair (C i) (x i).2 (y i).2)) = y i
    rw [ih]

@[simp] lemma samplePair_projections {n : ℕ} (S : PrescribedTree n) (x : Sample (Ω × Λ) S) :
    samplePair S (sampleFst S x) (sampleSnd S x) = x := by
  induction S with
  | leaf => change () = x; exact Subsingleton.elim _ _
  | node k C ih =>
    funext i
    change (((x i).1.1,(x i).1.2), samplePair (C i) (sampleFst (C i) (x i).2)
      (sampleSnd (C i) (x i).2)) = x i
    rw [ih]

def sampleProdEquiv {n : ℕ} (S : PrescribedTree n) : Sample (Ω × Λ) S ≃ Sample Ω S × Sample Λ S where
  toFun x := (sampleFst S x, sampleSnd S x)
  invFun x := samplePair S x.1 x.2
  left_inv := samplePair_projections S
  right_inv x := by simp

@[simp] lemma pathAt_sampleFst {n : ℕ} (S : PrescribedTree n) (a : S.Leaf)
    (x : Sample (Ω × Λ) S) : S.pathAt a (sampleFst S x) = KernelTower.pathFst n (S.pathAt a x) := by
  induction S with
  | leaf => rfl
  | node k C ih => exact congrArg (Prod.mk _) (ih a.1 a.2 (x a.1).2)

@[simp] lemma pathAt_sampleSnd {n : ℕ} (S : PrescribedTree n) (a : S.Leaf)
    (x : Sample (Ω × Λ) S) : S.pathAt a (sampleSnd S x) = KernelTower.pathSnd n (S.pathAt a x) := by
  induction S with
  | leaf => rfl
  | node k C ih => exact congrArg (Prod.mk _) (ih a.1 a.2 (x a.1).2)

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_TreeMarkLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators

/-- Every nonroot vertex is retained, including unary vertices. -/
def Edge : {n : ℕ} → PrescribedTree n → Type
  | 0, .leaf => Empty
  | _+1, .node _ C => (i : _) × Option (Edge (C i))

instance edgeFintype : {n : ℕ} → (S : PrescribedTree n) → Fintype (Edge S)
  | 0, .leaf => inferInstanceAs (Fintype Empty)
  | _+1, .node _ C => by
    letI : ∀ i, Fintype (Edge (C i)) := fun i => edgeFintype (C i)
    exact inferInstanceAs (Fintype ((i : _) × Option (Edge (C i))))

def edgeDepth : {n : ℕ} → (S : PrescribedTree n) → Edge S → Fin n
  | 0, .leaf, e => nomatch e
  | _+1, .node k C, e => by
    change (i : Fin k) × Option (Edge (C i)) at e
    obtain ⟨i,e⟩ := e
    cases e with
    | none => exact 0
    | some e => exact (edgeDepth (C i) e).succ

variable {Ω : Type}

def vertexValues : {n : ℕ} → (S : PrescribedTree n) → Sample Ω S → Edge S → Ω
  | 0, .leaf, _, e => nomatch e
  | _+1, .node k C, x, e => by
    change (i : Fin k) × Option (Edge (C i)) at e
    obtain ⟨i,e⟩ := e
    cases e with
    | none => exact (x i).1
    | some e => exact vertexValues (C i) (x i).2 e

def ofVertexValues : {n : ℕ} → (S : PrescribedTree n) → (Edge S → Ω) → Sample Ω S
  | 0, .leaf, _ => ()
  | _+1, .node _ C, v => fun i => (v ⟨i,none⟩, ofVertexValues (C i) (fun e => v ⟨i,some e⟩))

@[simp] lemma vertexValues_of {n : ℕ} (S : PrescribedTree n) (v : Edge S → Ω) :
    vertexValues S (ofVertexValues S v) = v := by
  induction S with
  | leaf => funext e; exact Empty.elim e
  | node k C ih =>
    funext ⟨i,e⟩
    cases e with
    | none => rfl
    | some e => exact congrFun (ih i (fun e => v ⟨i,some e⟩)) e

@[simp] lemma of_vertexValues {n : ℕ} (S : PrescribedTree n) (x : Sample Ω S) :
    ofVertexValues S (vertexValues S x) = x := by
  induction S with
  | leaf => change () = x; exact Subsingleton.elim _ _
  | node k C ih =>
    funext i
    change ((x i).1, ofVertexValues (C i) (vertexValues (C i) (x i).2)) = x i
    rw [ih]

def vertexEquiv {n : ℕ} (S : PrescribedTree n) : Sample Ω S ≃ (Edge S → Ω) where
  toFun := vertexValues S
  invFun := ofVertexValues S
  left_inv := of_vertexValues S
  right_inv := vertexValues_of S

variable [Fintype Ω]
noncomputable local instance treeMarkLawEdgeDecidableEq {n : ℕ}
    (S : PrescribedTree n) : DecidableEq (Edge S) := Classical.decEq _

end DilutedSpinGlass.PrescribedTree
end

end

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω : Type} [Fintype Ω]

noncomputable local instance treeMarkLawPropDecidable_rf13f56_1 (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
@[simp] theorem freshEval_const {n : ℕ} (S : PrescribedTree n)
    (K : KernelTower Ω n) (v : Internal S) (c : ℝ) (x : Sample Ω S) :
    freshEval S K v (fun _ => c) x = c := by
  induction S with
  | leaf => nomatch v
  | @node n k C ih =>
    cases v with
    | none => exact FiniteLaw.expect_const _ _
    | some v => exact ih v.1 (K.2 (x v.1).1) v.2 (x v.1).2


end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ColoredAnchor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
variable {Ω : Type} [Fintype Ω]

/-- All leaves protected, at a general positive insertion, not just along a
single direction. This retains the original finite-kernel law. -/
noncomputable def protectedAt {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (m : Fin (n+1) → ℝ) (G : Sample Ω S → ℝ)
    (A : FinitePath Ω n → ℝ) : ℝ :=
  (sampleLaw S (KernelTower.tilt n T (fun j => m j.succ)
    (fun y => Real.log (A y)))).expect (fun x => G x *
      Real.exp (-leafSum S (fun y => Real.log (A y)) x))

/-- A subset of old positions remains unused. Every used old position and
all fresh colored positions are canceled. -/
noncomputable def anchorAt {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (m : Fin (n+1) → ℝ) {ι : Type} (U : Finset ι)
    (paths : ι → Sample Ω S → FinitePath Ω n) (G : Sample Ω S → ℝ)
    (A : FinitePath Ω n → ℝ) : ℝ :=
  protectedAt S T m (fun x => G x * ∏ i ∈ U, A (paths i x)) A

end DilutedSpinGlass.PrescribedTree
end

end

section
section
namespace DilutedSpinGlass

def pathCoordinate {Ω : Type} : (n : ℕ) → FinitePath Ω n → Fin n → Ω
  | 0, _, i => Fin.elim0 i
  | n+1, x, i => Fin.cases x.1 (pathCoordinate n x.2) i

namespace PrescribedTree

def leafEdge : {n : ℕ} → (S : PrescribedTree n) → Leaf S → Fin n → Edge S
  | 0, .leaf, _, i => Fin.elim0 i
  | _+1, .node _ C, a, i => Fin.cases ⟨a.1,none⟩
      (fun j => ⟨a.1,some (leafEdge (C a.1) a.2 j)⟩) i

@[simp] lemma edgeDepth_leafEdge {n : ℕ} (S : PrescribedTree n) (a : S.Leaf) (i : Fin n) :
    edgeDepth S (leafEdge S a i) = i := by
  induction S with
  | leaf => exact Fin.elim0 i
  | node k C ih =>
    refine Fin.cases rfl (fun j => ?_) i
    exact congrArg Fin.succ (ih a.1 a.2 j)

end PrescribedTree
end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ActualTreeSelector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

namespace DilutedSpinGlass.MarkSelector
open scoped BigOperators

noncomputable def pathColor {C R : Type} [DecidableEq C] [Fintype R] {n : ℕ}
    (a b : R → C) (d : R → Fin n) (c : C) (y : FinitePath (R → Bool) n) : ℝ :=
  ∏ r, (if c = a r then sign (pathCoordinate n y (d r) r) else 1) *
    (if c = b r then sign (pathCoordinate n y (d r) r) else 1)

end DilutedSpinGlass.MarkSelector

end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ColorIterate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped ContDiff

namespace DilutedSpinGlass.PrescribedTree
variable {Ω : Type} [Fintype Ω]

/-- The literal ordered colored extension calculus. Each color either uses
one unused old leaf, which is then removed from the available list, or grows
one fresh branch with its original signed gamma coefficient. -/
noncomputable def coloredAt {n : ℕ} (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    {ι : Type} [DecidableEq ι] : List (FinitePath Ω n → ℝ) →
      (S : PrescribedTree n) → Finset ι → (ι → Sample Ω S → FinitePath Ω n) →
        (Sample Ω S → ℝ) → (FinitePath Ω n → ℝ) → ℝ
  | [], S, U, paths, G, A => anchorAt S T m U paths G A
  | D :: ds, S, U, paths, G, A =>
    (∑ i ∈ U, coloredAt T m ds S (U.erase i) paths (fun x => G x * D (paths i x)) A) +
    ∑ v : Internal S, gamma S m v * coloredAt T m ds (grow S v) U
      (fun i x => paths i (oldSample S v x))
      (fun x => G (oldSample S v x) * D (newPath S v x)) A

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_Polarization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped BigOperators

namespace DilutedSpinGlass.Polarization

def sign (b : Bool) : ℝ := if b then 1 else -1
@[simp] lemma sign_not (b : Bool) : sign (!b) = -sign b := by cases b <;> norm_num [sign]
@[simp] lemma sign_sq (b : Bool) : sign b * sign b = 1 := by cases b <;> norm_num [sign]

variable {ι : Type} [DecidableEq ι]

def flip (j : ι) (ε : ι → Bool) : ι → Bool := Function.update ε j (!ε j)

variable [Fintype ι]

variable {E : Type} [AddCommGroup E] [Module ℝ E]


noncomputable def averageDirection {k : ℕ} (ε : Fin k → Bool) (v : Fin k → E) : E :=
  (k : ℝ)⁻¹ • ∑ j, sign (ε j) • v j

end DilutedSpinGlass.Polarization
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_TreeSampleProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
variable {Ω Λ : Type}

def firstLeaf : {n : ℕ} → (S : PrescribedTree n) → S.Leaf
  | 0, .leaf => ()
  | _+1, .node k C => ⟨⟨0,k.pos⟩, firstLeaf (C ⟨0,k.pos⟩)⟩

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ShapeEmbedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators

/-- Inclusion of an exact prescribed splitting matrix into the actual history
geometry. This is an inclusion of leaf POSITIONS, not of sampled configurations. -/
structure SplitMap {n : ℕ} (T S : PrescribedTree n) where
  leaf : T.Leaf → S.Leaf
  split : ∀ a b, splitDepth S (leaf a) (leaf b) = splitDepth T a b

namespace SplitMap
variable {n : ℕ} {T S : PrescribedTree n}

variable {k l : ℕ+} {C : Fin k → PrescribedTree n} {D : Fin l → PrescribedTree n}

def childIndex (f : SplitMap (.node k C) (.node l D)) (i : Fin k) : Fin l :=
  (f.leaf ⟨i,firstLeaf (C i)⟩).1

lemma rootAgreement (f : SplitMap (.node k C) (.node l D)) (i : Fin k) (a : (C i).Leaf) :
    (f.leaf ⟨i,a⟩).1 = f.childIndex i := by
  by_contra h
  have hz := (splitDepth_node_zero D (f.leaf ⟨i,a⟩) (f.leaf ⟨i,firstLeaf (C i)⟩)).mpr h
  have hs := (splitDepth_same_child C i a (firstLeaf (C i))).symm.trans
    ((f.split ⟨i,a⟩ ⟨i,firstLeaf (C i)⟩).symm.trans hz)
  omega

def childLeaf (f : SplitMap (.node k C) (.node l D)) (i : Fin k) (a : (C i).Leaf) :
    (D (f.childIndex i)).Leaf := f.rootAgreement i a ▸ (f.leaf ⟨i,a⟩).2

lemma leaf_eq_child (f : SplitMap (.node k C) (.node l D)) (i : Fin k) (a : (C i).Leaf) :
    f.leaf ⟨i,a⟩ = ⟨f.childIndex i,f.childLeaf i a⟩ := by
  have h := f.rootAgreement i a
  change f.leaf ⟨i,a⟩ = ⟨f.childIndex i,h ▸ (f.leaf ⟨i,a⟩).2⟩
  generalize f.leaf ⟨i,a⟩ = z at h ⊢
  obtain ⟨j,b⟩ := z
  dsimp at h ⊢
  subst j
  rfl

def child (f : SplitMap (.node k C) (.node l D)) (i : Fin k) :
    SplitMap (C i) (D (f.childIndex i)) where
  leaf := f.childLeaf i
  split a b := by
    have h := f.split ⟨i,a⟩ ⟨i,b⟩
    rw [f.leaf_eq_child i a,f.leaf_eq_child i b,splitDepth_same_child,splitDepth_same_child] at h
    omega

end SplitMap
end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_LabeledColorHistory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω : Type} [Fintype Ω]

/-- The signed ordered history sum, retaining every actual old position and
new branch. The terminal observable may inspect all assigned color positions.
This is only an explicit finite expansion, not an assumed identity. -/
noncomputable def labeledHistory {n : ℕ} {C ι : Type} [DecidableEq C] [DecidableEq ι]
    (m : Fin (n+1) → ℝ)
    (V : (S : PrescribedTree n) → (C → S.Leaf) → (Sample Ω S → ℝ) → ℝ) :
    List C → (S : PrescribedTree n) → Finset ι → (ι → S.Leaf) →
      (C → S.Leaf) → (Sample Ω S → ℝ) → ℝ
  | [], S, _, _, pos, f => V S pos f
  | c::cs, S, U, loc, pos, f =>
      (∑ i ∈ U, labeledHistory m V cs S (U.erase i) loc
        (Function.update pos c (loc i)) f) +
      ∑ v : Internal S, gamma S m v * labeledHistory m V cs (grow S v) U
        (fun i => oldLeaf S v (loc i))
        (Function.update (fun c => oldLeaf S v (pos c)) c (newLeaf S v))
        (fun x => f (oldSample S v x))

end DilutedSpinGlass.PrescribedTree
end

end

section
section

namespace DilutedSpinGlass.KernelTower
variable {Ω : Type} [Fintype Ω]

/-- Two kernel paths share exactly their first d coordinates; the definition
also includes the diagonal endpoint d=n. -/
noncomputable def pairExpect : (n : ℕ) → KernelTower Ω n → ℕ →
    (FinitePath Ω n → FinitePath Ω n → ℝ) → ℝ
  | 0, _, _, f => f () ()
  | n+1, T, 0, f => (law (n+1) T).expect (fun x => (law (n+1) T).expect (f x))
  | n+1, T, d+1, f => T.1.expect (fun x => pairExpect n (T.2 x) d (fun y z => f (x,y) (x,z)))

end DilutedSpinGlass.KernelTower

end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ConcentrationRate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass
open Filter
open scoped Topology

/-- The scale prescribed by the manuscript; no enlarged moment hypothesis is
used in the bounded-model concentration step. -/
noncomputable def scoreScale (N : ℕ) : ℝ := (N:ℝ)^((3:ℝ)/4)
noncomputable def scoreMargin (N : ℕ) : ℝ := (N:ℝ)^(-(1:ℝ)/8)

end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_FiniteProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass
open scoped BigOperators

namespace FiniteLaw
variable {Ω Λ Γ : Type*} [Fintype Ω] [Fintype Λ] [Fintype Γ]

/-- Equality of the finite pushforward law, expressed without choosing a
representation of fibers. -/
def Projects (P : FiniteLaw Ω) (Q : FiniteLaw Λ) (π : Ω → Λ) : Prop :=
  ∀ f : Λ → ℝ, P.expect (fun x => f (π x)) = Q.expect f

end FiniteLaw

namespace KernelTower
variable {Ω Λ : Type} [Fintype Ω] [Fintype Λ]

def pathMap (π : Ω → Λ) : (n : ℕ) → FinitePath Ω n → FinitePath Λ n
  | 0, _ => ()
  | n+1, y => (π y.1,pathMap π n y.2)

/-- A genuine prior-law projection at every vertex, not a conclusion about
weighted roots. -/
def Projects (π : Ω → Λ) : (n : ℕ) → KernelTower Ω n → KernelTower Λ n → Prop
  | 0, _, _ => True
  | n+1, T, U => FiniteLaw.Projects T.1 U.1 π ∧ ∀ a, Projects π n (T.2 a) (U.2 (π a))

omit [Fintype Ω] [Fintype Λ] in
@[simp] theorem terminalState_pathMap (π : Ω → Λ) (r : ℕ) (y : FinitePath Ω (r+1)) :
    terminalState r (pathMap π (r+1) y) = π (terminalState r y) := by
  induction r with
  | zero => rfl
  | succ r ih => exact ih y.2
end KernelTower
end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ShapeMean
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.edgeFintype _root_.OAI.DilutedSpinGlass.PrescribedTree.leafDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

namespace DilutedSpinGlass.PrescribedTree
variable {Ω : Type} [Fintype Ω]

/-- Every descendant leaf receives the same one-site terminal observable,
with its own sampled path. -/
noncomputable def leafProduct : {n : ℕ} → (S : PrescribedTree n) →
    (FinitePath Ω n → ℝ) → Sample Ω S → ℝ
  | 0, .leaf, f, _ => f ()
  | _+1, .node _ C, f, z => ∏ i, leafProduct (C i) (fun y => f ((z i).1,y)) (z i).2

/-- Recursive conditional mean of a descendant spin product. -/
noncomputable def treeMean : {n : ℕ} → (S : PrescribedTree n) → KernelTower Ω n →
    (FinitePath Ω n → ℝ) → ℝ
  | 0, .leaf, _, f => f ()
  | _+1, .node _ C, T, f => ∏ i, T.1.expect (fun a => treeMean (C i) (T.2 a) (fun y => f (a,y)))

/-- One literal unary stretch; it samples one transition from the original
kernel tower rather than introducing independent or replacement disorder. -/
def unary {n : ℕ} (S : PrescribedTree n) : PrescribedTree (n+1) := .node 1 (fun _ => S)

@[simp] theorem treeMean_unary {n : ℕ} (S : PrescribedTree n) (T : KernelTower Ω (n+1))
    (f : FinitePath Ω (n+1) → ℝ) : treeMean (unary S) T f =
      T.1.expect (fun a => treeMean S (T.2 a) (fun y => f (a,y))) := by
  change (∏ _ : Fin 1, T.1.expect (fun a => treeMean S (T.2 a) (fun y => f (a,y)))) = _
  simp

end DilutedSpinGlass.PrescribedTree

end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_HeterogeneousProjection
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.edgeFintype _root_.OAI.DilutedSpinGlass.PrescribedTree.leafDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open scoped BigOperators
variable {Ω Λ I : Type} [Fintype Ω] [Fintype Λ]
  {A : I → Type} [∀ i, Fintype (A i)] {k L : ℕ}

omit [Fintype Ω] [Fintype Λ] [∀ i, Fintype (A i)] in
@[simp] theorem physical_pathMap (π : Ω → Λ) (roots : Fin k → I)
    (y : FinitePath (Ω × Row (A := A) roots) L) :
    physical roots L (KernelTower.pathMap (fun z : Ω × Row (A := A) roots => (π z.1,z.2)) L y) =
      KernelTower.pathMap π L (physical roots L y) := by
  induction L with
  | zero => rfl
  | succ L ih => exact congrArg (fun z => (π y.1.1,z)) (ih y.2)

omit [Fintype Ω] [Fintype Λ] [∀ i, Fintype (A i)] in
@[simp] theorem mark_pathMap (π : Ω → Λ) (roots : Fin k → I) (q : Fin k)
    (y : FinitePath (Ω × Row (A := A) roots) L) :
    mark q L (KernelTower.pathMap (fun z : Ω × Row (A := A) roots => (π z.1,z.2)) L y) =
      mark q L y := by
  induction L with
  | zero => rfl
  | succ L ih => exact congrArg (fun z => (y.1.2 q,z)) (ih y.2)

end DilutedSpinGlass.HeterogeneousMarks
end

end

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω : Type} [Fintype Ω] {N : ℕ}

/-- Covariance energy of one actual child, including its incoming transition.
The rest of the tree has not been sampled or conditioned upon. -/
noncomputable def childEnergy {n : ℕ} (C : PrescribedTree n)
    (T : KernelTower Ω (n+1)) (f : FinitePath Ω (n+1) → Fin N → ℝ) : ℝ :=
  (T.1.bind (fun a => C.sampleLaw (T.2 a))).covarianceEnergy
    (fun z v => C.leafProduct (fun y => f (z.1,y) v) z.2)

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_SplitDepthContinuity
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.edgeFintype _root_.OAI.DilutedSpinGlass.PrescribedTree.leafDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
noncomputable local instance instDecidableSplitDepthContinuity
    (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

/-- Divergence from one referenced leaf, with every old child retained. -/
noncomputable def pairDivergence : {n : ℕ} → (S : PrescribedTree n) →
    S.Leaf → (d : ℕ) → d < n → Divergence S
  | _+1, .node _ _, a, 0, _ => .here {a.1}
  | _+1, .node _ C, a, d+1, hd => .descend a.1 (pairDivergence (C a.1) a.2 d (by omega))

end DilutedSpinGlass.PrescribedTree
end

end

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω : Type} [Fintype Ω] {n : ℕ}

/-- Add an actual unary initial stem, preserving all descendant geometry. -/
def stem (S : PrescribedTree n) : (r : ℕ) → PrescribedTree (n+r)
  | 0 => S
  | r+1 => unary (stem S r)

/-- A literal family with one ranged split. The child shapes and all their
later branching depths are fixed. Moving d delays only this split. -/
def splitFamily (k : ℕ+) (C : Fin k → PrescribedTree n) :
    (r : ℕ) → Fin (r+1) → PrescribedTree (n+r+1)
  | 0, _ => .node k C
  | r+1, d => Fin.cases (.node k (fun i => stem (C i) (r+1)))
      (fun j => unary (splitFamily k C r j)) d

@[simp] lemma splitFamily_zero (k : ℕ+) (C : Fin k → PrescribedTree n) (r : ℕ) :
    splitFamily k C r 0 = .node k (fun i => stem (C i) r) := by
  cases r <;> rfl

@[simp] lemma splitFamily_succ (k : ℕ+) (C : Fin k → PrescribedTree n)
    (r : ℕ) (d : Fin (r+1)) : splitFamily k C (r+1) d.succ = unary (splitFamily k C r d) := rfl

/-- On one real kernel path, retain its prefix and compute the true mean of
its descendant shape. Omitted sampled branches have integrated to one. -/
noncomputable def tailMean (S : PrescribedTree n) : (r : ℕ) → KernelTower Ω (n+r) →
    (FinitePath Ω (n+r) → ℝ) → FinitePath Ω (n+r) → ℝ
  | 0, T, f, _ => treeMean S T f
  | r+1, T, f, x => tailMean S r (T.2 x.1) (fun y => f (x.1,y)) x.2

noncomputable def tailVariance (S : PrescribedTree n) (r : ℕ) (T : KernelTower Ω (n+r))
    (f : FinitePath Ω (n+r) → ℝ) : ℝ :=
  (KernelTower.law (n+r) T).covariance (tailMean S r T f) (tailMean S r T f)

/-- The sum of squared changes of the actual descendant mean when one split
is ranged over ALL available depths, with arbitrary fixed later child shapes. -/
noncomputable def splitShiftEnergy (k : ℕ+) (C : Fin k → PrescribedTree n)
    (r : ℕ) (T : KernelTower Ω (n+r+1)) (f : FinitePath Ω (n+r+1) → ℝ) : ℝ :=
  ∑ d : Fin r, (treeMean (splitFamily k C r d.castSucc) T f -
    treeMean (splitFamily k C r d.succ) T f)^2

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_UniformIndexCoupling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

namespace DilutedSpinGlass.SizeCoupling
open scoped BigOperators

/-- Choose a potential new index uniformly and an independent old fallback.
Only the zero new index uses the fallback; all other old indices coincide. -/
noncomputable def indexLaw (N : ℕ) [NeZero N] : FiniteLaw (Fin (N+1) × Fin N) :=
  FiniteLaw.uniform.bind (fun _ => FiniteLaw.uniform)

def oldIndex {N : ℕ} (z : Fin (N+1) × Fin N) : Fin N := Fin.cases z.2 (fun i => i) z.1

def newIndex {N : ℕ} (z : Fin (N+1) × Fin N) : Fin (N+1) := z.1

end DilutedSpinGlass.SizeCoupling
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_SizeSpinRoot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.SizeCoupling
open scoped BigOperators
open HeterogeneousMarks

/-- Literal finite perturbed spin root with one independent mark prior for each
realized perturbation. The final spin prior is uniform; earlier spin kernels
are dummy point masses. No physical or mark law is replaced. -/
noncomputable def spinRoot {N p k l r : ℕ} {A : Fin l → Type}
    [∀ i, Fintype (A i)]
    (Q : (i : Fin l) → Fin (r+1) → FiniteLaw (A i)) (m : Fin (r+1) → ℝ)
    (theta : Fin k → InteractionSample p) (h : Fin N → ℝ)
    (indices : Fin k → Fin p → Fin N) (sites : Fin l → Fin N)
    (ψ : (i : Fin l) → Spin → FinitePath (A i) (r+1) → ℝ) : ℝ :=
  root (KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform r) Q m
    (fun x => logWeight theta h indices (KernelTower.terminalState r x)) id
    (fun i x a => ψ i (KernelTower.terminalState r x (sites i)) a)

end DilutedSpinGlass.SizeCoupling
end

end

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω : Type} [Fintype Ω] {n : ℕ}

/-- On the SAME full sampled path, the true conditional mean of a fixed
later tree at each depth of its initial unary stretch. -/
noncomputable def stemMeanAt (S : PrescribedTree n) : (r : ℕ) → Fin (r+1) →
    KernelTower Ω (n+r) → (FinitePath Ω (n+r) → ℝ) → FinitePath Ω (n+r) → ℝ
  | 0, _, T, f, _ => treeMean S T f
  | r+1, d, T, f, x => Fin.cases (treeMean (stem S (r+1)) T f)
      (fun e => stemMeanAt S r e (T.2 x.1) (fun y => f (x.1,y)) x.2) d

@[simp] lemma stemMeanAt_zero (S : PrescribedTree n) (r : ℕ) (T : KernelTower Ω (n+r))
    (f : FinitePath Ω (n+r) → ℝ) (x : FinitePath Ω (n+r)) :
    stemMeanAt S r 0 T f x=treeMean (stem S r) T f := by cases r <;> rfl

@[simp] lemma stemMeanAt_succ (S : PrescribedTree n) (r : ℕ) (d : Fin (r+1))
    (T : KernelTower Ω (n+r+1)) (f : FinitePath Ω (n+r+1) → ℝ)
    (x : FinitePath Ω (n+r+1)) :
    stemMeanAt S (r+1) d.succ T f x=
      stemMeanAt S r d (T.2 x.1) (fun y => f (x.1,y)) x.2 := rfl

/-- The actual squared L2 martingale increment at depth d. -/
noncomputable def stemIncrementSq (S : PrescribedTree n) (r : ℕ)
    (T : KernelTower Ω (n+r)) (f : FinitePath Ω (n+r) → ℝ) (d : Fin r) : ℝ :=
  (KernelTower.law (n+r) T).expect (fun x =>
    (stemMeanAt S r d.succ T f x-stemMeanAt S r d.castSucc T f x)^2)

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ActualPrefix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

namespace DilutedSpinGlass.SizeCoupling
open scoped BigOperators

noncomputable def spinMean {N p k l r : ℕ} [NeZero N] {A : Fin l → Type}
    [∀ i, Fintype (A i)]
    (Q : (i : Fin l) → Fin (r+1) → FiniteLaw (A i)) (m : Fin (r+1) → ℝ)
    (theta : Fin k → InteractionSample p) (h : Fin N → ℝ)
    (ψ : (i : Fin l) → Spin → FinitePath (A i) (r+1) → ℝ) : ℝ :=
  (FiniteLaw.pi (fun _ : Fin k => FiniteLaw.pi (fun _ : Fin p =>
      (FiniteLaw.uniform : FiniteLaw (Fin N))))).expect (fun indices =>
    (FiniteLaw.pi (fun _ : Fin l => (FiniteLaw.uniform : FiniteLaw (Fin N)))).expect
      (fun sites => spinRoot Q m theta h indices sites ψ))

end DilutedSpinGlass.SizeCoupling
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_CountedSpinMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.SizeCoupling
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks
open scoped BigOperators NNReal

variable {Z : Type} [MeasurableSpace Z]

variable {X Y I : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    {A : I → Type} [∀ i, Fintype (A i)]

/-- Quenched mean at fixed physical and perturbation counts, under one common
countable type law. Marks retain their own finite alphabets. -/
noncomputable def countedMean (μ : Measure X) (ξ : Measure Y) (ν : Measure I)
    {p r N : ℕ} [NeZero N] (theta : X → InteractionSample p) (field : Y → ℝ)
    (Q : (i : I) → Fin (r+1) → FiniteLaw (A i)) (m : Fin (r+1) → ℝ)
    (ψ : (i : I) → Spin → FinitePath (A i) (r+1) → ℝ) (k l : ℕ) : ℝ :=
  ∫ a : RootPath I l, ∫ x : RootPath X k, ∫ h : RootPath Y N,
    spinMean (fun j => Q (rootArray l a j)) m (fun j => theta (rootArray k x j))
      (fun i => field (rootArray N h i)) (fun j => ψ (rootArray l a j))
      ∂rootLaw N (fun _ => ξ) ∂rootLaw k (fun _ => μ) ∂rootLaw l (fun _ => ν)

end DilutedSpinGlass.SizeCoupling
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_JointRootLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

/-- The actual independent Poisson container of iid root labels. -/
noncomputable def compoundRootLaw {X : Type} [MeasurableSpace X]
    (μ : Measure X) (r : ℝ≥0) : Measure (Sigma (RootPath X)) :=
  familyLaw (poissonMeasure r) (fun k => rootLaw k (fun _ => μ))

instance compoundRootLaw_prob {X : Type} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (r : ℝ≥0) : IsProbabilityMeasure (compoundRootLaw μ r) := by
  unfold compoundRootLaw
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)

theorem measurable_prodSigma {I : Type*} [Countable I] {X : I → Type*}
    [∀ i, MeasurableSpace (X i)] {A Y : Type*} [MeasurableSpace A] [MeasurableSpace Y]
    {f : A → (i : I) → X i → Y}
    (hf : ∀ i, Measurable (fun z : A × X i => f z.1 i z.2)) :
    Measurable (fun z : A × Sigma X => f z.1 z.2.1 z.2.2) := by
  exact (measurable_sigmaProd (f := fun i x a => f a i x) (fun i => (hf i).comp measurable_swap)).comp measurable_swap

variable {X I Y : Type} [MeasurableSpace X] [MeasurableSpace I] [MeasurableSpace Y] {M : ℕ}

abbrev FullRootState (Y X I : Type) (M : ℕ) :=
  RootPath Y M × (Sigma (RootPath X) × Sigma (RootPath I))

noncomputable def fullRootLaw (ξ : Fin M → Measure Y) (μ : Measure X) (ν : Measure I)
    (r s : ℝ≥0) : Measure (FullRootState Y X I M) :=
  (rootLaw M ξ).prod ((compoundRootLaw μ r).prod (compoundRootLaw ν s))

instance fullRootLaw_prob (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure I) [IsProbabilityMeasure ν]
    (r s : ℝ≥0) : IsProbabilityMeasure (fullRootLaw ξ μ ν r s) := by
  unfold fullRootLaw
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)

noncomputable def packRoot (F : RootPath Y M → (k : ℕ) → RootPath X k → (n : ℕ) → RootPath I n → ℝ)
    (z : FullRootState Y X I M) : ℝ := F z.1 z.2.1.1 z.2.1.2 z.2.2.1 z.2.2.2

end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_FinitePiInjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.FiniteLaw
open scoped BigOperators
noncomputable local instance instDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {ι κ : Type*} {α : κ → Type*}

noncomputable def injectionFactor (e : ι → κ) (g : (i : ι) → α (e i) → ℝ)
    (j : κ) (x : α j) : ℝ := by
  classical
  exact if h : ∃ i, e i = j then g (Classical.choose h) ((Classical.choose_spec h).symm ▸ x) else 1

end DilutedSpinGlass.FiniteLaw
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_SpinRootData
attribute [-instance] _root_.OAI.DilutedSpinGlass.compoundRootLaw_prob _root_.OAI.DilutedSpinGlass.fullRootLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PhysicalRoot
open _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
variable {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] {N : ℕ}

/-- Literal physical spin weight, with the independent physical root inputs
kept as a recursive product only for the variance calculation. -/
noncomputable def energy (V : X → (Fin N → Spin) → ℝ) (field : Y → ℝ)
    (h : RootPath Y N) (k : ℕ) (x : RootPath X k) (σ : Fin N → Spin) : ℝ :=
  (∑ j, V (rootArray k x j) σ)+∑ i, field (rootArray N h i)*spin (σ i)

theorem measurable_energy (V : X → (Fin N → Spin) → ℝ) (field : Y → ℝ)
    (hV : ∀ σ, Measurable (fun x => V x σ)) (hh : Measurable field)
    (k : ℕ) (σ : Fin N → Spin) :
    Measurable (fun z : RootPath Y N × RootPath X k => energy V field z.1 k z.2 σ) := by
  apply Measurable.add
  · exact Finset.measurable_sum _ (fun j _ => (hV σ).comp ((measurable_rootArray k j).comp measurable_snd))
  · exact Finset.measurable_sum _ (fun i _ =>
      ((hh.comp ((measurable_rootArray N i).comp measurable_fst))).mul_const _)

end DilutedSpinGlass.PhysicalRoot
end

end

section
section

namespace DilutedSpinGlass.DepthAverage
open scoped BigOperators
noncomputable local instance instDecidable_solutions (p : Prop) : Decidable p := Classical.propDecidable p
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
  {L : ℕ} [NeZero L]

 
noncomputable def depthLaw (α : Type) [Fintype α] [DecidableEq α] (L : ℕ) [NeZero L] :
    FiniteLaw (α → Fin L) := FiniteLaw.pi (fun _ : α => FiniteLaw.uniform)

noncomputable def average (D : (α → Fin L) → Prop) (F : (α → Fin L) → ℝ) : ℝ :=
  (depthLaw α L).expect (fun q => if D q then F q else 0)

noncomputable def coordinateProjection (e : β → α) (τ : β → Equiv.Perm (Fin L))
    (q : α → Fin L) : β → Fin L := fun i => τ i (q (e i))

end DilutedSpinGlass.DepthAverage
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_RegularDepth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.DepthAverage
open scoped BigOperators
noncomputable local instance regularDepthPropDecidable_rf13f56_1 (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
  {L : ℕ} [NeZero L]

noncomputable def normalized (q : Fin L) : ℝ := (q.val:ℝ)/(L:ℝ)

/-- Exactly the separated, interior distinct-coordinate domain of
`decor:average-definition`. Ancestry/order restrictions may further restrict it. -/
def Regular (η : ℝ) (q : α → Fin L) : Prop :=
  (∀ i, η < normalized (q i) ∧ normalized (q i) < 1-η) ∧
  ∀ i j, i ≠ j → η < |normalized (q i)-normalized (q j)|

noncomputable def shiftPerm (s : Bool) : Equiv.Perm (Fin L) :=
  if s then finRotate L else Equiv.refl _

end DilutedSpinGlass.DepthAverage
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_CountedSteps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal
variable {Ω I : Type} {A : I → Type} {L n : ℕ}

/-- Vary only the selected type, not the entire countable reservoir. -/
noncomputable def selectedFactor (sel : I → Bool)
    (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (t u : ℝ) (i : I) (x : FinitePath Ω L) (y : FinitePath (A i) L) : ℝ :=
  if sel i then 1+t*D i x y+u*E i x y else fixed i x y

noncomputable def otherLog (base : FinitePath Ω L → ℝ) (roots : Fin n → I)
    (sel : I → Bool) (fixed : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ) :
    FinitePath (Ω × Row (A := A) roots) L → ℝ :=
  logWeight base roots (fun i x y => if sel i then 1 else fixed i x y)

noncomputable def selectedCoefficient (roots : Fin n → I) (sel : I → Bool)
    (D : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (q : Fin n) (y : FinitePath (Ω × Row (A := A) roots) L) : ℝ :=
  if sel (roots q) then D (roots q) (physical roots L y) (mark q L y) else 0

variable [Fintype Ω] [∀ i, Fintype (A i)]

noncomputable def selectedScore (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i))
    (m : Fin L → ℝ) (base : FinitePath Ω L → ℝ) (roots : Fin n → I)
    (sel : I → Bool) (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (t u : ℝ) : ℝ :=
  (KernelTower.law L (KernelTower.tilt L (tower roots L T Q) m
    (logWeight base roots (selectedFactor sel fixed D E t u)))).expect
      (KernelTower.perturbScore (selectedCoefficient roots sel D) (selectedCoefficient roots sel E) t u)

end DilutedSpinGlass.HeterogeneousMarks
end

end

section
section
namespace DilutedSpinGlass.SizeCoupling
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks
open scoped BigOperators NNReal

variable {X Y I : Type} [MeasurableSpace X] [MeasurableSpace Y]
  [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
  {A : I → Type} [∀ i, Fintype (A i)]

noncomputable def fieldMean (ξ : Measure Y) {p r N k l : ℕ} [NeZero N]
    {B : Fin l → Type} [∀ i, Fintype (B i)]
    (theta : Fin k → InteractionSample p) (field : Y → ℝ)
    (Q : (i : Fin l) → Fin (r+1) → FiniteLaw (B i)) (m : Fin (r+1) → ℝ)
    (ψ : (i : Fin l) → Spin → FinitePath (B i) (r+1) → ℝ) : ℝ :=
  ∫ h : RootPath Y N, spinMean Q m theta (fun i => field (rootArray N h i)) ψ
      ∂rootLaw N (fun _ => ξ)

end DilutedSpinGlass.SizeCoupling
end

end

section
section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal

noncomputable def twoPoissonMean (r s : ℝ≥0) (f : ℕ → ℕ → ℝ) : ℝ :=
  ∫ k, ∫ l, f k l ∂poissonMeasure s ∂poissonMeasure r

end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_PerturbedSizeCoupling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.SizeCoupling
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks
open scoped BigOperators NNReal

variable {X Y I : Type} [MeasurableSpace X] [MeasurableSpace Y]
  [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
  {A : I → Type} [∀ i, Fintype (A i)]

/-- Total (unnormalized) pressure of the literal countable reservoir. The
entropy restores the counting-spin partition function from uniform spins. -/
noncomputable def perturbedMean (μ : Measure X) (ξ : Measure Y) (ν : Measure I)
    {p r N : ℕ} [NeZero N] (theta : X → InteractionSample p) (field : Y → ℝ)
    (Q : (i : I) → Fin (r+1) → FiniteLaw (A i)) (m : Fin (r+1) → ℝ)
    (ψ : (i : I) → Spin → FinitePath (A i) (r+1) → ℝ) (u v : ℝ≥0) : ℝ :=
  N*Real.log 2 + twoPoissonMean u v (countedMean (N := N) μ ξ ν theta field Q m ψ)

end DilutedSpinGlass.SizeCoupling

namespace DilutedSpinGlass
open scoped NNReal

noncomputable def scoreRate (N : ℕ) : ℝ≥0 := ⟨scoreScale N,Real.rpow_nonneg (Nat.cast_nonneg N) _⟩

end DilutedSpinGlass

end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_GeneralRootArrayLaw
attribute [-instance] _root_.OAI.DilutedSpinGlass.compoundRootLaw_prob _root_.OAI.DilutedSpinGlass.fullRootLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory

variable {X : Type} [MeasurableSpace X]

noncomputable def rootArrayEquiv : (n : ℕ) → RootPath X n ≃ᵐ (Fin n → X)
  | 0 => MeasurableEquiv.ofUniqueOfUnique _ _
  | n+1 => ((MeasurableEquiv.refl X).prodCongr (rootArrayEquiv n)).trans
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => X) 0).symm

end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_PhysicalIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal Topology
namespace DilutedSpinGlass

noncomputable def indexAverage {p N k : ℕ} (theta : Fin k → InteractionSample p)
    (h : Fin N → ℝ) : ℝ :=
  (∑ indices : Fin k → Fin p → Fin N, logPartition theta h indices) /
    (Fintype.card (Fin k → Fin p → Fin N):ℝ)


end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_PhysicalAverages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal Topology
namespace DilutedSpinGlass

noncomputable def fieldAverage {p : ℕ} (M : Model p) {N k : ℕ}
    (theta : Fin k → InteractionSample p) : ℝ :=
  ∫ h : Fin N → ℝ, indexAverage theta h ∂Measure.pi (fun _ : Fin N => M.field.toMeasure)

noncomputable def disorderAverage {p : ℕ} (M : Model p) (N k : ℕ) : ℝ :=
  ∫ theta : Fin k → InteractionSample p, fieldAverage M (N := N) theta
    ∂Measure.pi (fun _ : Fin k => M.disorder.toMeasure)

noncomputable def interactionMoment {p : ℕ} (M : Model p) : ℝ :=
  ∫ z : InteractionSample p, ‖z.1‖ ∂M.disorder.toMeasure

noncomputable def fieldMoment {p : ℕ} (M : Model p) : ℝ :=
  ∫ h : ℝ, |h| ∂M.field.toMeasure


end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_SpinBaseComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.FiniteLaw

@[simp] theorem pi_uniform {ι : Type} [Fintype ι] [DecidableEq ι]
    {B : ι → Type} [∀ i, Fintype (B i)] [∀ i, Nonempty (B i)] :
    pi (fun i => (uniform : FiniteLaw (B i))) = (uniform : FiniteLaw ((i : ι) → B i)) := by
  ext x
  simp [pi,uniform,Fintype.card_pi,Finset.prod_inv_distrib]

end DilutedSpinGlass.FiniteLaw

end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ActualNegligible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree

/-- Two independent branches at the designated physical height; all other
levels are unary. The height stays fixed, avoiding transports of spin paths. -/
def forkAt : (n d : ℕ) → d < n → PrescribedTree n
  | 0, _, hd => False.elim (Nat.not_lt_zero _ hd)
  | n+1, 0, _ => .node 2 (fun _ => single n)
  | n+1, d+1, hd => .node 1 (fun _ => forkAt n d (Nat.lt_of_succ_lt_succ hd))

def forkAtLeaf : (n d : ℕ) → (hd : d < n) → Fin 2 → (forkAt n d hd).Leaf
  | 0, _, hd, _ => False.elim (Nat.not_lt_zero _ hd)
  | _+1, 0, _, i => ⟨i,singleLeaf _⟩
  | n+1, d+1, hd, i => ⟨0,forkAtLeaf n d (Nat.lt_of_succ_lt_succ hd) i⟩

def forkAtVertex : (n d : ℕ) → (hd : d < n) → (forkAt n d hd).Internal
  | 0, _, hd => False.elim (Nat.not_lt_zero _ hd)
  | _+1, 0, _ => none
  | n+1, d+1, hd => some ⟨0,forkAtVertex n d (Nat.lt_of_succ_lt_succ hd)⟩

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_FullSelectedRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M : ℕ}

noncomputable def fullSelectedLog
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (sel : I → Bool) (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (t : ℝ) (z : FullRootState Y X I M) (u : ℝ) : ℝ :=
  packRoot (fun h k x n y => root T Q m (base h k x) (rootArray n y)
    (selectedFactor sel fixed D E t u)+(2*u^2)*n) z

noncomputable def fullSelectedScore
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (sel : I → Bool) (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (t : ℝ) (z : FullRootState Y X I M) (u : ℝ) : ℝ :=
  packRoot (fun h k x n y => selectedScore T Q m (base h k x) (rootArray n y) sel fixed D E t u+4*n*u) z

end DilutedSpinGlass.HeterogeneousMarks
end

end

section
section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal

/-- A bounded representative, used only with a proof of AE equality. It does
not impose a pointwise bound on all values of an unrestricted sample space. -/
noncomputable def clipReal (C x : ℝ) : ℝ := max (-C) (min C x)

lemma measurable_clipReal (C : ℝ) : Measurable (clipReal C) :=
  measurable_const.max (measurable_const.min measurable_id)

noncomputable def clipSample {p : ℕ} (C : ℝ) (z : InteractionSample p) : InteractionSample p :=
  (fun σ => clipReal C (z.1 σ),z.2)

lemma measurable_clipSample {p : ℕ} (C : ℝ) : Measurable (clipSample (p := p) C) := by
  apply Measurable.prodMk
  · exact Measurable.of_eval (fun σ => (measurable_clipReal C).comp ((measurable_pi_apply σ).comp measurable_fst))
  · exact measurable_snd

end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ShapeMarginal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree.SplitMap
open scoped BigOperators
variable {Ω : Type}

/-- Delete all unselected branches of an actual history. Unary vertices and
all ancestor coordinates are retained. -/
def pullSample : {n : ℕ} → {T S : PrescribedTree n} →
    SplitMap T S → Sample Ω S → Sample Ω T
  | 0, .leaf, .leaf, _, _ => ()
  | _+1, .node _ _, .node _ _, f, x =>
    fun i => ((x (f.childIndex i)).1,pullSample (f.child i) (x (f.childIndex i)).2)

end DilutedSpinGlass.PrescribedTree.SplitMap
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_SelectorPolarization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω : Type} [Fintype Ω]

/-- The exact signed constrained history sum for an anchored old tree. -/
noncomputable def constrainedHistory {n k : ℕ} {R : Type} [Fintype R] [DecidableEq R]
    (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (a b : R → Option (Fin k)) (d : R → Fin n)
    (spinColor : Option (Fin k) → FinitePath Ω n → ℝ)
    (S : PrescribedTree n) (anchor : S.Leaf) (f : Sample Ω S → ℝ) : ℝ := by
  classical
  exact labeledHistory m (fun S pos f =>
    (S.sampleLaw T).expect (fun x => f x * ∏ c, spinColor c (S.pathAt (pos c) x)) *
    ∏ r, if (d r).val+1 ≤ splitDepth S (pos (a r)) (pos (b r)) then (1:ℝ) else 0)
    (List.ofFn (fun j : Fin k => (some j : Option (Fin k)))).reverse S
    (Finset.univ.erase anchor) id (fun _ => anchor) f

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_FullSelectedThermal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M : ℕ}

noncomputable def fullSelectedThermal
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (sel : I → Bool) (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (t : ℝ) (z : FullRootState Y X I M) (u : ℝ) : ℝ :=
  KernelTower.thermalDefect (tower (rootArray z.2.2.1 z.2.2.2) L T Q) m
    (otherLog (base z.1 z.2.1.1 z.2.1.2) (rootArray z.2.2.1 z.2.2.2) sel fixed)
    (selectedCoefficient (rootArray z.2.2.1 z.2.2.2) sel D)
    (selectedCoefficient (rootArray z.2.2.1 z.2.2.2) sel E) t u

end DilutedSpinGlass.HeterogeneousMarks

end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ActualLowIncrement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.SizeCoupling
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

variable {Z I : Type} [MeasurableSpace Z] [Countable I] [MeasurableSpace I]
  [MeasurableSingletonClass I] {A : I → Type} [∀ i, Fintype (A i)]

noncomputable def parameterMean (π : Measure Z) (ν : Measure I) {p r N : ℕ} [NeZero N]
    (M : Model p) (Q : (i : I) → Fin (r+1) → FiniteLaw (A i)) (m : Fin (r+1) → ℝ)
    (ψ : Z → (i : I) → Spin → FinitePath (A i) (r+1) → ℝ) : ℝ :=
  ∫ z, perturbedMean (N := N) M.disorder.toMeasure M.field.toMeasure ν
    id id Q m (ψ z) (M.alpha*N) (scoreRate N) ∂π

end DilutedSpinGlass.SizeCoupling
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_CompoundPoisson
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- The law of the sum of iid marks with an independent Poisson count. -/
noncomputable def compoundPoisson (r : ℝ≥0) (μ : Measure E) : Measure E :=
  Measure.sum (fun n : ℕ => ENNReal.ofReal (Real.exp (-(r:ℝ))*(r:ℝ)^n/n.factorial) •
    Measure.map (fun x : Fin n → E => ∑ i, x i) (Measure.pi (fun _ : Fin n => μ)))

instance compoundPoisson_prob (r : ℝ≥0) (μ : Measure E) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (compoundPoisson r μ) := by
  constructor
  have hh := (hasSum_one_poissonMeasure r).tsum_eq
  rw [compoundPoisson,Measure.sum_apply _ MeasurableSet.univ]
  have hm : ∀ n : ℕ, (Measure.map (fun x : Fin n → E => ∑ i, x i) (Measure.pi (fun _ : Fin n => μ))) Set.univ = 1 := fun n => by
    rw [Measure.map_apply (by fun_prop) MeasurableSet.univ]
    simp
  simp only [Measure.smul_apply,hm,smul_eq_mul,mul_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) (hasSum_one_poissonMeasure r).summable,hh]
  norm_num

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_PatternComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.BooleanPolynomial
open scoped BigOperators
variable {R : Type} [Fintype R] [DecidableEq R]

noncomputable def truth (b : Bool) : ℝ := if b then 1 else 0
noncomputable def monomial (s : Finset R) (y : R → Bool) : ℝ := ∏ r ∈ s, truth (y r)
noncomputable def coefficient (F : (R → Bool) → ℝ) (s : Finset R) : ℝ :=
  ∑ x : R → Bool, F x * (∏ r ∈ s, if x r then (1:ℝ) else -1) *
    (∏ r ∈ sᶜ, if x r then (0:ℝ) else 1)

end DilutedSpinGlass.BooleanPolynomial
end

end

section
section
open Filter Set
open scoped Topology BigOperators

namespace DilutedSpinGlass

/-- The exact probe sequence of pert:parameters, indexed from zero. -/
noncomputable def extractionProbe (j : ℕ) : ℝ := 1 / ((j:ℝ)+4)

end DilutedSpinGlass
end

end

section
open scoped BigOperators

namespace DilutedSpinGlass.Pattern

/-- The manuscript's ±1 spin, represented by Bool. -/
def sign (s : Bool) : ℝ := if s then 1 else -1

@[simp] theorem abs_sign (s : Bool) : |sign s| = 1 := by cases s <;> norm_num [sign]
@[simp] theorem sign_sq (s : Bool) : sign s ^ 2 = 1 := by cases s <;> norm_num [sign]

noncomputable def character {ι : Type*} (S : Finset ι) (e : ι → Bool) : ℝ := ∏ i ∈ S, sign (e i)

@[simp] theorem abs_character {ι : Type*} (S : Finset ι) (e : ι → Bool) :
    |character S e| = 1 := by simp [character, Finset.abs_prod]

@[simp] theorem character_empty {ι : Type*} (e : ι → Bool) : character ∅ e = 1 := by
  simp [character]

/-- Moments include all replica subsets, not only pair overlaps. -/
noncomputable def moment {ι : Type*} [Fintype ι] [DecidableEq ι] (P : (ι → Bool) → ℝ) (S : Finset ι) : ℝ :=
  ∑ e, P e * character S e

end DilutedSpinGlass.Pattern

namespace DilutedSpinGlass.Pattern

/-- Empirical law of the replica pattern at a uniformly sampled site. -/
noncomputable def empirical {ι : Type*} [Fintype ι] {N : ℕ}
    (σ : Fin N → ι → Bool) (e : ι → Bool) : ℝ := by
  classical
  exact (∑ i : Fin N, if σ i=e then 1 else 0)/(N : ℝ)

end DilutedSpinGlass.Pattern

open _root_.MeasureTheory

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_CompoundSuperposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass
open Set

noncomputable def probeLow (j : ℕ) : ℝ := extractionProbe j ^ (j+4)
noncomputable def probeHigh (j : ℕ) : ℝ := 2*probeLow j

end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_FullSelectedRawConcentration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M : ℕ}

noncomputable def fullSelectedRawScore
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (sel : I → Bool) (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (t : ℝ) (z : FullRootState Y X I M) (u : ℝ) : ℝ :=
  packRoot (fun h k x n y => selectedScore T Q m (base h k x) (rootArray n y) sel fixed D E t u) z

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_TripleMarginal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

namespace DilutedSpinGlass.KernelTower
variable {Ω : Type} [Fintype Ω]
noncomputable def tripleExpectAt : (n : ℕ) → KernelTower Ω n → ℕ →
    (FinitePath Ω n → FinitePath Ω n → FinitePath Ω n → ℝ) → ℝ
  | 0, _, _, F => F () () ()
  | n+1, T, 0, F => (law (n+1) T).expect (fun x => (law (n+1) T).expect
      (fun y => (law (n+1) T).expect (F x y)))
  | n+1, T, d+1, F => T.1.expect (fun z => tripleExpectAt n (T.2 z) d
      (fun x y w => F (z,x) (z,y) (z,w)))

end DilutedSpinGlass.KernelTower

end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_FullThermalAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.KernelTower
variable {Ω : Type} [Fintype Ω] {N : ℕ}

/-- The squared spatial covariance density under the conditional continuation
law after a prefix of length d. This version allows the fixed physical height. -/
noncomputable def prefixEnergyAt : (n : ℕ) → KernelTower Ω n → ℕ →
    (FinitePath Ω n → Fin N → ℝ) → ℝ
  | 0, T, _, X => (law 0 T).covarianceEnergy X
  | n+1, T, 0, X => (law (n+1) T).covarianceEnergy X
  | n+1, T, d+1, X => T.1.expect (fun z => prefixEnergyAt n (T.2 z) d (fun y => X (z,y)))

end DilutedSpinGlass.KernelTower
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_FullSelectedError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M : ℕ}

noncomputable def fullSelectedDeviation
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (sel : I → Bool) (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (t : ℝ) (z : FullRootState Y X I M) (u center : ℝ) : ℝ :=
  let roots := rootArray z.2.2.1 z.2.2.2
  let f := KernelTower.perturbLog (otherLog (base z.1 z.2.1.1 z.2.1.2) roots sel fixed)
    (selectedCoefficient roots sel D) (selectedCoefficient roots sel E) t u
  let g := KernelTower.perturbScore (selectedCoefficient roots sel D) (selectedCoefficient roots sel E) t u
  (KernelTower.law L (KernelTower.tilt L (tower roots L T Q) m f)).expect (fun y => |g y-center|)

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_GlobalSelectedError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M : ℕ}

/-- The literal unnormalised score error from pert:error, with the quenched
center under the entire same-law reservoir disorder. -/
noncomputable def fullSelectedError
    (ξ : Fin M → Measure Y) (μ : Measure X) (ν : Measure I) (r s : ℝ≥0)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (sel : I → Bool) (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (t u : ℝ) : ℝ :=
  ∫ z, fullSelectedDeviation T Q m base sel fixed D E t z u
    (∫ w, fullSelectedRawScore T Q m base sel fixed D E t w u ∂fullRootLaw ξ μ ν r s)
      ∂fullRootLaw ξ μ ν r s

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_HistoryDistinct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {n : ℕ} {C ι : Type} [DecidableEq C] [DecidableEq ι]

structure HistoryValid (S : PrescribedTree n) (U : Finset ι) (loc : ι → S.Leaf)
    (P : Finset C) (pos : C → S.Leaf) : Prop where
  loc_inj : Function.Injective loc
  pos_inj : Set.InjOn pos P
  disjoint : ∀ i ∈ U, ∀ c ∈ P, loc i ≠ pos c

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ProfileHistory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {n : ℕ} {C ι : Type} [DecidableEq C] [DecidableEq ι]

/-- The available original positions and the already assigned colors cover
all current leaves. Previously fresh leaves are assigned, never made available. -/
structure HistoryCover (S : PrescribedTree n) (U : Finset ι) (loc : ι → S.Leaf)
    (P : Finset C) (pos : C → S.Leaf) : Prop extends HistoryValid S U loc P pos where
  cover : ∀ b : S.Leaf, (∃ i ∈ U, b = loc i) ∨ ∃ c ∈ P, b = pos c

end DilutedSpinGlass.PrescribedTree
end

end

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {L : ℕ} {C : Type} [Fintype C] [DecidableEq C]

abbrev SharingIndex (L : ℕ) (C : Type) := C × C × Fin L

def sharingProfile (S : PrescribedTree (L+1)) (pos : C → S.Leaf) : SharingIndex L C → Bool :=
  fun r => decide (r.2.2.val+1 ≤ splitDepth S (pos r.1) (pos r.2.1))

/-- Recover the complete split-depth matrix from interior sharing bits.
The terminal diagonal is known from colors, not from an endpoint mark. -/
def splitFromProfile (y : SharingIndex L C → Bool) (a b : C) : ℕ :=
  if a = b then L+1 else (Finset.univ.filter (fun d : Fin L => y (a,b,d))).card

noncomputable def requirementMap (s : Finset (SharingIndex L C)) :
    Fin (Fintype.card s) → SharingIndex L C := fun j => ((Fintype.equivFin s).symm j).1

variable {Ω : Type} [Fintype Ω] {k : ℕ}

/-- Literal signed extension history with an arbitrary prescribed split-depth
weight. In particular indicator weights encode exact consistent constraints. -/
noncomputable def shapeHistory (T : KernelTower Ω (L+1)) (m : Fin (L+2) → ℝ)
    (F : (Option (Fin k) → Option (Fin k) → ℕ) → ℝ)
    (spinColor : Option (Fin k) → FinitePath Ω (L+1) → ℝ)
    (S : PrescribedTree (L+1)) (anchor : S.Leaf) (f : Sample Ω S → ℝ) : ℝ := by
  classical
  exact labeledHistory m (fun S pos f =>
    (S.sampleLaw T).expect (fun x => f x * ∏ c, spinColor c (S.pathAt (pos c) x)) *
      F (fun a b => splitDepth S (pos a) (pos b)))
    (List.ofFn (fun j : Fin k => (some j : Option (Fin k)))).reverse S
    (Finset.univ.erase anchor) id (fun _ => anchor) f

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_MatrixHistory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω C ι : Type} [Fintype Ω] [Fintype C] [DecidableEq C] [DecidableEq ι] {n : ℕ}

noncomputable local instance matrixHistoryDecidable_rf13f56_1 (p : Prop) : Decidable p :=
  Classical.propDecidable p
/-- The constant-observable component of the analytic COMPLETE-matrix history.
It is the original old-erase/fresh-grow recursion, not the reference recursion. -/
noncomputable def matrixHistory (T : PrescribedTree n) (q : C → T.Leaf)
    (K : KernelTower Ω n) (m : Fin (n+1) → ℝ) (cs : List C)
    (S : PrescribedTree n) (U : Finset ι) (loc : ι → S.Leaf)
    (pos : C → S.Leaf) (f : Sample Ω S → ℝ) : ℝ :=
  labeledHistory m (fun R pos g => if ∀ a b,
    splitDepth R (pos a) (pos b) = splitDepth T (q a) (q b)
    then (R.sampleLaw K).expect g else 0) cs S U loc pos f

end DilutedSpinGlass.PrescribedTree
end

end

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
noncomputable local instance kappaRegularLeafDecidableEq {n : ℕ} (S : PrescribedTree n) :
    DecidableEq S.Leaf := Classical.decEq _

end DilutedSpinGlass.PrescribedTree
end

end

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω : Type} [Fintype Ω] {L : ℕ}

/-- One prescribed pair constraint, retaining the COMPLETE old law. -/
noncomputable def pairHistory (T : KernelTower Ω (L+1)) (m : Fin (L+2) → ℝ)
    (S : PrescribedTree (L+1)) (a : S.Leaf) (d : ℕ)
    (E D : FinitePath Ω (L+1) → ℝ) (f : Sample Ω S → ℝ) : ℝ := by
  classical
  exact (∑ b ∈ Finset.univ.erase a,
    if splitDepth S a b = d then (S.sampleLaw T).expect
      (fun x => f x * (E (S.pathAt a x) * D (S.pathAt b x))) else 0) +
    ∑ v : S.Internal, if splitDepth (grow S v) (oldLeaf S v a) (newLeaf S v) = d then
      gamma S m v * ((grow S v).sampleLaw T).expect
        (fun x => f (oldSample S v x) *
          (E ((grow S v).pathAt (oldLeaf S v a) x) *
            D ((grow S v).pathAt (newLeaf S v) x))) else 0

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_GlobalSelectedAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω : Type} [Fintype Ω] {n : ℕ}

noncomputable local instance pairObservableHistoryDecidable_rf13f56_1 (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
/-- Actual one-new-path history for an arbitrary two-path observable (in
particular the empirical spin overlap). All unused old replicas are retained. -/
noncomputable def pairObservableHistory (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (S : PrescribedTree n) (a : S.Leaf) (d : ℕ)
    (R : FinitePath Ω n → FinitePath Ω n → ℝ) (f : Sample Ω S → ℝ) : ℝ :=
  (∑ b ∈ Finset.univ.erase a,
    if splitDepth S a b = d then (S.sampleLaw T).expect
      (fun x => f x * R (S.pathAt a x) (S.pathAt b x)) else 0) +
    ∑ v : S.Internal, if splitDepth (grow S v) (oldLeaf S v a) (newLeaf S v) = d then
      gamma S m v * ((grow S v).sampleLaw T).expect
        (fun x => f (oldSample S v x) *
          R ((grow S v).pathAt (oldLeaf S v a) x) ((grow S v).pathAt (newLeaf S v) x)) else 0

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ParameterProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory Set
open scoped ENNReal

 
noncomputable def intervalParameterLaw (a b : ℝ) : Measure ℝ := volume[|Icc a b]

end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_PairSquare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω : Type} [Fintype Ω] {n : ℕ}

noncomputable local instance pairSquareDecidable_rf13f56_1 (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
noncomputable def pairFreshCost (S : PrescribedTree n) (m : Fin (n+1) → ℝ)
    (a : S.Leaf) (d : ℕ) (v : S.Internal) : ℝ :=
  if splitDepth (grow S v) (oldLeaf S v a) (newLeaf S v) = d then -gamma S m v else 0

end DilutedSpinGlass.PrescribedTree
end

end

section
section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory Set

 
noncomputable def boundParameter (a b x : ℝ) : ℝ := max a (min b x)

namespace HeterogeneousMarks
open scoped BigOperators NNReal ENNReal
variable {Ω I X Y U : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M : ℕ}

/-- The entire dictionary factor family, with its original two coordinates
and no truncation in the number of types. -/
noncomputable def parameterFactor {J : Type} (key : I → J) (a b t : J → ℝ)
    (D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (u : J → ℝ) (i : I) (x : FinitePath Ω L) (y : FinitePath (A i) L) : ℝ :=
  1+t (key i)*D i x y+boundParameter (a (key i)) (b (key i)) (u (key i))*E i x y

end HeterogeneousMarks
end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_TreeMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.FiniteLaw
open _root_.MeasureTheory
variable {Ω X : Type} [Fintype Ω] [MeasurableSpace X]

theorem measurable_tilt_weight (P : FiniteLaw Ω) (m : ℝ) {f : X → Ω → ℝ}
    (hf : ∀ a, Measurable (fun x => f x a)) (a : Ω) :
    Measurable (fun x => (P.tilt m (f x)).weight a) := by
  change Measurable (fun x => P.weight a * Real.exp (m*f x a) /
    P.expect (fun b => Real.exp (m*f x b)))
  exact (measurable_const.mul ((hf a).const_mul m).exp).div
    (P.measurable_expect (fun b => ((hf b).const_mul m).exp))

end DilutedSpinGlass.FiniteLaw

end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_SelectedTree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M : ℕ}

noncomputable def selectedTreeMean (S : PrescribedTree L)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : FinitePath Ω L → ℝ) {n : ℕ} (roots : Fin n → I)
    (sel : I → Bool) (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (t u : ℝ) (f : (S.Leaf → FinitePath Ω L) → ℝ) : ℝ :=
  (S.sampleLaw (KernelTower.tilt L (tower roots L T Q) m
    (logWeight base roots (selectedFactor sel fixed D E t u)))).expect
    (fun x => f (fun b => physical roots L (S.pathAt b x)))

noncomputable def selectedTreeScore (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : FinitePath Ω L → ℝ) {n : ℕ} (roots : Fin n → I)
    (sel : I → Bool) (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (t u : ℝ) (f : (S.Leaf → FinitePath Ω L) → ℝ) : ℝ :=
  (S.sampleLaw (KernelTower.tilt L (tower roots L T Q) m
    (logWeight base roots (selectedFactor sel fixed D E t u)))).expect
    (fun x => f (fun b => physical roots L (S.pathAt b x)) *
      KernelTower.perturbScore (selectedCoefficient roots sel D)
        (selectedCoefficient roots sel E) t u (S.pathAt a x))

variable (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (sel : I → Bool) (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (t u : ℝ) (f : (S.Leaf → FinitePath Ω L) → ℝ)

noncomputable def fullSelectedTreeMean (z : FullRootState Y X I M) : ℝ :=
  packRoot (fun h k x n y => selectedTreeMean S T Q m (base h k x) (rootArray n y) sel fixed D E t u f) z

noncomputable def fullSelectedTreeScore (z : FullRootState Y X I M) : ℝ :=
  packRoot (fun h k x n y => selectedTreeScore S a T Q m (base h k x) (rootArray n y) sel fixed D E t u f) z

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_SelectedPalm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
variable {Ω I : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)] {L n : ℕ}

noncomputable def selectedNumerator (sel : I → Bool)
    (E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (i : I) (x : FinitePath Ω L) (y : FinitePath (A i) L) : ℝ :=
  if sel i then E i x y else 0

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_FullPalm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
variable {Ω I Z : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [MeasurableSpace Z] {L n : ℕ}

variable [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    (ν : Measure I) [IsProbabilityMeasure ν]

noncomputable def averagedInsertedTreeScore (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : FinitePath Ω L → ℝ) (roots : Fin n → I)
    (factor numerator : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ) : ℝ :=
  ∫ i, insertedTreeScore S a T Q m base roots i factor numerator f ∂ν

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_MatrixNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω C ι : Type} [Fintype Ω] [Fintype C] [DecidableEq C] [DecidableEq ι] {n : ℕ}

noncomputable local instance weightedMatrixHistoryDecidable_rf13f56_1 (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
/-- A complete-matrix history with a general terminal observable. The full
ordered old-erase/fresh-grow history remains literal. -/
noncomputable def weightedMatrixHistory (T : PrescribedTree n) (q : C → T.Leaf)
    (V : (R : PrescribedTree n) → (C → R.Leaf) → (Sample Ω R → ℝ) → ℝ)
    (m : Fin (n+1) → ℝ) (cs : List C)
    (S : PrescribedTree n) (U : Finset ι) (loc : ι → S.Leaf)
    (pos : C → S.Leaf) (f : Sample Ω S → ℝ) : ℝ :=
  labeledHistory m (fun R pos g => if ∀ a b,
    splitDepth R (pos a) (pos b) = splitDepth T (q a) (q b)
    then V R pos g else 0) cs S U loc pos f

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_MatrixPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory
open scoped BigOperators
variable {Ω Z : Type} [Fintype Ω] [MeasurableSpace Z] {n : ℕ}

noncomputable local instance matrixPairRegularityPropDecidable_rf13f56_1 (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition
/-- Total absolute mass controlling one added color, with the entire old tree
left present. The bound is independent of the realized reservoir size. -/
noncomputable def pairHistoryMass (S : PrescribedTree n) (m : Fin (n+1) → ℝ) (a : S.Leaf) : ℝ :=
  ((Finset.univ : Finset S.Leaf).erase a).card + ∑ v : S.Internal, |gamma S m v|

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_SingletonRoot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M : ℕ}

noncomputable def rootTreeMean (S : PrescribedTree L)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (old : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ) (z : FullRootState Y X I M) : ℝ :=
  packRoot (fun h k x n y =>
    (S.sampleLaw (KernelTower.tilt L (tower (rootArray n y) L T Q) m
      (logWeight (base h k x) (rootArray n y) old))).expect
      (fun w => f (fun b => physical (rootArray n y) L (S.pathAt b w)))) z

variable (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure I) [IsProbabilityMeasure ν]
    (r s : ℝ≥0) (S : PrescribedTree L)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (old : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ)

noncomputable def oldTreeAverage : ℝ :=
  ∫ z, rootTreeMean S T Q m base old f z ∂fullRootLaw ξ μ ν r s

end DilutedSpinGlass.HeterogeneousMarks
end

end

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
variable {Ω I J X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I] [DecidableEq J]
    [MeasurableSpace X] [MeasurableSpace Y] {L M : ℕ}

noncomputable def parameterError
    (ξ : Fin M → Measure Y) (μ : Measure X) (ν : Measure I) (r s : ℝ≥0)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (key : I → J) (a b t : J → ℝ)
    (D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (j : J) (u : J → ℝ) : ℝ :=
  fullSelectedError ξ μ ν r s T Q m base (fun i => decide (key i = j))
    (parameterFactor key a b t D E u) D E (t j) (boundParameter (a j) (b j) (u j))

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ParameterRate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M N : ℕ}

abbrev rootAlphabet (z : FullRootState Y X I M) :=
  Ω × Row (A := A) (rootArray z.2.2.1 z.2.2.2)

noncomputable def rootTower (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i))
    (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (old : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (z : FullRootState Y X I M) : KernelTower (rootAlphabet (Ω := Ω) (A := A) z) L :=
  KernelTower.tilt L (tower (rootArray z.2.2.1 z.2.2.2) L T Q) m
    (logWeight (base z.1 z.2.1.1 z.2.1.2) (rootArray z.2.2.1 z.2.2.2) old)

def rootVector (V : FinitePath Ω L → Fin N → ℝ) (z : FullRootState Y X I M) :
    FinitePath (rootAlphabet (Ω := Ω) (A := A) z) L → Fin N → ℝ :=
  fun w => V (physical (rootArray z.2.2.1 z.2.2.2) L w)

noncomputable def rootConditionalEnergy (T : KernelTower Ω L)
    (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (old : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (d : ℕ) (V : FinitePath Ω L → Fin N → ℝ) (z : FullRootState Y X I M) : ℝ :=
  KernelTower.prefixEnergyAt L (rootTower T Q m base old z) d (rootVector V z)

end DilutedSpinGlass.HeterogeneousMarks
end

end

section
section

namespace DilutedSpinGlass.PhysicalRoot
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks Set Filter
open scoped NNReal ENNReal BigOperators Topology
variable {X I : ℕ → Type} {Y J : Type}
  [∀ N, MeasurableSpace (X N)] [MeasurableSpace Y]
  [∀ N, Countable (I N)] [∀ N, MeasurableSpace (I N)] [∀ N, MeasurableSingletonClass (I N)]
  [DecidableEq J] {A : (N : ℕ) → I N → Type} [∀ N i, Fintype (A N i)] {L : ℕ}

/-- The actual globally centered dictionary score error, divided by its type
intensity. The dictionary, sites, and mark alphabets are allowed to vary with N. -/
noncomputable def normalizedParameterError
    (μ : (N : ℕ) → Measure (X N)) (ν : (N : ℕ) → Measure (I N)) (ξ : Measure Y)
    (r : ℕ → ℝ≥0) (V : (N : ℕ) → X N → (Fin N → Spin) → ℝ) (field : Y → ℝ)
    (Q : (N : ℕ) → (i : I N) → Fin (L+1) → FiniteLaw (A N i)) (m : Fin (L+1) → ℝ)
    (key : (N : ℕ) → I N → J) (a b t w : J → ℝ)
    (D E : (N : ℕ) → (i : I N) → FinitePath (Fin N → Spin) (L+1) → FinitePath (A N i) (L+1) → ℝ)
    (j : J) (N : ℕ) (u : J → ℝ) : ℝ :=
  parameterError (fun _ : Fin N => ξ) (μ N) (ν N) (r N)
    ⟨scoreScale N,Real.rpow_nonneg (Nat.cast_nonneg N) _⟩
    (KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L) (Q N) m
    (fun h k x z => energy (V N) field h k x (KernelTower.terminalState L z))
    (key N) a b t (D N) (E N) j u / (w j*scoreScale N)

end DilutedSpinGlass.PhysicalRoot
end

end

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
variable {Ω I : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)] {L n : ℕ}

/-- The old reservoir and the new insertion factor are distinct arguments.
Keeping `old` fixed is essential when extracting a single analytic function
from the entire countable dictionary of insertion parameter values. -/
noncomputable def externalTreeScore (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : FinitePath Ω L → ℝ) (roots : Fin n → I) (i : I)
    (old : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (new numerator : FinitePath Ω L → FinitePath (A i) L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ) : ℝ :=
  (S.sampleLaw (KernelTower.tilt L
    (KernelTower.prod L (KernelTower.tilt L (tower roots L T Q) m
      (logWeight base roots old)) (markPrior L (Q i))) m
    (fun y => Real.log (new (physical roots L (KernelTower.pathFst L y))
      (KernelTower.pathSnd L y))))).expect (fun x =>
        f (fun b => physical roots L (KernelTower.pathFst L (S.pathAt b x))) *
          (numerator (physical roots L (KernelTower.pathFst L (S.pathAt a x)))
            (KernelTower.pathSnd L (S.pathAt a x)) /
            new (physical roots L (KernelTower.pathFst L (S.pathAt a x)))
              (KernelTower.pathSnd L (S.pathAt a x))))

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ConcreteReservoir
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.ConcreteReservoir
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot
open scoped NNReal BigOperators Topology

abbrev Site (N : ℕ) := Fin (max N 1)
instance siteNeZero (N : ℕ) : NeZero (max N 1) := ⟨by omega⟩

/-- N=0 is an irrelevant harmless extension; for every positive N this reads
exactly the spin at the uniformly sampled original site. -/
def readSpin {N : ℕ} (σ : Fin N → Spin) (i : Site N) : Spin :=
  if h : i.val < N then σ ⟨i.val,h⟩ else false

noncomputable def siteLaw (N : ℕ) : Measure (Site N) := (PMF.uniformOfFintype (Site N)).toMeasure
instance siteLaw_probability (N : ℕ) : IsProbabilityMeasure (siteLaw N) := by unfold siteLaw; infer_instance

abbrev Bond (p N : ℕ) := InteractionSample p × (Fin p → Site N)
noncomputable def bondLaw {p : ℕ} (M : Model p) (N : ℕ) : Measure (Bond p N) :=
  M.disorder.toMeasure.prod (PMF.uniformOfFintype (Fin p → Site N)).toMeasure
instance bondLaw_probability {p : ℕ} (M : Model p) (N : ℕ) : IsProbabilityMeasure (bondLaw M N) := by
  unfold bondLaw; infer_instance

noncomputable def boundedPotential {p N : ℕ} (C : ℝ) (z : Bond p N) (σ : Fin N → Spin) : ℝ :=
  clipReal C (z.1.1 (fun l => readSpin σ (z.2 l)))

lemma measurable_boundedPotential {p N : ℕ} (C : ℝ) (σ : Fin N → Spin) :
    Measurable (fun z : Bond p N => boundedPotential C z σ) := by
  apply (measurable_clipReal C).comp
  apply measurable_from_prod_countable_left
  intro indices
  exact (measurable_pi_apply (fun l => readSpin σ (indices l))).comp measurable_fst

variable {K : Type} [Countable K] [MeasurableSpace K] [MeasurableSingletonClass K] [DecidableEq K]
  {A : K → Type} [∀ q, Fintype (A q)] {L p : ℕ}
  (ν : Measure (K×ℕ)) [IsProbabilityMeasure ν]
  (Q : (q : K) → Fin (L+1) → FiniteLaw (A q)) (m : Fin (L+1) → ℝ)
  (D E : (q : K) → Spin → FinitePath (A q) (L+1) → ℝ)

noncomputable def markLaw (N : ℕ) : Measure ((K×ℕ)×Site N) := ν.prod (siteLaw N)
instance markLaw_probability (N : ℕ) : IsProbabilityMeasure (markLaw ν N) := by unfold markLaw; infer_instance

noncomputable def siteObservable
    (D : (q : K) → Spin → FinitePath (A q) (L+1) → ℝ) (N : ℕ)
    (i : (K×ℕ)×Site N) (x : FinitePath (Fin N → Spin) (L+1)) (y : FinitePath (A i.1.1) (L+1)) : ℝ :=
  D i.1.1 (readSpin (KernelTower.terminalState L x) i.2) y

/-- Literal full-root globally centered score for the physical iid-uniform
Poisson reservoir, with bounded representatives equal to the original bounded
physical variables almost surely. Every old dictionary term remains present. -/
noncomputable def scoreError (M : Model p) (C H : ℝ) (j : K×ℕ) (N : ℕ) (u : K×ℕ → ℝ) : ℝ :=
  normalizedParameterError (bondLaw M) (markLaw ν) M.field.toMeasure (fun N => M.alpha*N)
    (fun _ => boundedPotential C) (clipReal H) (fun _ i => Q i.1.1) m (fun _ => Prod.fst)
    (fun i => probeLow i.2) (fun i => probeHigh i.2) (fun i => extractionProbe i.2)
    (fun i => ν.real {i}) (siteObservable D) (siteObservable E) j N u

end DilutedSpinGlass.ConcreteReservoir
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_UniformRootDecorrelation
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory
open scoped BigOperators
variable {Z : Type} [MeasurableSpace Z] (μ : Measure Z) [IsProbabilityMeasure μ]
    (Ω : Z → Type) [∀ z, Fintype (Ω z)] (n d N : ℕ)
    (T : (z : Z) → KernelTower (Ω z) n)
    (X : (z : Z) → FinitePath (Ω z) n → Fin N → ℝ)
    (m : Fin (n+1) → ℝ) (S : PrescribedTree n) (a b : S.Leaf)

noncomputable def pairRootMean : ℝ :=
  ∫ z, (S.sampleLaw (T z)).expect (fun x =>
    FiniteLaw.dot (X z (S.pathAt a x)) (X z (S.pathAt b x))) ∂μ

noncomputable def pairRootCovariance : ℝ :=
  (∫ z, pairObservableHistory (T z) m S a d
    (fun x y => FiniteLaw.dot (X z x) (X z y))
    (fun x => FiniteLaw.dot (X z (S.pathAt a x)) (X z (S.pathAt b x))) ∂μ) -
  pairRootMean μ Ω n N T X S a b *
    (∫ z, pairObservableHistory (T z) m S a d
      (fun x y => FiniteLaw.dot (X z x) (X z y)) (fun _ => 1) ∂μ)

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ExternalTaylor
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory PrescribedTree
open scoped NNReal BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M N : ℕ}

noncomputable def rootPairObservable (T : KernelTower Ω L)
    (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (old : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (S : PrescribedTree L) (a : S.Leaf) (d : ℕ)
    (R : FinitePath Ω L → FinitePath Ω L → ℝ) (f : (S.Leaf → FinitePath Ω L) → ℝ)
    (z : FullRootState Y X I M) : ℝ :=
  pairObservableHistory (rootTower T Q (fun j => m j.succ) base old z) m S a d
    (fun x y => R (physical (rootArray z.2.2.1 z.2.2.2) L x) (physical (rootArray z.2.2.1 z.2.2.2) L y))
    (fun x => f (fun b => physical (rootArray z.2.2.1 z.2.2.2) L (S.pathAt b x)))

end DilutedSpinGlass.HeterogeneousMarks
end

end

section
section

namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory
open scoped BigOperators
variable {Ω I Z : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [MeasurableSpace Z] {L n : ℕ}

noncomputable def externalCoefficient (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (base : FinitePath Ω L → ℝ) (roots : Fin n → I) (i : I)
    (old : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (D E : FinitePath Ω L → FinitePath (A i) L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ) (k : ℕ) : ℝ :=
  PrescribedTree.anchorCoefficient S
    (KernelTower.prod L (KernelTower.tilt L (tower roots L T Q) (fun j => m j.succ)
      (logWeight base roots old)) (markPrior L (Q i))) m
    (fun y => D (physical roots L (KernelTower.pathFst L y)) (KernelTower.pathSnd L y)) a
    (fun x => f (fun b => physical roots L (KernelTower.pathFst L (S.pathAt b x))) *
      E (physical roots L (KernelTower.pathFst L (S.pathAt a x)))
        (KernelTower.pathSnd L (S.pathAt a x))) k

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_FullRootPalm
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M : ℕ}
    (ν : Measure I) [IsProbabilityMeasure ν]

noncomputable def fullInsertedTreeScore (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (factor numerator : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ) (z : FullRootState Y X I M) : ℝ :=
  packRoot (fun h k x n y => averagedInsertedTreeScore ν S a T Q m (base h k x) (rootArray n y) factor numerator f) z

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ExternalRoot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.ConcreteReservoir
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot
open scoped NNReal BigOperators Topology
variable {K : Type} [Countable K] [MeasurableSpace K] [MeasurableSingletonClass K] [DecidableEq K]
  {A : K → Type} [∀ q, Fintype (A q)] {L p : ℕ}
  (ν : Measure (K×ℕ)) [IsProbabilityMeasure ν]
  (Q : (q : K) → Fin (L+1) → FiniteLaw (A q)) (m : Fin (L+1) → ℝ)
  (D E : (q : K) → Spin → FinitePath (A q) (L+1) → ℝ)

noncomputable def spinFactor (u : K×ℕ → ℝ) (i : K×ℕ) (σ : Spin) (y : FinitePath (A i.1) (L+1)) : ℝ :=
  1+extractionProbe i.2*D i.1 σ y+boundParameter (probeLow i.2) (probeHigh i.2) (u i)*E i.1 σ y

/-- The increment of the actual quenched physical system with the complete
Poisson dictionary, not a pressure-rate proxy. Its size is N+1. -/
noncomputable def increment (M : Model p) (N : ℕ) (u : K×ℕ → ℝ) : ℝ :=
  SizeCoupling.perturbedMean (N := N+2) M.disorder.toMeasure M.field.toMeasure ν id id
    (fun i => Q i.1) m (spinFactor D E u) (M.alpha*(N+2)) (scoreRate (N+2)) -
  SizeCoupling.perturbedMean (N := N+1) M.disorder.toMeasure M.field.toMeasure ν id id
    (fun i => Q i.1) m (spinFactor D E u) (M.alpha*(N+1)) (scoreRate (N+1))

end DilutedSpinGlass.ConcreteReservoir
end

end

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M : ℕ}

/-- A fresh independent insertion, retaining every original mark in `z`.
The arguments `old` and `new` are intentionally distinct. -/
noncomputable def rootExternalTreeScore (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (old new E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ) (z : FullRootState Y X I M) (i : I) : ℝ :=
  packRoot (fun h k x n y => externalTreeScore S a T Q m (base h k x) (rootArray n y) i old (new i) (E i) f) z

noncomputable def rootExternalCoefficient (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (old D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ) (j : ℕ) (z : FullRootState Y X I M) (i : I) : ℝ :=
  packRoot (fun h k x n y => externalCoefficient S a T Q m (base h k x) (rootArray n y) i old (D i) (E i) f j) z

variable (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν η : Measure I) [IsProbabilityMeasure ν] [IsProbabilityMeasure η]
    (r s : ℝ≥0) (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (old D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ)

noncomputable def externalAverage (t u : ℝ) : ℝ :=
  ∫ z : FullRootState Y X I M × I, rootExternalTreeScore S a T Q (fun j => m j.succ) base old
    (fun i x y => 1+t*D i x y+u*E i x y) E f z.1 z.2 ∂(fullRootLaw ξ μ ν r s).prod η

noncomputable def externalCoefficientAverage (j : ℕ) : ℝ :=
  ∫ z : FullRootState Y X I M × I, rootExternalCoefficient S a T Q m base old D E f j z.1 z.2
    ∂(fullRootLaw ξ μ ν r s).prod η

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ConcreteSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.ConcreteReservoir
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot Filter Set
open scoped NNReal BigOperators Topology
variable {K : Type} [Countable K] [MeasurableSpace K] [MeasurableSingletonClass K] [DecidableEq K]
  {A : K → Type} [∀ q, Fintype (A q)] {L p : ℕ}
  (ν : Measure (K×ℕ)) [IsProbabilityMeasure ν]
  (Q : (q : K) → Fin (L+1) → FiniteLaw (A q)) (m : Fin (L+1) → ℝ)
  (D E : (q : K) → Spin → FinitePath (A q) (L+1) → ℝ)

noncomputable def clipParameters (u : K×ℕ → ℝ) (i : K×ℕ) : ℝ :=
  boundParameter (probeLow i.2) (probeHigh i.2) (u i)

end DilutedSpinGlass.ConcreteReservoir
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ExternalCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M : ℕ}
variable (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν η : Measure I) [IsProbabilityMeasure ν] [IsProbabilityMeasure η]
    (r s : ℝ≥0) (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (old D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ)

 
noncomputable def externalCovariance (t u : ℝ) : ℝ :=
  externalAverage ξ μ ν η r s S a T Q m base old D E f t u -
    oldTreeAverage ξ μ ν r s S T Q (fun j => m j.succ) base old f *
      externalAverage ξ μ ν η r s S a T Q m base old D E (fun _ => 1) t u

noncomputable def covarianceCoefficient (k : ℕ) : ℝ :=
  externalCoefficientAverage ξ μ ν η r s S a T Q m base old D E f k -
    oldTreeAverage ξ μ ν r s S T Q (fun j => m j.succ) base old f *
      externalCoefficientAverage ξ μ ν η r s S a T Q m base old D E (fun _ => 1) k

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_DictionaryAnalytic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators
variable {Ω K Z X Y : Type} [Fintype Ω]
    [Countable K] [MeasurableSpace K] [MeasurableSingletonClass K] [DecidableEq K]
    [Countable Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
    [MeasurableSpace X] [MeasurableSpace Y] {L M : ℕ}
    {A : K → Type} [∀ i, Fintype (A i)]
    (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure (K×ℕ)) [IsProbabilityMeasure ν]
    (τ : Measure Z) [IsProbabilityMeasure τ] (r s : ℝ≥0) (S : PrescribedTree L) (anchor : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : K) → Fin L → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (D E : (i : K) → Z → FinitePath Ω L → FinitePath (A i) L → ℝ)

noncomputable def dictionaryFactor (u : K×ℕ → ℝ) :
    (i : (K×ℕ)×Z) → FinitePath Ω L → FinitePath (A i.1.1) L → ℝ :=
  parameterFactor Prod.fst (fun i => probeLow i.2) (fun i => probeHigh i.2)
    (fun i => extractionProbe i.2) (fun i => D i.1.1 i.2) (fun i => E i.1.1 i.2) u

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_MatrixRoot
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory
open scoped BigOperators Classical
variable {Ω C : Type} [Fintype Ω] [Fintype C] [DecidableEq C] {L N : ℕ}

noncomputable def matrixObservableHistory (T : PrescribedTree L) (q : C → T.Leaf)
    (K : KernelTower Ω L) (m : Fin (L+1) → ℝ) (cs : List C) (S : PrescribedTree L)
    (x : S.Leaf) (A : (C → FinitePath Ω L) → ℝ) (f : Sample Ω S → ℝ) : ℝ :=
  weightedMatrixHistory T q
    (fun D pos g => (D.sampleLaw K).expect (fun z => g z*A (fun b => D.pathAt (pos b) z)))
    m cs S (Finset.univ.erase x) id (fun _ => x) f

noncomputable def matrixProjectionError (T : PrescribedTree L) (q : C → T.Leaf)
    (K : KernelTower Ω L) (a c : C) (A : (C → FinitePath Ω L) → ℝ)
    (X : FinitePath Ω L → Fin N → ℝ) : ℝ :=
  (T.sampleLaw K).l2 (fun z => A (fun b => T.pathAt (q b) z)-
    FiniteLaw.dot (X (T.pathAt (q a) z)) (X (T.pathAt (q c) z)))

noncomputable def oldProjectionError (S : PrescribedTree L) (K : KernelTower Ω L)
    (x y : S.Leaf) (f : Sample Ω S → ℝ) (X : FinitePath Ω L → Fin N → ℝ) : ℝ :=
  (S.sampleLaw K).l2 (fun z => FiniteLaw.dot (X (S.pathAt x z)) (X (S.pathAt y z))-f z)

noncomputable def shiftedCharge (Q : Finset ℕ) (T S : PrescribedTree L) (k : ℕ) : ℝ :=
  chargeBound (2*(leaves S+k:ℕ)) ((Q.card:ℝ)*(leaves S+k:ℕ)) k (branchingCount T (· ∈ Q)) *
    (L:ℝ)⁻¹^(branchingCount T (· ∈ Q))

section Root
variable {Z : Type} [MeasurableSpace Z] (μ : Measure Z) [IsProbabilityMeasure μ]
    (Ω : Z → Type) [∀ z, Fintype (Ω z)]
    (T S : PrescribedTree L) (q : C → T.Leaf)
    (K : (z : Z) → KernelTower (Ω z) L) (m : Fin (L+1) → ℝ) (cs : List C)
    (x : S.Leaf) (A : (z : Z) → (C → FinitePath (Ω z) L) → ℝ)
    (f : (z : Z) → Sample (Ω z) S → ℝ)

noncomputable def matrixRootCovariance : ℝ :=
  (∫ z, matrixObservableHistory T q (K z) m cs S x (A z) (f z) ∂μ) -
  (∫ z, (S.sampleLaw (K z)).expect (f z) ∂μ) *
    (∫ z, matrixObservableHistory T q (K z) m cs S x (A z) (fun _ => 1) ∂μ)

end Root

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_MatrixTriple
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.KernelTower
variable {Ω : Type} [Fintype Ω] {N : ℕ}

/-- The actual half squared three-copy contraction difference. Unlike
covariance energy this retains the positive conditional-mean contribution. -/
noncomputable def halfTripleDifferenceAt (n : ℕ) (T : KernelTower Ω n) (d : ℕ)
    (X : FinitePath Ω n → Fin N → ℝ) : ℝ :=
  (1/2:ℝ)*tripleExpectAt n T d
    (fun x y z => (FiniteLaw.dot (X x) (X y)-FiniteLaw.dot (X x) (X z))^2)

end DilutedSpinGlass.KernelTower

end

end

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators

noncomputable local instance kappaLowerDecidable_rf13f56_1 (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition
/-- Higher-degree factors, after removing the one grid increment per branching vertex. -/
noncomputable def branchExcess : {n : ℕ} → PrescribedTree n → ℕ
  | 0, .leaf => 0
  | _+1, .node k C => (k:ℕ)-2 + ∑ i, branchExcess (C i)

/-- Every vertex with at least three children has its higher-degree reference
factors bounded away from zero. Binary vertices need only the grid increment. -/
noncomputable def BranchRegular : {n : ℕ} → PrescribedTree n → (Fin (n+1) → ℝ) → ℝ → Prop
  | 0, .leaf, _, _ => True
  | _+1, .node k C, m, η => (2 < (k:ℕ) → η ≤ m 1) ∧
      ∀ i, BranchRegular (C i) (fun j => m j.succ) η

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_RootMatrixTriple
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.FiniteLaw
open scoped BigOperators
variable {Ω : Type*} [Fintype Ω] {N : ℕ}

noncomputable def pairProjectionSq (P : FiniteLaw Ω) (X Y : Ω → Fin N → ℝ) : ℝ :=
  P.expect (fun x => P.expect (fun y => (dot (X x) (X y)-dot (Y x) (Y y))^2))

end DilutedSpinGlass.FiniteLaw
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ShapeProjectionEnergy
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
variable {Ω : Type} [Fintype Ω] {N n : ℕ}

/-- The error is measured in the genuine two-copy branch law, in the same
coupling as the physical spin products, not in a surrogate law. -/
noncomputable def branchProjectionSq (C : PrescribedTree n) (T : KernelTower Ω (n+1))
    (a : C.Leaf) (f Y : FinitePath Ω (n+1) → Fin N → ℝ) : ℝ :=
  (T.1.bind (fun z => C.sampleLaw (T.2 z))).pairProjectionSq
    (fun z i => C.leafProduct (fun w => f (z.1,w) i) z.2)
    (fun z => Y (z.1,C.pathAt a z.2))

/-- Conditional covariance of the actual shape with d preceding unary
transitions, averaged over their genuine kernel prefix. -/
noncomputable def shapeEnergyAt (C : PrescribedTree n) : (d : ℕ) →
    KernelTower Ω (n+1+d) → (FinitePath Ω (n+1+d) → Fin N → ℝ) → ℝ
  | 0, T, f => childEnergy C T f
  | d+1, T, f => T.1.expect (fun z => shapeEnergyAt C d (T.2 z) (fun y => f (z,y)))

noncomputable def shapeProjectionSqAt (C : PrescribedTree n) (a : C.Leaf) : (d : ℕ) →
    KernelTower Ω (n+1+d) → (FinitePath Ω (n+1+d) → Fin N → ℝ) →
      (FinitePath Ω (n+1+d) → Fin N → ℝ) → ℝ
  | 0, T, f, Y => branchProjectionSq C T a f Y
  | d+1, T, f, Y => T.1.expect (fun z =>
      shapeProjectionSqAt C a d (T.2 z) (fun y => f (z,y)) (fun y => Y (z,y)))

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ShiftedTree
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
noncomputable local instance shiftedTreeDecidable (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition

/-- Extending the final unary edge keeps every internal branching depth.
In contrast, `unary S` delays all of them by exactly one. -/
def bottomUnary : {n : ℕ} → PrescribedTree n → PrescribedTree (n+1)
  | 0, .leaf => unary .leaf
  | _+1, .node k C => .node k (fun i => bottomUnary (C i))

noncomputable def branchingDepths {n : ℕ} (S : PrescribedTree n) : Finset ℕ := by
  classical
  exact (Finset.univ.filter (fun v => 1 < vertexArity S v)).image (vertexDepth S)

/-- Both copies are aligned, but the two occurrences are different vertices. -/
def doubled {n : ℕ} (S : PrescribedTree n) : PrescribedTree (n+1) := .node 2 (fun _ => S)

noncomputable def shiftedTwinDepths {n : ℕ} (S : PrescribedTree n) : Finset ℕ :=
  (branchingDepths S).image (fun d => d+2)

/-- Regular depth assignments imply this no-adjacent-depth condition once
eta L > 1. It is precisely the geometric premise of shifted charging. -/
def NoAdjacentBranchDepths {n : ℕ} (S : PrescribedTree n) : Prop :=
  ∀ a ∈ branchingDepths S, ∀ b ∈ branchingDepths S, a+1 ≠ b

end DilutedSpinGlass.PrescribedTree
end

end

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω : Type} [Fintype Ω] {N n : ℕ}

/-- Retain a specified descendant leaf through the actual unary prefix. -/
def stemLeaf (S : PrescribedTree n) : (r : ℕ) → S.Leaf → (stem S r).Leaf
  | 0, a => a
  | r+1, a => ⟨0,stemLeaf S r a⟩

omit [Fintype Ω] in
@[simp] lemma leafProduct_unary (S : PrescribedTree n) (f : FinitePath Ω (n+1) → ℝ)
    (z : Sample Ω (unary S)) :
    leafProduct (unary S) f z=leafProduct S (fun y => f ((z 0).1,y)) (z 0).2 := by
  change (∏ i : Fin 1, leafProduct S (fun y => f ((z i).1,y)) (z i).2)=_
  simp only [Fin.prod_univ_one]
  rfl

/-- The true L2 contraction projection error, retaining the entire sampled
prefix to the designated branching node. The projector is the literal
conditional descendant mean evaluated on the chosen leaf's path. -/
noncomputable def stemContractionSq (S : PrescribedTree n) (a : S.Leaf) (r : ℕ)
    (T : KernelTower Ω (n+r)) (f : FinitePath Ω (n+r) → Fin N → ℝ) (B : Fin N → ℝ) : ℝ :=
  ((stem S r).sampleLaw T).expect (fun z => (FiniteLaw.dot (fun i =>
    leafProduct (stem S r) (fun x => f x i) z-
      tailMean S r T (fun x => f x i) ((stem S r).pathAt (stemLeaf S r a) z)) B)^2)

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ScheduledTopology
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass
open scoped BigOperators
noncomputable local instance instDecidable_solutions (p : Prop) : Decidable p := Classical.propDecidable p

/-- Finite rooted topology with unary vertices suppressed. Children have
fixed distinct positions, hence leaves remain labeled throughout realization. -/
inductive ReducedTopology : Type
  | leaf : ReducedTopology
  | node (k : ℕ+) (hk : 2 ≤ (k:ℕ)) (C : Fin k → ReducedTopology) : ReducedTopology

namespace ReducedTopology

@[reducible] def Vertex : ReducedTopology → Type
  | .leaf => Empty
  | .node k _ C => Option ((i : Fin k) × Vertex (C i))

def Leaf : ReducedTopology → Type
  | .leaf => Unit
  | .node k _ C => (i : Fin k) × Leaf (C i)

instance vertexFintype : (S : ReducedTopology) → Fintype S.Vertex
  | .leaf => inferInstanceAs (Fintype Empty)
  | .node _ _ C => by
    letI : ∀ i, Fintype (Vertex (C i)) := fun i => vertexFintype (C i)
    exact inferInstanceAs (Fintype (Option ((i : _) × Vertex (C i))))

instance leafFintype : (S : ReducedTopology) → Fintype S.Leaf
  | .leaf => inferInstanceAs (Fintype Unit)
  | .node _ _ C => by
    letI : ∀ i, Fintype (Leaf (C i)) := fun i => leafFintype (C i)
    exact inferInstanceAs (Fintype ((i : _) × Leaf (C i)))

/-- Strict ancestry and the genuine terminal grid horizon. -/
def Admissible : (S : ReducedTopology) → (S.Vertex → ℕ) → ℕ → ℕ → Prop
  | .leaf, _, _, _ => True
  | .node _ _ C, q, lo, hi =>
    lo ≤ q none ∧ q none < hi ∧
      ∀ i, Admissible (C i) (fun v => q (some ⟨i,v⟩)) (q none+1) hi

/-- Expand a depth assignment into the actual leveled prescribed tree.
Outside admissible assignments this is still total; no such assignment is
used in the geometry or analytic theorems below. -/
def realize : (r : ℕ) → (d : ℕ) → (S : ReducedTopology) →
    (S.Vertex → ℕ) → PrescribedTree r
  | 0, _, _, _ => .leaf
  | r+1, d, .leaf, q => PrescribedTree.unary (realize r (d+1) .leaf q)
  | r+1, d, .node k hk C, q =>
    if d < q none then PrescribedTree.unary (realize r (d+1) (.node k hk C) q)
    else .node k (fun i => realize r (d+1) (C i) (fun v => q (some ⟨i,v⟩)))

end ReducedTopology
end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ScheduledContinuity
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.ReducedTopology
open scoped BigOperators
variable {Ω : Type} [Fintype Ω]

/-- One assigned branching coordinate and all its later child coordinates. -/
def rootSchedule {k : ℕ+} {hk : 2 ≤ (k:ℕ)} {C : Fin k → ReducedTopology}
    (t : ℕ) (Q : (i : Fin k) → (C i).Vertex → ℕ) : (node k hk C).Vertex → ℕ :=
  fun v => match v with
  | none => t
  | some a => Q a.1 a.2

end DilutedSpinGlass.ReducedTopology
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_VertexContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.ConcreteReservoir
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot Filter Set
open scoped NNReal BigOperators Topology
variable {K : Type} [Countable K] [MeasurableSpace K] [MeasurableSingletonClass K] [DecidableEq K]
  {A : K → Type} [∀ q, Fintype (A q)] {L p : ℕ}
  (ν : Measure (K×ℕ)) [IsProbabilityMeasure ν]
  (Q : (q : K) → Fin (L+1) → FiniteLaw (A q)) (m : Fin (L+1) → ℝ)
  (D E : (q : K) → Spin → FinitePath (A q) (L+1) → ℝ)

noncomputable def physicalBase (_model : Model p) (C H : ℝ) (N : ℕ)
    (h : RootPath ℝ N) (k : ℕ) (x : RootPath (Bond p N) k) (y : FinitePath (Fin N → Spin) (L+1)) : ℝ :=
  energy (boundedPotential C) (clipReal H) h k x (KernelTower.terminalState L y)

lemma measurable_physicalBase (M : Model p) (C H : ℝ) (N k : ℕ) (y : FinitePath (Fin N → Spin) (L+1)) :
    Measurable (fun z : RootPath ℝ N × RootPath (Bond p N) k => physicalBase M C H N z.1 k z.2 y) :=
  measurable_energy _ _ (fun σ => measurable_boundedPotential C σ) (measurable_clipReal H) k _

noncomputable def observableAt
    (D : (q : K) → Spin → FinitePath (A q) (L+1) → ℝ) (N : ℕ) (q : K) (v : Site N)
    (x : FinitePath (Fin N → Spin) (L+1)) (y : FinitePath (A q) (L+1)) : ℝ :=
  D q (readSpin (KernelTower.terminalState L x) v) y

/-- The actual canceled-anchor covariance coefficient of one independent
site/mark insertion into the complete physical Poisson reservoir. -/
noncomputable def physicalCoefficient (S : PrescribedTree (L+1)) (anchor : S.Leaf)
    (M : Model p) (C H : ℝ) (N : ℕ) (u : K×ℕ → ℝ)
    (f : (S.Leaf → FinitePath (Fin N → Spin) (L+1)) → ℝ) (q : K) (k : ℕ) : ℝ :=
  covarianceCoefficient (fun _ : Fin N => M.field.toMeasure) (bondLaw M N) (markLaw ν N)
    ((siteLaw N).map (fun v => ((q,0),v))) (M.alpha*N) (scoreRate N) S anchor
    (KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L)
    (fun i => Q i.1.1) (Fin.cons 0 m) (physicalBase M C H N)
    (dictionaryFactor (observableAt D N) (observableAt E N) u)
    (siteObservable D N) (siteObservable E N) f k

end DilutedSpinGlass.ConcreteReservoir
end

end

section
section
namespace DilutedSpinGlass
open scoped BigOperators
/-- A canonical depth update, with no caller-dependent decidable-equality
instance. This is extensionally the ordinary function update. -/
noncomputable def updateCoordinate {α : Type} (q : α → ℕ) (v : α) (t : ℕ) : α → ℕ :=
  @Function.update α (fun _ => ℕ) (Classical.decEq α) q v t

@[simp] lemma updateCoordinate_self {α : Type} (v : α) (t : ℕ) (q : α → ℕ) :
    updateCoordinate q v t v=t := by
  exact @Function.update_self α (fun _ => ℕ) (Classical.decEq α) v t q

@[simp] lemma updateCoordinate_of_ne {α : Type} {a v : α} (h : a ≠ v) (t : ℕ) (q : α → ℕ) :
    updateCoordinate q v t a=q a := by
  exact @Function.update_of_ne α (fun _ => ℕ) (Classical.decEq α) a v h t q

namespace ReducedTopology
noncomputable local instance vertexContinuityDecidable (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition


def vertexArity : (S : ReducedTopology) → S.Vertex → ℕ+
  | .leaf, v => v.elim
  | .node k _ _, none => k
  | .node _ _ C, some v => vertexArity (C v.1) v.2

end ReducedTopology
end DilutedSpinGlass
end

end

section
section
namespace DilutedSpinGlass.ReducedTopology
open scoped BigOperators
noncomputable local instance realizeTranslationDecidable (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition

end DilutedSpinGlass.ReducedTopology
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ShapeMatrix
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω C : Type} [Fintype Ω] [Fintype C] [DecidableEq C] {L N k : ℕ}

noncomputable local instance shapeMatrixPropDecidable_rf13f56_1 (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
noncomputable def matrixSplitTest (T : PrescribedTree L) (q : C → T.Leaf)
    (B : C → C → ℕ) : ℝ := if ∀ a b, B a b = splitDepth T (q a) (q b) then 1 else 0

noncomputable def spatialProduct (D : C → FinitePath Ω L → Fin N → ℝ)
    (x : C → FinitePath Ω L) : ℝ := (∑ i, ∏ c, D c (x c) i)/(N:ℝ)

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_StemCoupling
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω : Type} [Fintype Ω] {n N : ℕ}

lemma stemLeaf_bijective (S : PrescribedTree n) (r : ℕ) :
    Function.Bijective (stemLeaf S r) := by
  induction r with
  | zero => exact Function.bijective_id
  | succ r ih =>
    constructor
    · intro a b h
      apply ih.1
      exact (Sigma.mk.inj h).2.eq
    · rintro ⟨i,b⟩
      have hi := Fin.eq_zero i
      subst i
      obtain ⟨a,rfl⟩ := ih.2 b
      exact ⟨a,rfl⟩

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_DoubledStemProjection
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω : Type} [Fintype Ω] {n N : ℕ}

/-- The overlap of every old leaf, with two complete independent descendant
sides retained. This is also the normalized full leaf product. -/
noncomputable def doubledOverlap (S : PrescribedTree n) (f : FinitePath Ω (n+1) → Fin N → ℝ)
    (z : Sample Ω (doubled S)) : ℝ :=
  FiniteLaw.dot (fun i => leafProduct S (fun x => f ((z 0).1,x) i) (z 0).2)
    (fun i => leafProduct S (fun x => f ((z 1).1,x) i) (z 1).2)

end DilutedSpinGlass.PrescribedTree
end

end

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω : Type} [Fintype Ω] {n N : ℕ}

def stemInternal (S : PrescribedTree n) : (r : ℕ) → S.Internal → (stem S r).Internal
  | 0,v => v
  | r+1,v => some ⟨0,stemInternal S r v⟩

/-- A later-split projector lifted through an arbitrary actual ancestral
prefix, without flattening the dependent tuple representation of paths. -/
noncomputable def splitProjector (S : PrescribedTree n) (r : ℕ) :
    (d : ℕ) → KernelTower Ω (n+r+1+d) → (FinitePath Ω (n+r+1+d) → ℝ) →
      FinitePath Ω (n+r+1+d) → ℝ
  | 0,T,f,x => tailMean S (r+1) T f x
  | d+1,T,f,x => splitProjector S r d (T.2 x.1) (fun y => f (x.1,y)) x.2

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_CoordinateFiber
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

namespace DilutedSpinGlass

@[simp] lemma updateCoordinate_update {α : Type} (q : α → ℕ) (v : α) (a b : ℕ) :
    updateCoordinate (updateCoordinate q v a) v b = updateCoordinate q v b := by
  classical
  funext w
  by_cases h : w=v
  · subst w; simp
  · simp only [updateCoordinate_of_ne h]

namespace ReducedTopology
open scoped BigOperators
noncomputable local instance instDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {Ω : Type} [Fintype Ω] {L : ℕ} [NeZero L]

/-- Actual change in the conditional tree mean when one assigned vertex
moves by one grid step. All remaining topology coordinates are unchanged. -/
noncomputable def vertexChangeSq (H d : ℕ) (S : ReducedTopology) (v : S.Vertex)
    (T : KernelTower Ω H) (f : FinitePath Ω H → ℝ) (q : S.Vertex → Fin L) : ℝ :=
  (PrescribedTree.treeMean (realize H d S (fun w => (q w).val)) T f-
   PrescribedTree.treeMean (realize H d S
    (updateCoordinate (fun w => (q w).val) v ((q v).val+1))) T f)^2

end ReducedTopology
end DilutedSpinGlass
end

end

section
section
namespace DilutedSpinGlass.FiniteLaw
open scoped BigOperators
variable {N : ℕ}

/-- Squared normalized spatial norm, with the original zero-size convention. -/
noncomputable def spatialSq (x : Fin N → ℝ) : ℝ := (∑ i, (x i)^2)/(N:ℝ)

end DilutedSpinGlass.FiniteLaw
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_CountableFullSupport
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory

/-- A concrete full-support probability law for every nonempty countable mark
dictionary, obtained by pushing forward a geometric law on its enumeration. -/
theorem exists_countable_full_support (I : Type) [Countable I] [Nonempty I]
    [MeasurableSpace I] [MeasurableSingletonClass I] :
    ∃ ν : Measure I, IsProbabilityMeasure ν ∧ ∀ i, 0 < ν.real {i} := by
  classical
  let : Encodable I := Encodable.ofCountable I
  let x₀ : I := Classical.choice ‹Nonempty I›
  let f : ℕ → I := fun n => (Encodable.decode (α := I) n).getD x₀
  have hf (i : I) : f (Encodable.encode i) = i := by simp [f]
  let p : unitInterval := ⟨1/2, by constructor <;> norm_num⟩
  have hp0 : p ≠ 0 := by intro h; have := congrArg Subtype.val h; norm_num [p] at this
  have hp1 : p ≠ 1 := by intro h; have := congrArg Subtype.val h; norm_num [p] at this
  let ν := (geometricMeasure p).map f
  have hfm : Measurable f := measurable_of_countable f
  refine ⟨ν,(by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)),?_⟩
  intro i
  have hsingle : {Encodable.encode i} ⊆ f ⁻¹' {i} := by
    intro j hj
    have hj' : j = Encodable.encode i := hj
    subst j
    exact hf i
  have hm : geometricMeasure p {Encodable.encode i} ≤ ν {i} := by
    dsimp [ν]
    rw [Measure.map_apply hfm (measurableSet_singleton i)]
    exact measure_mono hsingle
  have hpos : 0 < geometricMeasure p {Encodable.encode i} := by
    rw [geometricMeasure_singleton hp0]
    exact ENNReal.ofReal_pos.mpr (geometricMeasure_pos hp0 hp1 _)
  exact ENNReal.toReal_pos (hpos.trans_le hm).ne' (measure_ne_top ν _)

end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_UniversalDictionary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators

 
abbrev Table (L r : ℕ) := {g : (Fin L → Fin r → Bool) → ℚ // ∀ y, |g y| ≤ 1}

/-- Two bounded mark tables and the choice of spin or marker anchor. -/
abbrev Spec (L : ℕ) := Σ r : ℕ, Table L r × Table L r × Bool

instance tableCountable (L r : ℕ) : Countable (Table L r) := inferInstance
instance specCountable (L : ℕ) : Countable (Spec L) := inferInstance
instance tableNonempty (L r : ℕ) : Nonempty (Table L r) := ⟨⟨fun _ => 0,by simp⟩⟩
instance specNonempty (L : ℕ) : Nonempty (Spec L) := ⟨⟨0,Classical.choice inferInstance,
  Classical.choice inferInstance,false⟩⟩
instance specMeasurable (L : ℕ) : MeasurableSpace (Spec L) := ⊤
instance specSingleton (L : ℕ) : MeasurableSingletonClass (Spec L) := ⟨fun _ => trivial⟩
noncomputable instance specDecidable (L : ℕ) : DecidableEq (Spec L) := Classical.decEq _

abbrev Alphabet {L : ℕ} (q : Spec L) := Fin q.1 → Bool
noncomputable def prior {L : ℕ} (q : Spec L) (_ : Fin (L+1)) : FiniteLaw (Alphabet q) :=
  FiniteLaw.pi (fun _ => MarkSelector.rademacher)

def interior {L r : ℕ} (y : FinitePath (Fin r → Bool) (L+1)) : Fin L → Fin r → Bool :=
  fun d => pathCoordinate (L+1) y d.castSucc

noncomputable def direction {L : ℕ} (q : Spec L) (σ : Spin)
    (y : FinitePath (Alphabet q) (L+1)) : ℝ :=
  (q.2.1.1 (interior y) : ℝ) * spin σ
noncomputable def anchor {L : ℕ} (q : Spec L) (σ : Spin)
    (y : FinitePath (Alphabet q) (L+1)) : ℝ :=
  (q.2.2.1.1 (interior y) : ℝ) * (if q.2.2.2 then spin σ else 1)

/-- One fixed countable full-support law suffices for all finitely many
colors/requirements and their signed rational polarizations. -/
noncomputable def weights (L : ℕ) : Measure (Spec L × ℕ) :=
  (exists_countable_full_support (Spec L × ℕ)).choose
instance weightsProbability (L : ℕ) : IsProbabilityMeasure (weights L) :=
  (exists_countable_full_support (Spec L × ℕ)).choose_spec.1


def signQ (b : Bool) : ℚ := if b then 1 else -1
@[simp] lemma abs_signQ (b : Bool) : |signQ b| = 1 := by cases b <;> norm_num [signQ]
@[simp] lemma cast_signQ (b : Bool) : (signQ b : ℝ) = MarkSelector.sign b := by
  cases b <;> norm_num [signQ,MarkSelector.sign]

noncomputable def selector {L r : ℕ} {C : Type} [DecidableEq C]
    (a b : Fin r → C) (d : Fin r → Fin L) (c : C) : Table L r :=
  ⟨fun y => ∏ j, (if c = a j then signQ (y (d j) j) else 1) *
      (if c = b j then signQ (y (d j) j) else 1), by
    intro y
    rw [Finset.abs_prod]
    have he : (∏ j : Fin r, |(if c = a j then signQ (y (d j) j) else 1) *
        (if c = b j then signQ (y (d j) j) else 1)|) = 1 := by
      apply Finset.prod_eq_one
      intro j _
      rw [abs_mul]
      split_ifs <;> simp
    exact he.le⟩

/-- Signed averages needed by polarization stay in the SAME finite
alphabet and in the unit-bounded rational table family. -/
noncomputable def average {L r k : ℕ} (hk : 0 < k) (ε : Fin k → Bool)
    (g : Fin k → Table L r) : Table L r :=
  ⟨fun y => (k:ℚ)⁻¹ * ∑ j, signQ (ε j) * (g j).1 y, by
    intro y
    rw [abs_mul,abs_inv,abs_of_nonneg (Nat.cast_nonneg k)]
    have h : |∑ j, signQ (ε j) * (g j).1 y| ≤ (k:ℚ) := by
      calc
        _ ≤ ∑ j, |signQ (ε j) * (g j).1 y| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _j : Fin k, (1:ℚ) := by
          apply Finset.sum_le_sum
          intro j _
          simpa only [abs_mul,abs_signQ,one_mul] using (g j).2 y
        _ = _ := by simp
    have hk' : (0:ℚ) < k := by exact_mod_cast hk
    calc
      _ ≤ (k:ℚ)⁻¹ * k := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hk'.le)
      _ = 1 := inv_mul_cancel₀ hk'.ne'⟩

end DilutedSpinGlass.UniversalDictionary
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_PrefixProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.UniversalDictionary
open scoped BigOperators

noncomputable def polarizedSpec {L r k : ℕ} (hk : 0 < k) (ε : Fin k → Bool)
    (a b : Fin r → Option (Fin k)) (d : Fin r → Fin L) (spinAnchor : Bool) : Spec L :=
  ⟨r, average hk ε (fun j => selector a b d (some j)), selector a b d none, spinAnchor⟩

end DilutedSpinGlass.UniversalDictionary
end

end

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω I : Type} [Fintype Ω] [Fintype I] [DecidableEq I] {n N : ℕ}

/-- The normalized product of all leaves, with the exact zero-size convention. -/
noncomputable def treeOverlap (S : PrescribedTree n) (f : FinitePath Ω n → Fin N → ℝ)
    (z : Sample Ω S) : ℝ := (∑ i, leafProduct S (fun x => f x i) z)/(N:ℝ)

/-- Proper-child covariance at the later first split, retaining the entire
original evaluation prefix. These are genuine iterated kernel expectations. -/
noncomputable def descendantEnergyAt (C : PrescribedTree n) (r : ℕ) : (d : ℕ) →
    KernelTower Ω (n+1+r+1+d) → (FinitePath Ω (n+1+r+1+d) → Fin N → ℝ) → ℝ
  | 0,T,f => shapeEnergyAt C (r+1) T f
  | d+1,T,f => T.1.expect (fun x => descendantEnergyAt C r d (T.2 x) (fun y => f (x,y)))

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_MultileafMatrixPointwise
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.UniversalDictionary
open HeterogeneousMarks PrescribedTree
open scoped BigOperators
variable {Ω Z : Type} [Fintype Ω] {L n r k : ℕ}

/-- The actual old full reservoir is tilted first; the constrained history
then samples only its physical paths, with no fresh prior marks left. -/
noncomputable def externalHistory (S : PrescribedTree (L+1)) (anchorLeaf : S.Leaf)
    (T : KernelTower Ω (L+1)) (m : Fin (L+2) → ℝ)
    (base : FinitePath Ω (L+1) → ℝ) (roots : Fin n → (Spec L×ℕ)×Z)
    (old : (i : (Spec L×ℕ)×Z) → FinitePath Ω (L+1) → FinitePath (Alphabet i.1.1) (L+1) → ℝ)
    (read : Z → FinitePath Ω (L+1) → Spin) (v : Z)
    (a b : Fin r → Option (Fin k)) (d : Fin r → Fin L) (spinAnchor : Bool)
    (f : (S.Leaf → FinitePath Ω (L+1)) → ℝ) : ℝ :=
  constrainedHistory
    (KernelTower.tilt (L+1) (tower roots (L+1) T (fun i => prior i.1.1)) (fun j => m j.succ)
      (HeterogeneousMarks.logWeight base roots old)) m a b (fun j => (d j).castSucc)
    (fun c x => match c with
      | none => if spinAnchor then spin (read v (physical roots (L+1) x)) else 1
      | some _ => spin (read v (physical roots (L+1) x))) S anchorLeaf
    (fun x => f (fun a => physical roots (L+1) (S.pathAt a x)))

end DilutedSpinGlass.UniversalDictionary
end

end

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω I : Type} [Fintype Ω] [Fintype I] [DecidableEq I] {n N : ℕ}

/-- The complete old experiment: two entire sides separating at depth d,
with their first internal split after another r unary transitions. -/
def splitFrame (S : PrescribedTree n) (r d : ℕ) : PrescribedTree (n+r+1+d) :=
  stem (doubled (stem S r)) d

def splitFrameLeaf (S : PrescribedTree n) (r d : ℕ) (j : Fin 2) (a : S.Leaf) :
    (splitFrame S r d).Leaf := stemLeaf (doubled (stem S r)) d ⟨j,stemLeaf S r a⟩

def splitFrameVertex (S : PrescribedTree n) (r d : ℕ) : (splitFrame S r d).Internal :=
  stemInternal (doubled (stem S r)) d none

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_RootMultileafMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PrescribedTree
open scoped NNReal BigOperators
variable {Ω X Y Z : Type} [Fintype Ω]
    [MeasurableSpace X] [MeasurableSpace Y]
    [Countable Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] {L M r k : ℕ}

abbrev Labels (L : ℕ) (Z : Type) := (Spec L × ℕ) × Z

noncomputable def rootHistory (S : PrescribedTree (L+1)) (anchorLeaf : S.Leaf)
    (T : KernelTower Ω (L+1)) (m : Fin (L+2) → ℝ)
    (base : RootPath Y M → (n : ℕ) → RootPath X n → FinitePath Ω (L+1) → ℝ)
    (old : (i : Labels L Z) → FinitePath Ω (L+1) → FinitePath (Alphabet i.1.1) (L+1) → ℝ)
    (read : Z → FinitePath Ω (L+1) → Spin)
    (a b : Fin r → Option (Fin k)) (d : Fin r → Fin L) (spinAnchor : Bool)
    (f : (S.Leaf → FinitePath Ω (L+1)) → ℝ) (z : FullRootState Y X (Labels L Z) M) (v : Z) : ℝ :=
  packRoot (fun h n x t y => externalHistory S anchorLeaf T m (base h n x)
    (rootArray t y) old read v a b d spinAnchor f) z

variable (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure (Labels L Z)) [IsProbabilityMeasure ν]
    (τ : Measure Z) [IsProbabilityMeasure τ] (rate score : ℝ≥0)
    (S : PrescribedTree (L+1)) (anchorLeaf : S.Leaf)
    (T : KernelTower Ω (L+1)) (m : Fin (L+2) → ℝ)
    (base : RootPath Y M → (n : ℕ) → RootPath X n → FinitePath Ω (L+1) → ℝ)
    (old : (i : Labels L Z) → FinitePath Ω (L+1) → FinitePath (Alphabet i.1.1) (L+1) → ℝ)
    (read : Z → FinitePath Ω (L+1) → Spin)
    (a b : Fin r → Option (Fin k)) (d : Fin r → Fin L) (spinAnchor : Bool)
    (f : (S.Leaf → FinitePath Ω (L+1)) → ℝ)

noncomputable def historyAverage : ℝ :=
  ∫ z : FullRootState Y X (Labels L Z) M × Z,
    rootHistory S anchorLeaf T m base old read a b d spinAnchor f z.1 z.2
      ∂(fullRootLaw ξ μ ν rate score).prod τ

noncomputable def historyCovariance : ℝ :=
  historyAverage ξ μ ν τ rate score S anchorLeaf T m base old read a b d spinAnchor f -
    oldTreeAverage ξ μ ν rate score S T (fun i => prior i.1.1) (fun j => m j.succ) base old f *
      historyAverage ξ μ ν τ rate score S anchorLeaf T m base old read a b d spinAnchor (fun _ => 1)

end DilutedSpinGlass.UniversalDictionary
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_SimultaneousShift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass
open scoped BigOperators
noncomputable local instance simultaneousShiftPropDecidable (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition

namespace DepthAverage
variable {α : Type} [Fintype α] [DecidableEq α] {L : ℕ} [NeZero L]

noncomputable def shiftPathFlag (s : α → Bool) (t : ℕ) (v : α) : Bool :=
  if (Fintype.equivFin α v).val < t then s v else false

noncomputable def shiftPath (s : α → Bool) (t : ℕ) (q : α → Fin L) : α → Fin L :=
  coordinateProjection id (fun v => shiftPerm (shiftPathFlag s t v)) q

end DepthAverage
end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_SpatialScheduledContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.DepthAverage
open scoped BigOperators
noncomputable local instance spatialScheduledContinuityDepthDecidable (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition

end DilutedSpinGlass.DepthAverage
namespace DilutedSpinGlass.ReducedTopology
open _root_.MeasureTheory
open scoped BigOperators
noncomputable local instance spatialScheduledContinuityReducedDecidable (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
variable {Ω : Type} [Fintype Ω] {L N : ℕ} [NeZero L]

/-- Actual normalized spatial squared norm of the conditional-mean change.
Both schedules use the same ancestral kernel and spin function. -/
noncomputable def spatialScheduleChange (H d : ℕ) (S : ReducedTopology) (s : S.Vertex → Bool)
    (T : KernelTower Ω H) (f : FinitePath Ω H → Fin N → ℝ) (q : S.Vertex → Fin L) : ℝ :=
  (∑ i : Fin N,
    (PrescribedTree.treeMean (realize H d S (fun v => (q v).val)) T (fun x => f x i)-
     PrescribedTree.treeMean (realize H d S
       (fun v => (DepthAverage.shiftPerm (s v) (q v)).val)) T (fun x => f x i))^2)/(N:ℝ)

end DilutedSpinGlass.ReducedTopology
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ProductEvaluationContinuity
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω : Type} [Fintype Ω] {n N : ℕ}

/-- The actual change of a product of proper-child conditional means, when
its common evaluation depth advances by one on the SAME full sampled path. -/
noncomputable def productStemIncrementSq {ι : Type*} [Fintype ι]
    (C : ι → PrescribedTree n) (r : ℕ) (T : KernelTower Ω (n+r))
    (f : FinitePath Ω (n+r) → ℝ) (d : Fin r) : ℝ :=
  (KernelTower.law (n+r) T).expect (fun x =>
    ((∏ i, stemMeanAt (C i) r d.succ T f x)-
      (∏ i, stemMeanAt (C i) r d.castSucc T f x))^2)

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_TargetEvaluationContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω : Type} [Fintype Ω] {n N : ℕ}

/-- Actual product of the proper-child conditional means on a single path. -/
noncomputable def productStemMeanAt {ι : Type*} [Fintype ι]
    (C : ι → PrescribedTree n) (r : ℕ) (d : Fin (r+1)) (T : KernelTower Ω (n+r))
    (f : FinitePath Ω (n+r) → Fin N → ℝ) (x : FinitePath Ω (n+r)) (j : Fin N) : ℝ :=
  ∏ i, stemMeanAt (C i) r d T (fun y => f y j) x

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_TargetScheduleContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.DepthAverage
open scoped BigOperators
noncomputable local instance targetScheduleAverageDecidable (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition

end DilutedSpinGlass.DepthAverage
namespace DilutedSpinGlass.ReducedTopology
open scoped BigOperators
noncomputable local instance targetScheduleTopologyDecidable (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
variable {Ω : Type} [Fintype Ω] {L N : ℕ} [NeZero L]

/-- A branching-schedule projector evaluated on the SAME actual full path.
Its initial p coordinates are retained, not independently resampled. -/
noncomputable def scheduledTailProjection (H d p : ℕ) (S : ReducedTopology)
    (q : S.Vertex → Fin L) (T : KernelTower Ω (H+p))
    (f : FinitePath Ω (H+p) → Fin N → ℝ) (x : FinitePath Ω (H+p)) (i : Fin N) : ℝ :=
  PrescribedTree.tailMean (realize H d S (fun v => (q v).val)) p T (fun y => f y i) x

noncomputable def tailScheduleChange (H d p : ℕ) (S : ReducedTopology) (s : S.Vertex → Bool)
    (T : KernelTower Ω (H+p)) (f : FinitePath Ω (H+p) → Fin N → ℝ) (q : S.Vertex → Fin L) : ℝ :=
  (KernelTower.law (H+p) T).expect (fun x => FiniteLaw.spatialSq (fun i =>
    scheduledTailProjection H d p S q T f x i-
    scheduledTailProjection H d p S (fun v => DepthAverage.shiftPerm (s v) (q v)) T f x i))

end DilutedSpinGlass.ReducedTopology
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ProperChildScheduleContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.ReducedTopology
open scoped BigOperators
noncomputable local instance properChildSchedulePropDecidable (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
variable {Ω α ι : Type} [Fintype Ω] [Fintype α] [DecidableEq α] [Fintype ι]
  {L N : ℕ} [NeZero L]

/-- Product of the actual proper-child schedule projectors, restricted from
the parent depth-assignment cube. Coordinates may be independently translated.
No independent sampling of aligned copies occurs in this definition. -/
noncomputable def childScheduleProjection (H d p : ℕ) (C : ι → ReducedTopology)
    (e : (j : ι) → (C j).Vertex → α) (τ : (j : ι) → (C j).Vertex → Equiv.Perm (Fin L))
    (s : (j : ι) → (C j).Vertex → Bool)
    (T : KernelTower Ω (H+p)) (f : FinitePath Ω (H+p) → Fin N → ℝ)
    (q : α → Fin L) (x : FinitePath Ω (H+p)) (i : Fin N) : ℝ :=
  ∏ j, scheduledTailProjection H d p (C j)
    (fun v => DepthAverage.shiftPerm (s j v) (τ j v (q (e j v)))) T f x i

end DilutedSpinGlass.ReducedTopology
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ScheduledEvaluationContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.ReducedTopology
open scoped BigOperators
variable {Ω : Type} [Fintype Ω] {N : ℕ}

/-- Conditional scheduled-tree mean after a genuine sampled prefix. The
terminal reserve n is held fixed and the evaluation depth ranges over the
first r transitions. No unobserved ancestral variable is resampled. -/
noncomputable def scheduledPrefixMean (n : ℕ) : (r d : ℕ) → Fin (r+1) →
    (S : ReducedTopology) → (S.Vertex → ℕ) → KernelTower Ω (n+r) →
    (FinitePath Ω (n+r) → ℝ) → FinitePath Ω (n+r) → ℝ
  | 0,d,_,S,q,T,f,_ => PrescribedTree.treeMean (realize n d S q) T f
  | r+1,d,e,S,q,T,f,x => Fin.cases
      (PrescribedTree.treeMean (realize (n+r+1) d S q) T f)
      (fun e => scheduledPrefixMean n r (d+1) e S q (T.2 x.1) (fun y => f (x.1,y)) x.2) e

@[simp] lemma scheduledPrefixMean_zero (n r d : ℕ) (S : ReducedTopology) (q : S.Vertex → ℕ)
    (T : KernelTower Ω (n+r)) (f : FinitePath Ω (n+r) → ℝ) (x : FinitePath Ω (n+r)) :
    scheduledPrefixMean n r d 0 S q T f x=PrescribedTree.treeMean (realize (n+r) d S q) T f := by
  cases r <;> rfl

/-- Ranged proper-child conditional product in the actual scheduled shape. -/
noncomputable def scheduledProductMean {ι : Type*} [Fintype ι]
    (n r d : ℕ) (C : ι → ReducedTopology) (q : (j : ι) → (C j).Vertex → ℕ)
    (e : Fin (r+1)) (T : KernelTower Ω (n+r)) (f : FinitePath Ω (n+r) → Fin N → ℝ)
    (x : FinitePath Ω (n+r)) (i : Fin N) : ℝ :=
  ∏ j, scheduledPrefixMean n r d e (C j) (q j) T (fun y => f y i) x

end DilutedSpinGlass.ReducedTopology
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ConditionalScheduledMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.ReducedTopology
open scoped BigOperators
variable {Ω : Type} [Fintype Ω] {N : ℕ}

/-- The scheduled conditional mean on a literal full path, evaluated after
`e` transitions. Before the first branching this is the usual conditional
expectation; no independently sampled prefix occurs in this definition. -/
noncomputable def conditionalScheduledMean : (H d e : ℕ) →
    (S : ReducedTopology) → (S.Vertex → ℕ) → KernelTower Ω H →
    (FinitePath Ω H → ℝ) → FinitePath Ω H → ℝ
  | 0,_,_,_,_,T,f,_ => PrescribedTree.treeMean .leaf T f
  | H+1,d,0,S,q,T,f,_ => PrescribedTree.treeMean (realize (H+1) d S q) T f
  | H+1,d,e+1,S,q,T,f,x => conditionalScheduledMean H (d+1) e S q (T.2 x.1)
      (fun y => f (x.1,y)) x.2

/-- Proper-child mean product at an actual evaluation prefix, expressed
without a choice of terminal reserve. -/
noncomputable def conditionalScheduledProduct {ι : Type*} [Fintype ι]
    (H d e : ℕ) (C : ι → ReducedTopology) (q : (j : ι) → (C j).Vertex → ℕ)
    (T : KernelTower Ω H) (f : FinitePath Ω H → Fin N → ℝ)
    (x : FinitePath Ω H) (i : Fin N) : ℝ :=
  ∏ j, conditionalScheduledMean H d e (C j) (q j) T (fun y => f y i) x

end DilutedSpinGlass.ReducedTopology
end

end

section
section
namespace DilutedSpinGlass.DepthAverage
open scoped BigOperators
noncomputable local instance conditionalScheduledMeanDepthDecidable (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
variable {α : Type} [Fintype α] [DecidableEq α] {L : ℕ} [NeZero L]

/-- Put a distinguished evaluation coordinate back into its full parent
cube, keeping every other branching coordinate literally unchanged. -/
def insertCoordinate (a : α) (t : Fin L) (rest : {j : α // j≠a} → Fin L) : α → Fin L :=
  (Equiv.piSplitAt a (fun _ : α => Fin L)).symm (t,rest)

omit [Fintype α] [NeZero L] in
@[simp] lemma insertCoordinate_self (a : α) (t : Fin L) (rest : {j : α // j≠a} → Fin L) :
    insertCoordinate a t rest a=t := by simp [insertCoordinate,Equiv.piSplitAt_symm_apply]

omit [Fintype α] [NeZero L] in
@[simp] lemma insertCoordinate_other (a : α) (t : Fin L) (rest : {j : α // j≠a} → Fin L)
    (j : {j : α // j≠a}) : insertCoordinate a t rest j=rest j := by
  simp [insertCoordinate,Equiv.piSplitAt_symm_apply,j.property]


end DilutedSpinGlass.DepthAverage
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ConditionalSpatialContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.ReducedTopology
open scoped BigOperators
variable {Ω : Type} [Fintype Ω] {N : ℕ}

noncomputable local instance instDecidable_1_rf13f56_1 (p : Prop) : Decidable p := Classical.propDecidable p
/-- Single-copy spatial squared distance of two actual conditional means. -/
noncomputable def projectorChangeSq {M : ℕ} (T : KernelTower Ω M)
    (X Y : FinitePath Ω M → Fin N → ℝ) : ℝ :=
  (KernelTower.law M T).expect (fun x => FiniteLaw.spatialSq (fun i => X x i-Y x i))

end DilutedSpinGlass.ReducedTopology
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_EarliestChildDepth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.ReducedTopology
open scoped BigOperators
noncomputable local instance earliestChildDepthPropDecidable_rf13f56_1 (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
variable {ι : Type} [Fintype ι] {L : ℕ} [NeZero L]

/-- First available proper-child branching depth, with terminal value L
when every proper child is a leaf. This handles the induction endpoint. -/
noncomputable def earliestChildDepth (C : ι → ReducedTopology)
    (q : (j : ι) → (C j).Vertex → Fin L) : ℕ :=
  (Finset.univ.inf (fun w : (j : ι) × (C j).Vertex => (q w.1 w.2).castSucc)).val

end DilutedSpinGlass.ReducedTopology
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ConcreteHistory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree
  ConcreteReservoir Filter Set
open scoped NNReal BigOperators Topology
variable {L p r k : ℕ}

/-- The actual charge-weighted, sharing-constrained overlap history in the
complete prescribed-tree physical reservoir, centered by its old test. -/
noncomputable def physicalHistoryCovariance (m : Fin (L+1) → ℝ)
    (S : PrescribedTree (L+1)) (anchorLeaf : S.Leaf)
    (M : Model p) (C H : ℝ) (N : ℕ) (u : Spec L×ℕ → ℝ)
    (a b : Fin r → Option (Fin k)) (d : Fin r → Fin L) (spinAnchor : Bool)
    (f : (S.Leaf → FinitePath (Fin N → Spin) (L+1)) → ℝ) : ℝ :=
  historyCovariance (fun _ : Fin N => M.field.toMeasure) (bondLaw M N)
    (markLaw (weights L) N) (siteLaw N) (M.alpha*N) (scoreRate N) S anchorLeaf
    (KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L)
    (Fin.cons 0 m) (physicalBase M C H N)
    (dictionaryFactor (observableAt direction N) (observableAt anchor N) u)
    (fun v x => readSpin (KernelTower.terminalState L x) v) a b d spinAnchor f

end DilutedSpinGlass.UniversalDictionary
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ShapeRoot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PrescribedTree
open scoped NNReal BigOperators
variable {Ω X Y Z : Type} [Fintype Ω]
    [MeasurableSpace X] [MeasurableSpace Y]
    [Countable Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] {L M n k : ℕ}

noncomputable def externalShapeHistory (S : PrescribedTree (L+1)) (anchorLeaf : S.Leaf)
    (T : KernelTower Ω (L+1)) (m : Fin (L+2) → ℝ)
    (base : FinitePath Ω (L+1) → ℝ) (roots : Fin n → Labels L Z)
    (old : (i : Labels L Z) → FinitePath Ω (L+1) → FinitePath (Alphabet i.1.1) (L+1) → ℝ)
    (read : Z → FinitePath Ω (L+1) → Spin) (v : Z)
    (F : (Option (Fin k) → Option (Fin k) → ℕ) → ℝ) (spinAnchor : Bool)
    (f : (S.Leaf → FinitePath Ω (L+1)) → ℝ) : ℝ :=
  shapeHistory
    (KernelTower.tilt (L+1) (tower roots (L+1) T (fun i => prior i.1.1)) (fun j => m j.succ)
      (HeterogeneousMarks.logWeight base roots old)) m F
    (fun c x => match c with
      | none => if spinAnchor then spin (read v (physical roots (L+1) x)) else 1
      | some _ => spin (read v (physical roots (L+1) x))) S anchorLeaf
    (fun x => f (fun a => physical roots (L+1) (S.pathAt a x)))

noncomputable def rootShapeHistory (S : PrescribedTree (L+1)) (anchorLeaf : S.Leaf)
    (T : KernelTower Ω (L+1)) (m : Fin (L+2) → ℝ)
    (base : RootPath Y M → (n : ℕ) → RootPath X n → FinitePath Ω (L+1) → ℝ)
    (old : (i : Labels L Z) → FinitePath Ω (L+1) → FinitePath (Alphabet i.1.1) (L+1) → ℝ)
    (read : Z → FinitePath Ω (L+1) → Spin)
    (F : (Option (Fin k) → Option (Fin k) → ℕ) → ℝ) (spinAnchor : Bool)
    (f : (S.Leaf → FinitePath Ω (L+1)) → ℝ) (z : FullRootState Y X (Labels L Z) M) (v : Z) : ℝ :=
  packRoot (fun h n x t y => externalShapeHistory S anchorLeaf T m (base h n x)
    (rootArray t y) old read v F spinAnchor f) z

variable (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure (Labels L Z)) [IsProbabilityMeasure ν]
    (τ : Measure Z) [IsProbabilityMeasure τ] (rate score : ℝ≥0)
    (S : PrescribedTree (L+1)) (anchorLeaf : S.Leaf)
    (T : KernelTower Ω (L+1)) (m : Fin (L+2) → ℝ)
    (base : RootPath Y M → (n : ℕ) → RootPath X n → FinitePath Ω (L+1) → ℝ)
    (old : (i : Labels L Z) → FinitePath Ω (L+1) → FinitePath (Alphabet i.1.1) (L+1) → ℝ)
    (read : Z → FinitePath Ω (L+1) → Spin)
    (F : (Option (Fin k) → Option (Fin k) → ℕ) → ℝ) (spinAnchor : Bool)
    (f : (S.Leaf → FinitePath Ω (L+1)) → ℝ)

noncomputable def shapeAverage : ℝ :=
  ∫ z : FullRootState Y X (Labels L Z) M × Z,
    rootShapeHistory S anchorLeaf T m base old read F spinAnchor f z.1 z.2
      ∂(fullRootLaw ξ μ ν rate score).prod τ

noncomputable def shapeCovariance : ℝ :=
  shapeAverage ξ μ ν τ rate score S anchorLeaf T m base old read F spinAnchor f -
    oldTreeAverage ξ μ ν rate score S T (fun i => prior i.1.1) (fun j => m j.succ) base old f *
      shapeAverage ξ μ ν τ rate score S anchorLeaf T m base old read F spinAnchor (fun _ => 1)

end DilutedSpinGlass.UniversalDictionary
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ZeroShape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree
  ConcreteReservoir Filter Set
open scoped NNReal BigOperators Topology
variable {L p k : ℕ}

/-- Literal exact prescribed-shape covariance, using the original physical
site mean at every signed extension of the complete tilted reservoir. -/
noncomputable def physicalShapeCovariance (m : Fin (L+1) → ℝ)
    (S : PrescribedTree (L+1)) (anchorLeaf : S.Leaf)
    (M : Model p) (C H : ℝ) (N : ℕ) (u : Spec L×ℕ → ℝ)
    (F : (Option (Fin k) → Option (Fin k) → ℕ) → ℝ) (spinAnchor : Bool)
    (f : (S.Leaf → FinitePath (Fin N → Spin) (L+1)) → ℝ) : ℝ :=
  shapeCovariance (fun _ : Fin N => M.field.toMeasure) (bondLaw M N)
    (markLaw (weights L) N) (siteLaw N) (M.alpha*N) (scoreRate N) S anchorLeaf
    (KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L)
    (Fin.cons 0 m) (physicalBase M C H N)
    (dictionaryFactor (observableAt direction N) (observableAt anchor N) u)
    (fun v x => readSpin (KernelTower.terminalState L x) v) F spinAnchor f

end DilutedSpinGlass.UniversalDictionary
end

end

section
section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PrescribedTree
open scoped NNReal BigOperators
variable {Ω Z : Type} [Fintype Ω] {L n : ℕ}

def zeroSpec (L : ℕ) (spinAnchor : Bool) : Spec L :=
  ⟨0, ⟨fun _ => 0,by simp⟩, ⟨fun _ => 1,by simp⟩, spinAnchor⟩

@[simp] lemma zeroSpec_anchor (spinAnchor : Bool) (σ : Spin)
    (y : FinitePath (Alphabet (zeroSpec L spinAnchor)) (L+1)) :
    anchor (zeroSpec L spinAnchor) σ y = if spinAnchor then spin σ else 1 := by
  simp [anchor,zeroSpec]
  rfl

end DilutedSpinGlass.UniversalDictionary

end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_PhysicalPairConnection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PrescribedTree ConcreteReservoir
open scoped NNReal BigOperators
variable {Ω X Y : Type} [Fintype Ω] [MeasurableSpace X] [MeasurableSpace Y] {L M N : ℕ}

noncomputable def pairSplitTest (d : ℕ) (B : Option (Fin 1) → Option (Fin 1) → ℕ) : ℝ :=
  if B none (some 0) = d then 1 else 0

def readVector (read : Site N → FinitePath Ω (L+1) → Spin) (x : FinitePath Ω (L+1)) :
    Fin (max N 1) → ℝ := fun i => spin (read i x)

end DilutedSpinGlass.UniversalDictionary
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_PhysicalPairEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PrescribedTree ConcreteReservoir
open scoped NNReal BigOperators
variable {Ω X Y : Type} [Fintype Ω] [MeasurableSpace X] [MeasurableSpace Y] {L M N : ℕ}

noncomputable def pairOverlap (S : PrescribedTree (L+1)) (a b : S.Leaf)
    (read : Site N → FinitePath Ω (L+1) → Spin) (x : S.Leaf → FinitePath Ω (L+1)) : ℝ :=
  FiniteLaw.dot (readVector read (x a)) (readVector read (x b))

end DilutedSpinGlass.UniversalDictionary
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_PhysicalSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir Filter Set
open scoped NNReal BigOperators Topology
variable {L p : ℕ}

/-- The manuscript's singleton conditional spatial covariance density, under
the actual tilted reservoir, averaged over roots and the d-coordinate prefix. -/
noncomputable def physicalSingletonEnergy (m : Fin (L+1) → ℝ) (M : Model p) (C H : ℝ)
    (N : ℕ) (u : Spec L×ℕ → ℝ) (d : ℕ) : ℝ :=
  ∫ z, rootConditionalEnergy
    (KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L)
    (fun i => prior i.1.1) m (physicalBase M C H N)
    (dictionaryFactor (observableAt direction N) (observableAt anchor N) u) d
    (readVector (fun v x => readSpin (KernelTower.terminalState L x) v)) z
    ∂fullRootLaw (fun _ : Fin N => M.field.toMeasure) (bondLaw M N)
      (markLaw (weights L) N) (M.alpha*N) (scoreRate N)

noncomputable def singletonOldTest (d : ℕ) (hd : d < L+1) (N : ℕ) :
    ((forkAt (L+1) d hd).Leaf → FinitePath (Fin N → Spin) (L+1)) → ℝ :=
  pairOverlap (forkAt (L+1) d hd) (forkAtLeaf (L+1) d hd 0) (forkAtLeaf (L+1) d hd 1)
    (fun v x => readSpin (KernelTower.terminalState L x) v)

end DilutedSpinGlass.UniversalDictionary
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_FullCubeConditionalContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir Filter Set
open scoped NNReal BigOperators Topology
variable {L p : ℕ}

/-- The interior grid exponents; the automatically adjoined root exponent is zero. -/
noncomputable def gridExponents (L : ℕ) : Fin (L+1) → ℝ :=
  fun j => (((j:ℕ)+1:ℕ):ℝ)/((L+1:ℕ):ℝ)

/-- The singleton depth domain of the manuscript, with no artificial
normalization by its cardinality. At height L+1 its mass is at most one. -/
noncomputable def regularSingletonDepths (L : ℕ) (η : ℝ) : Finset (Fin (L+1)) :=
  Finset.univ.filter (fun d => η < (d:ℝ)/(L+1:ℕ) ∧ (d:ℝ)/(L+1:ℕ) < 1-η)


end DilutedSpinGlass.UniversalDictionary
end

end

section
section
namespace DilutedSpinGlass.ReducedTopology
open scoped BigOperators
noncomputable local instance fullCubeConditionalPropDecidable (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition

end DilutedSpinGlass.ReducedTopology
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ShapeMatrixPhysical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PrescribedTree ConcreteReservoir
open scoped NNReal BigOperators
variable {Ω X Y : Type} [Fintype Ω] [MeasurableSpace X] [MeasurableSpace Y] {L M N k : ℕ}

variable (S : PrescribedTree (L+1)) (a : S.Leaf) (K : KernelTower Ω (L+1))
    (m : Fin (L+2) → ℝ)
    (base : RootPath Y M → (n : ℕ) → RootPath X n → FinitePath Ω (L+1) → ℝ)
    (old : (i : Labels L (Site N)) → FinitePath Ω (L+1) → FinitePath (Alphabet i.1.1) (L+1) → ℝ)
    (read : Site N → FinitePath Ω (L+1) → Spin)
    (T : PrescribedTree (L+1)) (q : Option (Fin k) → T.Leaf)
    (f : (S.Leaf → FinitePath Ω (L+1)) → ℝ)

/-- A matrix multioverlap at the actual heterogeneous physical root,
retaining the literal old-test transport and root-dependent alphabet. -/
noncomputable def rootMatrixObservable (z : FullRootState Y X (Labels L (Site N)) M) : ℝ :=
  matrixObservableHistory T q
    (rootTower K (fun i => prior i.1.1) (fun j => m j.succ) base old z) m
    (List.ofFn (fun j : Fin k => (some j : Option (Fin k)))).reverse S a
    (spatialProduct (fun _ => rootVector (readVector read) z))
    (fun x => f (fun b => physical (rootArray z.2.2.1 z.2.2.2) (L+1) (S.pathAt b x)))

end DilutedSpinGlass.UniversalDictionary
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_MatrixPhysical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir Filter Set
open scoped NNReal BigOperators Topology
variable {L p k : ℕ}

/-- Centered exact-matrix multioverlap history of the actual physical root.
The root alphabet includes every sampled marker, and its entire old test is
retained. This definition uses no analytic decorrelation identity. -/
noncomputable def physicalMatrixCovariance (m : Fin (L+1) → ℝ)
    (S : PrescribedTree (L+1)) (a : S.Leaf) (M : Model p) (C H : ℝ)
    (N : ℕ) (u : Spec L×ℕ → ℝ) (T : PrescribedTree (L+1)) (q : Option (Fin k) → T.Leaf)
    (f : (S.Leaf → FinitePath (Fin N → Spin) (L+1)) → ℝ) : ℝ :=
  matrixRootCovariance
    (fullRootLaw (fun _ : Fin N => M.field.toMeasure) (bondLaw M N)
      (markLaw (weights L) N) (M.alpha*N) (scoreRate N))
    (rootAlphabet (Ω := Fin N → Spin) (A := fun i : Labels L (Site N) => Alphabet i.1.1)) T S q
    (rootTower (KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L)
      (fun i => prior i.1.1) m (physicalBase M C H N)
      (dictionaryFactor (observableAt direction N) (observableAt anchor N) u))
    (Fin.cons 0 m) (List.ofFn (fun j : Fin k => (some j : Option (Fin k)))).reverse a
    (fun z => spatialProduct (fun _ => rootVector
      (readVector (fun v x => readSpin (KernelTower.terminalState L x) v)) z))
    (fun z x => f (fun b => physical (rootArray z.2.2.1 z.2.2.2) (L+1) (S.pathAt b x)))

end DilutedSpinGlass.UniversalDictionary
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ProjectionShiftError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.DepthAverage
noncomputable local instance projectionShiftAveragePropDecidable (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition

end DilutedSpinGlass.DepthAverage
namespace DilutedSpinGlass.ReducedTopology
open scoped BigOperators
noncomputable local instance projectionShiftErrorPropDecidable_rf13f56_1 (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
variable {Ω α ι : Type} [Fintype Ω] [Fintype α] [DecidableEq α] [Fintype ι]
  {L N : ℕ} [NeZero L]

 
noncomputable def projectionShiftError (a : α) (C : ι → ReducedTopology)
    (e : (j : ι) → (C j).Vertex → {j : α // j≠a})
    (T : KernelTower Ω L) (f : FinitePath Ω L → Fin N → ℝ) (Q : α → Fin L) : ℝ :=
  2*Real.sqrt (projectorChangeSq T
    (conditionalScheduledProduct L 0 ((Q a).val+1) C (fun j v => (Q (e j v)).val+1) T f)
    (conditionalScheduledProduct L 0 (Q a).val C (fun j v => (Q (e j v)).val) T f))

end DilutedSpinGlass.ReducedTopology
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_RootProjectionIntegrability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory PrescribedTree
open scoped BigOperators
variable {Ω I X Y C : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] [Fintype C] [DecidableEq C] {M N n : ℕ}
attribute [local irreducible] PrescribedTree.matrixProjectionError PrescribedTree.oldProjectionError
    KernelTower.halfTripleDifferenceAt PrescribedTree.splitProjector

variable (S : PrescribedTree n) (r d : ℕ)
    (T : KernelTower Ω (n+r+1+d)) (Q : (i : I) → Fin (n+r+1+d) → FiniteLaw (A i))
    (m : Fin (n+r+1+d) → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω (n+r+1+d) → ℝ)
    (old : (i : I) → FinitePath Ω (n+r+1+d) → FinitePath (A i) (n+r+1+d) → ℝ)
    (V : FinitePath Ω (n+r+1+d) → Fin N → ℝ)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))

noncomputable def rootSplitProjector (z : FullRootState Y X I M)
    (x : FinitePath (rootAlphabet (Ω := Ω) (A := A) z) (n+r+1+d)) (i : Fin N) : ℝ :=
  splitProjector S r d (rootTower T Q m base old z) (fun y => rootVector V z y i) x

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_RootProjectionShiftError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.DepthAverage
open _root_.MeasureTheory
open scoped BigOperators
noncomputable local instance rootProjectionShiftErrorDecidable (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition

end DilutedSpinGlass.DepthAverage
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_HeightTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass

/-- Transport along equality of total depths only; no change to a kernel. -/
def kernelHeightCast {Ω : Type} [Fintype Ω] {n m : ℕ} (h : n=m)
    (T : KernelTower Ω n) : KernelTower Ω m := h ▸ T

def pathHeightCast {Ω : Type} {n m : ℕ} (h : n=m)
    (x : FinitePath Ω n) : FinitePath Ω m := h ▸ x

def vectorHeightCast {Ω : Type} {n m N : ℕ} (h : n=m)
    (f : FinitePath Ω n → Fin N → ℝ) : FinitePath Ω m → Fin N → ℝ :=
  fun x => f (pathHeightCast h.symm x)

@[simp] theorem kernelHeightCast_inv {Ω : Type} [Fintype Ω] {n m : ℕ} (h : n=m)
    (T : KernelTower Ω m) : kernelHeightCast h (kernelHeightCast h.symm T)=T := by cases h; rfl
@[simp] theorem vectorHeightCast_inv {Ω : Type} {n m N : ℕ} (h : n=m)
    (f : FinitePath Ω m → Fin N → ℝ) : vectorHeightCast h (vectorHeightCast h.symm f)=f := by cases h; rfl

namespace PrescribedTree
variable {Ω I : Type} [Fintype Ω] [Fintype I] [DecidableEq I] {n m N : ℕ}

def heightCast (h : n=m) (S : PrescribedTree n) : PrescribedTree m := h ▸ S

def leafHeightCast (h : n=m) (S : PrescribedTree n) (a : S.Leaf) : (heightCast h S).Leaf := by
  cases h; exact a

@[simp] theorem splitDepth_heightCast (h : n=m) (S : PrescribedTree n) (a b : S.Leaf) :
    splitDepth (heightCast h S) (leafHeightCast h S a) (leafHeightCast h S b)=splitDepth S a b := by
  cases h; rfl

omit [DecidableEq I] in
@[simp] theorem matrixProjectionError_heightCast (h : n=m) (S : PrescribedTree n)
    (q : I → S.Leaf) (T : KernelTower Ω n) (a c : I)
    (f X : FinitePath Ω n → Fin N → ℝ) :
    matrixProjectionError (heightCast h S) (fun j => leafHeightCast h S (q j))
      (kernelHeightCast h T) a c (spatialProduct (fun _ : I => vectorHeightCast h f))
      (vectorHeightCast h X)=
    matrixProjectionError S q T a c (spatialProduct (fun _ : I => f)) X := by cases h; rfl

end PrescribedTree
namespace ReducedTopology
variable {Ω ι : Type} [Fintype Ω] [Fintype ι] {n m N : ℕ}

@[simp] theorem conditionalScheduledProduct_heightCast (h : n=m) (d p : ℕ)
    (C : ι → ReducedTopology) (q : (j : ι) → (C j).Vertex → ℕ) (T : KernelTower Ω n)
    (f : FinitePath Ω n → Fin N → ℝ) :
    vectorHeightCast h (conditionalScheduledProduct n d p C q T f)=
      conditionalScheduledProduct m d p C q (kernelHeightCast h T) (vectorHeightCast h f) := by
  cases h; rfl

@[simp] theorem projectionShiftError_heightCast {α : Type} [Fintype α] [DecidableEq α]
    (h : n=m) (a : α) (C : ι → ReducedTopology)
    (e : (j : ι) → (C j).Vertex → {j : α // j≠a})
    (T : KernelTower Ω n) (f : FinitePath Ω n → Fin N → ℝ) (Q : α → Fin n) :
    projectionShiftError a C e (kernelHeightCast h T) (vectorHeightCast h f) (fun j => Fin.cast h (Q j))=
      projectionShiftError a C e T f Q := by cases h; rfl

end ReducedTopology
end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_RootChildSumIntegrability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory PrescribedTree
open scoped BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {M N n L : ℕ}

variable (k : ℕ) (C : Fin k → PrescribedTree n) (r d : ℕ) (h : L=n+1+r+1+d)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (old : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (V : FinitePath Ω L → Fin N → ℝ)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))

noncomputable def rootChildSum (z : FullRootState Y X I M) : ℝ :=
  (k:ℝ)*∑ j, Real.sqrt (descendantEnergyAt (C j) r d
    (kernelHeightCast h (rootTower T Q m base old z)) (vectorHeightCast h (rootVector V z)))

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_DepthChildMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.DepthAverage
open scoped BigOperators
noncomputable local instance depthChildMomentDecidable (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition

end DilutedSpinGlass.DepthAverage
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ScheduledFrameError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.ReducedTopology
open scoped BigOperators
variable {Ω α I : Type} [Fintype Ω] [Fintype α] [DecidableEq α]
  [Fintype I] [DecidableEq I] {N : ℕ}

 
theorem shiftedFrameHeight (H r d : ℕ) : H+1+(r+1)+1+d=H+1+1+r+1+d := by omega

end DilutedSpinGlass.ReducedTopology
end

end

section
section
namespace DilutedSpinGlass
variable {Ω : Type} [Fintype Ω] {n m N : ℕ}

@[simp] lemma kernelHeightCast_succ_fst (h : n+1=m+1) (T : KernelTower Ω (n+1)) :
    (kernelHeightCast h T).1=T.1 := by
  have hm := Nat.succ.inj h
  subst m
  rfl

@[simp] lemma kernelHeightCast_succ_snd (h : n+1=m+1) (T : KernelTower Ω (n+1)) (x : Ω) :
    (kernelHeightCast h T).2 x=kernelHeightCast (Nat.succ.inj h) (T.2 x) := by
  have hm := Nat.succ.inj h
  subst m
  rfl

omit [Fintype Ω] in
@[simp] lemma vectorHeightCast_succ_pair (h : n+1=m+1)
    (f : FinitePath Ω (n+1) → Fin N → ℝ) (x : Ω) (y : FinitePath Ω m) :
    vectorHeightCast h f (x,y)=vectorHeightCast (Nat.succ.inj h) (fun z => f (x,z)) y := by
  have hm := Nat.succ.inj h
  subst m
  rfl

end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ScheduledCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.ReducedTopology
open PrescribedTree
variable {Ω : Type} [Fintype Ω] {N L : ℕ}

/-- The actual single-copy conditional covariance of a reduced topology at a
specified evaluation depth, with all unary grid transitions retained. Outside
the available evaluation horizon it is zero; all induction applications are
inside the literal admissible regular-depth domain. -/
noncomputable def scheduledShapeEnergy (L d : ℕ) (S : ReducedTopology) (q : S.Vertex → ℕ)
    (T : KernelTower Ω L) (f : FinitePath Ω L → Fin N → ℝ) : ℝ :=
  if h : d<L then
    shapeEnergyAt (realize (L-(d+1)) (d+1) S q) d
      (kernelHeightCast (by omega) T) (vectorHeightCast (by omega) f)
  else 0

@[simp] lemma scheduledShapeEnergy_heightCast {n m : ℕ} (h : n=m) (d : ℕ)
    (S : ReducedTopology) (q : S.Vertex → ℕ) (T : KernelTower Ω n)
    (f : FinitePath Ω n → Fin N → ℝ) :
    scheduledShapeEnergy m d S q (kernelHeightCast h T) (vectorHeightCast h f) =
      scheduledShapeEnergy n d S q T f := by
  cases h
  rfl

end DilutedSpinGlass.ReducedTopology
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ScheduledRootMultileaf
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.ReducedTopology
open _root_.MeasureTheory DepthAverage
open scoped BigOperators
noncomputable local instance scheduledRootMultileafDecidableEq (type : Type) :
    DecidableEq type := Classical.decEq type

noncomputable local instance scheduledRootMultileafDecidable_rf13f56_1 (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
/-- The literal single-copy depth domain: one evaluation coordinate, the
branching coordinates, their strict ancestry and the regular interior cube. -/
def regularShapeDomain (S : ReducedTopology) (L : ℕ) [NeZero L] (η : ℝ)
    (Q : Option S.Vertex → Fin L) : Prop :=
  Regular η Q ∧ Admissible S (fun v => (Q (some v)).val) ((Q none).val+1) L

/-- A proper child retains the first branching coordinate as its evaluation
coordinate, and precisely its own internal branching coordinates. -/
def childCoordinates {k : ℕ+} {hk : 2≤(k:ℕ)} {C : Fin k → ReducedTopology}
    (j : Fin k) : Option (C j).Vertex → Option (ReducedTopology.node k hk C).Vertex
  | none => some none
  | some v => some (some ⟨j,v⟩)

end DilutedSpinGlass.ReducedTopology
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_RootChildMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass
open _root_.MeasureTheory
open scoped BigOperators

namespace HeterogeneousMarks
open PrescribedTree
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {M N n L : ℕ}

variable (k : ℕ) (C : Fin k → PrescribedTree n) (r d : ℕ) (h : L=n+1+r+1+d)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (old : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (V : FinitePath Ω L → Fin N → ℝ)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    (μ : Measure (FullRootState Y X I M)) [IsProbabilityMeasure μ]

/-- The actual root child energies, not an independent paired-copy law. -/
noncomputable def rootChildMeanSum : ℝ :=
  (k:ℝ)*∑ j, Real.sqrt (∫ z, descendantEnergyAt (C j) r d
    (kernelHeightCast h (rootTower T Q m base old z)) (vectorHeightCast h (rootVector V z)) ∂μ)

end HeterogeneousMarks
end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ShiftedFrameGeometry
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {n : ℕ}

noncomputable local instance shiftedFrameGeometryPropDecidable_rf13f56_1 (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
/-- Charged depths after retaining the genuine shared prefix above d. -/
noncomputable def shiftedPrefixDepths (S : PrescribedTree n) (d : ℕ) : Finset ℕ :=
  (shiftedTwinDepths S).image (fun u => u+d)

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ScheduledFrameGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {n m : ℕ}
@[simp] lemma branchingCount_heightCast (h : n=m) (S : PrescribedTree n) (P : ℕ → Prop) :
    branchingCount (heightCast h S) P=branchingCount S P := by cases h; rfl

end DilutedSpinGlass.PrescribedTree

end

end

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators

/-- The literal tail of the universal dictionary's reversed insertion list. -/
def canonicalMatrixTail (t : ℕ) : List (Option (Fin (t+1))) :=
  (List.ofFn (fun j : Fin t => some j.castSucc)).reverse

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_PhysicalTreeMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir Filter Set
open scoped NNReal BigOperators Topology
variable {L p k : ℕ}

/-- Literal centered history for the multileaf old overlap, with the actual
variable-marker root alphabet. -/
noncomputable def physicalTreeMatrixCovariance (m : Fin (L+1) → ℝ)
    (S : PrescribedTree (L+1)) (a : S.Leaf) (M : Model p) (C H : ℝ)
    (N : ℕ) (u : Spec L×ℕ → ℝ) (T : PrescribedTree (L+1)) (q : Option (Fin k) → T.Leaf) : ℝ :=
  matrixRootCovariance
    (fullRootLaw (fun _ : Fin N => M.field.toMeasure) (bondLaw M N)
      (markLaw (weights L) N) (M.alpha*N) (scoreRate N))
    (rootAlphabet (Ω := Fin N → Spin) (A := fun i : Labels L (Site N) => Alphabet i.1.1)) T S q
    (rootTower (KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L)
      (fun i => prior i.1.1) m (physicalBase M C H N)
      (dictionaryFactor (observableAt direction N) (observableAt anchor N) u))
    (Fin.cons 0 m) (List.ofFn (fun j : Fin k => (some j : Option (Fin k)))).reverse a
    (fun z => spatialProduct (fun _ => rootVector
      (readVector (fun v x => readSpin (KernelTower.terminalState L x) v)) z))
    (fun z => treeOverlap S (rootVector
      (readVector (fun v x => readSpin (KernelTower.terminalState L x) v)) z))

end DilutedSpinGlass.UniversalDictionary
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_RegularPhysicalShift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.ReducedTopology

noncomputable local instance instDecidableEq_rf13f56_1 (β : Type) : DecidableEq β := Classical.decEq β
def childBranchCoordinates {k : ℕ+} {hk : 2≤(k:ℕ)} {C : Fin k → ReducedTopology}
    (j : Fin k) (v : (C j).Vertex) :
    {x : Option (ReducedTopology.node k hk C).Vertex // x≠some none} :=
  ⟨some (some ⟨j,v⟩),by simp⟩

end DilutedSpinGlass.ReducedTopology
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir
open ReducedTopology
open scoped NNReal BigOperators
noncomputable local instance instDecidableEq_solutions (β : Type) : DecidableEq β := Classical.decEq β
attribute [local irreducible] projectionShiftError

end DilutedSpinGlass.UniversalDictionary
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_PhysicalScheduledStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir
open ReducedTopology
open scoped NNReal BigOperators
noncomputable local instance physicalScheduledStepDecidableEq (carrier : Type) :
    DecidableEq carrier := Classical.decEq carrier
variable {p : ℕ}

 
noncomputable def physicalScheduledEnergy (M : Model p) (θB hB : ℝ) (N L : ℕ)
    (u : Spec L × ℕ → ℝ) (S : ReducedTopology) (Q : Option S.Vertex → Fin (L+1)) : ℝ :=
  ∫ z, scheduledShapeEnergy (L+1) (Q none).val S (fun v => (Q (some v)).val)
    (rootTower (KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L)
      (fun i : Labels L (Site N) => prior i.1.1) (gridExponents L) (physicalBase M θB hB N)
      (dictionaryFactor (observableAt direction N) (observableAt anchor N) u) z)
    (rootVector (readVector (fun v x => readSpin (KernelTower.terminalState L x) v))
      (I := Labels L (Site N)) (A := fun i => Alphabet i.1.1) (X := Bond p N) (Y := ℝ) (M := N) z)
    ∂fullRootLaw (fun _ : Fin N => M.field.toMeasure) (bondLaw M N)
      (markLaw (weights L) N) (M.alpha*N) (scoreRate N)

end DilutedSpinGlass.UniversalDictionary
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_RegularNodeGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree

@[simp] lemma leaves_heightCast {n m : ℕ} (h : n=m) (S : PrescribedTree n) :
    leaves (heightCast h S)=leaves S := by cases h; rfl

@[simp] lemma canonicalMatrixTail_length (t : ℕ) : (canonicalMatrixTail t).length=t := by
  simp [canonicalMatrixTail]

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.ReducedTopology
open PrescribedTree
open scoped BigOperators

/-- A grid-independent budget for all leaves and history colors used in the
aligned two-copy experiment of a fixed topology. -/
def nodeHistoryBudget (k : ℕ+) (hk : 2≤(k:ℕ)) (C : Fin k → ReducedTopology) : ℕ :=
  4*Fintype.card (ReducedTopology.node k hk C).Leaf

noncomputable def nodeChargeConstant (k : ℕ+) (hk : 2≤(k:ℕ))
    (C : Fin k → ReducedTopology) (η : ℝ) : ℝ :=
  let R := nodeHistoryBudget k hk C
  (((2+(R:ℝ))*(R:ℝ))^(2*Fintype.card (ReducedTopology.node k hk C).Leaf-2+1)) /
    (min η 1)^R

end DilutedSpinGlass.ReducedTopology

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_RegularNodeEstimates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir
open ReducedTopology
open scoped NNReal BigOperators
noncomputable local instance regularNodeEstimatesDecidableEq (carrier : Type) :
    DecidableEq carrier := Classical.decEq carrier
variable {p : ℕ}

/-- The old or genuinely delayed proper-child projection cost, in the same
physical scheduled covariance family as the parent. -/
noncomputable def physicalChildMass (M : Model p) (θB hB : ℝ) (N L : ℕ)
    (u : Spec L × ℕ → ℝ) (k : ℕ+) (hk : 2≤(k:ℕ)) (C : Fin k → ReducedTopology)
    (s : Bool) (Q : Option (ReducedTopology.node k hk C).Vertex → Fin (L+1)) : ℝ :=
  (k:ℝ)*∑ j, Real.sqrt (physicalScheduledEnergy M θB hB N L u (C j)
    (DepthAverage.coordinateProjection (childCoordinates (hk := hk) j)
      (fun _ => DepthAverage.shiftPerm s) Q))


noncomputable def physicalNodeShift (M : Model p) (θB hB : ℝ) (N L : ℕ)
    (u : Spec L × ℕ → ℝ) (k : ℕ+) (hk : 2≤(k:ℕ)) (C : Fin k → ReducedTopology)
    (Q : Option (ReducedTopology.node k hk C).Vertex → Fin (L+1)) : ℝ :=
  ∫ z, projectionShiftError (some none) C (fun j => childBranchCoordinates (hk := hk) j)
    (rootTower (KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L)
      (fun i : Labels L (Site N) => prior i.1.1) (gridExponents L) (physicalBase M θB hB N)
      (dictionaryFactor (observableAt direction N) (observableAt anchor N) u) z)
    (rootVector (readVector (fun v x => readSpin (KernelTower.terminalState L x) v))
      (I := Labels L (Site N)) (A := fun i => Alphabet i.1.1) (X := Bond p N) (Y := ℝ) (M := N) z) Q
    ∂fullRootLaw (fun _ : Fin N => M.field.toMeasure) (bondLaw M N)
      (markLaw (weights L) N) (M.alpha*N) (scoreRate N)

/-- Topology-dependent quadratic energy budget in the depth continuity bound. -/
noncomputable def nodeShiftBudget (k : ℕ+) (C : Fin k → ReducedTopology) : ℝ :=
  8*((k:ℝ)*(∑ j, (Fintype.card (C j).Vertex:ℝ)*
    (∑ v : (C j).Vertex, (vertexArity (C j) v:ℝ)^2))+(k:ℝ)^2)

end DilutedSpinGlass.UniversalDictionary

end

section
namespace DilutedSpinGlass
open _root_.MeasureTheory
open scoped NNReal
variable {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]

/-- A bounded-test distance, with the scale written outside the test. -/
def BoundedDistance (μ ν : Measure X) (d : ℝ) : Prop :=
  ∀ (f : X → ℝ), Measurable f → ∀ (B : ℝ), (∀ x, |f x|≤B) →
    |(∫ x, f x ∂μ)-(∫ x, f x ∂ν)|≤B*d

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_RegularNodeProducer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir
open ReducedTopology
open scoped NNReal BigOperators
noncomputable local instance instDecidableEq_solutions_1 (β : Type) : DecidableEq β := Classical.decEq β
attribute [local irreducible] projectionShiftError matrixProjectionError oldProjectionError
    matrixObservableHistory KernelTower.halfTripleDifferenceAt splitProjector

end DilutedSpinGlass.UniversalDictionary

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_RegularNodeAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir
open ReducedTopology Filter Set
open scoped NNReal BigOperators Topology
noncomputable local instance regularNodeAverageDecidableEq (carrier : Type) :
    DecidableEq carrier := Classical.decEq carrier
variable {p : ℕ}

/-- Regular depth-cube average of the literal physical covariance energy. -/
noncomputable def physicalShapeAverage (M : Model p) (θB hB : ℝ) (N L : ℕ)
    (u : Spec L × ℕ → ℝ) (S : ReducedTopology) (η : ℝ) : ℝ :=
  DepthAverage.average (regularShapeDomain S (L+1) η)
    (physicalScheduledEnergy M θB hB N L u S)

noncomputable def physicalChildrenAverage (M : Model p) (θB hB : ℝ) (N L : ℕ)
    (u : Spec L × ℕ → ℝ) (k : ℕ+) (C : Fin k → ReducedTopology) (η : ℝ) : ℝ :=
  Real.sqrt ((k:ℝ)*∑ j, Real.sqrt (physicalShapeAverage M θB hB N L u (C j) (η/2)))

end DilutedSpinGlass.UniversalDictionary

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_RegularCovarianceLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir
open ReducedTopology Filter Set
open scoped NNReal BigOperators Topology
noncomputable local instance regularCovarianceLimitDecidableEq (valueType : Type) :
    DecidableEq valueType := Classical.decEq valueType
variable {p L : ℕ}

/-- The two precise outputs of the shared physical reservoir selection used by
the covariance induction. A witness is produced below from the model, with its
low-increment and parameter bounds retained alongside it. -/
structure ScheduledControl (M : Model p) (θB hB : ℝ) (L : ℕ)
    (Ns : ℕ → ℕ) (us : ℕ → Spec L×ℕ → ℝ) : Prop where
  singleton : ∀ η : ℝ, 0<η → ∀ t : ℝ, 0<t → ∀ᶠ n in atTop,
    physicalShapeAverage M θB hB (Ns n+1) L (us n) .leaf η≤((L+1:ℕ):ℝ)⁻¹/η+t
  matrix : ∀ (α : Type) [Fintype α] [DecidableEq α]
    (D : (α → Fin (L+1)) → Prop)
    (S T : (α → Fin (L+1)) → PrescribedTree (L+1))
    (a : (Q : α → Fin (L+1)) → (S Q).Leaf)
    (k : (α → Fin (L+1)) → ℕ), (∀ Q, 0<k Q) →
    ∀ (q : (Q : α → Fin (L+1)) → Option (Fin (k Q)) → (T Q).Leaf)
      (denom : (α → Fin (L+1)) → ℝ),
    Tendsto (fun n => DepthAverage.average D (fun Q =>
      |physicalTreeMatrixCovariance (gridExponents L) (S Q) (a Q) M θB hB
        (Ns n+1) (us n) (T Q) (q Q)|/|denom Q|)) atTop (𝓝 0)

noncomputable def physicalShapeLimsup (M : Model p) (θB hB : ℝ) (L : ℕ)
    (Ns : ℕ → ℕ) (us : ℕ → Spec L×ℕ → ℝ) (S : ReducedTopology) (η : ℝ) : ℝ :=
  limsup (fun n => physicalShapeAverage M θB hB (Ns n+1) L (us n) S η) atTop

end DilutedSpinGlass.UniversalDictionary

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_FullRegularSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir
open ReducedTopology Filter Set
open scoped NNReal BigOperators Topology
variable {p L : ℕ}

noncomputable local instance fullRegularSelectionDecidableEq_rf13f56_1 (β : Type) :
    DecidableEq β := Classical.decEq β
/-- The full signed identity, retained for marker anchors as well as spin
anchors. This is the literal output of the analytic perturbation selector. -/
structure FullShapeControl (M : Model p) (C H : ℝ) (L : ℕ)
    (Ns : ℕ → ℕ) (us : ℕ → Spec L×ℕ → ℝ) : Prop where
  shape : ∀ (S : PrescribedTree (L+1)) (a : S.Leaf)
    (f : (n : ℕ) → (S.Leaf → FinitePath (Fin (Ns n+1) → Spin) (L+1)) → ℝ)
    (B : ℝ), 0≤B → (∀ n x, |f n x|≤B) →
    ∀ (k : ℕ) (F : (Option (Fin k) → Option (Fin k) → ℕ) → ℝ) (spinAnchor : Bool),
    Tendsto (fun n => physicalShapeCovariance (gridExponents L) S a M C H
      (Ns n+1) (us n) F spinAnchor (f n)) atTop (𝓝 0)

end DilutedSpinGlass.UniversalDictionary

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_MarkerJointHistory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
noncomputable local instance markerJointHistoryDecidableEq (carrier : Type) :
    DecidableEq carrier := Classical.decEq carrier
variable {Ω C : Type} [Fintype Ω] [Fintype C] {n : ℕ}

def markerEmbedding {D : Type} (a : D) : Option C → D ⊕ C :=
  Option.elim' (Sum.inl a) Sum.inr

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_MarkerGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {n : ℕ}

noncomputable def stemLeafEquiv (A : PrescribedTree n) (r : ℕ) : A.Leaf ≃ (stem A r).Leaf :=
  Equiv.ofBijective (stemLeaf A r) (stemLeaf_bijective A r)

@[simp] lemma stemLeafEquiv_apply (A : PrescribedTree n) (r : ℕ) (a : A.Leaf) :
    stemLeafEquiv A r a=stemLeaf A r a := rfl

def unaryLeafEquiv (A : PrescribedTree n) : A.Leaf ≃ (unary A).Leaf where
  toFun a := ⟨0,a⟩
  invFun a := a.2
  left_inv _ := rfl
  right_inv a := by rcases a with ⟨i,a⟩; have hi := Fin.eq_zero i; subst i; rfl

def markerFork (A : PrescribedTree n) : PrescribedTree (n+1) :=
  .node 2 (fun i : Fin 2 => Fin.cases (motive := fun _ => PrescribedTree n) (single n) (fun _ : Fin 1 => A) i)

def markerLeaf (A : PrescribedTree n) : Option A.Leaf → (markerFork A).Leaf
  | none => ⟨0,singleLeaf n⟩
  | some a => ⟨1,a⟩

def doubledLeaf (A : PrescribedTree n) : A.Leaf ⊕ A.Leaf → (doubled A).Leaf
  | .inl a => ⟨0,a⟩
  | .inr a => ⟨1,a⟩

noncomputable def markerOldIndex (A : PrescribedTree n) (r : ℕ) :
    (stem (unary A) r).Leaf ≃ A.Leaf :=
  (stemLeafEquiv (unary A) r).symm.trans (unaryLeafEquiv A).symm

noncomputable def markerOld (A : PrescribedTree n) (r : ℕ)
    (a : (stem (unary A) r).Leaf) : (stem (doubled A) r).Leaf :=
  stemLeaf (doubled A) r ⟨0,markerOldIndex A r a⟩

def markerFresh (A : PrescribedTree n) (r : ℕ) (a : A.Leaf) :
    (stem (doubled A) r).Leaf := stemLeaf (doubled A) r ⟨1,a⟩

def markerTarget (A : PrescribedTree n) (r : ℕ) : Option A.Leaf → (stem (markerFork A) r).Leaf :=
  stemLeaf (markerFork A) r ∘ markerLeaf A

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_MarkerNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
noncomputable local instance markerNormalizationPropDecidable (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_MarkerRootIdentity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory
open scoped BigOperators
noncomputable local instance markerRootIdentityDecidable (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_MarkerPhysicalBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PrescribedTree ConcreteReservoir
open scoped NNReal BigOperators
variable {Ω X Y : Type} [Fintype Ω] [MeasurableSpace X] [MeasurableSpace Y] {L M N k : ℕ}

variable (S : PrescribedTree (L+1)) (a : S.Leaf) (K : KernelTower Ω (L+1))
    (m : Fin (L+2) → ℝ)
    (base : RootPath Y M → (n : ℕ) → RootPath X n → FinitePath Ω (L+1) → ℝ)
    (old : (i : Labels L (Site N)) → FinitePath Ω (L+1) → FinitePath (Alphabet i.1.1) (L+1) → ℝ)
    (read : Site N → FinitePath Ω (L+1) → Spin)
    (T : PrescribedTree (L+1)) (q : Option (Fin k) → T.Leaf)
    (f : (S.Leaf → FinitePath Ω (L+1)) → ℝ)

/-- A matrix multioverlap at the actual heterogeneous physical root,
retaining the literal old-test transport and root-dependent alphabet. -/
noncomputable def rootMarkerObservable (z : FullRootState Y X (Labels L (Site N)) M) : ℝ :=
  matrixObservableHistory T q
    (rootTower K (fun i => prior i.1.1) (fun j => m j.succ) base old z) m
    (List.ofFn (fun j : Fin k => (some j : Option (Fin k)))).reverse S a
    (spatialProduct (fun c x i => match c with | none => 1 | some _ => rootVector (readVector read) z x i))
    (fun x => f (fun b => physical (rootArray z.2.2.1 z.2.2.2) (L+1) (S.pathAt b x)))

end DilutedSpinGlass.UniversalDictionary

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_MarkerConcrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory
open scoped BigOperators
variable {Z : Type} [MeasurableSpace Z] {n N : ℕ}

noncomputable local instance instDecidable_12_rf13f56_1 (p : Prop) : Decidable p := Classical.propDecidable p
noncomputable def markerColorEquiv (A : PrescribedTree n) :
    Fin (Fintype.card A.Leaf) ≃ A.Leaf := (Fintype.equivFin A.Leaf).symm

noncomputable def markerColorTarget (A : PrescribedTree n) (r : ℕ) :
    Option (Fin (Fintype.card A.Leaf)) → (stem (markerFork A) r).Leaf :=
  markerTarget A r ∘ (Equiv.optionCongr (markerColorEquiv A))

noncomputable def markerColorFresh (A : PrescribedTree n) (r : ℕ) :
    Fin (Fintype.card A.Leaf) → (stem (doubled A) r).Leaf :=
  markerFresh A r ∘ markerColorEquiv A

noncomputable def markerColorOld (A : PrescribedTree n) (r : ℕ) :
    Fin (Fintype.card A.Leaf) ≃ (stem (unary A) r).Leaf :=
  (markerColorEquiv A).trans (markerOldIndex A r).symm

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_MarkerVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω : Type} [Fintype Ω] {n N : ℕ}

/-- The complete overlap in one of two conditionally independent descendants
of an actually sampled stem. -/
noncomputable def forkOverlap (A : PrescribedTree n) : (r : ℕ) →
    (FinitePath Ω (n+1+r) → Fin N → ℝ) → Fin 2 → Sample Ω (stem (doubled A) r) → ℝ
  | 0, V, j, w => treeOverlap A (fun y => V ((w j).1,y)) (w j).2
  | r+1, V, j, w => forkOverlap A r (fun y => V ((w 0).1,y)) j (w 0).2

noncomputable def forkPairMean (A : PrescribedTree n) (r : ℕ)
    (K : KernelTower Ω (n+1+r)) (V : FinitePath Ω (n+1+r) → Fin N → ℝ) : ℝ :=
  ((stem (doubled A) r).sampleLaw K).expect (fun w => forkOverlap A r V 0 w * forkOverlap A r V 1 w)

noncomputable def unarySquareMean (A : PrescribedTree n) (r : ℕ)
    (K : KernelTower Ω (n+1+r)) (V : FinitePath Ω (n+1+r) → Fin N → ℝ) : ℝ :=
  ((stem (unary A) r).sampleLaw K).expect (fun w => (treeOverlap (stem (unary A) r) V w)^2)

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_RootOverlapVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.FiniteLaw
open _root_.MeasureTheory
variable {Z : Type} [MeasurableSpace Z]

noncomputable def mixedVariance (μ : Measure Z) (Ω : Z → Type) [∀ z, Fintype (Ω z)]
    (P : (z : Z) → FiniteLaw (Ω z)) (F : (z : Z) → Ω z → ℝ) : ℝ :=
  (∫ z, (P z).expect (fun w => (F z w)^2) ∂μ) - (∫ z, (P z).expect (F z) ∂μ)^2

end DilutedSpinGlass.FiniteLaw
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory
open scoped BigOperators
variable {Z : Type} [MeasurableSpace Z] {n N : ℕ}

noncomputable local instance rootOverlapVarianceDecidable_rf13f56_1 (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
noncomputable def overlapVariance (μ : Measure Z) (Ω : Z → Type) [∀ z, Fintype (Ω z)]
    (S : PrescribedTree n) (K : (z : Z) → KernelTower (Ω z) n)
    (V : (z : Z) → FinitePath (Ω z) n → Fin N → ℝ) : ℝ :=
  FiniteLaw.mixedVariance μ (fun z => Sample (Ω z) S)
    (fun z => S.sampleLaw (K z)) (fun z => treeOverlap S (V z))

noncomputable def markerDefect (μ : Measure Z) (Ω : Z → Type) [∀ z, Fintype (Ω z)]
    (A : PrescribedTree n) (r : ℕ) (K : (z : Z) → KernelTower (Ω z) (n+1+r))
    (V : (z : Z) → FinitePath (Ω z) (n+1+r) → Fin N → ℝ) : ℝ :=
  (∫ z, forkPairMean A r (K z) (V z) ∂μ) -
    (∫ z, ((stem (unary A) r).sampleLaw (K z)).expect (treeOverlap (stem (unary A) r) (V z)) ∂μ)^2

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_PhysicalMarkerControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory
open scoped BigOperators
variable {Z : Type} [MeasurableSpace Z] {h N k : ℕ}

noncomputable local instance instDecidableEq_rf13f56_2 (β : Type) : DecidableEq β := Classical.decEq β
noncomputable def markerMatrixCovariance (μ : Measure Z) (Ω : Z → Type) [∀ z, Fintype (Ω z)]
    (S : PrescribedTree h) (a : S.Leaf) (T : PrescribedTree h) (q : Option (Fin k) → T.Leaf)
    (K : (z : Z) → KernelTower (Ω z) h) (m : Fin (h+1) → ℝ)
    (V : (z : Z) → FinitePath (Ω z) h → Fin N → ℝ) : ℝ :=
  matrixRootCovariance μ Ω T S q K m
    (List.ofFn (fun c : Fin k => (some c : Option (Fin k)))).reverse a
    (fun z => spatialProduct (fun c x i => match c with | none => 1 | some _ => V z x i))
    (fun z => treeOverlap S (V z))

@[simp] lemma markerMatrixCovariance_heightCast {h' : ℕ} (e : h=h')
    (μ : Measure Z) (Ω : Z → Type) [∀ z, Fintype (Ω z)]
    (S : PrescribedTree h) (a : S.Leaf) (T : PrescribedTree h) (q : Option (Fin k) → T.Leaf)
    (K : (z : Z) → KernelTower (Ω z) h) (m : Fin (h+1) → ℝ)
    (V : (z : Z) → FinitePath (Ω z) h → Fin N → ℝ) :
    markerMatrixCovariance μ Ω (heightCast e S) (leafHeightCast e S a)
      (heightCast e T) (fun c => leafHeightCast e T (q c))
      (fun z => kernelHeightCast e (K z)) (fun j => m (Fin.cast (congrArg (fun a => a+1) e.symm) j))
      (fun z => vectorHeightCast e (V z)) = markerMatrixCovariance μ Ω S a T q K m V := by
  cases e
  rfl

@[simp] lemma overlapVariance_heightCast {h' : ℕ} (e : h=h')
    (μ : Measure Z) (Ω : Z → Type) [∀ z, Fintype (Ω z)] (S : PrescribedTree h)
    (K : (z : Z) → KernelTower (Ω z) h)
    (V : (z : Z) → FinitePath (Ω z) h → Fin N → ℝ) :
    overlapVariance μ Ω (heightCast e S) (fun z => kernelHeightCast e (K z))
      (fun z => vectorHeightCast e (V z)) = overlapVariance μ Ω S K V := by
  cases e
  rfl

end DilutedSpinGlass.PrescribedTree
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir Filter
open scoped NNReal BigOperators Topology
variable {L p k : ℕ}

noncomputable def physicalMarkerMatrixCovariance (m : Fin (L+1) → ℝ)
    (S : PrescribedTree (L+1)) (a : S.Leaf) (M : Model p) (C H : ℝ)
    (N : ℕ) (u : Spec L×ℕ → ℝ) (T : PrescribedTree (L+1)) (q : Option (Fin k) → T.Leaf) : ℝ :=
  markerMatrixCovariance
    (fullRootLaw (fun _ : Fin N => M.field.toMeasure) (bondLaw M N)
      (markLaw (weights L) N) (M.alpha*N) (scoreRate N))
    (rootAlphabet (Ω := Fin N → Spin) (A := fun i : Labels L (Site N) => Alphabet i.1.1)) S a T q
    (rootTower (KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L)
      (fun i => prior i.1.1) m (physicalBase M C H N)
      (dictionaryFactor (observableAt direction N) (observableAt anchor N) u))
    (Fin.cons 0 m)
    (rootVector (readVector (fun v x => readSpin (KernelTower.terminalState L x) v)))

end DilutedSpinGlass.UniversalDictionary

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ScheduledMarkerEstimate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.ReducedTopology
open _root_.MeasureTheory PrescribedTree
variable {Z : Type} [MeasurableSpace Z] {L N : ℕ}

@[simp] lemma realize_heightCast {n m : ℕ} (e : n=m) (d : ℕ)
    (S : ReducedTopology) (q : S.Vertex → ℕ) :
    heightCast e (realize n d S q)=realize m d S q := by cases e; rfl

noncomputable def scheduledOverlapVariance (μ : Measure Z) (Ω : Z → Type) [∀ z, Fintype (Ω z)]
    (S : ReducedTopology) (q : S.Vertex → ℕ) (K : (z : Z) → KernelTower (Ω z) L)
    (V : (z : Z) → FinitePath (Ω z) L → Fin N → ℝ) : ℝ :=
  overlapVariance μ Ω (realize L 0 S q) K V

noncomputable def scheduledMarkerDefect (μ : Measure Z) (Ω : Z → Type) [∀ z, Fintype (Ω z)]
    (d : ℕ) (S : ReducedTopology) (q : S.Vertex → ℕ) (K : (z : Z) → KernelTower (Ω z) L)
    (V : (z : Z) → FinitePath (Ω z) L → Fin N → ℝ) : ℝ :=
  if h : d<L then markerDefect μ Ω (realize (L-(d+1)) (d+1) S q) d
    (fun z => kernelHeightCast (by omega) (K z)) (fun z => vectorHeightCast (by omega) (V z)) else 0

end DilutedSpinGlass.ReducedTopology

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_OverlapDepthAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.DepthAverage
open scoped BigOperators
noncomputable local instance overlapDepthAveragePropDecidable (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition

end DilutedSpinGlass.DepthAverage

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_RegularOverlapGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.ReducedTopology
open DepthAverage
noncomputable local instance regularOverlapGeometryDecidableEq_rf13f56_1 (type : Type) :
    DecidableEq type := Classical.decEq type
noncomputable local instance regularOverlapGeometryPropDecidable_rf13f56_1 (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
variable {L : ℕ} [NeZero L]

def regularOverlapDomain (S : ReducedTopology) (L : ℕ) [NeZero L] (η : ℝ)
    (q : S.Vertex → Fin L) : Prop :=
  Regular η q ∧ Admissible S (fun v => (q v).val) 0 L

end DilutedSpinGlass.ReducedTopology

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_PhysicalOverlapConcentration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir
open ReducedTopology Filter Set
open scoped NNReal BigOperators Topology
variable {L p : ℕ}

noncomputable local instance physicalOverlapConcentrationDictionaryDecidableEq_rf13f56_1 (type : Type) :
    DecidableEq type := Classical.decEq type
noncomputable def physicalOverlapVariance (M : Model p) (C H : ℝ) (N L : ℕ)
    (u : Spec L×ℕ → ℝ) (S : ReducedTopology) (q : S.Vertex → Fin (L+1)) : ℝ :=
  scheduledOverlapVariance
    (fullRootLaw (fun _ : Fin N => M.field.toMeasure) (bondLaw M N)
      (markLaw (weights L) N) (M.alpha*N) (scoreRate N))
    (rootAlphabet (Ω := Fin N → Spin) (A := fun i : Labels L (Site N) => Alphabet i.1.1)) S (fun v => (q v).val)
    (rootTower (KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L)
      (fun i => prior i.1.1) (gridExponents L) (physicalBase M C H N)
      (dictionaryFactor (observableAt direction N) (observableAt anchor N) u))
    (rootVector (readVector (fun v x => readSpin (KernelTower.terminalState L x) v)))

noncomputable def physicalMarkerDefect (M : Model p) (C H : ℝ) (N L : ℕ)
    (u : Spec L×ℕ → ℝ) (S : ReducedTopology) (Q : Option S.Vertex → Fin (L+1)) : ℝ :=
  scheduledMarkerDefect
    (fullRootLaw (fun _ : Fin N => M.field.toMeasure) (bondLaw M N)
      (markLaw (weights L) N) (M.alpha*N) (scoreRate N))
    (rootAlphabet (Ω := Fin N → Spin) (A := fun i : Labels L (Site N) => Alphabet i.1.1))
    (Q none).val S (fun v => (Q (some v)).val)
    (rootTower (KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L)
      (fun i => prior i.1.1) (gridExponents L) (physicalBase M C H N)
      (dictionaryFactor (observableAt direction N) (observableAt anchor N) u))
    (rootVector (readVector (fun v x => readSpin (KernelTower.terminalState L x) v)))

end DilutedSpinGlass.UniversalDictionary

end

section
namespace DilutedSpinGlass.DepthAverage
open scoped BigOperators
noncomputable local instance physicalOverlapConcentrationAverageDecidable (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition

end DilutedSpinGlass.DepthAverage
namespace DilutedSpinGlass.ReducedTopology
open DepthAverage
open scoped BigOperators
noncomputable local instance physicalOverlapConcentrationTopologyDecidableEq (type : Type) :
    DecidableEq type := Classical.decEq type

end DilutedSpinGlass.ReducedTopology

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_MixedDeviation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.FiniteLaw
open _root_.MeasureTheory
open scoped BigOperators
variable {Z : Type} [MeasurableSpace Z]

noncomputable def mixedDeviation (μ : Measure Z) (Ω : Z → Type) [∀ z, Fintype (Ω z)]
    (P : (z : Z) → FiniteLaw (Ω z)) (F : (z : Z) → Ω z → ℝ) : ℝ :=
  ∫ z, (P z).expect (fun w => |F z w-(∫ y, (P y).expect (F y) ∂μ)|) ∂μ

end DilutedSpinGlass.FiniteLaw

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_PhysicalOverlapAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir
open ReducedTopology Filter Set
open scoped NNReal BigOperators Topology
noncomputable local instance physicalOverlapAverageDecidableEq (carrier : Type) :
    DecidableEq carrier := Classical.decEq carrier
variable {p L : ℕ}

noncomputable def physicalOverlapAverage (M : Model p) (C H : ℝ) (N L : ℕ)
    (u : Spec L×ℕ → ℝ) (S : ReducedTopology) (η : ℝ) : ℝ :=
  DepthAverage.average (regularOverlapDomain S (L+1) η) (physicalOverlapVariance M C H N L u S)

end DilutedSpinGlass.UniversalDictionary

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_PhysicalOverlapLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir
open ReducedTopology Filter Set
open scoped NNReal BigOperators Topology
noncomputable local instance physicalOverlapLimitDecidableEq (carrier : Type) :
    DecidableEq carrier := Classical.decEq carrier
variable {p L : ℕ}

noncomputable def physicalOverlapLimsup (M : Model p) (C H : ℝ) (L : ℕ)
    (Ns : ℕ → ℕ) (us : ℕ → Spec L×ℕ → ℝ) (S : ReducedTopology) (η : ℝ) : ℝ :=
  limsup (fun n => physicalOverlapAverage M C H (Ns n+1) L (us n) S η) atTop

end DilutedSpinGlass.UniversalDictionary

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_HierarchyBasic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.MeasureTheory Filter Set TopologicalSpace
open scoped Topology NNReal ENNReal

namespace DilutedSpinGlass

abbrev AtomicWeights (ι : Type*) [Fintype ι] := {w : ι → ℝ≥0 // ∑ i, w i = 1}

noncomputable def atomicProbability {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (x : ι → X) (w : AtomicWeights ι) : ProbabilityMeasure X :=
  ⟨∑ i, (w.val i : ℝ≥0∞) • Measure.dirac (x i), {
    measure_univ := by simp [← ENNReal.ofNNReal_finsetSum, w.property] }⟩

 theorem integral_atomicProbability {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    [MeasurableSingletonClass X] (x : ι → X) (w : AtomicWeights ι) (f : X → ℝ) :
    ∫ t, f t ∂(atomicProbability x w) = ∑ i, (w.val i : ℝ) * f (x i) := by
  change (∫ t, f t ∂(∑ i, (w.val i : ℝ≥0∞) • Measure.dirac (x i))) = _
  rw [integral_finsetSum_measure]
  · simp [NNReal.smul_def]
  · intro i _
    exact (integrable_dirac (by simp : ‖f (x i)‖ₑ < ∞)).smul_measure (by simp)

 theorem continuous_atomicProbability {X ι : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] [T1Space X] [Fintype ι] (x : ι → X) :
    Continuous (atomicProbability x) := by
  rw [ProbabilityMeasure.continuous_iff_forall_continuous_integral]
  intro f
  simp_rw [integral_atomicProbability]
  exact continuous_finsetSum _ (fun i _ =>
    (NNReal.continuous_coe.comp ((continuous_apply i).comp continuous_subtype_val)).mul
      continuous_const)

end DilutedSpinGlass

namespace DilutedSpinGlass

 theorem simple_map_atomic {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (s : SimpleFunc X X) (μ : ProbabilityMeasure X) :
    μ.map s.measurable.aemeasurable ∈ Set.range (atomicProbability (fun x : s.range => (x : X))) := by
  classical
  have hmap : μ.toMeasure.map s = ∑ a ∈ s.range, μ.toMeasure (s ⁻¹' {a}) • Measure.dirac a :=
    (Measure.ae_mem_finset_iff_map_eq_sum_dirac s.measurable.aemeasurable).mp
      (Eventually.of_forall s.mem_range_self)
  let w : s.range → ℝ≥0 := fun a => μ (s ⁻¹' {a.val})
  have hw : ∑ a, w a = 1 := by
    apply ENNReal.coe_injective
    have hh : (∑ a ∈ s.range, μ.toMeasure (s ⁻¹' {a})) = 1 := by
      simpa [Measure.map_apply s.measurable MeasurableSet.univ] using
        congrArg (fun ν : Measure X => ν Set.univ) hmap.symm
    calc
      ((∑ a, w a : ℝ≥0) : ℝ≥0∞) = ∑ a : s.range, μ.toMeasure (s ⁻¹' {a.val}) := by
        simp [w]
      _ = ∑ a ∈ s.range, μ.toMeasure (s ⁻¹' {a}) :=
        Finset.sum_coe_sort s.range (fun a => μ.toMeasure (s ⁻¹' {a}))
      _ = 1 := hh
  refine ⟨⟨w, hw⟩, ?_⟩
  apply Subtype.ext
  change (∑ a : s.range, (w a : ℝ≥0∞) • Measure.dirac (a : X)) = μ.toMeasure.map s
  rw [hmap]
  simpa [w] using
    (Finset.sum_coe_sort s.range (fun a => μ.toMeasure (s ⁻¹' {a}) • Measure.dirac a))

end DilutedSpinGlass

namespace DilutedSpinGlass

 theorem probability_map_tendsto {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : ProbabilityMeasure X)
    (s : ℕ → SimpleFunc X X) (hs : ∀ x, Tendsto (fun n => s n x) atTop (𝓝 x)) :
    Tendsto (fun n => μ.map (s n).measurable.aemeasurable) atTop (𝓝 μ) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro f
  have hmap (n : ℕ) : (∫ x, f x ∂(μ.map (s n).measurable.aemeasurable)) =
      ∫ x, f (s n x) ∂μ := by
    rw [ProbabilityMeasure.toMeasure_map, integral_map (s n).measurable.aemeasurable
      f.continuous.aestronglyMeasurable]
  simp_rw [hmap]
  apply tendsto_integral_of_dominated_convergence (fun _ => ‖f‖)
  · intro n
    exact (f.continuous.measurable.comp (s n).measurable).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    exact Eventually.of_forall (fun x => f.norm_coe_le_norm (s n x))
  · exact Eventually.of_forall (fun x => f.continuous.continuousAt.tendsto.comp (hs x))

/-- The missing recursive weak-hierarchy infrastructure: probability laws on
separable metric Borel spaces form a separable space for the actual weak
 topology. The finite approximations are global, not chosen separately by μ. -/
theorem probabilityMeasure_separable {X : Type*} [MetricSpace X]
    [SeparableSpace X] [MeasurableSpace X] [BorelSpace X] :
    SeparableSpace (ProbabilityMeasure X) := by
  classical
  let h : StronglyMeasurable (id : X → X) := stronglyMeasurable_id
  let s := h.approx
  let D : Set (ProbabilityMeasure X) := ⋃ n, Set.range
    (atomicProbability (fun x : (s n).range => (x : X)))
  have hD : IsSeparable D := by
    apply IsSeparable.iUnion
    intro n
    exact isSeparable_range (continuous_atomicProbability _)
  apply (Dense.isSeparable_iff ?_).mp hD
  intro μ
  apply isClosed_closure.mem_of_tendsto (probability_map_tendsto μ s h.tendsto_approx)
  apply Eventually.of_forall
  intro n
  apply subset_closure
  exact Set.mem_iUnion.mpr ⟨n, simple_map_atomic (s n) μ⟩

end DilutedSpinGlass
namespace DilutedSpinGlass
open TopologicalSpace
open scoped BoundedContinuousFunction
local instance hierarchyBasicMeasurableSpace (space : TopCat) : MeasurableSpace space := borel space
local instance hierarchyBasicBorelSpace (space : TopCat) : BorelSpace space := ⟨rfl⟩

theorem hierarchy_properties (r : ℕ) : MetrizableSpace (Hierarchy r) ∧
    SeparableSpace (Hierarchy r) := by
  induction r with
  | zero => exact ⟨inferInstanceAs (MetrizableSpace ℝ), inferInstanceAs (SeparableSpace ℝ)⟩
  | succ r ih =>
    let : MetrizableSpace (Hierarchy r) := ih.1
    let : SeparableSpace (Hierarchy r) := ih.2
    let : MetricSpace (Hierarchy r) := metrizableSpaceMetric (Hierarchy r)
    exact ⟨inferInstanceAs (MetrizableSpace (ProbabilityMeasure (Hierarchy r))),
      probabilityMeasure_separable (X := Hierarchy r)⟩

instance hierarchyMetrizable (r : ℕ) : MetrizableSpace (Hierarchy r) :=
  (hierarchy_properties r).1
instance hierarchySeparable (r : ℕ) : SeparableSpace (Hierarchy r) :=
  (hierarchy_properties r).2

instance hierarchySecondCountable (r : ℕ) : SecondCountableTopology (Hierarchy r) := by
  let : MetricSpace (Hierarchy r) := metrizableSpaceMetric (Hierarchy r)
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)

end DilutedSpinGlass

end

section
namespace DilutedSpinGlass.ReducedTopology
open scoped BigOperators
noncomputable local instance hierarchyBasicDecidableEq (type : Type) :
    DecidableEq type := Classical.decEq type

noncomputable def nodes (k : ℕ+) (hk : 2≤(k:ℕ)) (s : Finset ReducedTopology) : Finset ReducedTopology :=
  Finset.univ.image (fun C : Fin k → {T // T∈s} => ReducedTopology.node k hk (fun j => (C j).val))

noncomputable def boundedTopologies : ℕ → Finset ReducedTopology
  | 0 => {.leaf}
  | n+1 => {.leaf} ∪ (Finset.univ : Finset (Fin (n+2))).biUnion
      (fun j => if h : 2≤j.val then nodes ⟨j.val,by omega⟩ h (boundedTopologies n) else ∅)

end DilutedSpinGlass.ReducedTopology

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_QTreeLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators

noncomputable local instance qTreeLawDecidableEq_rf13f56_1 (type : Type) :
    DecidableEq type := Classical.decEq type
noncomputable def qExpect {n : ℕ} (m : Fin (n+1) → ℝ)
    (F : PrescribedTree n → ℝ) : ℕ → PrescribedTree n → ℝ
  | 0, S => F S
  | k+1, S => ∑ v : Internal S, (-gamma S m v / leaves S) * qExpect m F k (grow S v)

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_FiniteLogExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω : Type} [Fintype Ω]

/-- Terminal moment of a genuine prescribed tree, then expectation over Q. -/
noncomputable def qMoment {n : ℕ} (m : Fin (n+1) → ℝ) (T : KernelTower Ω n)
    (D : FinitePath Ω n → ℝ) (k : ℕ) (S : PrescribedTree n) : ℝ :=
  qExpect m (fun R => (sampleLaw R T).expect (leafProduct R D)) k S

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.PrescribedTree
variable {Ω : Type} [Fintype Ω]
open scoped BigOperators Topology NNReal ENNReal
open Set Filter

noncomputable def logInsertion {n : ℕ} (T : KernelTower Ω n)
    (m : Fin (n+1) → ℝ) (D : FinitePath Ω n → ℝ) (t : ℝ) : ℝ :=
  KernelTower.backwardLog n T (fun j => m j.succ) (fun y => Real.log (1+t*D y))

noncomputable def logJet {n : ℕ} (T : KernelTower Ω n)
    (m : Fin (n+1) → ℝ) (D : FinitePath Ω n → ℝ) : ℕ → ℝ → ℝ
  | 0 => logInsertion T m D
  | k+1 => extensionIterate T m D k (single n) (leafProduct (single n) D)

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_QTopologyBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open scoped BigOperators

noncomputable def insertionRadius (C : ℝ) : ℝ := 1-Real.exp (-2*C-1)
noncomputable def normalizedInsertion (C x : ℝ) : ℝ :=
  (Real.exp (x-C)-1)/insertionRadius C

end DilutedSpinGlass

end

section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators

noncomputable local instance qTopologyBoundDecidableEq_rf13f56_1 (type : Type) :
    DecidableEq type := Classical.decEq type
noncomputable local instance qTopologyBoundDecidable_rf13f56_1 (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
/-- A shape-only constant, independent of every assigned depth and system size. -/
noncomputable def shapeCharge (k : ℕ) (S : ReducedTopology) : ℝ :=
  chargeBound (2*(1+k:ℕ)) ((Fintype.card S.Vertex:ℝ)*(1+k:ℕ)) k (Fintype.card S.Vertex)

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_SubsetTree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators

namespace SplitMap
variable {n : ℕ} {k l : ℕ+} {C : Fin k → PrescribedTree n} {D : Fin l → PrescribedTree n}

def ofChildren (e : Fin k → Fin l) (he : Function.Injective e)
    (f : ∀ i, SplitMap (C i) (D (e i))) : SplitMap (.node k C) (.node l D) where
  leaf a := ⟨e a.1,(f a.1).leaf a.2⟩
  split a b := by
    obtain ⟨i,a⟩ := a
    obtain ⟨j,b⟩ := b
    by_cases hij : i=j
    · subst j
      rw [splitDepth_same_child,splitDepth_same_child,(f i).split]
    · rw [splitDepth_diff_child _ _ _ (fun h => hij (he h)),splitDepth_diff_child _ _ _ hij]

end SplitMap

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_CavityBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.MeasureTheory Filter Set TopologicalSpace
open scoped Topology NNReal ENNReal BigOperators

namespace DilutedSpinGlass
@[simp] theorem q_pos (x : ℝ) (s : Spin) : 0 < q x s := by
  unfold q
  exact div_pos (Real.exp_pos _) (mul_pos (by norm_num) (Real.cosh_pos _))

@[simp] theorem q_sum (x : ℝ) : ∑ s : Spin, q x s = 1 := by
  rw [Fintype.sum_bool]
  simp only [q, spin, Bool.false_eq_true, ↓reduceIte, mul_one, mul_neg_one]
  rw [← add_div]
  rw [Real.cosh_eq]
  field_simp

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_MeasureHierarchy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.MeasureTheory Filter Set TopologicalSpace
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

namespace DilutedSpinGlass.MeasureMean

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- Logarithmic conditional power mean, for an arbitrary Borel probability law. -/
noncomputable def logMean (m : ℝ) (f : Ω → ℝ) : ℝ :=
  Real.log (∫ x, Real.exp (m * f x) ∂μ) / m

end DilutedSpinGlass.MeasureMean

namespace DilutedSpinGlass
local instance measureHierarchyContinuousMeasurableSpace (space : TopCat) :
    MeasurableSpace space := borel space

end DilutedSpinGlass

namespace DilutedSpinGlass
local instance measureHierarchyStabilityMeasurableSpace (space : TopCat) :
    MeasurableSpace space := borel space

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_RegularBadMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.DepthAverage
open scoped BigOperators
noncomputable local instance regularBadMassDecidable (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition

end DilutedSpinGlass.DepthAverage

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_FiniteEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory Set
open scoped NNReal BigOperators

noncomputable local instance finiteEncodingDecidableEq_rf13f56_1 (type : Type) :
    DecidableEq type := Classical.decEq type
lemma continuous_atomicProbability_joint {X ι : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] [T1Space X] [Fintype ι] :
    Continuous (fun z : (ι → X) × AtomicWeights ι => atomicProbability z.1 z.2) := by
  rw [ProbabilityMeasure.continuous_iff_forall_continuous_integral]
  intro f
  simp_rw [integral_atomicProbability]
  apply continuous_finsetSum
  intro i _
  exact (NNReal.continuous_coe.comp ((continuous_apply i).comp
    (continuous_subtype_val.comp continuous_snd))).mul
    (f.continuous.comp ((continuous_apply i).comp continuous_fst))

namespace FiniteLaw
variable {Ω : Type} [Fintype Ω]

noncomputable local instance finiteEncodingDecidableEq_rf13f56_2 (type : Type) :
    DecidableEq type := Classical.decEq type
noncomputable def nnWeights (P : FiniteLaw Ω) : AtomicWeights Ω :=
  ⟨fun i => ⟨P.weight i,P.nonneg i⟩, by
    apply NNReal.coe_injective
    exact (NNReal.coe_sum Finset.univ (fun i => (⟨P.weight i,P.nonneg i⟩ : ℝ≥0))).trans P.total⟩


noncomputable def asProbability {X : Type*} [MeasurableSpace X]
    (P : FiniteLaw Ω) (f : Ω → X) : ProbabilityMeasure X := atomicProbability f P.nnWeights

lemma measurable_asProbability {Z X : Type*} [MeasurableSpace Z]
    [TopologicalSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] [T1Space X]
    [MeasurableSpace (ProbabilityMeasure X)] [BorelSpace (ProbabilityMeasure X)]
    (P : Z → FiniteLaw Ω) (f : Z → Ω → X)
    (hP : ∀ a, Measurable (fun z => (P z).weight a))
    (hf : ∀ a, Measurable (fun z => f z a)) :
    Measurable (fun z => (P z).asProbability (f z)) := by
  have hw : Measurable (fun z => (P z).nnWeights) := by
    apply Measurable.subtype_mk
    exact Measurable.of_eval (fun a => (hP a).subtype_mk)
  exact continuous_atomicProbability_joint.measurable.comp
    ((Measurable.of_eval hf).prodMk hw)

end FiniteLaw

namespace KernelTower
variable {Ω : Type} [Fintype Ω]

noncomputable local instance finiteEncodingDecidableEq_rf13f56_3 (type : Type) :
    DecidableEq type := Classical.decEq type
local instance finiteEncodingMeasurableSpace_rf13f56_1 (space : TopCat) :
    MeasurableSpace space := borel space
noncomputable def encode : (r : ℕ) → KernelTower Ω (r+1) →
    (FinitePath Ω (r+1) → ℝ) → Hierarchy r
  | 0,T,V => Real.artanh (T.1.expect (fun a => V (a,())))
  | r+1,T,V => T.1.asProbability (fun a => encode r (T.2 a) (fun y => V (a,y)))

def TerminalInterior : (r : ℕ) → KernelTower Ω (r+1) →
    (FinitePath Ω (r+1) → ℝ) → Prop
  | 0,T,V => T.1.expect (fun a => V (a,())) ∈ Ioo (-1) 1
  | r+1,T,V => ∀ a, TerminalInterior r (T.2 a) (fun y => V (a,y))

end KernelTower
end DilutedSpinGlass

end

section
namespace DilutedSpinGlass.DepthAverage
open scoped BigOperators
noncomputable local instance finiteEncodingAverageDecidable (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition

end DilutedSpinGlass.DepthAverage
namespace DilutedSpinGlass.PrescribedTree
open ReducedTopology DepthAverage
open scoped BigOperators

noncomputable local instance finiteEncodingTreeDecidableEq_rf13f56_1 (type : Type) :
    DecidableEq type := Classical.decEq type
noncomputable local instance finiteEncodingTreeDecidable_rf13f56_1 (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
noncomputable def shapeBadConstant (S : ReducedTopology) : ℝ :=
  (Fintype.card S.Vertex:ℝ)+(Fintype.card S.Vertex:ℝ)^2

end DilutedSpinGlass.PrescribedTree

end

section
namespace DilutedSpinGlass
open _root_.MeasureTheory
open scoped BigOperators
local instance finiteEncodingReindexMeasurableSpace (space : TopCat) :
    MeasurableSpace space := borel space

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_MeasurableEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory Set
open scoped BigOperators BoundedContinuousFunction
local instance measurableEncodingMeasurableSpace (X : TopCat) : MeasurableSpace X := borel X
local instance measurableEncodingBorelSpace (X : TopCat) : BorelSpace X := ⟨rfl⟩

namespace KernelTower
variable {Ω Z : Type} [Fintype Ω] [MeasurableSpace Z]

lemma measurable_encode_tilt (r : ℕ) (T : KernelTower Ω (r+1)) (m : Fin (r+1) → ℝ)
    {f V : Z → FinitePath Ω (r+1) → ℝ}
    (hf : ∀ y, Measurable (fun z => f z y)) (hV : ∀ y, Measurable (fun z => V z y)) :
    Measurable (fun z => encode r (tilt (r+1) T m (f z)) (V z)) := by
  induction r with
  | zero =>
    change Measurable (fun z => Real.artanh
      ((T.1.tilt (m 0) (fun a => f z (a,()))).expect (fun a => V z (a,()))))
    have he := FiniteLaw.measurable_tilt_expect T.1 (m 0)
      (fun a => hf (a,())) (fun a => hV (a,()))
    exact ((measurable_const.add he).div (measurable_const.sub he)).sqrt.log
  | succ r ih =>
    let : MeasurableSpace (ProbabilityMeasure (Hierarchy r)) := borel _
    let : BorelSpace (ProbabilityMeasure (Hierarchy r)) := ⟨rfl⟩
    change Measurable (fun z =>
      (T.1.tilt (m 0) (fun a => backwardLog (r+1) (T.2 a) (fun j => m j.succ)
        (fun y => f z (a,y)))).asProbability
      (fun a => encode r (tilt (r+1) (T.2 a) (fun j => m j.succ) (fun y => f z (a,y)))
        (fun y => V z (a,y))))
    apply FiniteLaw.measurable_asProbability
    · intro a
      exact FiniteLaw.measurable_tilt_weight _ _ (fun b => measurable_backwardLog _ _ _
        (fun y => hf (b,y))) a
    · intro a
      exact ih (T.2 a) (fun j => m j.succ) (fun y => hf (a,y)) (fun y => hV (a,y))

end KernelTower
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_QSubtreePotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {n N : ℕ} {Ω : Type} [Fintype Ω]

noncomputable def subsetOverlap (T : PrescribedTree n) (A : Finset T.Leaf)
    (V : FinitePath Ω n → Fin N → ℝ) (w : Sample Ω T) : ℝ :=
  (∑ i, ∏ a∈A, V (T.pathAt a w) i)/(N:ℝ)

end DilutedSpinGlass.PrescribedTree

end

section
namespace DilutedSpinGlass.PrescribedTree
open ReducedTopology DepthAverage
open scoped BigOperators
noncomputable local instance qSubtreePotentialDecidableEq (carrier : Type) :
    DecidableEq carrier := Classical.decEq carrier
noncomputable local instance qSubtreePotentialPropDecidable (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition

noncomputable def subtreePotential {L : ℕ} (K : ℕ) (F : PrescribedTree L → ℝ) (T : PrescribedTree L) : ℝ :=
  ∑ S∈boundedTopologies K, ∑ q : S.Vertex → Fin L,
    if S.Admissible (fun v => q v) 0 L then
      if Nonempty (SplitMap (S.realize L 0 (fun v => q v)) T) then F (S.realize L 0 (fun v => q v)) else 0
    else 0

end DilutedSpinGlass.PrescribedTree

end

section
namespace DilutedSpinGlass
open _root_.MeasureTheory
open scoped BigOperators
local instance qSubtreePotentialMeasurableSpace (space : TopCat) : MeasurableSpace space := borel space

/-- A label block split at its first interaction occurrence. -/
def blockSuccEquiv (ι : Type) (k : ℕ) : ι ⊕ (Fin k × ι) ≃ Fin (k+1) × ι where
  toFun := Sum.elim (fun i => (0,i)) (fun z => (z.1.succ,z.2))
  invFun := fun z => Fin.cases (.inl z.2) (fun j => .inr (j,z.2)) z.1
  left_inv := by intro z; cases z <;> simp
  right_inv := by rintro ⟨j,i⟩; refine Fin.cases ?_ (fun j => ?_) j <;> simp

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_TopologyDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open scoped BigOperators
noncomputable local instance finiteMapDecEq (β : Type) : DecidableEq β := Classical.decEq β
namespace FiniteLaw
variable {Ω β : Type} [Fintype Ω] [Fintype β]
noncomputable def map (P : FiniteLaw Ω) (f : Ω → β) : FiniteLaw β where
  weight b := P.expect (fun a => if f a=b then 1 else 0)
  nonneg b := P.expect_nonneg (fun a => by split_ifs <;> norm_num)
  total := by
    classical
    rw [← expect_fintype_sum]
    simp

noncomputable def spinLog {ι : Type} [Fintype ι] (F : (ι → Spin) → ℝ) (x : ι → ℝ) : ℝ :=
  Real.log (∑ s : ι → Spin, (∏ i, q (x i) (s i))*Real.exp (F s))

end FiniteLaw
end DilutedSpinGlass

end

section
namespace DilutedSpinGlass.PrescribedTree
open ReducedTopology DepthAverage Filter Set
open scoped BigOperators Topology
noncomputable local instance topologyDecayDecidableEq (valueType : Type) :
    DecidableEq valueType := Classical.decEq valueType

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_PhysicalSubtreeConcentration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir
open ReducedTopology Filter Set
open scoped NNReal BigOperators Topology
variable {p L : ℕ}

noncomputable local instance physicalSubtreeConcentrationDecidableEq_rf13f56_1 (type : Type) :
    DecidableEq type := Classical.decEq type
noncomputable def physicalTreeVariance (M : Model p) (C H : ℝ) (N L : ℕ)
    (u : Spec L×ℕ → ℝ) (T : PrescribedTree (L+1)) : ℝ :=
  overlapVariance
    (fullRootLaw (fun _ : Fin N => M.field.toMeasure) (bondLaw M N)
      (markLaw (weights L) N) (M.alpha*N) (scoreRate N))
    (rootAlphabet (Ω := Fin N → Spin) (A := fun i : Labels L (Site N) => Alphabet i.1.1)) T
    (rootTower (KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L)
      (fun i => prior i.1.1) (gridExponents L) (physicalBase M C H N)
      (dictionaryFactor (observableAt direction N) (observableAt anchor N) u))
    (rootVector (readVector (fun v x => readSpin (KernelTower.terminalState L x) v)))

end DilutedSpinGlass.UniversalDictionary

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_RootOverlapDeviation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory
variable {Z : Type} [MeasurableSpace Z] {n N : ℕ}

noncomputable def overlapDeviation (μ : Measure Z) (Ω : Z → Type) [∀ z, Fintype (Ω z)]
    (S : PrescribedTree n) (K : (z : Z) → KernelTower (Ω z) n)
    (V : (z : Z) → FinitePath (Ω z) n → Fin N → ℝ) : ℝ :=
  FiniteLaw.mixedDeviation μ (fun z => Sample (Ω z) S)
    (fun z => S.sampleLaw (K z)) (fun z => treeOverlap S (V z))

noncomputable def subsetDeviation (μ : Measure Z) (Ω : Z → Type) [∀ z, Fintype (Ω z)]
    (S : PrescribedTree n) (A : Finset S.Leaf) (K : (z : Z) → KernelTower (Ω z) n)
    (V : (z : Z) → FinitePath (Ω z) n → Fin N → ℝ) : ℝ :=
  FiniteLaw.mixedDeviation μ (fun z => Sample (Ω z) S)
    (fun z => S.sampleLaw (K z)) (fun z => subsetOverlap S A (V z))

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_QSubsetDeviation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory ReducedTopology Filter
open scoped BigOperators Topology
noncomputable local instance qSubsetDeviationDecidableEq (carrier : Type) :
    DecidableEq carrier := Classical.decEq carrier
noncomputable local instance qSubsetDeviationDecidable (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
variable {Z : Type} [MeasurableSpace Z] {n N : ℕ}

noncomputable def shapeDeviation (μ : Measure Z) (Ω : Z → Type) [∀ z, Fintype (Ω z)]
    (S : PrescribedTree n) (K : (z : Z) → KernelTower (Ω z) n)
    (V : (z : Z) → FinitePath (Ω z) n → Fin N → ℝ) : ℝ :=
  ∑ A : Finset S.Leaf, if A.Nonempty then subsetDeviation μ Ω S A K V else 0

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_PhysicalShapeError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir
open ReducedTopology Filter Set
open scoped NNReal BigOperators Topology
variable {p L : ℕ}

noncomputable local instance physicalShapeErrorDecidableEq_rf13f56_1 (type : Type) :
    DecidableEq type := Classical.decEq type
noncomputable def physicalTreeDeviation (M : Model p) (C H : ℝ) (N L : ℕ)
    (u : Spec L×ℕ → ℝ) (T : PrescribedTree (L+1)) : ℝ :=
  overlapDeviation
    (fullRootLaw (fun _ : Fin N => M.field.toMeasure) (bondLaw M N)
      (markLaw (weights L) N) (M.alpha*N) (scoreRate N))
    (rootAlphabet (Ω := Fin N → Spin) (A := fun i : Labels L (Site N) => Alphabet i.1.1)) T
    (rootTower (KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L)
      (fun i => prior i.1.1) (gridExponents L) (physicalBase M C H N)
      (dictionaryFactor (observableAt direction N) (observableAt anchor N) u))
    (rootVector (readVector (fun v x => readSpin (KernelTower.terminalState L x) v)))

noncomputable def physicalShapeDeviation (M : Model p) (C H : ℝ) (N L : ℕ)
    (u : Spec L×ℕ → ℝ) (T : PrescribedTree (L+1)) : ℝ :=
  shapeDeviation
    (fullRootLaw (fun _ : Fin N => M.field.toMeasure) (bondLaw M N)
      (markLaw (weights L) N) (M.alpha*N) (scoreRate N))
    (rootAlphabet (Ω := Fin N → Spin) (A := fun i : Labels L (Site N) => Alphabet i.1.1)) T
    (rootTower (KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L)
      (fun i => prior i.1.1) (gridExponents L) (physicalBase M C H N)
      (dictionaryFactor (observableAt direction N) (observableAt anchor N) u))
    (rootVector (readVector (fun v x => readSpin (KernelTower.terminalState L x) v)))

end DilutedSpinGlass.UniversalDictionary

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_FiniteHierarchyDense
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory Filter Set TopologicalSpace
open scoped Topology NNReal ENNReal BigOperators

local instance finiteHierarchyDenseMeasurableSpace (space : TopCat) : MeasurableSpace space := borel space

/-- Genuine finitely branching laws at every level, not an altered trial class. -/
def FiniteHierarchy : (r : ℕ) → Hierarchy r → Prop
  | 0,_ => True
  | r+1,μ => ∃ (n : ℕ) (x : Fin n → Hierarchy r) (w : AtomicWeights (Fin n)),
      (∀ i,FiniteHierarchy r (x i)) ∧ μ = atomicProbability x w

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_FunctionalContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators NNReal
variable {p r : ℕ} (M : Model p) (m : Fin r → ℝ) (hm : ∀ i,0 < m i)

noncomputable def trialSiteField {k : ℕ} (ζ : Hierarchy (r+1)) (θ : Fin k → InteractionSample p) : ℝ :=
  ∫ h,trialLog r ζ m (siteLog θ h) ∂M.field.toMeasure
noncomputable def trialSiteDisorder (ζ : Hierarchy (r+1)) (k : ℕ) : ℝ :=
  ∫ θ,trialSiteField M m ζ θ ∂Measure.pi (fun _ : Fin k => M.disorder.toMeasure)

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_RootEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory
open scoped BigOperators
local instance rootEncodingMeasurableSpace (space : TopCat) : MeasurableSpace space := borel space

lemma measurable_packRoot_into {X I Y W : Type} [MeasurableSpace X] [MeasurableSpace I]
    [MeasurableSpace Y] [MeasurableSpace W] {M : ℕ}
    {F : RootPath Y M → (k : ℕ) → RootPath X k → (n : ℕ) → RootPath I n → W}
    (hF : ∀ k n, Measurable (fun z : (RootPath Y M × RootPath X k) × RootPath I n =>
      F z.1.1 k z.1.2 n z.2)) :
    Measurable (fun z : FullRootState Y X I M => F z.1 z.2.1.1 z.2.1.2 z.2.2.1 z.2.2.2) := by
  have hn (k : ℕ) : Measurable (fun z : (RootPath Y M × RootPath X k) × Sigma (RootPath I) =>
      F z.1.1 k z.1.2 z.2.1 z.2.2) := measurable_prodSigma
        (f := fun (z : RootPath Y M × RootPath X k) n y => F z.1 k z.2 n y) (hF k)
  have hk : Measurable (fun z : (RootPath Y M × Sigma (RootPath I)) × Sigma (RootPath X) =>
      F z.1.1 z.2.1 z.2.2 z.1.2.1 z.1.2.2) :=
    measurable_prodSigma (f := fun (z : RootPath Y M × Sigma (RootPath I)) k x =>
      F z.1 k x z.2.1 z.2.2) (fun k =>
        (hn k).comp ((measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd))
  exact hk.comp ((measurable_fst.prodMk measurable_snd.snd).prodMk measurable_snd.fst)

namespace HeterogeneousMarks
open ConcreteReservoir PrescribedTree KernelTower
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M N : ℕ}

variable (T : KernelTower Ω (L+1)) (Q : (i : I) → Fin (L+1) → FiniteLaw (A i))
    (m : Fin (L+1) → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω (L+1) → ℝ)
    (old : (i : I) → FinitePath Ω (L+1) → FinitePath (A i) (L+1) → ℝ)
    (V : FinitePath Ω (L+1) → Site N → ℝ)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))

noncomputable def rootEncoding (z : FullRootState Y X I M) (i : Site N) : Hierarchy L :=
  encode L (rootTower T Q m base old z) (fun y => rootVector V z y i)

include hb in
lemma measurable_rootEncoding (i : Site N) : Measurable (fun z => rootEncoding T Q m base old V z i) := by
  apply measurable_packRoot_into (F := fun h k x n y =>
    encode L (tilt (L+1) (tower (rootArray n y) (L+1) T Q) m
      (logWeight (base h k x) (rootArray n y) old))
      (fun w => V (physical (rootArray n y) (L+1) w) i))
  intro k n
  apply measurable_from_prod_countable_left
  intro y
  dsimp only
  exact measurable_encode_tilt L (tower (rootArray n y) (L+1) T Q) m
    (fun w => (hb k _).add measurable_const) (fun _ => measurable_const)

include hb in
lemma measurable_rootEncoding_joint : Measurable (fun z : FullRootState Y X I M × Site N =>
    rootEncoding T Q m base old V z.1 z.2) := by
  apply measurable_from_prod_countable_left
  exact measurable_rootEncoding T Q m base old V hb

noncomputable def rootEncodingLaw (μ : Measure (FullRootState Y X I M)) [IsProbabilityMeasure μ] :
    Hierarchy (L+1) :=
  ⟨Measure.map
    (fun z : FullRootState Y X I M × Site N => rootEncoding T Q m base old V z.1 z.2)
    (μ.prod (siteLaw N)),
    (Measure.isProbabilityMeasure_map_iff
      (measurable_rootEncoding_joint T Q m base old V hb).aemeasurable).mpr inferInstance⟩

end HeterogeneousMarks
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ProductTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory Set
open scoped BigOperators
local instance productTowerMeasurableSpace (space : TopCat) :
    MeasurableSpace space := borel space
namespace FinitePath
variable {ι : Type} {α : ι → Type}
def proj : (n : ℕ) → FinitePath ((i : ι) → α i) n → (i : ι) → FinitePath (α i) n
  | 0,_,_ => ()
  | n+1,y,i => (y.1 i,proj n y.2 i)
end FinitePath
namespace KernelTower
variable {ι : Type} [Fintype ι] [DecidableEq ι] {α : ι → Type} [∀ i, Fintype (α i)]
noncomputable def pi : (n : ℕ) → ((i : ι) → KernelTower (α i) n) →
    KernelTower ((i : ι) → α i) n
  | 0,_ => ()
  | n+1,T => (FiniteLaw.pi (fun i => (T i).1), fun x => pi n (fun i => (T i).2 (x i)))


end KernelTower
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_MixedPatterns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory PrescribedTree KernelTower ConcreteReservoir
open scoped BigOperators
local instance rootInsertionMeasurableSpace (space : TopCat) : MeasurableSpace space := borel space
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M N : ℕ}
variable (T : KernelTower Ω (L+1)) (Q : (i : I) → Fin (L+1) → FiniteLaw (A i))
    (m : Fin (L+1) → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω (L+1) → ℝ)
    (old : (i : I) → FinitePath Ω (L+1) → FinitePath (A i) (L+1) → ℝ)
    (V : FinitePath Ω (L+1) → Site N → Spin)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))

noncomputable def rootInsertion (a : ℕ) (F : (Fin a → Spin) → ℝ)
    (z : FullRootState Y X I M × (Fin a → Site N)) : ℝ :=
  backwardLog (L+1) (rootTower T Q m base old z.1) m
    (fun y => F (fun i => V (physical (rootArray z.1.2.2.1 z.1.2.2.2) (L+1) y) (z.2 i)))

noncomputable def independentInsertion (a : ℕ) (F : (Fin a → Spin) → ℝ)
    (z : Fin a → FullRootState Y X I M × Site N) : ℝ :=
  backwardLog (L+1) (KernelTower.pi (L+1) (fun i => rootTower T Q m base old (z i).1)) m
    (fun y => F (fun i => V
      (physical (rootArray (z i).1.2.2.1 (z i).1.2.2.2) (L+1) (FinitePath.proj (L+1) y i)) (z i).2))

end DilutedSpinGlass.HeterogeneousMarks

end

section
namespace DilutedSpinGlass.Pattern
open _root_.MeasureTheory
open scoped BigOperators
noncomputable local instance mixedPatternsDecidableEq_rf13f56_1 (type : Type) :
    DecidableEq type := Classical.decEq type
variable {Z : Type} [MeasurableSpace Z] (μ : Measure Z) [IsProbabilityMeasure μ]
    (Ω : Z → Type) [∀ z, Fintype (Ω z)] (P : (z : Z) → FiniteLaw (Ω z))
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (mass : (z : Z) → Ω z → (ι → Bool) → ℝ)
    (hmass : ∀ z w e, 0 ≤ mass z w e) (htotal : ∀ z w, ∑ e, mass z w e=1)
    (hmean : ∀ e, Measurable (fun z => (P z).expect (fun w => mass z w e)))

noncomputable def mixedMass (e : ι → Bool) : ℝ := ∫ z, (P z).expect (fun w => mass z w e) ∂μ

end DilutedSpinGlass.Pattern

end

section
namespace DilutedSpinGlass
open KernelTower _root_.MeasureTheory
local instance exponentsExistMeasurableSpace (space : TopCat) : MeasurableSpace space := borel space

noncomputable def zeroHierarchy : (r : ℕ) → Hierarchy r
  | 0 => (show Hierarchy 0 from (0 : ℝ))
  | r+1 => (show ProbabilityMeasure (Hierarchy r) from
      ⟨Measure.dirac (zeroHierarchy r),Measure.dirac.isProbabilityMeasure⟩)

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_BranchingEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω : Type} [Fintype Ω]

noncomputable def branchingMean : {n : ℕ} → (S : PrescribedTree n) →
    KernelTower Ω n → (S.Leaf → FinitePath Ω n → ℝ) → ℝ
  | 0,.leaf,_,F => F () ()
  | _+1,.node _ C,T,F => ∏ j, T.1.expect (fun a =>
      branchingMean (C j) (T.2 a) (fun b y => F ⟨j,b⟩ (a,y)))

def branchingProduct : {n : ℕ} → (S : PrescribedTree n) →
    (S.Leaf → FinitePath Ω n → ℝ) → Sample Ω S → ℝ
  | 0,.leaf,F,_ => F () ()
  | _+1,.node _ C,F,z => ∏ j, branchingProduct (C j)
      (fun b y => F ⟨j,b⟩ ((z j).1,y)) (z j).2

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ProductPatterns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open scoped BigOperators

namespace PrescribedTree
variable {Ω : Type} [Fintype Ω]
noncomputable def patternMass {n : ℕ} (S : PrescribedTree n) (T : KernelTower Ω n)
    (V : FinitePath Ω n → Spin) (e : S.Leaf → Spin) : ℝ :=
  (sampleLaw S T).expect (fun z => if (fun a => V (pathAt S a z))=e then 1 else 0)

end PrescribedTree
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_RootPatternComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory PrescribedTree Pattern
open scoped BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M N : ℕ}
noncomputable local instance rootPatternComparisonDecidableEq_rf13f56_1 (carrier : Type) :
    DecidableEq carrier := Classical.decEq carrier
variable (μ : Measure (FullRootState Y X I M)) [IsProbabilityMeasure μ]
    (S : PrescribedTree L) (T : KernelTower Ω L)
    (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (old : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (V : FinitePath Ω L → Fin N → Spin)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))

noncomputable def rootPatternMass (e : S.Leaf → Spin) : ℝ :=
  ∫ z, rootTreeMean S T Q m base old (fun x => empirical (fun i a => V (x a) i) e) z ∂μ

end DilutedSpinGlass.HeterogeneousMarks

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ReservoirRate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open Filter _root_.MeasureTheory
open scoped NNReal Topology

/-- The old-site Poisson intensity, written so that its deficit from αN is
manifestly nonnegative. The exponent is p-1. -/
noncomputable def reservoirRate (α : ℝ≥0) (q N : ℕ) : ℝ≥0 :=
  α*N*((N:ℝ≥0)/(N+1))^q

noncomputable def reservoirDistance (α : ℝ≥0) (q N : ℕ) : ℝ :=
  ((α*N-reservoirRate α q N:ℝ≥0):ℝ)/Real.sqrt (reservoirRate α q N)

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_FiniteTowerPi
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir
open ReducedTopology Filter Set
open scoped NNReal BigOperators Topology
variable {p L : ℕ}

noncomputable def reservoirShapeDeviation (M : Model p) (C H : ℝ) (N L : ℕ)
    (u : Spec L×ℕ → ℝ) (S : PrescribedTree (L+1)) : ℝ :=
  shapeDeviation
    (fullRootLaw (fun _ : Fin N => M.field.toMeasure) (bondLaw M N)
      (markLaw (weights L) N) (reservoirRate M.alpha (p-1) N) (scoreRate N))
    (rootAlphabet (Ω := Fin N → Spin) (A := fun i : Labels L (Site N) => Alphabet i.1.1)) S
    (rootTower (KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L)
      (fun i => prior i.1.1) (gridExponents L) (physicalBase M C H N)
      (dictionaryFactor (observableAt direction N) (observableAt anchor N) u))
    (rootVector (readVector (fun v x => readSpin (KernelTower.terminalState L x) v)))

end DilutedSpinGlass.UniversalDictionary

end

section
namespace DilutedSpinGlass.KernelTower
open scoped BigOperators
variable {ι Ω : Type} [Fintype ι] [DecidableEq ι] [Fintype Ω]

noncomputable def piTower : (n : ℕ) → (ι → KernelTower Ω n) → KernelTower (ι → Ω) n
  | 0,_ => ()
  | n+1,T => (FiniteLaw.pi (fun i => (T i).1),fun x => piTower n (fun i => (T i).2 (x i)))

end DilutedSpinGlass.KernelTower

namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {ι Ω : Type}

def sampleMap (f : Ω → ι) : {n : ℕ} → (S : PrescribedTree n) → Sample Ω S → Sample ι S
  | 0,.leaf,_ => ()
  | _+1,.node _ C,x => fun i => (f (x i).1,sampleMap f (C i) (x i).2)

@[simp] lemma pathAt_sampleMap (f : Ω → ι) {n : ℕ} (S : PrescribedTree n)
    (a : S.Leaf) (x : Sample Ω S) :
    S.pathAt a (sampleMap f S x)=KernelTower.pathMap f n (S.pathAt a x) := by
  induction S with
  | leaf => rfl
  | node k C ih => exact congrArg (Prod.mk _) (ih a.1 a.2 (x a.1).2)

def samplePi : {n : ℕ} → (S : PrescribedTree n) → (ι → Sample Ω S) → Sample (ι → Ω) S
  | 0,.leaf,_ => ()
  | _+1,.node _ C,x => fun j => (fun i => (x i j).1,samplePi (C j) (fun i => (x i j).2))

@[simp] lemma sampleMap_pi {n : ℕ} (S : PrescribedTree n) (x : ι → Sample Ω S) (i : ι) :
    sampleMap (fun y : ι → Ω => y i) S (samplePi S x)=x i := by
  induction S with
  | leaf => change () = x i; exact Subsingleton.elim _ _
  | node k C ih =>
    funext j
    change ((x i j).1,sampleMap (fun y : ι → Ω => y i) (C j) (samplePi (C j) (fun i => (x i j).2)))=x i j
    rw [ih]

@[simp] lemma samplePi_eval {n : ℕ} (S : PrescribedTree n) (x : Sample (ι → Ω) S) :
    samplePi S (fun i => sampleMap (fun y : ι → Ω => y i) S x)=x := by
  induction S with
  | leaf => change () = x; exact Subsingleton.elim _ _
  | node k C ih =>
    funext j
    change ((fun i => (x j).1 i),samplePi (C j) (fun i => sampleMap (fun y : ι → Ω => y i) (C j) (x j).2))=x j
    rw [ih]

def samplePiEquiv {n : ℕ} (S : PrescribedTree n) : Sample (ι → Ω) S ≃ (ι → Sample Ω S) where
  toFun x i := sampleMap (fun y : ι → Ω => y i) S x
  invFun := samplePi S
  left_inv := samplePi_eval S
  right_inv x := funext (sampleMap_pi S x)

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_RealEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable def mapModel {p : ℕ} (M : Model p) (T : InteractionSample p → InteractionSample p)
    (g : ℝ → ℝ) (hT : Measurable T) (hg : Measurable g) : Model p where
  alpha := M.alpha
  disorder := ⟨Measure.map T M.disorder.toMeasure,
    (Measure.isProbabilityMeasure_map_iff hT.aemeasurable).mpr inferInstance⟩
  field := ⟨Measure.map g M.field.toMeasure,
    (Measure.isProbabilityMeasure_map_iff hg.aemeasurable).mpr inferInstance⟩

end DilutedSpinGlass

end

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators
local instance hierarchyTranslationMeasurableSpace (space : TopCat) : MeasurableSpace space := borel space
end DilutedSpinGlass

end

section
namespace DilutedSpinGlass
open _root_.MeasureTheory Set TopologicalSpace
open scoped BigOperators NNReal
local instance realEncodingMeasurableSpace (space : TopCat) : MeasurableSpace space := borel space

namespace KernelTower
variable {Ω Λ : Type} [Fintype Ω] [Fintype Λ]

/-- Literal messages at leaves, with no spin terminal transition. -/
noncomputable def realEncode : (r : ℕ) → KernelTower Ω r →
    (FinitePath Ω r → ℝ) → Hierarchy r
  | 0,_,V => V ()
  | r+1,T,V => T.1.asProbability (fun a => realEncode r (T.2 a) (fun y => V (a,y)))

/-- Pad a finite conditional law along an injection with a specified retraction.
Off-support children are harmless but are specified, rather than postulated. -/
noncomputable def embed (f : Ω → Λ) (g : Λ → Ω) : (r : ℕ) →
    KernelTower Ω r → KernelTower Λ r
  | 0,_ => ()
  | r+1,T => (T.1.map f, fun a => embed f g r (T.2 (g a)))

end KernelTower

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_FunctionalStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory PrescribedTree KernelTower ConcreteReservoir
open scoped BigOperators
local instance functionalStabilityRootMeasurableSpace (space : TopCat) :
    MeasurableSpace space := borel space
end DilutedSpinGlass.HeterogeneousMarks

end

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
variable {p r : ℕ} (M : Model p) (m : Fin r → ℝ) (hm : ∀ d,0 < m d) (ζ : Hierarchy (r+1))

noncomputable def trialDisorderAt (k : ℕ) (h : ℝ) : ℝ :=
  ∫ z : Fin k → InteractionSample p,trialLog r ζ m (siteLog z h)
    ∂Measure.pi (fun _ : Fin k => M.disorder.toMeasure)

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_RootPatternProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory PrescribedTree Pattern ConcreteReservoir
open scoped BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M N : ℕ}
variable (μ : Measure (FullRootState Y X I M)) [IsProbabilityMeasure μ]
    (S : PrescribedTree L) (T : KernelTower Ω L)
    (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (old : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (V : FinitePath Ω L → Site N → Spin)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))

noncomputable def rootSitePattern (e : S.Leaf → Spin)
    (z : FullRootState Y X I M × Site N) : ℝ :=
  rootTreeMean S T Q m base old (fun y => if (fun a => V (y a) z.2)=e then 1 else 0) z.1

end DilutedSpinGlass.HeterogeneousMarks

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_RootCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory PrescribedTree Pattern ConcreteReservoir
open scoped BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M N : ℕ}
variable (μ : Measure (FullRootState Y X I M)) [IsProbabilityMeasure μ]
    (S : PrescribedTree L) (T : KernelTower Ω L)
    (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (old : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (V : FinitePath Ω L → Site N → Spin)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))

noncomputable def sameTreeCoefficient (a : ℕ) (f : (Fin a → Spin) → ℝ)
    (z : FullRootState Y X I M) : ℝ :=
  (FiniteLaw.uniform : FiniteLaw (Fin a → Site N)).expect (fun i =>
    treeMean S (rootTower T Q m base old z)
      (fun y => f (fun j => V (physical (rootArray z.2.2.1 z.2.2.2) L y) (i j))))

noncomputable def independentTreeCoefficient (a : ℕ) (f : (Fin a → Spin) → ℝ)
    (z : Fin a → FullRootState Y X I M × Site N) : ℝ :=
  treeMean S (KernelTower.pi L (fun i => rootTower T Q m base old (z i).1))
    (fun y => f (fun i => V (physical (rootArray (z i).1.2.2.1 (z i).1.2.2.2) L
      (FinitePath.proj L y i)) (z i).2))

end DilutedSpinGlass.HeterogeneousMarks

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_SameInsertionAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory PrescribedTree KernelTower ConcreteReservoir
open scoped BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M N : ℕ}
variable (T : KernelTower Ω (L+1)) (Q : (i : I) → Fin (L+1) → FiniteLaw (A i))
    (m : Fin (L+1) → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω (L+1) → ℝ)
    (old : (i : I) → FinitePath Ω (L+1) → FinitePath (A i) (L+1) → ℝ)
    (V : FinitePath Ω (L+1) → Site N → Spin)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))

noncomputable def sameInsertionAverage (a : ℕ) (F : (Fin a → Spin) → ℝ)
    (z : FullRootState Y X I M) : ℝ :=
  (FiniteLaw.uniform : FiniteLaw (Fin a → Site N)).expect (fun i => rootInsertion T Q m base old V a F (z,i))

end DilutedSpinGlass.HeterogeneousMarks

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_PhysicalInsertionComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir KernelTower
open scoped NNReal BigOperators Topology
variable {p : ℕ}

noncomputable def reservoirLaw (M : Model p) (N L : ℕ) :=
  fullRootLaw (fun _ : Fin N => M.field.toMeasure) (bondLaw M N)
    (markLaw (weights L) N) (reservoirRate M.alpha (p-1) N) (scoreRate N)
instance reservoirLaw_prob (M : Model p) (N L : ℕ) : IsProbabilityMeasure (reservoirLaw M N L) := by
  unfold reservoirLaw
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)

def physicalSpin (N L : ℕ) (y : FinitePath (Fin N → Spin) (L+1)) (i : Site N) : Spin :=
  readSpin (KernelTower.terminalState L y) i

noncomputable def reservoirTrialLaw (M : Model p) (C H : ℝ) (N L : ℕ)
    (u : Spec L×ℕ → ℝ) : Hierarchy (L+1) :=
  rootEncodingLaw
    (KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L)
    (fun i : Labels L (Site N) => prior i.1.1) (gridExponents L) (physicalBase M C H N)
    (dictionaryFactor (observableAt direction N) (observableAt anchor N) u)
    (fun y i => spin (physicalSpin N L y i)) (measurable_physicalBase M C H N) (reservoirLaw M N L)

noncomputable def reservoirInsertion (M : Model p) (C H : ℝ) (N L : ℕ)
    (u : Spec L×ℕ → ℝ) (a : ℕ) (F : (Fin a → Spin) → ℝ) : ℝ :=
  ∫ z, sameInsertionAverage
    (KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L)
    (fun i : Labels L (Site N) => prior i.1.1) (gridExponents L) (physicalBase M C H N)
    (dictionaryFactor (observableAt direction N) (observableAt anchor N) u)
    (physicalSpin N L) a F z ∂reservoirLaw M N L

end DilutedSpinGlass.UniversalDictionary

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_NormalizationSymmetry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable def centeredInteraction {p : ℕ} (z : InteractionSample p) : Interaction p :=
  fun s => z.1 s-z.1 (fun _ => true)

noncomputable def normalizedFactor {p : ℕ} (z : ℝ×(Fin p → Spin → ℝ)) : Interaction p :=
  fun s => Real.log (1+z.1*∏ l,z.2 l (s l))-Real.log (1+z.1*∏ l,z.2 l true)

lemma measurable_centeredInteraction (p : ℕ) : Measurable (centeredInteraction (p := p)) := by
  unfold centeredInteraction
  fun_prop
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_NormalizedCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators

noncomputable def centerSample {p : ℕ} (z : InteractionSample p) : InteractionSample p :=
  (centeredInteraction z,z.2)
lemma measurable_centerSample (p : ℕ) : Measurable (centerSample (p := p)) :=
  (measurable_centeredInteraction p).prodMk measurable_snd

noncomputable def centeredModel {p : ℕ} (M : Model p) : Model p :=
  mapModel M centerSample id (measurable_centerSample p) measurable_id

noncomputable def clippedModel {p : ℕ} (M : Model p) (K : ℝ) : Model p :=
  mapModel M (clipSample K) (clipReal K) (measurable_clipSample K) (measurable_clipReal K)

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_CompoundPhysicalMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PhysicalRoot
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks KernelTower
open scoped NNReal ENNReal BigOperators
variable {X Y I : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I]
    {A : I → Type} [∀ i,Fintype (A i)] {N L : ℕ}

noncomputable def energyRoot (Q : (i : I) → Fin (L+1) → FiniteLaw (A i))
    (m : Fin (L+1) → ℝ) (field : Y → ℝ)
    (factor : (i : I) → FinitePath (Fin N → Spin) (L+1) → FinitePath (A i) (L+1) → ℝ)
    (h : RootPath Y N) (a : Sigma (RootPath I)) (E : (Fin N → Spin) → ℝ) : ℝ :=
  root (terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L) Q m
    (fun y => E (terminalState L y)+∑ i,field (rootArray N h i)*spin (terminalState L y i))
    (rootArray a.1 a.2) factor

noncomputable def rootSample (V : X → (Fin N → Spin) → ℝ) (field : Y → ℝ)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (factor : (i : I) → FinitePath (Fin N → Spin) (L+1) → FinitePath (A i) (L+1) → ℝ)
    (h : RootPath Y N) (k : ℕ) (x : RootPath X k) (n : ℕ) (a : RootPath I n) : ℝ :=
  root (terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L) Q m
    (fun y => energy V field h k x (terminalState L y)) (rootArray n a) factor

end DilutedSpinGlass.PhysicalRoot

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_UpperMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- Coordinatewise zero cutoff, retaining iid f and independence from b. -/
noncomputable def factorCut (R : ℝ) (f : Spin → ℝ) : Spin → ℝ :=
  if ‖f‖≤R then f else 0

noncomputable def patternFeature {n : ℕ} (R : ℝ) (P : FiniteLaw (Fin n → Spin))
    (f : Spin → ℝ) : ℝ := P.expect (fun s => ∏ a,factorCut R f (s a))

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_FinitePoissonSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators

noncomputable def finiteUniform (A : Type*) [Fintype A] [Nonempty A]
    [MeasurableSpace A] : Measure A := (PMF.uniformOfFintype A).toMeasure
instance finiteUniform_prob (A : Type*) [Fintype A] [Nonempty A] [MeasurableSpace A] :
    IsProbabilityMeasure (finiteUniform A) := by unfold finiteUniform; infer_instance

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_CavitySplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators

noncomputable def oneNewRate (α : ℝ≥0) (q N : ℕ) : ℝ≥0 :=
  α*(q+1)*((N:ℝ≥0)/(N+1))^q

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_CavityRateLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open Filter
open scoped Topology NNReal BigOperators

noncomputable def cavityBadRate (α : ℝ≥0) (q N : ℕ) : ℝ :=
  (α:ℝ)*(N+1)-(reservoirRate α q N:ℝ)-(oneNewRate α q N:ℝ)

end DilutedSpinGlass

end

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory

/-- Move the singled-out interaction coordinate to the distinguished last slot,
 preserving the relative order of all other slots. -/
def cavityCoordinateEquiv {q : ℕ} (j : Fin (q+1)) : Equiv.Perm (Fin (q+1)) where
  toFun := j.insertNth (Fin.last q) (fun i => i.castSucc)
  invFun := Fin.lastCases j (fun i => j.succAbove i)
  left_inv x := by
    refine Fin.succAboveCases j ?_ (fun i => ?_) x
    · simp only [Fin.insertNth_apply_same,Fin.lastCases_last]
    · simp only [Fin.insertNth_apply_succAbove,Fin.lastCases_castSucc]
  right_inv x := by
    refine Fin.lastCases ?_ (fun i => ?_) x
    · simp only [Fin.lastCases_last,Fin.insertNth_apply_same]
    · simp only [Fin.lastCases_castSucc,Fin.insertNth_apply_succAbove]

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_SpinMarginal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace DilutedSpinGlass.HeterogeneousMarks
open KernelTower
open scoped BigOperators
variable {Ω Λ I : Type} [Fintype Ω] [Fintype Λ] {A : I → Type} [∀ i,Fintype (A i)]
    {k L N : ℕ}

noncomputable def terminalRoot (a : Ω) (P : FiniteLaw Ω)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (E : Ω → ℝ) (roots : Fin k → I)
    (ψ : (i : I) → Ω → FinitePath (A i) (L+1) → ℝ) : ℝ :=
  root (terminalTower a P L) Q m (fun y => E (terminalState L y)) roots
    (fun i y z => ψ i (terminalState L y) z)

end DilutedSpinGlass.HeterogeneousMarks

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_MarkSiteCoupling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PhysicalRoot
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks KernelTower
open scoped BigOperators NNReal
variable {X Y I : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    {A : I → Type} [∀ i,Fintype (A i)] {N p L : ℕ}

noncomputable def indexedPotential (theta : X → InteractionSample p)
    (z : X × (Fin p → Fin N)) (σ : Fin N → Spin) : ℝ :=
  (theta z.1).1 (fun j => σ (z.2 j))

noncomputable def locatedFactor
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    (i : I × Fin N) (y : FinitePath (Fin N → Spin) (L+1))
    (a : FinitePath (A i.1) (L+1)) : ℝ := ψ i.1 (terminalState L y i.2) a

end DilutedSpinGlass.PhysicalRoot

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ClippedModelFacts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable def replicaInsertionMoment {p n : ℕ} (M : Model p) (R : ℝ)
    (P : Fin p → FiniteLaw (Fin n → Spin)) : ℝ :=
  ∫ z : InteractionSample p, (-z.2.2.1)^n*(FiniteLaw.pi P).expect
    (fun s => ∏ a : Fin n,∏ l : Fin p,factorCut R (z.2.2.2 l) (s l a)) ∂M.disorder.toMeasure

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_PoissonCountThinning
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

noncomputable def rawReplicaMoment {p n : ℕ} (M : Model p)
    (P : Fin p → FiniteLaw (Fin n → Spin)) : ℝ :=
  ∫ z : InteractionSample p, (FiniteLaw.pi P).expect
    (fun s => ∏ a : Fin n,(-z.2.2.1)*∏ l : Fin p,z.2.2.2 l (s l a)) ∂M.disorder.toMeasure

end DilutedSpinGlass

end

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators

noncomputable def successCount {p k : ℕ} [NeZero p] (a : Fin k → Fin p) : ℕ :=
  ∑ i,if a i=0 then 1 else 0

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_UpperReplicaPatterns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable def qLaw (x : ℝ) : FiniteLaw Spin where
  weight := q x
  nonneg s := (q_pos x s).le
  total := q_sum x

noncomputable def averagedFactor (f : Spin → ℝ) (x : ℝ) : ℝ :=
  ∑ s : Spin,q x s*f s

/-- The finite law of spin patterns induced by one fresh message label on
all replica leaves. The message label, including its root, is shared across
leaves; only the final spin draws are conditionally independent. -/
noncomputable def freshPatternLaw {Z : Type} [Fintype Z] {n : ℕ}
    (Q : FiniteLaw Z) (x : Z → Fin n → ℝ) : FiniteLaw (Fin n → Spin) :=
  (Q.bind (fun z => FiniteLaw.pi (fun a : Fin n => qLaw (x z a)))).map Prod.snd

/-- Empirical pattern law of the old spin array at independently drawn sites. -/
noncomputable def oldPatternLaw {N n : ℕ} [NeZero N]
    (s : Fin N → Fin n → Spin) : FiniteLaw (Fin n → Spin) :=
  (FiniteLaw.uniform : FiniteLaw (Fin N)).map s

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_InsertionCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- The actual independent index/fresh-label sampling for a fixed old replica
array. A fresh label is one whole tree sample, not a new draw at each leaf. -/
noncomputable def insertionCoefficient {Z : Type} [Fintype Z] {p n N : ℕ} [NeZero N]
    (M : Model p) (old : Fin N → Fin n → Spin) (Q : FiniteLaw Z)
    (x : Z → Fin n → ℝ) (sel : Fin p → Bool) : ℝ :=
  ∫ z : InteractionSample p,
    (FiniteLaw.pi (fun _ : Fin p => (FiniteLaw.uniform : FiniteLaw (Fin N)).bind (fun _ => Q))).expect
      (fun w => ∏ a : Fin n, -(z.2.2.1 * ∏ l : Fin p,
        if sel l then z.2.2.2 l (old (w l).1 a)
        else averagedFactor (z.2.2.2 l) (x (w l).2 a))) ∂M.disorder.toMeasure

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_InsertionPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory
open scoped BigOperators

noncomputable def mixedFactor {p : ℕ} (z : InteractionSample p) (sel : Fin p → Bool)
    (s : Fin p → Spin) (x : Fin p → ℝ) : ℝ :=
  z.2.2.1 * ∏ l : Fin p,if sel l then z.2.2.2 l (s l) else averagedFactor (z.2.2.2 l) (x l)

noncomputable def insertionPoint {Z : Type} [Fintype Z] {p n N : ℕ} [NeZero N]
    (z : InteractionSample p) (old : Fin N → Fin n → Spin) (Q : FiniteLaw Z)
    (x : Z → Fin n → ℝ) (sel : Fin p → Bool) : ℝ :=
  (FiniteLaw.pi (fun _ : Fin p => (FiniteLaw.uniform : FiniteLaw (Fin N)).bind (fun _ => Q))).expect
    (fun w => ∏ a : Fin n,-mixedFactor z sel (fun l => old (w l).1 a) (fun l => x (w l).2 a))

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_CountArrayBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PhysicalRoot
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks KernelTower SizeCoupling
open scoped BigOperators NNReal
variable {X Y I : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    {A : I → Type} [∀ i,Fintype (A i)] {N p L k l : ℕ}

noncomputable def arrayRoot (theta : X → InteractionSample p) (field : Y → ℝ)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    (a : Fin l → I) (x : Fin k → X) (h : RootPath Y N)
    (j : Fin k → Fin p → Fin N) (w : Fin l → Fin N) : ℝ :=
  spinRoot (fun t => Q (a t)) m (fun t => theta (x t))
    (fun t => field (rootArray N h t)) j w (fun t => ψ (a t))

end DilutedSpinGlass.PhysicalRoot

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_CavityInsertionAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open scoped BigOperators
open _root_.MeasureTheory

noncomputable def cavitySiteEnergy {p k : ℕ} (θ : Fin k → InteractionSample p) (h : ℝ)
    (s : Fin k × Fin (p-1) → Spin) : ℝ :=
  Real.log ((∑ ε : Spin, Real.exp (h*spin ε+∑ j,(θ j).1 (appendSpin (fun l => s (j,l)) ε)))/2)

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_AveragedEnergyRoot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory Filter
open scoped BigOperators Topology

namespace UniversalDictionary
open ConcreteReservoir

noncomputable def reservoirInsertionOn {ι : Type} [Fintype ι] {p : ℕ}
    (M : Model p) (C H : ℝ) (N L : ℕ) (u : Spec L×ℕ → ℝ) (F : (ι → Spin) → ℝ) : ℝ :=
  reservoirInsertion M C H N L u (Fintype.card ι)
    (fun s => F (fun i => s (Fintype.equivFin ι i)))

end UniversalDictionary
end DilutedSpinGlass

end

section
namespace DilutedSpinGlass.PhysicalRoot
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks KernelTower
open scoped BigOperators NNReal
variable {Y I : Type} [MeasurableSpace Y] [Countable I] [MeasurableSpace I]
    [MeasurableSingletonClass I] {A : I → Type} [∀ i,Fintype (A i)] {N L : ℕ}

noncomputable def averagedEnergyRoot (ξ : Measure Y) (ν : Measure I) (s : ℝ≥0)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ) (field : Y → ℝ)
    (factor : (i : I) → FinitePath (Fin N → Spin) (L+1) → FinitePath (A i) (L+1) → ℝ)
    (E : (Fin N → Spin) → ℝ) : ℝ :=
  ∫ h,∫ a,energyRoot Q m field factor h a E ∂compoundRootLaw ν s ∂rootLaw N (fun _ => ξ)

end DilutedSpinGlass.PhysicalRoot

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_CavityTrialIdentity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

noncomputable def cavityBondEnergy {p k : ℕ} (θ : Fin k → InteractionSample p)
    (s : Fin k × Fin p → Spin) : ℝ := ∑ j,(θ j).1 (fun i => s (j,i))

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_TowerPadding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.KernelTower
variable {Ω Λ : Type} [Fintype Ω] [Fintype Λ]

noncomputable def pad (a : Ω) : (n : ℕ) → KernelTower Ω n → KernelTower Ω (n+1)
  | 0,_ => (FiniteLaw.point a,fun _ => ())
  | n+1,T => (T.1,fun x => pad a n (T.2 x))

def pathPrefix : (n : ℕ) → FinitePath Ω (n+1) → FinitePath Ω n
  | 0,_ => ()
  | n+1,x => (x.1,pathPrefix n x.2)

end DilutedSpinGlass.KernelTower

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_CommonTreeSample
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω Λ R ι : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
    [Fintype ι] [DecidableEq ι] {n : ℕ}

noncomputable def mixedTreeD {p N : ℕ} (z : InteractionSample p) (sel : Fin p → Bool)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (r : Fin p → R) (i : Fin p → Fin N) (w : FinitePath (Ω × (Fin p → Λ)) n) : ℝ :=
  mixedFactor z sel (fun l => V (KernelTower.pathFst n w) (i l))
    (fun l => x (r l) (KernelTower.pathMap (fun a : Fin p → Λ => a l) n (KernelTower.pathSnd n w)))

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_UpperCommonCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory
open scoped BigOperators
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
    {n p N : ℕ} [NeZero N]

noncomputable def mixedLeafAvg (S : PrescribedTree n) (T : KernelTower Ω n)
    (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (z : InteractionSample p) (sel : Fin p → Bool) : ℝ :=
  (FiniteLaw.pi (fun _ : Fin p => (FiniteLaw.uniform : FiniteLaw (Fin N)))).expect (fun i =>
    (FiniteLaw.pi (fun _ : Fin p => Q)).expect (fun r =>
      (S.sampleLaw (KernelTower.prod n T (KernelTower.piTower n (fun j : Fin p => U (r j))))).expect
        (leafProduct S (fun y => -mixedTreeD z sel V x r i y))))

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_UpperRegularized
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory Filter
open scoped BigOperators Topology
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
    {n p N : ℕ} [NeZero N]

noncomputable def mixedLogAvg (T : KernelTower Ω n)
    (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin (n+1) → ℝ) (z : InteractionSample p) (sel : Fin p → Bool) (t : ℝ) : ℝ :=
  (FiniteLaw.pi (fun _ : Fin p => (FiniteLaw.uniform : FiniteLaw (Fin N)))).expect (fun i =>
    (FiniteLaw.pi (fun _ : Fin p => Q)).expect (fun r =>
      logInsertion (KernelTower.prod n T (KernelTower.piTower n (fun j : Fin p => U (r j))))
        m (mixedTreeD z sel V x r i) t))

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_MixedEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory Filter
open scoped BigOperators Topology

noncomputable def mixedSpinLaw {p : ℕ} (sel : Fin p → Bool) (s : Fin p → Spin) (x : Fin p → ℝ) :
    FiniteLaw (Fin p → Spin) :=
  FiniteLaw.pi (fun l => if sel l then FiniteLaw.point (s l) else qLaw (x l))

noncomputable def mixedEnergy {p : ℕ} (z : InteractionSample p)
    (sel : Fin p → Bool) (s : Fin p → Spin) (x : Fin p → ℝ) : ℝ :=
  (mixedSpinLaw sel s x).logMean 1 z.1

namespace PrescribedTree
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
    {n p N : ℕ} [NeZero N]

noncomputable def mixedTreeEnergy (z : InteractionSample p) (sel : Fin p → Bool)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (r : Fin p → R) (i : Fin p → Fin N) (w : FinitePath (Ω × (Fin p → Λ)) n) : ℝ :=
  mixedEnergy z sel (fun l => V (KernelTower.pathFst n w) (i l))
    (fun l => x (r l) (KernelTower.pathMap (fun a : Fin p → Λ => a l) n (KernelTower.pathSnd n w)))

noncomputable def mixedEnergyAvg (T : KernelTower Ω n)
    (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin (n+1) → ℝ) (z : InteractionSample p) (sel : Fin p → Bool) : ℝ :=
  (FiniteLaw.pi (fun _ : Fin p => (FiniteLaw.uniform : FiniteLaw (Fin N)))).expect (fun i =>
    (FiniteLaw.pi (fun _ : Fin p => Q)).expect (fun r =>
      KernelTower.backwardLog n (KernelTower.prod n T (KernelTower.piTower n (fun j : Fin p => U (r j))))
        (fun j => m j.succ) (mixedTreeEnergy z sel V x r i)))

end PrescribedTree
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_UpperInsertion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory Filter
open scoped BigOperators Topology
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
    {n p N : ℕ} [NeZero N]

noncomputable def referenceD (z : InteractionSample p) : ℝ :=
  z.2.2.1*∏ l,z.2.2.2 l false

noncomputable def mixedNormalizedAvg (T : KernelTower Ω n)
    (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin (n+1) → ℝ) (z : InteractionSample p) (sel : Fin p → Bool) (t : ℝ) : ℝ :=
  mixedLogAvg T Q U V x m z sel t-Real.log (1+t*referenceD z)

noncomputable def regularization (k : ℕ) : ℝ := 1-1/(k+1)

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_InsertionPoissonAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace UniversalDictionary
open ConcreteReservoir

noncomputable def insertionPoisson {ι X : ℕ → Type} [∀ k,Fintype (ι k)] [∀ k,MeasurableSpace (X k)]
    {p : ℕ} (M : Model p) (C H : ℝ) (N L : ℕ) (u : Spec L×ℕ → ℝ)
    (μ : (k : ℕ) → Measure (X k)) (F : (k : ℕ) → X k → (ι k → Spin) → ℝ) (ρ : ℝ≥0) : ℝ :=
  ∫ k, ∫ x,reservoirInsertionOn M C H N L u (F k x) ∂μ k ∂poissonMeasure ρ

noncomputable def trialPoisson {ι X : ℕ → Type} [∀ k,Fintype (ι k)] [∀ k,MeasurableSpace (X k)]
    (L : ℕ) (ζ : Hierarchy (L+1)) (μ : (k : ℕ) → Measure (X k))
    (F : (k : ℕ) → X k → (ι k → Spin) → ℝ) (ρ : ℝ≥0) : ℝ :=
  ∫ k, ∫ x,trialLog L ζ (fun i => gridExponents L i.castSucc) (FiniteLaw.spinLog (F k x)) ∂μ k ∂poissonMeasure ρ

end UniversalDictionary
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_MarkMeanProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory KernelTower PhysicalRoot
open scoped BigOperators NNReal
variable {I : Type} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I]
    {A : I → Type} [∀ i,Fintype (A i)] {N J k L : ℕ}

noncomputable def locatedTerminalRoot
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    (site : Fin J → Fin N) (E : (Fin N → Spin) → ℝ)
    (a : RootPath (I×Fin J) k) : ℝ :=
  terminalRoot (fun _ : Fin N => false) FiniteLaw.uniform (fun i : I×Fin J => Q i.1)
    m E (rootArray k a) (fun i σ b => ψ i.1 (σ (site i.2)) b)

noncomputable def terminalMean [NeZero J]
    (ν : Measure I) (s : ℝ≥0)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    (site : Fin J → Fin N) (E : (Fin N → Spin) → ℝ) : ℝ :=
  ∫ a : Sigma (RootPath (I×Fin J)),locatedTerminalRoot Q m ψ site E a.2
    ∂compoundRootLaw (ν.prod (finiteUniform (Fin J))) s

end DilutedSpinGlass.HeterogeneousMarks

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_TowerArraySplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.KernelTower
variable {Ω Λ : Type} [Fintype Ω] [Fintype Λ]

def splitFirst (l : ℕ) (z : Ω × (Fin (l+1) → Λ)) : (Ω × (Fin l → Λ)) × Λ :=
  ((z.1,fun i => z.2 i.succ),z.2 0)

end DilutedSpinGlass.KernelTower

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_UpperRootInsertion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
    {n p N : ℕ} [NeZero N]

/-- The actual root energy difference on appending a fresh independent block,
with the ordinary physical energy held fixed. -/
noncomputable def mixedRootIncrement (T : KernelTower Ω n)
    (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin (n+1) → ℝ) (f : FinitePath Ω n → ℝ)
    (z : InteractionSample p) (sel : Fin p → Bool) : ℝ :=
  (FiniteLaw.pi (fun _ : Fin p => (FiniteLaw.uniform : FiniteLaw (Fin N)))).expect (fun i =>
    (FiniteLaw.pi (fun _ : Fin p => Q)).expect (fun r =>
      KernelTower.backwardLog n (KernelTower.prod n T (KernelTower.piTower n (fun j : Fin p => U (r j))))
        (fun j => m j.succ) (fun w => f (KernelTower.pathFst n w)+mixedTreeEnergy z sel V x r i w)-
      KernelTower.backwardLog n T (fun j => m j.succ) f))

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_CavityProxy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal BigOperators

namespace UniversalDictionary
open ConcreteReservoir

noncomputable def cavityProxy {p : ℕ} (M : Model p) (C H : ℝ)
    (N L : ℕ) (u : Spec L×ℕ → ℝ) : ℝ := Real.log 2+
  insertionPoisson M C H N L u
    (fun k => (Measure.pi (fun _ : Fin k => M.disorder.toMeasure)).prod M.field.toMeasure)
    (fun _ z => cavitySiteEnergy z.1 z.2) (M.alpha*p)-
  insertionPoisson M C H N L u
    (fun k => Measure.pi (fun _ : Fin k => M.disorder.toMeasure))
    (fun _ θ => cavityBondEnergy θ) (M.alpha*(p-1:ℕ))

end UniversalDictionary
end DilutedSpinGlass

end

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped NNReal BigOperators

noncomputable def functionalEnvelope {p : ℕ} (M : Model p) : ℝ :=
  fieldMoment M+((M.alpha:ℝ)*p+(M.alpha:ℝ)*(p-1:ℕ))*interactionMoment M

end DilutedSpinGlass

end

section
namespace DilutedSpinGlass
open _root_.MeasureTheory
open scoped BigOperators

namespace PrescribedTree
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
    {n p N : ℕ} [NeZero N]

noncomputable def edgeRoot (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (x : R → FinitePath Λ n → ℝ) (m : Fin n → ℝ) (z : InteractionSample p) : ℝ :=
  (FiniteLaw.pi (fun _ : Fin p => Q)).expect (fun r =>
    KernelTower.backwardLog n (KernelTower.piTower n (fun j : Fin p => U (r j))) m
      (fun y => Real.log (edge z.1 (fun j => x (r j)
        (KernelTower.pathMap (fun a : Fin p → Λ => a j) n y)))))

end PrescribedTree
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_CenteredPressure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

noncomputable def referenceEnergy {p : ℕ} (z : InteractionSample p) : ℝ := z.1 (fun _ => true)
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_UpperTrial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory
open scoped BigOperators
local instance upperTrialMeasurableSpace (space : TopCat) : MeasurableSpace space := borel space

namespace PrescribedTree
variable {Λ R : Type} [Fintype Λ] [Fintype R]
noncomputable def finiteTrialLaw (r : ℕ) (Q : FiniteLaw R) (U : R → KernelTower Λ r)
    (x : R → FinitePath Λ r → ℝ) : Hierarchy (r+1) :=
  Q.asProbability (fun a => KernelTower.realEncode r (U a) (x a))

end PrescribedTree
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_TerminalMeanField
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory KernelTower PhysicalRoot
open scoped BigOperators NNReal
variable {I Y : Type} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I]
    [MeasurableSpace Y] {A : I → Type} [∀ i,Fintype (A i)] {N J k p L : ℕ}

noncomputable def fieldEnergy (field : Y → ℝ) (h : RootPath Y N) (σ : Fin N → Spin) : ℝ :=
  ∑ i,field (rootArray N h i)*spin (σ i)

end DilutedSpinGlass.HeterogeneousMarks

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_UpperCountState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory KernelTower
open scoped BigOperators

/-- Each cavity interaction has its own independent p-tuple of trial trees. -/
def CavityState (Ω Λ : Type) (p : ℕ) : ℕ → Type
  | 0 => Ω
  | l+1 => CavityState Ω Λ p l × (Fin p → Λ)

instance cavityStateFintype (Ω Λ : Type) [Fintype Ω] [Fintype Λ] (p : ℕ) :
    (l : ℕ) → Fintype (CavityState Ω Λ p l)
  | 0 => inferInstanceAs (Fintype Ω)
  | l+1 => by
    letI := cavityStateFintype Ω Λ p l
    exact inferInstanceAs (Fintype (CavityState Ω Λ p l × (Fin p → Λ)))

def cavityProject {Ω Λ : Type} {p : ℕ} : (l : ℕ) → CavityState Ω Λ p l → Ω
  | 0,σ => σ
  | l+1,σ => cavityProject l σ.1

variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R] {n p N : ℕ} [NeZero N]

noncomputable def cavityTower (T : KernelTower Ω n) (U : R → KernelTower Λ n) :
    (l : ℕ) → RootPath (Fin p → R) l → KernelTower (CavityState Ω Λ p l) n
  | 0,_ => T
  | l+1,r => KernelTower.prod n (cavityTower T U l r.2) (piTower n (fun j => U (r.1 j)))

noncomputable def cavityEnergy (V : FinitePath Ω n → Fin N → Spin)
    (x : R → FinitePath Λ n → ℝ) (j : Fin p) :
    (l : ℕ) → RootPath (Fin p → R) l → RootPath (Fin p → Fin N) l →
      RootPath (InteractionSample p) l → (FinitePath Ω n → ℝ) →
        FinitePath (CavityState Ω Λ p l) n → ℝ
  | 0,_,_,_,f,y => f y
  | l+1,r,i,z,f,y => cavityEnergy V x j l r.2 i.2 z.2 f (pathFst n y)+
      mixedTreeEnergy z.1 (fun a => decide (a=j))
        (fun y => V (pathMap (cavityProject l) n y)) x r.1 i.1 y

noncomputable def cavityRoot (T : KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (j : Fin p) (l : ℕ)
    (r : RootPath (Fin p → R) l) (i : RootPath (Fin p → Fin N) l)
    (z : RootPath (InteractionSample p) l) (f : FinitePath Ω n → ℝ) : ℝ :=
  backwardLog n (cavityTower T U l r) m (cavityEnergy V x j l r i z f)

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_CavityAllocation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open KernelTower
variable {ι Ω Λ R : Type} [Fintype ι] [DecidableEq ι]
    [Fintype Ω] [Fintype Λ] [Fintype R] {n p : ℕ}

/-- Duplicate every block at every site before selecting its actual allocation.
The unused duplicates disappear by prior-law projection, not by independence
of tilted physical sites. -/
def cavityJoin : (l : ℕ) → RootPath ι l →
    (ι → CavityState Ω Λ p l) → CavityState (ι → Ω) Λ p l
  | 0,_,z => z
  | l+1,c,z => (cavityJoin l c.2 (fun i => (z i).1),(z c.1).2)

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_UpperDatum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory
open scoped BigOperators

def rootMap {X Y : Type} (f : X → Y) : (k : ℕ) → RootPath X k → RootPath Y k
  | 0,_ => ()
  | k+1,z => (f z.1,rootMap f k z.2)

namespace PrescribedTree
variable {Ω Λ R X : Type} [Fintype Ω] [Fintype Λ] [Fintype R] [MeasurableSpace X]
    {n p N : ℕ} [NeZero N]

abbrev UpperDatum (p N : ℕ) (R : Type) := InteractionSample p × (Fin p → Fin N) × (Fin p → R)

noncomputable def upperDatumLaw [MeasurableSpace R] (M : Model p) (Q : FiniteLaw R) :
    Measure (UpperDatum p N R) :=
  M.disorder.toMeasure.prod
    (((FiniteLaw.pi (fun _ : Fin p => (FiniteLaw.uniform : FiniteLaw (Fin N)))).asProbability id).toMeasure.prod
      ((FiniteLaw.pi (fun _ : Fin p => Q)).asProbability id).toMeasure)

end PrescribedTree
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_CavitySeparable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
variable {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] {N k p : ℕ} [NeZero N]

noncomputable def cavityArrayEnergy (theta : X → InteractionSample p) (field : Y → ℝ)
    (E : (Fin N → Spin) → ℝ) (j : Fin k → Fin (p-1) → Fin N)
    (z : (Fin k → X) × Y) : (Fin N → Spin) → ℝ :=
  fun σ => E σ+cavitySiteEnergy (fun a => theta (z.1 a)) (field z.2) (fun a => σ (j a.1 a.2))

noncomputable def cavityArrayValue (ξ : Measure Y) (theta : X → InteractionSample p)
    (field : Y → ℝ) (F : ((Fin N → Spin) → ℝ) → ℝ) (E : (Fin N → Spin) → ℝ)
    (z : Fin k → X) : ℝ :=
  (FiniteLaw.uniform : FiniteLaw (Fin k → Fin (p-1) → Fin N)).expect
    (fun j => ∫ h,F (cavityArrayEnergy theta field E j (z,h)) ∂ξ)

end DilutedSpinGlass

end

section
namespace DilutedSpinGlass.PrescribedTree
open KernelTower
open scoped BigOperators
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R] {n p N : ℕ} [NeZero N]

noncomputable def singleBlockEnergy (V : FinitePath Ω n → Spin)
    (x : R → FinitePath Λ n → ℝ) (j : Fin p) (l : ℕ)
    (r : Fin p → R) (z : InteractionSample p)
    (y : FinitePath (CavityState Ω Λ p (l+1)) n) : ℝ :=
  mixedEnergy z (fun a => decide (a=j))
    (fun _ => V (pathMap (cavityProject l) n (pathFst n y)))
    (fun a => x (r a) (pathMap (fun b : Fin p → Λ => b a) n (pathSnd n y)))

noncomputable def allocatedEnergy (V : FinitePath Ω n → Spin)
    (x : R → FinitePath Λ n → ℝ) (j : Fin p) (s : Fin N) :
    (l : ℕ) → RootPath (Fin p → R) l → RootPath (Fin N) l →
      RootPath (InteractionSample p) l → (FinitePath Ω n → ℝ) →
        FinitePath (CavityState Ω Λ p l) n → ℝ
  | 0,_,_,_,f,y => f y
  | l+1,r,c,z,f,y => allocatedEnergy V x j s l r.2 c.2 z.2 f (pathFst n y)+
      if c.1=s then singleBlockEnergy V x j l r.1 z.1 y else 0

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_EnergyInsertionMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory

def selectedCount : (l : ℕ) → RootPath Bool l → ℕ
  | 0,_ => 0
  | l+1,(true,b) => selectedCount l b+1
  | l+1,(false,b) => selectedCount l b

def selectRoot {X : Type} : (l : ℕ) → (b : RootPath Bool l) → RootPath X l → RootPath X (selectedCount l b)
  | 0,_,z => z
  | l+1,(true,b),z => (z.1,selectRoot l b z.2)
  | l+1,(false,b),z => selectRoot l b z.2

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_OneNewLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory PhysicalRoot
variable {X : Type} [MeasurableSpace X] {q N : ℕ} [NeZero N]

noncomputable def newPotential (theta : X → InteractionSample (q+1))
    (z : X×(Fin q → Fin N)) : (Fin (N+1) → Spin) → ℝ :=
  fun σ => (theta z.1).1 (appendSpin (fun b => σ (z.2 b).succ) (σ 0))

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_FullRootIncrement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
variable {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
    {N p k : ℕ} [NeZero N]

noncomputable def cavityPoissonValue (μ : Measure X) (ξ : Measure Y)
    (theta : X → InteractionSample p) (field : Y → ℝ)
    (F : ((Fin N → Spin) → ℝ) → ℝ) (r : ℝ≥0) (E : (Fin N → Spin) → ℝ) : ℝ :=
  ∫ k,∫ z : Fin k → X,cavityArrayValue ξ theta field F E z
    ∂Measure.pi (fun _ : Fin k => μ) ∂poissonMeasure r

end DilutedSpinGlass

end

section

namespace DilutedSpinGlass.PrescribedTree
open KernelTower
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R] {n p : ℕ}

def selectCavity : (l : ℕ) → (b : RootPath Bool l) → CavityState Ω Λ p l →
    CavityState Ω Λ p (selectedCount l b)
  | 0,_,z => z
  | l+1,(true,b),z => (selectCavity l b z.1,z.2)
  | l+1,(false,b),z => selectCavity l b z.1

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_CavityMaskEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open KernelTower
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R] {n p N : ℕ} [NeZero N]

noncomputable def activeEnergy (V : FinitePath Ω n → Spin)
    (x : R → FinitePath Λ n → ℝ) (j : Fin p) :
    (l : ℕ) → RootPath (Fin p → R) l → RootPath (InteractionSample p) l →
      (FinitePath Ω n → ℝ) → FinitePath (CavityState Ω Λ p l) n → ℝ
  | 0,_,_,f,y => f y
  | l+1,r,z,f,y => activeEnergy V x j l r.2 z.2 f (pathFst n y)+
      singleBlockEnergy V x j l r.1 z.1 y

noncomputable def maskedEnergy (V : FinitePath Ω n → Spin)
    (x : R → FinitePath Λ n → ℝ) (j : Fin p) :
    (l : ℕ) → RootPath Bool l → RootPath (Fin p → R) l → RootPath (InteractionSample p) l →
      (FinitePath Ω n → ℝ) → FinitePath (CavityState Ω Λ p l) n → ℝ
  | 0,_,_,_,f,y => f y
  | l+1,(b,bs),r,z,f,y => maskedEnergy V x j l bs r.2 z.2 f (pathFst n y)+
      if b then singleBlockEnergy V x j l r.1 z.1 y else 0

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_CavityPack
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open KernelTower
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R] {n p : ℕ}

def cavityPack : (l : ℕ) → Ω × (Fin l → Fin p → Λ) → CavityState Ω Λ p l
  | 0,z => z.1
  | l+1,z => (cavityPack l (z.1,fun i => z.2 i.succ),z.2 0)

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_OldEnergyEmbedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory PhysicalRoot
open scoped NNReal
variable {X : Type} [MeasurableSpace X] {q N : ℕ} [NeZero N]

noncomputable def liftOldEnergy : (((Fin N → Spin) → ℝ) →L[ℝ] ((Fin (N+1) → Spin) → ℝ)) where
  toFun E σ := E (fun i => σ i.succ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := by fun_prop

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_UpperCountMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory KernelTower
open scoped BigOperators
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
    [MeasurableSpace R] [MeasurableSingletonClass R] {n p N : ℕ} [NeZero N]

instance upperDatumLaw_probability (M : Model p) (Q : FiniteLaw R) :
    IsProbabilityMeasure (upperDatumLaw (N := N) M Q) := by
  unfold upperDatumLaw
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)

noncomputable def realCountEnergy (V : FinitePath Ω n → Fin N → Spin) (k : ℕ)
    (i : RootPath (Fin p → Fin N) k) (z : RootPath (InteractionSample p) k)
    (f : FinitePath Ω n → ℝ) (y : FinitePath Ω n) : ℝ :=
  f y+∑ a,(rootArray k z a).1 (fun j => V y (rootArray k i a j))

noncomputable def datumRoot (T : KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (j : Fin p) (f : FinitePath Ω n → ℝ) (k l : ℕ)
    (z : RootPath (UpperDatum p N R) k) (w : RootPath (UpperDatum p N R) l) : ℝ :=
  cavityRoot T U V x m j l (rootMap (fun a => a.2.2) l w) (rootMap (fun a => a.2.1) l w)
    (rootMap Prod.fst l w)
    (realCountEnergy V k (rootMap (fun a => a.2.1) k z) (rootMap Prod.fst k z) f)

noncomputable def upperCountMean (M : Model p) (T : KernelTower Ω n) (Q : FiniteLaw R)
    (U : R → KernelTower Λ n) (V : FinitePath Ω n → Fin N → Spin)
    (x : R → FinitePath Λ n → ℝ) (m : Fin n → ℝ) (j : Fin p)
    (f : FinitePath Ω n → ℝ) (k l : ℕ) : ℝ :=
  ∫ z,∫ w,datumRoot T U V x m j f k l z w ∂rootLaw l (fun _ => upperDatumLaw M Q)
    ∂rootLaw k (fun _ => upperDatumLaw M Q)

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_UpperFreshLocal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory KernelTower
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
    [MeasurableSpace R] [MeasurableSingletonClass R] {n p N : ℕ} [NeZero N]

noncomputable def freshRoot (T : KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (f : FinitePath Ω n → ℝ) (sel : Fin p → Bool)
    (a : UpperDatum p N R) : ℝ :=
  backwardLog n (KernelTower.prod n T (piTower n (fun d => U (a.2.2 d)))) m
    (fun y => f (pathFst n y)+mixedTreeEnergy a.1 sel V x a.2.2 a.2.1 y)

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_PhysicalReservoirIncrement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.SizeCoupling
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot KernelTower
open scoped NNReal BigOperators
variable {X Y I : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I]
    {A : I → Type} [∀ i,Fintype (A i)] {N q L : ℕ} [NeZero N]

noncomputable def energyCavityIncrement
    (μ : Measure X) (ξ : Measure Y) (ν : Measure I) (α s : ℝ≥0)
    (theta : X → InteractionSample (q+1)) (field : Y → ℝ)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ) : ℝ :=
  let F := averagedEnergyRoot ξ (ν.prod (finiteUniform (Fin N))) s
    (fun i : I×Fin N => Q i.1) m field (locatedFactor ψ)
  let μo := Measure.map (indexedPotential (N := N) theta)
    (μ.prod (finiteUniform (Fin (q+1) → Fin N)))
  Real.log 2+
    (∫ E,cavityPoissonValue μ ξ theta field F (oneNewRate α q N) E-F E
      ∂compoundPoisson (reservoirRate α q N) μo)-
    (∫ E,∫ v,F (E+v)-F E ∂compoundPoisson (α*N-reservoirRate α q N) μo
      ∂compoundPoisson (reservoirRate α q N) μo)

end DilutedSpinGlass.SizeCoupling

end

section
namespace DilutedSpinGlass
open _root_.MeasureTheory

namespace PrescribedTree
open KernelTower
open scoped BigOperators
variable {Ω Λ R X : Type} [Fintype Ω] [Fintype Λ] [Fintype R] [MeasurableSpace X]
    {n p N : ℕ} [NeZero N]

noncomputable def activeDatumRoot (T : KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (j : Fin p) (f : FinitePath Ω n → ℝ) (l : ℕ)
    (z : RootPath (InteractionSample p × (Fin p → R)) l) : ℝ :=
  backwardLog n (cavityTower T U l (rootMap Prod.snd l z)) m
    (activeEnergy V x j l (rootMap Prod.snd l z) (rootMap Prod.fst l z) f)

end PrescribedTree
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_CavityDatumProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory
namespace PrescribedTree
open _root_.MeasureTheory KernelTower
open scoped BigOperators
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
    [MeasurableSpace R] [MeasurableSingletonClass R] {n p N : ℕ} [NeZero N]

noncomputable def allocatedDatumRoot (T : KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (j : Fin p) (s : Fin N) (f : FinitePath Ω n → ℝ) (l : ℕ)
    (c : RootPath (Fin N) l) (z : RootPath (InteractionSample p × (Fin p → R)) l) : ℝ :=
  backwardLog n (cavityTower T U l (rootMap Prod.snd l z)) m
    (allocatedEnergy V x j s l (rootMap Prod.snd l z) c (rootMap Prod.fst l z) f)

end PrescribedTree
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ReservoirSiteTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir KernelTower
open scoped NNReal BigOperators
variable {p N L : ℕ} [NeZero N]

noncomputable def variableSiteInsertion (M : Model p) (C H : ℝ)
    (u : Spec L×ℕ → ℝ) (b : ℕ) (F : (Fin b → Spin) → ℝ) (d : ℕ) [NeZero d] : ℝ :=
  let rd := fun (σ : Fin N → Spin) (i : Fin d) => if h : i.val<N then σ ⟨i.val,h⟩ else false
  let ψ := fun (i : (Spec L×ℕ)×Fin d) (y : FinitePath (Fin N → Spin) (L+1))
    (a : FinitePath (Alphabet i.1.1) (L+1)) => spinFactor direction anchor u i.1 (rd (terminalState L y) i.2) a
  (FiniteLaw.uniform : FiniteLaw (Fin b → Fin d)).expect (fun i =>
    ∫ E,averagedEnergyRoot M.field.toMeasure ((weights L).prod (finiteUniform (Fin d))) (scoreRate N)
        (fun i : (Spec L×ℕ)×Fin d => prior i.1.1) (gridExponents L) (clipReal H) ψ
        (E+(fun σ => F (fun j => rd σ (i j))))-
      averagedEnergyRoot M.field.toMeasure ((weights L).prod (finiteUniform (Fin d))) (scoreRate N)
        (fun i : (Spec L×ℕ)×Fin d => prior i.1.1) (gridExponents L) (clipReal H) ψ E
      ∂compoundPoisson (reservoirRate M.alpha (p-1) N)
        (Measure.map (fun z : InteractionSample p × (Fin p → Fin d) =>
          fun σ => clipReal C (z.1.1 (fun j => rd σ (z.2 j))))
          (M.disorder.toMeasure.prod (finiteUniform (Fin p → Fin d)))))

end DilutedSpinGlass.UniversalDictionary

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ReservoirInsertionOnEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir KernelTower
open scoped NNReal BigOperators
variable {p N L : ℕ} [NeZero N]

noncomputable def reservoirEnergyRoot (M : Model p) (H : ℝ) (N L : ℕ) [NeZero N]
    (u : Spec L×ℕ → ℝ) : ((Fin N → Spin) → ℝ) → ℝ :=
  averagedEnergyRoot M.field.toMeasure ((weights L).prod (finiteUniform (Fin N))) (scoreRate N)
    (fun i : (Spec L×ℕ)×Fin N => prior i.1.1) (gridExponents L) (clipReal H)
    (locatedFactor (spinFactor direction anchor u))

noncomputable def reservoirEnergyLaw (M : Model p) (C : ℝ) (N : ℕ) [NeZero N] :
    Measure ((Fin N → Spin) → ℝ) :=
  compoundPoisson (reservoirRate M.alpha (p-1) N)
    (Measure.map (fun z : InteractionSample p × (Fin p → Fin N) =>
      fun σ => clipReal C (z.1.1 (fun j => σ (z.2 j))))
      (M.disorder.toMeasure.prod (finiteUniform (Fin p → Fin N))))

end DilutedSpinGlass.UniversalDictionary

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_CavityAllocatedMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]

noncomputable def energyInsertionFunctional (ρ : Measure E) (F : E → ℝ) (v : E) : ℝ :=
  ∫ E,F (E+v)-F E ∂ρ

end DilutedSpinGlass

end

section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory KernelTower
open scoped BigOperators
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
    [MeasurableSpace R] [MeasurableSingletonClass R] {n p N : ℕ} [NeZero N]

noncomputable def activeCountMean (M : Model p) (Q : FiniteLaw R)
    (T : KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (j : Fin p) (f : FinitePath Ω n → ℝ) (l : ℕ) : ℝ :=
  ∫ z,activeDatumRoot T U V x m j f l z ∂rootLaw l (fun _ =>
    M.disorder.toMeasure.prod ((FiniteLaw.pi (fun _ : Fin p => Q)).asProbability id).toMeasure)

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_PoissonSiteThinning
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators

noncomputable def successCountAt {p k : ℕ} [NeZero p] (s : Fin p) (a : Fin k → Fin p) : ℕ :=
  ∑ i,if a i=s then 1 else 0

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ClippedCavityProxy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir KernelTower SizeCoupling
open scoped NNReal BigOperators
variable {p N L : ℕ}

noncomputable def clippedSiteInsertion (M : Model p) (C H : ℝ) (N L : ℕ)
    (u : Spec L×ℕ → ℝ) (r : ℝ≥0) : ℝ :=
  insertionPoisson M C H N L u
    (fun k => (Measure.pi (fun _ : Fin k => M.disorder.toMeasure)).prod M.field.toMeasure)
    (fun _ z => cavitySiteEnergy (fun j => clipSample C (z.1 j)) (clipReal H z.2)) r
noncomputable def clippedBondInsertion (M : Model p) (C H : ℝ) (N L : ℕ)
    (u : Spec L×ℕ → ℝ) (r : ℝ≥0) : ℝ :=
  insertionPoisson M C H N L u
    (fun k => Measure.pi (fun _ : Fin k => M.disorder.toMeasure))
    (fun _ θ => cavityBondEnergy (fun j => clipSample C (θ j))) r
noncomputable def clippedCavityProxy (M : Model p) (C H : ℝ) (N L : ℕ)
    (u : Spec L×ℕ → ℝ) : ℝ := Real.log 2+
  clippedSiteInsertion M C H N L u (M.alpha*p)-
  clippedBondInsertion M C H N L u (M.alpha*(p-1:ℕ))

end DilutedSpinGlass.UniversalDictionary

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_PhysicalFieldOrder
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
variable {p N : ℕ} [NeZero N]

noncomputable def centeredDisorderAt (M : Model p) (k : ℕ) (h : Fin N → ℝ) : ℝ :=
  ∫ z : Fin k → InteractionSample p,indexAverage z h-(N:ℝ)*Real.log 2
    ∂Measure.pi (fun _ : Fin k => M.disorder.toMeasure)

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_GridIncrementSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir KernelTower SizeCoupling
open scoped NNReal BigOperators

noncomputable def clippedPhysicalMean {q L : ℕ} (M : Model (q+1)) (C H : ℝ)
    (N : ℕ) [NeZero N] (s : ℝ≥0) (u : Spec L×ℕ → ℝ) : ℝ :=
  perturbedMean (N := N) M.disorder.toMeasure M.field.toMeasure (weights L) (clipSample C) (clipReal H)
    (fun i : Spec L×ℕ => prior i.1) (gridExponents L) (spinFactor direction anchor u) (M.alpha*N) s

noncomputable def clippedReservoirIncrement {q L : ℕ} (M : Model (q+1)) (C H : ℝ)
    (N : ℕ) [NeZero N] (u : Spec L×ℕ → ℝ) : ℝ :=
  energyCavityIncrement (N := N) M.disorder.toMeasure M.field.toMeasure (weights L) M.alpha (scoreRate N)
    (clipSample C) (clipReal H) (fun i : Spec L×ℕ => prior i.1) (gridExponents L)
    (spinFactor direction anchor u)

end DilutedSpinGlass.UniversalDictionary

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_IncrementCavityProxy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir KernelTower SizeCoupling
open scoped NNReal BigOperators

noncomputable def cavityIncrementError (α : ℝ≥0) (q : ℕ) (C : ℝ) (N : ℕ) : ℝ :=
  C*cavityBadRate α q N+6*scoreScale N/(N+1)+
  C*|(oneNewRate α q N:ℝ)-(α:ℝ)*(q+1)|+
  C*|(α:ℝ)*N-(reservoirRate α q N:ℝ)-(α:ℝ)*q|+
  (scoreScale (N+1)-scoreScale N)

end DilutedSpinGlass.UniversalDictionary

end

end OAI
end


