-- Prove2me | Definitions.Def_OAIQ093D005
-- name    : OAIQ093D005
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-02T17:56:32.064344+00:00
-- url     : https://prove2.me/theorems/5767f3f5-77ee-402f-b07d-ef8da5364a77
-- title:
--   Definitions bundle OAIQ093D005 of the split of OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 458 declarations of OpenAI's Lean: 246 definitions, 1 inductive type or structure, 27 instances and 184 theorems. The definitions and types are `OAI.PolycyclicRecognition.finiteIndexLift`, `OAI.PolycyclicRecognition.finiteIndexOrientationHomEquiv`, `OAI.PolycyclicRecognition.finiteIndexPowerHom`, `OAI.PolycyclicRecognition.finiteIndexReturn`, `OAI.PolycyclicRecognition.finiteLieBracket`, `OAI.PolycyclicRecognition.finiteLieSmoothNormedAddCommGroup`, `OAI.PolycyclicRecognition.finiteLieSmoothNormedSpace`, `OAI.PolycyclicRecognition.finiteOrbitEmbedding`, `OAI.PolycyclicRecognition.finiteOrbitIntegerLattice`, `OAI.PolycyclicRecognition.finiteOrbitIntegerRepresentation`, `OAI.PolycyclicRecognition.finiteRationalAverage`, `OAI.PolycyclicRecognition.finiteRationalCoinvariantsSection`, `OAI.PolycyclicRecognition.finiteTargetKernel`, `OAI.PolycyclicRecognition.finsuppHomPostcompEquiv`, `OAI.PolycyclicRecognition.finsuppRepresentationModuleEquiv`, `OAI.PolycyclicRecognition.flatSamplePairs`, `OAI.PolycyclicRecognition.flowDeriv`, `OAI.PolycyclicRecognition.flowLineBase`, `OAI.PolycyclicRecognition.flowLineSlope`, `OAI.PolycyclicRecognition.flowSegmentDomain`, `OAI.PolycyclicRecognition.flowSegmentPoint`, `OAI.PolycyclicRecognition.flowTimeSlice`, `OAI.PolycyclicRecognition.freeAveragedExtension`, `OAI.PolycyclicRecognition.freeAveragedLinearMap`, `OAI.PolycyclicRecognition.freeIdentityCoefficient`, `OAI.PolycyclicRecognition.generatorGroupWord`, `OAI.PolycyclicRecognition.generatorPair`, `OAI.PolycyclicRecognition.generatorPairParameters`, `OAI.PolycyclicRecognition.generatorSchemeNormedAddCommGroup`, `OAI.PolycyclicRecognition.generatorSchemeNormedSpace`, `OAI.PolycyclicRecognition.generatorSchemeWord`, `OAI.PolycyclicRecognition.generatorWordBase`, `OAI.PolycyclicRecognition.genericWeightDirections`, `OAI.PolycyclicRecognition.gradedGenerator`, `OAI.PolycyclicRecognition.gradedGeneratorLinearMap`, `OAI.PolycyclicRecognition.gradedGeneratorMap`, `OAI.PolycyclicRecognition.groupAverage`, `OAI.PolycyclicRecognition.groupAverageGood`, `OAI.PolycyclicRecognition.haarFiberSlice`, `OAI.PolycyclicRecognition.haarSectionMeasure` and 207 more.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory, in whole or in part: `PolycyclicRecognition_Algebra_AdmissibleGeneratorWords`, `PolycyclicRecognition_Algebra_AlternatingProductSubmersion`, `PolycyclicRecognition_Algebra_AscendingCoinvariantRelations`, `PolycyclicRecognition_Algebra_AutocorrelationRecurrence`, `PolycyclicRecognition_Algebra_BackwardRecurrenceStep`, `PolycyclicRecognition_Algebra_CenteredSourceTerminals`, `PolycyclicRecognition_Algebra_CharacteristicFiniteIndex`, `PolycyclicRecognition_Algebra_ClosedEmbeddingSplitKernel`, `PolycyclicRecognition_Algebra_CoordinateMinorPermutation`, `PolycyclicRecognition_Algebra_CyclicPowerIndex`, `PolycyclicRecognition_Algebra_EquivariantCommutatorFiltration`, `PolycyclicRecognition_Algebra_ExactTensorCoefficient`, `PolycyclicRecognition_Algebra_ExpandedSchemeAmplitudes`, `PolycyclicRecognition_Algebra_ExtensionSectionFactor`, `PolycyclicRecognition_Algebra_FiberAverageL2`, `PolycyclicRecognition_Algebra_FiniteFinsuppHom`, `PolycyclicRecognition_Algebra_FiniteGeneratedCharacterLog`, `PolycyclicRecognition_Algebra_FiniteGroupRelativeInjective`, `PolycyclicRecognition_Algebra_FiniteIndexTrace`, `PolycyclicRecognition_Algebra_FiniteInduction`, `PolycyclicRecognition_Algebra_FiniteInvariantOrbit`, `PolycyclicRecognition_Algebra_FiniteLinearSymmetries`, `PolycyclicRecognition_Algebra_FiniteRationalRepresentation`, `PolycyclicRecognition_Algebra_FiniteRestriction`, `PolycyclicRecognition_Algebra_FinsuppRepresentationModule`, `PolycyclicRecognition_Algebra_GeneratorConjugation`, `PolycyclicRecognition_Algebra_GeneratorSchemes`, `PolycyclicRecognition_Algebra_GradedGeneratorLimit`, `PolycyclicRecognition_Algebra_GradedHorizontalStructure`, `PolycyclicRecognition_Algebra_GroupAveragedRepresentative`, `PolycyclicRecognition_Algebra_GroupFiniteGenerationFromFP`, `PolycyclicRecognition_Algebra_HilbertOrbitAverage`, `PolycyclicRecognition_Algebra_InductionAmbientQuotient`, `PolycyclicRecognition_Algebra_InnerBarTranslation`, `PolycyclicRecognition_Algebra_IntegerInducedTranslation`, `PolycyclicRecognition_Algebra_IntegerQuotientCoordinates`, `PolycyclicRecognition_Algebra_IntegerRegularCoordinates`, `PolycyclicRecognition_Algebra_InvariantFactor`, `PolycyclicRecognition_Algebra_InvariantSubspaceDeterminant`, `PolycyclicRecognition_Algebra_JointDirectionLabels`, `PolycyclicRecognition_Algebra_LeftTangentTrivialization`, `PolycyclicRecognition_Algebra_LinearInvariantInverse`, `PolycyclicRecognition_Algebra_LocalVirtualSolvabilityBound`, `PolycyclicRecognition_Algebra_NatTotalComplexSymmetry`, `PolycyclicRecognition_Algebra_NilpotentProducts`, `PolycyclicRecognition_Algebra_NilpotentQuotientRank`, `PolycyclicRecognition_Algebra_NilpotentRationalConjugation`, `PolycyclicRecognition_Algebra_NilpotentSectionRemainder`, `PolycyclicRecognition_Algebra_NormalInductionTensor`, `PolycyclicRecognition_Algebra_ParametrizedGeneratorSchemes`, `PolycyclicRecognition_Algebra_Polycyclic`, `PolycyclicRecognition_Algebra_PolyhedralSymmetries`, `PolycyclicRecognition_Algebra_PolynomialCoordinateGroup`, `PolycyclicRecognition_Algebra_PolynomialMinor`, `PolycyclicRecognition_Algebra_PolynomialProductParameters`, `PolycyclicRecognition_Algebra_QuotientLinearAction`, `PolycyclicRecognition_Algebra_QuotientSectionCoordinates`, `PolycyclicRecognition_Algebra_RankOneCharacter`, `PolycyclicRecognition_Algebra_RankOneEndomorphisms`, `PolycyclicRecognition_Algebra_RankOneRepresentation`, `PolycyclicRecognition_Algebra_RationalAbelianTorsion`, `PolycyclicRecognition_Algebra_RationalCharacterCancellation`, `PolycyclicRecognition_Algebra_RationalFiniteCoinvariants`, `PolycyclicRecognition_Algebra_RationalModuleFunctor`, `PolycyclicRecognition_Algebra_RationalOrientationCoefficient`, `PolycyclicRecognition_Algebra_RationalOrientationExtension`, `PolycyclicRecognition_Algebra_RationalRankOneAction`, `PolycyclicRecognition_Algebra_RationalRepresentationFunctor`, `PolycyclicRecognition_Algebra_RationalScalarTwist`, `PolycyclicRecognition_Algebra_RealEigenAnnihilator`, `PolycyclicRecognition_Algebra_RealNilpotentLogIntertwiner`, `PolycyclicRecognition_Algebra_RelativeCommutatorSeries`, `PolycyclicRecognition_Algebra_RiemannianChartLength`, `PolycyclicRecognition_Algebra_ScalarExtendedH2CrossProduct`, `PolycyclicRecognition_Algebra_SemisimpleKernelProjection`, `PolycyclicRecognition_Algebra_SemisimpleSpectralOperator`, `PolycyclicRecognition_Algebra_SeparateGroupClosure`, `PolycyclicRecognition_Algebra_SequenceRealExtension`, `PolycyclicRecognition_Algebra_SourceBundleStates`, `PolycyclicRecognition_Algebra_SpectralLogValue`, `PolycyclicRecognition_Algebra_SpectralUnitGroup`, `PolycyclicRecognition_Algebra_SubgroupInductionExact`, `PolycyclicRecognition_Algebra_ThreeCongruenceMatrix`, `PolycyclicRecognition_Algebra_TupleLiftProjection`, `PolycyclicRecognition_Algebra_UltrafilterSubgroup`, `PolycyclicRecognition_Algebra_UniformPolynomialGrowth`, `PolycyclicRecognition_Algebra_UnitNetPartition`, `PolycyclicRecognition_Algebra_UnitaryCocycle`, `PolycyclicRecognition_Algebra_UnitaryMautner`, `PolycyclicRecognition_Algebra_WordLengthFiltration`, `PolycyclicRecognition_Analysis_BackwardSwitchProbability`, `PolycyclicRecognition_Analysis_BarChainExhaustion`, `PolycyclicRecognition_Analysis_CoarsePathWords`, `PolycyclicRecognition_Analysis_CompactGeneratingBalls`, `PolycyclicRecognition_Analysis_CompactPairs`, `PolycyclicRecognition_Analysis_ExactProfileTransport`, `PolycyclicRecognition_Analysis_FiniteKernelCoarseEquivalence`, `PolycyclicRecognition_Analysis_FlatSwitchSamples`, `PolycyclicRecognition_Analysis_HaarAveraging`, `PolycyclicRecognition_Analysis_HaarPrefixCoordinates`, `PolycyclicRecognition_Analysis_HaarProduct`, `PolycyclicRecognition_Analysis_IntegralKernelRepresentation`, `PolycyclicRecognition_Analysis_IntegralRepresentationMap`, `PolycyclicRecognition_Analysis_InvariantMetrization`, `PolycyclicRecognition_Analysis_MetricFolnerVolume`, `PolycyclicRecognition_Analysis_NormalizedEndpointMeasure`, `PolycyclicRecognition_Analysis_OccupationCompactRestriction`, `PolycyclicRecognition_Analysis_ProfileIncrementLimits`, `PolycyclicRecognition_Analysis_QuotientSectionRightHaar`, `PolycyclicRecognition_Analysis_RescaledAffineComparison`, `PolycyclicRecognition_Analysis_RetainedProbeAnchors`, `PolycyclicRecognition_Analysis_SeparatedTupleVolume`, `PolycyclicRecognition_Analysis_SourceBundleHaarImage`, `PolycyclicRecognition_Analysis_SuccessfulSampleBlockPaths`, `PolycyclicRecognition_Analysis_SupportSymmetries`, `PolycyclicRecognition_Analysis_TrivialTensorChainNaturality`, `PolycyclicRecognition_Analysis_TrivialTensorChains`, `PolycyclicRecognition_Analysis_UnitSeparatedNet`, `PolycyclicRecognition_Finiteness_CochainExhaustion`, `PolycyclicRecognition_Finiteness_CountableUnionCohomology`, `PolycyclicRecognition_Finiteness_DimensionFromRegularCohomology`, `PolycyclicRecognition_Finiteness_FiniteGroupProjectiveNorm`, `PolycyclicRecognition_Finiteness_FiniteIndexTopHomology`, `PolycyclicRecognition_Finiteness_GroupIsoDuality`, `PolycyclicRecognition_Finiteness_HomologyClassExhaustion`, `PolycyclicRecognition_Finiteness_HomologyOrientationEquiv`, `PolycyclicRecognition_Finiteness_InnerHomologyAction`, `PolycyclicRecognition_Finiteness_NormalQuotientCompleteVanishing`, `PolycyclicRecognition_Finiteness_OrientationHomologyAction`, `PolycyclicRecognition_Finiteness_ProjectiveTensorCoefficient`, `PolycyclicRecognition_Finiteness_QuotientCoinvariantsFiniteness`, `PolycyclicRecognition_Finiteness_RationalBicomplexComparison`, `PolycyclicRecognition_Finiteness_RationalGroupHomology`, `PolycyclicRecognition_Finiteness_RationalTensorHomology`, `PolycyclicRecognition_Finiteness_SubgroupBarResolution`, `PolycyclicRecognition_Geometry_CartanAdjointAction`, `PolycyclicRecognition_Geometry_CartanResidualAction`, `PolycyclicRecognition_Geometry_CartanResidualBounds`, `PolycyclicRecognition_Geometry_CartanSamplingParameters`, `PolycyclicRecognition_Geometry_CartanTransformedPolarTemplates`, `PolycyclicRecognition_Geometry_CompactFlowSegments`, `PolycyclicRecognition_Geometry_ContinuousFlowAffinity`, `PolycyclicRecognition_Geometry_ExponentialDuhamel`, `PolycyclicRecognition_Geometry_ExponentialDuhamelDerivative`, `PolycyclicRecognition_Geometry_FiniteLieSmooth`, `PolycyclicRecognition_Geometry_GenericWeightDirections`, `PolycyclicRecognition_Geometry_HeightChangeOfCoordinates`, `PolycyclicRecognition_Geometry_HorizontalFlowDerivative`, `PolycyclicRecognition_Geometry_LieExponential`, `PolycyclicRecognition_Geometry_MatrixDifferentialFromSmoothness`, `PolycyclicRecognition_Geometry_NilpotentLinearFlow`, `PolycyclicRecognition_Geometry_PolynomialDerivativeGrowth`, `PolycyclicRecognition_Geometry_PolynomialDifferential`, `PolycyclicRecognition_Geometry_PositiveSizeTriangularRepresentation`, `PolycyclicRecognition_Geometry_PositiveWeightCones`, `PolycyclicRecognition_Geometry_ProfileFlowConvergence`, `PolycyclicRecognition_Geometry_RationalFlowBoxes`, `PolycyclicRecognition_Geometry_RepresentedExponentialDifferential`, `PolycyclicRecognition_Geometry_RootFlow`, `PolycyclicRecognition_Geometry_RootRepresentation`, `PolycyclicRecognition_Geometry_RootSwitchCurves`, `PolycyclicRecognition_Geometry_SpectralLieDerivation`, `PolycyclicRecognition_Geometry_SupportedFlowLipschitz`, `PolycyclicRecognition_Geometry_TriangularAdjointEmbedding`, `PolycyclicRecognition_Geometry_TriangularExponentialAverage`, `PolycyclicRecognition_Geometry_TriangularOperatorAverage`, `PolycyclicRecognition_Geometry_WeightChambers`, `PolycyclicRecognition_Geometry_WeightSamplingPolytope`, `PolycyclicRecognition_Lattices_IntegerSemidirectLattice`, `PolycyclicRecognition_Lattices_IntegerTimeLattice`, `PolycyclicRecognition_Lattices_SemidirectUniformLattice`, `TendstoTactic`, `Thompson_FiniteAverage`, `Thompson_FiniteCoarea`, `Thompson_FiniteLevels`, `Thompson_MeanApproximation`, `Thompson_ProbabilityDefects`, `ToMathlib_Analysis_Matrix_UnitaryAux`, `ToMathlib_GroupTheory_Closure`, `ToMathlib_GroupTheory_CosetCover`, `Unipotent_Commutator`, `Unipotent_FG`, `Unipotent_GammaN`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ093D010` and `OAIQ093D011`; the statements `OAI.PolycyclicRecognition.CartanWordModel.exists_controlled_increment_volume`, `OAI.PolycyclicRecognition.CartanWordModel.exists_sequence_path_tuple_lifts`, `OAI.PolycyclicRecognition.CartanWordModel.terminal_product_exponent_le` and `unipotent_commutator_trivial`; the proofs of `GeneratesNS.theorem_3_1`, `OAI_PolycyclicRecognition_CartanWordModel_exists_directional_visit_bound`, `OAI.PolycyclicRecognition.CartanWordModel.exists_segmentWordPath_bound`, `OAI.PolycyclicRecognition.CartanWordModel.exists_templateWordPath_bound`, `centralizer_iso`, `fg_of_subgroup_fg_nilpotent` and `unipotent_commutator_trivial`.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/GroupTheory at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega

section
-- module Solutions.OAIQ093_PR.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
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
in d13f23b (Kadison similarity, oaiq-075). A def, made a local instance by the port only in modules naming
`CommCStarAlgebra` or `IsMulCommutative` (`oaiport.comm_cstar_line`): as a global instance it made `whnf` time out in
FactorGeneration modules with their own `CStarAlgebra` instances on a subalgebra (oaiq-122). -/
@[reducible]
noncomputable def starSubalgebraCommCStarAlgebra {B : Type*} [CStarAlgebra B] (A : StarSubalgebra ℂ B)
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
/-- Mathlib d13f23b's `MeasurableSpace Circle` (Mathlib.MeasureTheory.Group.Circle): the subtype structure. A def,
turned on as a local instance in the modules that use the characters `𝐞`/`fourierChar`/`probChar` (q141). -/
@[reducible] def circleMeasurableSpace : MeasurableSpace Circle :=
  inferInstanceAs <| MeasurableSpace <| Subtype (· ∈ Submonoid.unitSphere ℂ)
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NilpotentProducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Polynomial bounds for products with nilpotent increments

The finite-degree product estimate in the nilpotent-coordinate argument is
proved here in a normed associative algebra. The factors need not commute.
Homogeneous terms are sums over ordered sublists, so nilpotence truncates the
expansion before a fixed degree, independently of the number of factors.
-/

namespace PolycyclicRecognition

open scoped BigOperators

section Ring

variable {A : Type*} [Ring A]

/-- The degree-`k` part of an ordered product of `1 + x`. -/
def homogeneousProduct (l : List A) (k : ℕ) : A :=
  ((l.sublistsLen k).map List.prod).sum

@[simp] theorem homogeneousProduct_zero (l : List A) : homogeneousProduct l 0 = 1 := by
  simp [homogeneousProduct]

@[simp] theorem homogeneousProduct_nil_succ (k : ℕ) :
    homogeneousProduct ([] : List A) (k + 1) = 0 := by
  simp [homogeneousProduct]

end Ring

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_GeneratorConjugation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual group words realizing a basis of generator conjugates

A faithful exponential-compatible representation turns the operator words
from `GeneratorOrbit` into conjugation by finite words in generator
one-parameter subgroups. No generation or submersion assertion is assumed.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieAlgebra

/-- A finite word using only the specified generator exponentials. -/
def generatorGroupWord {I L G : Type*} [SMul ℝ L] [Group G]
    (X : I → L) (Exp : L → G) (w : List (I × ℝ)) : G :=
  (w.map (fun p => Exp (p.2 • X p.1))).prod

@[simp] theorem generatorGroupWord_nil {I L G : Type*} [SMul ℝ L] [Group G]
    (X : I → L) (Exp : L → G) : generatorGroupWord X Exp [] = 1 := rfl

@[simp] theorem generatorGroupWord_cons {I L G : Type*} [SMul ℝ L] [Group G]
    (X : I → L) (Exp : L → G) (i : I) (t : ℝ) (w : List (I × ℝ)) :
    generatorGroupWord X Exp ((i, t) :: w) = Exp (t • X i) * generatorGroupWord X Exp w := rfl

attribute [local instance 100] LieRing.ofAssociativeRing

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_LieExponential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Compatibility with OpenAI's Mathlib (d13f23b): the tangent-space instances and casts it
declares beside `TangentSpace` (`IsManifold/Basic.lean`, `IsManifold/ExtChartAt.lean`). -/

section TangentSpaceCompat

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {x : M}

/-- The definitional identification of the tangent spaces at two points. -/
def tangentSpaceCast (x y : M) : TangentSpace I x ≃L[𝕜] TangentSpace I y where
  toFun v := v
  invFun v := v
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end TangentSpaceCompat
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_FiniteLieSmooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Smoothness of finite Lie polynomials

A finite-dimensional Lie bracket is a continuous bilinear map in basis
coordinates. Consequently the actual finite Dynkin expressions are smooth;
no smoothness of a chosen logarithm chart is assumed here.
-/

noncomputable section

namespace PolycyclicRecognition

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]

local instance finiteLieSmoothNormedAddCommGroup : NormedAddCommGroup L :=
  NormedAddCommGroup.induced _ _ (finBasis ℝ L).equivFun.toLinearMap
    (finBasis ℝ L).equivFun.injective
local instance finiteLieSmoothNormedSpace : NormedSpace ℝ L :=
  NormedSpace.induced ℝ _ _ (finBasis ℝ L).equivFun.toLinearMap

/-- Continuous bilinear realization of the given finite-dimensional bracket. -/
def finiteLieBracket : L →L[ℝ] L →L[ℝ] L :=
  (show L →ₗ[ℝ] L →L[ℝ] L from
    { toFun := fun x => Module.End.toContinuousLinearMap (𝕜 := ℝ) L (LieModule.toEnd ℝ L L x)
      map_add' := by intro x y; ext z; exact add_lie x y z
      map_smul' := by intro c x; ext z; exact smul_lie c x z }).toContinuousLinearMap

@[simp] theorem finiteLieBracket_apply (x y : L) : finiteLieBracket x y = ⁅x, y⁆ := rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_GeneratorSchemes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite generator schemes with locally open endpoint maps

A conjugated-generator basis gives a single finite scheme, with fixed
conjugating words, whose endpoint map covers a neighborhood of the identity.
The logarithm of that map has the identity-rank differential proved from BCH.
-/

noncomputable section

namespace PolycyclicRecognition

open Module

variable {I L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {G : Type*} [Group G]

local instance generatorSchemeNormedAddCommGroup : NormedAddCommGroup L :=
  NormedAddCommGroup.induced _ _ (finBasis ℝ L).equivFun.toLinearMap
    (finBasis ℝ L).equivFun.injective
local instance generatorSchemeNormedSpace : NormedSpace ℝ L :=
  NormedSpace.induced ℝ _ _ (finBasis ℝ L).equivFun.toLinearMap

/-- Reverse a generator word and negate its one-parameter amplitudes. -/
def inverseGeneratorWord (w : List (I × ℝ)) : List (I × ℝ) :=
  w.reverse.map (fun p => (p.1, -p.2))

variable (X : I → L) (Exp : L → G)

/-- Fixed conjugating words with one variable generator inserted in each. -/
def generatorSchemeWord {n : ℕ} (w : Fin n → List (I × ℝ)) (i : Fin n → I)
    (t : Fin n → ℝ) : List (I × ℝ) :=
  (List.ofFn (fun k => w k ++ [(i k, t k)] ++ inverseGeneratorWord (w k))).flatten

attribute [local instance 100] LieRing.ofAssociativeRing

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_JointDirectionLabels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Joint transport of direction labels in both flow times

Keeping both times as coordinates turns the horizontal flows into
measure-preserving skew products. This supplies local convergence in measure
on triples directly, including compact sets that are not product sets.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Filter Set
open scoped Topology

def pairTimeMeasure : Measure (ℝ × ℝ) := volume.prod volume

instance instSigmaFiniteProdRealPairTimeMeasure : SigmaFinite pairTimeMeasure := by unfold pairTimeMeasure; infer_instance

instance instIsLocallyFiniteMeasureProdRealPairTimeMeasure : IsLocallyFiniteMeasure pairTimeMeasure := by unfold pairTimeMeasure; infer_instance

variable {G V : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

def timedRightTranslation (Exp : V → G) (hExp : Continuous Exp)
    (pick : (ℝ × ℝ) → ℝ) (hpick : Continuous pick) (v : V) :
    C((ℝ × ℝ) × G, (ℝ × ℝ) × G) :=
  ⟨fun z => (z.1, z.2 * Exp (pick z.1 • v)), by fun_prop⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CompactFlowSegments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compact families of flow segments remain in an open domain -/

noncomputable section

namespace PolycyclicRecognition

open Set Filter
open scoped Topology

variable {G V : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

def flowSegmentPoint (Exp : V → G) (v : V) (z : (ℝ × ℝ) × G) (r : ℝ) : G :=
  z.2 * Exp (((1 - r) * z.1.1 + r * z.1.2) • v)

def flowSegmentDomain (U : Set G) (Exp : V → G) (v : V) : Set ((ℝ × ℝ) × G) :=
  {z | ∀ r ∈ Icc (0 : ℝ) 1, flowSegmentPoint Exp v z r ∈ U}

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ContinuousFlowAffinity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Continuity upgrades almost-everywhere affine flow restrictions -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped Topology

variable {G V W : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

def flowLineBase (U : Set G) (Exp : V → G) (v : V) (T : ℝ) : Set G :=
  {g | ∀ t ∈ Icc 0 T, g * Exp (t • v) ∈ U}

def flowLineSlope (f : G → W) (Exp : V → G) (v : V) (T : ℝ) (g : G) : W :=
  T⁻¹ • (f (g * Exp (T • v)) - f g)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_AdmissibleGeneratorWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Generator words whose entire path stays in an open set -/

noncomputable section

namespace PolycyclicRecognition

open Set Filter
open scoped Topology

variable {G V I : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

def generatorWordBase (U : Set G) (Exp : V → G) (X : I → V) :
    List (I × ℝ) → Set G
  | [] => U
  | (i, t) :: w => flowLineBase U Exp (t • X i) 1 ∩
      (fun g => g * Exp (t • X i)) ⁻¹' generatorWordBase U Exp X w

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialCoordinateGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The group carried by a polynomial coordinate law

This type keeps the group multiplication distinct from vector addition. The
exponential-coordinate bijection is the identity on underlying points.
-/

noncomputable section

namespace PolycyclicRecognition

variable {V I : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A word evaluated directly by the polynomial multiplication. -/
def polynomialWord (m : V → V → V) (X : I → V) : List (I × ℝ) → V
  | [] => 0
  | (i, t) :: w => m (t • X i) (polynomialWord m X w)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_PolynomialDifferential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Formal partial derivatives are the actual differential -/

noncomputable section

namespace PolycyclicRecognition

open MvPolynomial
open scoped BigOperators

def polynomialDifferential {m : ℕ} (p : MvPolynomial (Fin m) ℝ) (x : Fin m → ℝ) :
    (Fin m → ℝ) →L[ℝ] ℝ :=
  ∑ j, MvPolynomial.eval x (pderiv j p) • ContinuousLinearMap.proj j

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialMinor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial derivative minors and their uniform degree bounds -/

noncomputable section

namespace PolycyclicRecognition

open MvPolynomial Matrix
open scoped BigOperators

def polynomialJacobianMinor {n k : ℕ} (p : Fin n → MvPolynomial (Fin (n + k)) ℝ) :
    MvPolynomial (Fin (n + k)) ℝ :=
  Matrix.det (Matrix.of fun i j => pderiv (Fin.castAdd k j) (p i))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ExpandedSchemeAmplitudes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The conjugate scheme inside a word with independent amplitudes -/

noncomputable section

namespace PolycyclicRecognition

variable {I : Type*} {n d c : ℕ}

/-- Each slot remembers either a fixed amplitude or one inserted coordinate. -/
def schemeAmplitudeSlots (w : Fin n → List (I × ℝ)) (i : Fin n → I) :
    List (I × (ℝ ⊕ Fin n)) :=
  (List.ofFn fun j =>
    (w j).map (fun p => (p.1, Sum.inl p.2)) ++ [(i j, Sum.inr j)] ++
      (inverseGeneratorWord (w j)).map (fun p => (p.1, Sum.inl p.2))).flatten

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_AlternatingProductSubmersion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Submersion of an alternating product from two linear images

If generators in the union of two images bracket-generate the limiting
algebra, one fixed alternating product has a surjective differential.
Identity factors pad the unused side of each generator slot. The rank is
proved for the full product map, before restricting any parameters.
-/

noncomputable section
namespace PolycyclicRecognition

open Module

variable {U V : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

def generatorPair (side : Bool) (v : U) : U × U :=
  if side then (v, 0) else (0, v)

def generatorPairParameters {I : Type*} {m : ℕ}
    (side : I → Bool) (v : I → U) (letters : Fin m → I) :
    (Fin m → ℝ) →L[ℝ] (Fin m → U × U) :=
  ContinuousLinearMap.pi (fun j =>
    (ContinuousLinearMap.proj j : (Fin m → ℝ) →L[ℝ] ℝ).smulRight
      (generatorPair (side (letters j)) (v (letters j))))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_Polycyclic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Compatibility with OpenAI's Mathlib (d13f23b): its instance that `comap` keeps a finite index
(`GroupTheory/Index.lean`). -/

instance Subgroup.finiteIndex_comap_compat {G G' : Type*} [Group G] [Group G'] (f : G →* G')
    (H' : Subgroup G') [H'.FiniteIndex] : (H'.comap f).FiniteIndex :=
  ⟨by rw [Subgroup.index_comap]; exact Subgroup.FiniteIndex.index_ne_zero (H := H'.subgroupOf f.range)⟩
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FinsuppRepresentationModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The group-ring module of a direct sum of representations -/

noncomputable section
namespace PolycyclicRecognition

open Representation
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2

variable (k : Type) [CommRing k] (G : Type) [Group G] (α : Type) (A : Rep k G)

def finsuppRepresentationModuleEquiv :
    (α →₀ A.ρ.asModule) ≃ₗ[k[G]] (Rep.finsupp α A).ρ.asModule where
  toAddEquiv := (Finsupp.mapRange.addEquiv A.ρ.asModuleEquiv.toAddEquiv).trans
    (Rep.finsupp α A).ρ.asModuleEquiv.symm.toAddEquiv
  map_smul' r v := by
    apply (Rep.finsupp α A).ρ.asModuleEquiv.injective
    let e := Finsupp.mapRange.linearEquiv (α := α) A.ρ.asModuleEquiv
    change e (r • v) = (A.ρ.finsupp α).asAlgebraHom r (e v)
    induction r using MonoidAlgebra.induction_linear with
    | zero => simp
    | add r s hr hs => simp only [add_smul, map_add, hr, hs, LinearMap.add_apply]
    | single g c =>
      induction v using Finsupp.induction_linear with
      | zero => simp
      | add v w hv hw => simp only [smul_add, map_add, hv, hw]
      | single i a =>
        simp [e, Representation.asAlgebraHom_single, Representation.finsupp_single]
        ext j
        rfl


end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FiniteFinsuppHom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Hom out of a finite group-ring module commutes with direct sums -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory Representation
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2

variable (k : Type) [CommRing k] (G : Type) [Group G]
  (α : Type) (A B : Rep k G)

def finsuppHomPostcompEquiv :
    (A.ρ.asModule →ₗ[k[G]] (α →₀ B.ρ.asModule)) ≃ₗ[k]
      (A.ρ.asModule →ₗ[k[G]] (Rep.finsupp α B).ρ.asModule) where
  __ := LinearEquiv.arrowCongrAddEquiv (LinearEquiv.refl k[G] A.ρ.asModule)
    (finsuppRepresentationModuleEquiv k G α B)
  map_smul' c f := by
    ext a
    change finsuppRepresentationModuleEquiv k G α B (c • f a) =
      c • finsuppRepresentationModuleEquiv k G α B (f a)
    exact ((finsuppRepresentationModuleEquiv k G α B).restrictScalars k).map_smul c (f a)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_AscendingCoinvariantRelations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coinvariant relations are detected in a finite subgroup stage

For an ascending exhaustion of a group, a linear combination of coinvariant
relations uses only finitely many group elements. It therefore already lies
in the relations of one stage of the exhaustion.
-/
noncomputable section
namespace PolycyclicRecognition
open Representation
variable {K V : Type} [Group K] [AddCommGroup V] [Module ℤ V]
variable (ρ : Representation ℤ K V)

abbrev subgroupCoinvariantRelations (H : Subgroup K) : Submodule ℤ V :=
  Coinvariants.ker (ρ.comp H.subtype)

theorem subgroupCoinvariantRelations_mono {H J : Subgroup K} (h : H ≤ J) :
    subgroupCoinvariantRelations ρ H ≤ subgroupCoinvariantRelations ρ J := by
  apply Submodule.span_le.mpr
  rintro x ⟨⟨g, v⟩, rfl⟩
  exact Coinvariants.sub_mem_ker (ρ := ρ.comp J.subtype) ⟨g.val, h g.property⟩ v

theorem subgroupCoinvariantRelations_exhaustion (H : ℕ → Subgroup K) (S : Subgroup K)
    (hmono : Monotone H) (hcover : ∀ g ∈ S, ∃ n, g ∈ H n)
    {v : V} (hv : v ∈ subgroupCoinvariantRelations ρ S) :
    ∃ n, v ∈ subgroupCoinvariantRelations ρ (H n) := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨g, v⟩, rfl⟩ := hx
    obtain ⟨n, hn⟩ := hcover g.val g.property
    exact ⟨n, Coinvariants.sub_mem_ker (ρ := ρ.comp (H n).subtype) ⟨g.val, hn⟩ v⟩
  | zero => exact ⟨0, Submodule.zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨i, hi⟩ := hx
    obtain ⟨j, hj⟩ := hy
    exact ⟨max i j, Submodule.add_mem _
      (subgroupCoinvariantRelations_mono ρ (hmono (Nat.le_max_left _ _)) hi)
      (subgroupCoinvariantRelations_mono ρ (hmono (Nat.le_max_right _ _)) hj)⟩
  | smul r x _ hx =>
    obtain ⟨n, hn⟩ := hx
    exact ⟨n, Submodule.smul_mem _ r hn⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_HaarAveraging
attribute [-instance] _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Averaging translated masses

The boundary argument averages a Radon measure over Haar translates.  The
identities below use genuine measures and measurable multiplication, including
the Tonelli step.  Invariance is required only of Haar measure, not of the
measure whose translated masses are being compared.
-/

namespace PolycyclicRecognition

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal

variable {G : Type*} [Group G] [MeasurableSpace G]
  [MeasurableMul₂ G] [MeasurableInv G]

/-- A left translate, expressed as a measurable preimage. -/
def leftTranslate (E : Set G) (z : G) : Set G := {y | z⁻¹ * y ∈ E}

/-- Balls for a left-invariant length function. -/
def lengthBall (ℓ : GroupSeminorm G) (r : ℝ) : Set G := {x | ℓ x < r}

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_AutocorrelationRecurrence
attribute [-instance] _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The positive autocorrelation behind backward recurrence -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set
open scoped ENNReal

variable {G : Type*} [Group G] [MeasurableSpace G]
  [MeasurableMul₂ G] [MeasurableInv G]

/-- Average a function over the inverse of a sampled right increment. -/
def rightInverseAverage (σ : Measure G) (f : G → ℝ≥0∞) (x : G) : ℝ≥0∞ :=
  ∫⁻ s, f (x * s⁻¹) ∂σ

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_BackwardRecurrenceStep
attribute [-instance] _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One quantitative step of backward recurrence -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set Filter
open scoped ENNReal

variable {G : Type*} [Group G] [MeasurableSpace G]
  [MeasurableMul₂ G] [MeasurableInv G]

/-- Probability of returning to `A` after a difference of two independent
increments with law `σ`. -/
def twoSampleReturn (σ : Measure G) (A : Set G) (x : G) : ℝ≥0∞ :=
  ∫⁻ s₁, ∫⁻ s₂, A.indicator (fun _ => (1 : ℝ≥0∞)) (x * s₁ * s₂⁻¹) ∂σ ∂σ

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CompactPairs
attribute [-instance] _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compact sections of Lipschitz quasi-inverse pairs

The space consists of actual continuous maps, with the compact-open topology.
Uniform Lipschitz bounds and a bound at one point give compactness in a proper
target. The quasi-inverse conditions are closed, including their compositions.
-/

noncomputable section

open Set Metric
open scoped NNReal

namespace PolycyclicRecognition

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y] [ProperSpace Y]

/-- The compact family of maps with a common Lipschitz constant and a common
bound at one point. -/
theorem isCompact_lipschitz_family (K : ℝ≥0) (a : X) (b : Y) (R : ℝ) :
    IsCompact {f : C(X, Y) | LipschitzWith K f ∧ dist (f a) b ≤ R} := by
  let S : Set C(X, Y) := {f | LipschitzWith K f ∧ dist (f a) b ≤ R}
  let T : Set (X → Y) := {f | LipschitzWith K f ∧ dist (f a) b ≤ R}
  have hT : IsClosed T :=
    (isClosed_setOfPred_lipschitzWith K).inter
      (isClosed_le ((continuous_apply a).dist continuous_const) continuous_const)
  have heq : ContinuousMap.toFun '' S = T := by
    ext f
    constructor
    · rintro ⟨f, hf, rfl⟩
      exact hf
    · rintro ⟨hf, hb⟩
      exact ⟨⟨f, hf.continuous⟩, ⟨hf, hb⟩, rfl⟩
  have hcompact : IsCompact T := by
    apply (isCompact_pi_infinite (fun x : X =>
      isCompact_closedBall b ((K : ℝ) * dist x a + R))).of_isClosed_subset hT
    intro f hf x
    change dist (f x) b ≤ (K : ℝ) * dist x a + R
    exact (dist_triangle (f x) (f a) b).trans
      (add_le_add (hf.1.dist_le_mul x a) hf.2)
  apply ArzelaAscoli.isCompact_of_equicontinuous S
  · rwa [heq]
  · exact (LipschitzWith.uniformEquicontinuous
      (fun f : S => (f : C(X, Y))) K (fun f => f.property.1)).equicontinuous

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CenteredSourceTerminals
attribute [-instance] _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The source terminal set for a tuple centered at its initial image -/

noncomputable section
namespace PolycyclicRecognition

open Set
open scoped NNReal

variable {N G : Type*} [TopologicalSpace N] [Group G] [MetricSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G]

def relativeTupleTerminals {h : ℕ} (ι : N → G) (origin base pivot : G)
    (last : Fin h) (S : Set (Fin h → N)) : Set G :=
  (fun v => origin⁻¹ * (base * ι (v last) * pivot)) '' S

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CharacteristicFiniteIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Characteristic finite-index refinements

A finite-index subgroup of a finitely generated group contains a
characteristic finite-index subgroup. We intersect kernels of maps into the
finite permutation group on its cosets. This is the finite-index refinement
needed in the induction proving virtual torsion freeness.
-/

noncomputable section
namespace PolycyclicRecognition

variable {G F : Type*} [Group G] [Group F]

/-- The intersection only ranges over a finite type of homomorphisms. -/
def finiteTargetKernel (G F : Type*) [Group G] [Group F] : Subgroup G :=
  ⨅ f : G →* F, f.ker

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_QuotientSectionCoordinates
attribute [-instance] _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coordinates separating a quotient and its kernel

A continuous section of the actual quotient map gives global coordinates.
The formulas retain the conjugation and section cocycle needed for product
Haar measure and the ideal-coordinate estimates.
-/

noncomputable section
namespace PolycyclicRecognition

variable {N Q : Type*} [Group N] [Group Q]
  [TopologicalSpace N] [TopologicalSpace Q] [IsTopologicalGroup N] [IsTopologicalGroup Q]
  (π : N →* Q) (hπ : Continuous π) (s : C(Q, N)) (hs : ∀ q, π (s q) = q)

/-- The section cocycle of left translation, valued in the actual kernel. -/
def quotientSectionCocycle (n : N) (q : Q) : π.ker :=
  ⟨n * s q * (s (π n * q))⁻¹, by simp [hs]⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ClosedEmbeddingSplitKernel
attribute [-instance] _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A closed kernel embedding gives a closed embedding over a split quotient -/

noncomputable section
namespace PolycyclicRecognition

variable {N G Q : Type*} [Group N] [Group G] [Group Q]
  [TopologicalSpace N] [TopologicalSpace G] [TopologicalSpace Q]
  [IsTopologicalGroup N] [IsTopologicalGroup G] [IsTopologicalGroup Q]
  (f : N →* G) (hf : Continuous f) (π : G →* Q) (hπ : Continuous π)
  (s : C(Q, N)) (hs : ∀ q, π (f (s q)) = q)

/-- The homomorphism on the actual kernels. -/
def splitKernelHom : (π.comp f).ker →* π.ker :=
  { toFun n := ⟨f n, n.property⟩
    map_one' := Subtype.ext (map_one f)
    map_mul' a b := Subtype.ext (map_mul f (a : N) (b : N)) }

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CoordinateMinorPermutation
attribute [-instance] _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reordering an actual nonzero minor into the sliced coordinates -/

noncomputable section

namespace PolycyclicRecognition

open Set MeasureTheory

/-- This map permutes coordinates, preserving both the cube and Lebesgue measure. -/
def reindexParameters {l m : ℕ} (e : Fin l ≃ Fin m) :
    (Fin l → ℝ) →L[ℝ] (Fin m → ℝ) :=
  ContinuousLinearMap.pi (fun j => ContinuousLinearMap.proj (e.symm j))

@[simp] theorem reindexParameters_apply {l m : ℕ} (e : Fin l ≃ Fin m)
    (x : Fin l → ℝ) (j : Fin m) : reindexParameters e x j = x (e.symm j) := rfl

@[simp] theorem reindexParameters_apply_equiv {l m : ℕ} (e : Fin l ≃ Fin m)
    (x : Fin l → ℝ) (j : Fin l) : reindexParameters e x (e j) = x j := by simp

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_IntegerTimeLattice
attribute [-instance] _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The integer time lattice in the real one-parameter group -/

noncomputable section
namespace PolycyclicRecognition
open Set

def integerTimeLattice : Subgroup (Multiplicative ℝ) :=
  (AddSubgroup.zmultiples (1 : ℝ)).toSubgroup

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_SemidirectUniformLattice
attribute [-instance] _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform lattices in a semidirect product

The lattices in the two factors form a lattice whenever the acting lattice
preserves the first lattice. The compact cover uses the inverse action before
reducing the first coordinate.
-/

noncomputable section
namespace PolycyclicRecognition
open Set
variable {N D : Type*} [Group N] [Group D]
  [TopologicalSpace N] [TopologicalSpace D]
  (φ : D →* MulAut N) (Λ : Subgroup N) (Δ : Subgroup D)
  (hφ : ∀ d ∈ Δ, ∀ x ∈ Λ, φ d x ∈ Λ)

def semidirectLattice : Subgroup (N ⋊[φ] D) where
  carrier := {p | p.left ∈ Λ ∧ p.right ∈ Δ}
  one_mem' := ⟨Λ.one_mem, Δ.one_mem⟩
  mul_mem' := by
    intro p q hp hq
    exact ⟨Λ.mul_mem hp.1 (hφ p.right hp.2 q.left hq.1), Δ.mul_mem hp.2 hq.2⟩
  inv_mem' := by
    intro p hp
    exact ⟨hφ p.right⁻¹ (Δ.inv_mem hp.2) p.left⁻¹ (Λ.inv_mem hp.1), Δ.inv_mem hp.2⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_IntegerSemidirectLattice
attribute [-instance] _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The integral semidirect product is the lattice in its real extension -/

noncomputable section
namespace PolycyclicRecognition
variable {H N : Type*} [Group H] [Group N]

def integerTimeHom : Multiplicative ℤ →* Multiplicative ℝ where
  toFun n := Multiplicative.ofAdd (n.toAdd : ℝ)
  map_one' := by apply Multiplicative.ext; exact Int.cast_zero
  map_mul' n m := by apply Multiplicative.ext; exact Int.cast_add _ _

theorem realAction_int (φ : Multiplicative ℝ →* MulAut N) (n : ℤ) :
    φ (Multiplicative.ofAdd (n : ℝ)) = φ (Multiplicative.ofAdd 1) ^ n := by
  have he : (Multiplicative.ofAdd (1 : ℝ)) ^ n = Multiplicative.ofAdd (n : ℝ) := by
    apply Multiplicative.ext
    change n • (1 : ℝ) = (n : ℝ)
    simp
  rw [← he, map_zpow]

theorem mulAut_zpow_semiconj (a : MulAut H) (b : MulAut N) (e : H → N)
    (he : ∀ x, e (a x) = b (e x)) (n : ℤ) (x : H) :
    e ((a ^ n) x) = (b ^ n) (e x) := by
  have hi (y : H) : e (a.symm y) = b.symm (e y) := by
    apply b.injective
    rw [← he, a.apply_symm_apply, b.apply_symm_apply]
  have hp (a' : MulAut H) (b' : MulAut N) (h : ∀ y, e (a' y) = b' (e y)) (k : ℕ) :
      ∀ y, e ((a' ^ k) y) = (b' ^ k) (e y) := by
    induction k with
    | zero => exact fun _ => rfl
    | succ k ih =>
      intro y
      rw [pow_succ', pow_succ']
      change e (a' ((a' ^ k) y)) = b' ((b' ^ k) (e y))
      rw [h, ih]
  cases n with
  | ofNat n => exact hp a b he n x
  | negSucc n =>
    change e ((a ^ (-((n + 1 : ℕ) : ℤ))) x) = (b ^ (-((n + 1 : ℕ) : ℤ))) (e x)
    rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, ← inv_pow, ← inv_pow]
    exact hp a.symm b.symm hi (n + 1) x

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CyclicPowerIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Compatibility with OpenAI's Mathlib (d13f23b): a lemma it has and ours lacks. -/

namespace OAI

/-! # Finite-index cyclic subgroups for an arbitrary positive power -/

noncomputable section
namespace PolycyclicRecognition
variable {H : Type} [Group H]

def integerScaleHom (m : ℕ) : Multiplicative ℤ →* Multiplicative ℤ where
  toFun n := Multiplicative.ofAdd ((m : ℤ) * n.toAdd)
  map_one' := by apply Multiplicative.ext; simp
  map_mul' n k := by apply Multiplicative.ext; exact mul_add _ n.toAdd k.toAdd

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FiniteRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Restriction through a surjective group homomorphism preserves finite generation -/

noncomputable section
namespace PolycyclicRecognition

open Representation
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2

variable (k : Type) [CommRing k] {G J : Type} [Group G] [Group J]
  (f : J →* G) (A : Rep k G)

def restrictionModuleEquiv :
    A.ρ.asModule ≃ₗ[k] (Rep.res f A).ρ.asModule :=
  A.ρ.asModuleEquiv.trans (Rep.res f A).ρ.asModuleEquiv.symm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FiniteInduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite generation is preserved by subgroup induction -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory Representation
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2

variable (k : Type) [CommRing k] {G : Type} [Group G]
  (N : Subgroup G) (A : Rep k N)

def inductionAtOne (a : A.ρ.asModule) : (Rep.ind N.subtype A).ρ.asModule :=
  (Rep.ind N.subtype A).ρ.asModuleEquiv.symm
    (IndV.mk N.subtype A.ρ 1 (A.ρ.asModuleEquiv a))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_GroupIsoDuality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Transport of regular-module cohomology and duality through group isomorphisms -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2

variable (k : Type) [CommRing k] {G J : Type} [Group G] [Group J]

def regularCohomologyGroupIso (e : G ≃* J) (i : ℕ) :
    groupCohomology (Rep.leftRegular k G) i ≅ groupCohomology (Rep.leftRegular k J) i :=
  groupCohomology.mapIso e (MonoidAlgebra.domCongr k k e).toLinearEquiv (by
    intro g
    apply MonoidAlgebra.lhom_ext'
    intro h
    apply LinearMap.ext_ring
    simp [map_mul]) i

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_IntegerQuotientCoordinates
attribute [-instance] _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coordinates adapted to a chosen lift of an infinite cyclic quotient -/

noncomputable section
namespace PolycyclicRecognition

variable {G : Type} [Group G] (q : G →* Multiplicative ℤ)
  (t : G) (ht : q t = Multiplicative.ofAdd 1)

def integerQuotientHeight (g : G) : ℤ := (q g).toAdd

@[simp] theorem integerQuotientHeight_mul (g h : G) :
    integerQuotientHeight q (g * h) = integerQuotientHeight q g + integerQuotientHeight q h := by
  simp [integerQuotientHeight]

@[simp] theorem integerQuotientHeight_kernel (n : q.ker) : integerQuotientHeight q n = 0 := by
  exact congrArg Multiplicative.toAdd n.property

include ht in
@[simp] theorem integerQuotientHeight_lift_zpow (i : ℤ) :
    integerQuotientHeight q (t ^ i) = i := by
  simp [integerQuotientHeight, ht]

def integerQuotientPart (g : G) : q.ker :=
  ⟨g * t ^ (-integerQuotientHeight q g), by
    change q (g * t ^ (-integerQuotientHeight q g)) = 1
    apply Multiplicative.toAdd.injective
    simp [map_mul, map_zpow, ht, integerQuotientHeight]⟩

theorem integerQuotientPart_decompose (g : G) :
    (integerQuotientPart q t ht g : G) * t ^ integerQuotientHeight q g = g := by
  simp [integerQuotientPart, zpow_neg, mul_assoc]

@[simp] theorem integerQuotientPart_kernel_mul (n : q.ker) (g : G) :
    integerQuotientPart q t ht ((n : G) * g) = n * integerQuotientPart q t ht g := by
  apply Subtype.ext
  simp [integerQuotientPart, mul_assoc]

@[simp] theorem integerQuotientPart_lift_zpow (i : ℤ) :
    integerQuotientPart q t ht (t ^ i) = 1 := by
  apply Subtype.ext
  simp [integerQuotientPart, integerQuotientHeight_lift_zpow q t ht, zpow_neg]

def integerQuotientCoordinates : G ≃ ℤ × q.ker where
  toFun g := (integerQuotientHeight q g, integerQuotientPart q t ht g)
  invFun p := (p.2 : G) * t ^ p.1
  left_inv g := integerQuotientPart_decompose q t ht g
  right_inv p := by
    rcases p with ⟨i, n⟩
    apply Prod.ext
    · simp [integerQuotientHeight_lift_zpow q t ht]
    · simp [integerQuotientPart_lift_zpow q t ht]

theorem integerQuotientPart_lift_mul (g : G) :
    integerQuotientPart q t ht (t * g) =
      MulAut.conjNormal (H := q.ker) t (integerQuotientPart q t ht g) := by
  apply Subtype.ext
  change t * g * t ^ (-integerQuotientHeight q (t * g)) =
    t * (g * t ^ (-integerQuotientHeight q g)) * t⁻¹
  have hh : integerQuotientHeight q t = 1 := by simp [integerQuotientHeight, ht]
  rw [integerQuotientHeight_mul, hh]
  have he : -(1 + integerQuotientHeight q g) = -integerQuotientHeight q g + (-1) := by omega
  rw [he, zpow_add, zpow_neg_one]
  group

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_IntegerRegularCoordinates
attribute [-instance] _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The regular module in coordinates adapted to a cyclic quotient -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory Representation
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2

variable (k : Type) [CommRing k] {G : Type} [Group G]
  (q : G →* Multiplicative ℤ) (t : G) (ht : q t = Multiplicative.ofAdd 1)

def integerRegularLinearEquiv : k[G] ≃ₗ[k] (ℤ →₀ k[q.ker]) :=
  (MonoidAlgebra.coeffLinearEquiv k).trans
    ((Finsupp.domLCongr (integerQuotientCoordinates q t ht)).trans
      ((Finsupp.curryLinearEquiv k).trans
        (Finsupp.mapRange.linearEquiv (MonoidAlgebra.coeffLinearEquiv k).symm)))

@[simp] theorem integerRegularLinearEquiv_single (g : G) (a : k) :
    integerRegularLinearEquiv k q t ht (MonoidAlgebra.single g a) =
      Finsupp.single (integerQuotientHeight q g)
        (MonoidAlgebra.single (integerQuotientPart q t ht g) a) := by
  simp [integerRegularLinearEquiv, Finsupp.curryLinearEquiv, integerQuotientCoordinates]

def integerRestrictedRegularEquiv :
    (Rep.res q.ker.subtype (Rep.leftRegular k G)).ρ.Equiv
      (Rep.finsupp ℤ (Rep.leftRegular k q.ker)).ρ :=
  Representation.Equiv.mk (integerRegularLinearEquiv k q t ht) fun n => by
    apply MonoidAlgebra.lhom_ext'
    intro g
    apply LinearMap.ext_ring
    change integerRegularLinearEquiv k q t ht
        (Representation.leftRegular k G (n : G) (MonoidAlgebra.single g 1)) =
      ((Representation.leftRegular k q.ker).finsupp ℤ) n
        (integerRegularLinearEquiv k q t ht (MonoidAlgebra.single g 1))
    simp only [Representation.ofMulAction_single, smul_eq_mul,
      integerRegularLinearEquiv_single, integerQuotientHeight_mul,
      integerQuotientHeight_kernel, zero_add, integerQuotientPart_kernel_mul,
      Representation.finsupp_single]

def integerRestrictedRegularIso :
    Rep.res q.ker.subtype (Rep.leftRegular k G) ≅ Rep.finsupp ℤ (Rep.leftRegular k q.ker) :=
  Rep.mkIso (integerRestrictedRegularEquiv k q t ht)

def kernelConjugationLinearEquiv : k[q.ker] ≃ₗ[k] k[q.ker] :=
  (MonoidAlgebra.domCongr k k (MulAut.conjNormal (H := q.ker) t)).toLinearEquiv

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_IntegerInducedTranslation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The induced translation is a shift with a cochain conjugation twist -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory Representation
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2
attribute [local instance 2000] Rep.instLinear
attribute [local instance 2100] Linear.homModule

variable (k : Type) [CommRing k] {G : Type} [Group G]
  (q : G →* Multiplicative ℤ) (t : G) (ht : q t = Multiplicative.ofAdd 1)

theorem inverse_conjugation_eq :
    (MulAut.conjNormal (H := q.ker) t⁻¹).symm = MulAut.conjNormal (H := q.ker) t := by
  change (MulAut.conjNormal (H := q.ker) t⁻¹)⁻¹ = _
  rw [map_inv, inv_inv]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NilpotentRationalConjugation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # Nilpotent conjugation has a dimension-bounded unipotence exponent

On an abelian normal subgroup, conjugation minus the identity is the
commutator map. Its successive powers lie in successive lower-central terms.
Rationalization therefore gives a nilpotent operator, whose exponent is
bounded by the rational rank rather than by a chosen group nilpotency class.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped IsMulCommutative TensorProduct commutatorElement

variable {G : Type} [Group G] (H : Subgroup G) [H.Normal] [IsMulCommutative H]

def integralConjugationDifference (g : G) : Module.End ℤ (Additive H) :=
  (MulAut.conjNormal (H := H) g).toAdditive.toIntLinearEquiv.toLinearMap - 1

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RelativeCommutatorSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Compatibility with OpenAI's Mathlib (d13f23b): one-sided `commutator_mono`. -/

namespace OAI

/-! # Iterated action commutators and a centralizer criterion -/

namespace PolycyclicRecognition

open scoped commutatorElement
variable {G : Type} [Group G]

def relativeCommutatorSeries (K N : Subgroup G) : ℕ → Subgroup G
  | 0 => N
  | n + 1 => ⁅K, relativeCommutatorSeries K N n⁆

instance relativeCommutatorSeries_normal (K N : Subgroup G) [K.Normal] [N.Normal] (n : ℕ) :
    (relativeCommutatorSeries K N n).Normal := by
  induction n with
  | zero => exact inferInstanceAs N.Normal
  | succ n ih =>
    let := ih
    exact inferInstanceAs (⁅K, relativeCommutatorSeries K N n⁆ : Subgroup G).Normal

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_EquivariantCommutatorFiltration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Linear control of iterated commutators in a normal subgroup

An equivariant homomorphism from a normal subgroup into an additive vector
space sends action commutators to action differences. Vanishing of the
linear action filtration therefore puts the relative commutator series in
the kernel of that homomorphism.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped commutatorElement
variable {G k V : Type} [Group G] [Field k] [AddCommGroup V] [Module k V]

def linearPreimageSubgroup {N : Subgroup G} (π : N →* Multiplicative V)
    (W : Submodule k V) : Subgroup N where
  carrier := {a | (π a).toAdd ∈ W}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    change (π (a * b)).toAdd ∈ W
    simpa only [map_mul, toAdd_mul] using W.add_mem ha hb
  inv_mem' := by
    intro a ha
    change (π a⁻¹).toAdd ∈ W
    simpa only [map_inv, toAdd_inv] using W.neg_mem ha

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_FiniteGroupProjectiveNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Norms on projective integral representations of finite groups

Every invariant vector in a free representation is a norm. Splitting the
normalized free cover extends this to projective representations. Consequently,
a scalar endomorphism of the trivial representation factors through a projective
representation exactly when the group order divides that scalar.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

theorem freeRepresentation_action_coeff {α : Type} (g : G)
    (x : α →₀ ℤ[G]) (a : α) (h : G) :
    (Representation.free ℤ G α g x a).coeff h = (x a).coeff (g⁻¹ * h) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, MonoidAlgebra.coeff_add, hx, hy]
  | single b z =>
    simp only [Representation.free, Representation.finsupp_single]
    by_cases hab : b = a
    · subst b
      simp [Representation.leftRegular, Representation.coeff_ofMulAction]
    · simp [hab]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_ProjectiveTensorCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Tensoring projectives by an integer-projective coefficient

The internal Hom is exact on epimorphisms when its first argument is
projective over the integers. The tensor–Hom adjunction then preserves
projective representations, with no finite-rank assumption.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits MonoidalCategory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

theorem representation_ihom_preserves_epimorphisms (A : Rep.{0} ℤ G)
    [Module.Projective ℤ A] : (ihom A).PreservesEpimorphisms where
  preserves {X Y} f hf := by
    apply (Rep.epi_iff_surjective _).mpr
    intro u
    change A →ₗ[ℤ] Y at u
    obtain ⟨v, hv⟩ := Module.projective_lifting_property f.hom.toLinearMap u
      ((Rep.epi_iff_surjective f).mp hf)
    exact ⟨v, hv⟩

theorem representation_tensor_projective (A P : Rep.{0} ℤ G)
    [Module.Projective ℤ A] [Projective P] : Projective (A ⊗ P) := by
  let := representation_ihom_preserves_epimorphisms A
  let := Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms
    (ihom.adjunction A)
  exact Functor.projective_obj (tensorLeft A) P

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ExactTensorCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact tensoring by the flat integral coefficient

This uses flatness of the underlying integer module; no equivariant splitting
is claimed for the constant-functions sequence.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits MonoidalCategory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2300] TensorProduct.instModule
variable {G : Type} [Group G]

theorem representation_tensorLeft_map_exact (A : Rep.{0} ℤ G) [Module.Flat ℤ A]
    (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.Exact) :
    (S.map (tensorLeft A)).Exact := by
  have hs := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
    (S.map (forget₂ (Rep ℤ G) (ModuleCat ℤ)))).mp
      (hS.map (forget₂ (Rep ℤ G) (ModuleCat ℤ)))
  have he := Module.Flat.lTensor_exact A (f := S.f.hom.toLinearMap)
    (g := S.g.hom.toLinearMap) hs
  apply (forget₂ (Rep ℤ G) (ModuleCat ℤ)).reflects_exact_of_faithful
  apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
  exact he

theorem representation_tensorLeft_preserves_homology (A : Rep.{0} ℤ G) [Module.Flat ℤ A] :
    (tensorLeft A).PreservesHomology :=
  Functor.preservesHomology_of_map_exact _ (representation_tensorLeft_map_exact A)

theorem representation_tensorLeft_map_shortExact (A : Rep.{0} ℤ G) [Module.Flat ℤ A]
    (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) :
    (S.map (tensorLeft A)).ShortExact := by
  let := representation_tensorLeft_preserves_homology A
  let := Functor.preservesMonomorphisms_of_map_exact (tensorLeft A)
    (representation_tensorLeft_map_exact A)
  let := Functor.preservesEpimorphisms_of_map_exact (tensorLeft A)
    (representation_tensorLeft_map_exact A)
  let := hS.mono_f
  let := hS.epi_g
  exact hS.map (tensorLeft A)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ExtensionSectionFactor
attribute [-instance] _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The normalized factor system of an actual group extension -/

noncomputable section
namespace PolycyclicRecognition
variable {N G Q : Type*} [Group N] [Group G] [Group Q]
open Classical

/-- A normalized section exists for every surjective group extension. -/
def normalizedExtensionSection (S : GroupExtension N G Q) : S.Section where
  toFun q := if q = 1 then 1 else S.surjInvRightHom q
  rightInverse_rightHom q := by
    dsimp only
    split_ifs with h
    · simp only [h, map_one]
    · exact S.surjInvRightHom.rightInverse_rightHom q

@[simp] theorem normalizedExtensionSection_one (S : GroupExtension N G Q) :
    normalizedExtensionSection S 1 = 1 := by
  simp [normalizedExtensionSection]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FiberAverageL2
attribute [-instance] _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Square-integrable averages over probability fibers

These estimates justify the whole-fiber averages in the inverse coupling.
The outer measure may be finite without being normalized.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace PolycyclicRecognition

variable {X Y W : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Normalize the restriction to a region of positive finite mass. -/
def normalizedRestriction (m : Measure Y) (B : Set Y) : Measure Y :=
  (m B)⁻¹ • m.restrict B

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FiniteGeneratedCharacterLog
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Logarithms of powers of finitely generated abelian characters

A finite-index free subgroup supplies a compatible choice on a basis.
The index-power map pulls that choice back to the whole group.
-/

noncomputable section
namespace PolycyclicRecognition

variable {G : Type} [CommGroup G]

def finiteIndexPowerHom (K : Subgroup G) : G →* K where
  toFun g := ⟨g ^ K.index, K.pow_index_mem g⟩
  map_one' := by apply Subtype.ext; exact one_pow _
  map_mul' g h := by apply Subtype.ext; exact mul_pow g h _

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FiniteGroupRelativeInjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Extending maps into projectives across integral split inclusions

For a finite group, a projective representation is injective with respect to
short exact sequences that split as sequences of abelian groups. The extension
uses the coefficient at the identity followed by the finite group sum.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G] [Fintype G]

def freeIdentityCoefficient (α : Type) : Module.End ℤ (Rep.free ℤ G α) :=
  Finsupp.mapRange.linearMap
    (MonoidAlgebra.lsingle 1 ∘ₗ Finsupp.lapply 1 ∘ₗ
      (MonoidAlgebra.coeffLinearEquiv ℤ).toLinearMap)

omit [Fintype G] in
@[simp]
theorem freeIdentityCoefficient_apply (α : Type) (x : Rep.free ℤ G α) (a : α) :
    freeIdentityCoefficient α x a = MonoidAlgebra.single 1 ((x a).coeff 1) := rfl

def freeAveragedLinearMap {α : Type} (B : Rep.{0} ℤ G)
    (l : B →ₗ[ℤ] Rep.free ℤ G α) : B →ₗ[ℤ] Rep.free ℤ G α :=
  ∑ g : G, (Rep.free ℤ G α).ρ g ∘ₗ freeIdentityCoefficient α ∘ₗ l ∘ₗ B.ρ g⁻¹

theorem freeAveragedLinearMap_coeff {α : Type} (B : Rep.{0} ℤ G)
    (l : B →ₗ[ℤ] Rep.free ℤ G α) (b : B) (a : α) (h : G) :
    (freeAveragedLinearMap B l b a).coeff h = (l (B.ρ h⁻¹ b) a).coeff 1 := by
  classical
  calc
    _ = ∑ g : G, (Representation.free ℤ G α g
        (freeIdentityCoefficient α (l (B.ρ g⁻¹ b))) a).coeff h := by
      simp [freeAveragedLinearMap]
    _ = ∑ g : G, (freeIdentityCoefficient α (l (B.ρ g⁻¹ b)) a).coeff (g⁻¹ * h) := by
      apply Finset.sum_congr rfl
      intro g _
      exact freeRepresentation_action_coeff g _ a h
    _ = _ := by simp [freeIdentityCoefficient, MonoidAlgebra.coeff_single, Finsupp.single_apply, eq_comm, inv_mul_eq_one]

def freeAveragedExtension {α : Type} (B : Rep.{0} ℤ G)
    (l : B →ₗ[ℤ] Rep.free ℤ G α) : B ⟶ Rep.free ℤ G α :=
  Rep.ofHom ⟨freeAveragedLinearMap B l, fun g => by
    apply LinearMap.ext
    intro b
    ext a h
    change (freeAveragedLinearMap B l (B.ρ g b) a).coeff h =
      (Representation.free ℤ G α g (freeAveragedLinearMap B l b) a).coeff h
    rw [freeAveragedLinearMap_coeff, freeRepresentation_action_coeff,
      freeAveragedLinearMap_coeff]
    congr 2
    simp only [mul_inv_rev, inv_inv, map_mul, Module.End.mul_apply]⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FiniteIndexTrace
attribute [-instance] _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The index in the induction/coinduction trace -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory Representation
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G] (H : Subgroup G) [H.FiniteIndex] (D : Rep.{0} ℤ G)

def finiteIndexLift : D ⟶ Rep.ind H.subtype (Rep.res H.subtype D) := by
  classical
  exact Rep.resCoindToHom H.subtype D (Rep.res H.subtype D) (𝟙 _) ≫
    (Rep.indCoindIso (Rep.res H.subtype D)).inv

def finiteIndexReturn : Rep.ind H.subtype (Rep.res H.subtype D) ⟶ D :=
  (Rep.indResHomEquiv H.subtype (Rep.res H.subtype D) D).symm (𝟙 _)

omit [H.FiniteIndex] in
@[simp] theorem finiteIndexReturn_mk (g : G) (a : D) :
    (finiteIndexReturn H D).hom
      (IndV.mk H.subtype (Rep.res H.subtype D).ρ g a) = D.ρ g⁻¹ a := by
  classical
  simp [finiteIndexReturn, Rep.indResHomEquiv]
  exact (Finsupp.sum_single_index (a := g) (b := (1 : ℤ))
    (h := fun i d => @SMul.smul ℤ D.V D.hV2.toSMul d (D.ρ i⁻¹ a))
    (D.hV2.zero_smul _)).trans (D.hV2.one_smul _)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FiniteInvariantOrbit
attribute [-instance] _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Selecting a label in a finite linear group

Embedding a vector in the Euclidean product of all its group translates
provides an invariant strictly convex norm without changing the topology or
norm instances on the original height space.
-/

noncomputable section

namespace PolycyclicRecognition

open Set

variable {W E : Type*} [AddCommGroup W] [Module ℝ W]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (Γ : Subgroup (W ≃ₗ[ℝ] W)) [Fintype Γ] (e : W →ₗ[ℝ] E)

/-- All group translates, recorded in a finite Euclidean product. -/
def finiteOrbitEmbedding : W →ₗ[ℝ] PiLp 2 (fun _ : Γ => E) :=
  (WithLp.linearEquiv 2 ℝ (Γ → E)).symm.toLinearMap.comp
    (LinearMap.pi (fun g : Γ => e.comp g.val.toLinearMap))

omit [Fintype Γ] in
@[simp] theorem finiteOrbitEmbedding_apply (w : W) (g : Γ) :
    finiteOrbitEmbedding Γ e w g = e (g.val w) := rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FiniteLinearSymmetries
attribute [-instance] _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finiteness of linear height symmetries

The finite-symmetry step used in Lemma `support-symmetries` reduces to
permuting a finite spanning collection of covectors. The elementary linear
algebra fact proved here applies equally to vectors in the dual height space.
It does not assume that the permutation of covectors determines a symmetry:
it proves uniqueness from the spanning hypothesis.
-/

namespace PolycyclicRecognition

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- There are only finitely many invertible continuous linear maps preserving
a fixed finite spanning collection of vectors. -/
theorem finite_linear_symmetries (s : Finset W)
    (hspan : Submodule.span ℝ (s : Set W) = ⊤) :
    Set.Finite {A : W ≃L[ℝ] W | ∀ w ∈ s, A w ∈ s} := by
  classical
  let Sym := {A : W ≃L[ℝ] W // ∀ w ∈ s, A w ∈ s}
  let restrict : Sym → (s → s) := fun A w => ⟨A.val w, A.property w w.property⟩
  have hinj : Function.Injective restrict := by
    intro A B hab
    apply Subtype.ext
    have heq : A.val.toLinearMap = B.val.toLinearMap := by
      apply LinearMap.ext_on hspan
      intro w hw
      exact congrArg Subtype.val (congrFun hab ⟨w, hw⟩)
    ext w
    exact congrArg (fun L : W →ₗ[ℝ] W => L w) heq
  have hfinite : Finite Sym := Finite.of_injective restrict hinj
  exact Set.finite_coe_iff.mp hfinite

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ThreeCongruenceMatrix
attribute [-instance] _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integral matrices congruent to the identity modulo three -/
noncomputable section
namespace PolycyclicRecognition
open Matrix
variable {I : Type} [Fintype I] [DecidableEq I]

def matrixMod (m : ℕ) : Matrix I I ℤ →+* Matrix I I (ZMod m) :=
  (Int.castRingHom (ZMod m)).mapMatrix

@[simp] theorem matrixMod_apply (m : ℕ) (A : Matrix I I ℤ) (i j : I) :
    matrixMod m A i j = (A i j : ZMod m) := rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FiniteRationalRepresentation
attribute [-instance] _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A uniform bound for finite faithful rational representations

The integral lattice is the span of the finite orbit of a rational basis.
Reduction modulo three then bounds the group order.
-/
noncomputable section
namespace PolycyclicRecognition
open Module
variable {G V I : Type} [Group G] [Finite G]
  [AddCommGroup V] [Module ℚ V] [Fintype I]

def finiteOrbitIntegerLattice (ρ : G →* Module.End ℚ V) (b : Basis I ℚ V) :
    Submodule ℤ V := Submodule.span ℤ (Set.range fun p : G × I => ρ p.1 (b p.2))

omit [Finite G] [Fintype I] in
theorem finiteOrbitIntegerLattice_stable (ρ : G →* Module.End ℚ V)
    (b : Basis I ℚ V) (g : G) {v : V} (hv : v ∈ finiteOrbitIntegerLattice ρ b) :
    ρ g v ∈ finiteOrbitIntegerLattice ρ b := by
  let f := (ρ g).restrictScalars ℤ
  change f v ∈ finiteOrbitIntegerLattice ρ b
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨⟨h, i⟩, rfl⟩ := hv
    apply Submodule.subset_span
    refine ⟨(g * h, i), ?_⟩
    simp [f, map_mul, Module.End.mul_apply]
  | zero => simp
  | add x y _ _ hx hy => simpa only [map_add] using (finiteOrbitIntegerLattice ρ b).add_mem hx hy
  | smul a x _ hx => simpa only [map_smul] using (finiteOrbitIntegerLattice ρ b).smul_mem a hx

def finiteOrbitIntegerRepresentation (ρ : G →* Module.End ℚ V) (b : Basis I ℚ V) :
    G →* Module.End ℤ (finiteOrbitIntegerLattice ρ b) where
  toFun g :=
    { toFun v := ⟨ρ g v, finiteOrbitIntegerLattice_stable ρ b g v.property⟩
      map_add' x y := Subtype.ext (map_add (ρ g) (x : V) (y : V))
      map_smul' a v := Subtype.ext ((ρ g).restrictScalars ℤ |>.map_smul a (v : V)) }
  map_one' := by ext v; exact congrArg (fun f : Module.End ℚ V => f v) ρ.map_one
  map_mul' g h := by ext v; exact congrArg (fun f : Module.End ℚ V => f v) (ρ.map_mul g h)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_GradedGeneratorLimit
attribute [-instance] _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Generating vectors and group laws survive the graded limit -/

noncomputable section

namespace PolycyclicRecognition

open Module LieModule Filter
open scoped Topology

variable {L I : Type*} [LieRing L] [LieAlgebra ℝ L] [Fintype I] [DecidableEq I]

/-- The part of a vector whose coordinate degree equals the prescribed
generator degree. -/
def gradedGenerator {n : ℕ} (b : Basis (Fin n) ℝ L) (cost : Fin n → ℝ)
    (s : ℝ) (x : L) : Fin n → ℝ :=
  fun j => if s = cost j then b.repr x j else 0

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_GradedHorizontalStructure
attribute [-instance] _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The horizontal projection and conjugation law of the graded limit -/

noncomputable section
namespace PolycyclicRecognition

open Module Filter
open scoped Topology BigOperators

/-- The degree-one part of exponential coordinates is linear in the
original horizontal vector. -/
def gradedGeneratorLinearMap
    {L : Type*} [LieRing L] [LieAlgebra ℝ L] {n : ℕ}
    (b : Basis (Fin n) ℝ L) (cost : Fin n → ℝ) (s : ℝ) :
    L →ₗ[ℝ] (Fin n → ℝ) where
  toFun := gradedGenerator b cost s
  map_add' := by
    intro x y
    ext j
    by_cases hj : s = cost j <;> simp [gradedGenerator, hj]
  map_smul' := by
    intro c x
    ext j
    by_cases hj : s = cost j <;> simp [gradedGenerator, hj]

def gradedGeneratorMap
    {L : Type*} [LieRing L] [LieAlgebra ℝ L] [TopologicalSpace L]
    [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L] [FiniteDimensional ℝ L] {n : ℕ}
    (b : Basis (Fin n) ℝ L) (cost : Fin n → ℝ) (s : ℝ) :
    L →L[ℝ] (Fin n → ℝ) :=
  (gradedGeneratorLinearMap b cost s).toContinuousLinearMap

@[simp] theorem gradedGeneratorMap_apply
    {L : Type*} [LieRing L] [LieAlgebra ℝ L] [TopologicalSpace L]
    [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L] [FiniteDimensional ℝ L] {n : ℕ}
    (b : Basis (Fin n) ℝ L) (cost : Fin n → ℝ) (s : ℝ) (v : L) :
    gradedGeneratorMap b cost s v = gradedGenerator b cost s v := rfl

attribute [local instance 100] LieRing.ofAssociativeRing

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_GroupAveragedRepresentative
attribute [-instance] _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exactly invariant representatives from group averaging

A probability equivalent to Haar measure is quasi-preserved by every right
translation. On the invariant measurable set where an orbit function is
essentially constant, its group integral is that constant. Assigning zero on
the complement gives a measurable, everywhere invariant representative.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory MeasureTheory.Measure Set Filter

variable {G X : Type*} [Group G] [MeasurableSpace G] [MeasurableSpace X]
  [MulAction G X] (η : Measure G) [IsProbabilityMeasure η]

def groupAverage (f : X → ℝ) (x : X) : ℝ := ∫ g, f (g • x) ∂η

def groupAverageGood (f : X → ℝ) : Set X :=
  {x | ∀ᵐ g ∂η, f (g • x) = groupAverage η f x}

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_IntegralRepresentationMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The group-ring linear map of an integral representation morphism -/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2
variable {G : Type} [Group G] {A B C : Rep.{0} ℤ G}

def integralRepresentationMap (f : A ⟶ B) : A.ρ.asModule →ₗ[ℤ[G]] B.ρ.asModule :=
  Representation.IntertwiningMap.equivLinearMapAsModule A.ρ B.ρ f.hom

@[simp] theorem integralRepresentationMap_apply (f : A ⟶ B) (a : A) :
    integralRepresentationMap f (A.ρ.asModuleEquiv.symm a) =
      B.ρ.asModuleEquiv.symm (f.hom a) := rfl

@[simp] theorem integralRepresentationMap_comp (f : A ⟶ B) (g : B ⟶ C) :
    integralRepresentationMap (f ≫ g) =
      (integralRepresentationMap g).comp (integralRepresentationMap f) := rfl

@[simp] theorem integralRepresentationMap_zero :
    integralRepresentationMap (0 : A ⟶ B) = 0 := rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_GroupFiniteGenerationFromFP
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # FP one implies finite generation

The finite supports of augmentation-kernel generators generate the group.
Projection to the permutation module on their left cosets proves this directly.
-/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2

variable {G : Type} [Group G]

def integralCosetProjection (K : Subgroup G) :
    Rep.leftRegular ℤ G ⟶ Rep.ofMulAction ℤ G (G ⧸ K) :=
  Rep.leftRegularHom _ (MonoidAlgebra.single (QuotientGroup.mk 1) 1)

@[simp] theorem integralCosetProjection_single (K : Subgroup G) (g : G) (r : ℤ) :
    (integralCosetProjection K).hom (MonoidAlgebra.single g r) =
      MonoidAlgebra.single (QuotientGroup.mk g) r := by
  simp [integralCosetProjection,
    Representation.ofMulAction_single, smul_eq_mul]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_HilbertOrbitAverage
attribute [-instance] _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Hilbert averaging over a group orbit

The closed convex hull of a unitary orbit has a fixed vector of minimal norm.
This requires no invariant mean on the acting group. It supplies the averaging
step in the construction of ergodic conditional component measures.
-/

noncomputable section

namespace PolycyclicRecognition

open Set

variable {G E : Type*} [Group G] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E)

/-- The closed convex hull of the actual orbit. -/
def hilbertOrbitHull : Set E := closure (convexHull ℝ (range (fun g => ρ g x)))

variable [CompleteSpace E]

section IsometricAction

variable [DistribMulAction G E] [SMulCommClass G ℝ E] [IsIsometricSMul G E]

/-- The bundled unitary representation of a real linear isometric action. -/
def isometricLinearAction : G →* (E ≃ₗᵢ[ℝ] E) where
  toFun g :=
    { DistribMulAction.toLinearEquiv ℝ E g with
      norm_map' := fun v => by
        change ‖g • v‖ = ‖v‖
        have h := (isometry_smul E g).dist_eq v 0
        simpa only [smul_zero, dist_zero_right] using h }
  map_one' := by ext v; exact one_smul G v
  map_mul' g h := by ext v; exact mul_smul g h v

end IsometricAction

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SubgroupInductionExact
attribute [-instance] _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact induction from arbitrary subgroups -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits Representation
open scoped MonoidAlgebra TensorProduct
attribute [local instance 2000] Rep.hV2
variable (k : Type) [CommRing k] {G : Type} [Group G] (N : Subgroup G)

@[simp] theorem subgroupInductionMap_mk {A B : Rep k N} (f : A ⟶ B) (g : G) (a : A) :
    (Rep.indMap N.subtype f).hom (IndV.mk N.subtype A.ρ g a) =
      IndV.mk N.subtype B.ρ g (f.hom a) := by
  simp [Rep.indMap, IndV.mk]

instance subgroupInduction_preservesProjectives :
    (Rep.indFunctor k N.subtype).PreservesProjectiveObjects :=
  Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms
    (Rep.indResAdjunction k N.subtype)

instance subgroupInduction_additive : (Rep.indFunctor k N.subtype).Additive where
  map_add {A B} f h := by
    apply Rep.hom_ext
    apply IntertwiningMap.ext
    apply IndV.hom_ext
    intro g
    apply LinearMap.ext
    intro a
    simp [Rep.indMap, IndV.mk, Rep.add_hom]


end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_InductionAmbientQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A common ambient representation for subgroup induction

All the induced restrictions of a fixed coefficient are quotients of the same
module. The relations increase with the subgroup. The commuting right action
on the group-ring factor gives the actual ambient group action.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits Representation
open scoped MonoidAlgebra TensorProduct
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2300] TensorProduct.instModule
variable {G : Type} [Group G] (A : Rep.{0} ℤ G)

def inductionAmbientAction : Representation ℤ G (ℤ[G] ⊗[ℤ] A) where
  toFun g := (MonoidAlgebra.mapDomainLinearMap ℤ ℤ (fun x : G => x * g⁻¹)).rTensor A
  map_one' := by ext; simp
  map_mul' g h := by ext; simp [mul_inv_rev, mul_assoc]

abbrev inductionAmbient : Rep ℤ G := Rep.of (inductionAmbientAction A)

abbrev inductionDiagonalAction : Representation ℤ G (ℤ[G] ⊗[ℤ] A) :=
  Representation.tprod (Representation.leftRegular ℤ G) A.ρ

theorem inductionAmbient_diagonal_commute (g h : G) :
    (inductionAmbientAction A g).comp (inductionDiagonalAction A h) =
      (inductionDiagonalAction A h).comp (inductionAmbientAction A g) := by
  ext x a
  simp [inductionAmbientAction, inductionDiagonalAction, mul_assoc]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_SubgroupBarResolution
attribute [-instance] _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
attribute [-simp] _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Subgroup inclusions on the free bar resolution -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory Rep Finsupp
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G] (H : Subgroup G)

def subgroupFreeInclusion (n : ℕ) :
    Rep.free ℤ H (Fin n → H) ⟶ Rep.res H.subtype (Rep.free ℤ G (Fin n → G)) :=
  Rep.freeLift ℤ H _ (fun x => Finsupp.single (H.subtype ∘ x) (MonoidAlgebra.single 1 1))

theorem subgroupFreeInclusion_single (n : ℕ) (x : Fin n → H) (h : H) (r : ℤ) :
    (subgroupFreeInclusion H n).hom (Finsupp.single x (MonoidAlgebra.single h r)) =
      Finsupp.single (H.subtype ∘ x) (MonoidAlgebra.single (h : G) r) := by
  change Representation.freeLift
    (Rep.res H.subtype (Rep.free ℤ G (Fin n → G))).ρ
    (fun y : Fin n → H => Finsupp.single (H.subtype ∘ y) (MonoidAlgebra.single 1 1))
    (Finsupp.single x (MonoidAlgebra.single h r)) = _
  rw [Representation.freeLift_single_single]
  change r • Representation.free ℤ G (Fin n → G) (h : G)
      (Finsupp.single (H.subtype ∘ x) (MonoidAlgebra.single 1 1)) = _
  rw [Representation.free_single_single, mul_one]
  simp

theorem subgroupFreeInclusion_d (n : ℕ) :
    subgroupFreeInclusion H (n + 1) ≫ (Rep.resFunctor H.subtype).map (Rep.barComplex.d ℤ G n) =
      Rep.barComplex.d ℤ H n ≫ subgroupFreeInclusion H n := by
  apply Rep.free_ext
  intro x
  change (Rep.barComplex.d ℤ G n).hom
      ((subgroupFreeInclusion H (n + 1)).hom (Finsupp.single x (MonoidAlgebra.single 1 1))) =
    (subgroupFreeInclusion H n).hom
      ((Rep.barComplex.d ℤ H n).hom (Finsupp.single x (MonoidAlgebra.single 1 1)))
  rw [subgroupFreeInclusion_single, Subgroup.coe_one, Rep.barComplex.d_single,
    Rep.barComplex.d_single, map_add, map_sum, subgroupFreeInclusion_single]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [subgroupFreeInclusion_single, Subgroup.coe_one]
  congr 1
  exact (Fin.comp_contractNth (· * ·) (· * ·) (f := H.subtype)
    (fun _ _ => rfl) j x).symm

def subgroupBarResolutionMap : Rep.barComplex ℤ H ⟶
    ((Rep.resFunctor H.subtype).mapProjectiveResolution (Rep.barResolution ℤ G)).complex :=
  ChainComplex.ofHom (subgroupFreeInclusion H) (fun n => by
    change subgroupFreeInclusion H (n + 1) ≫
        (Rep.resFunctor H.subtype).map ((Rep.barComplex ℤ G).d (n + 1) n) =
      (Rep.barComplex ℤ H).d (n + 1) n ≫ subgroupFreeInclusion H n
    simpa only [ChainComplex.of_d] using subgroupFreeInclusion_d H n)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_InnerBarTranslation
attribute [-instance] _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
attribute [-simp] _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An augmented bar-resolution lift of inner conjugation -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory Rep Finsupp
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]


def innerBarFreeMap (a : G) (n : ℕ) :
    Rep.free ℤ G (Fin n → G) ⟶ Rep.free ℤ G (Fin n → G) :=
  Rep.freeLift ℤ G _ (fun x =>
    Finsupp.single ((MulAut.conj a) ∘ x) (MonoidAlgebra.single a⁻¹ 1))

theorem innerBarFreeMap_single (a : G) (n : ℕ) (x : Fin n → G) (h : G) (r : ℤ) :
    (innerBarFreeMap a n).hom (Finsupp.single x (MonoidAlgebra.single h r)) =
      Finsupp.single ((MulAut.conj a) ∘ x) (MonoidAlgebra.single (h * a⁻¹) r) := by
  change Representation.freeLift (Representation.free ℤ G (Fin n → G))
    (fun x => Finsupp.single ((MulAut.conj a) ∘ x) (MonoidAlgebra.single a⁻¹ 1))
      (Finsupp.single x (MonoidAlgebra.single h r)) = _
  rw [Representation.freeLift_single_single, Representation.free_single_single]
  simp

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_InvariantFactor
attribute [-instance] _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conditioning on all invariant measurable sets

The factor retains the original points but equips them with the sigma algebra
of invariant sets. Its conditional kernel is pointwise constant on every orbit
and has the original probability as its barycenter.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory ProbabilityTheory Set

variable (G X : Type*) [Group G] [mX : MeasurableSpace X] [MulAction G X]

/-- The sigma algebra of measurable sets invariant under the entire action. -/
@[instance_reducible]
def invariantSigma : MeasurableSpace X :=
  ⨅ g : G, MeasurableSpace.invariants (g • ·)

theorem invariantSigma_le : invariantSigma G X ≤ ‹MeasurableSpace X› :=
  (iInf_le _ (1 : G)).trans (MeasurableSpace.invariants_le _)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_InvariantSubspaceDeterminant
attribute [-instance] _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Determinants of scalar commutators on an invariant subspace

Restricting an action to a genuinely invariant subspace gives an action
by linear equivalences. Its commutators have determinant one, so a scalar
commutator has scalar a root of unity of degree the subspace dimension.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped commutatorElement
variable {G K V : Type*} [Group G] [Field K] [AddCommGroup V] [Module K V]

def invariantSubspaceAction (ρ : G →* (V ≃ₗ[K] V)) (W : Submodule K V)
    (hW : ∀ g : G, ∀ v ∈ W, ρ g v ∈ W) : G →* (W ≃ₗ[K] W) where
  toFun g :=
    { (ρ g).toLinearMap.restrict (hW g) with
      invFun := fun v => ⟨ρ g⁻¹ v, hW g⁻¹ v v.property⟩
      left_inv := by
        intro v
        apply Subtype.ext
        change ρ g⁻¹ (ρ g v) = v
        rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
        rfl
      right_inv := by
        intro v
        apply Subtype.ext
        change ρ g (ρ g⁻¹ v) = v
        rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
        rfl }
  map_one' := by
    ext v
    change ρ 1 v = v
    rw [map_one]
    rfl
  map_mul' g h := by
    ext v
    change ρ (g * h) v = ρ g (ρ h v)
    rw [map_mul]
    rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_LeftTangentTrivialization
attribute [-instance] _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Left translation identifies the tangent fibers

The differential of translation back to the identity is an actual continuous
linear equivalence. Its matrix in any fixed local tangent chart varies
smoothly. These facts supply the frame for the left-invariant metric.
-/

noncomputable section
namespace PolycyclicRecognition

open Bundle Function
open scoped Manifold ContDiff

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ∞ G]

def leftTranslateDerivative (g : G) : E →L[ℝ] E :=
  mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun h : G => g * h) 1

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_LinearInvariantInverse
attribute [-instance] _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Inverting a finite-dimensional map preserves its invariant subspaces -/

namespace PolycyclicRecognition

theorem inverse_mem_of_preserves_submodule
    {L : Type*} [AddCommGroup L] [Module ℝ L] [FiniteDimensional ℝ L]
    (e : L ≃ₗ[ℝ] L) (V : Submodule ℝ L)
    (he : ∀ x ∈ V, e x ∈ V) {x : L} (hx : x ∈ V) : e.symm x ∈ V := by
  let f : V →ₗ[ℝ] V :=
    { toFun := fun v => ⟨e v, he v v.property⟩
      map_add' := fun a b => Subtype.ext (e.map_add a b)
      map_smul' := fun r a => Subtype.ext (e.map_smul r a) }
  have hi : Function.Injective f := by
    intro a b h
    exact Subtype.ext (e.injective (congrArg Subtype.val h))
  obtain ⟨y, hy⟩ := (LinearMap.injective_iff_surjective.mp hi) ⟨x, hx⟩
  have heq : e (y : L) = x := congrArg Subtype.val hy
  rw [← heq, e.symm_apply_apply]
  exact y.property

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_IntegralKernelRepresentation
attribute [-instance] _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives
attribute [-simp] _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The categorical kernel and its concrete group-ring module -/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2
attribute [local instance 3000] Submodule.module
variable {G : Type} [Group G] {A B C : Rep.{0} ℤ G}

abbrev integralKernelObject (f : A ⟶ B) : Rep ℤ G := by
  letI : Module ℤ f.hom.ker.toSubmodule := f.hom.ker.toSubmodule.module
  exact Rep.of f.hom.ker.toRepresentation

def integralKernelInclusion (f : A ⟶ B) : integralKernelObject f ⟶ A :=
  Rep.ofHom ⟨f.hom.ker.toSubmodule.subtype, fun _ => rfl⟩

@[simp] theorem integralKernelInclusion_apply (f : A ⟶ B) (a : integralKernelObject f) :
    (integralKernelInclusion f).hom a = a.val := rfl

instance integralKernelInclusion_mono (f : A ⟶ B) : Mono (integralKernelInclusion f) :=
  (Rep.mono_iff_injective _).mpr Subtype.val_injective

@[simp] theorem integralKernelInclusion_comp (f : A ⟶ B) :
    integralKernelInclusion f ≫ f = 0 := by
  ext a
  exact a.property

def integralKernelLift (f : A ⟶ B) (g : C ⟶ A) (hg : g ≫ f = 0) :
    C ⟶ integralKernelObject f :=
  Rep.ofHom ⟨g.hom.toLinearMap.codRestrict f.hom.ker.toSubmodule (fun a => by
    exact congrArg (fun q => q.hom a) hg), fun s => by
      ext a
      exact Rep.hom_comm_apply g s a⟩

@[simp] theorem integralKernelLift_comp (f : A ⟶ B) (g : C ⟶ A) (hg : g ≫ f = 0) :
    integralKernelLift f g hg ≫ integralKernelInclusion f = g := by
  ext
  rfl

def integralKernelIsLimit (f : A ⟶ B) :
    IsLimit (KernelFork.ofι (integralKernelInclusion f) (integralKernelInclusion_comp f)) :=
  KernelFork.IsLimit.ofι' _ _ (fun g hg =>
    ⟨integralKernelLift f g hg, integralKernelLift_comp f g hg⟩)

def integralKernelIso (f : A ⟶ B) : integralKernelObject f ≅ kernel f :=
  (limit.isoLimitCone ⟨_, integralKernelIsLimit f⟩).symm

def integralKernelModuleEquiv (f : A ⟶ B) :
    (integralKernelObject f).ρ.asModule ≃ₗ[ℤ[G]] LinearMap.ker (integralRepresentationMap f) :=
  LinearEquiv.ofBijective
    ((integralRepresentationMap (integralKernelInclusion f)).codRestrict _ (fun a => a.property))
    ⟨fun _a _b h => Subtype.ext (congrArg Subtype.val h), fun a => ⟨⟨a.val, a.property⟩, rfl⟩⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NilpotentQuotientRank
attribute [-instance] _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # Uniform rank bounds persist in nilpotent quotients

The inverse image of a subgroup need not be finitely generated. For the
generator bound we lift only a finite generating set. The abelian rank bound
uses the full inverse image and needs no finite-generation assumption.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped IsMulCommutative
variable {G Q : Type} [Group G] [Group.IsNilpotent G] [Group Q]

def quotientSubgroupMap (q : G →* Q) (K : Subgroup Q) : K.comap q →* K where
  toFun g := ⟨q g, g.property⟩
  map_one' := Subtype.ext q.map_one
  map_mul' x y := Subtype.ext (q.map_mul x y)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_BarChainExhaustion
attribute [-instance] _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite support in bar chains along a subgroup exhaustion

Every bar chain has a representative in one member of an increasing exhaustive
sequence of subgroups. The inclusion is injective in every degree.
-/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
variable {G : Type} [Group G]

def subgroupBarInclusion (H : Subgroup G) (A : Rep ℤ G) :
    groupHomology.inhomogeneousChains (Rep.res H.subtype A) ⟶
      groupHomology.inhomogeneousChains A :=
  groupHomology.chainsMap H.subtype (𝟙 (Rep.res H.subtype A))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_CochainExhaustion
attribute [-instance] _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cochains on an increasing exhaustive sequence of subgroups -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
variable {G : Type} [Group G]

def subgroupCochainRestriction (H : Subgroup G) (A : Rep ℤ G) :
    groupCohomology.inhomogeneousCochains A ⟶
      groupCohomology.inhomogeneousCochains (Rep.res H.subtype A) :=
  groupCohomology.cochainsMap H.subtype (𝟙 (Rep.res H.subtype A))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_CountableUnionCohomology
attribute [-instance] _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cohomology above a uniform dimension bound on an exhaustive sequence

Two consecutive local vanishings suffice. The primitive-correction argument
accounts for the one extra dimension in a countable increasing union.
-/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear

variable {G : Type} [Group G]

def subgroupCochainStep {H K : Subgroup G} (hHK : H ≤ K) (A : Rep ℤ G) :
    groupCohomology.inhomogeneousCochains (Rep.res K.subtype A) ⟶
      groupCohomology.inhomogeneousCochains (Rep.res H.subtype A) :=
  groupCohomology.cochainsMap (Subgroup.inclusion hHK)
    (Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_TrivialTensorChains
attribute [-instance] _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Tensoring group chains with a trivial coefficient module -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory MonoidalCategory
open scoped TensorProduct
attribute [local instance 2000] Rep.hV2

variable {k G : Type} [CommRing k] [Group G] (V : ModuleCat k) (A : Rep k G)

def trivialTensorCoefficient : Rep k G := Rep.trivial k G V ⊗ A

theorem trivialTensorCoefficient_tmul (g : G) (v : V) (a : A) :
    (trivialTensorCoefficient V A).ρ g (v ⊗ₜ[k] a) = v ⊗ₜ[k] A.ρ g a := by
  change TensorProduct.map (LinearMap.id : V →ₗ[k] V) (A.ρ g) (v ⊗ₜ[k] a) = _
  rw [TensorProduct.map_tmul, LinearMap.id_apply]

def trivialTensorChainsIso [DecidableEq G] :
    ((tensorLeft V).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (groupHomology.inhomogeneousChains A) ≅
      groupHomology.inhomogeneousChains (trivialTensorCoefficient V A) := by
  refine HomologicalComplex.Hom.isoOfComponents
    (fun i => (TensorProduct.finsuppRight k k V A.V (Fin i → G)).toModuleIso) ?_
  rintro i j rfl
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  apply LinearMap.ext
  intro v
  apply Finsupp.lhom_ext'
  intro x
  apply LinearMap.ext
  intro a
  change (groupHomology.inhomogeneousChains (trivialTensorCoefficient V A)).d (j + 1) j
      (TensorProduct.finsuppRight k k V A.V (Fin (j + 1) → G)
        (v ⊗ₜ[k] Finsupp.single x a)) =
    TensorProduct.finsuppRight k k V A.V (Fin j → G)
      (TensorProduct.map (LinearMap.id : V →ₗ[k] V)
        ((groupHomology.inhomogeneousChains A).d (j + 1) j).hom
        (v ⊗ₜ[k] Finsupp.single x a))
  rw [groupHomology.inhomogeneousChains.d_def, groupHomology.inhomogeneousChains.d_def,
    TensorProduct.finsuppRight_tmul_single, TensorProduct.map_tmul, LinearMap.id_apply]
  erw [groupHomology.inhomogeneousChains.d_single,
    groupHomology.inhomogeneousChains.d_single, trivialTensorCoefficient_tmul]
  simp only [TensorProduct.tmul_add, TensorProduct.tmul_sum, map_add, map_sum,
    TensorProduct.finsuppRight_tmul_single]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  rw [TensorProduct.tmul_smul, map_smul, TensorProduct.finsuppRight_tmul_single]
  rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_RationalTensorHomology
attribute [-instance] _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rational tensoring commutes with the homology used here -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory MonoidalCategory

def rationalChainHomologyIso (C : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) :
    (((tensorLeft (ModuleCat.of ℤ ℚ)).mapHomologicalComplex (ComplexShape.down ℕ)).obj C).homology n ≅
      (tensorLeft (ModuleCat.of ℤ ℚ)).obj (C.homology n) :=
  (C.sc n).mapHomologyIso (tensorLeft (ModuleCat.of ℤ ℚ))

def rationalTensorHomologyIso {G : Type} [Group G] [DecidableEq G]
    (A : Rep ℤ G) (n : ℕ) :
    groupHomology (trivialTensorCoefficient (ModuleCat.of ℤ ℚ) A) n ≅
      (tensorLeft (ModuleCat.of ℤ ℚ)).obj (groupHomology A n) :=
  (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n).mapIso
      (trivialTensorChainsIso (ModuleCat.of ℤ ℚ) A).symm ≪≫
    rationalChainHomologyIso (groupHomology.inhomogeneousChains A) n

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RationalModuleFunctor
attribute [-instance] _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rationalization as a functor to rational modules

The codomain remembers the rational scalar action. Flatness proves exactness;
it does not assert a finite-dimensionality conclusion.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
open scoped TensorProduct
attribute [local instance 2000] ModuleCat.isModule
attribute [local instance 2300] TensorProduct.instModule

def rationalModuleFunctor : ModuleCat.{0} ℤ ⥤ ModuleCat.{0} ℚ where
  obj M := ModuleCat.of ℚ (ℚ ⊗[ℤ] M)
  map f := ModuleCat.ofHom (f.hom.baseChange ℚ)
  map_id M := by
    apply ModuleCat.hom_ext
    exact LinearMap.baseChange_id
  map_comp f g := by
    apply ModuleCat.hom_ext
    exact LinearMap.baseChange_comp f.hom g.hom

instance instAdditiveModuleCatIntRatRationalModuleFunctor : rationalModuleFunctor.Additive where
  map_add := by
    intro A B f g
    apply ModuleCat.hom_ext
    exact LinearMap.baseChange_add f.hom g.hom

theorem rationalModuleFunctor_map_exact (S : ShortComplex (ModuleCat.{0} ℤ))
    (hS : S.Exact) : (S.map rationalModuleFunctor).Exact := by
  have hs := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS
  have he := Module.Flat.lTensor_exact ℚ (f := S.f.hom) (g := S.g.hom) hs
  apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
  change Function.Exact (S.f.hom.baseChange ℚ) (S.g.hom.baseChange ℚ)
  exact he

instance instPreservesHomologyModuleCatIntRatRationalModuleFunctor : rationalModuleFunctor.PreservesHomology :=
  Functor.preservesHomology_of_map_exact _ rationalModuleFunctor_map_exact

def rationalModuleHomologyIso (C : ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ) :
    (((rationalModuleFunctor.mapHomologicalComplex (ComplexShape.down ℕ)).obj C).homology n) ≅
      ModuleCat.of ℚ (ℚ ⊗[ℤ] C.homology n) :=
  (C.sc n).mapHomologyIso rationalModuleFunctor

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RationalRepresentationFunctor
attribute [-instance] _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rationalization and restriction of scalars for group representations

The tensor extension is exact and left adjoint to scalar restriction. Thus it
preserves the projectives used in the finite rational-coefficient resolution.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2300] TensorProduct.instModule
variable {G : Type} [Group G]

def rationalizeRepresentation (A : Rep.{0} ℤ G) : Rep ℚ G :=
  Rep.of {
    toFun g := (A.ρ g).baseChange ℚ
    map_one' := by
      apply TensorProduct.AlgebraTensorModule.ext
      intro q a
      change q ⊗ₜ[ℤ] A.ρ 1 a = q ⊗ₜ[ℤ] a
      rw [map_one]
      rfl
    map_mul' g h := by
      apply TensorProduct.AlgebraTensorModule.ext
      intro q a
      change q ⊗ₜ[ℤ] A.ρ (g * h) a = q ⊗ₜ[ℤ] A.ρ g (A.ρ h a)
      rw [map_mul]
      rfl }

def rationalizeRepresentationMap {A B : Rep.{0} ℤ G} (f : A ⟶ B) :
    rationalizeRepresentation A ⟶ rationalizeRepresentation B :=
  Rep.ofHom ⟨f.hom.toLinearMap.baseChange ℚ, fun g => by
    apply TensorProduct.AlgebraTensorModule.ext
    intro q a
    change q ⊗ₜ[ℤ] f.hom (A.ρ g a) = q ⊗ₜ[ℤ] B.ρ g (f.hom a)
    rw [Rep.hom_comm_apply]⟩

def rationalizeRepresentationFunctor : Rep.{0} ℤ G ⥤ Rep.{0} ℚ G where
  obj := rationalizeRepresentation
  map := rationalizeRepresentationMap
  map_id A := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    exact LinearMap.baseChange_id
  map_comp f g := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    exact LinearMap.baseChange_comp f.hom.toLinearMap g.hom.toLinearMap

instance instAdditiveRepIntRatRationalizeRepresentationFunctor : (rationalizeRepresentationFunctor (G := G)).Additive where
  map_add := by
    intro A B f g
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    exact LinearMap.baseChange_add f.hom.toLinearMap g.hom.toLinearMap

def integralRestrictionRepresentation (A : Rep.{0} ℚ G) : Rep ℤ G :=
  Rep.of {
    toFun g := (A.ρ g).restrictScalars ℤ
    map_one' := by ext x; change A.ρ 1 x = x; rw [map_one]; rfl
    map_mul' g h := by ext x; change A.ρ (g * h) x = A.ρ g (A.ρ h x); rw [map_mul]; rfl }

def integralRestrictionMap {A B : Rep.{0} ℚ G} (f : A ⟶ B) :
    integralRestrictionRepresentation A ⟶ integralRestrictionRepresentation B :=
  Rep.ofHom ⟨f.hom.toLinearMap.restrictScalars ℤ, fun g => by
    apply LinearMap.ext
    exact Rep.hom_comm_apply f g⟩

def integralRestrictionFunctor : Rep.{0} ℚ G ⥤ Rep.{0} ℤ G where
  obj := integralRestrictionRepresentation
  map := integralRestrictionMap
  map_id _ := rfl
  map_comp _ _ := rfl

instance instPreservesEpimorphismsRepRatIntIntegralRestrictionFunctor : (integralRestrictionFunctor (G := G)).PreservesEpimorphisms where
  preserves f hf := (Rep.epi_iff_surjective _).mpr ((Rep.epi_iff_surjective f).mp hf)

local instance instModuleRatVIntIntegralRestrictionRepresentation (B : Rep.{0} ℚ G) : Module ℚ (integralRestrictionRepresentation B) := B.hV2

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RankOneRepresentation
attribute [-instance] _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Nonzero maps determine rank-one integral representations -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule

theorem integralEnd_apply (f : ℤ →ₗ[ℤ] ℤ) (x : ℤ) : f x = x * f 1 := by
  simpa only [smul_eq_mul, mul_one] using f.map_smul x (1 : ℤ)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RankOneEndomorphisms
attribute [-instance] _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integral endomorphisms of a rank-one representation -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G] (D : Rep ℤ G) (e : D.V ≃ₗ[ℤ] ℤ)

def rankOneEndomorphismsEquiv : (D ⟶ D) ≃ₗ[ℤ] ℤ := by
  let a : (D ⟶ D) ≃+ ℤ := {
    toFun := fun f => e (f.hom (e.symm 1))
    invFun := fun z => z • (𝟙 D : D ⟶ D)
    left_inv := fun f => by
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      ext x
      apply e.injective
      have hf := integralEnd_apply (e.conj f.hom.toLinearMap) (e x)
      change e (e (f.hom (e.symm 1)) • x) = e (f.hom x)
      rw [map_zsmul]
      change e (f.hom.toLinearMap (e.symm 1)) * e x = e (f.hom.toLinearMap x)
      simpa only [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply,
        mul_comm] using hf.symm
    right_inv := fun z => by
      change e (z • e.symm 1) = z
      rw [map_zsmul, LinearEquiv.apply_symm_apply]
      exact mul_one z
    map_add' := fun f g => e.map_add _ _ }
  exact { a with map_smul' := fun r x => map_intCast_smul a ℤ ℤ r x }

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_DimensionFromRegularCohomology
attribute [-instance] _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The regular module detects finite cohomological dimension

For a finite resolution, vanishing with regular coefficients implies the
same vanishing with free coefficients. Free covers and dimension shifting
then give vanishing with every coefficient module.
-/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule

variable {G : Type} [Group G]

def regularFreeCover (A : Rep.{0} ℤ G) : Rep.free ℤ G A ⟶ A :=
  Rep.freeLift ℤ G A id

instance regularFreeCover_epi (A : Rep.{0} ℤ G) : Epi (regularFreeCover A) := by
  rw [Rep.epi_iff_surjective]
  intro a
  refine ⟨Finsupp.single a (MonoidAlgebra.single 1 1), ?_⟩
  change Representation.freeLift A.ρ id
    (Finsupp.single a (MonoidAlgebra.single 1 1)) = a
  rw [Representation.freeLift_single_single]
  simp only [id_eq, map_one, Module.End.one_apply]
  exact @one_smul ℤ A _ A.hV2.toMulAction a

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_QuotientCoinvariantsFiniteness
attribute [-instance] _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # Finite generation after normal-subgroup coinvariants

The quotient group acts on the actual coinvariants of each resolution term.
When the quotient is finitely generated abelian, its noetherian group ring
makes homology finite as well. No homological tameness implication is assumed.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
open scoped MonoidAlgebra IsMulCommutative
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G] (N : Subgroup G) [N.Normal]

instance quotientCoinvariants_additive :
    (Rep.quotientToCoinvariantsFunctor.{0} ℤ N).Additive where
  map_add := by
    intro X Y f g
    ext x
    induction x using Representation.Coinvariants.induction_on with
    | h x => rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_InnerHomologyAction
attribute [-instance] _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Inner conjugation is the identity on group homology -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory HomologicalComplex
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2200] TensorProduct.instModule
attribute [local instance 2300] Representation.Coinvariants.instModule Pi.Function.module
variable {G : Type} [Group G] (A : Rep ℤ G)

def innerHomologyCoefficient (a : G) : A ⟶ Rep.res (MulAut.conj a).toMonoidHom A :=
  Rep.ofHom ⟨A.ρ a, by
    intro g
    change A.ρ a * A.ρ g = A.ρ (a * g * a⁻¹) * A.ρ a
    rw [← map_mul, ← map_mul]
    congr 1
    group⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ScalarExtendedH2CrossProduct
attribute [-instance] _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The second-homology cross product over a field

Both variables of the integral cross product are extended by scalars. Its
alternation is proved directly, including in characteristic two.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped TensorProduct
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable (K : Type) [Field K]

def scalarTensorUnit (M : Type) [AddCommGroup M] [Module ℤ M] :
    M →ₗ[ℤ] K ⊗[ℤ] M := TensorProduct.mk ℤ K M 1

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_HomologyClassExhaustion
attribute [-instance] _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Homology classes and finite generation along subgroup exhaustions -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2
variable {G : Type} [Group G]

def subgroupHomologyInclusion (H : Subgroup G) (A : Rep ℤ G) (i : ℕ) :
    groupHomology (Rep.res H.subtype A) i ⟶ groupHomology A i :=
  HomologicalComplex.homologyMap (subgroupBarInclusion H A) i

def subgroupRestrictionMap {H K : Subgroup G} (hHK : H ≤ K) (A : Rep ℤ G) :
    Rep.res H.subtype A ⟶ Rep.res (Subgroup.inclusion hHK) (Rep.res K.subtype A) :=
  Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_RationalGroupHomology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Scalar extension of the actual inhomogeneous bar complex -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
attribute [local instance 2000] Rep.hV2 Rep.instLinear ModuleCat.isModule
attribute [local instance 2300] TensorProduct.instModule Finsupp.module
variable {G : Type} [Group G]

def rationalizeGroupChainsIso (A : Rep.{0} ℤ G) :
    ((rationalModuleFunctor.mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (groupHomology.inhomogeneousChains A)) ≅
        groupHomology.inhomogeneousChains (rationalizeRepresentation A) := by
  classical
  refine HomologicalComplex.Hom.isoOfComponents
    (fun i => (TensorProduct.finsuppRight ℤ ℚ ℚ A.V (Fin i → G)).toModuleIso) ?_
  rintro i j rfl
  apply ModuleCat.hom_ext
  let L : (ℚ ⊗[ℤ] ((Fin (j + 1) → G) →₀ A.V)) →ₗ[ℚ]
      ((Fin j → G) →₀ (ℚ ⊗[ℤ] A.V)) :=
    ((TensorProduct.finsuppRight ℤ ℚ ℚ A.V (Fin (j + 1) → G)).toModuleIso.hom ≫
      (groupHomology.inhomogeneousChains (rationalizeRepresentation A)).d (j + 1) j).hom
  let R : (ℚ ⊗[ℤ] ((Fin (j + 1) → G) →₀ A.V)) →ₗ[ℚ]
      ((Fin j → G) →₀ (ℚ ⊗[ℤ] A.V)) :=
    ((((rationalModuleFunctor.mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (groupHomology.inhomogeneousChains A)).d (j + 1) j) ≫
      (TensorProduct.finsuppRight ℤ ℚ ℚ A.V (Fin j → G)).toModuleIso.hom).hom
  change L = R
  apply TensorProduct.AlgebraTensorModule.ext
  intro q f
  induction f using Finsupp.induction_linear with
  | zero => simp only [TensorProduct.tmul_zero, map_zero]
  | add f h hf hh => simp only [TensorProduct.tmul_add, map_add, hf, hh]
  | single x a =>
    change (groupHomology.inhomogeneousChains (rationalizeRepresentation A)).d (j + 1) j
      (TensorProduct.finsuppRight ℤ ℚ ℚ A.V (Fin (j + 1) → G)
        (q ⊗ₜ[ℤ] Finsupp.single x a)) =
      TensorProduct.finsuppRight ℤ ℚ ℚ A.V (Fin j → G)
        (((groupHomology.inhomogeneousChains A).d (j + 1) j).hom.baseChange ℚ
          (q ⊗ₜ[ℤ] Finsupp.single x a))
    rw [groupHomology.inhomogeneousChains.d_def, groupHomology.inhomogeneousChains.d_def,
      TensorProduct.finsuppRight_tmul_single]
    change groupHomology.inhomogeneousChains.d (rationalizeRepresentation A) j
      (Finsupp.single x (q ⊗ₜ[ℤ] a)) =
      TensorProduct.finsuppRight ℤ ℚ ℚ A.V (Fin j → G)
        (q ⊗ₜ[ℤ] groupHomology.inhomogeneousChains.d A j (Finsupp.single x a))
    let qa : rationalizeRepresentation A := q ⊗ₜ[ℤ] a
    change groupHomology.inhomogeneousChains.d (rationalizeRepresentation A) j
      (Finsupp.single x qa) = _
    rw [groupHomology.inhomogeneousChains.d_single]
    change _ = TensorProduct.finsuppRight ℤ ℚ ℚ A.V (Fin j → G)
      (q ⊗ₜ[ℤ] groupHomology.inhomogeneousChains.d A j (Finsupp.single x a))
    rw [groupHomology.inhomogeneousChains.d_single]
    simp only [TensorProduct.tmul_add, TensorProduct.tmul_sum, map_add, map_sum,
      TensorProduct.finsuppRight_tmul_single]
    congr 1
    apply Finset.sum_congr rfl
    intro l _
    dsimp only [qa, rationalizeRepresentation, Rep.of]
    change ((-1 : ℚ) ^ (l.val + 1)) •
        (Finsupp.single (l.contractNth (· * ·) x) (q ⊗ₜ[ℤ] a) :
          (Fin j → G) →₀ (ℚ ⊗[ℤ] A.V)) = _
    simp only [Finsupp.smul_single, TensorProduct.finsuppRight_tmul_single]
    rcases Nat.even_or_odd (l.val + 1) with h | h
    · simp only [h.neg_one_pow, one_smul]
      congr 2
      exact (@one_smul ℤ A.V _ A.hV2.toMulAction a).symm
    · simp only [h.neg_one_pow, neg_one_smul, TensorProduct.tmul_neg]

def rationalizeGroupHomologyIso (A : Rep.{0} ℤ G) (n : ℕ) :
    groupHomology (rationalizeRepresentation A) n ≅
      ModuleCat.of ℚ (ℚ ⊗[ℤ] groupHomology A n) :=
  (HomologicalComplex.homologyFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) n).mapIso
    (rationalizeGroupChainsIso A).symm ≪≫
      rationalModuleHomologyIso (groupHomology.inhomogeneousChains A) n

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NormalInductionTensor
attribute [-instance] _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Induced restriction as the quotient regular representation tensored with a coefficient -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory Representation MonoidalCategory
open scoped MonoidAlgebra TensorProduct
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2300] TensorProduct.instModule
variable {G : Type} [Group G] (N : Subgroup G) [N.Normal] (A : Rep.{0} ℤ G)

abbrev quotientRegularTensor : Rep ℤ G :=
  Rep.res (QuotientGroup.mk' N) (Rep.leftRegular ℤ (G ⧸ N)) ⊗ A

def normalInductionTensorRaw : ℤ[G] ⊗[ℤ] A →ₗ[ℤ] quotientRegularTensor N A :=
  TensorProduct.lift <|
    (Finsupp.lift _ _ _ fun g =>
      (TensorProduct.mk ℤ _ _ (MonoidAlgebra.single (QuotientGroup.mk' N g⁻¹) (1 : ℤ))).comp
        (A.ρ g⁻¹)) ∘ₗ (MonoidAlgebra.coeffLinearEquiv ℤ).toLinearMap

@[simp]
theorem normalInductionTensorRaw_single (g : G) (a : A) :
    normalInductionTensorRaw N A (MonoidAlgebra.single g 1 ⊗ₜ[ℤ] a) =
      MonoidAlgebra.single (QuotientGroup.mk' N g⁻¹) (1 : ℤ) ⊗ₜ[ℤ] A.ρ g⁻¹ a := by
  simp [normalInductionTensorRaw]

def normalTensorTerm (g : G) : A →ₗ[ℤ] Rep.ind N.subtype (Rep.res N.subtype A) :=
  (IndV.mk N.subtype (Rep.res N.subtype A).ρ g⁻¹).comp (A.ρ g⁻¹)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_NormalQuotientCompleteVanishing
attribute [-instance] _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite-dimensional quotients propagate induced-kernel vanishing

The quotient resolution is inflated and tensored with the coefficient.
Its countable free terms are actual sums of the induced kernel coefficient.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits MonoidalCategory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2300] TensorProduct.instModule
variable {G : Type} [Group G] (N : Subgroup G) [N.Normal] (A : Rep.{0} ℤ G)

abbrev quotientTensorFunctor : Rep.{0} ℤ (G ⧸ N) ⥤ Rep.{0} ℤ G :=
  Rep.resFunctor (k := ℤ) (QuotientGroup.mk' N) ⋙ tensorLeft A

def quotientTensorFreeNatIso :
    (quotientTensorFunctor N A).obj (Rep.free ℤ (G ⧸ N) ℕ) ≅
      ((quotientTensorFunctor N A).obj (Rep.leftRegular ℤ (G ⧸ N))).finsupp ℕ :=
  Rep.finsuppTensorRight (k := ℤ) (G := G) A
    (Rep.res (QuotientGroup.mk' N) (Rep.leftRegular ℤ (G ⧸ N))) ℕ

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_UltrafilterSubgroup
attribute [-instance] _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Subgroup limits preserve a fixed derived-series bound -/
noncomputable section
namespace PolycyclicRecognition
open Filter
variable {G I : Type} [Group G]

def ultrafilterSubgroup (U : Ultrafilter I) (K : I → Subgroup G) : Subgroup G where
  carrier := {g | ∀ᶠ i in U, g ∈ K i}
  one_mem' := Eventually.of_forall (fun i => (K i).one_mem)
  mul_mem' hx hy := by
    filter_upwards [hx, hy] with i hi hj
    exact (K i).mul_mem hi hj
  inv_mem' hx := by
    filter_upwards [hx] with i hi
    exact (K i).inv_mem hi

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_LocalVirtualSolvabilityBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform virtual solvability in locally virtually nilpotent groups -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
variable {G : Type} [Group G]

def virtualSolvabilityIndexBound (b d : ℕ) : ℕ :=
  3 ^ ((2 * d * d) * (2 * d * d)) * b ^ b

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NatTotalComplexSymmetry
attribute [-instance] _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The Koszul symmetry for first-quadrant chain complexes -/
namespace PolycyclicRecognition

instance natDownTotalComplexSymmetry :
    TotalComplexShapeSymmetry (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ) where
  symm p q := Nat.add_comm q p
  σ p q := (-1 : ℤˣ) ^ (p * q)
  σ_ε₁ := by
    intro p p' h q
    change p' + 1 = p at h
    subst p
    change (-1 : ℤˣ) ^ ((p' + 1) * q) * 1 = (-1 : ℤˣ) ^ q * (-1 : ℤˣ) ^ (p' * q)
    rw [Nat.add_mul, one_mul, pow_add, mul_one, mul_comm]
  σ_ε₂ := by
    intro p q q' h
    change q' + 1 = q at h
    subst q
    change (-1 : ℤˣ) ^ (p * (q' + 1)) * (-1 : ℤˣ) ^ p = 1 * (-1 : ℤˣ) ^ (p * q')
    rw [Nat.mul_add, mul_one, pow_add, mul_assoc, Int.units_mul_self, mul_one, one_mul]

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NilpotentSectionRemainder
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial bounds for the actual ideal section remainder

The remainder of an exponential after removing its pure quotient section
is computed with the finite BCH formula. Its ideal coordinates have a
polynomial bound in the original logarithm. No box comparison is assumed.
-/

noncomputable section
namespace PolycyclicRecognition

open Module Set
open scoped BigOperators

variable {V I J : Type*} [LieRing V] [LieAlgebra ℝ V] [Fintype I] [Fintype J]
  (U : LieIdeal ℝ V) (bI : Basis I ℝ U) (bQ : Basis J ℝ (V ⧸ U.toSubmodule))
  (lift : J → V) (hlift : ∀ j, U.toSubmodule.mkQ (lift j) = bQ j)

variable {N Q : Type*}
  [Group N]
  [Group Q]
  (ExpN : V → N)
  (ExpQ : (V ⧸ U.toSubmodule) → Q)
  (π : N →* Q)
  (hπ : ∀ v, π (ExpN v) = ExpQ (U.toSubmodule.mkQ v))
  (hinjQ : Function.Injective ExpQ)
  (hzeroQ : ExpQ 0 = 1)
  (hneg : ∀ v, ExpN (-v) = (ExpN v)⁻¹)
  {c : ℕ}

/-- The product constant depends on dimension, nilpotence degree, and a
uniform bracket bound, rather than on the chosen basis. -/
def sectionDynkinConstant (d c : ℕ) (C : ℝ) : ℝ :=
  (c : ℝ) * 2 ^ c * (1 + (d : ℝ) ^ 2 * C) ^ c * (3 : ℝ) ^ c

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ParametrizedGeneratorSchemes
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Continuous path samples for the finite generator schemes

The conjugating letters are fixed. Only the inserted amplitudes vary, so
the whole expanded word has a fixed combinatorial pattern and continuous
amplitudes. This makes each of its support-path samples continuous.
-/

noncomputable section

namespace PolycyclicRecognition

variable {I Y : Type*} {k : ℕ}

def parameterGeneratorSchemeWord (w : Fin k → List (I × ℝ)) (i : Fin k → I)
    (σ : Y → Fin k → ℝ) : List (I × (Y → ℝ)) :=
  (List.ofFn (fun j =>
    (w j).map (fun z => (z.1, fun _ : Y => z.2)) ++
      [(i j, fun y => σ y j)] ++
      (inverseGeneratorWord (w j)).map (fun z => (z.1, fun _ : Y => z.2)))).flatten

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolyhedralSymmetries
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite linear symmetry group of a spanning polytope

The support body in the height argument is a convex hull of finitely many
covectors. Preserving that body permutes its extreme points. We prove that
these form a finite spanning set, so the symmetry family is finite.
-/

namespace PolycyclicRecognition

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- A finite spanning polytope has finitely many linear symmetries. Its given
generators need not themselves be vertices. -/
theorem finite_polytope_symmetries (s : Finset W)
    (hspan : Submodule.span ℝ (s : Set W) = ⊤) :
    Set.Finite {A : W ≃L[ℝ] W | A '' convexHull ℝ (s : Set W) = convexHull ℝ (s : Set W)} := by
  classical
  let C := convexHull ℝ (s : Set W)
  let V := Set.extremePoints ℝ C
  have hV : V.Finite := s.finite_toSet.subset extremePoints_convexHull_subset
  have hC : convexHull ℝ V = C := by
    calc
      convexHull ℝ V = closure (convexHull ℝ V) := (hV.isClosed_convexHull ℝ).closure_eq.symm
      _ = C := closure_convexHull_extremePoints (s.finite_toSet.isCompact_convexHull ℝ)
        (convex_convexHull ℝ (s : Set W))
  have hVspan : Submodule.span ℝ (hV.toFinset : Set W) = ⊤ := by
    rw [hV.coe_toFinset]
    apply top_unique
    rw [← hspan]
    apply Submodule.span_le.mpr
    intro x hx
    have hxC : x ∈ C := subset_convexHull ℝ (s : Set W) hx
    rw [← hC] at hxC
    exact (convexHull_min (Submodule.subset_span : V ⊆ Submodule.span ℝ V)
      (Submodule.convex _)) hxC
  apply (finite_linear_symmetries hV.toFinset hVspan).subset
  intro A hA v hv
  have himage : A '' V = V := by
    change A '' Set.extremePoints ℝ C = Set.extremePoints ℝ C
    rw [image_extremePoints, hA]
  have hAv : A v ∈ V := himage ▸ Set.mem_image_of_mem A (hV.mem_toFinset.mp hv)
  exact hV.mem_toFinset.mpr hAv

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialProductParameters
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Transporting polynomial lattice parameters through an added real coordinate -/

noncomputable section
namespace PolycyclicRecognition
open Module

variable {U V W : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {d e k n : ℕ}

def transportedProductParameter (p : V ≃ V) (s : W ≃ₗ[ℝ] (V × ℝ))
    (E : W ≃ (V × ℝ)) : W ≃ W :=
  s.toEquiv.trans ((p.prodCongr (Equiv.refl ℝ)).trans E.symm)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_QuotientLinearAction
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
attribute [-simp] _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The action induced on an invariant quotient -/

noncomputable section
namespace PolycyclicRecognition

variable {G K V : Type*} [Group G] [Field K] [AddCommGroup V] [Module K V]

def quotientLinearAction (ρ : G →* (V ≃ₗ[K] V)) (W : Submodule K V)
    (hW : ∀ g : G, ∀ v ∈ W, ρ g v ∈ W) : G →* ((V ⧸ W) ≃ₗ[K] (V ⧸ W)) where
  toFun g :=
    { W.mapQ W (ρ g).toLinearMap (hW g) with
      invFun := W.mapQ W (ρ g⁻¹).toLinearMap (hW g⁻¹)
      left_inv := by
        intro v
        obtain ⟨v, rfl⟩ := W.mkQ_surjective v
        change W.mkQ (ρ g⁻¹ (ρ g v)) = W.mkQ v
        rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
        rfl
      right_inv := by
        intro v
        obtain ⟨v, rfl⟩ := W.mkQ_surjective v
        change W.mkQ (ρ g (ρ g⁻¹ v)) = W.mkQ v
        rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
        rfl }
  map_one' := by
    apply LinearEquiv.ext
    intro v
    obtain ⟨v, rfl⟩ := W.mkQ_surjective v
    change W.mkQ (ρ 1 v) = W.mkQ v
    rw [map_one]
    rfl
  map_mul' g h := by
    apply LinearEquiv.ext
    intro v
    obtain ⟨v, rfl⟩ := W.mkQ_surjective v
    change W.mkQ (ρ (g * h) v) = W.mkQ (ρ g (ρ h v))
    rw [map_mul]
    rfl

@[simp] theorem quotientLinearAction_mkQ (ρ : G →* (V ≃ₗ[K] V)) (W : Submodule K V)
    (hW : ∀ g : G, ∀ v ∈ W, ρ g v ∈ W) (g : G) (v : V) :
    quotientLinearAction ρ W hW g (W.mkQ v) = W.mkQ (ρ g v) := rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RankOneCharacter
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
attribute [-simp] _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The scalar character of a rank-one integral representation -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G]

theorem rankOne_action_coordinate (D : Rep ℤ G) (e : D.V ≃ₗ[ℤ] ℤ)
    (g : G) (x : D) : e (D.ρ g x) = e x * e (D.ρ g (e.symm 1)) := by
  simpa only [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply] using
    integralEnd_apply (e.conj (D.ρ g)) (e x)

def rankOneCharacter (D : Rep ℤ G) (e : D.V ≃ₗ[ℤ] ℤ) : G →* ℤ where
  toFun g := e (D.ρ g (e.symm 1))
  map_one' := by simp
  map_mul' g h := by
    rw [map_mul, Module.End.mul_apply, rankOne_action_coordinate]
    exact mul_comm _ _

def scalarCharacterRep (χ : G →* ℤ) : Rep ℤ G :=
  Rep.of ((algebraMap ℤ (Module.End ℤ ℤ)).toMonoidHom.comp χ)

def rankOneCharacterIso (D : Rep ℤ G) (e : D.V ≃ₗ[ℤ] ℤ) :
    D ≅ scalarCharacterRep (rankOneCharacter D e) :=
  Rep.mkIso (Representation.Equiv.mk e (by
    intro g
    ext x
    change e (D.ρ g x) = e (D.ρ g (e.symm 1)) * e x
    rw [rankOne_action_coordinate, mul_comm]))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RationalAbelianTorsion
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rationalization detects torsion in abelian groups -/
noncomputable section
namespace PolycyclicRecognition
open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits
variable {A : Type} [CommGroup A]

theorem rational_module_isZero_of_surjective {M P : Type}
    [AddCommGroup M] [AddCommGroup P] [Module ℤ M] [Module ℤ P]
    (f : M →ₗ[ℤ] P) (hf : Function.Surjective f)
    (hM : IsZero (ModuleCat.of ℚ (ℚ ⊗[ℤ] M))) :
    IsZero (ModuleCat.of ℚ (ℚ ⊗[ℤ] P)) := by
  let fQ := ModuleCat.ofHom (f.baseChange ℚ)
  let : Epi fQ := (ModuleCat.epi_iff_surjective fQ).mpr (f.baseChange_surjective ℚ hf)
  exact IsZero.of_epi fQ hM

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RationalRankOneAction
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
attribute [-simp] _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The rational character of an action on a rank-one abelian group -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
open scoped TensorProduct
variable {G M : Type} [Group G] [AddCommGroup M] [Module ℤ M]

def integralLinear (f : M →+ M) : M →ₗ[ℤ] M where
  toFun := f
  map_add' := f.map_add
  map_smul' r x := by
    exact (congrArg f (int_smul_eq_zsmul (inferInstance : Module ℤ M) r x)).trans
      ((map_zsmul f r x).trans (int_smul_eq_zsmul (inferInstance : Module ℤ M) r (f x)).symm)

def rationalizedAction (ρ : G →* AddMonoid.End M) :
    Representation ℚ G (ℚ ⊗[ℤ] M) where
  toFun g := (integralLinear (ρ g)).baseChange ℚ
  map_one' := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro r x
    change r ⊗ₜ[ℤ] ((ρ 1) x) = r ⊗ₜ[ℤ] x
    rw [map_one]
    rfl
  map_mul' g h := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro r x
    change r ⊗ₜ[ℤ] ((ρ (g * h)) x) = r ⊗ₜ[ℤ] ((ρ g) ((ρ h) x))
    rw [map_mul]
    rfl

def rationalActionCharacter (ρ : G →* AddMonoid.End M)
    (e : (ℚ ⊗[ℤ] M) ≃ₗ[ℚ] ℚ) : G →* ℚ where
  toFun g := e (rationalizedAction ρ g (e.symm 1))
  map_one' := by simp
  map_mul' g h := by
    let F := e.toLinearMap.comp ((rationalizedAction ρ g).comp e.symm.toLinearMap)
    have hf (r : ℚ) : F r = r * F 1 := by
      simpa only [smul_eq_mul, mul_one] using F.map_smul r 1
    change e (rationalizedAction ρ (g * h) (e.symm 1)) = _
    rw [map_mul, Module.End.mul_apply]
    have hv := hf (e (rationalizedAction ρ h (e.symm 1)))
    dsimp [F] at hv
    rw [LinearEquiv.symm_apply_apply] at hv
    exact hv.trans (mul_comm _ _)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RationalCharacterCancellation
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
attribute [-simp] _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cancelling a rational character on its one-dimensional representation -/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
open scoped TensorProduct
variable {G M : Type} [Group G] [AddCommGroup M] [Module ℤ M]

def rationalScalarMap (r : ℚ) : ModuleCat.of ℤ ℚ ⟶ ModuleCat.of ℤ ℚ :=
  ModuleCat.ofHom (r • (LinearMap.id : ℚ →ₗ[ℤ] ℚ))

@[simp] theorem rationalScalarMap_apply (r q : ℚ) :
    (rationalScalarMap r).hom q = r * q := rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RationalFiniteCoinvariants
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact rational coinvariants for a finite group

The averaging map descends to coinvariants and is a section of their quotient
map. Its naturality proves preservation of injections directly.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2300] Representation.Coinvariants.instModule
variable {H : Type} [Group H] [Fintype H]
variable {V W : Type} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]

def finiteRationalAverage (ρ : Representation ℚ H V) : V →ₗ[ℚ] V :=
  (Fintype.card H : ℚ)⁻¹ • ∑ g : H, ρ g

theorem finiteRationalAverage_apply (ρ : Representation ℚ H V) (x : V) :
    finiteRationalAverage ρ x = (Fintype.card H : ℚ)⁻¹ • ∑ g : H, ρ g x := by
  simp only [finiteRationalAverage, LinearMap.smul_apply, LinearMap.sum_apply]

theorem finiteRationalAverage_action (ρ : Representation ℚ H V) (g : H) (x : V) :
    finiteRationalAverage ρ (ρ g x) = finiteRationalAverage ρ x := by
  simp only [finiteRationalAverage_apply]
  congr 1
  exact Fintype.sum_bijective (· * g) (Group.mulRight_bijective g) _ _
    (fun h => by rw [map_mul]; rfl)

def finiteRationalCoinvariantsSection (ρ : Representation ℚ H V) :
    ρ.Coinvariants →ₗ[ℚ] V :=
  Representation.Coinvariants.lift ρ (finiteRationalAverage ρ)
    (fun g => LinearMap.ext (finiteRationalAverage_action ρ g))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RationalOrientationCoefficient
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
attribute [-simp] _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rational coefficient representations extending an integral orientation -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
open scoped TensorProduct
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G]

def rationalCharacterRep (χ : G →* ℚ) : Rep ℤ G :=
  Rep.of ((Algebra.lsmul ℤ ℤ ℚ).toMonoidHom.comp χ)

@[simp] theorem rationalCharacterRep_apply (χ : G →* ℚ) (g : G) (q : ℚ) :
    (rationalCharacterRep χ).ρ g q = χ g * q := rfl

def rationalizedOrientationEquiv {K : Type} [Group K] (R : Rep ℤ K)
    (eR : R.V ≃ₗ[ℤ] ℤ) :
    (trivialTensorCoefficient (ModuleCat.of ℤ ℚ) R).V ≃ₗ[ℤ] ℚ :=
  (TensorProduct.congr (LinearEquiv.refl ℤ ℚ) eR).trans (TensorProduct.rid ℤ ℚ)

@[simp] theorem rationalizedOrientationEquiv_tmul {K : Type} [Group K]
    (R : Rep ℤ K) (eR : R.V ≃ₗ[ℤ] ℤ) (q : ℚ) (a : R) :
    rationalizedOrientationEquiv R eR (q ⊗ₜ[ℤ] a) = (eR a : ℚ) * q := by
  change TensorProduct.rid ℤ ℚ (q ⊗ₜ[ℤ] eR a) = _
  rw [TensorProduct.rid_tmul]
  simp only [zsmul_eq_mul]

def rationalizedOrientationIso (N : Subgroup G) (R : Rep ℤ N)
    (eR : R.V ≃ₗ[ℤ] ℤ) (χ : G →* ℚ)
    (hχ : ∀ a : N, χ (a : G) = (rankOneCharacter R eR a : ℚ)) :
    trivialTensorCoefficient (ModuleCat.of ℤ ℚ) R ≅ Rep.res N.subtype (rationalCharacterRep χ) :=
  Rep.mkIso (Representation.Equiv.mk (rationalizedOrientationEquiv R eR) (by
    intro a
    apply TensorProduct.ext
    apply LinearMap.ext
    intro q
    apply LinearMap.ext
    intro v
    change rationalizedOrientationEquiv R eR
        ((trivialTensorCoefficient (ModuleCat.of ℤ ℚ) R).ρ a (q ⊗ₜ[ℤ] v)) =
      χ (a : G) * rationalizedOrientationEquiv R eR (q ⊗ₜ[ℤ] v)
    rw [trivialTensorCoefficient_tmul, rationalizedOrientationEquiv_tmul,
      rationalizedOrientationEquiv_tmul, hχ, rankOne_action_coordinate]
    push_cast
    dsimp [rankOneCharacter]
    ring))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_OrientationHomologyAction
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Ambient conjugation on the local top orientation homology -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G] (N : Subgroup G) [N.Normal]

def invariantConjugationCoefficient (R : Rep ℤ N)
    (hinv : ∀ (g : G) (a : N), R.ρ (MulAut.conjNormal g a) = R.ρ a) (g : G) :
    R ⟶ Rep.res (MulAut.conjNormal (H := N) g).toMonoidHom R :=
  Rep.ofHom ⟨LinearMap.id, by
    intro a
    change LinearMap.id ∘ₗ R.ρ a = R.ρ (MulAut.conjNormal g a) ∘ₗ LinearMap.id
    rw [hinv, LinearMap.id_comp, LinearMap.comp_id]⟩

def invariantConjugationHomologyMap (R : Rep ℤ N)
    (hinv : ∀ (g : G) (a : N), R.ρ (MulAut.conjNormal g a) = R.ρ a)
    (d : ℕ) (g : G) : groupHomology R d ⟶ groupHomology R d :=
  groupHomology.map (MulAut.conjNormal (H := N) g).toMonoidHom
    (invariantConjugationCoefficient N R hinv g) d

theorem invariantConjugationHomologyMap_one (R : Rep ℤ N)
    (hinv : ∀ (g : G) (a : N), R.ρ (MulAut.conjNormal g a) = R.ρ a) (d : ℕ) :
    invariantConjugationHomologyMap N R hinv d 1 = 𝟙 _ := by
  rw [invariantConjugationHomologyMap, ← groupHomology.map_id]
  apply groupHomology.map_congr
  · ext a
    exact congrArg (fun e : MulAut N => ((e a : N) : G)) (map_one (MulAut.conjNormal (H := N)))
  · rfl

theorem invariantConjugationHomologyMap_mul (R : Rep ℤ N)
    (hinv : ∀ (g : G) (a : N), R.ρ (MulAut.conjNormal g a) = R.ρ a)
    (d : ℕ) (g h : G) :
    invariantConjugationHomologyMap N R hinv d (g * h) =
      invariantConjugationHomologyMap N R hinv d h ≫
        invariantConjugationHomologyMap N R hinv d g := by
  rw [invariantConjugationHomologyMap, invariantConjugationHomologyMap,
    invariantConjugationHomologyMap, ← groupHomology.map_comp]
  apply groupHomology.map_congr
  · ext a
    exact congrArg (fun e : MulAut N => ((e a : N) : G)) (map_mul (MulAut.conjNormal (H := N)) g h)
  · rfl

def invariantConjugationHomologyAction (R : Rep ℤ N)
    (hinv : ∀ (g : G) (a : N), R.ρ (MulAut.conjNormal g a) = R.ρ a)
    (d : ℕ) : G →* AddMonoid.End (groupHomology R d) where
  toFun g := (invariantConjugationHomologyMap N R hinv d g).hom.toAddMonoidHom
  map_one' := by
    rw [invariantConjugationHomologyMap_one]
    rfl
  map_mul' g h := by
    rw [invariantConjugationHomologyMap_mul]
    rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RationalOrientationExtension
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
attribute [-simp] _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Extending the kernel orientation by its rational top homology

The conjugation action on the rationalized top homology gives an ambient
character. Inverting its source gives the original integral orientation on
the normal subgroup.
-/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
attribute [local instance 2000] Rep.hV2 Rep.instLinear ModuleCat.isModule
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G]

def inverseSourceRationalCharacter (χ : G →* ℚ) : G →* ℚ where
  toFun g := χ g⁻¹
  map_one' := by simp
  map_mul' g h := by rw [mul_inv_rev, map_mul, mul_comm]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_TrivialTensorChainNaturality
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Naturality of the trivial-coefficient tensor comparison -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory MonoidalCategory
open scoped TensorProduct
attribute [local instance 2000] Rep.hV2
variable {k G H : Type} [CommRing k] [Group G] [Group H]
  {V W : ModuleCat k} {A : Rep k G} {B : Rep k H}

def trivialTensorCoefficientMap (u : V ⟶ W) (f : G →* H) (φ : A ⟶ Rep.res f B) :
    trivialTensorCoefficient V A ⟶ Rep.res f (trivialTensorCoefficient W B) :=
  Rep.ofHom ⟨TensorProduct.map u.hom φ.hom.toLinearMap, by
    intro g
    apply TensorProduct.ext
    apply LinearMap.ext
    intro v
    apply LinearMap.ext
    intro a
    change u.hom v ⊗ₜ[k] φ.hom (A.ρ g a) = u.hom v ⊗ₜ[k] B.ρ (f g) (φ.hom a)
    rw [Rep.hom_comm_apply]
    rfl⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RationalScalarTwist
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rational scalar twists of an ambient coefficient representation -/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory MonoidalCategory
open scoped TensorProduct
attribute [local instance 2000] Rep.hV2 Rep.instLinear ModuleCat.isModule
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G]

def rationalScalarTwist (A : Rep ℤ G) (η : G →* ℚ) : Rep ℤ G :=
  rationalCharacterRep η ⊗ A

def rationalScalarTwistRestrictionIso (N : Subgroup G) (A : Rep ℤ G)
    (η : G →* ℚ) (hη : ∀ a : N, η (a : G) = 1) :
    trivialTensorCoefficient (ModuleCat.of ℤ ℚ) (Rep.res N.subtype A) ≅
      Rep.res N.subtype (rationalScalarTwist A η) :=
  Rep.mkIso (Representation.Equiv.mk (LinearEquiv.refl ℤ _) (by
    intro a
    apply TensorProduct.ext
    apply LinearMap.ext
    intro q
    apply LinearMap.ext
    intro v
    change q ⊗ₜ[ℤ] (A.ρ (a : G) v) = (η (a : G) * q) ⊗ₜ[ℤ] (A.ρ (a : G) v)
    rw [hη, one_mul]))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RealEigenAnnihilator
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A real split annihilator from spanning real eigenvectors -/

noncomputable section
namespace PolycyclicRecognition

open Polynomial Module

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  (D : Module.End ℝ V)

def realEigenPolynomial : ℝ[X] := ∏ r : D.Eigenvalues, (X - C (r : ℝ))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RealNilpotentLogIntertwiner
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Real-linear maps intertwine the canonical rational logarithm -/

noncomputable section
namespace PolycyclicRecognition
variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
local instance realLogRationalTarget : Module ℚ W := Module.compHom W (algebraMap ℚ ℝ)
local instance realLogRationalSource_r784cef_1 : Module ℚ V := Module.compHom V (algebraMap ℚ ℝ)
local instance realLogRationalTowerV_r784cef_1 : IsScalarTower ℚ ℝ V :=
  ⟨fun q r v => by change (algebraMap ℚ ℝ q * r) • v = algebraMap ℚ ℝ q • (r • v); rw [mul_smul]⟩
local instance realLogRationalTowerW : IsScalarTower ℚ ℝ W :=
  ⟨fun q r v => by change (algebraMap ℚ ℝ q * r) • v = algebraMap ℚ ℝ q • (r • v); rw [mul_smul]⟩
local instance realLogRationalCommV_r784cef_1 : SMulCommClass ℝ ℚ V :=
  ⟨fun r q v => by change r • (algebraMap ℚ ℝ q • v) = algebraMap ℚ ℝ q • (r • v); rw [smul_comm]⟩
local instance realLogRationalCommW : SMulCommClass ℝ ℚ W :=
  ⟨fun r q v => by change r • (algebraMap ℚ ℝ q • v) = algebraMap ℚ ℝ q • (r • v); rw [smul_comm]⟩

def rationalEndRestriction (V : Type*) [AddCommGroup V] [Module ℝ V] :
    Module.End ℝ V →+* Module.End ℚ V where
  toFun f := f.restrictScalars ℚ
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RiemannianChartLength
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Chart displacement controlled by the length of a path -/

noncomputable section
namespace PolycyclicRecognition

open Set MeasureTheory Manifold
open scoped Manifold ContDiff ENNReal NNReal Bundle

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) 1 M]
  [Bundle.RiemannianBundle (TangentSpace (𝓘(ℝ, E)) : M → Type _)]

local instance tangentModelOperatorENorm (x : M) (y : E) :
    ENorm (TangentSpace (𝓘(ℝ, E)) x →L[ℝ] TangentSpace (𝓘(ℝ, E)) y) :=
  inferInstanceAs (ENorm (TangentSpace (𝓘(ℝ, E)) x →L[ℝ] E))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SemisimpleKernelProjection
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The canonical fixed-space projection preserves invariant filtrations

For a semisimple operator, its kernel and range are complementary. The
projection to the kernel preserves every invariant subspace, including the
lower central series when the operator is A - 1.
-/

noncomputable section
namespace PolycyclicRecognition
variable {L : Type*} [AddCommGroup L] [Module ℝ L] [FiniteDimensional ℝ L]

theorem semisimple_kernel_range_isCompl (B : Module.End ℝ L) (hB : B.IsSemisimple) :
    IsCompl B.ker B.range := by
  have hker : B.ker ∈ B.invtSubmodule := by
    change ∀ x ∈ B.ker, B x ∈ B.ker
    intro x hx
    change B (B x) = 0
    rw [LinearMap.mem_ker.mp hx, map_zero]
  obtain ⟨W, hW, hKW⟩ := Module.End.isSemisimple_iff.mp hB B.ker hker
  have hW' : ∀ x ∈ W, B x ∈ W := hW
  let f : W →ₗ[ℝ] W := B.restrict hW'
  have hi : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply sub_eq_zero.mp
    apply Submodule.disjoint_def.mp hKW.disjoint
    · change B ((x : L) - (y : L)) = 0
      rw [map_sub]
      exact sub_eq_zero.mpr (congrArg Subtype.val hxy)
    · exact W.sub_mem x.property y.property
  have hs : Function.Surjective f := LinearMap.injective_iff_surjective.mp hi
  have hr : B.range = W := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      have hx : x ∈ B.ker ⊔ W := by rw [hKW.sup_eq_top]; trivial
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hx
      rw [← hab, map_add, LinearMap.mem_ker.mp ha, zero_add]
      exact hW' b hb
    · intro x hx
      obtain ⟨y, hy⟩ := hs ⟨x, hx⟩
      exact ⟨y, congrArg Subtype.val hy⟩
  rw [hr]
  exact hKW

omit [FiniteDimensional ℝ L] in
theorem semisimple_sub_one (B : Module.End ℝ L) (hB : B.IsSemisimple) :
    Module.End.IsSemisimple (B - 1) := by
  have h := (Module.End.isSemisimple_sub_algebraMap_iff (f := B) (μ := (1 : ℝ))).mpr hB
  simpa only [map_one] using h

def semisimpleKernelProjection (B : Module.End ℝ L) (hB : B.IsSemisimple) : Module.End ℝ L :=
  B.ker.projection B.range (semisimple_kernel_range_isCompl B hB)

theorem semisimpleKernelProjection_mem (B : Module.End ℝ L) (hB : B.IsSemisimple) (x : L) :
    semisimpleKernelProjection B hB x ∈ B.ker :=
  Submodule.projection_apply_mem _ _

theorem semisimpleKernelProjection_preserves (B : Module.End ℝ L) (hB : B.IsSemisimple)
    (U : Submodule ℝ L) (hU : ∀ x ∈ U, B x ∈ U) {x : L} (hx : x ∈ U) :
    semisimpleKernelProjection B hB x ∈ U := by
  let f : U →ₗ[ℝ] U := B.restrict hU
  have hf : Module.End.IsSemisimple f := hB.restrict hU
  have hc := semisimple_kernel_range_isCompl f hf
  have hx' : (⟨x, hx⟩ : U) ∈ f.ker ⊔ f.range := by rw [hc.sup_eq_top]; trivial
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hx'
  have ha' : (a : L) ∈ B.ker := congrArg Subtype.val (LinearMap.mem_ker.mp ha)
  have hb' : (b : L) ∈ B.range := by
    obtain ⟨y, hy⟩ := hb
    exact ⟨y, congrArg Subtype.val hy⟩
  have he : (a : L) + (b : L) = x := congrArg Subtype.val hab
  rw [← he, map_add]
  change B.ker.projection B.range (semisimple_kernel_range_isCompl B hB) a +
    B.ker.projection B.range (semisimple_kernel_range_isCompl B hB) b ∈ U
  rw [Submodule.projection_apply_of_mem_left _ ha',
    Submodule.projection_apply_of_mem_right _ hb', add_zero]
  exact a.property

theorem semisimple_add_kernelProjection_bijective (B : Module.End ℝ L)
    (hB : B.IsSemisimple) : Function.Bijective (B + semisimpleKernelProjection B hB) := by
  let P := semisimpleKernelProjection B hB
  have hz (x : L) (hx : (B + P) x = 0) : x = 0 := by
    have hPB : P (B x) = 0 := Submodule.projection_apply_of_mem_right _ ⟨x, rfl⟩
    have hPP : P (P x) = P x :=
      Submodule.projection_apply_of_mem_left _ (semisimpleKernelProjection_mem B hB x)
    have hp := congrArg P hx
    change P (B x + P x) = P 0 at hp
    rw [map_add, hPB, hPP, map_zero, zero_add] at hp
    have hBx : B x = 0 := by
      change B x + P x = 0 at hx
      rwa [hp, add_zero] at hx
    have hPx : P x = x := Submodule.projection_apply_of_mem_left _ hBx
    exact hPx.symm.trans hp
  have hi : Function.Injective (B + P) := by
    intro x y hxy
    apply sub_eq_zero.mp
    apply hz
    rw [map_sub, hxy, sub_self]
  exact ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩

/-- A vector whose image lies in an invariant subspace differs from its fixed
component by a vector in that subspace. -/
theorem semisimple_sub_projection_mem_of_apply_mem
    (B : Module.End ℝ L) (hB : B.IsSemisimple)
    (U : Submodule ℝ L) (hU : ∀ x ∈ U, B x ∈ U) {x : L} (hx : B x ∈ U) :
    x - semisimpleKernelProjection B hB x ∈ U := by
  let P := semisimpleKernelProjection B hB
  let e : L ≃ₗ[ℝ] L := LinearEquiv.ofBijective (B + P)
    (semisimple_add_kernelProjection_bijective B hB)
  have he : e (x - P x) = B x := by
    have hBP : B (P x) = 0 := semisimpleKernelProjection_mem B hB x
    have hPP : P (P x) = P x := Submodule.projection_apply_of_mem_left _
      (semisimpleKernelProjection_mem B hB x)
    change B (x - P x) + P (x - P x) = B x
    rw [map_sub, map_sub, hBP, hPP]
    abel
  have hp : e.symm (B x) ∈ U := inverse_mem_of_preserves_submodule e U
    (fun y hy => U.add_mem (hU y hy) (semisimpleKernelProjection_preserves B hB U hU hy)) hx
  rwa [← he, e.symm_apply_apply] at hp

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SemisimpleSpectralOperator
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Scalar functional calculus on the eigenspaces of a semisimple operator

Only the finite-dimensional application needed for a matrix logarithm is
used. The operator is constructed from the internal eigenspace direct sum.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped DirectSum
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

def semisimpleEigenspaceEquiv (S : Module.End ℂ V) (hS : S.IsSemisimple) :
    (⨁ μ : ℂ, S.eigenspace μ) ≃ₗ[ℂ] V := by
  classical
  exact LinearEquiv.ofBijective (DirectSum.coeLinearMap S.eigenspace)
    (DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      S.eigenspaces_iSupIndep hS.iSup_eigenspace_eq_top)

def semisimpleSpectralOperator (S : Module.End ℂ V) (hS : S.IsSemisimple)
    (f : ℂ → ℂ) : Module.End ℂ V := by
  classical
  exact (DirectSum.toModule ℂ ℂ V (fun μ => f μ • (S.eigenspace μ).subtype)).comp
    (semisimpleEigenspaceEquiv S hS).symm.toLinearMap

theorem semisimpleSpectralOperator_apply (S : Module.End ℂ V) (hS : S.IsSemisimple)
    (f : ℂ → ℂ) {μ : ℂ} {x : V} (hx : x ∈ S.eigenspace μ) :
    semisimpleSpectralOperator S hS f x = f μ • x := by
  classical
  have he : semisimpleEigenspaceEquiv S hS
      (DirectSum.lof ℂ ℂ (fun μ => S.eigenspace μ) μ ⟨x, hx⟩) = x :=
    DirectSum.coeLinearMap_lof S.eigenspace μ ⟨x, hx⟩
  change (DirectSum.toModule ℂ ℂ V (fun μ => f μ • (S.eigenspace μ).subtype))
    ((semisimpleEigenspaceEquiv S hS).symm x) = _
  rw [← he, LinearEquiv.symm_apply_apply, DirectSum.toModule_lof]
  rw [he]
  rfl

theorem semisimple_eigenspace_ext (S : Module.End ℂ V) (hS : S.IsSemisimple)
    {W : Type*} [AddCommGroup W] [Module ℂ W] {F G : V →ₗ[ℂ] W}
    (h : ∀ μ x, x ∈ S.eigenspace μ → F x = G x) : F = G := by
  apply sub_eq_zero.mp
  apply LinearMap.ker_eq_top.mp
  apply top_unique
  rw [← hS.iSup_eigenspace_eq_top]
  apply iSup_le
  intro μ x hx
  rw [LinearMap.mem_ker, LinearMap.sub_apply, h μ x hx, sub_self]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SeparateGroupClosure
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Closures and components using separately continuous multiplication

Polynomial matrix groups have this weaker topological structure. It is
enough to form subgroup closures and the normal identity component. In a
Noetherian space the latter has finite index.
-/

noncomputable section
namespace PolycyclicRecognition

variable {G : Type*} [Group G] [TopologicalSpace G]
  [SeparatelyContinuousMul G] [ContinuousInv G]

def separateClosure (S : Subgroup G) : Subgroup G where
  carrier := closure (S : Set G)
  one_mem' := subset_closure S.one_mem
  mul_mem' hg hh := map_mem_closure₂'
    (fun g => continuous_const_mul g) (fun h => continuous_mul_const h) hg hh
    (fun _ hg _ hh => S.mul_mem hg hh)
  inv_mem' hg := map_mem_closure continuous_inv hg (fun _ ha => S.inv_mem ha)

def separateIdentityComponent (G : Type*) [Group G] [TopologicalSpace G]
    [SeparatelyContinuousMul G] [ContinuousInv G] : Subgroup G where
  carrier := connectedComponent (1 : G)
  one_mem' := mem_connectedComponent
  mul_mem' := by
    intro g h hg hh
    have hm := (continuous_const_mul g).mapsTo_connectedComponent 1 hh
    rw [connectedComponent_eq hg]
    simpa only [mul_one] using hm
  inv_mem' := by
    intro g hg
    have hm := continuous_inv.mapsTo_connectedComponent (1 : G) hg
    simpa only [inv_one] using hm

instance separateIdentityComponent_normal : (separateIdentityComponent G).Normal where
  conj_mem a ha g := by
    change g * a * g⁻¹ ∈ connectedComponent (1 : G)
    have hc : Continuous (fun x : G => g * x * g⁻¹) :=
      (continuous_const_mul g).mul_const g⁻¹
    have hm := hc.mapsTo_connectedComponent 1 ha
    simpa only [mul_one, mul_inv_cancel] using hm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SequenceRealExtension
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Extending a scale sequence without regularity assumptions

The geometric box lemmas use real scales. Arbitrary data on a strictly
increasing scale sequence extend by zero off that sequence, preserving
vanishing errors and subexponential upper bounds.
-/

noncomputable section
namespace PolycyclicRecognition

open Filter
open scoped Topology

/-- No interpolation or regularity of the envelope is required. -/
def sequenceRealExtension (scale : ℕ → ℝ) (f : ℕ → ℝ) (r : ℝ) : ℝ := by
  classical
  exact if h : ∃ n, scale n = r then f h.choose else 0

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_HaarPrefixCoordinates
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
attribute [-simp] _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Product Haar measure in increment and endpoint coordinates

The change `(u₁, …, uₕ) ↦ (u₁, u₁u₂, …, u₁⋯uₕ)` preserves product
Haar measure. Its inverse is the successive-difference map used in the
endpoint-tuple volume argument.
-/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]

def prefixShear (n : ℕ) : (G × (Fin n → G)) ≃ᵐ (G × (Fin n → G)) where
  toFun p := (p.1, fun i => p.1 * p.2 i)
  invFun p := (p.1, fun i => p.1⁻¹ * p.2 i)
  left_inv p := by ext i <;> simp
  right_inv p := by ext i <;> simp
  measurable_toFun := measurable_fst.prodMk (measurable_pi_iff.mpr
    (fun i => measurable_fst.mul ((measurable_pi_apply i).comp measurable_snd)))
  measurable_invFun := measurable_fst.prodMk (measurable_pi_iff.mpr
    (fun i => measurable_fst.inv.mul ((measurable_pi_apply i).comp measurable_snd)))

/-- Finite multiplication in successive endpoint coordinates, retaining
the first coordinate as the first increment. -/
def prefixCoordinateEquiv : (n : ℕ) → (Fin n → G) ≃ᵐ (Fin n → G)
  | 0 => MeasurableEquiv.refl _
  | n + 1 =>
    let split := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => G) 0
    split.trans (((MeasurableEquiv.refl G).prodCongr (prefixCoordinateEquiv n)).trans
      ((prefixShear n).trans split.symm))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SourceBundleStates
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
attribute [-simp] _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Passing bundle products to conjugated successive source states -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]

def sourceBundleStateEquiv (h : ℕ) (x : G) (φ : Fin h → G ≃ᵐ G) :
    (Fin h → G) ≃ᵐ (Fin h → G) :=
  (MeasurableEquiv.piCongrRight φ).trans
    ((prefixCoordinateEquiv h).trans (MeasurableEquiv.mulLeft (fun _ : Fin h => x)))

@[simp] theorem sourceBundleStateEquiv_apply (h : ℕ) (x : G) (φ : Fin h → G ≃ᵐ G)
    (u : Fin h → G) (i : Fin h) :
    sourceBundleStateEquiv h x φ u i = x * prefixCoordinateEquiv h (fun j => φ j (u j)) i := rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SpectralUnitGroup
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives
attribute [-simp] _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finitely generated group of nonzero spectral values

We include the conjugate eigenvalues so the resulting group has its actual
conjugation involution, independently of a later choice of logarithm.
-/

noncomputable section
namespace PolycyclicRecognition

variable {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

def spectralUnits (S : Module.End ℂ V) : Set ℂˣ :=
  {z | S.HasEigenvalue (z : ℂ)}

def spectralUnitGroup (S : Module.End ℂ V) : Subgroup ℂˣ :=
  Subgroup.closure (spectralUnits S ∪ star '' spectralUnits S)

omit [FiniteDimensional ℂ V] in
theorem spectralUnitGroup_star (S : Module.End ℂ V) {z : ℂˣ}
    (hz : z ∈ spectralUnitGroup S) : star z ∈ spectralUnitGroup S := by
  induction hz using Subgroup.closure_induction with
  | mem z hz =>
    rcases hz with hz | ⟨w, hw, rfl⟩
    · exact Subgroup.subset_closure (Or.inr ⟨z, hz, rfl⟩)
    · have hw' : w ∈ spectralUnitGroup S := Subgroup.subset_closure (Or.inl hw)
      simpa only [star_star] using hw'
  | one => simp
  | mul x y _ _ hx hy =>
    simpa only [star_mul] using (spectralUnitGroup S).mul_mem hy hx
  | inv x _ hx => simpa only [star_inv] using (spectralUnitGroup S).inv_mem hx

def spectralUnitConjugation (S : Module.End ℂ V) : spectralUnitGroup S →* spectralUnitGroup S where
  toFun z := ⟨star z.val, spectralUnitGroup_star S z.property⟩
  map_one' := by apply Subtype.ext; exact star_one _
  map_mul' x y := by apply Subtype.ext; simp [star_mul, mul_comm]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SpectralLogValue
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives
attribute [-simp] _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Scalar values of a compatible spectral logarithm -/

noncomputable section
namespace PolycyclicRecognition
variable {V : Type} [AddCommGroup V] [Module ℂ V]

def spectralLogValue (S : Module.End ℂ V)
    (L : spectralUnitGroup S →* Multiplicative ℂ) (z : ℂ) : ℂ := by
  classical
  exact if hz : z ≠ 0 then
    if hm : Units.mk0 z hz ∈ spectralUnitGroup S then (L ⟨Units.mk0 z hz, hm⟩).toAdd else 0
  else 0

theorem spectralLogValue_unit (S : Module.End ℂ V)
    (L : spectralUnitGroup S →* Multiplicative ℂ) (z : spectralUnitGroup S) :
    spectralLogValue S L (z.val : ℂ) = (L z).toAdd := by
  simp [spectralLogValue, Units.ne_zero z.val, z.property]

theorem spectralLogValue_mul (S : Module.End ℂ V)
    (L : spectralUnitGroup S →* Multiplicative ℂ) (z w : spectralUnitGroup S) :
    spectralLogValue S L ((z.val : ℂ) * (w.val : ℂ)) =
      spectralLogValue S L (z.val : ℂ) + spectralLogValue S L (w.val : ℂ) := by
  have h := spectralLogValue_unit S L (z * w)
  simpa only [Subgroup.coe_mul, Units.val_mul, spectralLogValue_unit,
    map_mul, toAdd_mul] using h

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_TupleLiftProjection
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Projection of thickened endpoint tuples into increment coordinates

Bounding the auxiliary coordinates costs at most their product volume.
The subsequent change from total nilpotent coordinates to increments is
Haar preserving, including for noncommutative nilpotent groups.
-/

noncomputable section
namespace PolycyclicRecognition

open Set MeasureTheory
open scoped ENNReal

variable {N D : Type*} [Group N] [TopologicalSpace N] [T2Space N]
  [SecondCountableTopology N] [MeasurableSpace N] [BorelSpace N]
  [MeasurableMul₂ N] [MeasurableInv N] [TopologicalSpace D] [MeasurableSpace D]

def tupleIncrementRegion (h : ℕ) (K : Set ((Fin h → N) × D)) : Set (Fin h → N) :=
  (prefixCoordinateEquiv h).symm '' (Prod.fst '' K)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_UniformPolynomialGrowth
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform polynomial growth over compact coefficient families -/

noncomputable section
namespace PolycyclicRecognition

open MvPolynomial Set
open scoped BigOperators

theorem finite_bounded_exponents (m D : ℕ) :
    {s : Fin m →₀ ℕ | ∀ i, s i ≤ D}.Finite :=
  ((Set.Finite.pi' (fun _ : Fin m => Set.finite_le_nat D)).preimage
    DFunLike.coe_injective.injOn)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_UnitSeparatedNet
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
attribute [-simp] _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The locally finite unit net used for Lipschitz replacement -/

noncomputable section
namespace PolycyclicRecognition

open Set Metric

variable {X : Type*} [MetricSpace X]

/-- Compact sets contain only finitely many points of a unit-separated set. -/
theorem finite_separated_subset_of_compact {V K : Set X}
    (hV : V.Pairwise (fun x y => 1 < dist x y)) (hK : IsCompact K) (hVK : V ⊆ K) :
    V.Finite := by
  classical
  obtain ⟨C, hC, hcover⟩ := Metric.totallyBounded_iff.mp hK.totallyBounded (1 / 3 : ℝ) (by norm_num)
  have hc (x : V) : ∃ c : C, dist (x : X) c < 1 / 3 := by
    have h := hcover (hVK x.property)
    rcases mem_iUnion.mp h with ⟨c, h⟩
    rcases mem_iUnion.mp h with ⟨hc, h⟩
    exact ⟨⟨c, hc⟩, mem_ball.mp h⟩
  choose c hc using hc
  have hinj : Function.Injective c := by
    intro x y he
    apply Subtype.ext
    by_contra hne
    have hsep := hV x.property y.property hne
    have htri := dist_triangle (x : X) (c x : X) y
    have hx := hc x
    have hy := hc y
    rw [← he] at hy
    rw [dist_comm (c x : X) y] at htri
    linarith
  let : Finite C := hC.to_subtype
  let : Finite V := Finite.of_injective c hinj
  exact Set.toFinite V

/-- Every bounded part of the net is finite, giving the local finiteness
needed to glue the cutoff partitions. -/
theorem finite_unit_net_ball [ProperSpace X] {V : Set X}
    (hV : V.Pairwise (fun x y => 1 < dist x y)) (x : X) (R : ℝ) :
    (V ∩ Metric.closedBall x R).Finite :=
  finite_separated_subset_of_compact (hV.mono inter_subset_left)
    (isCompact_closedBall x R) inter_subset_right

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_UnitNetPartition
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
attribute [-simp] _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finitely supported cutoff weights on the infinite unit net -/

noncomputable section
namespace PolycyclicRecognition

open Set Metric
open scoped BigOperators

variable {X : Type*} [MetricSpace X] [ProperSpace X]
  {V : Set X} (hV : V.Pairwise (fun x y => 1 < dist x y))

include hV in
theorem finite_subtype_unit_net_ball (x : X) (R : ℝ) :
    {v : V | dist x v ≤ R}.Finite := by
  have h := (finite_unit_net_ball hV x R).preimage_embedding (Function.Embedding.subtype V)
  apply h.subset
  intro v hv
  change dist x v.val ≤ R at hv
  refine ⟨v.property, ?_⟩
  change dist v.val x ≤ R
  simpa only [dist_comm] using hv

def unitNetMass (x : X) : V →₀ ℝ :=
  Finsupp.ofSupportFinite (fun v => max 0 (2 - dist x v)) (by
    apply (finite_subtype_unit_net_ball hV x 2).subset
    intro v hv
    change max 0 (2 - dist x v) ≠ 0 at hv
    change dist x v ≤ 2
    by_contra hn
    apply hv
    exact max_eq_left (by linarith))

@[simp] theorem unitNetMass_apply (x : X) (v : V) :
    unitNetMass hV x v = max 0 (2 - dist x v) := rfl

def unitNetTotal (x : X) : ℝ := (unitNetMass hV x).sum (fun _ a => a)

def unitNetPartition (x : X) : V →₀ ℝ :=
  (unitNetTotal hV x)⁻¹ • unitNetMass hV x

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_UnitaryCocycle
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete cocycles for bundled unitary representations

The bundled form lets central restriction and quotient descent use their
actual representations without changing ambient scalar-action instances.
-/

noncomputable section

namespace PolycyclicRecognition

variable {G E F : Type*} [Group G]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

@[instance_reducible]
def unitaryDistribMulAction (ρ : G →* (E ≃ₗᵢ[ℝ] E)) : DistribMulAction G E where
  smul g x := ρ g x
  one_smul x := by change ρ 1 x = x; rw [map_one]; rfl
  mul_smul g h x := by change ρ (g * h) x = ρ g (ρ h x); rw [map_mul]; rfl
  smul_zero g := map_zero (ρ g)
  smul_add g := map_add (ρ g)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_UnitaryMautner
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed vectors and contracted elements

The fixed-vector case of Cornulier--Tessera, Lemma 5.2. The proof uses only
strong continuity and the isometry identity, with explicit contracting
sequences. The closed subgroup generated by these elements then has the
same fixed vectors as the contracting subgroup.
-/

noncomputable section

namespace PolycyclicRecognition

open Filter Set
open scoped Topology

variable {G E : Type*} [Group G] [TopologicalSpace G]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  (ρ : G →* (E ≃ₗᵢ[ℝ] E))

def unitaryStabilizer (v : E) : Subgroup G where
  carrier := {g | ρ g v = v}
  one_mem' := by change ρ 1 v = v; rw [ρ.map_one]; rfl
  mul_mem' := by
    intro g h hg hh
    change ρ (g * h) v = v
    rw [ρ.map_mul]
    change ρ g (ρ h v) = v
    rw [hh, hg]
  inv_mem' := by
    intro g hg
    have he := congrArg (fun w => ρ g⁻¹ w) hg
    have hi : ρ g⁻¹ * ρ g = 1 := by rw [← ρ.map_mul, inv_mul_cancel, ρ.map_one]
    change (ρ g⁻¹ * ρ g) v = ρ g⁻¹ v at he
    rw [hi] at he
    exact he.symm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_WordLengthFiltration
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Word-length filtration for a nilpotent generated algebra

Left multiplication raises word length; a derivation carrying generators to
generators preserves it. This separates the nilpotent and semisimple parts
of the finite solvable representation.
-/

noncomputable section
namespace PolycyclicRecognition

variable {A ι : Type*} [Ring A] [Algebra ℝ A] (j : ι → A)

def wordLengthSpan (k : ℕ) : Submodule ℝ A :=
  Submodule.span ℝ {a | ∃ l : List ι, k ≤ l.length ∧ (l.map j).prod = a}

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_BackwardSwitchProbability
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Probability of retaining every intermediate sheet -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set
open scoped ENNReal NNReal

variable {G : Type*} [Group G] [MeasurableSpace G]

/-- Iterate the actual independent pairs of increment samples, killing a
path at its first exit from the prescribed next set. -/
def survivingSwitchProbability (σ : ℕ → Measure G) (S : ℕ → Set G) :
    ℕ → ℕ → G → ℝ≥0∞
  | _, 0, _ => 1
  | n, k + 1, x => ∫⁻ s₁, ∫⁻ s₂,
      (S (n + 1)).indicator (survivingSwitchProbability σ S (n + 1) k)
        (x * s₁ * s₂⁻¹) ∂σ n ∂σ n

/-- The product of the successive transition thresholds, in the same
recursive order as the independent sampling. -/
def switchThresholdProduct (τ : ℕ → ℝ≥0) : ℕ → ℕ → ℝ≥0∞
  | _, 0 => 1
  | n, k + 1 => τ n * switchThresholdProduct τ (n + 1) k

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RootFlow
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Logarithmic distortion in Cartan root spaces

Generalized root spaces determine the nilpotent correction to the scalar
weight action. A compatible group conjugation identity then gives logarithmic
distortion.
-/

noncomputable section

namespace PolycyclicRecognition

open LieAlgebra LieModule

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]
  [FiniteDimensional ℝ L]
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra] (χ : Weight ℝ H L)

/-- Fixed linear coordinates put a compatible norm on the root space. -/
def rootCoordinates : (rootSpace H χ) ≃ₗ[ℝ]
    (Fin (Module.finrank ℝ (rootSpace H χ)) → ℝ) :=
  (Module.finBasis ℝ (rootSpace H χ)).equivFun

local instance rootNormedAddCommGroup : NormedAddCommGroup (rootSpace H χ) :=
  NormedAddCommGroup.induced _ _ (rootCoordinates H χ).toLinearMap
    (rootCoordinates H χ).injective

local instance rootNormedSpace : NormedSpace ℝ (rootSpace H χ) :=
  NormedSpace.induced ℝ _ _ (rootCoordinates H χ).toLinearMap

local instance rootNontrivial : Nontrivial (rootSpace H χ) :=
  (LieSubmodule.nontrivial_iff_ne_bot ℝ H L).mpr χ.genWeightSpace_ne_bot

/-- The actual adjoint action on a Cartan generalized root space. -/
def rootAction (h : H) : (rootSpace H χ) →L[ℝ] (rootSpace H χ) :=
  Module.End.toContinuousLinearMap (𝕜 := ℝ) (rootSpace H χ) (toEnd ℝ H (rootSpace H χ) h)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanResidualAction
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial bounds for the residual Cartan action

On an actual generalized root space, subtracting its scalar character leaves
an operator nilpotent in a uniform dimension bound. Its exponential therefore
has polynomial growth in the Cartan parameter. This supplies the residual
operator estimate used in box conjugation.
-/

noncomputable section

namespace PolycyclicRecognition

open LieAlgebra LieModule Module

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra] (χ : Weight ℝ H L)

local instance instNormedAddCommGroupSubtypeMemLieSubmoduleRealLieSubalgebraRootSpaceCoeWeight_solutions : NormedAddCommGroup (rootSpace H χ) :=
  NormedAddCommGroup.induced _ _ (rootCoordinates H χ).toLinearMap
    (rootCoordinates H χ).injective
local instance instNormedSpaceRealSubtypeMemLieSubmoduleLieSubalgebraRootSpaceCoeWeight_solutions : NormedSpace ℝ (rootSpace H χ) :=
  NormedSpace.induced ℝ _ _ (rootCoordinates H χ).toLinearMap

local instance instNontrivialSubtypeMemLieSubmoduleRealLieSubalgebraRootSpaceCoeWeight_solutions_r784cef_1 : Nontrivial (rootSpace H χ) :=
  (LieSubmodule.nontrivial_iff_ne_bot ℝ H L).mpr χ.genWeightSpace_ne_bot
set_option maxHeartbeats 1000000 in
/-- Dependence of the residual operator on the Cartan parameter is linear. -/
def rootResidualLinear : H →ₗ[ℝ] ((rootSpace H χ) →L[ℝ] (rootSpace H χ)) where
  toFun h := rootAction H χ h - χ h • 1
  map_add' h k := by
    change Module.End.toContinuousLinearMap (𝕜 := ℝ) (rootSpace H χ)
      (toEnd ℝ H (rootSpace H χ) (h + k)) - χ (h + k) • 1 = _
    simp only [map_add, add_smul, rootAction]
    abel
  map_smul' a h := by
    change Module.End.toContinuousLinearMap (𝕜 := ℝ) (rootSpace H χ)
      (toEnd ℝ H (rootSpace H χ) (a • h)) - χ (a • h) • 1 = _
    simp only [map_smul, smul_sub, smul_smul, RingHom.id_apply]
    rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanResidualBounds
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounds for the actual residual automorphism

We identify the residual automorphism on a nonzero root with the analytic
exponential already estimated there. This removes a separate bound premise
for the automorphisms constructed from the Cartan action.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieAlgebra LieModule
open scoped BigOperators

variable {L : Type*}
  [LieRing L]
  [LieAlgebra ℝ L]
  [FiniteDimensional ℝ L]
  {n : ℕ}
  (H : LieSubalgebra ℝ L)
  [H.IsCartanSubalgebra]
  (χ : Weight ℝ H L)
  (hχ : χ.IsNonZero)

local instance instNormedAddCommGroupSubtypeMemLieSubmoduleRealLieSubalgebraRootSpaceCoeWeight_solutions_1 : NormedAddCommGroup (rootSpace H χ) :=
  NormedAddCommGroup.induced _ _ (rootCoordinates H χ).toLinearMap
    (rootCoordinates H χ).injective
local instance instNormedSpaceRealSubtypeMemLieSubmoduleLieSubalgebraRootSpaceCoeWeight_solutions_1 : NormedSpace ℝ (rootSpace H χ) :=
  NormedSpace.induced ℝ _ _ (rootCoordinates H χ).toLinearMap

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RootRepresentation
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Root distortion in a faithful integrated representation

The conjugation identity is proved from a Lie homomorphism into a normed
algebra and the ordinary exponential matching identities. It is not an
additional geometric hypothesis.
-/

noncomputable section

namespace PolycyclicRecognition

open LieAlgebra LieModule

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] rootNormedAddCommGroup rootNormedSpace rootNontrivial

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra] (χ : Weight ℝ H L)
  (j : L →ₗ⁅ℝ⁆ A)

def representedRootVector : (rootSpace H χ) →L[ℝ] A :=
  (show (rootSpace H χ) →ₗ[ℝ] A from
    { toFun := fun v => j v
      map_add' := fun x y => j.map_add x y
      map_smul' := fun r x => j.map_smul r x }).toContinuousLinearMap

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanAdjointAction
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full exponential Cartan action

The scalar dilation and the polynomial residual automorphism together give
the exponential of the actual adjoint action on every nonzero root. In a
compatible faithful representation this is conjugation, not an independently
assumed action on the nilpotent ideal.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieAlgebra LieModule

variable {L : Type*}
  [LieRing L]
  [LieAlgebra ℝ L]
  [FiniteDimensional ℝ L]
  {n : ℕ}
  (H : LieSubalgebra ℝ L)
  [H.IsCartanSubalgebra]

variable (χ : Weight ℝ H L) (hχ : χ.IsNonZero)

local instance instNormedAddCommGroupSubtypeMemLieSubmoduleRealLieSubalgebraRootSpaceCoeWeight_solutions_2 : NormedAddCommGroup (rootSpace H χ) :=
  NormedAddCommGroup.induced _ _ (rootCoordinates H χ).toLinearMap
    (rootCoordinates H χ).injective
local instance instNormedSpaceRealSubtypeMemLieSubmoduleLieSubalgebraRootSpaceCoeWeight_solutions_2 : NormedSpace ℝ (rootSpace H χ) :=
  NormedSpace.induced ℝ _ _ (rootCoordinates H χ).toLinearMap

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CoarsePathWords
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
attribute [-simp] _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Subdividing coarse paths into bounded-increment words

A path with speed `L` and additive error `κ` admits a unit-step word of
length at most `(L + 1) * (κ + 2)`. Its prefixes remain within `κ + 2` of
points on the path. In the application `L = O(r)` and `κ = O(log r)`, so this
loss is polynomial and its extra height error is sublinear.
-/

noncomputable section

namespace PolycyclicRecognition

open Metric Set

/-- The uniform subdivision of the unit interval, constant after its endpoint. -/
def subdivisionPoint (n : ℕ) (hn : 0 < n) (i : ℕ) : unitInterval :=
  ⟨((min i n : ℕ) : ℝ) / n, by
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    constructor
    · positivity
    · exact (div_le_one hn').mpr (by exact_mod_cast Nat.min_le_right i n)⟩

@[simp] theorem subdivisionPoint_coe (n : ℕ) (hn : 0 < n) {i : ℕ} (hi : i ≤ n) :
    (subdivisionPoint n hn i : ℝ) = (i : ℝ) / n := by
  simp only [subdivisionPoint, Nat.min_eq_left hi]

@[simp] theorem subdivisionPoint_zero (n : ℕ) (hn : 0 < n) :
    subdivisionPoint n hn 0 = 0 := by
  apply Subtype.ext
  simp

@[simp] theorem subdivisionPoint_self (n : ℕ) (hn : 0 < n) :
    subdivisionPoint n hn n = 1 := by
  apply Subtype.ext
  simp [ne_of_gt hn]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CompactGeneratingBalls
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
attribute [-simp] _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Compatibility with OpenAI's Mathlib (d13f23b): the word API of `Group.Generators`
(`Mathlib/Geometry/Group/WordProd.lean` and `WordMetric.lean` there). -/

namespace OAI

/-! # Compact bounds for words in a compact symmetric generating set -/

noncomputable section
namespace PolycyclicRecognition

open Set
open scoped Pointwise

variable {G : Type*} [Group G] (K : Set G) (hK : Subgroup.closure K = ⊤)
  (hsymm : ∀ g : G, g⁻¹ ∈ K ↔ g ∈ K)

theorem isCompact_set_pow [TopologicalSpace G] [ContinuousMul G]
    (hcompact : IsCompact K) (n : ℕ) : IsCompact (K ^ n) := by
  induction n with
  | zero => simp
  | succ n ih => simpa only [pow_succ] using ih.mul hcompact

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_RescaledAffineComparison
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Deterministic comparison through a change of scale

Two ordinary sampling laws need not agree. Their mixed comparison and the
exact change of coordinates suffice to compare the deterministic affine
approximations. Finite separation then identifies their linear parts.
-/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Filter Set
open scoped Topology ENNReal

/-- The operator on compact profiles induced by a change of chart. -/
def rescaleCompactProfile {Z W : Type*} [TopologicalSpace Z] [CompactSpace Z]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (t : ℝ) (φ : C(Z, Z)) (f : C(Z, W)) : C(Z, W) := t • f.comp φ

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ExactProfileTransport
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Deterministic affine comparison after an exact change of chart -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Filter
open scoped Topology ENNReal

/-- Restriction to a changed compact chart, scalar normalization and the
constant change of center. -/
def transportCompactProfile
    {Z Z' W : Type*} [TopologicalSpace Z] [TopologicalSpace Z']
    [CompactSpace Z] [CompactSpace Z'] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (t : ℝ) (ψ : C(Z, Z')) (c : W) (f : C(Z', W)) : C(Z, W) :=
  t • f.comp ψ + ContinuousMap.const Z c

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_FiniteKernelCoarseEquivalence
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite kernels do not change the discrete group coarse structure -/
noncomputable section
namespace PolycyclicRecognition
variable {G Q : Type*} [Group G] [Group Q]

theorem finite_kernel_preimage_finite (q : G →* Q) [Finite q.ker]
    (S : Set Q) (hS : S.Finite) : (q ⁻¹' S).Finite := by
  apply hS.preimage'
  intro y _
  by_cases h : ∃ g, q g = y
  · obtain ⟨g, hg⟩ := h
    let f : (q ⁻¹' {y}) → q.ker := fun x => ⟨g⁻¹ * x,
      by change q (g⁻¹ * x) = 1; rw [map_mul, map_inv, hg, x.property]; exact inv_mul_cancel y⟩
    have hf : Function.Injective f := by
      intro x z hxz
      apply Subtype.ext
      exact mul_left_cancel (congrArg (fun a : q.ker => (a : G)) hxz)
    let : Finite (q ⁻¹' {y}) := Finite.of_injective f hf
    exact Set.toFinite _
  · have he : q ⁻¹' {y} = ∅ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      exact fun hx => h ⟨x, hx⟩
    rw [he]
    exact Set.finite_empty

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_FlatSwitchSamples
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The recursive independent sampling law on the flat parameter cube -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory

/-- The first block holds first samples and the second block holds second samples. -/
def flatSamplePairs (m : ℕ) (t : Fin (m + m) → ℝ) : Fin m → ℝ × ℝ :=
  fun j => (t (Fin.castAdd m j), t (Fin.natAdd m j))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_HaarProduct
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Factoring a measure along Haar fibers

A measure finite on compact subsets of a compact section times a group,
and invariant under translations of the group coordinate, is a product.
The section measure is obtained by averaging over a set of positive finite
Haar measure, never by restricting to a single fiber.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set
open scoped ENNReal Pointwise

variable {G X : Type*} [MeasurableSpace G] [MeasurableSpace X]
  (M : Measure (X × G))

/-- The group measure cut out by a measurable subset of the compact section. -/
def haarFiberSlice (E : Set X) : Measure G :=
  (M.restrict (E ×ˢ univ)).map Prod.snd

/-- Average the coupling over a fixed finite Haar region to define its
section measure. -/
def haarSectionMeasure (m : Measure G) (B : Set G) : Measure X :=
  (m B)⁻¹ • (M.restrict (univ ×ˢ B)).map Prod.fst

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_InvariantMetrization
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
attribute [-simp] _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A compatible left-invariant metric

Take the supremum of the bounded metric over left translations. The left
uniformity makes this supremum compatible with the original topology.
This supplies the metrization step in the proper chain-metric construction.
-/

noncomputable section
namespace PolycyclicRecognition

open Set Filter Metric Topology
open scoped Uniformity

variable {G : Type*} [Group G] [MetricSpace G]

/-- The bounded supremum over all left translations of a given metric. -/
def leftInvariantDistance (x y : G) : ℝ :=
  ⨆ g : G, min 1 (dist (g * x) (g * y))

theorem translateDistance_bdd (x y : G) :
    BddAbove (Set.range (fun g : G => min 1 (dist (g * x) (g * y)))) :=
  ⟨1, by rintro _ ⟨g, rfl⟩; exact min_le_left _ _⟩

theorem min_dist_le_leftInvariantDistance (x y : G) :
    min 1 (dist x y) ≤ leftInvariantDistance x y := by
  simpa only [one_mul, leftInvariantDistance] using le_ciSup (translateDistance_bdd x y) (1 : G)

@[simp] theorem leftInvariantDistance_self (x : G) : leftInvariantDistance x x = 0 := by
  simp [leftInvariantDistance]

theorem leftInvariantDistance_comm (x y : G) :
    leftInvariantDistance x y = leftInvariantDistance y x := by
  simp only [leftInvariantDistance, dist_comm]

theorem min_one_add_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    min 1 (a + b) ≤ min 1 a + min 1 b := by
  by_cases h : a ≤ 1
  · by_cases h' : b ≤ 1
    · simpa only [min_eq_right h, min_eq_right h'] using min_le_right 1 (a + b)
    · rw [min_eq_right h, min_eq_left (le_of_not_ge h')]
      exact (min_le_left _ _).trans (by linarith)
  · rw [min_eq_left (le_of_not_ge h)]
    exact (min_le_left _ _).trans (by have := le_min (by norm_num : (0 : ℝ) ≤ 1) hb; linarith)

theorem leftInvariantDistance_triangle (x y z : G) :
    leftInvariantDistance x z ≤ leftInvariantDistance x y + leftInvariantDistance y z := by
  apply ciSup_le
  intro g
  exact (min_le_min_left 1 (dist_triangle (g * x) (g * y) (g * z))).trans
    ((min_one_add_le _ _ dist_nonneg dist_nonneg).trans
      (add_le_add (le_ciSup (translateDistance_bdd x y) g)
        (le_ciSup (translateDistance_bdd y z) g)))

section LeftUniform
variable [IsLeftUniformGroup G]

/-- All left translations are equicontinuous for a metric inducing the left uniformity. -/
theorem leftTranslations_uniform_control {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x y : G, dist x y < δ → ∀ g : G, dist (g * x) (g * y) < ε := by
  have h : {p : G × G | dist p.1 p.2 < ε} ∈
      Filter.comap (fun p : G × G => p.1⁻¹ * p.2) (𝓝 (1 : G)) := by
    rw [← uniformity_eq_comap_inv_mul_nhds_one G]
    exact dist_mem_uniformity hε
  obtain ⟨U, hU, hsub⟩ := h
  have hpre : (fun p : G × G => p.1⁻¹ * p.2) ⁻¹' U ∈ 𝓤 G := by
    rw [uniformity_eq_comap_inv_mul_nhds_one G]
    exact preimage_mem_comap hU
  obtain ⟨δ, hδ, hcontrol⟩ := mem_uniformity_dist.mp hpre
  refine ⟨δ, hδ, ?_⟩
  intro x y hxy g
  exact hsub (show (g * x, g * y) ∈ (fun p : G × G => p.1⁻¹ * p.2) ⁻¹' U by
    simpa [mul_assoc] using hcontrol hxy)

theorem leftInvariantDistance_topology (s : Set G) :
    IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0, ∀ y, leftInvariantDistance x y < ε → y ∈ s := by
  rw [Metric.isOpen_iff]
  constructor
  · intro hs x hx
    obtain ⟨r, hr, hball⟩ := hs x hx
    refine ⟨min 1 r, lt_min zero_lt_one hr, ?_⟩
    intro y hy
    have hmin := (min_dist_le_leftInvariantDistance x y).trans_lt hy
    have hdist : dist x y < r := by
      rcases lt_min_iff.mp hmin with ⟨h1, hr'⟩
      rcases min_lt_iff.mp h1 with h | h
      · exact False.elim ((lt_irrefl (1 : ℝ)) h)
      · simpa only [min_eq_right (le_of_lt h)] using hr'
    exact hball (by simpa only [mem_ball, dist_comm] using hdist)
  · intro hs x hx
    obtain ⟨ε, hε, hball⟩ := hs x hx
    obtain ⟨δ, hδ, hcontrol⟩ := leftTranslations_uniform_control (G := G) (half_pos hε)
    refine ⟨δ, hδ, ?_⟩
    intro y hy
    apply hball y
    have hxy : dist x y < δ := by simpa only [mem_ball, dist_comm] using hy
    have hsup : leftInvariantDistance x y ≤ ε / 2 :=
      ciSup_le (fun g => (min_le_right _ _).trans (hcontrol x y hxy g).le)
    exact hsup.trans_lt (half_lt_self hε)

/-- The left-invariant metric with exactly the original topology. -/
@[instance_reducible]
def leftInvariantMetric : MetricSpace G :=
  MetricSpace.ofDistTopology leftInvariantDistance leftInvariantDistance_self
    leftInvariantDistance_comm leftInvariantDistance_triangle leftInvariantDistance_topology
    (by
      intro x y hxy
      have h := min_dist_le_leftInvariantDistance x y
      rw [hxy] at h
      have hd : dist x y ≤ 0 := (min_le_iff.mp h).resolve_left (by norm_num)
      exact dist_le_zero.mp hd)

end LeftUniform

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.Thompson_FiniteAverage
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
attribute [-simp] _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Real finite averages and left-translation cancellation

These are literal finite sums. The translation estimate cancels the common
intersection of the two finite sets, and the function bound is global. No
invariant mean, support assumption, or limiting average is used.
-/

noncomputable section

universe uα uι uG

namespace ThompsonNonamenability

open scoped BigOperators symmDiff

variable {α : Type uα} {ι : Type uι}

section Translation

variable {G : Type uG} [Group G] [DecidableEq G]

def leftTranslate (h : G) (A : Finset G) : Finset G := A.image (fun g => h * g)

def boundaryRatio (A : Finset G) (h : G) : ℝ :=
  ((leftTranslate h A ∆ A).card : ℝ) / (A.card : ℝ)

@[simp] theorem card_leftTranslate (h : G) (A : Finset G) :
    (leftTranslate h A).card = A.card :=
  Finset.card_image_of_injective A (fun _ _ hxy => mul_left_cancel hxy)

end Translation

end ThompsonNonamenability

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.Thompson_FiniteLevels
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
attribute [-simp] _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite scalar levels

The distinct values of a nonnegative function on a finite set, together with
zero, give a finite subdivision. Its positive gaps reconstruct every value
and every absolute difference by strict superlevel indicators. These are
finite sums, including when the only level is zero.
-/

open scoped BigOperators

universe uG

namespace ThompsonNonamenability

variable {G : Type uG}

/-- The actual ordered levels of `p` on `K`, with zero included. -/
structure FiniteLevelChain (K : Finset G) (p : G → ℝ) where
  n : ℕ
  value : Fin (n + 1) → ℝ
  value_zero : value 0 = 0
  strictMono_value : StrictMono value
  image_value_eq : Finset.univ.image value = insert 0 (K.image p)

namespace FiniteLevelChain

/-- Construct the level chain by sorting the actual finite image. -/
noncomputable def ofNonneg (K : Finset G) (p : G → ℝ)
    (hp : ∀ x ∈ K, 0 ≤ p x) : FiniteLevelChain K p := by
  classical
  let L : Finset ℝ := insert 0 (K.image p)
  have hpos : 0 < L.card := Finset.card_pos.mpr ⟨0, by simp [L]⟩
  let n := L.card - 1
  have hcard : L.card = n + 1 := by dsimp [n]; omega
  let e : Fin (n + 1) ↪o ℝ := L.orderEmbOfFin hcard
  have heimage : Finset.univ.image e = L :=
    Finset.image_orderEmbOfFin_univ L hcard
  have hnonneg : ∀ a ∈ L, 0 ≤ a := by
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact le_rfl
    · rcases Finset.mem_image.mp ha with ⟨x, hx, rfl⟩
      exact hp x hx
  have hezero : e 0 = 0 := by
    have hz : (0 : ℝ) ∈ Finset.univ.image e := by
      rw [heimage]
      simp [L]
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hz
    apply le_antisymm
    · calc
        e 0 ≤ e j := e.monotone (Fin.zero_le j)
        _ = 0 := hj
    · exact hnonneg (e 0) (Finset.orderEmbOfFin_mem L hcard 0)
  exact ⟨n, e, hezero, e.strictMono, heimage⟩

variable {K : Finset G} {p : G → ℝ} (c : FiniteLevelChain K p)

/-- Width of the interval immediately above the indexed level. -/
def gap (i : Fin c.n) : ℝ := c.value i.succ - c.value i.castSucc

end FiniteLevelChain

end ThompsonNonamenability

end OAI
end

section
-- module Solutions.OAIQ093_PR.Thompson_FiniteCoarea
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe uG

namespace ThompsonNonamenability

open scoped BigOperators symmDiff

variable {G : Type uG} [DecidableEq G]

namespace FiniteLevelChain

variable {K : Finset G} {p : G → ℝ}

/-- The strict superlevel set at the lower endpoint of a positive layer. -/
def levelSet (c : FiniteLevelChain K p) (i : Fin c.n) : Finset G := by
  classical
  exact K.filter (fun x => c.value i.castSucc < p x)

end FiniteLevelChain

end ThompsonNonamenability

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.Thompson_ProbabilityDefects
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
attribute [-simp] _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite probabilities and their simultaneous translation defects

One ℓ¹ space on `S × G` carries the sum of all translation defects.  In
particular its norm is the exact finite sum, without a factor depending on
`S.card`.  This is the finite-probability input to the separation argument.
-/

noncomputable section

open scoped BigOperators Classical

universe uG uι

namespace ThompsonNonamenability

variable {G : Type uG}

/-- The total mass of a finitely supported real function. -/
def mass : (G →₀ ℝ) →ₗ[ℝ] ℝ :=
  Finsupp.linearCombination ℝ (fun _ : G => (1 : ℝ))

@[simp]
theorem mass_apply (p : G →₀ ℝ) : mass p = ∑ g ∈ p.support, p g := by
  simp [mass, Finsupp.linearCombination_apply, Finsupp.sum]

@[simp]
theorem mass_single (g : G) (a : ℝ) : mass (Finsupp.single g a) = a := by
  simp [mass]

/-- Nonnegative finite weights with total mass one. -/
def IsProbabilityWeights (p : G →₀ ℝ) : Prop :=
  (∀ g, 0 ≤ p g) ∧ mass p = 1

/-- The simultaneous defects use the ℓ¹ norm on the product index set. -/
abbrev DefectSpace (S : Finset G) := lp (fun _ : ({h // h ∈ S} × G) => ℝ) 1

variable [Group G]

/-- Translation defect of the point probability at `g`. -/
def diracDefect (S : Finset G) (g : G) : DefectSpace S :=
  ∑ h : S, (lp.single 1 (h, h.val * g) (1 : ℝ) - lp.single 1 (h, g) (1 : ℝ))

/-- The linear extension of the point-probability defects. -/
def defectMap (S : Finset G) : (G →₀ ℝ) →ₗ[ℝ] DefectSpace S :=
  Finsupp.linearCombination ℝ (diracDefect S)

@[simp]
theorem defectMap_single (S : Finset G) (g : G) (a : ℝ) :
    defectMap S (Finsupp.single g a) = a • diracDefect S g := by
  simp [defectMap]

/-- The actual image of finite nonnegative probabilities under the defect map. -/
def defectSet (S : Finset G) : Set (DefectSpace S) :=
  defectMap S '' {p : G →₀ ℝ | IsProbabilityWeights p}

end ThompsonNonamenability

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.Thompson_MeanApproximation
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite probabilities approximately invariant under a finite set

The usual positive normalized invariant mean forces zero to lie in the
closure of the actual finite-probability defect set. The separation argument
uses bounded coordinate functions of a continuous linear functional on ℓ¹;
no identification of the full dual of ℓ¹ is assumed.
-/

noncomputable section

open scoped ENNReal BigOperators

universe uG

namespace ThompsonNonamenability

variable {G : Type uG} [Group G] [DecidableEq G]

local instance instFactLeENNRealOfNat_solutions : Fact (1 ≤ (1 : ℝ≥0∞)) := ⟨le_rfl⟩

end ThompsonNonamenability

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_MetricFolnerVolume
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The volume estimates in metric Følner transfer

A finite union of fixed-radius target balls has mass bounded below by its
source cardinality, using a separated net and bounded coarse multiplicity.
Its metric boundary is covered by balls indexed by the source boundary.
-/

noncomputable section

namespace PolycyclicRecognition

open Metric Set MeasureTheory
open scoped ENNReal

def metricFolnerSet {X Y : Type*} [PseudoMetricSpace Y]
    (u : X → Y) (E : Finset X) (a : ℝ) : Set Y :=
  ⋃ p ∈ E, ball (u p) a

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_NormalizedEndpointMeasure
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Normalized measure on an independent endpoint domain

Normalizing the restricted coordinate measure produces a probability on
the endpoint subtype. A bad set of probability below one half leaves at
least half of the original coordinate volume.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set
open scoped ENNReal

variable {V : Type*} [MeasurableSpace V]

/-- Probability normalization on the endpoint subtype. -/
def normalizedEndpointMeasure (μ : Measure V) (S : Set V) : Measure S :=
  (μ S)⁻¹ • μ.comap Subtype.val

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_OccupationCompactRestriction
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compactly supported starting densities in the profile argument -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Filter Set
open scoped Topology

/-- Evaluation at a fixed time is continuous in the topology of uniform
convergence on compact sets. -/
def flowTimeSlice {V : Type*} [TopologicalSpace V]
    (F : C(V × ℝ, V)) (T : ℝ) : C(V, V) :=
  F.comp ⟨fun z => (z, T), continuous_id.prodMk continuous_const⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ProfileFlowConvergence
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform evaluation of compact profile families along converging flows -/

noncomputable section

namespace PolycyclicRecognition

open Set Filter
open scoped Topology

variable {U V W : Type*} [TopologicalSpace U] [LocallyCompactSpace U]
  [TopologicalSpace V] [LocallyCompactSpace V] [PseudoMetricSpace W]

/-- Evaluate a profile and a coordinate map jointly on fixed profile and
parameter sets. -/
def profileAlongMap (S : Set C(V, W)) (K : Set U) (T : C(U, V)) : C(S × K, W) :=
  ⟨fun p => p.1.val (T p.2.val), continuous_eval.comp
    ((continuous_subtype_val.comp continuous_fst).prodMk
      (T.continuous.comp (continuous_subtype_val.comp continuous_snd)))⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ProfileIncrementLimits
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Supported increment constraints from actual converging chart flows -/

noncomputable section

namespace PolycyclicRecognition

open Set Filter MeasureTheory
open scoped Topology

variable {U V W : Type*} [TopologicalSpace U] [LocallyCompactSpace U]
  [TopologicalSpace V] [LocallyCompactSpace V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- A normalized increment of a profile between two coordinate maps. -/
def profileIncrementMap (S : Set C(V, W)) (K : Set U) (q : ℝ)
    (A T : C(U, V)) : C(S × K, W) :=
  q • (profileAlongMap S K T - profileAlongMap S K A)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_QuotientSectionRightHaar
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
attribute [-simp] _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Right Haar measure in quotient-section coordinates

Right translations translate each kernel fiber on the right. Consequently
the product of right Haar measures gives a right-invariant measure without
assuming that conjugation preserves the kernel measure. In a unimodular
ambient group, Haar uniqueness then gives left invariance as well.
-/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set

variable {N Q : Type*} [Group N] [Group Q]
  [TopologicalSpace N] [TopologicalSpace Q] [IsTopologicalGroup N] [IsTopologicalGroup Q]
  (π : N →* Q) (hπ : Continuous π) (s : C(Q, N)) (hs : ∀ q, π (s q) = q)

def quotientSectionRightCocycle (n : N) (q : Q) : π.ker :=
  ⟨s q * n * (s (q * π n))⁻¹, by simp [hs]⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_RetainedProbeAnchors
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Retaining the good anchors needed by measured packing -/

noncomputable section
namespace PolycyclicRecognition

open Filter Set

/-- Empty image tiles use the original neighboring sheet as anchor.
An occupied tile retains its exact geometric anchor. -/
def occupiedTileAnchor {G X : Type*} {m : ℕ}
    (points : Fin m → Finset X) (anchor : Fin m → G) (fallback : G) (j : Fin m) : G :=
  if (points j).Nonempty then anchor j else fallback

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SeparatedTupleVolume
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
attribute [-simp] _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Nilpotent increment volume from separated ambient endpoint tuples

Thickening chosen lifts gives disjoint cells even when the factor map has
a kernel. Projection discards only the volume of the bounded Cartan
coordinates; changing to increments preserves the remaining Haar volume.
-/

noncomputable section
namespace PolycyclicRecognition

open Set MeasureTheory
open scoped ENNReal

variable {N D G : Type*} [Group N] [Group D] [Group G]

def tupleFactorAction (φ : D →* MulAut N) (h : ℕ) :
    (Fin h → D) →* MulAut (Fin h → N) where
  toFun d := MulEquiv.piCongrRight (fun i => φ (d i))
  map_one' := by ext n i; simp
  map_mul' d e := by ext n i; simp

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_PolynomialDerivativeGrowth
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Derivative bounds on growing polynomial input cubes -/

noncomputable section
namespace PolycyclicRecognition

open MvPolynomial Set Metric
open scoped BigOperators

def polynomialMapDifferential {m n : ℕ} (p : Fin n → MvPolynomial (Fin m) ℝ)
    (x : Fin m → ℝ) : (Fin m → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi (fun i => polynomialDifferential (p i) x)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SourceBundleHaarImage
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Joint source-bundle Haar volume before conjugation

The polynomial image is taken in the product of all bundle coordinates.
Thus a correlated restriction of the common parameter set is retained.
-/

noncomputable section
namespace PolycyclicRecognition

open Module MeasureTheory Filter Set
open scoped Manifold Topology

variable {L I : Type*} [LieRing L] [LieAlgebra ℝ L] [Fintype I]
  {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [MeasurableSpace G] [BorelSpace G]

def sourceBundleProduct {m h M : ℕ}
    (lie : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (X : I → L) (s : I → ℝ)
    (letters : Fin m → I)
    (input : (Fin M → ℝ) ≃L[ℝ] (Fin h → Fin (m + m) → ℝ)) (r : ℝ)
    (t : Fin M → ℝ) : Fin h → G := fun j =>
  (List.ofFn (fun k : Fin m => Exp (lie
    (((input t j) (Fin.castAdd m k) - (input t j) (Fin.natAdd m k)) •
      (Real.exp (r * s (letters k)) • X (letters k)))))).prod

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SuccessfulSampleBlockPaths
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Separate geometric paths for successive sampled bundles -/

noncomputable section
namespace PolycyclicRecognition

open Set

variable {N G : Type*} [Group N] [Group G]

/-- The actual difference word of one block of the global sample vector. -/
def sampledBlockWord {h m : ℕ} (sample : ℕ → ℝ → N)
    (t : Fin (h * m + h * m) → ℝ) (i : Fin h) : List N :=
  List.ofFn (fun j : Fin m => sample (finProdFinEquiv (i, j)).val
    (t (Fin.castAdd (h * m) (finProdFinEquiv (i, j))) -
      t (Fin.natAdd (h * m) (finProdFinEquiv (i, j)))))

/-- Products of complete sampled blocks, extended by the identity. -/
def sampledBlockProducts {h m : ℕ} (sample : ℕ → ℝ → N)
    (t : Fin (h * m + h * m) → ℝ) (j : ℕ) : N :=
  if hj : j < h then (sampledBlockWord sample t ⟨j, hj⟩).prod else 1

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SupportSymmetries
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
attribute [-simp] _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The actual finite group of height labels

The segment support determines a finite spanning body in the dual. A linear
support isometry preserves that body and hence permutes its vertices. This
proves finiteness of the group used to label stationary slopes and profiles.
-/

noncomputable section

namespace PolycyclicRecognition

variable {W I B : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W] [Fintype I] [Fintype B] [Nonempty B]

/-- Precomposition of continuous covectors by a height automorphism. -/
def heightDualAction (A : W ≃L[ℝ] W) : (W →L[ℝ] ℝ) ≃L[ℝ] (W →L[ℝ] ℝ) :=
  A.symm.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)

omit [FiniteDimensional ℝ W] in
@[simp] theorem heightDualAction_apply (A : W ≃L[ℝ] W) (φ : W →L[ℝ] ℝ) (w : W) :
    heightDualAction A φ w = φ (A w) := rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_FiniteIndexTopHomology
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The index on top homology with induced orientation coefficients

The coefficient return map becomes multiplication by the subgroup index.
Identifying it with subgroup inclusion is a separate bar-resolution step.
-/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G] (H : Subgroup G) [H.FiniteIndex] (D : Rep ℤ G)

def finiteIndexOrientationHomEquiv :
    (D ⟶ Rep.ind H.subtype (Rep.res H.subtype D)) ≃ₗ[ℤ]
      (Rep.res H.subtype D ⟶ Rep.res H.subtype D) := by
  classical
  exact (Linear.homCongr ℤ (Iso.refl D) (Rep.indCoindIso (Rep.res H.subtype D))).trans
    (Rep.resCoindHomEquiv.{0} H.subtype D (Rep.res H.subtype D)).symm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_HomologyOrientationEquiv
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives
attribute [-simp] _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Transport of a top-homology orientation along a group isomorphism -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G J : Type} [Group G] [Group J]

def restrictionHomLinearEquiv (e : G ≃* J) (D A : Rep ℤ J) :
    (D ⟶ A) ≃ₗ[ℤ] (Rep.res e.toMonoidHom D ⟶ Rep.res e.toMonoidHom A) where
  toFun := Rep.resMap e.toMonoidHom
  invFun f := Rep.ofHom ⟨f.hom.toLinearMap, by
    intro j
    simpa using f.hom.isIntertwining' (e.symm j)⟩
  left_inv f := by apply Rep.hom_ext; rfl
  right_inv f := by apply Rep.hom_ext; rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def orientationRestrictionRoundtripIso (e : G ≃* J) (A : Rep ℤ G) :
    Rep.res e.toMonoidHom (Rep.res e.symm.toMonoidHom A) ≅ A :=
  Rep.mkIso (Representation.Equiv.mk (LinearEquiv.refl ℤ A.V) (by
    intro g
    ext a
    change A.ρ (e.symm (e g)) a = A.ρ g a
    rw [e.symm_apply_apply]))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_RationalBicomplexComparison
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rational total comparison for the actual integral bicomplex

Exact rationalization allows the row kernel to be rationally acyclic. The
integral rows themselves need not be exact.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct

instance rationalModuleFunctor_preservesFiniteLimits :
    PreservesFiniteLimits rationalModuleFunctor :=
  Functor.preservesFiniteLimits_of_preservesHomology _

instance rationalModuleFunctor_preservesFiniteColimits :
    PreservesFiniteColimits rationalModuleFunctor :=
  Functor.preservesFiniteColimits_of_preservesHomology _

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_WeightSamplingPolytope
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The compact polyhedron used for sampling the nilpotent boxes -/

noncomputable section
namespace PolycyclicRecognition

open Set
open scoped BigOperators

variable {W I B : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W] [Fintype I] [Fintype B]

/-- Strict halfspaces give its interior sampling region. -/
def weightSamplingInterior (α : I → W →L[ℝ] ℝ) : Set W :=
  {x | ∀ i, α i x < ‖α i‖}

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanSamplingParameters
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete parameters for the neighboring-sheet sampling argument -/

noncomputable section

namespace PolycyclicRecognition

open Set

set_option maxHeartbeats 1000000 in
/-- The open profile-height domain retains the strict facet inequalities. -/
def samplingHeightDomain {W I : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (α : I → W →L[ℝ] ℝ) (a : ℝ) : Set W := {w | ∀ i, α i w < a * ‖α i‖}

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanTransformedPolarTemplates
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual target templates in the offset comparison

The target cone is the inverse image under precomposition by the affine
label. Its vanishing widths and positive ideal widths are consequences of
the source polar template, without requiring the label to preserve a ball.
-/

noncomputable section
namespace PolycyclicRecognition

open Set

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W]

set_option maxHeartbeats 1000000 in
/-- The target functionals whose pullbacks lie in the source cone. -/
def transformedPolarCone (K : ProperCone ℝ (StrongDual ℝ W)) (A : W ≃ₗ[ℝ] W) :
    ProperCone ℝ (StrongDual ℝ W) :=
  K.comap ((ContinuousLinearMap.compL ℝ W W ℝ).flip
    A.toLinearMap.toContinuousLinearMap)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ExponentialDuhamel
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The difference formula for matrix exponentials

The scalar-time exponential derivative and the fundamental theorem of
calculus give the noncommutative difference formula. This is the concrete
step toward identifying the differential in the retained Dixmier input.
-/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

local instance instNormedAlgebraRat_solutions : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ExponentialDuhamelDerivative
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The differential of the noncommutative exponential

The difference formula and continuity of integrals on a compact interval
identify the derivative along each line. Analyticity then identifies the
actual Frechet differential; no inverse-exponential theorem is assumed.
-/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set Filter
open scoped Topology

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

local instance instNormedAlgebraRat_solutions_1 : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_GenericWeightDirections
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Generic directions for a finite weight arrangement -/

noncomputable section

namespace PolycyclicRecognition

open Set

variable {W I : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W] [Finite I]

def genericWeightDirections (α : I → W →L[ℝ] ℝ) : Set W :=
  {w | ∀ i, α i w ≠ 0}

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_HeightChangeOfCoordinates
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
attribute [-simp] _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite height groups and bounds under a change of normed coordinates -/

noncomputable section
namespace PolycyclicRecognition

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ V]
  [FiniteDimensional ℝ W]

def heightConjugation (e : V ≃ₗ[ℝ] W) : (V ≃ₗ[ℝ] V) →* (W ≃ₗ[ℝ] W) where
  toFun A := e.symm.trans (A.trans e)
  map_one' := by ext w; simp
  map_mul' A B := by ext w; simp

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_HorizontalFlowDerivative
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Measurable, locally bounded derivatives along horizontal flows -/

noncomputable section

namespace PolycyclicRecognition

open Set Filter MeasureTheory
open scoped NNReal

def flowDeriv {G V W : Type*} [Group G] [SMul ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (f : G → W) (Exp : V → G) (v : V) (g : G) : W :=
  deriv (fun t : ℝ => f (g * Exp (t • v))) 0

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_TriangularAdjointEmbedding
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
attribute [-simp] _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A triangular adjoint basis from a faithful triangular representation

Order matrix units by increasing row and decreasing column. Commuting
with an upper triangular matrix then gives an upper triangular operator.
Restricting this action to a faithfully embedded Lie algebra supplies
its actual adjoint basis.
-/

noncomputable section

namespace PolycyclicRecognition

open Module Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Rows increase and columns decrease in the ordering of matrix units. -/
def triangularMatrixOrder (n : ℕ) : Fin n × Fin n ≃ Fin (n * n) :=
  (Equiv.prodCongr (Equiv.refl (Fin n)) Fin.revPerm).trans finProdFinEquiv

@[simp] theorem triangularMatrixOrder_val {n : ℕ} (p : Fin n × Fin n) :
    (triangularMatrixOrder n p : ℕ) = (p.2.rev : ℕ) + n * (p.1 : ℕ) := rfl

/-- Matrix coordinates with respect to this ordering. -/
def triangularMatrixCoordinates (n : ℕ) :
    Matrix (Fin n) (Fin n) ℝ ≃ₗ[ℝ] (Fin (n * n) → ℝ) where
  toFun A i := A ((triangularMatrixOrder n).symm i).1
    ((triangularMatrixOrder n).symm i).2
  invFun v i j := v (triangularMatrixOrder n (i, j))
  left_inv A := by ext i j; simp
  right_inv v := by ext i; simp
  map_add' A B := rfl
  map_smul' r A := rfl

@[simp] theorem triangularMatrixCoordinates_apply {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin (n * n)) :
    triangularMatrixCoordinates n A i =
      A ((triangularMatrixOrder n).symm i).1 ((triangularMatrixOrder n).symm i).2 := rfl

@[simp] theorem triangularMatrixCoordinates_symm_apply {n : ℕ}
    (v : Fin (n * n) → ℝ) (i j : Fin n) :
    (triangularMatrixCoordinates n).symm v i j =
      v (triangularMatrixOrder n (i, j)) := rfl

/-- The ordered matrix units. -/
def triangularMatrixBasis (n : ℕ) :
    Basis (Fin (n * n)) ℝ (Matrix (Fin n) (Fin n) ℝ) :=
  (Pi.basisFun ℝ (Fin (n * n))).map (triangularMatrixCoordinates n).symm

@[simp] theorem triangularMatrixBasis_apply {n : ℕ} (i j : Fin n) :
    triangularMatrixBasis n (triangularMatrixOrder n (i, j)) = Matrix.single i j 1 := by
  ext k l
  change (triangularMatrixCoordinates n).symm
    ((Pi.basisFun ℝ (Fin (n * n))) (triangularMatrixOrder n (i, j))) k l = _
  rw [Pi.basisFun_apply, triangularMatrixCoordinates_symm_apply]
  simp only [Pi.single_apply, EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq,
    Matrix.single_apply, eq_comm]

@[simp] theorem triangularMatrixBasis_repr_apply {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin (n * n)) :
    (triangularMatrixBasis n).repr A i = triangularMatrixCoordinates n A i := by
  change (Pi.basisFun ℝ (Fin (n * n))).repr (triangularMatrixCoordinates n A) i = _
  simp only [Pi.basisFun_repr]

@[simp] theorem triangularMatrixBasis_repr {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    (triangularMatrixBasis n).repr A (triangularMatrixOrder n (i, j)) = A i j := by
  rw [triangularMatrixBasis_repr_apply, triangularMatrixCoordinates_apply]
  simp only [Equiv.symm_apply_apply]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_MatrixDifferentialFromSmoothness
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Discharging the matrix Lie differential input

The representation is only assumed continuous. Automatic smoothness is
proved using exponential product coordinates, and the Lie-homomorphism law
is proved using related vector fields in a chart.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold ContDiff Matrix.Norms.Operator

attribute [local instance 100] LieRing.ofAssociativeRing

local instance matrixDifferentialChartedSpace (n : ℕ) :
    @ChartedSpace (Matrix (Fin n) (Fin n) ℝ)
      (@UniformSpace.toTopologicalSpace _ (@PseudoMetricSpace.toUniformSpace _
        (@SeminormedAddCommGroup.toPseudoMetricSpace _
          (@NormedAddCommGroup.toSeminormedAddCommGroup _
            (Matrix.linftyOpNormedAddCommGroup (m := Fin n) (n := Fin n) (α := ℝ))))))
      (Matrix (Fin n) (Fin n) ℝ) inferInstance := by
  convert chartedSpaceSelf (Matrix (Fin n) (Fin n) ℝ) using 1
  all_goals try with_reducible_and_instances rfl
  rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_NilpotentLinearFlow
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial linear flows used in the logarithm of a lattice automorphism -/

noncomputable section
namespace PolycyclicRecognition

section Derivative
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
local instance linearFlowDerivativeRationalModule : Module ℚ V := Module.compHom V (algebraMap ℚ ℝ)

end Derivative
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_PositiveSizeTriangularRepresentation
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
attribute [-simp] _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positive-size padding for the triangular representation

A trivial one-dimensional summand handles zero-dimensional Lie algebras
without a separate group-realization case.
-/

noncomputable section
namespace PolycyclicRecognition

attribute [local instance 100] LieRing.ofAssociativeRing

def matrixTrivialSummand (m : ℕ) :
    Matrix (Fin m) (Fin m) ℝ →ₗ⁅ℝ⁆ Matrix (Fin m ⊕ Fin 1) (Fin m ⊕ Fin 1) ℝ where
  toFun A := Matrix.fromBlocks A 0 0 0
  map_add' A B := by ext i j; cases i <;> cases j <;> simp
  map_smul' r A := by ext i j; cases i <;> cases j <;> simp
  map_lie' {A B} := by
    simp only [Ring.lie_def, Matrix.fromBlocks_multiply, mul_zero, add_zero]
    ext i j; cases i <;> cases j <;> simp

def padTriangularMatrix (m : ℕ) :
    Matrix (Fin m) (Fin m) ℝ →ₗ⁅ℝ⁆ Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
  (Matrix.reindexAlgEquiv ℝ ℝ (finSumFinEquiv : Fin m ⊕ Fin 1 ≃ Fin (m + 1))).toLieEquiv.toLieHom.comp
    (matrixTrivialSummand m)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_PositiveWeightCones
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The positive parts of the ray and two-generator cones -/

noncomputable section
namespace PolycyclicRecognition

open Set
open scoped BigOperators

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The pointed two-generator cone with its vertex omitted. -/
def positiveWeightCone (α η : V) : Set V :=
  {β | ∃ c d : ℝ, 0 ≤ c ∧ 0 ≤ d ∧ 0 < c + d ∧ β = c • α + d • η}

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RationalFlowBoxes
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A countable interval cover of admissible flow segments -/

noncomputable section

namespace PolycyclicRecognition

open Set Filter Metric

def rationalFlowBox
    {G V : Type*} [Group G] [SMul ℝ V]
    (U : Set G) (Exp : V → G) (v : V) (q : ℚ × ℚ) : Set ((ℝ × ℝ) × G) :=
  {z | z.1.1 ∈ Ioo (q.1 : ℝ) q.2 ∧ z.1.2 ∈ Ioo (q.1 : ℝ) q.2 ∧
    ∀ a ∈ Icc (q.1 : ℝ) q.2, z.2 * Exp (a • v) ∈ U}

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_TriangularExponentialAverage
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Invertibility of the averaged real triangular exponential

This is the linear operator appearing in the differential of exponential
coordinates. Its diagonal entries are integrals of positive real
exponentials, so they cannot vanish. No global exponential theorem is used.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Matrix.Norms.Operator
open MeasureTheory Set

variable {n : ℕ}

def triangularExpAverage (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  ∫ t in (0 : ℝ)..1, NormedSpace.exp (t • A)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_TriangularOperatorAverage
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Invertibility of an averaged operator with real triangular matrix

This is the linear-algebra part of regularity of real triangular exponential
coordinates. It applies to the adjoint operator in its given triangular basis.
-/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory
open scoped Matrix.Norms.Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ}

def operatorExpAverage (D : E →L[ℝ] E) : E →L[ℝ] E :=
  ∫ t in (0 : ℝ)..1, NormedSpace.exp (t • D)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RepresentedExponentialDifferential
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exponential differential in a faithful Lie representation

Left translation identifies this differential with the average of the
negative adjoint flow. A real triangular adjoint basis makes that average
invertible, independently of a global exponential chart.
-/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory
attribute [local instance 100] LieRing.ofAssociativeRing

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

local instance instNormedAlgebraRat_solutions_2 : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RootSwitchCurves
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Continuous short switches with constant height

Use the actual root one-parameter subgroup for a switch. Every pair of its
points has logarithmic distance at a supporting Cartan position, while its
canonical height is exactly constant. No choice of geodesics is needed.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieAlgebra
open scoped Manifold

def rootSwitchCurve {L G : Type*} [SMul ℝ L] [Mul G]
    (Exp : L → G) (v : L) (a : ℝ) (x d : G) (t : ℝ) : G :=
  x * Exp ((t * a) • v) * d

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_SpectralLieDerivation
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A compatible spectral logarithm is a Lie derivation

The multiplicative relations among eigenvalues are essential: brackets of
eigenvectors have the product eigenvalue, so their logarithmic weights add.
-/

noncomputable section
namespace PolycyclicRecognition
attribute [local instance] LieRing.ofAssociativeRing

variable {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem semisimple_bilinear_ext (S : Module.End ℂ V) (hS : S.IsSemisimple)
    {B C : V →ₗ[ℂ] V →ₗ[ℂ] V}
    (h : ∀ μ ν x y, x ∈ S.eigenspace μ → y ∈ S.eigenspace ν → B x y = C x y) : B = C := by
  apply semisimple_eigenspace_ext S hS
  intro μ x hx
  apply semisimple_eigenspace_ext S hS
  intro ν y hy
  exact h μ ν x y hx hy

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_SupportedFlowLipschitz
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Horizontal Lipschitz bounds for every supported profile -/

noncomputable section
namespace PolycyclicRecognition

open Set Filter MeasureTheory
open scoped Topology NNReal

def profileFlowDistance {V W : Type*} [TopologicalSpace V] [LocallyCompactSpace V]
    [PseudoMetricSpace W] (S : Set C(V, W)) (z : V) (s t : ℝ)
    (F : C(V × ℝ, V)) : C(S, ℝ) :=
  ⟨fun f => dist (f.val (F (z, s))) (f.val (F (z, t))), by
    exact (continuous_eval.comp (continuous_subtype_val.prodMk continuous_const)).dist
      (continuous_eval.comp (continuous_subtype_val.prodMk continuous_const))⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_WeightChambers
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Incident weight chambers determine an extreme ray

Both signs of every active hyperplane occur among genuine open chambers.
Intersecting their closures therefore imposes the active equations; actual
extremality, rather than a rank assumption, identifies the resulting ray.
-/

noncomputable section

namespace PolycyclicRecognition

open Set Filter
open scoped Topology

variable {W I : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W] [Finite I]

def weightSigns (α : I → W →L[ℝ] ℝ) (w : W) (i : I) : Bool := decide (0 < α i w)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.TendstoTactic
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


set_option linter.style.longLine false

/-!
# `poly_tendsto` — a tactic for limits of polynomial-like quotients

Proves goals of the form
  `Filter.Tendsto (fun x => N x / D x) Filter.atTop (nhds 0)`
where `x` ranges over `ℕ` or `ℝ`, and `N`, `D` are polynomial-like expressions
in `x` (built from `+`, `-`, `*`, `/`, `^`, `x` itself and `x`-free atoms as
coefficients) whose degrees satisfy `deg N < deg D`.

Two proof strategies are tried in order:

1. **Polynomial reflection** (literal exponents only, top-level division):
   reify `N` and `D` into `Polynomial ℝ` terms, apply
   `Polynomial.div_tendsto_atTop_zero_of_degree_lt`, and discharge the degree
   side goals with `compute_degree!`. This handles denominators that are sums,
   like `(x + 1) ^ 3`.

2. **Monomial asymptotics** (supports symbolic `ℕ` exponents like `x ^ (d + 3)`,
   division nested inside products, and constant factors in the denominator):
   normalize the whole expression into a sum of monomials `c * x ^ e` over a
   single-monomial denominator, prove each `(fun x => c * x ^ eᵢ) =o[atTop]
   (fun x => x ^ e)` via `Asymptotics.isLittleO_pow_pow_atTop_of_lt` with the
   exponent comparison discharged by `omega`, combine with `IsLittleO.add`, and
   finish with `IsLittleO.tendsto_div_nhds_zero`. The function equality is
   discharged by `ring`.

A goal over `ℕ` is first reduced to one over `ℝ` by abstracting `(↑x : ℝ)` and
composing with `tendsto_natCast_atTop_atTop`. `Function.comp` in the goal is
unfolded and casts are normalized with `push_cast` beforehand.

If both strategies fail and every occurrence of the variable `x` lives inside a
common shifted subterm `x + c` (or `c + x`) with `c` constant — e.g.
`(x + c) ^ d / (x + c) ^ (d + 3)` — the limit is reduced to one in the shifted
variable via `tendsto_atTop_add_const_right` and the strategies are retried.
-/

open Filter Polynomial Asymptotics

namespace PolyTendsto


end PolyTendsto
end

section
-- module Solutions.OAIQ093_PR.ToMathlib_Analysis_Matrix_UnitaryAux
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
attribute [-simp] _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Unitary matrices: helper lemmas

General-purpose material extracted from the Gromov development, destined for mathlib.
-/


-- TODO - cleanup and PR to mathlib
@[simp]
lemma isStarNormal_unitary_coe {n: ℕ} (f: Matrix.unitaryGroup (Fin n) ℂ): IsStarNormal (Matrix.toEuclideanLin f.val) := by
  apply isStarNormal_of_mem_unitary

  rw [Unitary.mem_iff]
  refine ⟨?_, ?_⟩
  .
    have f_prop := f.property
    rw [Matrix.mem_unitaryGroup_iff'] at f_prop
    apply_fun Matrix.toEuclideanLin at f_prop
    rw [LinearMap.star_eq_adjoint]
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    rw [Matrix.star_eq_conjTranspose] at f_prop

    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal] at f_prop
    -- TODO - make a better lemma and PR to mathlib
    rw [Matrix.toLin_mul (v₂ := (EuclideanSpace.basisFun (Fin n) ℂ).toBasis )] at f_prop
    rw [← Matrix.toEuclideanLin_eq_toLin_orthonormal] at f_prop
    conv at f_prop =>
      lhs
      equals (f.val.conjTranspose.toEuclideanLin) * (f.val.toEuclideanLin) =>
        rfl


    rw [f_prop]
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
    rw [LinearMap.ext_iff]
    intro x
    simp

  .
    have f_prop := f.property
    rw [Matrix.mem_unitaryGroup_iff] at f_prop
    apply_fun Matrix.toEuclideanLin at f_prop
    rw [LinearMap.star_eq_adjoint]
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    rw [Matrix.star_eq_conjTranspose] at f_prop

    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal] at f_prop
    -- TODO - make a better lemma and PR to mathlib
    rw [Matrix.toLin_mul (v₂ := (EuclideanSpace.basisFun (Fin n) ℂ).toBasis )] at f_prop
    rw [← Matrix.toEuclideanLin_eq_toLin_orthonormal] at f_prop
    conv at f_prop =>
      lhs
      equals (f.val.toEuclideanLin) * (f.val.conjTranspose.toEuclideanLin) =>
        rfl

    rw [f_prop]
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
    rw [LinearMap.ext_iff]
    intro x
    simp

@[simp]
lemma isStarNormal_unitary_coe_toLin {n: ℕ} (f: Matrix.unitaryGroup (Fin n) ℂ): IsStarNormal (Matrix.toLin ((EuclideanSpace.basisFun (Fin n) ℂ).toBasis) ((EuclideanSpace.basisFun (Fin n) ℂ).toBasis ) f.val) := by
  rw [← Matrix.toEuclideanLin_eq_toLin_orthonormal]
  simp
end

section
-- module Solutions.OAIQ093_PR.ToMathlib_GroupTheory_Closure
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
attribute [-simp] _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Subgroup closures

General-purpose material extracted from the Gromov development, destined for mathlib.
-/


open scoped Pointwise Finset

namespace Subgroup

/-- If every element of `B` conjugates `A` into itself, then `B` normalizes `A`.

Together with `Subgroup.coe_mul_of_right_le_normalizer_left` this gives
`↑(A ⊔ B) = ↑A * ↑B`. -/
@[to_additive /-- If every element of `B` conjugates `A` into itself, then `B` normalizes `A`. -/]
theorem le_normalizer_of_conj_mem {G : Type*} [Group G] {A B : Subgroup G}
    (hab : ∀ b ∈ B, ∀ a ∈ A, b * a * b⁻¹ ∈ A) : B ≤ normalizer A := by
  intro b hb
  rw [mem_normalizer_iff]
  refine fun n => ⟨hab b hb n, fun h => ?_⟩
  simpa [mul_assoc] using hab b⁻¹ (inv_mem hb) _ h

end Subgroup
end

section
-- module Solutions.OAIQ093_PR.ToMathlib_GroupTheory_CosetCover
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
attribute [-simp] _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Right coset covers by a constant subgroup

Right-handed analogues of the `leftCoset_cover_const` results in
`Mathlib/GroupTheory/CosetCover.lean`, where they are intended to go.

Upstreaming status: ready modulo style (line lengths, `simp` squeezing).
-/


open scoped Pointwise

namespace Subgroup

variable {G : Type*} [Group G]

section rightCoset_cover_const

variable {ι : Type*} {s : Finset ι} {H : Subgroup G} {g : ι → G}

@[to_additive]
theorem rightCoset_cover_const_iff_surjOn :
    ⋃ i ∈ s, (MulOpposite.op (g i)) • (H : Set G) = Set.univ ↔
      Set.SurjOn ((fun a => Quotient.mk _ (g a)) :
        ι → (Quotient (QuotientGroup.rightRel H))) s Set.univ := by
  -- QuotientGroup.quotientRightRelEquivQuotientLeftRel
  simp [Set.eq_univ_iff_forall, mem_rightCoset_iff, Set.SurjOn,
    Quotient.forall, Quotient.eq, QuotientGroup.rightRel_apply]

variable (hcovers : ⋃ i ∈ s, (MulOpposite.op (g i)) • (H : Set G) = Set.univ)
include hcovers

@[to_additive]
theorem finiteIndex_of_rightCoset_cover_const : H.FiniteIndex := by
  simp_rw [rightCoset_cover_const_iff_surjOn] at hcovers
  have := Set.finite_univ_iff.mp <| Set.Finite.of_surjOn _ hcovers s.finite_toSet
  rw [Equiv.finite_iff (QuotientGroup.quotientRightRelEquivQuotientLeftRel _)] at this
  exact H.finiteIndex_of_finite_quotient

end rightCoset_cover_const

end Subgroup
end

section
-- module Solutions.OAIQ093_PR.Unipotent_Commutator
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

/-!
# Iterated commutators and the lower central series

`iteratedCommutator`, the generating sets `iterate_comm_set`, and
`lower_central_generates_succ`.
-/


set_option linter.style.longLine false
set_option linter.style.commandStart false
set_option linter.style.cdot false

open scoped commutatorElement IsMulCommutative Pointwise

@[expose]
def iteratedCommutator {T: Type*} [Group T] (base right: T) (n: ℕ) := Nat.iterate (fun x => ⁅x, right⁆) n base


@[expose]
def iterate_comm_set {G: Type*} [Group G] [DecidableEq G] (S: Finset G) (n: ℕ): Finset G :=
  match n with
  | 0 => S
  | n + 1 => Finset.biUnion S (fun s => Finset.image (fun g => ⁅g, s⁆) (iterate_comm_set S n))
end

section
-- module Solutions.OAIQ093_PR.Unipotent_FG
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
attribute [-simp] _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

/-!
# Finite generation of subgroups

That subgroups of finitely generated abelian and nilpotent groups are finitely generated, plus
the supporting transfer lemmas along homomorphisms.
-/


set_option linter.style.longLine false
set_option linter.style.commandStart false
set_option linter.style.cdot false

open scoped commutatorElement IsMulCommutative Pointwise

variable {G: Type*} [Group G] [DecidableEq G] (S: Finset G)

variable {G: Type*} [Group G] [DecidableEq G] (S: Finset G)


-- TODO - cleanup and upstream to mathlib
@[expose]
instance torsion_characteristic {G: Type*} [CommGroup G]: (CommGroup.torsion G).Characteristic := by
  rw [Subgroup.characteristic_iff_le_map]
  intro f g hg
  simp
  rw [CommGroup.mem_torsion] at hg
  use (f.symm.toMonoidHom g)
  refine ⟨?_, by simp⟩
  rw [CommGroup.mem_torsion]
  apply MonoidHom.isOfFinOrder
  exact hg

-- TODO - generalize and upstream to mathlib


@[expose]
instance subgroup_map_finite {A B: Type*} [Group A] [Group B] (f: A →* B) (G: Subgroup A) [Finite G]: Finite (Subgroup.map f G) := by
  have foo: (Subgroup.map f G) ≃ (Set.image f G.carrier) := {
    toFun := fun a => a
    invFun := fun a => a
  }
  rw [Equiv.finite_iff foo]
  rw [Set.finite_coe_iff]
  apply Finite.Set.finite_image


@[simp]
lemma toIntLinearMap_id {M : Type*}  [AddCommGroup M]: (AddMonoidHom.id M).toIntLinearMap = LinearMap.id := by
  ext a
  simp
end

section
-- module Solutions.OAIQ093_PR.Unipotent_GammaN
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

/-!
# Existence of a unipotent `γ_n`

`exists_gamma_n_unipotent_center_N'` and `exists_gamma_n_unipotent_N'`.
-/


set_option linter.style.longLine false
set_option linter.style.commandStart false
set_option linter.style.cdot false

open scoped commutatorElement IsMulCommutative Pointwise

variable {G: Type*} [Group G] [DecidableEq G] (S: Finset G)

@[expose]
def gamma_conj_bound {H: Type*}  [DecidableEq H] [Group H]  {N': Subgroup H} (gamma: MulAut N') := ∀ k: ℕ, (0 < k) →  ∀ g, ∃ p q: ℕ, 0 < p ∧ ∀ b: ℕ, 0 < b → ∀ a: ℕ, (0 < a) → (a < b) → ((Finset.image (fun x ↦ (List.map (fun (i:  ↥(Finset.Ico a b)) ↦ (gamma)^[k * ↑i] g) x.toList).prod))
        (Finset.Ico a b).attach.powerset).card ≤ p * (b^q) * (b - a)^q


--   -- simp at ord_fin
--   --rw [Nat.card_prod] at ord_fin
end


