-- Prove2me | Definitions.Def_OAIQ093D003
-- name    : OAIQ093D003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T16:00:42.111037+00:00
-- url     : https://prove2.me/theorems/e7f14bfb-1d20-416e-b95b-449b4192f75a
-- title:
--   Definitions bundle OAIQ093D003 of the split of OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 788 declarations of OpenAI's Lean: 347 definitions, 21 inductive types or structures, 27 instances and 393 theorems. The definitions and types are `OAI.PolycyclicRecognition.ControlledContraction`, `OAI.PolycyclicRecognition.ControlledContraction.ofChart`, `OAI.PolycyclicRecognition.ControlledMetricFolnerPairs`, `OAI.PolycyclicRecognition.ControlledMetricFolnerPairs.toReiter`, `OAI.PolycyclicRecognition.ControlledReiterFamily`, `OAI.PolycyclicRecognition.CoordinatePolynomial`, `OAI.PolycyclicRecognition.CosetCollisionBound`, `OAI.PolycyclicRecognition.DekimpeLatticeRealizationInput`, `OAI.PolycyclicRecognition.DependsOnBoolean`, `OAI.PolycyclicRecognition.ErgodicDecompositionInput`, `OAI.PolycyclicRecognition.ExponentialConjugationLaw`, `OAI.PolycyclicRecognition.FactorExtension`, `OAI.PolycyclicRecognition.FactorExtension.equivProd`, `OAI.PolycyclicRecognition.FactorExtension.groupExtension`, `OAI.PolycyclicRecognition.FactorExtension.inl`, `OAI.PolycyclicRecognition.FactorExtension.map`, `OAI.PolycyclicRecognition.FactorExtension.projection`, `OAI.PolycyclicRecognition.FarbWeinbergerLatticeInput`, `OAI.PolycyclicRecognition.FiniteIntegralProjectivePresentation`, `OAI.PolycyclicRecognition.FiniteOrbitAverage`, `OAI.PolycyclicRecognition.FiniteOrbitAverage.apply`, `OAI.PolycyclicRecognition.FiniteOrbitAverage.compose`, `OAI.PolycyclicRecognition.FiniteOrbitAverage.onL2`, `OAI.PolycyclicRecognition.FiniteOrbitAverage.onVector`, `OAI.PolycyclicRecognition.FiniteRationalLinearModel`, `OAI.PolycyclicRecognition.GeodesicMetricExistenceInput`, `OAI.PolycyclicRecognition.GromovPolynomialGrowthInput`, `OAI.PolycyclicRecognition.GroupCoarseEquivalence.metric`, `OAI.PolycyclicRecognition.GroupCoarseEquivalence.refl`, `OAI.PolycyclicRecognition.GroupCoarseEquivalence.symm`, `OAI.PolycyclicRecognition.GroupCoarseEquivalence.trans`, `OAI.PolycyclicRecognition.GroupExtensionSection.coordinate`, `OAI.PolycyclicRecognition.GroupExtensionSection.decode`, `OAI.PolycyclicRecognition.GroupExtensionSection.factor`, `OAI.PolycyclicRecognition.GroupExtensionSection.factorSystem`, `OAI.PolycyclicRecognition.GroupExtensionSection.gaugeSection`, `OAI.PolycyclicRecognition.GroupExtensionSection.mulEquiv`, `OAI.PolycyclicRecognition.GroupExtensionSection.normalFormEquiv`, `OAI.PolycyclicRecognition.HasApproximateMidpoints`, `OAI.PolycyclicRecognition.HasBoundedFiniteSubgroupOrders` and 328 more.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory, in whole or in part: `PolycyclicRecognition_Algebra_ApproximateMidpointProper`, `PolycyclicRecognition_Algebra_AscendingQuotientColimit`, `PolycyclicRecognition_Algebra_BasisPolynomialMaps`, `PolycyclicRecognition_Algebra_BooleanStepAction`, `PolycyclicRecognition_Algebra_BooleanStepRing`, `PolycyclicRecognition_Algebra_BoundedLocallyFiniteKernel`, `PolycyclicRecognition_Algebra_BundleWordCoordinates`, `PolycyclicRecognition_Algebra_CanonicalNilpotentLogarithm`, `PolycyclicRecognition_Algebra_ChartedVectorFieldBracket`, `PolycyclicRecognition_Algebra_CocycleGrowth`, `PolycyclicRecognition_Algebra_CommutingUnipotentLogarithm`, `PolycyclicRecognition_Algebra_ConjugationLift`, `PolycyclicRecognition_Algebra_ConnectedScalarCommutators`, `PolycyclicRecognition_Algebra_ControlledCycleFillings`, `PolycyclicRecognition_Algebra_ControlledPrism`, `PolycyclicRecognition_Algebra_ControlledPrismIdentity`, `PolycyclicRecognition_Algebra_ControlledReiterCocycles`, `PolycyclicRecognition_Algebra_CoordinateConjugation`, `PolycyclicRecognition_Algebra_CoordinateOrbitRepresentation`, `PolycyclicRecognition_Algebra_CoordinatePolynomial`, `PolycyclicRecognition_Algebra_DifferenceAmplitudeWord`, `PolycyclicRecognition_Algebra_EnvelopingTruncation`, `PolycyclicRecognition_Algebra_ExtensionSectionFactor`, `PolycyclicRecognition_Algebra_FactorAutomorphismDescent`, `PolycyclicRecognition_Algebra_FactorExtensionConjugation`, `PolycyclicRecognition_Algebra_FactorExtensionMap`, `PolycyclicRecognition_Algebra_FactorExtensionTopology`, `PolycyclicRecognition_Algebra_FactorSystemGauge`, `PolycyclicRecognition_Algebra_FactorSystemPullback`, `PolycyclicRecognition_Algebra_FactorSystemTwist`, `PolycyclicRecognition_Algebra_FactorSystemTwistAction`, `PolycyclicRecognition_Algebra_FiniteFinsuppHom`, `PolycyclicRecognition_Algebra_FiniteLogCoefficientBound`, `PolycyclicRecognition_Algebra_FiniteOrbitAverage`, `PolycyclicRecognition_Algebra_FiniteRationalLinearModel`, `PolycyclicRecognition_Algebra_FiniteUnitaryAverage`, `PolycyclicRecognition_Algebra_GaugeExtensionSection`, `PolycyclicRecognition_Algebra_GromovInput`, `PolycyclicRecognition_Algebra_GroupExtensionFactorSystem`, `PolycyclicRecognition_Algebra_HomogeneousUniversalLogarithm`, `PolycyclicRecognition_Algebra_HomogeneousWordProjection`, `PolycyclicRecognition_Algebra_IndependentSwitchParameters`, `PolycyclicRecognition_Algebra_InvariantFactor`, `PolycyclicRecognition_Algebra_InvariantLinearLayer`, `PolycyclicRecognition_Algebra_LinearConjugationCentralizer`, `PolycyclicRecognition_Algebra_LocallyBoundedDerivedSeries`, `PolycyclicRecognition_Algebra_LogarithmCoefficientStability`, `PolycyclicRecognition_Algebra_MidpointGrids`, `PolycyclicRecognition_Algebra_MonoidCoefficientLinear`, `PolycyclicRecognition_Algebra_MonoidTensorCoordinates`, `PolycyclicRecognition_Algebra_NilpotentCodimensionOne`, `PolycyclicRecognition_Algebra_NilpotentIdealDerivation`, `PolycyclicRecognition_Algebra_NilpotentMatrixProducts`, `PolycyclicRecognition_Algebra_NilpotentMatrixSpanning`, `PolycyclicRecognition_Algebra_NilpotentRepresentationProducts`, `PolycyclicRecognition_Algebra_NilpotentSpanningOperators`, `PolycyclicRecognition_Algebra_NilpotentUniversalLogarithm`, `PolycyclicRecognition_Algebra_NilpotentWordEvaluation`, `PolycyclicRecognition_Algebra_NonabelianFactorSystem`, `PolycyclicRecognition_Algebra_OrderedCentralWords`, `PolycyclicRecognition_Algebra_OrderedInterpolation`, `PolycyclicRecognition_Algebra_OrderedInterpolationRadius`, `PolycyclicRecognition_Algebra_OrderedPowerWords`, `PolycyclicRecognition_Algebra_OrderedProductSums`, `PolycyclicRecognition_Algebra_PairedWordCoproduct`, `PolycyclicRecognition_Algebra_PolyZ`, `PolycyclicRecognition_Algebra_PolynomialCoordinateEvaluation`, `PolycyclicRecognition_Algebra_PolynomialCoordinateGroup`, `PolycyclicRecognition_Algebra_PolynomialCoordinateOperations`, `PolycyclicRecognition_Algebra_PolynomialCoordinateOrbit`, `PolycyclicRecognition_Algebra_PolynomialCoordinateTopology`, `PolycyclicRecognition_Algebra_PolynomialCurveOperations`, `PolycyclicRecognition_Algebra_PolynomialFamilies`, `PolycyclicRecognition_Algebra_PolynomialFunctionSpace`, `PolycyclicRecognition_Algebra_PolynomialGroupLaws`, `PolycyclicRecognition_Algebra_PolynomialIntegerGrid`, `PolycyclicRecognition_Algebra_PolynomialMatrixCommutator`, `PolycyclicRecognition_Algebra_PolynomialMatrixFunctions`, `PolycyclicRecognition_Algebra_PolynomialMatrixGroup`, `PolycyclicRecognition_Algebra_PolynomialMatrixScalarExtension`, `PolycyclicRecognition_Algebra_PolynomialMatrixStabilizer`, `PolycyclicRecognition_Algebra_PolynomialOneParameterNilpotent`, `PolycyclicRecognition_Algebra_PolynomialQuotientAction`, `PolycyclicRecognition_Algebra_PrimitiveWordProjection`, `PolycyclicRecognition_Algebra_ProjectedFactorSystem`, `PolycyclicRecognition_Algebra_RationalCompleteIdentity`, `PolycyclicRecognition_Algebra_RationalFiniteQuotient`, `PolycyclicRecognition_Algebra_RationalPowerSeriesHom`, `PolycyclicRecognition_Algebra_RationalUniversalLogarithm`, `PolycyclicRecognition_Algebra_RationalWordCoproduct`, `PolycyclicRecognition_Algebra_RationalWordEvaluation`, `PolycyclicRecognition_Algebra_RationalWordOperators`, `PolycyclicRecognition_Algebra_RationalWordTruncationEvaluation`, `PolycyclicRecognition_Algebra_RealNilpotentSpanningOperators`, `PolycyclicRecognition_Algebra_RepCofiber`, `PolycyclicRecognition_Algebra_RepresentationDirectSum`, `PolycyclicRecognition_Algebra_SequenceSubexponential`, `PolycyclicRecognition_Algebra_SequentialModuleTail`, `PolycyclicRecognition_Algebra_SequentialRepresentationColimit`, `PolycyclicRecognition_Algebra_SequentialRepresentationDescent`, `PolycyclicRecognition_Algebra_SequentialRepresentationDiagram`, `PolycyclicRecognition_Algebra_SubexponentialBounds`, `PolycyclicRecognition_Algebra_SubgroupInductionCoordinates`, `PolycyclicRecognition_Algebra_TransferredAction`, `PolycyclicRecognition_Algebra_TranslationLocalHomeomorph`, `PolycyclicRecognition_Algebra_TruncatedEnvelopingAlgebra`, `PolycyclicRecognition_Algebra_TruncatedPrimitiveCoefficients`, `PolycyclicRecognition_Algebra_TruncatedRationalScalars`, `PolycyclicRecognition_Algebra_TuplePrism`, `PolycyclicRecognition_Algebra_TwoImageLimits`, `PolycyclicRecognition_Algebra_UniformCosetBound`, `PolycyclicRecognition_Algebra_UnipotentGroupNilpotent`, `PolycyclicRecognition_Algebra_UnipotentProducts`, `PolycyclicRecognition_Algebra_UnitParameterInverse`, `PolycyclicRecognition_Algebra_UnitaryCocycle`, `PolycyclicRecognition_Algebra_UniversalCoefficientStability`, `PolycyclicRecognition_Algebra_UniversalLogarithmWordCoefficients`, `PolycyclicRecognition_Algebra_WordCoefficientAgreement`, `PolycyclicRecognition_Algebra_WordCutCounting`, `PolycyclicRecognition_Algebra_WordMinimumDegree`, `PolycyclicRecognition_Algebra_WordSplits`, `PolycyclicRecognition_Algebra_WordTensorConvolution`, `PolycyclicRecognition_Analysis_AffineAction`, `PolycyclicRecognition_Analysis_CoarseEquivalence`, `PolycyclicRecognition_Analysis_CoarseEquivalenceMetric`, `PolycyclicRecognition_Analysis_CoarsePathConcatenation`, `PolycyclicRecognition_Analysis_CommutingIntegralHom`, `PolycyclicRecognition_Analysis_CompactExtensionModels`, `PolycyclicRecognition_Analysis_ControlledChainRepresentation`, `PolycyclicRecognition_Analysis_ControlledFaceSupport`, `PolycyclicRecognition_Analysis_ControlledFiniteChains`, `PolycyclicRecognition_Analysis_ControlledMetricFolner`, `PolycyclicRecognition_Analysis_ErgodicDecompositionInput`, `PolycyclicRecognition_Analysis_IntegralBilinearExtension`, `PolycyclicRecognition_Analysis_IntegralQuotientKernel`, `PolycyclicRecognition_Analysis_LinearMetricChains`, `PolycyclicRecognition_Analysis_MetricCoarseBridge`, `PolycyclicRecognition_Analysis_MetricQuasiEquivalence`, `PolycyclicRecognition_Analysis_MetricTent`, `PolycyclicRecognition_Analysis_NormalizedMetricTent`, `PolycyclicRecognition_Analysis_OneParameterIntegralCurve`, `PolycyclicRecognition_Analysis_Packing`, `PolycyclicRecognition_Analysis_PolynomialEndpointSchemes`, `PolycyclicRecognition_Analysis_RemezInput`, `PolycyclicRecognition_Analysis_SelfQuasiIsometry`, `PolycyclicRecognition_Analysis_SmallCoefficientMean`, `PolycyclicRecognition_Analysis_SmallCoefficientRationalMean`, `PolycyclicRecognition_Analysis_StationarySlope`, `PolycyclicRecognition_Analysis_SuccessfulWordPaths`, `PolycyclicRecognition_Analysis_TranslationCovering`, `PolycyclicRecognition_Analysis_TupleChainPrism`, `PolycyclicRecognition_Finiteness_BooleanStepProjective`, `PolycyclicRecognition_Finiteness_CoarseGroupRingCohomology`, `PolycyclicRecognition_Finiteness_CoefficientNaturalCohomology`, `PolycyclicRecognition_Finiteness_CohomologicalFiniteness`, `PolycyclicRecognition_Finiteness_ControlledCochainComplex`, `PolycyclicRecognition_Finiteness_ControlledCochainHomotopy`, `PolycyclicRecognition_Finiteness_ControlledCochainMap`, `PolycyclicRecognition_Finiteness_ControlledCochains`, `PolycyclicRecognition_Finiteness_ControlledTupleMaps`, `PolycyclicRecognition_Finiteness_DualityEndgame`, `PolycyclicRecognition_Finiteness_FiniteProjectivePresentations`, `PolycyclicRecognition_Finiteness_FiniteResolutionTruncation`, `PolycyclicRecognition_Finiteness_FreeAbelianDuality`, `PolycyclicRecognition_Finiteness_IntegralProjectiveTower`, `PolycyclicRecognition_Finiteness_PolycyclicDualityComparison`, `PolycyclicRecognition_Finiteness_ProjectiveKernelStableMap`, `PolycyclicRecognition_Finiteness_ProjectiveResolutionSyzygies`, `PolycyclicRecognition_Finiteness_ProjectiveTowerCohomology`, `PolycyclicRecognition_Finiteness_ProjectiveTowerComparison`, `PolycyclicRecognition_Finiteness_RationalFiniteResolution`, `PolycyclicRecognition_Finiteness_RationalHomologyDimension`, `PolycyclicRecognition_Finiteness_ReducedCohomologyInput`, `PolycyclicRecognition_Finiteness_RepCochainMaps`, `PolycyclicRecognition_Finiteness_SequentialProjectiveTelescope`, `PolycyclicRecognition_Finiteness_SequentialResolutionVanishing`, `PolycyclicRecognition_Finiteness_SmallCoefficientRing`, `PolycyclicRecognition_Finiteness_SplitProjectiveColimit`, `PolycyclicRecognition_Finiteness_StableResolutionIdentity`, `PolycyclicRecognition_Finiteness_StableSyzygyMap`, `PolycyclicRecognition_Finiteness_UnitaryReducedVanishing`, `PolycyclicRecognition_Geometry_AlgebraHomLieDifferential`, `PolycyclicRecognition_Geometry_AnalyticNilpotentExponential`, `PolycyclicRecognition_Geometry_AnalyticRepresentationAtlas`, `PolycyclicRecognition_Geometry_AnalyticRepresentationGroup`, `PolycyclicRecognition_Geometry_CartanMultiplication`, `PolycyclicRecognition_Geometry_ChartContraction`, `PolycyclicRecognition_Geometry_CompactLieLaws`, `PolycyclicRecognition_Geometry_CompactRotationalTwist`, `PolycyclicRecognition_Geometry_ControlledContraction`, `PolycyclicRecognition_Geometry_ExponentialCoefficientStability`, `PolycyclicRecognition_Geometry_ExponentialProductChart`, `PolycyclicRecognition_Geometry_ExponentialProductCoefficients`, `PolycyclicRecognition_Geometry_ExponentialTangentUniqueness`, `PolycyclicRecognition_Geometry_FiniteCoordinateSmoothness`, `PolycyclicRecognition_Geometry_FiniteExponentialLogarithm`, `PolycyclicRecognition_Geometry_FiniteLieNorm`, `PolycyclicRecognition_Geometry_LieExponential`, `PolycyclicRecognition_Geometry_LieIntegrationNaturality`, `PolycyclicRecognition_Geometry_LieModelMetric`, `PolycyclicRecognition_Geometry_LieProductDifferential`, `PolycyclicRecognition_Geometry_LocalExponentialOpen`, `PolycyclicRecognition_Geometry_LocalParameterSmoothness`, `PolycyclicRecognition_Geometry_ManifoldRelatedBracket`, `PolycyclicRecognition_Geometry_MinimizingLieMetric`, `PolycyclicRecognition_Geometry_NormalizedWeightRays`, `PolycyclicRecognition_Geometry_OrderedInterpolationWeights`, `PolycyclicRecognition_Geometry_ParametricLieWords`, `PolycyclicRecognition_Geometry_PolynomialLieWordCoordinates`, `PolycyclicRecognition_Geometry_PrimitiveNilpotentExponential`, `PolycyclicRecognition_Geometry_ProductLieAlgebra`, `PolycyclicRecognition_Geometry_RepresentedSolvableLieModel`, `PolycyclicRecognition_Geometry_RotationFactorLifts`, `PolycyclicRecognition_Geometry_RotationalTwistCharacter`, `PolycyclicRecognition_Geometry_RotationalTwistLift`, `PolycyclicRecognition_Geometry_SemidirectProductTopology`, `PolycyclicRecognition_Geometry_SmoothHomLieDifferential`, `PolycyclicRecognition_Geometry_SmoothRotationalTwist`, `PolycyclicRecognition_Geometry_TransferredHeight`, `PolycyclicRecognition_Geometry_TransportedManifold`, `PolycyclicRecognition_Geometry_TriangulableLieModel`, `PolycyclicRecognition_Geometry_TriangularLieDifferential`, `PolycyclicRecognition_Geometry_TriangularLocalLogarithm`, `PolycyclicRecognition_Geometry_TriangularMatrixHeight`, `PolycyclicRecognition_Geometry_TriangularProducts`, `PolycyclicRecognition_Geometry_TriangularWordBounds`, `PolycyclicRecognition_Geometry_TruncatedWordExponential`, `PolycyclicRecognition_Geometry_UniversalBCHCoefficientBound`, `PolycyclicRecognition_Geometry_WeightChamberAction`, `PolycyclicRecognition_Geometry_WeightedWordComponents`, `PolycyclicRecognition_Geometry_WeightedWordLogarithm`, `PolycyclicRecognition_Geometry_WeightedWordSubalgebra`, `PolycyclicRecognition_Geometry_WeightedWordSubstitution`, `PolycyclicRecognition_Geometry_WordLieProjection`, `PolycyclicRecognition_Lattices_IntegralLatticeGenerators`, `PolycyclicRecognition_Lattices_IntegralLatticePowerIndex`, `PolycyclicRecognition_Lattices_RecognitionLatticeAssembly`, `PolycyclicRecognition_Lattices_SolvableLatticeModel`, `PolycyclicRecognition_Lattices_SolvableLatticeRecognition`, `PolycyclicRecognition_Lattices_VectorLatticeModel`, `Thompson_InvariantMean`, `Thompson_Model`.
--
--   **Imports.** It imports the published bundle `Def_PolycyclicRecognition`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ093D007`, `OAIQ093D008`, `OAIQ093D009`, `OAIQ093D010` and `OAIQ093D011`; the statements `OAI.PolycyclicRecognition.TypeFPInfinity.heightKernel_virtualSolvable`, `OAI.PolycyclicRecognition.cartan_unitary_reduced_vanishing`, `OAI.PolycyclicRecognition.dekimpeLatticeRealizationInput`, `OAI.PolycyclicRecognition.exists_triangulable_model_of_representations`, `OAI.PolycyclicRecognition.group_recognition_of_gromov`, `OAI.PolycyclicRecognition.nilpotent_by_abelian_uniform_lattice`, `OAI.PolycyclicRecognition.polycyclic_of_nilpotent_by_abelian_duality` and `OAI.PolycyclicRecognition.virtuallyPolycyclic_of_coarse_rational_bounds`.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/GroupTheory at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_PolycyclicRecognition

section
-- module Solutions.OAIQ093_PR.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ApproximateMidpointProper
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Properness of locally compact invariant metrics with approximate midpoints -/

namespace PolycyclicRecognition

open Set Metric Filter
open scoped Pointwise Topology

/-- The length-space consequence needed for properness and minimizing segments. -/
def HasApproximateMidpoints (X : Type*) [PseudoMetricSpace X] : Prop :=
  ∀ x y : X, ∀ ε : ℝ, 0 < ε → ∃ z : X,
    dist x z ≤ dist x y / 2 + ε ∧ dist z y ≤ dist x y / 2 + ε

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_RepCochainMaps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Maps and homotopies on cochains computed from representation complexes -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
attribute [local instance 2000] Rep.hV2
attribute [local instance 2000] Rep.instLinear
attribute [local instance 2100] Linear.homModule

variable (k : Type) [CommRing k] {G : Type} [Group G]
  {P Q R : ChainComplex (Rep k G) ℕ}

def repCochainPrecomp (u : P ⟶ Q) (A : Rep k G) :
    Q.linearYonedaObj k A ⟶ P.linearYonedaObj k A :=
  (HomologicalComplex.unopFunctor (ModuleCat k) (ComplexShape.down ℕ)).map
    ((((linearYoneda k (Rep k G)).obj A).rightOp.mapHomologicalComplex _).map u).op

@[simp] theorem repCochainPrecomp_apply (u : P ⟶ Q) (A : Rep k G)
    (i : ℕ) (f : Q.X i ⟶ A) :
    ((repCochainPrecomp k u A).f i).hom f = u.f i ≫ f := rfl

@[simp] theorem repCochainPrecomp_comp (u : P ⟶ Q) (v : Q ⟶ R) (A : Rep k G) :
    repCochainPrecomp k (u ≫ v) A =
      repCochainPrecomp k v A ≫ repCochainPrecomp k u A := by
  ext i f
  change (u.f i ≫ v.f i) ≫ f = u.f i ≫ (v.f i ≫ f)
  exact Category.assoc _ _ _

@[simp] theorem repCochainPrecomp_id (A : Rep k G) :
    repCochainPrecomp k (𝟙 P) A = 𝟙 _ := by
  ext i f
  exact Category.id_comp f

@[simp] theorem repCochainPrecomp_sub (u v : P ⟶ Q) (A : Rep k G) :
    repCochainPrecomp k (u - v) A = repCochainPrecomp k u A - repCochainPrecomp k v A := by
  ext i f
  change (u.f i - v.f i) ≫ f = u.f i ≫ f - v.f i ≫ f
  exact Preadditive.sub_comp _ _ _

def repCochainHomotopy {u v : P ⟶ Q} (h : Homotopy u v) (A : Rep k G) :
    Homotopy (repCochainPrecomp k u A) (repCochainPrecomp k v A) :=
  (((linearYoneda k (Rep k G)).obj A).rightOp.mapHomotopy h).unop

def repCochainHomotopyEquiv (e : HomotopyEquiv P Q) (A : Rep k G) :
    HomotopyEquiv (Q.linearYonedaObj k A) (P.linearYonedaObj k A) where
  hom := repCochainPrecomp k e.hom A
  inv := repCochainPrecomp k e.inv A
  homotopyHomInvId := by
    simpa only [repCochainPrecomp_comp, repCochainPrecomp_id] using
      repCochainHomotopy k e.homotopyInvHomId A
  homotopyInvHomId := by
    simpa only [repCochainPrecomp_comp, repCochainPrecomp_id] using
      repCochainHomotopy k e.homotopyHomInvId A

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_CohomologicalFiniteness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The finiteness and duality properties used in recognition

These are concrete properties of the trivial integral representation and its
projective resolutions. A finite classifying space supplies a finite resolution
of this kind, but no predicate for an unspecified classifying space is used.
The cohomology condition includes the possibly nontrivial orientation action:
only the underlying integral module in top degree is required to be `ℤ`.
-/

namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits
open scoped MonoidAlgebra

variable (G : Type) [Group G]

/-- The trivial integral representation used to compute integral finiteness. -/
abbrev trivialIntegral : Rep ℤ G := Rep.trivial ℤ G ℤ

/-- Finite generation refers to the group-ring action of the representation. -/
def IntegralRepresentationFinite (A : Rep ℤ G) : Prop :=
  letI : Module ℤ A := A.hV2
  Module.Finite ℤ[G] A.ρ.asModule

/-- Type `FP_n(ℤ)`: a projective resolution finite over `ℤ[G]` through degree `n`. -/
def TypeFP (n : ℕ) : Prop :=
  ∃ P : ProjectiveResolution (trivialIntegral G),
    ∀ i, i ≤ n → IntegralRepresentationFinite G (P.complex.X i)

/-- Type `FP_∞(ℤ)` means type `FP_n(ℤ)` in every finite degree. -/
def TypeFPInfinity : Prop := ∀ n, TypeFP G n

/-- A finite projective resolution, with all terms finite over the group ring. -/
def HasFiniteProjectiveResolution : Prop :=
  ∃ (P : ProjectiveResolution (trivialIntegral G)) (d : ℕ),
    (∀ i, IntegralRepresentationFinite G (P.complex.X i)) ∧
    ∀ i, d < i → IsZero (P.complex.X i)

/-- Finite integral cohomological dimension is finite projective dimension of
the trivial integral representation. -/
def HasFiniteIntegralCohomologicalDimension : Prop :=
  ∃ d : ℕ, HasProjectiveDimensionLE (trivialIntegral G) d

/-- Integral Poincaré duality in dimension `n`, allowing an orientation twist. -/
def IsIntegralPoincareDualityGroup (n : ℕ) : Prop :=
  HasFiniteProjectiveResolution G ∧
  (∀ i, i ≠ n → IsZero (groupCohomology (Rep.leftRegular ℤ G) i)) ∧
  Nonempty (groupCohomology (Rep.leftRegular ℤ G) n ≅ ModuleCat.of ℤ ℤ)

end PolycyclicRecognition

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

def representationModuleHomEquiv :
    (A ⟶ B) ≃ₗ[k] (A.ρ.asModule →ₗ[k[G]] B.ρ.asModule) :=
  (Rep.homLinearEquiv A B).trans (IntertwiningMap.equivLinearMapAsModule A.ρ B.ρ)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_CoefficientNaturalCohomology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coefficient naturality for cohomology from a chosen resolution

The comparison uses one fixed homotopy equivalence with the bar resolution.
Consequently it commutes with every coefficient morphism.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G] {A B : Rep.{0} ℤ G}

def coefficientNaturalCohomologyIso
    (P : ProjectiveResolution (Rep.trivial ℤ G ℤ)) (A : Rep.{0} ℤ G) (n : ℕ) :
    groupCohomology A n ≅ (P.complex.linearYonedaObj ℤ A).homology n :=
  (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.up ℕ) n).mapIso
      (groupCohomology.inhomogeneousCochainsIso A) ≪≫
    isoOfQuasiIsoAt
      (repCochainHomotopyEquiv ℤ
        (ProjectiveResolution.homotopyEquiv P (Rep.barResolution ℤ G)) A).hom n

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_ProjectiveResolutionSyzygies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Projectivity of the top syzygy

Successive quotient terms of a projective resolution fit into short exact
sequences. Finite projective dimension therefore makes the corresponding
top quotient projective; it remains finitely generated when the old term is.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
variable {G : Type} [Group G] (P : ProjectiveResolution (trivialIntegral G))

def resolutionOpcyclesSequence (n : ℕ) : ShortComplex (Rep ℤ G) :=
  ShortComplex.mk (P.complex.fromOpcycles (n + 1) n) (P.complex.pOpcycles n) (by
    rw [← cancel_epi (P.complex.pOpcycles (n + 1)),
      P.complex.p_fromOpcycles_assoc, P.complex.d_pOpcycles, comp_zero])

theorem resolutionOpcyclesSequence_shortExact (n : ℕ) :
    (resolutionOpcyclesSequence P n).ShortExact := by
  have hsc : (P.complex.sc' (n + 2) (n + 1) n).Exact := P.exact_succ n
  let e := P.complex.opcyclesIsoSc' (n + 2) (n + 1) n (by simp) (by simp)
  have : Mono (P.complex.sc' (n + 2) (n + 1) n).fromOpcycles := hsc.mono_fromOpcycles
  have he : P.complex.fromOpcycles (n + 1) n =
      e.hom ≫ (P.complex.sc' (n + 2) (n + 1) n).fromOpcycles := by
    exact (e.inv_comp_eq).mp
      (P.complex.opcyclesIsoSc'_inv_fromOpcycles (n + 2) (n + 1) n (by simp) (by simp))
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · let S := ShortComplex.mk (P.complex.d (n + 1) n) (P.complex.pOpcycles n)
      (P.complex.d_pOpcycles (n + 1) n)
    have hS : S.Exact := ShortComplex.exact_of_g_is_cokernel _
      (P.complex.opcyclesIsCokernel (n + 1) n (by simp))
    let φ : S ⟶ resolutionOpcyclesSequence P n :=
      { τ₁ := P.complex.pOpcycles (n + 1)
        τ₂ := 𝟙 _
        τ₃ := 𝟙 _
        comm₁₂ := by simp [S, resolutionOpcyclesSequence]
        comm₂₃ := by simp [S, resolutionOpcyclesSequence] }
    have : Epi φ.τ₁ := by
      change Epi (P.complex.pOpcycles (n + 1))
      infer_instance
    have : IsIso φ.τ₂ := by
      change IsIso (𝟙 _)
      infer_instance
    have : Mono φ.τ₃ := by
      change Mono (𝟙 _)
      infer_instance
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mp hS
  · change Mono (P.complex.fromOpcycles (n + 1) n)
    have hmono : Mono (e.hom ≫ (P.complex.sc' (n + 2) (n + 1) n).fromOpcycles) :=
      inferInstance
    exact he.symm ▸ hmono
  · change Epi (P.complex.pOpcycles n)
    infer_instance

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_StableResolutionIdentity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The stable identity of a resolution syzygy

Maps factoring through projective representations form the image of a chosen
projective cover. The identity is zero in that quotient precisely when the
representation is projective. Applied to a resolution syzygy this detects
finite integral cohomological dimension, without assuming any stable
vanishing theorem.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
attribute [local instance 2300] Submodule.Quotient.module
variable {G : Type} [Group G]

def projectiveCoverMap (B : Rep.{0} ℤ G) : (projectiveResolution B).complex.X 0 ⟶ B :=
  (projectiveResolution B).π.f 0

instance projectiveCoverMap_epi (B : Rep.{0} ℤ G) : Epi (projectiveCoverMap B) := by
  exact epi_of_isColimit_cofork (projectiveResolution B).isColimitCokernelCofork

def projectiveCoverPostcomp (A B : Rep.{0} ℤ G) :
    (A ⟶ (projectiveResolution B).complex.X 0) →ₗ[ℤ] (A ⟶ B) where
  toFun f := f ≫ projectiveCoverMap B
  map_add' f g := by simp only [Preadditive.add_comp]
  map_smul' r f := by simp only [RingHom.id_apply, Linear.smul_comp]

def projectiveFactorSubmodule (A B : Rep.{0} ℤ G) : Submodule ℤ (A ⟶ B) :=
  LinearMap.range (projectiveCoverPostcomp A B)

abbrev StableRepresentationHom (A B : Rep.{0} ℤ G) :=
  (A ⟶ B) ⧸ projectiveFactorSubmodule A B

def stableRepresentationClass (A B : Rep.{0} ℤ G) :
    (A ⟶ B) →ₗ[ℤ] StableRepresentationHom A B :=
  (projectiveFactorSubmodule A B).mkQ

theorem stableRepresentationClass_eq_zero_iff_projective_factor
    {A B : Rep.{0} ℤ G} (f : A ⟶ B) :
    stableRepresentationClass A B f = 0 ↔
      ∃ (P : Rep.{0} ℤ G), Projective P ∧
        ∃ (u : A ⟶ P) (v : P ⟶ B), u ≫ v = f := by
  change (projectiveFactorSubmodule A B).mkQ f = 0 ↔ _
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨(projectiveResolution B).complex.X 0, inferInstance,
      u, projectiveCoverMap B, hu⟩
  · rintro ⟨P, hP, u, v, huv⟩
    let := hP
    refine ⟨u ≫ Projective.factorThru v (projectiveCoverMap B), ?_⟩
    change (u ≫ _) ≫ projectiveCoverMap B = f
    rw [Category.assoc, Projective.factorThru_comp, huv]

theorem stableRepresentationClass_eq_iff_projective_factor
    {A B : Rep.{0} ℤ G} (f g : A ⟶ B) :
    stableRepresentationClass A B f = stableRepresentationClass A B g ↔
      ∃ (P : Rep.{0} ℤ G), Projective P ∧
        ∃ (u : A ⟶ P) (v : P ⟶ B), u ≫ v = f - g := by
  rw [← sub_eq_zero, ← map_sub, stableRepresentationClass_eq_zero_iff_projective_factor]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_StableSyzygyMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Syzygy maps modulo projective factors

A lift through the projective middle term induces an endomorphism of the next
syzygy. Changing the lift changes that endomorphism by a projective factor.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
attribute [local instance 2300] Submodule.Quotient.module
variable {G : Type} [Group G]
variable (P : ProjectiveResolution (trivialIntegral G)) (n : ℕ)

abbrev resolutionSyzygy := P.complex.opcycles n

def resolutionSyzygyLift (f : resolutionSyzygy P n ⟶ resolutionSyzygy P n) :
    P.complex.X n ⟶ P.complex.X n :=
  Projective.factorThru (P.complex.pOpcycles n ≫ f) (P.complex.pOpcycles n)

@[reassoc]
theorem resolutionSyzygyLift_comm (f : resolutionSyzygy P n ⟶ resolutionSyzygy P n) :
    resolutionSyzygyLift P n f ≫ P.complex.pOpcycles n = P.complex.pOpcycles n ≫ f :=
  Projective.factorThru_comp _ _

def resolutionSyzygyMap (f : resolutionSyzygy P n ⟶ resolutionSyzygy P n) :
    resolutionSyzygy P (n + 1) ⟶ resolutionSyzygy P (n + 1) := by
  let S := resolutionOpcyclesSequence P n
  have hS := resolutionOpcyclesSequence_shortExact P n
  let : Mono S.f := hS.mono_f
  exact hS.exact.lift (S.f ≫ resolutionSyzygyLift P n f) (by
    change (P.complex.fromOpcycles (n + 1) n ≫ resolutionSyzygyLift P n f) ≫
      P.complex.pOpcycles n = 0
    rw [Category.assoc, resolutionSyzygyLift_comm, ← Category.assoc]
    have hz : P.complex.fromOpcycles (n + 1) n ≫ P.complex.pOpcycles n = 0 := S.zero
    exact (congrArg (fun a => a ≫ f) hz).trans (zero_comp))

@[reassoc]
theorem resolutionSyzygyMap_comm (f : resolutionSyzygy P n ⟶ resolutionSyzygy P n) :
    resolutionSyzygyMap P n f ≫ P.complex.fromOpcycles (n + 1) n =
      P.complex.fromOpcycles (n + 1) n ≫ resolutionSyzygyLift P n f := by
  let := (resolutionOpcyclesSequence_shortExact P n).mono_f
  apply ShortComplex.Exact.lift_f

theorem resolutionSyzygyMap_stable_of_lift
    (f : resolutionSyzygy P n ⟶ resolutionSyzygy P n)
    (l : P.complex.X n ⟶ P.complex.X n)
    (hl : l ≫ P.complex.pOpcycles n = P.complex.pOpcycles n ≫ f)
    (s : resolutionSyzygy P (n + 1) ⟶ resolutionSyzygy P (n + 1))
    (hs : s ≫ P.complex.fromOpcycles (n + 1) n = P.complex.fromOpcycles (n + 1) n ≫ l) :
    stableRepresentationClass _ _ (resolutionSyzygyMap P n f) =
      stableRepresentationClass _ _ s := by
  let S := resolutionOpcyclesSequence P n
  have hS := resolutionOpcyclesSequence_shortExact P n
  let : Mono S.f := hS.mono_f
  have hz : (resolutionSyzygyLift P n f - l) ≫ S.g = 0 := by
    change (resolutionSyzygyLift P n f - l) ≫ P.complex.pOpcycles n = 0
    rw [Preadditive.sub_comp, resolutionSyzygyLift_comm, hl, sub_self]
  let v : P.complex.X n ⟶ resolutionSyzygy P (n + 1) :=
    hS.exact.lift (resolutionSyzygyLift P n f - l) hz
  have hv : v ≫ P.complex.fromOpcycles (n + 1) n = resolutionSyzygyLift P n f - l :=
    hS.exact.lift_f _ hz
  apply (stableRepresentationClass_eq_iff_projective_factor _ _).mpr
  refine ⟨P.complex.X n, inferInstance, S.f, v, ?_⟩
  apply (cancel_mono S.f).mp
  change (P.complex.fromOpcycles (n + 1) n ≫ v) ≫ P.complex.fromOpcycles (n + 1) n =
    (resolutionSyzygyMap P n f - s) ≫ P.complex.fromOpcycles (n + 1) n
  rw [Category.assoc, hv, Preadditive.comp_sub, Preadditive.sub_comp]
  exact congrArg₂ (fun x y => x - y) (resolutionSyzygyMap_comm P n f).symm hs.symm

def resolutionSyzygyStableMap :
    (resolutionSyzygy P n ⟶ resolutionSyzygy P n) →ₗ[ℤ]
      StableRepresentationHom (resolutionSyzygy P (n + 1)) (resolutionSyzygy P (n + 1)) := by
  let a : (resolutionSyzygy P n ⟶ resolutionSyzygy P n) →+
      StableRepresentationHom (resolutionSyzygy P (n + 1)) (resolutionSyzygy P (n + 1)) :=
    AddMonoidHom.mk' (fun f => stableRepresentationClass _ _ (resolutionSyzygyMap P n f)) (by
      intro f g
      have h := resolutionSyzygyMap_stable_of_lift P n (f + g)
        (resolutionSyzygyLift P n f + resolutionSyzygyLift P n g)
        (by simp only [Preadditive.add_comp, Preadditive.comp_add, resolutionSyzygyLift_comm])
        (resolutionSyzygyMap P n f + resolutionSyzygyMap P n g)
        (by simp only [Preadditive.add_comp, Preadditive.comp_add, resolutionSyzygyMap_comm])
      exact h.trans (map_add _ _ _))
  exact { a with map_smul' := fun r f => map_intCast_smul a ℤ ℤ r f }

theorem resolutionSyzygyStableMap_eq_zero_of_projective_factor
    (f : resolutionSyzygy P n ⟶ resolutionSyzygy P n)
    (hf : stableRepresentationClass _ _ f = 0) : resolutionSyzygyStableMap P n f = 0 := by
  obtain ⟨Q, hQ, u, v, huv⟩ :=
    (stableRepresentationClass_eq_zero_iff_projective_factor f).mp hf
  let := hQ
  let S := resolutionOpcyclesSequence P n
  let a := Projective.factorThru v (P.complex.pOpcycles n)
  have ha : a ≫ P.complex.pOpcycles n = v := Projective.factorThru_comp _ _
  have h := resolutionSyzygyMap_stable_of_lift P n f
    (P.complex.pOpcycles n ≫ u ≫ a)
    (by rw [Category.assoc, Category.assoc, ha, huv])
    0 (by
      rw [zero_comp, ← Category.assoc, ← Category.assoc]
      change 0 = (S.f ≫ S.g) ≫ u ≫ a
      simp only [S.zero, zero_comp])
  exact h.trans ((stableRepresentationClass _ _).map_zero)

def resolutionStableSyzygyTransition :
    StableRepresentationHom (resolutionSyzygy P n) (resolutionSyzygy P n) →ₗ[ℤ]
      StableRepresentationHom (resolutionSyzygy P (n + 1)) (resolutionSyzygy P (n + 1)) :=
  (projectiveFactorSubmodule _ _).liftQ (resolutionSyzygyStableMap P n) (by
    intro f hf
    apply resolutionSyzygyStableMap_eq_zero_of_projective_factor P n f
    exact (Submodule.Quotient.mk_eq_zero _).mpr hf)

@[simp]
theorem resolutionStableSyzygyTransition_class
    (f : resolutionSyzygy P n ⟶ resolutionSyzygy P n) :
    resolutionStableSyzygyTransition P n (stableRepresentationClass _ _ f) =
      stableRepresentationClass _ _ (resolutionSyzygyMap P n f) := rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_SequentialResolutionVanishing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Vanishing coefficient limits in finite resolution degrees

A finite group-ring module sends a coefficient system with zero direct limit
to an eventually zero Hom system. Applying this to a cocycle in a projective
resolution proves the corresponding zero-finitary cohomology statement.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule

variable {G : Type} [Group G]

variable (A : ℕ → Rep.{0} ℤ G)
  (f : ∀ i j, i ≤ j → (A i ⟶ A j))

abbrev coefficientModuleTransition (i j : ℕ) (h : i ≤ j) :
    (A i).ρ.asModule →ₗ[ℤ[G]] (A j).ρ.asModule :=
  representationModuleHomEquiv ℤ G (A i) (A j) (f i j h)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SequentialRepresentationDiagram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Vanishing sequential systems and normalized syzygies

This packages only the sequential diagrams needed by the complete-cohomology
construction. Vanishing means that each element is killed at a later stage.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable (G : Type) [Group G]

structure SequentialRepresentationDiagram where
  obj : ℕ → Rep.{0} ℤ G
  map : ∀ i j, i ≤ j → (obj i ⟶ obj j)
  map_id : ∀ i, map i i le_rfl = 𝟙 _
  map_comp : ∀ i j k (hij : i ≤ j) (hjk : j ≤ k),
    map i j hij ≫ map j k hjk = map i k (hij.trans hjk)

namespace SequentialRepresentationDiagram
variable {G} (D : SequentialRepresentationDiagram G)

abbrev moduleMap (i j : ℕ) (h : i ≤ j) := coefficientModuleTransition D.obj D.map i j h

instance moduleMap_directed : DirectedSystem (fun i => (D.obj i).ρ.asModule)
    (fun i j h => D.moduleMap i j h) where
  map_self := by
    intro i x
    change representationModuleHomEquiv ℤ G (D.obj i) (D.obj i) (D.map i i le_rfl) x = x
    rw [D.map_id]
    rfl
  map_map := by
    intro k j i hij hjk x
    change representationModuleHomEquiv ℤ G (D.obj i) (D.obj k)
      (D.map i j hij ≫ D.map j k hjk) x = D.moduleMap i k (hij.trans hjk) x
    rw [D.map_comp]

abbrev ModuleLimit := Module.DirectLimit (fun i => (D.obj i).ρ.asModule) D.moduleMap

def mapFunctor (F : Rep.{0} ℤ G ⥤ Rep.{0} ℤ G) : SequentialRepresentationDiagram G where
  obj i := F.obj (D.obj i)
  map i j h := F.map (D.map i j h)
  map_id i := by rw [D.map_id, F.map_id]
  map_comp i j k hij hjk := by rw [← F.map_comp, D.map_comp]

end SequentialRepresentationDiagram
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SequentialRepresentationColimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete sequential colimits of representations

Only the two elementwise properties used in coefficient calculations are
packaged: every element comes from a stage, and zero is detected at a later
stage. They identify the cocone with the actual group-ring module colimit.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]
namespace SequentialRepresentationDiagram
variable (D : SequentialRepresentationDiagram G) (A : Rep.{0} ℤ G)

structure ColimitCocone where
  ι : ∀ i : ℕ, D.obj i ⟶ A
  comm : ∀ i j (h : i ≤ j), D.map i j h ≫ ι j = ι i
  surj : ∀ a : A, ∃ (i : ℕ) (x : D.obj i), (ι i).hom x = a
  zero_exact : ∀ (i : ℕ) (x : D.obj i), (ι i).hom x = 0 →
    ∃ (j : ℕ) (h : i ≤ j), (D.map i j h).hom x = 0

namespace ColimitCocone
variable {D A} (c : D.ColimitCocone A)

def moduleMap (i : ℕ) : (D.obj i).ρ.asModule →ₗ[ℤ[G]] A.ρ.asModule :=
  representationModuleHomEquiv ℤ G (D.obj i) A (c.ι i)

def moduleLift : D.ModuleLimit →ₗ[ℤ[G]] A.ρ.asModule :=
  Module.DirectLimit.lift ℤ[G] ℕ _ _ c.moduleMap (by
    intro i j h x
    change representationModuleHomEquiv ℤ G (D.obj i) A (D.map i j h ≫ c.ι j) x =
      representationModuleHomEquiv ℤ G (D.obj i) A (c.ι i) x
    rw [c.comm])

@[simp]
theorem moduleLift_of (i : ℕ) (x : (D.obj i).ρ.asModule) :
    c.moduleLift (Module.DirectLimit.of ℤ[G] ℕ _ D.moduleMap i x) = c.moduleMap i x :=
  Module.DirectLimit.lift_of _ _ _

theorem moduleLift_bijective : Function.Bijective c.moduleLift := by
  constructor
  · apply (injective_iff_map_eq_zero _).mpr
    intro z hz
    obtain ⟨i, x, rfl⟩ := Module.DirectLimit.exists_of z
    rw [c.moduleLift_of] at hz
    have hx : (c.ι i).hom ((D.obj i).ρ.asModuleEquiv x) = 0 := by
      have he := congrArg A.ρ.asModuleEquiv hz
      exact he
    obtain ⟨j, hij, hj⟩ := c.zero_exact i ((D.obj i).ρ.asModuleEquiv x) hx
    have he : D.moduleMap i j hij x = 0 := by
      apply (D.obj j).ρ.asModuleEquiv.injective
      exact hj
    have hc := Module.DirectLimit.of_f (R := ℤ[G]) (ι := ℕ)
      (G := fun i => (D.obj i).ρ.asModule) (f := D.moduleMap) (hij := hij) (x := x)
    rw [he, map_zero] at hc
    exact hc.symm
  · intro a
    obtain ⟨i, x, hx⟩ := c.surj (A.ρ.asModuleEquiv a)
    refine ⟨Module.DirectLimit.of ℤ[G] ℕ _ D.moduleMap i
      ((D.obj i).ρ.asModuleEquiv.symm x), ?_⟩
    rw [c.moduleLift_of]
    apply A.ρ.asModuleEquiv.injective
    exact hx

def moduleEquiv : D.ModuleLimit ≃ₗ[ℤ[G]] A.ρ.asModule :=
  LinearEquiv.ofBijective c.moduleLift c.moduleLift_bijective

end ColimitCocone
end SequentialRepresentationDiagram
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_AscendingQuotientColimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The concrete colimit of an ascending sequence of invariant relations

Every element is represented in the initial quotient. A class vanishes in the
quotient by the union precisely when it vanishes at a finite stage.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2300] Submodule.Quotient.module
variable {G : Type} [Group G] (A : Rep.{0} ℤ G)

abbrev RepresentationInvariant (N : Submodule ℤ A) : Prop :=
  ∀ g, N ≤ N.comap (A.ρ g)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialIntegerGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Extending polynomial identities from integral coordinates

This is the identity principle used to extend maps of nilpotent lattices to
their real polynomial coordinate groups.
-/

noncomputable section
namespace PolycyclicRecognition

theorem mvPolynomial_eq_of_integer_grid {I : Type*} (p q : MvPolynomial I ℝ)
    (h : ∀ z : I → ℤ, MvPolynomial.eval (fun i => (z i : ℝ)) p =
      MvPolynomial.eval (fun i => (z i : ℝ)) q) : p = q := by
  apply MvPolynomial.funext_set (fun _ => Set.range (Int.cast : ℤ → ℝ))
  · intro _
    exact Set.infinite_range_of_injective Int.cast_injective
  · intro x hx
    choose z hz using fun i => hx i (Set.mem_univ i)
    have he : (fun i => (z i : ℝ)) = x := funext hz
    simpa only [he] using h z

def IsCoordinatePolynomial {I J : Type*} (f : (I → ℝ) → (J → ℝ)) : Prop :=
  ∃ p : J → MvPolynomial I ℝ, ∀ x j, MvPolynomial.eval x (p j) = f x j

namespace IsCoordinatePolynomial
variable {I J K : Type*}

theorem reindex (r : J → I) : IsCoordinatePolynomial (fun x : I → ℝ => x ∘ r) := by
  refine ⟨fun j => MvPolynomial.X (r j), ?_⟩
  intro x j
  exact MvPolynomial.eval_X _

theorem comp {f : (I → ℝ) → (J → ℝ)} {g : (J → ℝ) → (K → ℝ)}
    (hg : IsCoordinatePolynomial g) (hf : IsCoordinatePolynomial f) :
    IsCoordinatePolynomial (g ∘ f) := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  refine ⟨fun k => MvPolynomial.bind₁ p (q k), ?_⟩
  intro x k
  change MvPolynomial.eval₂Hom (RingHom.id ℝ) x (MvPolynomial.bind₁ p (q k)) = _
  rw [MvPolynomial.eval₂Hom_bind₁]
  have he : (fun i => MvPolynomial.eval₂Hom (RingHom.id ℝ) x (p i)) = f x := funext (hp x)
  rw [he]
  exact hq (f x) k

theorem pair {f : (I → ℝ) → (J → ℝ)} {g : (I → ℝ) → (K → ℝ)}
    (hf : IsCoordinatePolynomial f) (hg : IsCoordinatePolynomial g) :
    IsCoordinatePolynomial (fun x => Sum.elim (f x) (g x)) := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  refine ⟨Sum.elim p q, ?_⟩
  intro x j
  cases j with
  | inl j => exact hp x j
  | inr k => exact hq x k

theorem ext_integer_grid {f g : (I → ℝ) → (J → ℝ)}
    (hf : IsCoordinatePolynomial f) (hg : IsCoordinatePolynomial g)
    (h : ∀ z : I → ℤ, f (fun i => (z i : ℝ)) = g (fun i => (z i : ℝ))) : f = g := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  have he : ∀ j, p j = q j := by
    intro j
    apply mvPolynomial_eq_of_integer_grid
    intro z
    rw [hp, hq, h z]
  funext x j
  rw [← hp, ← hq, he]

theorem ext_nat_grid {f g : (I → ℝ) → (J → ℝ)}
    (hf : IsCoordinatePolynomial f) (hg : IsCoordinatePolynomial g)
    (h : ∀ z : I → ℕ, f (fun i => (z i : ℝ)) = g (fun i => (z i : ℝ))) : f = g := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  have he : ∀ j, p j = q j := by
    intro j
    apply MvPolynomial.funext_set (fun _ => Set.range (Nat.cast : ℕ → ℝ))
    · intro _
      exact Set.infinite_range_of_injective Nat.cast_injective
    · intro x hx
      choose z hz using fun i => hx i (Set.mem_univ i)
      have hx' : (fun i => (z i : ℝ)) = x := funext hz
      rw [hp, hq, ← hx', h z]
  funext x j
  rw [← hp, ← hq, he]

end IsCoordinatePolynomial

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialCoordinateOperations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomiality of the coordinate operations in a finite Lie word -/

noncomputable section
namespace PolycyclicRecognition
namespace IsCoordinatePolynomial
variable {I J S : Type*}

theorem const (v : J → ℝ) : IsCoordinatePolynomial (fun _ : I → ℝ => v) := by
  exact ⟨fun j => MvPolynomial.C (v j), fun _ _ => MvPolynomial.eval_C _⟩

theorem add {f g : (I → ℝ) → (J → ℝ)}
    (hf : IsCoordinatePolynomial f) (hg : IsCoordinatePolynomial g) :
    IsCoordinatePolynomial (fun x => f x + g x) := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  refine ⟨fun j => p j + q j, ?_⟩
  intro x j
  simp only [map_add, hp, hq, Pi.add_apply]

theorem smul (r : ℝ) {f : (I → ℝ) → (J → ℝ)} (hf : IsCoordinatePolynomial f) :
    IsCoordinatePolynomial (fun x => r • f x) := by
  obtain ⟨p, hp⟩ := hf
  refine ⟨fun j => MvPolynomial.C r * p j, ?_⟩
  intro x j
  simp only [map_mul, MvPolynomial.eval_C, hp, Pi.smul_apply, smul_eq_mul]

theorem coordinate_smul (i : I) (v : J → ℝ) :
    IsCoordinatePolynomial (fun x : I → ℝ => x i • v) := by
  refine ⟨fun j => MvPolynomial.X i * MvPolynomial.C (v j), ?_⟩
  intro x j
  simp only [map_mul, MvPolynomial.eval_X, MvPolynomial.eval_C,
    Pi.smul_apply, smul_eq_mul]

theorem sum (s : Finset S) (f : S → (I → ℝ) → (J → ℝ))
    (hf : ∀ i ∈ s, IsCoordinatePolynomial (f i)) :
    IsCoordinatePolynomial (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using (const (I := I) (0 : J → ℝ))
  | @insert a s ha ih =>
    have hpoly := (hf a (Finset.mem_insert_self ..)).add
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))
    simpa only [Finset.sum_insert ha] using hpoly

theorem linear {d e : ℕ} (A : (Fin d → ℝ) →ₗ[ℝ] (Fin e → ℝ)) :
    IsCoordinatePolynomial A := by
  let b := Pi.basisFun ℝ (Fin d)
  refine ⟨fun j => ∑ i, MvPolynomial.C (A (b i) j) * MvPolynomial.X i, ?_⟩
  intro x j
  calc
    _ = ∑ i, A (b i) j * x i := by simp
    _ = A (∑ i, x i • b i) j := by
      simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro i _
      exact mul_comm _ _
    _ = A x j := by rw [show ∑ i, x i • b i = x from b.sum_equivFun x]

theorem bilinear {d e k : ℕ}
    (B : (Fin d → ℝ) →ₗ[ℝ] (Fin e → ℝ) →ₗ[ℝ] (Fin k → ℝ))
    {f : (I → ℝ) → (Fin d → ℝ)} {g : (I → ℝ) → (Fin e → ℝ)}
    (hf : IsCoordinatePolynomial f) (hg : IsCoordinatePolynomial g) :
    IsCoordinatePolynomial (fun x => B (f x) (g x)) := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  let b := Pi.basisFun ℝ (Fin d)
  let c := Pi.basisFun ℝ (Fin e)
  refine ⟨fun l => ∑ i, ∑ j,
    MvPolynomial.C (B (b i) (c j) l) * p i * q j, ?_⟩
  intro x l
  have hx : ∑ i, f x i • b i = f x := b.sum_equivFun _
  have hy : ∑ j, g x j • c j = g x := c.sum_equivFun _
  calc
    _ = ∑ i, ∑ j, B (b i) (c j) l * f x i * g x j := by
      simp only [map_sum, map_mul, MvPolynomial.eval_C, hp, hq]
    _ = B (∑ i, f x i • b i) (∑ j, g x j • c j) l := by
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
        Finset.smul_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      conv_rhs => rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = B (f x) (g x) l := by rw [hx, hy]

end IsCoordinatePolynomial
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_BasisPolynomialMaps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial maps in specified finite-dimensional bases -/

noncomputable section
namespace PolycyclicRecognition
open Module
variable {V W U : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  {d e k : ℕ}

def IsPolynomialInBasis (b : Basis (Fin d) ℝ V) (c : Basis (Fin e) ℝ W)
    (f : V → W) : Prop :=
  IsCoordinatePolynomial (fun x => c.equivFun (f (b.equivFun.symm x)))

namespace IsPolynomialInBasis
variable {b : Basis (Fin d) ℝ V} {c : Basis (Fin e) ℝ W}
  {a : Basis (Fin k) ℝ U}

theorem linear (f : V →ₗ[ℝ] W) : IsPolynomialInBasis b c f :=
  IsCoordinatePolynomial.linear (c.equivFun.toLinearMap.comp
    (f.comp b.equivFun.symm.toLinearMap))

theorem comp {f : V → W} {g : W → U}
    (hg : IsPolynomialInBasis c a g) (hf : IsPolynomialInBasis b c f) :
    IsPolynomialInBasis b a (g ∘ f) := by
  have h := IsCoordinatePolynomial.comp hg hf
  simpa only [IsPolynomialInBasis, Function.comp_def, LinearEquiv.symm_apply_apply] using h

theorem ext_integer_grid {f g : V → W}
    (hf : IsPolynomialInBasis b c f) (hg : IsPolynomialInBasis b c g)
    (h : ∀ z : Fin d → ℤ,
      f (b.equivFun.symm (fun i => (z i : ℝ))) =
        g (b.equivFun.symm (fun i => (z i : ℝ)))) : f = g := by
  have he := IsCoordinatePolynomial.ext_integer_grid hf hg (fun z => congrArg c.equivFun (h z))
  funext x
  apply c.equivFun.injective
  simpa only [LinearEquiv.symm_apply_apply] using congrFun he (b.equivFun x)

end IsPolynomialInBasis
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_BooleanStepRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The ring of integer-valued functions on finite Boolean partitions

Only finitely many of the chosen Boolean coordinates may be used by any one
function. These functions form an actual subring, and each function has finite
range. This provides the small coefficient algebra needed for a countable group.
-/
noncomputable section
namespace PolycyclicRecognition
variable {X I : Type}

/-- A function is constant on the cells cut out by the indicated coordinates. -/
def DependsOnBoolean (a : I → X → Bool) (s : Finset I) (f : X → ℤ) : Prop :=
  ∀ x y, (∀ i ∈ s, a i x = a i y) → f x = f y

theorem DependsOnBoolean.mono {a : I → X → Bool} {s t : Finset I} {f : X → ℤ}
    (h : DependsOnBoolean a s f) (hst : s ⊆ t) : DependsOnBoolean a t f :=
  fun x y hxy => h x y (fun i hi => hxy i (hst hi))

def booleanStepRing (a : I → X → Bool) : Subring (X → ℤ) where
  carrier := {f | ∃ s : Finset I, DependsOnBoolean a s f}
  zero_mem' := ⟨∅, fun _ _ _ => rfl⟩
  one_mem' := ⟨∅, fun _ _ _ => rfl⟩
  neg_mem' := by
    rintro f ⟨s, hs⟩
    exact ⟨s, fun x y hxy => congrArg Neg.neg (hs x y hxy)⟩
  add_mem' := by
    classical
    rintro f g ⟨s, hs⟩ ⟨t, ht⟩
    refine ⟨s ∪ t, fun x y hxy => ?_⟩
    change f x + g x = f y + g y
    rw [hs.mono (Finset.subset_union_left) x y hxy,
      ht.mono (Finset.subset_union_right) x y hxy]
  mul_mem' := by
    classical
    rintro f g ⟨s, hs⟩ ⟨t, ht⟩
    refine ⟨s ∪ t, fun x y hxy => ?_⟩
    change f x * g x = f y * g y
    rw [hs.mono (Finset.subset_union_left) x y hxy,
      ht.mono (Finset.subset_union_right) x y hxy]

def booleanPartitionCell (a : I → X → Bool) (s : Finset I) : Type :=
  Set.range (fun x : X => fun i : s => a i x)

def booleanPartitionPoint (a : I → X → Bool) (s : Finset I) (x : X) :
    booleanPartitionCell a s := ⟨fun i => a i x, ⟨x, rfl⟩⟩

instance instFiniteBooleanPartitionCell (a : I → X → Bool) (s : Finset I) : Finite (booleanPartitionCell a s) := by
  dsimp [booleanPartitionCell]
  infer_instance

def booleanPartitionRepresentative (a : I → X → Bool) (s : Finset I)
    (c : booleanPartitionCell a s) : X := c.property.choose

theorem booleanPartitionPoint_representative (a : I → X → Bool) (s : Finset I)
    (c : booleanPartitionCell a s) :
    booleanPartitionPoint a s (booleanPartitionRepresentative a s c) = c := by
  apply Subtype.ext
  exact c.property.choose_spec

theorem dependsOnBoolean_factorization {a : I → X → Bool} {s : Finset I} {f : X → ℤ}
    (h : DependsOnBoolean a s f) :
    ∃ v : booleanPartitionCell a s → ℤ,
      f = fun x => v (booleanPartitionPoint a s x) := by
  refine ⟨fun c => f (booleanPartitionRepresentative a s c), ?_⟩
  funext x
  apply h
  intro i hi
  have he := congrArg (fun c : booleanPartitionCell a s => c.val ⟨i, hi⟩)
    (booleanPartitionPoint_representative a s (booleanPartitionPoint a s x))
  exact he.symm

theorem booleanStepRing_finite_range (a : I → X → Bool) (f : booleanStepRing a) :
    (Set.range (f : X → ℤ)).Finite := by
  obtain ⟨s, hs⟩ := f.property
  obtain ⟨v, hv⟩ := dependsOnBoolean_factorization hs
  rw [hv]
  exact (Set.finite_range v).subset (Set.range_comp_subset_range _ _)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SequentialRepresentationDescent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Descent of compatible maps out of a concrete sequential colimit -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]
namespace SequentialRepresentationDiagram.ColimitCocone
variable {D : SequentialRepresentationDiagram G} {A : Rep.{0} ℤ G}
variable (c : D.ColimitCocone A) (B : Rep.{0} ℤ G)
variable (f : ∀ i, D.obj i ⟶ B)
variable (hf : ∀ i j (h : i ≤ j), D.map i j h ≫ f j = f i)

def descentModuleMap : D.ModuleLimit →ₗ[ℤ[G]] B.ρ.asModule :=
  Module.DirectLimit.lift ℤ[G] ℕ _ _
    (fun i => representationModuleHomEquiv ℤ G (D.obj i) B (f i)) (by
      intro i j h x
      change representationModuleHomEquiv ℤ G (D.obj i) B (D.map i j h ≫ f j) x = _
      rw [hf])

def desc : A ⟶ B :=
  (representationModuleHomEquiv ℤ G A B).symm
    ((descentModuleMap B f hf).comp c.moduleEquiv.symm.toLinearMap)

@[reassoc (attr := simp)]
theorem ι_desc (i : ℕ) : c.ι i ≫ c.desc B f hf = f i := by
  apply (representationModuleHomEquiv ℤ G (D.obj i) B).injective
  apply LinearMap.ext
  intro x
  have he : c.moduleEquiv.symm (c.moduleMap i x) =
      Module.DirectLimit.of ℤ[G] ℕ _ D.moduleMap i x := by
    apply c.moduleEquiv.injective
    rw [c.moduleEquiv.apply_symm_apply]
    exact (c.moduleLift_of i x).symm
  change descentModuleMap B f hf (c.moduleEquiv.symm (c.moduleMap i x)) = _
  rw [he]
  exact Module.DirectLimit.lift_of _ _ _

theorem hom_ext {f g : A ⟶ B} (h : ∀ i, c.ι i ≫ f = c.ι i ≫ g) : f = g := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro a
  obtain ⟨i, x, rfl⟩ := c.surj a
  exact ConcreteCategory.congr_hom (h i) x

end SequentialRepresentationDiagram.ColimitCocone
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_SplitProjectiveColimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Projectivity of a sequential colimit with split transition maps

This is used for countable algebras of integer-valued step functions. Finite
partition refinements give split inclusions of free modules; their actual
colimit is projective. The splitting is constructed by compatible lifts.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]
namespace SequentialRepresentationDiagram
variable (D : SequentialRepresentationDiagram G)
variable (r : ∀ i, D.obj (i + 1) ⟶ D.obj i)
variable (hr : ∀ i, D.map i (i + 1) (Nat.le_succ i) ≫ r i = 𝟙 _)

/-- Correct arbitrary lifts by the retraction so that successive lifts agree. -/
def compatibleProjectiveLift [∀ i, Projective (D.obj i)]
    {E X : Rep.{0} ℤ G} (e : E ⟶ X) [Epi e] (f : ∀ i, D.obj i ⟶ X) :
    ∀ i, D.obj i ⟶ E
  | 0 => Projective.factorThru (f 0) e
  | i + 1 => r i ≫ compatibleProjectiveLift e f i +
      (𝟙 _ - r i ≫ D.map i (i + 1) (Nat.le_succ i)) ≫
        Projective.factorThru (f (i + 1)) e

theorem compatibleProjectiveLift_comp [∀ i, Projective (D.obj i)]
    {E X : Rep.{0} ℤ G} (e : E ⟶ X) [Epi e] (f : ∀ i, D.obj i ⟶ X)
    (hf : ∀ i, D.map i (i + 1) (Nat.le_succ i) ≫ f (i + 1) = f i) (i : ℕ) :
    compatibleProjectiveLift D r e f i ≫ e = f i := by
  induction i with
  | zero => exact Projective.factorThru_comp _ _
  | succ i ih =>
    rw [compatibleProjectiveLift, Preadditive.add_comp, Category.assoc,
      ih, Category.assoc, Projective.factorThru_comp,
      Preadditive.sub_comp, Category.id_comp, Category.assoc, hf i]
    abel

include hr in
theorem compatibleProjectiveLift_step [∀ i, Projective (D.obj i)]
    {E X : Rep.{0} ℤ G} (e : E ⟶ X) [Epi e] (f : ∀ i, D.obj i ⟶ X) (i : ℕ) :
    D.map i (i + 1) (Nat.le_succ i) ≫ compatibleProjectiveLift D r e f (i + 1) =
      compatibleProjectiveLift D r e f i := by
  rw [compatibleProjectiveLift, Preadditive.comp_add, ← Category.assoc, hr i,
    Category.id_comp, ← Category.assoc, Preadditive.comp_sub, Category.comp_id,
    ← Category.assoc, hr i, Category.id_comp, sub_self, zero_comp, add_zero]

include hr in
theorem split_colimit_projective {A : Rep.{0} ℤ G} (c : D.ColimitCocone A)
    [∀ i, Projective (D.obj i)] : Projective A where
  factors {E X} f e := by
    intro he
    let u := compatibleProjectiveLift D r e (fun i => c.ι i ≫ f)
    have hu : ∀ i j (h : i ≤ j), D.map i j h ≫ u j = u i := by
      intro i j h
      induction h with
      | refl => rw [D.map_id, Category.id_comp]
      | @step j h ih =>
        rw [← D.map_comp i j (j + 1) h (Nat.le_succ j), Category.assoc]
        change D.map i j h ≫
          (D.map j (j + 1) (Nat.le_succ j) ≫
            compatibleProjectiveLift D r e (fun i => c.ι i ≫ f) (j + 1)) = _
        rw [compatibleProjectiveLift_step D r hr]
        exact ih
    refine ⟨c.desc E u hu, ?_⟩
    apply c.hom_ext
    intro i
    rw [← Category.assoc, c.ι_desc E u hu i]
    exact compatibleProjectiveLift_comp D r e (fun i => c.ι i ≫ f)
      (fun i => by rw [← Category.assoc, c.comm]) i

end SequentialRepresentationDiagram
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_BooleanStepProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Countable Boolean step rings are projective over the integers

Enumerating the Boolean coordinates gives a sequence of finite partitions.
Their modules are free, the refinement maps split, and their colimit is the
step ring itself. No freeness theorem about all bounded functions is needed.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
variable {X I : Type} (a : I → X → Bool) (b : ℕ → I)

noncomputable def booleanPrefix (n : ℕ) : Finset I := by
  classical
  exact (Finset.range n).image b

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_BooleanStepAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Translation on a Boolean step-function ring -/
noncomputable section
namespace PolycyclicRecognition
variable {G I : Type} [Group G]
variable (a : I → G → Bool) (t : G → I → I)
variable (ht : ∀ g i x, a i (g⁻¹ * x) = a (t g i) x)

def booleanStepTranslate (g : G) (f : booleanStepRing a) : booleanStepRing a := by
  classical
  refine ⟨fun x => f.val (g⁻¹ * x), ?_⟩
  obtain ⟨s, hs⟩ := f.property
  refine ⟨s.image (t g), fun x y hxy => hs _ _ ?_⟩
  intro i hi
  rw [ht, ht]
  exact hxy (t g i) (Finset.mem_image.mpr ⟨i, hi, rfl⟩)

/-- The action is by actual ring automorphisms, given by left translation. -/
@[instance_reducible]
def booleanStepMulSemiringAction : MulSemiringAction G (booleanStepRing a) where
  smul := booleanStepTranslate a t ht
  one_smul f := by
    apply Subtype.ext
    funext x
    change f.val (1⁻¹ * x) = f.val x
    rw [inv_one, one_mul]
  mul_smul g h f := by
    apply Subtype.ext
    funext x
    change f.val ((g * h)⁻¹ * x) = f.val (h⁻¹ * (g⁻¹ * x))
    rw [mul_inv_rev, mul_assoc]
  smul_zero _ := rfl
  smul_add _ _ _ := rfl
  smul_one _ := rfl
  smul_mul _ _ _ := rfl

@[simp]
theorem booleanStepTranslate_apply (g : G) (f : booleanStepRing a) (x : G) :
    (booleanStepTranslate a t ht g f).val x = f.val (g⁻¹ * x) := rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_BoundedLocallyFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing a locally finite kernel with bounded finite subgroup orders

The bound on finite subgroups remains an explicit premise. Local finiteness
then makes the whole kernel finite, and a finite kernel preserves virtual
solvability by centralizing that kernel.
-/
noncomputable section
namespace PolycyclicRecognition
variable {G : Type} [Group G]

def HasBoundedFiniteSubgroupOrders (G : Type) [Group G] : Prop :=
  ∃ b : ℕ, ∀ H : Subgroup G, Finite H → Nat.card H ≤ b

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ParametricLieWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Lie words as functions of their structure constants

The bilinear bracket itself varies in a finite-dimensional vector space.
Word evaluation is smooth jointly in that bracket and the input vectors, so
word identities and normalization equations persist under limits.
-/

noncomputable section

namespace PolycyclicRecognition

open Set

variable {V I : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {n : ℕ∞}

/-- The defining identities of a real Lie bracket, with bilinearity supplied
by its continuous-linear-map type. -/
def IsLieBracket (B : V →L[ℝ] V →L[ℝ] V) : Prop :=
  (∀ x, B x x = 0) ∧ ∀ x y z, B x (B y z) = B (B x y) z + B y (B x z)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CompactLieLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compact families of normalized Lie laws

Bounded brackets and generators satisfying fixed word-basis identities form
a compact parameter set. Limits retain the Lie identities and the exact word
normalizations, so bracket generation cannot disappear in a limit.
-/

noncomputable section

namespace PolycyclicRecognition

open Set Metric

variable {V I J : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A bilinear bracket satisfying alternation and Jacobi gives the ordinary
Lie ring structure on the existing additive group. -/
@[instance_reducible] def lieRingOfBilinear (B : V →L[ℝ] V →L[ℝ] V) (h : IsLieBracket B) : LieRing V where
  toAddCommGroup := inferInstance
  bracket := fun x y => B x y
  add_lie := by intro x y z; exact congrArg (fun f : V →L[ℝ] V => f z) (B.map_add x y)
  lie_add := by intro x y z; exact (B x).map_add y z
  lie_self := h.1
  leibniz_lie := h.2

/-- The bracket is compatible with the original real vector-space structure. -/
@[instance_reducible] def lieAlgebraOfBilinear (B : V →L[ℝ] V →L[ℝ] V) (h : IsLieBracket B) :
    @LieAlgebra ℝ V _ (lieRingOfBilinear B h) := by
  letI := lieRingOfBilinear B h
  exact { toModule := NormedSpace.toModule
          lie_smul := fun t x y => (B x).map_smul t y }

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_UnipotentProducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Concrete polynomial bounds for unipotent matrix products

Products of `n` strictly upper triangular `n × n` matrices vanish, even when
the factors are different. Consequently the preceding fixed-degree estimate
applies to arbitrarily long products of unipotent increments.
-/

namespace PolycyclicRecognition

variable {n : ℕ} {R : Type*} [Ring R]

/-- Strict upper triangularity, with diagonal vanishing included. -/
def StrictUpper (A : Matrix (Fin n) (Fin n) R) : Prop :=
  ∀ i j, j ≤ i → A i j = 0

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_FiniteLieNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bracket bounds from finitely many structure constants

The norm is the coordinate maximum in a specified basis. Consequently the
bound applies uniformly to every rescaled word basis from the box calculus.
-/

noncomputable section

namespace PolycyclicRecognition

open Module
open scoped BigOperators

variable {L J : Type*} [LieRing L] [LieAlgebra ℝ L] [Fintype J]
  (b : Basis J ℝ L)

/-- The bracket in coordinates is the bilinear expression in the actual
structure constants. -/
theorem basis_bracket_coordinate (x y : L) (l : J) :
    b.repr ⁅x, y⁆ l = ∑ i, ∑ j, b.repr x i * b.repr y j * b.repr ⁅b i, b j⁆ l := by
  conv_lhs => rw [← b.sum_repr x, ← b.sum_repr y]
  simp only [sum_lie_sum, smul_lie, lie_smul, map_sum, map_smul,
    Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul, mul_assoc, mul_left_comm]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialGroupLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial group laws in a fixed coordinate space

The binary Dynkin coefficients are fixed once in the original nilpotent
group. Changing its basis changes only the bracket. The group identities and
the straight-line one-parameter identities are closed conditions on this
finite-dimensional bracket parameter.
-/

noncomputable section

namespace PolycyclicRecognition

open Set
open scoped BigOperators

variable {V P : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Identities obeyed by a group in exponential coordinates, including its
actual straight-line one-parameter subgroups. -/
def PolynomialGroupLaws (m : V → V → V) : Prop :=
  (∀ x y z, m (m x y) z = m x (m y z)) ∧
  (∀ x, m 0 x = x) ∧ (∀ x, m x 0 = x) ∧
  (∀ x, m (-x) x = 0) ∧
  (∀ x (s t : ℝ), m (s • x) (t • x) = (s + t) • x)

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

/-- The definitional identification of `TangentSpace I x` with the model space. -/
def tangentSpaceCastModel (x : M) : TangentSpace I x ≃L[𝕜] E where
  toFun v := v
  invFun v := v
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end TangentSpaceCompat
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CoordinateConjugation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conjugation identities persist under coordinate limits

The exponential of the coordinate adjoint is the genuine logarithmic
conjugation map. This identity is closed in the bracket parameter and will
identify the columns of the limiting generator endpoint map.
-/

noncomputable section

namespace PolycyclicRecognition

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- The usual adjoint-exponential identity written entirely in fixed
coordinates. -/
def ExponentialConjugationLaw (m : V → V → V) (B : V →L[ℝ] V →L[ℝ] V) : Prop :=
  ∀ x y (t : ℝ), m (m (t • x) y) (-(t • x)) =
    NormedSpace.exp (t • B x) y

attribute [local instance 100] LieRing.ofAssociativeRing

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ExponentialProductChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Local product charts from the finite Dynkin identity

Products of exponentials in a basis have a locally surjective logarithm map.
The proof gets smoothness from the finite Dynkin polynomial and its derivative
from the exact one-coordinate restrictions. No smooth-logarithm or local
product assertion is a separate input.
-/

noncomputable section

namespace PolycyclicRecognition

open Module Set Filter
open scoped Topology ContDiff

/-- An ordered product with just one nonidentity factor equals that factor,
without a commutativity assumption. -/
theorem list_prod_ofFn_eq_single {G : Type*} [Monoid G] {n : ℕ}
    (f : Fin n → G) (i : Fin n) (hf : ∀ j, j ≠ i → f j = 1) :
    (List.ofFn f).prod = f i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    rw [List.ofFn_succ, List.prod_cons]
    refine Fin.cases ?_ (fun i => ?_) i hf
    · intro hf
      have ht : (List.ofFn (fun j : Fin n => f j.succ)).prod = 1 := by
        apply List.prod_eq_one
        intro g hg
        obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hg
        exact hf j.succ (by simp)
      rw [ht, mul_one]
    · intro hf
      rw [hf 0 (Fin.succ_ne_zero i).symm, one_mul]
      exact ih (fun j => f j.succ) i (fun j hj => hf j.succ (by simpa))

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

/-- A separate type for the group structure supplied by a coordinate law. -/
def PolynomialCoordinateGroup (m : V → V → V) (_h : PolynomialGroupLaws m) := V

namespace PolynomialCoordinateGroup

variable (m : V → V → V) (h : PolynomialGroupLaws m)

instance instGroup : Group (PolynomialCoordinateGroup m h) where
  mul x y := m x y
  mul_assoc := h.1
  one := (0 : V)
  one_mul := h.2.1
  mul_one := h.2.2.1
  inv x := -(show V from x)
  inv_mul_cancel := h.2.2.2.1

/-- Exponential coordinates identify the underlying sets bijectively. -/
def exp : V ≃ PolynomialCoordinateGroup m h := Equiv.refl _

@[simp] theorem exp_zero : exp m h 0 = 1 := rfl

@[simp] theorem exp_neg (x : V) : exp m h (-x) = (exp m h x)⁻¹ := rfl

@[simp] theorem exp_mul (x y : V) : exp m h (m x y) = exp m h x * exp m h y := rfl

end PolynomialCoordinateGroup

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_PolynomialEndpointSchemes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Smooth generator endpoint maps for varying polynomial laws

Each scheme is a fixed finite expression in the bracket, generators, and
its variable amplitudes. Consequently it remains smooth outside the set of
valid group laws, as required for the parameter-preserving submersion theorem.
-/

noncomputable section

namespace PolycyclicRecognition

open Module

variable {V P I : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

def polynomialListProduct (m : V → V → V) : List V → V
  | [] => 0
  | x :: xs => m x (polynomialListProduct m xs)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialFamilies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed-degree polynomial formulas in the independent amplitudes -/

noncomputable section

namespace PolycyclicRecognition

open MvPolynomial
open scoped BigOperators

/-- The external parameter changes coefficients, but not the degree bound. -/
def HasPolynomialFormula {P : Type*} {m : ℕ} (f : P → (Fin m → ℝ) → ℝ) : Prop :=
  ∃ D : ℕ, ∀ a, ∃ p : MvPolynomial (Fin m) ℝ,
    p.totalDegree ≤ D ∧ ∀ x, MvPolynomial.eval x p = f a x

def HasPolynomialCoordinates {P : Type*} {m n : ℕ}
    (f : P → (Fin m → ℝ) → (Fin n → ℝ)) : Prop :=
  ∀ i, HasPolynomialFormula (fun a x => f a x i)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_RemezInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Scalar polynomial sublevel estimates

M. I. Ganzburg, *A multivariate Remez-type inequality with φ-concave
weights*, Colloquium Mathematicum 147 (2017), 221–240, Theorem 1.2(a),
p. 222, DOI 10.4064/cm6884-7-2016.

The sharp estimate gives a coarse cube specialization. Its Chebyshev factor
is bounded by `(4 n |V| / |S|)^D`, using
`1 - (1 - t)^(1/n) ≥ t/n` and `T_D(x) ≤ (2*x)^D` for `x ≥ 1`.
For the cube `V = [-R,R]^n`, its volume is at most `2^n (1+R)^n`.
A fixed constant absorbs these factors. Coordinate slicing also proves
the weaker exponent `n * D`, which suffices for the image-volume estimates.
-/

noncomputable section

namespace PolycyclicRecognition

open Set Metric MeasureTheory

/-- The precise published input used to keep mass away from a polynomial's
zero set. The constant depends only on the dimension and degree. -/
def RemezPolynomialInput : Prop :=
  ∀ n D : ℕ, 1 ≤ n → 1 ≤ D → ∃ A : ℝ, 0 < A ∧
    ∀ (p : MvPolynomial (Fin n) ℝ), p.totalDegree ≤ D →
    ∀ R : ℝ, 1 ≤ R → ∀ S : Set (Fin n → ℝ),
    MeasurableSet S → S ⊆ closedBall 0 R → 0 < (volume S).toReal →
    ∀ η : ℝ, 0 ≤ η → (∀ x ∈ S, |MvPolynomial.eval x p| ≤ η) →
    ∀ x ∈ closedBall 0 R,
      |MvPolynomial.eval x p| ≤
        (A * (1 + R) ^ n / (volume S).toReal) ^ (n * D) * η

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SubexponentialBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite algebra of subexponential losses -/

namespace PolycyclicRecognition

open Filter
open scoped Topology

/-- A lower bound of the form `exp (-o(r))`, expressed without a choice
of error function. -/
def HasSubexponentialLowerBound (f : ℝ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ r in atTop, Real.exp (-ε * r) ≤ f r

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_DifferenceAmplitudeWord
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Two independent interval samples per generator switch -/

noncomputable section

namespace PolycyclicRecognition

open Module

/-- First samples minus second samples, with the same fixed order of letters. -/
def differenceParameters (m : ℕ) : (Fin (m + m) → ℝ) →L[ℝ] (Fin m → ℝ) :=
  ContinuousLinearMap.pi (fun j =>
    (ContinuousLinearMap.proj (Fin.castAdd m j) : (Fin (m + m) → ℝ) →L[ℝ] ℝ) -
      ContinuousLinearMap.proj (Fin.natAdd m j))

@[simp] theorem differenceParameters_apply (m : ℕ) (t : Fin (m + m) → ℝ) (j : Fin m) :
    differenceParameters m t j = t (Fin.castAdd m j) - t (Fin.natAdd m j) := rfl

@[simp] theorem differenceParameters_append (m : ℕ) (x y : Fin m → ℝ) :
    differenceParameters m (Fin.append x y) = x - y := by ext j; simp only [differenceParameters_apply, Fin.append_left, Fin.append_right, Pi.sub_apply]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_BundleWordCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed source bundles in joint independent coordinates -/

noncomputable section
namespace PolycyclicRecognition

open scoped BigOperators

abbrev WordLawData (I : Type*) (n : ℕ) :=
  ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) × (I → Fin n → ℝ)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RationalPowerSeriesHom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rational power-series homomorphisms killed by a power of the variable -/

noncomputable section
namespace PolycyclicRecognition

variable {A : Type*} [Ring A] [Algebra ℚ A] (F : PowerSeries ℚ →+* A)

theorem rationalPowerSeriesHom_C (q : ℚ) :
    F (PowerSeries.C q) = algebraMap ℚ A q :=
  F.map_rat_algebraMap q

theorem rationalPowerSeriesHom_polynomial (p : Polynomial ℚ) :
    F (p : PowerSeries ℚ) = Polynomial.aeval (F PowerSeries.X) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [Polynomial.coe_add, map_add, hp, hq]
  | monomial k q =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coe_mul, Polynomial.coe_C,
      Polynomial.coe_pow, Polynomial.coe_X, map_mul, map_pow, rationalPowerSeriesHom_C,
      map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_FiniteExponentialLogarithm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Compatibility with OpenAI's Mathlib (d13f23b): `log` and `exp` as inverse power series
(`Mathlib/RingTheory/PowerSeries/Log.lean` and `Substitution.lean` there). -/

namespace PowerSeries

theorem derivative_log_mul_one_add_X_compat (A : Type*) [CommRing A] [Algebra ℚ A] :
    d⁄dX A (log A) * (1 + X) = 1 := by
  ext n
  rw [mul_add, mul_one, map_add, coeff_one, deriv_log]
  cases n with
  | zero => simp [coeff_zero_mul_X]
  | succ n =>
    rw [coeff_succ_mul_X]
    simp only [coeff_mk, map_pow, map_neg, map_one, pow_succ, Nat.succ_ne_zero, if_false]
    ring

theorem eq_of_derivative_mul_one_add_X_eq_self_compat {A : Type*} [CommRing A] [IsAddTorsionFree A]
    {g : A⟦X⟧} (hderiv : d⁄dX A g * (1 + X) = g) :
    g = constantCoeff g • (1 + X) := by
  have : Invertible (1 + X : A⟦X⟧) := (isUnit_iff_constantCoeff.mpr (by simp)).invertible
  have hcu : constantCoeff (⅟(1 + X) : A⟦X⟧) = 1 := by
    have h := congrArg (constantCoeff (R := A)) (mul_invOf_self (1 + X : A⟦X⟧))
    rw [map_mul] at h
    simpa using h
  have hg : g * ⅟(1 + X) = d⁄dX A g := by
    conv_lhs => rw [← hderiv]
    rw [mul_assoc, mul_invOf_self, mul_one]
  have key : g * ⅟(1 + X) = C (constantCoeff g) := by
    refine derivative.ext ?_ ?_
    · simp only [Derivation.leibniz, derivative_invOf, map_add, derivative_one, derivative_X,
        zero_add, derivative_C, mul_one, smul_eq_mul, ← hg]
      ring
    · simp [hcu]
  rw [smul_eq_C_mul, ← key, mul_assoc, invOf_mul_self, mul_one]

theorem subst_exp_log (A : Type*) [CommRing A] [Algebra ℚ A] :
    (exp A).subst (log A) = 1 + X := by
  have : IsAddTorsionFree A := IsAddTorsionFree.of_module_rat A
  have hderiv : d⁄dX A ((exp A).subst (log A)) * (1 + X) = (exp A).subst (log A) := by
    rw [derivative_subst (hg := HasSubst.log), derivative_exp, mul_assoc,
      derivative_log_mul_one_add_X_compat, mul_one]
  have hconst : constantCoeff ((exp A).subst (log A)) = 1 := by
    rw [constantCoeff_eq, constantCoeff_subst (HasSubst.of_constantCoeff_zero' constantCoeff_log),
      finsum_eq_single _ 0 (fun d hd ↦ by
        rw [map_pow, show MvPowerSeries.constantCoeff (log A) = 0 from constantCoeff_log,
          zero_pow hd, smul_zero])]
    simp []
  have h := eq_of_derivative_mul_one_add_X_eq_self_compat hderiv
  rwa [hconst, one_smul] at h

theorem subst_log_exp_sub_one (A : Type*) [CommRing A] [Algebra ℚ A] :
    (log A).subst (exp A - 1) = X := by
  have hP : (exp A - 1).constantCoeff = 0 := by simp [constantCoeff_exp]
  have hP' : IsUnit ((exp A - 1).coeff 1) := by simp [coeff_exp]
  have hPQ : (exp A - 1).subst (log A) = X := by
    rw [subst_sub HasSubst.log, subst_exp_log A, ← coe_substAlgHom HasSubst.log (R := A), map_one]
    ring
  have hQ : log A = (exp A - 1).substInvOfIsUnit hP' := calc
    _ = PowerSeries.subst (log A) X := (subst_X HasSubst.log).symm
    _ = _ := by
      rw [← (exp A - 1).subst_substInvOfIsUnit_left hP hP',
        subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' hP) HasSubst.log _, hPQ, X_subst _]
  rw [hQ, (exp A - 1).subst_substInvOfIsUnit_left hP hP']

end PowerSeries

namespace OAI

/-! # Finite exponential and logarithm identities

Formal power-series identities evaluate in an associative rational algebra
at a nilpotent element. All expressions are finite polynomials.
-/

noncomputable section
namespace PolycyclicRecognition

variable {A : Type*} [Ring A] [Algebra ℚ A]

def finiteNilpotentLog (n : ℕ) (a : A) : A :=
  Polynomial.aeval a (PowerSeries.trunc n (PowerSeries.log ℚ))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CanonicalNilpotentLogarithm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A truncation-independent logarithm for unipotent elements -/

noncomputable section
namespace PolycyclicRecognition

variable {A : Type*} [Ring A] [Algebra ℚ A]

def nilpotentLog (a : A) : A :=
  finiteNilpotentLog (nilpotencyClass a + 1) a

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ChartedVectorFieldBracket
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Lie brackets in vector-space charts

The source chart is used only locally. This bridges the differential of an
algebra-valued map with the intrinsic bracket of vector fields.
-/

noncomputable section
namespace PolycyclicRecognition

open Set Filter Function Bundle VectorField
open scoped Manifold ContDiff Topology

variable {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]

theorem fderiv_chart_comp
    {f : M → F} (hf : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, F)) ∞ f)
    (x₀ : M) {y : E} (hy : y ∈ (extChartAt (𝓘(ℝ, E)) x₀).target) :
    fderiv ℝ (f ∘ (extChartAt (𝓘(ℝ, E)) x₀).symm) y =
      (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) f ((extChartAt (𝓘(ℝ, E)) x₀).symm y)).comp
        (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (extChartAt (𝓘(ℝ, E)) x₀).symm y) := by
  have hi : MDifferentiableAt (𝓘(ℝ, E)) (𝓘(ℝ, E))
      (extChartAt (𝓘(ℝ, E)) x₀).symm y := by
    simpa only [mfld_simps, mdifferentiableWithinAt_univ] using
      mdifferentiableWithinAt_extChartAt_symm hy
  have hh : HasFDerivAt (f ∘ (extChartAt (𝓘(ℝ, E)) x₀).symm)
      ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) f ((extChartAt (𝓘(ℝ, E)) x₀).symm y)).comp
        (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (extChartAt (𝓘(ℝ, E)) x₀).symm y)) y :=
    (((hf _).mdifferentiableAt (by simp)).hasMFDerivAt.comp y hi.hasMFDerivAt).hasFDerivAt
  exact HasFDerivAt.fderiv (𝕜 := ℝ) (E := E) (F := F) hh

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CocycleGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Sublinear cocycle bounds from compact coboundary approximation

Compact-uniform approximation by coboundaries makes an isometric cocycle
sublinear on words of linearly bounded length.
-/

namespace PolycyclicRecognition

variable {G E : Type*} [Group G] [NormedAddCommGroup E]
  [DistribMulAction G E] [IsIsometricSMul G E]

/-- The left cocycle convention for an isometric representation. -/
def IsCocycle (b : G → E) : Prop := ∀ g h, b (g * h) = b g + g • b h

omit [IsIsometricSMul G E] in
theorem IsCocycle.map_one {b : G → E} (hb : IsCocycle b) : b 1 = 0 := by
  have h := hb 1 1
  simp only [one_mul, one_smul] at h
  apply add_left_cancel (a := b 1)
  simpa only [add_zero] using h.symm

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CommutingUnipotentLogarithm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The logarithm of commuting unipotent products -/

noncomputable section
namespace PolycyclicRecognition

variable {A : Type*} [Ring A] [Algebra ℚ A]

theorem commute_nilpotentLog {a b : A} (h : Commute a b) :
    Commute (nilpotentLog a) (nilpotentLog b) := by
  unfold nilpotentLog finiteNilpotentLog
  simp only [Polynomial.aeval_eq_smeval]
  exact Polynomial.smeval_commute ℚ _ _ h

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ConjugationLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Recovering a group action from faithful conjugation

Pointwise automorphisms compatible with ambient conjugation automatically
form an action. This removes a separate action-law assumption when the Cartan
automorphisms have already been identified in a faithful representation.
-/

noncomputable section

namespace PolycyclicRecognition

variable {N D G : Type*} [Group N] [Group D] [Group G]

/-- Faithful ambient conjugation forces the action laws. -/
def conjugationLift (ι : N →* G) (κ : D →* G) (hι : Function.Injective ι)
    (a : D → MulAut N)
    (ha : ∀ d n, ι (a d n) = κ d * ι n * (κ d)⁻¹) : D →* MulAut N where
  toFun := a
  map_one' := by
    apply MulEquiv.ext
    intro n
    apply hι
    simp only [ha, map_one, inv_one, one_mul, mul_one, MulAut.one_apply]
  map_mul' d e := by
    apply MulEquiv.ext
    intro n
    apply hι
    simp only [ha, map_mul, mul_inv_rev, MulAut.mul_apply]
    simp only [mul_assoc]

@[simp] theorem conjugationLift_apply
    (ι : N →* G) (κ : D →* G) (hι : Function.Injective ι)
    (a : D → MulAut N) (ha : ∀ d n, ι (a d n) = κ d * ι n * (κ d)⁻¹)
    (d : D) : conjugationLift ι κ hι a ha d = a d := rfl

/-- A normal image supplies the pointwise automorphisms by transport from
the actual subgroup. In particular, no action is part of this premise. -/
def conjugationLiftOfNormal (ι : N →* G) (κ : D →* G) (hι : Function.Injective ι)
    (hnormal : ι.range.Normal) : D →* MulAut N := by
  let _ := hnormal
  let e : N ≃* ι.range := MonoidHom.ofInjective hι
  let a : D → MulAut N := fun d => e.trans ((MulAut.conjNormal (κ d)).trans e.symm)
  apply conjugationLift ι κ hι a
  intro d n
  simp only [a, e, MulEquiv.trans_apply, MonoidHom.apply_ofInjective_symm,
    MulAut.conjNormal_apply, MonoidHom.ofInjective_apply]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialMatrixGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial topology on invertible matrices

Both a matrix and its inverse are retained as affine coordinates. Inversion
then exchanges coordinates, and translations are polynomial coordinate maps.
The resulting topology is Noetherian and T1. Only separate continuity of
multiplication is asserted; the product topology need not be the affine
polynomial topology on a product.
-/

noncomputable section
namespace PolycyclicRecognition

@[ext]
structure PolynomialMatrixGroup (K : Type*) (n : ℕ) [Field K] where
  toGL : Matrix.GeneralLinearGroup (Fin n) K

namespace PolynomialMatrixGroup

variable {K : Type*} [Field K] {n : ℕ}

def equivGL : PolynomialMatrixGroup K n ≃ Matrix.GeneralLinearGroup (Fin n) K where
  toFun := toGL
  invFun := PolynomialMatrixGroup.mk
  left_inv _ := rfl
  right_inv _ := rfl

instance instGroup : Group (PolynomialMatrixGroup K n) := equivGL.group

def mulEquivGL : PolynomialMatrixGroup K n ≃* Matrix.GeneralLinearGroup (Fin n) K :=
  { equivGL with map_mul' := fun _ _ => rfl }

def entries (g : PolynomialMatrixGroup K n) : Matrix (Fin n) (Fin n) K := g.toGL.val

@[simp] theorem entries_mul (g h : PolynomialMatrixGroup K n) :
    entries (g * h) = entries g * entries h := rfl

abbrev Coord (n : ℕ) := Bool × Fin n × Fin n

def leftPolynomial (h : PolynomialMatrixGroup K n) (s : Coord n) :
    MvPolynomial (Coord n) K :=
  if s.1 then
    ∑ k, MvPolynomial.X (true, s.2.1, k) * MvPolynomial.C (entries h⁻¹ k s.2.2)
  else
    ∑ k, MvPolynomial.C (entries h s.2.1 k) * MvPolynomial.X (false, k, s.2.2)

def rightPolynomial (h : PolynomialMatrixGroup K n) (s : Coord n) :
    MvPolynomial (Coord n) K :=
  if s.1 then
    ∑ k, MvPolynomial.C (entries h⁻¹ s.2.1 k) * MvPolynomial.X (true, k, s.2.2)
  else
    ∑ k, MvPolynomial.X (false, s.2.1, k) * MvPolynomial.C (entries h k s.2.2)

end PolynomialMatrixGroup
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialMatrixCommutator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial continuity of commutator sections

For a fixed matrix, conjugation by the variable matrix is polynomial in
the matrix and inverse coordinates. Hence the commutator is continuous
in either variable separately in the polynomial topology.
-/

noncomputable section
namespace PolycyclicRecognition.PolynomialMatrixGroup

open scoped commutatorElement
variable {K : Type*} [Field K] {n : ℕ}

def conjugationPolynomial (h : PolynomialMatrixGroup K n) (s : Coord n) :
    MvPolynomial (Coord n) K :=
  ∑ l, ∑ k, MvPolynomial.X (false, s.2.1, k) *
    MvPolynomial.C ((if s.1 then entries h⁻¹ else entries h) k l) *
    MvPolynomial.X (true, l, s.2.2)

end PolycyclicRecognition.PolynomialMatrixGroup

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialMatrixStabilizer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Closed linear stabilizers in the polynomial matrix topology

Membership of a matrix translate in a subspace is a family of polynomial
equations, obtained from its annihilating linear functionals. Consequently
the finite-index common eigenspace stabilizer is dense and fixes that
eigenspace under a connected matrix group.
-/

noncomputable section
namespace PolycyclicRecognition.PolynomialMatrixGroup

variable {K : Type*} [Field K] {n : ℕ}

def linearAction : PolynomialMatrixGroup K n ≃*
    ((Fin n → K) ≃ₗ[K] (Fin n → K)) :=
  mulEquivGL.trans (Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin n → K)))

def functionalPolynomial (φ : Module.Dual K (Fin n → K)) (v : Fin n → K) :
    MvPolynomial (Coord n) K :=
  ∑ i, ∑ j, MvPolynomial.C (φ (fun k => if i = k then 1 else 0)) *
    MvPolynomial.X (false, i, j) * MvPolynomial.C (v j)

end PolycyclicRecognition.PolynomialMatrixGroup

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ConnectedScalarCommutators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Scalar commutators of a connected matrix group are trivial

On an invariant subspace a scalar commutator is a root of unity by its
determinant. For each vector its orbit under these commutators is therefore
finite. Polynomial continuity and connectedness make this orbit constant.
-/

noncomputable section
namespace PolycyclicRecognition.PolynomialMatrixGroup

open scoped commutatorElement
variable {K : Type*} [Field K] {n : ℕ}

def vectorPolynomial (v : Fin n → K) (i : Fin n) : MvPolynomial (Coord n) K :=
  ∑ j, MvPolynomial.X (false, i, j) * MvPolynomial.C (v j)

end PolycyclicRecognition.PolynomialMatrixGroup

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_TuplePrism
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The simplicial prism on tuples

The universal homogeneous simplex on a set has one simplex for every tuple.
Two maps of vertices are joined by the prism that uses the first map before
a chosen vertex and the second map afterwards.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
open scoped Simplicial

variable {A B : Type} {n : ℕ}

def tupleSimplicial (A : Type) : SimplicialObject (Type) where
  obj q := Fin (q.unop.len + 1) → A
  map f := ↾fun x => x ∘ f.unop.toOrderHom
  map_id _ := rfl
  map_comp _ _ := rfl

def tupleSimplicialMap (f : A → B) : tupleSimplicial A ⟶ tupleSimplicial B where
  app _ := ↾fun x => f ∘ x
  naturality _ _ _ := rfl

def tuplePrism (f g : A → B) (i : Fin (n + 1))
    (x : Fin (n + 1) → A) (k : Fin (n + 2)) : B :=
  if h : k.val ≤ i.val then f (x ⟨k.val, lt_of_le_of_lt h i.isLt⟩)
  else g (x ⟨k.val - 1, by omega⟩)

@[simp] theorem tuplePrism_zero (f g : A → B) (i : Fin (n + 1))
    (x : Fin (n + 1) → A) : tuplePrism f g i x 0 = f (x 0) := by
  simp [tuplePrism]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.Thompson_Model
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped ENNReal

universe uG

namespace ThompsonNonamenability

abbrev BoundedReal (G : Type uG) := lp (fun _ : G => ℝ) ∞

variable {G : Type uG} [Group G]

def leftPull (h : G) : BoundedReal G →ₗ[ℝ] BoundedReal G where
  toFun f := ⟨fun g => f (h * g), memℓp_infty ⟨‖f‖, by
    rintro y ⟨g, rfl⟩
    exact lp.norm_apply_le_norm ENNReal.top_ne_zero f (h * g)⟩⟩
  map_add' f g := by
    apply lp.ext
    funext x
    rfl
  map_smul' r f := by
    apply lp.ext
    funext x
    rfl

structure InvariantMean (G : Type uG) [Group G] where
  toLinearMap : BoundedReal G →ₗ[ℝ] ℝ
  positive : ∀ f : BoundedReal G, (∀ g, 0 ≤ f g) → 0 ≤ toLinearMap f
  normalized : toLinearMap 1 = 1
  left_invariant : ∀ (h : G) (f : BoundedReal G),
    toLinearMap (leftPull h f) = toLinearMap f

end ThompsonNonamenability

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.Thompson_InvariantMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Positive normalized left-invariant means

The domain is the actual space of all bounded real functions on the group.
Continuity is a consequence of positivity and normalization, not an assumption.
-/

noncomputable section

open scoped ENNReal

universe uG

namespace ThompsonNonamenability

@[simp]
theorem BoundedReal.smul_one_apply {G : Type uG} (r : ℝ) (g : G) :
    (r • (1 : BoundedReal G)) g = r := by
  simp [lp.coeFn_smul, lp.infty_coeFn_one]

variable {G : Type uG} [Group G]

@[simp]
theorem leftPull_apply (h : G) (f : BoundedReal G) (g : G) :
    leftPull h f g = f (h * g) := rfl

@[simp]
theorem leftPull_one (f : BoundedReal G) : leftPull (1 : G) f = f := by
  apply lp.ext
  funext g
  simp

namespace InvariantMean

instance instCoeFunForallSubtypePreLpRealMemAddSubgroupBoundedReal : CoeFun (InvariantMean G) (fun _ => BoundedReal G → ℝ) :=
  ⟨fun M => M.toLinearMap⟩

@[simp]
theorem map_zero (M : InvariantMean G) : M 0 = 0 := M.toLinearMap.map_zero

@[simp]
theorem map_add (M : InvariantMean G) (f g : BoundedReal G) :
    M (f + g) = M f + M g := M.toLinearMap.map_add f g

@[simp]
theorem map_sub (M : InvariantMean G) (f g : BoundedReal G) :
    M (f - g) = M f - M g := M.toLinearMap.map_sub f g

@[simp]
theorem map_smul (M : InvariantMean G) (r : ℝ) (f : BoundedReal G) :
    M (r • f) = r * M f := by
  simpa only [smul_eq_mul] using M.toLinearMap.map_smul r f

/-- Evaluation of a constant function. -/
@[simp]
theorem map_const (M : InvariantMean G) (r : ℝ) :
    M (r • (1 : BoundedReal G)) = r := by
  rw [map_smul, M.normalized, mul_one]

/-- Positivity gives monotonicity for the pointwise order. -/
theorem mono (M : InvariantMean G) {f g : BoundedReal G}
    (hfg : ∀ x, f x ≤ g x) : M f ≤ M g := by
  have h := M.positive (g - f) (fun x => sub_nonneg.mpr (hfg x))
  rw [map_sub] at h
  exact sub_nonneg.mp h

/-- A mean has norm at most one, as a consequence of its defining axioms. -/
theorem abs_apply_le_norm (M : InvariantMean G) (f : BoundedReal G) :
    |M f| ≤ ‖f‖ := by
  have hbound (g : G) : -‖f‖ ≤ f g ∧ f g ≤ ‖f‖ := by
    apply abs_le.mp
    simpa only [Real.norm_eq_abs] using
      lp.norm_apply_le_norm ENNReal.top_ne_zero f g
  have hlo := M.mono (f := (-‖f‖) • (1 : BoundedReal G)) (g := f)
    (fun g => by simpa only [BoundedReal.smul_one_apply] using (hbound g).1)
  have hhi := M.mono (f := f) (g := ‖f‖ • (1 : BoundedReal G))
    (fun g => by simpa only [BoundedReal.smul_one_apply] using (hbound g).2)
  rw [map_const] at hlo hhi
  exact abs_le.mpr ⟨hlo, hhi⟩

/-- The continuous functional furnished automatically by a positive normalized mean. -/
def toContinuousLinearMap (M : InvariantMean G) : BoundedReal G →L[ℝ] ℝ :=
  M.toLinearMap.mkContinuous 1 (fun f => by
    simpa only [one_mul, Real.norm_eq_abs] using M.abs_apply_le_norm f)

@[simp]
theorem toContinuousLinearMap_apply (M : InvariantMean G) (f : BoundedReal G) :
    M.toContinuousLinearMap f = M f := rfl

end InvariantMean

end ThompsonNonamenability

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CoarseEquivalence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Coarse equivalences of discrete groups

Finite subsets are the bounded sets in a word metric on a finitely generated
group. Controlling all finite sets of differences is the metric-free form of
being bornologous. For finitely generated groups, a coarse equivalence in this
sense is a quasi-isometry. It also matches the coarse-equivalence formulation
of Li's finiteness and duality theorems.
-/

namespace PolycyclicRecognition

open scoped Pointwise

variable {G H J : Type*} [Group G] [Group H] [Group J]

theorem groupBornologous_hom (f : G →* H) : GroupBornologous f := by
  intro S hS
  refine ⟨f '' S, hS.image f, fun x y hxy => ?_⟩
  exact ⟨x⁻¹ * y, hxy, by simp⟩

theorem GroupBornologous.comp {f : G → H} {g : H → J}
    (hg : GroupBornologous g) (hf : GroupBornologous f) :
    GroupBornologous (g ∘ f) := by
  intro S hS
  obtain ⟨T, hT, hfT⟩ := hf S hS
  obtain ⟨U, hU, hgU⟩ := hg T hT
  exact ⟨U, hU, fun x y hxy => hgU (f x) (f y) (hfT x y hxy)⟩

namespace GroupCoarseEquivalence

/-- Coarse inverses force finite fibers; this is the properness condition in
the discrete-group definition of a coarse map. -/
theorem finite_fiber (e : GroupCoarseEquivalence G H) (y : H) :
    (e.toFun ⁻¹' {y}).Finite := by
  apply (e.left_error.image (fun a => e.invFun y * a⁻¹)).subset
  intro x hx
  have hxy : e.toFun x = y := hx
  refine ⟨x⁻¹ * e.invFun y, ?_, ?_⟩
  · exact ⟨x, by dsimp only; rw [hxy]⟩
  · simp

def symm (e : GroupCoarseEquivalence G H) : GroupCoarseEquivalence H G where
  toFun := e.invFun
  invFun := e.toFun
  bornologous_toFun := e.bornologous_invFun
  bornologous_invFun := e.bornologous_toFun
  left_error := e.right_error
  right_error := e.left_error

omit [Group J] in
theorem composite_error (f : G → H) (g : H → G) (f' : H → J) (g' : J → H)
    (hg : GroupBornologous g)
    (h : (Set.range fun x => x⁻¹ * g (f x)).Finite)
    (h' : (Set.range fun y => y⁻¹ * g' (f' y)).Finite) :
    (Set.range fun x => x⁻¹ * g (g' (f' (f x)))).Finite := by
  obtain ⟨T, hT, hgT⟩ := hg _ h'
  apply (h.mul hT).subset
  rintro _ ⟨x, rfl⟩
  refine ⟨x⁻¹ * g (f x), ⟨x, rfl⟩,
    (g (f x))⁻¹ * g (g' (f' (f x))), ?_, ?_⟩
  · exact hgT (f x) (g' (f' (f x))) ⟨f x, rfl⟩
  · simp [mul_assoc]

def trans (e : GroupCoarseEquivalence G H) (e' : GroupCoarseEquivalence H J) :
    GroupCoarseEquivalence G J where
  toFun := e'.toFun ∘ e.toFun
  invFun := e.invFun ∘ e'.invFun
  bornologous_toFun := e'.bornologous_toFun.comp e.bornologous_toFun
  bornologous_invFun := e.bornologous_invFun.comp e'.bornologous_invFun
  left_error := composite_error e.toFun e.invFun e'.toFun e'.invFun
    e.bornologous_invFun e.left_error e'.left_error
  right_error := composite_error e'.invFun e'.toFun e.invFun e.toFun
    e'.bornologous_toFun e'.right_error e.right_error

end GroupCoarseEquivalence

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_ControlledCochains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cochains with finite support on controlled tuples

These are the scalar homogeneous cochains used to compare group-ring
cohomology under a coarse equivalence. Support is finite after restricting
all pairwise differences to any finite set. The pullback below uses both
bounded-difference control and finite fibers of the coarse map.
-/

noncomputable section
namespace PolycyclicRecognition

variable {G H : Type*} [Group G] [Group H]
variable (R : Type*) [CommRing R]

/-- All pairwise differences of a tuple belong to the indicated finite scale. -/
def IsControlledTuple {n : ℕ} (S : Set G) (x : Fin (n + 1) → G) : Prop :=
  ∀ i j, (x i)⁻¹ * x j ∈ S

/-- Homogeneous scalar cochains, locally finite on every controlled set. -/
def controlledCochains (G : Type*) [Group G] (n : ℕ) :
    Submodule R ((Fin (n + 1) → G) → R) where
  carrier := {c | ∀ S : Set G, S.Finite →
    {x | IsControlledTuple S x ∧ c x ≠ 0}.Finite}
  zero_mem' := by intro S _; simp
  add_mem' := by
    intro c d hc hd S hS
    apply ((hc S hS).union (hd S hS)).subset
    intro x hx
    by_cases hcx : c x = 0
    · exact Or.inr ⟨hx.1, by simpa only [Pi.add_apply, hcx, zero_add] using hx.2⟩
    · exact Or.inl ⟨hx.1, hcx⟩
  smul_mem' := by
    intro a c hc S hS
    apply (hc S hS).subset
    intro x hx
    refine ⟨hx.1, fun hz => hx.2 ?_⟩
    simp only [Pi.smul_apply, hz, smul_zero]

variable {R}

instance instCoeFunSubtypeForallForallFinHAddNatOfNatMemSubmoduleControlledCochains {n : ℕ} : CoeFun (controlledCochains R G n)
    (fun _ => (Fin (n + 1) → G) → R) := ⟨fun c => c.val⟩

/-- Coordinatewise pullback retains properness on finite tuple spaces. -/
theorem GroupCoarseEquivalence.finite_tuple_fiber (e : GroupCoarseEquivalence G H)
    (n : ℕ) (y : Fin (n + 1) → H) :
    {x : Fin (n + 1) → G | e.toFun ∘ x = y}.Finite := by
  let A (i : Fin (n + 1)) := {g : G // e.toFun g = y i}
  have hA (i : Fin (n + 1)) : Finite (A i) := (e.finite_fiber (y i)).to_subtype
  let (i : Fin (n + 1)) : Finite (A i) := hA i
  let F : {x : Fin (n + 1) → G // e.toFun ∘ x = y} → ∀ i, A i :=
    fun x i => ⟨x.val i, congrFun x.property i⟩
  have hi : Function.Injective F := by
    intro x z h
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun h i)
  exact Set.finite_coe_iff.mp (Finite.of_injective F hi)

/-- Pullback is well-defined because controlled tuples map to controlled
tuples and the map on tuples has finite fibers. -/
def controlledCochainPullback (e : GroupCoarseEquivalence G H) (n : ℕ) :
    controlledCochains R H n →ₗ[R] controlledCochains R G n where
  toFun c := ⟨fun x => c (e.toFun ∘ x), by
    intro S hS
    obtain ⟨T, hT, he⟩ := e.bornologous_toFun S hS
    have hf := (c.property T hT).preimage'
      (fun y _ => e.finite_tuple_fiber n y)
    apply hf.subset
    intro x hx
    exact ⟨fun i j => he (x i) (x j) (hx.1 i j), hx.2⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem controlledCochainPullback_apply
    (e : GroupCoarseEquivalence G H) (n : ℕ) (c : controlledCochains R H n)
    (x : Fin (n + 1) → G) : controlledCochainPullback e n c x = c (e.toFun ∘ x) := rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_ControlledTupleMaps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Properness estimates for controlled tuple maps

A bounded-difference tuple is determined up to finitely many choices once its
first vertex belongs to a finite set. This is the support estimate used for
the prism homotopy between close coarse maps.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped Pointwise
variable {G H : Type*} [Group G] [Group H] {n m : ℕ}

/-- Fixing a finite set of possible first vertices makes a controlled
set of tuples finite. -/
theorem finite_controlled_tuples_first (S A : Set G) (hS : S.Finite) (hA : A.Finite) :
    {x : Fin (n + 1) → G | IsControlledTuple S x ∧ x 0 ∈ A}.Finite := by
  let B : Set G := A * S
  have hB : B.Finite := hA.mul hS
  apply (Set.Finite.pi' (fun _ : Fin (n + 1) => hB)).subset
  intro x hx i
  exact ⟨x 0, hx.2, (x 0)⁻¹ * x i, hx.1 0 i, by simp⟩

omit [Group H] in
/-- A tuple map whose first output is the image of its first input has
finite fibers on controlled tuples whenever the underlying map is proper. -/
theorem finite_controlled_tuple_map_fiber
    (f : G → H) (hf : ∀ y, (f ⁻¹' {y}).Finite)
    (F : (Fin (n + 1) → G) → (Fin (m + 1) → H))
    (hF : ∀ x, F x 0 = f (x 0))
    (S : Set G) (hS : S.Finite) (y : Fin (m + 1) → H) :
    {x | IsControlledTuple S x ∧ F x = y}.Finite := by
  apply (finite_controlled_tuples_first S (f ⁻¹' {y 0}) hS (hf _)).subset
  intro x hx
  refine ⟨hx.1, ?_⟩
  change f (x 0) = y 0
  rw [← hF, hx.2]

/-- Mixed tuples of two close maps have uniformly controlled differences.
This is precisely the estimate required by the usual prism construction. -/
theorem controlled_mixed_tuple
    (f g : G → H) (hf : GroupBornologous f) (hg : GroupBornologous g)
    (hclose : (Set.range fun x => (f x)⁻¹ * g x).Finite)
    (S : Set G) (hS : S.Finite) :
    ∃ T : Set H, T.Finite ∧
      ∀ (x : Fin (n + 1) → G), IsControlledTuple S x →
      ∀ (a : Fin (m + 1) → Fin (n + 1)) (choose : Fin (m + 1) → Bool),
        IsControlledTuple T (fun i => if choose i then g (x (a i)) else f (x (a i))) := by
  obtain ⟨A, hA, hfA⟩ := hf S hS
  obtain ⟨B, hB, hgB⟩ := hg S hS
  let C := Set.range fun x => (f x)⁻¹ * g x
  let T := (A ∪ B) ∪ (A * C ∪ C⁻¹ * A)
  refine ⟨T, (hA.union hB).union ((hA.mul hclose).union (hclose.inv.mul hA)), ?_⟩
  intro x hx a choose i j
  have hfij := hfA (x (a i)) (x (a j)) (hx _ _)
  have hgij := hgB (x (a i)) (x (a j)) (hx _ _)
  have hci : (f (x (a i)))⁻¹ * g (x (a i)) ∈ C := ⟨_, rfl⟩
  have hcj : (f (x (a j)))⁻¹ * g (x (a j)) ∈ C := ⟨_, rfl⟩
  cases hi : choose i <;> cases hj : choose j <;> simp only [hi, hj, Bool.false_eq_true,
    ite_false, if_false, ite_true, if_true]
  · exact Or.inl (Or.inl hfij)
  · exact Or.inr (Or.inl ⟨_, hfij, _, hcj, by simp [mul_assoc]⟩)
  · apply Or.inr ∘ Or.inr
    refine ⟨((f (x (a i)))⁻¹ * g (x (a i)))⁻¹, Set.inv_mem_inv.mpr hci,
      (f (x (a i)))⁻¹ * f (x (a j)), hfij, ?_⟩
    simp [mul_assoc]
  · exact Or.inl (Or.inr hgij)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ControlledPrism
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The prism preserves controlled support

Closeness bounds all mixed pairs of vertices. Properness of the first vertex
then gives finite fibers at each controlled scale.
-/

noncomputable section
namespace PolycyclicRecognition
variable {G H R : Type} [Group G] [Group H] [CommRing R] {n : ℕ}

theorem controlled_tuplePrism (e e' : GroupCoarseEquivalence G H)
    (hc : (Set.range fun x => (e.toFun x)⁻¹ * e'.toFun x).Finite)
    (S : Set G) (hS : S.Finite) :
    ∃ T : Set H, T.Finite ∧ ∀ (x : Fin (n + 1) → G), IsControlledTuple S x →
      ∀ i, IsControlledTuple T (tuplePrism e.toFun e'.toFun i x) := by
  obtain ⟨T, hT, hmix⟩ := controlled_mixed_tuple (n := n) (m := n + 1)
    e.toFun e'.toFun e.bornologous_toFun e'.bornologous_toFun hc S hS
  refine ⟨T, hT, fun x hx i => ?_⟩
  let a : Fin (n + 2) → Fin (n + 1) := fun k =>
    if h : k.val ≤ i.val then ⟨k.val, lt_of_le_of_lt h i.isLt⟩
    else ⟨k.val - 1, by omega⟩
  let choose : Fin (n + 2) → Bool := fun k => decide (¬ k.val ≤ i.val)
  convert hmix x hx a choose using 1
  all_goals try with_reducible_and_instances rfl
  funext k
  by_cases h : k.val ≤ i.val <;> simp [tuplePrism, a, choose, h]

/-- Each prism summand is defined on the controlled cochains themselves. -/
def controlledPrismTerm (e e' : GroupCoarseEquivalence G H)
    (hc : (Set.range fun x => (e.toFun x)⁻¹ * e'.toFun x).Finite)
    (i : Fin (n + 1)) :
    controlledCochains R H (n + 1) →ₗ[R] controlledCochains R G n where
  toFun c := ⟨fun x => c (tuplePrism e.toFun e'.toFun i x), by
    intro S hS
    obtain ⟨T, hT, hprism⟩ := controlled_tuplePrism e e' hc S hS
    let C := {y : Fin (n + 2) → H | IsControlledTuple T y ∧ c y ≠ 0}
    have hC : C.Finite := c.property T hT
    have hF : (⋃ y ∈ C, {x : Fin (n + 1) → G |
        IsControlledTuple S x ∧ tuplePrism e.toFun e'.toFun i x = y}).Finite :=
      hC.biUnion (fun y _ => finite_controlled_tuple_map_fiber e.toFun e.finite_fiber
        (tuplePrism e.toFun e'.toFun i) (fun x => tuplePrism_zero _ _ _ x) S hS y)
    apply hF.subset
    intro x hx
    exact Set.mem_iUnion.mpr ⟨_, Set.mem_iUnion.mpr ⟨⟨hprism x hx.1 i, hx.2⟩, hx.1, rfl⟩⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem controlledPrismTerm_apply (e e' : GroupCoarseEquivalence G H)
    (hc : (Set.range fun x => (e.toFun x)⁻¹ * e'.toFun x).Finite)
    (i : Fin (n + 1)) (c : controlledCochains R H (n + 1))
    (x : Fin (n + 1) → G) :
    controlledPrismTerm e e' hc i c x = c (tuplePrism e.toFun e'.toFun i x) := rfl

/-- The negative alternating prism, with the sign convention of Mathlib's
chain homotopy, lowers cochain degree by one. -/
def controlledPrism (e e' : GroupCoarseEquivalence G H)
    (hc : (Set.range fun x => (e.toFun x)⁻¹ * e'.toFun x).Finite) :
    controlledCochains R H (n + 1) →ₗ[R] controlledCochains R G n :=
  -∑ i : Fin (n + 1), (-1 : R) ^ i.val • controlledPrismTerm e e' hc i

@[simp] theorem controlledPrism_apply (e e' : GroupCoarseEquivalence G H)
    (hc : (Set.range fun x => (e.toFun x)⁻¹ * e'.toFun x).Finite)
    (c : controlledCochains R H (n + 1)) (x : Fin (n + 1) → G) :
    controlledPrism e e' hc c x =
      -∑ i : Fin (n + 1), (-1 : R) ^ i.val * c (tuplePrism e.toFun e'.toFun i x) := by
  simp [controlledPrism, smul_eq_mul]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_TupleChainPrism
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The prism on free homogeneous chains

Linearization of the tuple homotopy gives the chain homotopy. The formulas
below identify its components with the alternating prism and boundary.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
open scoped Simplicial
variable {A B R : Type} [CommRing R]

def tupleFreeSimplicial (R A : Type) [CommRing R] : SimplicialObject (ModuleCat R) :=
  tupleSimplicial A ⋙ ModuleCat.monoidAlgebraFree R

def tupleChainComplex (R A : Type) [CommRing R] : ChainComplex (ModuleCat R) ℕ :=
  (AlgebraicTopology.alternatingFaceMapComplex _).obj (tupleFreeSimplicial R A)

def tupleChainMap (f : A → B) : tupleChainComplex R A ⟶ tupleChainComplex R B :=
  (AlgebraicTopology.alternatingFaceMapComplex _).map
    (((SimplicialObject.whiskering Type (ModuleCat R)).obj
      (ModuleCat.monoidAlgebraFree R)).map (tupleSimplicialMap f))

@[simp] theorem tupleChainMap_single (f : A → B) (n : ℕ) (x : Fin (n + 1) → A) :
    (tupleChainMap (R := R) f).f n (MonoidAlgebra.single x 1) =
      MonoidAlgebra.single (f ∘ x) 1 := by
  change MonoidAlgebra.mapDomainLinearMap R R (fun y => f ∘ y)
    (MonoidAlgebra.single x 1) = _
  exact MonoidAlgebra.mapDomainLinearMap_single _ _ _

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ControlledFaceSupport
attribute [-simp] _root_.OAI.PolycyclicRecognition.controlledPrismTerm_apply _root_.OAI.PolycyclicRecognition.controlledPrism_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Controlled support under face maps

Deleting a vertex has finite fibers once the pairwise differences of the
original tuple are bounded. This supplies the local finiteness needed by
the homogeneous cochain differential.
-/

noncomputable section
namespace PolycyclicRecognition

variable {G : Type*} [Group G] {n : ℕ}

/-- Faces of a controlled tuple retain the same scale. -/
theorem IsControlledTuple.face {S : Set G} {x : Fin (n + 2) → G}
    (hx : IsControlledTuple S x) (i : Fin (n + 2)) :
    IsControlledTuple S (x ∘ i.succAbove) :=
  fun j k => hx (i.succAbove j) (i.succAbove k)

/-- On controlled tuples a fixed face has only finitely many possible
missing vertices. -/
theorem finite_controlled_face_fiber (S : Set G) (hS : S.Finite)
    (i : Fin (n + 2)) (y : Fin (n + 1) → G) :
    {x : Fin (n + 2) → G | IsControlledTuple S x ∧ x ∘ i.succAbove = y}.Finite := by
  let A : Set G := Set.range y ∪ (fun s => y 0 * s) '' S
  have hA : A.Finite := (Set.finite_range y).union (hS.image _)
  apply (Set.Finite.pi' (fun _ : Fin (n + 2) => hA)).subset
  intro x hx k
  rcases Fin.eq_self_or_eq_succAbove i k with hk | ⟨j, hk⟩
  · rw [hk]
    apply Or.inr
    refine ⟨(y 0)⁻¹ * x i, ?_, by simp⟩
    have hy : x (i.succAbove 0) = y 0 := congrFun hx.2 0
    rw [← hy]
    exact hx.1 _ _
  · rw [hk]
    apply Or.inl
    exact ⟨j, (congrFun hx.2 j).symm⟩

variable {R : Type*} [CommRing R]

/-- Face pullback preserves locally finite support. -/
def controlledFace (i : Fin (n + 2)) :
    controlledCochains R G n →ₗ[R] controlledCochains R G (n + 1) where
  toFun c := ⟨fun x => c (x ∘ i.succAbove), by
    intro S hS
    let C := {y : Fin (n + 1) → G | IsControlledTuple S y ∧ c y ≠ 0}
    have hC : C.Finite := c.property S hS
    have hF : (⋃ y ∈ C,
        {x : Fin (n + 2) → G | IsControlledTuple S x ∧ x ∘ i.succAbove = y}).Finite :=
      hC.biUnion (fun y _ => finite_controlled_face_fiber S hS i y)
    apply hF.subset
    intro x hx
    exact Set.mem_iUnion.mpr ⟨x ∘ i.succAbove,
      Set.mem_iUnion.mpr ⟨⟨hx.1.face i, hx.2⟩, hx.1, rfl⟩⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem controlledFace_apply (i : Fin (n + 2))
    (c : controlledCochains R G n) (x : Fin (n + 2) → G) :
    controlledFace i c x = c (x ∘ i.succAbove) := rfl

/-- The homogeneous coboundary, as an actual map on controlled cochains. -/
def controlledCoboundary :
    controlledCochains R G n →ₗ[R] controlledCochains R G (n + 1) :=
  ∑ i : Fin (n + 2), (-1 : R) ^ i.val • controlledFace i

@[simp] theorem controlledCoboundary_apply (c : controlledCochains R G n)
    (x : Fin (n + 2) → G) :
    controlledCoboundary c x = ∑ i : Fin (n + 2), (-1 : R) ^ i.val * c (x ∘ i.succAbove) := by
  simp [controlledCoboundary, smul_eq_mul]

/-- Coordinatewise coarse pullback commutes with the homogeneous coboundary. -/
theorem controlledCoboundary_pullback {H : Type*} [Group H]
    (e : GroupCoarseEquivalence G H) (c : controlledCochains R H n) :
    controlledCoboundary (controlledCochainPullback e n c) =
      controlledCochainPullback e (n + 1) (controlledCoboundary c) := by
  apply Subtype.ext
  funext x
  simp only [controlledCoboundary_apply, controlledCochainPullback_apply]
  rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_ControlledCochainComplex
attribute [-simp] _root_.OAI.PolycyclicRecognition.controlledPrismTerm_apply _root_.OAI.PolycyclicRecognition.controlledPrism_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The complex of controlled homogeneous cochains

The square-zero identity is inherited from the standard homogeneous resolution;
the support lemmas prove that its dual differential stays inside the controlled
cochains.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory

variable {G R : Type} [Group G] [CommRing R] {n : ℕ}

def controlledLinearExtension (c : controlledCochains R G n) :
    MonoidAlgebra R (Fin (n + 1) → G) →ₗ[R] R :=
  (Finsupp.linearCombination R (fun x => c x)).comp
    (MonoidAlgebra.coeffLinearEquiv R).toLinearMap

theorem controlledLinearExtension_coboundary (c : controlledCochains R G n) :
    controlledLinearExtension (controlledCoboundary c) =
      (controlledLinearExtension c).comp (Rep.standardComplex.d R G (n + 1)) := by
  ext x
  simp [controlledLinearExtension, Rep.standardComplex.d_single,
    controlledCoboundary_apply, Finset.mul_sum]

theorem standardBoundary_squared :
    (Rep.standardComplex.d R G (n + 1)).comp (Rep.standardComplex.d R G (n + 2)) = 0 := by
  apply LinearMap.ext
  intro v
  have h := (Rep.standardComplex R G).d_comp_d (n + 2) (n + 1) n
  have hv := congrArg (fun f : (Rep.standardComplex R G).X (n + 2) ⟶
      (Rep.standardComplex R G).X n => f.hom v) h
  change ((Rep.standardComplex R G).d (n + 1) n).hom
    (((Rep.standardComplex R G).d (n + 2) (n + 1)).hom v) = 0 at hv
  rw [Rep.standardComplex.d_apply, Rep.standardComplex.d_apply] at hv
  exact hv

/-- The actual controlled coboundary squares to zero. -/
theorem controlledCoboundary_squared (c : controlledCochains R G n) :
    controlledCoboundary (controlledCoboundary c) = 0 := by
  have h : controlledLinearExtension (controlledCoboundary (controlledCoboundary c)) = 0 := by
    rw [controlledLinearExtension_coboundary, controlledLinearExtension_coboundary,
      LinearMap.comp_assoc, standardBoundary_squared, LinearMap.comp_zero]
  apply Subtype.ext
  funext x
  have hx := congrArg (fun f => f (MonoidAlgebra.single x 1)) h
  simpa [controlledLinearExtension] using hx

/-- Locally finite scalar homogeneous cochains, with the standard alternating differential. -/
def controlledCochainComplex (R G : Type) [CommRing R] [Group G] :
    CochainComplex (ModuleCat R) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of R (controlledCochains R G n))
    (fun _ => ModuleCat.ofHom controlledCoboundary) (fun _ => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      exact controlledCoboundary_squared c)

@[simp] theorem controlledCochainComplex_d (n : ℕ) :
    (controlledCochainComplex R G).d n (n + 1) = ModuleCat.ofHom controlledCoboundary := by
  simp [controlledCochainComplex, CochainComplex.of.d]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_ControlledCochainMap
attribute [-simp] _root_.OAI.PolycyclicRecognition.controlledPrismTerm_apply _root_.OAI.PolycyclicRecognition.controlledPrism_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coarse pullback as a map of controlled cochain complexes -/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
variable {G H J R : Type} [Group G] [Group H] [Group J] [CommRing R]

/-- Coarse pullback commutes with the actual homogeneous differential. -/
def controlledCochainMap (e : GroupCoarseEquivalence G H) :
    controlledCochainComplex R H ⟶ controlledCochainComplex R G :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom (controlledCochainPullback e n))
    (fun n => by
      rw [controlledCochainComplex_d, controlledCochainComplex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      change controlledCoboundary (controlledCochainPullback e n c) =
        controlledCochainPullback e (n + 1) (controlledCoboundary c)
      exact controlledCoboundary_pullback e c)

@[simp] theorem controlledCochainMap_apply (e : GroupCoarseEquivalence G H)
    (n : ℕ) (c : controlledCochains R H n) (x : Fin (n + 1) → G) :
    ((controlledCochainMap e).f n c : controlledCochains R G n).val x =
      c (e.toFun ∘ x) := rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ControlledPrismIdentity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The controlled prism identity

The identity is inherited from the actual simplicial chain homotopy, after
the support estimate has placed every summand in the controlled complex.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
variable {G H R : Type} [Group G] [Group H] [CommRing R] {n : ℕ}

@[simp] theorem controlledLinearExtension_single (c : controlledCochains R G n)
    (x : Fin (n + 1) → G) (r : R) :
    controlledLinearExtension c (MonoidAlgebra.single x r) = r * c x := by
  simp [controlledLinearExtension]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ControlledFiniteChains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite chains at a controlled scale

These submodules retain a finite set of allowed relative positions. They
provide the chain-level control needed for the remaining FP transfer argument.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
variable {R G H : Type} [CommRing R] [Group G] [Group H] {n m : ℕ}

def controlledChainSpan (R G : Type) [CommRing R] [Group G] (n : ℕ) (S : Set G) :
    Submodule R (MonoidAlgebra R (Fin (n + 1) → G)) :=
  Submodule.span R {c | ∃ x, IsControlledTuple S x ∧ c = MonoidAlgebra.single x 1}

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_ControlledCochainHomotopy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Close coarse maps give homotopic controlled pullbacks -/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory HomologicalComplex
variable {G H R : Type} [Group G] [Group H] [CommRing R]

def controlledPrismHom (e e' : GroupCoarseEquivalence G H)
    (hc : (Set.range fun x => (e.toFun x)⁻¹ * e'.toFun x).Finite) (i j : ℕ) :
    (controlledCochainComplex R H).X i ⟶ (controlledCochainComplex R G).X j :=
  if h : j + 1 = i then
    h ▸ (show (controlledCochainComplex R H).X (j + 1) ⟶
      (controlledCochainComplex R G).X j from
        ModuleCat.ofHom (controlledPrism (n := j) e e' hc))
  else 0

@[simp] theorem controlledPrismHom_succ (e e' : GroupCoarseEquivalence G H)
    (hc : (Set.range fun x => (e.toFun x)⁻¹ * e'.toFun x).Finite) (n : ℕ) :
    controlledPrismHom (R := R) e e' hc (n + 1) n =
      ModuleCat.ofHom (controlledPrism e e' hc) := by
  unfold controlledPrismHom
  exact dite_eq_left rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_CoarseGroupRingCohomology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coarse invariance of group-ring cohomology

The maps need not be homomorphisms. Their finite coarse errors provide the
controlled prism homotopies, and hence inverse maps on group-ring cohomology.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
variable {G H R : Type} [Group G] [Group H] [CommRing R]

def GroupCoarseEquivalence.refl (G : Type) [Group G] : GroupCoarseEquivalence G G where
  toFun := id
  invFun := id
  bornologous_toFun := groupBornologous_hom (MonoidHom.id G)
  bornologous_invFun := groupBornologous_hom (MonoidHom.id G)
  left_error := by simp
  right_error := by simp

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ControlledCycleFillings
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coarse invariance of uniformly controlled cycle fillings

Only finite chains occur here. A fixed input scale must admit a fixed filling
scale for every cycle. This quantitative condition is stronger than ordinary
acyclicity of the standard resolution and is the condition needed in the
remaining finiteness argument.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory HomologicalComplex
variable {R G H J : Type} [CommRing R] [Group G] [Group H] [Group J] {n : ℕ}

def HasControlledCycleFillings (R G : Type) [CommRing R] [Group G] (n : ℕ) : Prop :=
  ∀ S : Set G, S.Finite → ∃ T : Set G, T.Finite ∧
    ∀ c : MonoidAlgebra R (Fin (n + 2) → G), c ∈ controlledChainSpan R G (n + 1) S →
      (tupleChainComplex R G).d (n + 1) n c = 0 →
      ∃ b : MonoidAlgebra R (Fin (n + 3) → G),
        b ∈ controlledChainSpan R G (n + 2) T ∧
          (tupleChainComplex R G).d (n + 2) (n + 1) b = c

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_StationarySlope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Averaging the stationary height cocycle

The normalized pair space carries a measure-preserving action. Its height
evaluation is a cocycle for inverse pullback. We construct that action on the
actual space `L²`, and show that integration gives an additive slope. No
reduced-cohomology assertion is assumed in this construction.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Filter

variable {G X W : Type*} [Group G] [MeasurableSpace X] [MulAction G X]
  [MeasurableConstSMul G X]
  [NormedAddCommGroup W]
  (μ : Measure X) [SMulInvariantMeasure G X μ]

/-- Inverse pullback is the left representation associated to a left action. -/
def stationaryPullback (g : G) : Lp W 2 μ →+ Lp W 2 μ :=
  Lp.compMeasurePreserving (fun x : X => g⁻¹ • x) (measurePreserving_smul g⁻¹ μ)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FiniteOrbitAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite convex averages of translates

The same finite data act on actual functions and on their L2 classes. This
allows the averages to be transported to a conditional component measure.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set

/-- A finite probability distribution on acting elements. -/
structure FiniteOrbitAverage (G : Type*) where
  index : Type
  [finiteIndex : Fintype index]
  weight : index → ℝ
  nonneg : ∀ i, 0 ≤ weight i
  mass : ∑ i, weight i = 1
  element : index → G

attribute [instance] FiniteOrbitAverage.finiteIndex

variable {G X : Type*} [Group G] [MulAction G X]

/-- The actual finite average, with the inverse convention of the Koopman action. -/
def FiniteOrbitAverage.apply (A : FiniteOrbitAverage G) (f : X → ℝ) (x : X) : ℝ :=
  ∑ i, A.weight i * f ((A.element i)⁻¹ • x)

variable [MeasurableSpace X] [MeasurableConstSMul G X]

variable
  (μ : Measure X) [SMulInvariantMeasure G X μ]

/-- The same average of the actual unitary operators. -/
def FiniteOrbitAverage.onL2 (A : FiniteOrbitAverage G) (v : Lp ℝ 2 μ) : Lp ℝ 2 μ :=
  ∑ i, A.weight i • stationaryPullback μ (A.element i) v

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FiniteUnitaryAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite simultaneous averages in a unitary representation

Each finite convex averaging operator is a contraction. Successively averaging
each of finitely many vectors preserves all earlier bounds. This is the
Hilbert averaging step used for the abelian cohomology base case.
-/

noncomputable section

namespace PolycyclicRecognition

open Set

variable {G E : Type*} [Group G] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def FiniteOrbitAverage.onVector (A : FiniteOrbitAverage G)
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) : E := ∑ i, A.weight i • ρ (A.element i) x

def FiniteOrbitAverage.compose (A B : FiniteOrbitAverage G) : FiniteOrbitAverage G where
  index := A.index × B.index
  weight ij := A.weight ij.1 * B.weight ij.2
  nonneg ij := mul_nonneg (A.nonneg _) (B.nonneg _)
  mass := by simp only [Fintype.sum_prod_type, ← Finset.mul_sum, B.mass, mul_one, A.mass]
  element ij := A.element ij.1 * B.element ij.2

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_ReducedCohomologyInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The precise published reduced-cohomology input

Cornulier--Tessera, *On the vanishing of reduced 1-cohomology for Banach
representations*, Ann. Inst. Fourier 70 (2020), 1951--2003, Corollary 1.9,
together with Definition 1.1: real-triangulable Lie groups have `WAP_t`.
The proposition below is only its real Hilbert-space consequence, for the
particular representation used by the application. Isometric Hilbert
representations are weakly almost periodic. The topology on cocycles is
uniform norm convergence on compact subsets, as defined in §1.1.

Source: https://aif.centre-mersenne.org/item/10.5802/aif.3363.pdf
-/

namespace PolycyclicRecognition

variable (G E : Type*) [Group G] [TopologicalSpace G]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [DistribMulAction G E] [IsIsometricSMul G E] [SMulCommClass G ℝ E]

/-- The needed Hilbert-space specialization of Corollary 1.9. Continuity and
absence of invariant vectors are hypotheses of the published theorem. -/
def ReducedCohomologyInput (G E : Type*) [Group G] [TopologicalSpace G]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [DistribMulAction G E] [IsIsometricSMul G E] [SMulCommClass G ℝ E] : Prop :=
  (∀ v : E, (∀ g : G, g • v = v) → v = 0) →
  (∀ v : E, Continuous (fun g : G => g • v)) →
  ∀ b : G → E, Continuous b → IsCocycle b →
    ∀ Q : Set G, IsCompact Q → ∀ ε : ℝ, 0 < ε →
      ∃ φ : E, ∀ q ∈ Q, ‖b q + q • φ - φ‖ ≤ ε

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_UnitaryCocycle
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

def IsUnitaryCocycle (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (b : G → E) : Prop :=
  ∀ g h, b (g * h) = b g + ρ g (b h)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ControlledReiterCocycles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Controlled scalar averages turn sublinear cocycles into coboundaries

The geometric data are compactly supported probability densities with
translation error of order inverse scale and support of order scale.
They contain no representation or cohomology hypotheses.
-/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Filter

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]

structure ControlledReiterFamily (μ : Measure G) (length : G → ℝ) where
  scale : ℕ → ℝ
  scale_pos : ∀ n, 0 < scale n
  scale_tendsto : Tendsto scale atTop atTop
  weight : ℕ → G → ℝ
  continuous_weight : ∀ n, Continuous (weight n)
  compact_support : ∀ n, HasCompactSupport (weight n)
  nonneg : ∀ n x, 0 ≤ weight n x
  mass : ∀ n, ∫ x, weight n x ∂μ = 1
  control : ∀ Q : Set G, IsCompact Q → ∃ A C : ℝ, 0 ≤ A ∧ 0 ≤ C ∧
    ∀ᶠ n in atTop, ∀ q, q ∈ Q →
      (∀ x, weight n (q⁻¹ * x) - weight n x ≠ 0 → length x ≤ A * scale n) ∧
      (∫ x, |weight n (q⁻¹ * x) - weight n x| ∂μ) ≤ C / scale n

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CoordinateOrbitRepresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Linearizing a group through its translated coordinate functions

Right translates of separating coordinates span a faithful representation.
A uniform finite-dimensional space containing those translates makes the
representation finite dimensional; polynomial multiplication will supply it.
-/

noncomputable section
namespace PolycyclicRecognition

variable {G I : Type*} [Group G] (q : I → G → ℝ)

def rightTranslateLinear (g : G) : (G → ℝ) →ₗ[ℝ] (G → ℝ) where
  toFun f x := f (x * g)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CoordinatePolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial restrictions to coordinate lines -/

noncomputable section
namespace PolycyclicRecognition

open Polynomial

/-- Each coordinate-line restriction is a polynomial of degree at most `D`. -/
def CoordinatePolynomial (n D : ℕ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ (i : Fin n) (x : Fin n → ℝ), ∃ p : ℝ[X], p.natDegree ≤ D ∧
    ∀ t : ℝ, p.eval t = f (Function.update x i t)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_EnvelopingTruncation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite word truncation of an enveloping algebra

The ideal is generated by all sufficiently long products of Lie generators.
It is invariant under every extended Lie derivation.
-/

noncomputable section
namespace PolycyclicRecognition

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

local notation "U" => UniversalEnvelopingAlgebra R L
local notation "η" => UniversalEnvelopingAlgebra.ι R (L := L)

def envelopingLongWords (c : ℕ) : Set U :=
  {u | ∃ l : List L, c ≤ l.length ∧ (l.map η).prod = u}

def envelopingTruncationIdeal (c : ℕ) : TwoSidedIdeal U :=
  TwoSidedIdeal.span (envelopingLongWords (R := R) (L := L) c)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ExtensionSectionFactor
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

namespace GroupExtensionSection
variable (S : GroupExtension N G Q) (σ : S.Section)

/-- This element measures the failure of the chosen section to multiply. -/
def factor (q r : Q) : N :=
  Classical.choose (σ.mul_mul_mul_inv_mem_range_inl q r)

@[simp] theorem inl_factor (q r : Q) :
    S.inl (factor S σ q r) = σ q * σ r * (σ (q * r))⁻¹ :=
  Classical.choose_spec (σ.mul_mul_mul_inv_mem_range_inl q r)

theorem factor_one_left (hσ : σ 1 = 1) (q : Q) : factor S σ 1 q = 1 := by
  apply S.inl_injective
  simp only [inl_factor, hσ, one_mul, mul_inv_cancel, map_one]

theorem factor_one_right (hσ : σ 1 = 1) (q : Q) : factor S σ q 1 = 1 := by
  apply S.inl_injective
  simp only [inl_factor, hσ, mul_one, mul_inv_cancel, map_one]

/-- The exact nonabelian two-cocycle identity. -/
theorem factor_cocycle (q r s : Q) :
    factor S σ q r * factor S σ (q * r) s =
      S.conjAct (σ q) (factor S σ r s) * factor S σ q (r * s) := by
  apply S.inl_injective
  simp only [map_mul, inl_factor, S.inl_conjAct_comm]
  rw [mul_assoc q r s]
  group

/-- Conjugation by the section multiplies up to the stated inner factor. -/
theorem section_action_mul (q r : Q) :
    S.conjAct (σ q) * S.conjAct (σ r) =
      MulAut.conj (factor S σ q r) * S.conjAct (σ (q * r)) := by
  apply DFunLike.ext
  intro x
  apply S.inl_injective
  change S.inl (S.conjAct (σ q) (S.conjAct (σ r) x)) =
    S.inl (factor S σ q r * S.conjAct (σ (q * r)) x * (factor S σ q r)⁻¹)
  simp only [S.inl_conjAct_comm, map_mul, map_inv, inl_factor]
  group

end GroupExtensionSection
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanMultiplication
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Multiplication of overlapping Cartan factors

Compatible conjugation gives the actual multiplication homomorphism from the
semidirect product. Its kernel records the overlap. Local surjectivity makes
it globally surjective in a connected ambient group, and an open product map
then has compact lifts of compact sets. No complementary subgroup is assumed.
-/

noncomputable section

namespace PolycyclicRecognition

open Set Topology
open scoped Topology

variable {N D G : Type*} [Group N] [Group D] [Group G]
  (ι : N →* G) (κ : D →* G) (φ : D →* MulAut N)
  (hconj : ∀ d n, ι (φ d n) = κ d * ι n * (κ d)⁻¹)

set_option maxHeartbeats 1000000 in
/-- Actual factor multiplication as a group homomorphism. -/
def cartanMultiplication : N ⋊[φ] D →* G :=
  SemidirectProduct.lift ι κ (fun d => by
    ext n
    exact hconj d n)

set_option maxHeartbeats 1000000 in
@[simp] theorem cartanMultiplication_apply (z : N ⋊[φ] D) :
    cartanMultiplication ι κ φ hconj z = ι z.left * κ z.right := rfl

set_option maxHeartbeats 1000000 in
/-- This kernel equation retains the entire overlap of the factors. -/
theorem mem_cartanMultiplication_ker (z : N ⋊[φ] D) :
    z ∈ (cartanMultiplication ι κ φ hconj).ker ↔ ι z.left = (κ z.right)⁻¹ := by
  simp only [MonoidHom.mem_ker, cartanMultiplication_apply, mul_eq_one_iff_eq_inv]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FactorAutomorphismDescent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Descending automorphisms through overlapping group factors -/

noncomputable section
namespace PolycyclicRecognition

/-- A commutation identity can be checked on surjective coordinate maps. -/
theorem commutes_of_surjective_coordinates {X Y N D : Type*}
    (eN : X → N) (eD : Y → D) (hn : Function.Surjective eN) (hd : Function.Surjective eD)
    (A : N → N) (B : D → N → N) (a : X → X) (b : Y → X → X)
    (hA : ∀ x, A (eN x) = eN (a x))
    (hB : ∀ y x, B (eD y) (eN x) = eN (b y x))
    (hab : ∀ y x, a (b y x) = b y (a x)) : ∀ d n, A (B d n) = B d (A n) := by
  intro d n
  obtain ⟨y,rfl⟩ := hd d
  obtain ⟨x,rfl⟩ := hn n
  rw [hB,hA,hA,hB,hab]

/-- Invariance of a character can be checked in surjective factor coordinates. -/
theorem character_invariant_of_factor_coordinates {X N D G Q K : Type*}
    [Monoid N] [Monoid D] [Monoid G] [Monoid Q]
    (ι : N →* G) (κ : D →* G) (q : G →* Q) (e : X → N)
    (he : Function.Surjective e)
    (hp : Function.Surjective (fun p : N × D => ι p.1 * κ p.2))
    (rot : K → X → X) (act : K → G → G)
    (hq : ∀ x, q (ι (e x)) = 1)
    (ha : ∀ k x d, act k (ι (e x) * κ d) = ι (e (rot k x)) * κ d) :
    ∀ k g, q (act k g) = q g := by
  intro k g
  obtain ⟨⟨n,d⟩,hnd⟩ := hp g
  obtain ⟨x,hx⟩ := he n
  have hg : ι (e x) * κ d = g := (congrArg (fun t => ι t * κ d) hx).trans hnd
  rw [← hg,ha,map_mul,map_mul,hq,hq]

variable {N D G K : Type*} [Group N] [Group D] [Group G] [Group K]
  (ι : N →* G) (κ : D →* G) (φ : D →* MulAut N)
  (hconj : ∀ d n, ι (φ d n) = κ d * ι n * (κ d)⁻¹)
  (hsurj : Function.Surjective (fun p : N × D => ι p.1 * κ p.2))
  (α : K →* MulAut N)
  (hcomm : ∀ k d n, α k (φ d n) = φ d (α k n))
  (hfix : ∀ k n d, ι n = κ d → α k n = n)

def rotatedFactorHom (k : K) : N ⋊[φ] D →* G :=
  (cartanMultiplication ι κ φ hconj).comp
    (SemidirectProduct.map (α k).toMonoidHom (MonoidHom.id D) (fun d => by
      ext n
      exact hcomm k d n))

include hsurj in
theorem factorHom_surjective :
    Function.Surjective (cartanMultiplication ι κ φ hconj) := by
  intro g
  obtain ⟨⟨n,d⟩,he⟩ := hsurj g
  exact ⟨⟨n,d⟩,he⟩

include hfix in
theorem rotatedFactorHom_kernel (k : K) :
    (cartanMultiplication ι κ φ hconj).ker ≤
      (rotatedFactorHom ι κ φ hconj α hcomm k).ker := by
  intro p hp
  have hn : ι p.left = κ p.right⁻¹ := by
    simpa only [map_inv] using (mem_cartanMultiplication_ker ι κ φ hconj p).mp hp
  have hf := hfix k p.left p.right⁻¹ hn
  change ι (α k p.left) * κ p.right = 1
  rw [hf, hn, map_inv, inv_mul_cancel]

/-- The induced endomorphism on the original group. -/
def descendedFactorHom (k : K) : G →* G :=
  (cartanMultiplication ι κ φ hconj).liftOfSurjective
    (factorHom_surjective ι κ φ hconj hsurj)
    ⟨rotatedFactorHom ι κ φ hconj α hcomm k,
      rotatedFactorHom_kernel ι κ φ hconj α hcomm hfix k⟩

@[simp] theorem descendedFactorHom_product (k : K) (n : N) (d : D) :
    descendedFactorHom ι κ φ hconj hsurj α hcomm hfix k (ι n * κ d) =
      ι (α k n) * κ d := by
  exact (cartanMultiplication ι κ φ hconj).liftOfRightInverse_comp_apply _ _ _ ⟨n,d⟩

theorem descendedFactorHom_one (g : G) :
    descendedFactorHom ι κ φ hconj hsurj α hcomm hfix 1 g = g := by
  obtain ⟨⟨n,d⟩,rfl⟩ := hsurj g
  simp

theorem descendedFactorHom_mul (k l : K) (g : G) :
    descendedFactorHom ι κ φ hconj hsurj α hcomm hfix (k*l) g =
      descendedFactorHom ι κ φ hconj hsurj α hcomm hfix k
        (descendedFactorHom ι κ φ hconj hsurj α hcomm hfix l g) := by
  obtain ⟨⟨n,d⟩,rfl⟩ := hsurj g
  simp

/-- An action on the first factor commuting with the second factor and
fixing their actual intersection descends to an action on the whole group. -/
def descendedFactorAction : K →* MulAut G where
  toFun k :=
    { toFun := descendedFactorHom ι κ φ hconj hsurj α hcomm hfix k
      invFun := descendedFactorHom ι κ φ hconj hsurj α hcomm hfix k⁻¹
      left_inv g := by
        rw [← descendedFactorHom_mul, inv_mul_cancel, descendedFactorHom_one]
      right_inv g := by
        rw [← descendedFactorHom_mul, mul_inv_cancel, descendedFactorHom_one]
      map_mul' := (descendedFactorHom ι κ φ hconj hsurj α hcomm hfix k).map_mul }
  map_one' := by
    ext g
    exact descendedFactorHom_one ι κ φ hconj hsurj α hcomm hfix g
  map_mul' k l := by
    ext g
    exact descendedFactorHom_mul ι κ φ hconj hsurj α hcomm hfix k l g

@[simp] theorem descendedFactorAction_product (k : K) (n : N) (d : D) :
    descendedFactorAction ι κ φ hconj hsurj α hcomm hfix k (ι n * κ d) =
      ι (α k n) * κ d :=
  descendedFactorHom_product ι κ φ hconj hsurj α hcomm hfix k n d

section Topology
variable [TopologicalSpace N] [TopologicalSpace D] [TopologicalSpace G]
  [TopologicalSpace K] [IsTopologicalGroup G]

/-- Joint continuity descends through the open factor product. -/
theorem continuous_descendedFactorAction
    (hι : Continuous ι) (hκ : Continuous κ)
    (hα : Continuous (fun p : K × N => α p.1 p.2))
    (hopen : IsOpenMap (fun p : N × D => ι p.1 * κ p.2)) :
    Continuous (fun p : K × G => descendedFactorAction ι κ φ hconj hsurj α hcomm hfix p.1 p.2) := by
  let q : K × (N × D) → K × G := Prod.map id (fun p => ι p.1 * κ p.2)
  have hqc : Continuous q := continuous_id.prodMap ((hι.comp continuous_fst).mul
    (hκ.comp continuous_snd))
  have hqs : Function.Surjective q := Function.Surjective.prodMap Function.surjective_id hsurj
  have hqo : IsOpenMap q := IsOpenMap.id.prodMap hopen
  apply (hqo.isQuotientMap hqc hqs).continuous_iff.mpr
  have he : (fun p : K × G => descendedFactorAction ι κ φ hconj hsurj α hcomm hfix p.1 p.2) ∘ q =
      fun p : K × (N × D) => ι (α p.1 p.2.1) * κ p.2.2 := by
    funext p
    exact descendedFactorAction_product ι κ φ hconj hsurj α hcomm hfix p.1 p.2.1 p.2.2
  rw [he]
  exact (hι.comp (hα.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd)))).mul
    (hκ.comp (continuous_snd.comp continuous_snd))

end Topology
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NonabelianFactorSystem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Groups from a normalized nonabelian factor system

The multiplication retains the inner correction, so quotient lifts are not
required to commute or to give a splitting.
-/

namespace PolycyclicRecognition

structure NonabelianFactorSystem (N Q : Type*) [Group N] [Group Q] where
  action : Q → MulAut N
  factor : Q → Q → N
  action_one : action 1 = 1
  factor_one_left : ∀ q, factor 1 q = 1
  factor_one_right : ∀ q, factor q 1 = 1
  action_mul : ∀ q r, action q * action r = MulAut.conj (factor q r) * action (q * r)
  cocycle : ∀ q r s, factor q r * factor (q * r) s =
    action q (factor r s) * factor q (r * s)

namespace NonabelianFactorSystem
variable {N Q : Type*} [Group N] [Group Q] (S : NonabelianFactorSystem N Q)

theorem action_mul_apply (q r : Q) (x : N) :
    S.action q (S.action r x) =
      S.factor q r * S.action (q * r) x * (S.factor q r)⁻¹ :=
  DFunLike.congr_fun (S.action_mul q r) x

end NonabelianFactorSystem

@[ext] structure FactorExtension {N Q : Type*} [Group N] [Group Q]
    (S : NonabelianFactorSystem N Q) where
  left : N
  right : Q

namespace FactorExtension
variable {N Q : Type*} [Group N] [Group Q] (S : NonabelianFactorSystem N Q)

instance instOne : One (FactorExtension S) := ⟨⟨1, 1⟩⟩
instance instMul : Mul (FactorExtension S) :=
  ⟨fun a b => ⟨a.left * S.action a.right b.left * S.factor a.right b.right,
    a.right * b.right⟩⟩
instance instInv : Inv (FactorExtension S) :=
  ⟨fun a => ⟨(S.factor a.right⁻¹ a.right)⁻¹ * S.action a.right⁻¹ a.left⁻¹, a.right⁻¹⟩⟩

@[simp] theorem one_left : (1 : FactorExtension S).left = 1 := rfl
@[simp] theorem one_right : (1 : FactorExtension S).right = 1 := rfl
@[simp] theorem mul_left (a b : FactorExtension S) :
    (a * b).left = a.left * S.action a.right b.left * S.factor a.right b.right := rfl
@[simp] theorem mul_right (a b : FactorExtension S) : (a * b).right = a.right * b.right := rfl
@[simp] theorem inv_left (a : FactorExtension S) :
    a⁻¹.left = (S.factor a.right⁻¹ a.right)⁻¹ * S.action a.right⁻¹ a.left⁻¹ := rfl
@[simp] theorem inv_right (a : FactorExtension S) : a⁻¹.right = a.right⁻¹ := rfl

instance instGroup : Group (FactorExtension S) where
  mul_assoc a b c := by
    apply FactorExtension.ext
    · simp only [mul_left, mul_right, map_mul, S.action_mul_apply]
      simp only [mul_assoc]
      rw [← S.cocycle]
      group
    · exact mul_assoc _ _ _
  one_mul a := by
    apply FactorExtension.ext
    · simp only [mul_left, one_left, one_right, S.action_one, MulAut.one_apply,
        S.factor_one_left, one_mul, mul_one]
    · exact one_mul _
  mul_one a := by
    apply FactorExtension.ext
    · simp only [mul_left, one_left, one_right, map_one, S.factor_one_right, mul_one]
    · exact mul_one _
  inv_mul_cancel a := by
    apply FactorExtension.ext
    · simp only [mul_left, inv_left, inv_right, map_inv, one_left]
      group
    · exact inv_mul_cancel _

/-- The kernel inclusion into the group with the given factor system. -/
def inl : N →* FactorExtension S where
  toFun x := ⟨x, 1⟩
  map_one' := rfl
  map_mul' x y := by
    apply FactorExtension.ext
    · simp only [mul_left, S.action_one, MulAut.one_apply, S.factor_one_left, mul_one]
    · exact (one_mul (1 : Q)).symm

/-- Projection to the original quotient. -/
def projection : FactorExtension S →* Q where
  toFun a := a.right
  map_one' := rfl
  map_mul' _ _ := rfl

theorem inl_injective : Function.Injective (inl S) := by
  intro x y h
  exact congrArg FactorExtension.left h

theorem projection_surjective : Function.Surjective (projection S) :=
  fun q => ⟨⟨1, q⟩, rfl⟩

/-- The product coordinates are an actual equivalence of sets. -/
def equivProd : FactorExtension S ≃ N × Q where
  toFun a := (a.left, a.right)
  invFun a := ⟨a.1, a.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end FactorExtension
end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FactorExtensionMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Maps between groups with the same quotient factor system -/

namespace PolycyclicRecognition.FactorExtension
variable {N M Q : Type*} [Group N] [Group M] [Group Q]
  (S : NonabelianFactorSystem N Q) (T : NonabelianFactorSystem M Q)
  (f : N →* M)
  (ha : ∀ q n, f (S.action q n) = T.action q (f n))
  (hc : ∀ q r, f (S.factor q r) = T.factor q r)

/-- Extend a kernel homomorphism compatible with both action and cocycle. -/
def map : FactorExtension S →* FactorExtension T where
  toFun a := ⟨f a.left, a.right⟩
  map_one' := by apply FactorExtension.ext; exact f.map_one; rfl
  map_mul' a b := by
    apply FactorExtension.ext
    · change f (a.left * S.action a.right b.left * S.factor a.right b.right) = _
      simp only [map_mul, ha, hc]
      rfl
    · rfl

theorem map_injective (hf : Function.Injective f) :
    Function.Injective (map S T f ha hc) := by
  intro a b h
  apply FactorExtension.ext
  · exact hf (congrArg FactorExtension.left h)
  · exact congrArg (fun x : FactorExtension T => x.right) h


/-- The defining group extension of a factor system. -/
def groupExtension : GroupExtension N (FactorExtension S) Q where
  inl := inl S
  rightHom := projection S
  inl_injective := inl_injective S
  range_inl_eq_ker_rightHom := by
    ext a
    constructor
    · rintro ⟨n, rfl⟩
      rfl
    · intro ha
      change a.right = 1 at ha
      refine ⟨a.left, ?_⟩
      apply FactorExtension.ext
      · rfl
      · exact ha.symm
  rightHom_surjective := projection_surjective S

end PolycyclicRecognition.FactorExtension

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FactorExtensionConjugation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conjugation on the completed kernel in factor coordinates -/

namespace PolycyclicRecognition.FactorExtension
variable {N Q : Type*} [Group N] [Group Q] (S : NonabelianFactorSystem N Q)

theorem conjugation_inl (a : FactorExtension S) (n : N) :
    (groupExtension S).conjAct a n = a.left * S.action a.right n * a.left⁻¹ := by
  apply (groupExtension S).inl_injective
  rw [(groupExtension S).inl_conjAct_comm]
  apply mul_inv_eq_iff_eq_mul.mpr
  change a * inl S n = inl S (a.left * S.action a.right n * a.left⁻¹) * a
  apply FactorExtension.ext
  · change a.left * S.action a.right n * S.factor a.right 1 =
      (a.left * S.action a.right n * a.left⁻¹) * S.action 1 a.left * S.factor 1 a.right
    rw [S.factor_one_right, S.action_one, MulAut.one_apply, S.factor_one_left]
    group
  · exact (mul_one a.right).trans (one_mul a.right).symm

theorem conjugation_eq (a : FactorExtension S) :
    (groupExtension S).conjAct a = MulAut.conj a.left * S.action a.right := by
  apply DFunLike.ext
  exact conjugation_inl S a

/-- The coordinate section has exactly the prescribed kernel action. -/
theorem conjugation_section (q : Q) :
    (groupExtension S).conjAct (⟨1, q⟩ : FactorExtension S) = S.action q := by
  rw [conjugation_eq]
  change MulAut.conj 1 * S.action q = S.action q
  rw [map_one, one_mul]

end PolycyclicRecognition.FactorExtension

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FactorExtensionTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Completing the kernel while retaining the discrete quotient -/

noncomputable section
namespace PolycyclicRecognition
open Filter Topology

variable {N Q : Type*} [Group N] [Group Q] [TopologicalSpace N] [TopologicalSpace Q]
  (S : NonabelianFactorSystem N Q)

@[instance_reducible] def factorExtensionTopology : TopologicalSpace (FactorExtension S) :=
  TopologicalSpace.induced (FactorExtension.equivProd S) inferInstance

attribute [local instance] factorExtensionTopology

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FactorSystemGauge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Changing quotient lifts by an explicit kernel element

This permits inner corrections in the completed kernel without changing the
extension. The correction need not belong to the original lattice.
-/

namespace PolycyclicRecognition.NonabelianFactorSystem
variable {N Q : Type*} [Group N] [Group Q]
  (S : NonabelianFactorSystem N Q) (b : Q → N) (hb : b 1 = 1)

def gauge : NonabelianFactorSystem N Q where
  action q := MulAut.conj (b q) * S.action q
  factor q r := b q * S.action q (b r) * S.factor q r * (b (q * r))⁻¹
  action_one := by simp only [hb, S.action_one, map_one, mul_one]
  factor_one_left q := by
    simp only [hb, S.action_one, MulAut.one_apply, S.factor_one_left,
      one_mul, mul_one, mul_inv_cancel]
  factor_one_right q := by
    simp only [hb, map_one, S.factor_one_right, mul_one, mul_inv_cancel]
  action_mul q r := by
    apply DFunLike.ext
    intro x
    change b q * S.action q (b r * S.action r x * (b r)⁻¹) * (b q)⁻¹ =
      (b q * S.action q (b r) * S.factor q r * (b (q * r))⁻¹) *
        (b (q * r) * S.action (q * r) x * (b (q * r))⁻¹) *
          (b q * S.action q (b r) * S.factor q r * (b (q * r))⁻¹)⁻¹
    simp only [map_mul, map_inv, S.action_mul_apply]
    group
  cocycle q r s := by
    change (b q * S.action q (b r) * S.factor q r * (b (q * r))⁻¹) *
        (b (q * r) * S.action (q * r) (b s) * S.factor (q * r) s * (b ((q * r) * s))⁻¹) =
      (b q * S.action q (b r * S.action r (b s) * S.factor r s * (b (r * s))⁻¹) * (b q)⁻¹) *
        (b q * S.action q (b (r * s)) * S.factor q (r * s) * (b (q * (r * s)))⁻¹)
    simp only [map_mul, map_inv, S.action_mul_apply]
    have hc : S.action q (S.factor r s) =
        S.factor q r * S.factor (q * r) s * (S.factor q (r * s))⁻¹ :=
      eq_mul_inv_iff_mul_eq.mpr (S.cocycle q r s).symm
    rw [hc, mul_assoc q r s]
    group

end PolycyclicRecognition.NonabelianFactorSystem

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_MetricCoarseBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Metric quasi-isometries and the discrete group coarse structure

The finiteness and duality endgame uses finite sets of group differences.
Here an actual metric quasi-isometry supplies that data. The metrics are
left invariant and their bounded identity balls are finite, as for word
metrics on finitely generated groups. No recognition theorem is assumed.
-/

noncomputable section

namespace PolycyclicRecognition

open Metric

variable {G H : Type*} [Group G] [Group H]
  [MetricSpace G] [MetricSpace H]
  [IsIsometricSMul G G] [IsIsometricSMul H H]

/-- Left invariance measures a group difference by the distance between its
two endpoints. -/
theorem dist_one_groupDifference (x y : G) : dist 1 (x⁻¹ * y) = dist x y := by
  simpa using (dist_mul_left x⁻¹ x y)

/-- An upper coarse Lipschitz inequality sends each finite set of group
differences into a finite identity ball. -/
theorem groupBornologous_of_metric_bound (f : G → H)
    (hfinite : ∀ R : ℝ, (closedBall (1 : H) R).Finite)
    {K C : ℝ} (hK : 0 ≤ K)
    (hupper : ∀ x y, dist (f x) (f y) ≤ K * dist x y + C) :
    GroupBornologous f := by
  intro S hS
  obtain ⟨R, hR⟩ := (isBounded_iff_subset_closedBall (1 : G)).mp hS.isBounded
  refine ⟨closedBall (1 : H) (K * R + C), hfinite _, ?_⟩
  intro x y hxy
  have hdist : dist x y ≤ R := by
    have h := hR hxy
    simpa only [mem_closedBall, dist_comm (x⁻¹ * y), dist_one_groupDifference] using h
  change dist ((f x)⁻¹ * f y) 1 ≤ _
  rw [dist_comm, dist_one_groupDifference]
  exact (hupper x y).trans (add_le_add (mul_le_mul_of_nonneg_left hdist hK) le_rfl)

/-- Uniformly bounded metric displacement is a finite set of group errors. -/
theorem finite_groupDifference_range_of_metric_bound (r : G → G)
    (hfinite : ∀ R : ℝ, (closedBall (1 : G) R).Finite)
    {E : ℝ} (herror : ∀ x, dist x (r x) ≤ E) :
    (Set.range fun x => x⁻¹ * r x).Finite := by
  apply (hfinite E).subset
  rintro _ ⟨x, rfl⟩
  simpa only [mem_closedBall, dist_comm (x⁻¹ * r x), dist_one_groupDifference]
    using herror x

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_SemidirectProductTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The product topology on the Cartan semidirect cover -/

noncomputable section
namespace PolycyclicRecognition

variable {N D : Type*} [Group N] [Group D] [TopologicalSpace N] [TopologicalSpace D]
  (φ : D →* MulAut N)

@[instance_reducible]
def semidirectProductTopology : TopologicalSpace (N ⋊[φ] D) :=
  TopologicalSpace.induced SemidirectProduct.equivProd inferInstance

attribute [local instance] semidirectProductTopology

def semidirectProductHomeomorph : (N ⋊[φ] D) ≃ₜ N × D where
  toEquiv := SemidirectProduct.equivProd
  continuous_toFun := continuous_induced_dom
  continuous_invFun := continuous_induced_rng.2 continuous_id

theorem continuous_semidirect_left : Continuous (fun p : N ⋊[φ] D => p.left) :=
  (semidirectProductHomeomorph φ).continuous.fst

theorem continuous_semidirect_right : Continuous (fun p : N ⋊[φ] D => p.right) :=
  (semidirectProductHomeomorph φ).continuous.snd

theorem continuous_semidirect_inr :
    Continuous (SemidirectProduct.inr : D → N ⋊[φ] D) :=
  (semidirectProductHomeomorph φ).symm.continuous.comp
    (continuous_const.prodMk continuous_id)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_FiniteResolutionTruncation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A finite resolution from finite dimension and finite generation

Canonical truncation replaces the last term by its quotient syzygy. The
projectivity of that syzygy follows from finite projective dimension, while
finite generation passes to the quotient.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits

def finiteResolutionShape (d : ℕ) : ComplexShape (Fin (d + 1)) where
  Rel i j := j.val + 1 = i.val
  next_eq := by intros; apply Fin.ext; omega
  prev_eq := by intros; apply Fin.ext; omega

def finiteResolutionEmbedding (d : ℕ) :
    (finiteResolutionShape d).Embedding (ComplexShape.down ℕ) :=
  ComplexShape.Embedding.mk' _ _ Fin.val Fin.val_injective (fun _ _ => Iff.rfl)

instance instIsTruncGEFinHAddNatOfNatFiniteResolutionEmbedding (d : ℕ) : (finiteResolutionEmbedding d).IsTruncGE where
  rel' _ _ h := h
  mem_next {j k} h := by
    change k + 1 = j.val at h
    exact ⟨⟨k, by omega⟩, rfl⟩

theorem finiteResolutionEmbedding_boundary (d : ℕ) (i : Fin (d + 1)) :
    (finiteResolutionEmbedding d).BoundaryGE i ↔ i.val = d := by
  constructor
  · intro h
    by_contra hi
    have hi' : i.val + 1 < d + 1 := by omega
    exact h.2 ⟨i.val + 1, hi'⟩ rfl
  · intro hi
    apply (finiteResolutionEmbedding d).boundaryGE (i' := d + 1)
    · change i.val + 1 = d + 1
      omega
    · intro j hj
      change j.val = d + 1 at hj
      omega

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_DualityEndgame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The conditional finiteness and duality endgame

Elementary amenability is an explicit premise. Finiteness transfer, elementary
amenable finiteness, duality transfer, and solvable duality are retained as
separate parameters with the following mathematical sources.

* Xin Li, *Dynamic characterizations of quasi-isometry and applications to
  cohomology*, AGT 18 (2018), Corollaries 4.47 and 4.48.
* Kropholler–Martínez-Pérez–Nucinkis, *Cohomological finiteness conditions for
  elementary amenable groups*, J. reine angew. Math. 637 (2009), Theorem 1.1
  (viii) ⇒ (v) and the structural conclusion in §2. We use only their consequence
  that an elementary amenable group of type FP∞ has a finite-index solvable
  subgroup of finite integral cohomological dimension: intersect the solvable
  subgroup with the type-F subgroup.
* R. Bieri, *Homological dimension of discrete groups*, 2nd ed. (1981),
  Theorem 9.23: solvable integral Poincaré duality groups are polycyclic.

The propositions concern group-ring resolutions, group cohomology, and
finite-index subgroups.
-/

namespace PolycyclicRecognition

/-- Li, Corollary 4.47, specialized to integral coefficients and finitely
generated groups. The choice of left coarse structure is changed to Li's right
coarse structure by inversion. -/
def LiFinitenessInput : Prop :=
  ∀ (Γ H : Type) [Group Γ] [Group H] [Group.FG Γ] [Group.FG H],
    GroupCoarseEquivalence Γ H → ∀ n, TypeFP Γ n → TypeFP H n

/-- Li, Corollary 4.48, integral Poincaré duality transfer with both finite
cohomological dimension hypotheses retained. -/
def LiDualityInput : Prop :=
  ∀ (Γ H : Type) [Group Γ] [Group H] [Group.FG Γ] [Group.FG H],
    GroupCoarseEquivalence Γ H →
    HasFiniteIntegralCohomologicalDimension Γ →
    HasFiniteIntegralCohomologicalDimension H →
    ∀ n, IsIntegralPoincareDualityGroup Γ n → IsIntegralPoincareDualityGroup H n

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_PolycyclicDualityComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The algebraic Poincaré-duality comparison group

Only two standard published consequences are needed here:

* D. J. S. Robinson, *A Course in the Theory of Groups*, second edition,
  GTM 80, Springer (1996), Theorem 5.4.15(i), p.153: every polycyclic
  group has a finite-index poly-infinite-cyclic subgroup. We use only its
  torsion-free consequence, not normality or a chosen infinite-cyclic series.
* R. Bieri, *Homological Dimension of Discrete Groups*, second edition
  (1981), Theorems 9.9 and 9.10, and their explicit consequence on p.176:
  every torsion-free polycyclic group is an integral Poincaré-duality group.

These are explicit conditional inputs. The resulting recognition theorem
retains elementary amenability as a hypothesis.
-/

namespace PolycyclicRecognition

/-- Group-theoretic torsion freeness. This only excludes nonidentity finite-order
elements; it does not impose the unique-root property on a noncommutative group. -/
def HasNoNontrivialTorsion (P : Type) [Group P] : Prop :=
  ∀ (g : P) (n : ℕ), n ≠ 0 → g ^ n = 1 → g = 1

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RepCofiber
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coordinates on the mapping cone used for cyclic extensions -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance 2000] Rep.hV2

variable {k G : Type} [CommRing k] [Group G]

theorem rep_shortComplex_exact_iff (S : ShortComplex (Rep k G)) :
    S.Exact ↔ ∀ x : S.X₂, S.g.hom x = 0 → ∃ y : S.X₁, S.f.hom y = x := by
  constructor
  · intro h
    exact (ShortComplex.moduleCat_exact_iff _).mp
      (h.map (forget₂ (Rep k G) (ModuleCat k)))
  · intro h
    apply (forget₂ (Rep k G) (ModuleCat k)).reflects_exact_of_faithful
    exact (ShortComplex.moduleCat_exact_iff _).mpr h

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_FreeAbelianDuality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Free abelian rank bounds from integral cohomological dimension

The coordinate homomorphism splits off one infinite cyclic quotient at a time.
The resulting duality calculation bounds the rank of every embedded integral
lattice in a group of finite integral cohomological dimension.
-/

noncomputable section
namespace PolycyclicRecognition

abbrev IntegralLatticeGroup (n : ℕ) := Multiplicative (Fin n → ℤ)

def latticeCoordinate (n : ℕ) : IntegralLatticeGroup (n + 1) →* Multiplicative ℤ where
  toFun a := Multiplicative.ofAdd (a.toAdd 0)
  map_one' := rfl
  map_mul' _ _ := rfl

def latticeCoordinateSection (n : ℕ) : IntegralLatticeGroup (n + 1) :=
  Multiplicative.ofAdd (Fin.cases 1 (fun _ => 0))

@[simp] theorem latticeCoordinate_section (n : ℕ) :
    latticeCoordinate n (latticeCoordinateSection n) = Multiplicative.ofAdd 1 := rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_SolvableLatticeModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Solvable-lattice realization

K. Dekimpe, *Solvable Lie Algebras, Lie Groups and Polynomial Structures*,
Compositio Mathematica 121 (2000), 183–204, Theorem 4.1, p.199,
DOI 10.1023/A:1001738932743, gives a finite-index subgroup of a
polycyclic-by-finite group as a uniform lattice in a connected simply
connected solvable Lie group. We use only this consequence, omitting the
additional equality with the Fitting subgroup and omitting normality.

The realization predicate specifies a finite-dimensional smooth Lie structure
and a discrete lattice with compact coset quotient.
-/

noncomputable section

namespace PolycyclicRecognition

open scoped Manifold

attribute [instance] SimplyConnectedSolvableLieModel.normedAddCommGroup
  SimplyConnectedSolvableLieModel.normedSpace SimplyConnectedSolvableLieModel.finiteDimensional
  SimplyConnectedSolvableLieModel.topologicalSpace SimplyConnectedSolvableLieModel.chartedSpace
  SimplyConnectedSolvableLieModel.group SimplyConnectedSolvableLieModel.lieGroup
  SimplyConnectedSolvableLieModel.t2Space SimplyConnectedSolvableLieModel.simplyConnectedSpace
  SimplyConnectedSolvableLieModel.secondCountableTopology
  SimplyConnectedSolvableLieModel.solvable

/-- The exact lattice-realization consequence of Dekimpe's Theorem 4.1
needed for the paper's lattice formulation. -/
def DekimpeLatticeRealizationInput : Prop :=
  ∀ (P : Type) [Group P], IsVirtuallyPolycyclic P →
    ∃ Γ : Subgroup P, Γ.FiniteIndex ∧
      ∃ (S : SimplyConnectedSolvableLieModel) (Λ : Subgroup S.carrier),
        DiscreteTopology Λ ∧ CompactSpace (S.carrier ⧸ Λ) ∧ Nonempty (Γ ≃* Λ)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_VectorLatticeModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The integral vector lattice as a solvable Lie lattice

This constructs the abelian case of the lattice-realization input. The compact
fundamental cover is the closed unit parallelepiped of the standard real basis.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold

def vectorSolvableLieModel (n : ℕ) : SimplyConnectedSolvableLieModel := by
  let V := Fin n → ℝ
  let : ChartedSpace V (Multiplicative V) := inferInstanceAs (ChartedSpace V V)
  let : LieGroup (𝓘(ℝ, V)) ⊤ (Multiplicative V) :=
    { toIsManifold := by change IsManifold (𝓘(ℝ, V)) ⊤ V; infer_instance
      contMDiff_mul := by
        change ContMDiff ((𝓘(ℝ, V)).prod (𝓘(ℝ, V))) (𝓘(ℝ, V)) ⊤
          (fun p : V × V => p.1 + p.2)
        exact contMDiff_add (I := 𝓘(ℝ, V)) (n := ⊤)
      contMDiff_inv := by
        change ContMDiff (𝓘(ℝ, V)) (𝓘(ℝ, V)) ⊤ (fun v : V => -v)
        exact contDiff_neg.contMDiff }
  let : SimplyConnectedSpace (Multiplicative V) := inferInstanceAs (SimplyConnectedSpace V)
  exact { modelSpace := V, carrier := Multiplicative V }

def standardVectorLattice (n : ℕ) : Subgroup (vectorSolvableLieModel n).carrier :=
  (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin n)))).toAddSubgroup.toSubgroup

theorem standardVectorLattice_uniform (n : ℕ) : IsUniformLattice (standardVectorLattice n) := by
  let b := Pi.basisFun ℝ (Fin n)
  let L := Submodule.span ℤ (Set.range b)
  change IsUniformLattice (G := Multiplicative (Fin n → ℝ)) L.toAddSubgroup.toSubgroup
  have hdisc : DiscreteTopology (standardVectorLattice n) :=
    inferInstanceAs (DiscreteTopology L)
  let K : Set (Fin n → ℝ) := parallelepiped b
  have hK : IsCompact K := b.parallelepiped.isCompact
  refine ⟨hdisc, K, hK, ?_⟩
  intro g
  let z := ZSpan.floor b g.toAdd
  refine ⟨⟨Multiplicative.ofAdd (z : Fin n → ℝ), z.property⟩,
    Multiplicative.ofAdd (ZSpan.fract b g.toAdd), ?_, ?_⟩
  · exact ZSpan.fundamentalDomain_subset_parallelepiped b
      (ZSpan.fract_mem_fundamentalDomain b g.toAdd)
  · change (z : Fin n → ℝ) + ZSpan.fract b g.toAdd = g.toAdd
    dsimp only [z, ZSpan.fract]
    abel

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_IntegralBilinearExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Extending an integral two-step law to a real Lie group -/

noncomputable section
namespace PolycyclicRecognition

variable {d e : ℕ}

def integerVectorMap (n : ℕ) : (Fin n → ℤ) →+ (Fin n → ℝ) where
  toFun x i := (x i : ℝ)
  map_zero' := by ext i; exact Int.cast_zero
  map_add' x y := by ext i; exact Int.cast_add _ _

theorem integerVectorMap_injective (n : ℕ) : Function.Injective (integerVectorMap n) := by
  intro x y h
  ext i
  have hi : (x i : ℝ) = (y i : ℝ) := congrFun h i
  exact_mod_cast hi

theorem integerVectorMap_mem (n : ℕ) (x : Fin n → ℤ) :
    integerVectorMap n x ∈ Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin n))) := by
  apply ((Pi.basisFun ℝ (Fin n)).mem_span_iff_repr_mem ℤ _).mpr
  intro i
  exact ⟨x i, rfl⟩

theorem exists_integerVectorMap_of_mem (n : ℕ) (x : Fin n → ℝ)
    (hx : x ∈ Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin n)))) :
    ∃ z, integerVectorMap n z = x := by
  have h := ((Pi.basisFun ℝ (Fin n)).mem_span_iff_repr_mem ℤ x).mp hx
  choose z hz using h
  exact ⟨z, funext hz⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_IntegralLatticeGenerators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coordinate generators and the standard embedding of the integral lattice -/

noncomputable section
namespace PolycyclicRecognition

def integralLatticeGenerator (n : ℕ) (i : Fin n) : IntegralLatticeGroup n :=
  Multiplicative.ofAdd ((Pi.basisFun ℤ (Fin n)) i)

def integerVectorHom (n : ℕ) : IntegralLatticeGroup n →* Multiplicative (Fin n → ℝ) where
  toFun z := Multiplicative.ofAdd (integerVectorMap n z.toAdd)
  map_one' := by apply Multiplicative.ext; exact (integerVectorMap n).map_zero
  map_mul' z w := by apply Multiplicative.ext; exact (integerVectorMap n).map_add z.toAdd w.toAdd

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_IntegralLatticePowerIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite-index powers in an integral vector lattice -/

noncomputable section
namespace PolycyclicRecognition

def latticePowerHom (n m : ℕ) : IntegralLatticeGroup n →* IntegralLatticeGroup n where
  toFun z := z ^ m
  map_one' := one_pow m
  map_mul' z w := (Commute.all z w).mul_pow m

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FactorSystemPullback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Restriction of a factor system to a quotient homomorphism -/

noncomputable section
namespace PolycyclicRecognition
variable {N Q H : Type} [Group N] [Group Q] [Group H]
  (R : NonabelianFactorSystem N Q) (f : H →* Q)

def NonabelianFactorSystem.pullback : NonabelianFactorSystem N H where
  action h := R.action (f h)
  factor h k := R.factor (f h) (f k)
  action_one := by rw [map_one, R.action_one]
  factor_one_left h := by rw [map_one, R.factor_one_left]
  factor_one_right h := by rw [map_one, R.factor_one_right]
  action_mul h k := by rw [map_mul]; exact R.action_mul _ _
  cocycle h k l := by simp only [map_mul]; exact R.cocycle _ _ _

def factorPullbackMap : FactorExtension (R.pullback f) →* FactorExtension R where
  toFun x := ⟨x.left, f x.right⟩
  map_one' := by apply FactorExtension.ext; rfl; exact map_one f
  map_mul' x y := by apply FactorExtension.ext; rfl; exact map_mul f _ _

attribute [local instance] factorExtensionTopology

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FactorSystemTwist
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing a commuting quotient action from a factor system

The original cocycle is retained. Fixedness of its values is exactly the
condition needed to remove the commuting semisimple quotient action.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped IsMulCommutative
variable {N Q : Type} [Group N] [Group Q] [IsMulCommutative Q]
  (R : NonabelianFactorSystem N Q) (χ : Q →* MulAut N)
  (hcomm : ∀ q r, Commute (R.action q) (χ r))
  (hfix : ∀ q r s, χ q (R.factor r s) = R.factor r s)

include hfix in
omit [IsMulCommutative Q] in
theorem twist_inverse_fixed (q r s : Q) :
    (χ q)⁻¹ (R.factor r s) = R.factor r s := by
  apply (χ q).injective
  change χ q ((χ q).symm (R.factor r s)) = χ q (R.factor r s)
  rw [MulEquiv.apply_symm_apply, hfix]

theorem twist_inverse_product (q r : Q) (x : N) :
    (χ q)⁻¹ ((χ r)⁻¹ x) = (χ (q * r))⁻¹ x := by
  change ((χ q)⁻¹ * (χ r)⁻¹) x = (χ (q * r))⁻¹ x
  rw [mul_comm q r, map_mul, mul_inv_rev]

include hcomm in
omit [IsMulCommutative Q] in
theorem twist_inverse_commute (q r : Q) (x : N) :
    R.action q ((χ r)⁻¹ x) = (χ r)⁻¹ (R.action q x) :=
  DFunLike.congr_fun (hcomm q r).inv_right.eq x

include hcomm hfix in
/-- Remove the actual quotient homomorphism from every section action. -/
def NonabelianFactorSystem.twist : NonabelianFactorSystem N Q where
  action q := (χ q)⁻¹ * R.action q
  factor := R.factor
  action_one := by rw [map_one, inv_one, one_mul, R.action_one]
  factor_one_left := R.factor_one_left
  factor_one_right := R.factor_one_right
  action_mul q r := by
    apply DFunLike.ext
    intro x
    change (χ q)⁻¹ (R.action q ((χ r)⁻¹ (R.action r x))) =
      R.factor q r * (χ (q * r))⁻¹ (R.action (q * r) x) * (R.factor q r)⁻¹
    rw [twist_inverse_commute R χ hcomm, twist_inverse_product,
      R.action_mul_apply, map_mul, map_mul, map_inv,
      twist_inverse_fixed R χ hfix]
  cocycle q r s := by
    change R.factor q r * R.factor (q * r) s =
      (χ q)⁻¹ (R.action q (R.factor r s)) * R.factor q (r * s)
    rw [← twist_inverse_commute R χ hcomm,
      twist_inverse_fixed R χ hfix, R.cocycle]

theorem factorSystem_twist_recompose (q : Q) (x : N) :
    (R.twist χ hcomm hfix).action q (χ q x) = R.action q x := by
  change (χ q)⁻¹ (R.action q (χ q x)) = R.action q x
  have hc : R.action q (χ q x) = χ q (R.action q x) :=
    DFunLike.congr_fun (hcomm q q).eq x
  rw [hc]
  exact (χ q).symm_apply_apply _

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FactorSystemTwistAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The removed action and the original extension

The removed quotient action acts on the twisted extension. The original
extension embeds into its semidirect product as the graph of the quotient.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped IsMulCommutative
variable {N Q : Type} [Group N] [Group Q] [IsMulCommutative Q]
  (R : NonabelianFactorSystem N Q) (χ : Q →* MulAut N)
  (hcomm : ∀ q r, Commute (R.action q) (χ r))
  (hfix : ∀ q r s, χ q (R.factor r s) = R.factor r s)

theorem twist_action_commutes (q r : Q) (x : N) :
    χ q ((R.twist χ hcomm hfix).action r x) =
      (R.twist χ hcomm hfix).action r (χ q x) := by
  have hc₀ : Commute (χ q) (χ r) := by
    change χ q * χ r = χ r * χ q
    rw [← map_mul, ← map_mul, mul_comm q r]
  have hc : Commute (χ q) ((χ r)⁻¹) := hc₀.inv_right
  have ha : χ q (R.action r x) = R.action r (χ q x) :=
    DFunLike.congr_fun (hcomm r q).symm.eq x
  change χ q ((χ r)⁻¹ (R.action r x)) = (χ r)⁻¹ (R.action r (χ q x))
  have hi : χ q ((χ r)⁻¹ (R.action r x)) = (χ r)⁻¹ (χ q (R.action r x)) :=
    DFunLike.congr_fun hc.eq _
  rw [hi, ha]

def factorTwistAction : Q →* MulAut (FactorExtension (R.twist χ hcomm hfix)) where
  toFun q :=
    { toFun a := ⟨χ q a.left, a.right⟩
      invFun a := ⟨χ q⁻¹ a.left, a.right⟩
      left_inv a := by
        apply FactorExtension.ext
        · change (χ q⁻¹ * χ q) a.left = a.left
          rw [← map_mul, inv_mul_cancel, map_one]
          rfl
        · rfl
      right_inv a := by
        apply FactorExtension.ext
        · change (χ q * χ q⁻¹) a.left = a.left
          rw [← map_mul, mul_inv_cancel, map_one]
          rfl
        · rfl
      map_mul' a b := by
        apply FactorExtension.ext
        · change χ q (a.left * (R.twist χ hcomm hfix).action a.right b.left *
              R.factor a.right b.right) = _
          rw [map_mul, map_mul, twist_action_commutes, hfix]
          rfl
        · rfl }
  map_one' := by
    apply DFunLike.ext
    intro a
    apply FactorExtension.ext
    · exact DFunLike.congr_fun (map_one χ) a.left
    · rfl
  map_mul' q r := by
    apply DFunLike.ext
    intro a
    apply FactorExtension.ext
    · exact DFunLike.congr_fun (map_mul χ q r) a.left
    · rfl

/-- The graph embedding retains both coordinates of the original group. -/
def factorTwistGraph : FactorExtension R →*
    (FactorExtension (R.twist χ hcomm hfix) ⋊[factorTwistAction R χ hcomm hfix] Q) where
  toFun a := ⟨⟨a.left, a.right⟩, a.right⟩
  map_one' := rfl
  map_mul' a b := by
    apply SemidirectProduct.ext
    · apply FactorExtension.ext
      · change a.left * R.action a.right b.left * R.factor a.right b.right =
          a.left * (R.twist χ hcomm hfix).action a.right (χ a.right b.left) *
            R.factor a.right b.right
        rw [factorSystem_twist_recompose]
      · rfl
    · rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_WordCutCounting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binomial counting of the internal cuts of a word -/

namespace PolycyclicRecognition

open scoped BigOperators

theorem sum_range_prefix_choose (d k : ℕ) :
    (∑ i ∈ Finset.range d, i.choose k) = d.choose (k + 1) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Finset.sum_range_succ, ih, Nat.choose_succ_succ]
    exact Nat.add_comm _ _

theorem sum_internal_word_cuts (d k : ℕ) (hd : 0 < d) :
    (∑ i : Fin (d + 1), if 0 < i.val ∧ i.val < d then (i.val - 1).choose k else 0) =
      (d - 1).choose (k + 1) := by
  cases d with
  | zero => omega
  | succ d =>
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, lt_self_iff_false, false_and, ite_false, if_false, zero_add,
      Fin.val_succ, Nat.add_sub_cancel]
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, Nat.zero_lt_succ,
      Nat.add_lt_add_iff_right, true_and, lt_self_iff_false, ite_false, if_false, add_zero]
    simpa only [Fin.isLt, ite_true, if_true, ← Fin.sum_univ_eq_sum_range] using sum_range_prefix_choose d k

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_WordLieProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The right-nested commutator projection of rational words -/

noncomputable section
namespace PolycyclicRecognition

abbrev RationalWords (n : ℕ) := MonoidAlgebra ℚ (FreeMonoid (Fin n))

variable {A : Type*} [Ring A] [Algebra ℚ A] {n : ℕ} (X : Fin n → A)

def wordRightLie : List (Fin n) → A
  | [] => 0
  | [i] => X i
  | i :: j :: l => X i * wordRightLie (j :: l) - wordRightLie (j :: l) * X i

def wordLieProjection : RationalWords n →ₗ[ℚ] A :=
  (Finsupp.linearCombination ℚ (fun w : FreeMonoid (Fin n) => wordRightLie X w.toList)).comp
    (MonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap

theorem wordLieProjection_single (w : FreeMonoid (Fin n)) (q : ℚ) :
    wordLieProjection X (MonoidAlgebra.single w q) = q • wordRightLie X w.toList := by
  change Finsupp.linearCombination ℚ _ (Finsupp.single w q) = _
  exact Finsupp.linearCombination_single (R := ℚ)
    (v := fun w : FreeMonoid (Fin n) => wordRightLie X w.toList) q w

def rationalWordLetter (i : Fin n) : RationalWords n :=
  MonoidAlgebra.single (FreeMonoid.of i) 1

theorem wordLieProjection_letter_mul (i : Fin n) (p : RationalWords n) :
    wordLieProjection X (rationalWordLetter i * p) =
      X i * wordLieProjection X p - wordLieProjection X p * X i + p.coeff 1 • X i := by
  induction p using MonoidAlgebra.induction_on with
  | of w =>
    change wordLieProjection X (rationalWordLetter i * MonoidAlgebra.single w 1) =
      X i * wordLieProjection X (MonoidAlgebra.single w 1) -
        wordLieProjection X (MonoidAlgebra.single w 1) * X i +
        (MonoidAlgebra.single w (1 : ℚ)).coeff 1 • X i
    rw [rationalWordLetter, MonoidAlgebra.single_mul_single, one_mul,
      wordLieProjection_single, wordLieProjection_single, one_smul, one_smul]
    cases hw : w.toList with
    | nil =>
      have hw1 : w = 1 := FreeMonoid.toList.injective hw
      subst w
      simp [wordRightLie, MonoidAlgebra.coeff_single]
    | cons j l =>
      have hw1 : w ≠ 1 := by
        intro h
        simp [h] at hw
      simp [wordRightLie, hw, MonoidAlgebra.coeff_single, hw1]
  | add p q hp hq =>
    simp only [mul_add, map_add, hp, hq, add_mul, MonoidAlgebra.coeff_add,
      Finsupp.add_apply, add_smul]
    abel
  | smul r p hp =>
    simp only [mul_smul_comm, map_smul, hp, smul_mul_assoc, MonoidAlgebra.coeff_smul,
      Finsupp.smul_apply, smul_sub, smul_add, smul_smul, Algebra.mul_smul_comm, smul_eq_mul]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RationalWordEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Evaluation and the empty-word coefficient of rational words -/

noncomputable section
namespace PolycyclicRecognition

variable {A : Type*} [Ring A] [Algebra ℚ A] {n : ℕ}

def rationalWordEvaluation (X : Fin n → A) : RationalWords n →ₐ[ℚ] A :=
  MonoidAlgebra.lift ℚ A (FreeMonoid (Fin n)) (FreeMonoid.lift X)

theorem rationalWordEvaluation_single (X : Fin n → A)
    (w : FreeMonoid (Fin n)) (q : ℚ) :
    rationalWordEvaluation X (MonoidAlgebra.single w q) = q • (w.toList.map X).prod := by
  rw [rationalWordEvaluation, MonoidAlgebra.lift_single, FreeMonoid.lift_apply]

def rationalWordAugmentation : RationalWords n →ₐ[ℚ] ℚ :=
  rationalWordEvaluation (fun _ => 0)

theorem rationalWordAugmentation_eq_coeff (p : RationalWords n) :
    rationalWordAugmentation p = p.coeff 1 := by
  induction p using MonoidAlgebra.induction_on with
  | of w =>
    change rationalWordEvaluation (fun _ => (0 : ℚ)) (MonoidAlgebra.single w 1) =
      (MonoidAlgebra.single w (1 : ℚ)).coeff 1
    rw [rationalWordEvaluation_single]
    cases hw : w.toList with
    | nil =>
      have hw1 : w = 1 := FreeMonoid.toList.injective hw
      subst w
      simp [MonoidAlgebra.coeff_single]
    | cons i l =>
      have hw1 : w ≠ 1 := by intro h; simp [h] at hw
      simp [MonoidAlgebra.coeff_single, hw1]
  | add p q hp hq =>
    simp only [map_add, hp, hq, MonoidAlgebra.coeff_add, Finsupp.add_apply]
  | smul r p hp =>
    simp only [map_smul, hp, MonoidAlgebra.coeff_smul, Finsupp.smul_apply]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_WordSplits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite prefix/suffix convolution for word coefficients -/

noncomputable section
namespace PolycyclicRecognition

open scoped BigOperators

variable {n : ℕ}

def wordSplit (w : FreeMonoid (Fin n)) (i : Fin (w.length + 1)) :
    FreeMonoid (Fin n) × FreeMonoid (Fin n) :=
  (FreeMonoid.ofList (w.toList.take i.val), FreeMonoid.ofList (w.toList.drop i.val))

theorem wordSplit_mul (w : FreeMonoid (Fin n)) (i : Fin (w.length + 1)) :
    (wordSplit w i).1 * (wordSplit w i).2 = w := by
  apply FreeMonoid.toList.injective
  simp [wordSplit]

theorem wordSplit_left_length (w : FreeMonoid (Fin n)) (i : Fin (w.length + 1)) :
    (wordSplit w i).1.length = i.val := by
  have hi : i.val ≤ w.toList.length := Nat.le_of_lt_succ i.isLt
  simp [wordSplit, FreeMonoid.length, Nat.min_eq_left hi]

theorem wordSplit_injective (w : FreeMonoid (Fin n)) : Function.Injective (wordSplit w) := by
  intro i j h
  apply Fin.ext
  simpa only [wordSplit_left_length] using congrArg (fun p => p.1.length) h

theorem exists_wordSplit (w u v : FreeMonoid (Fin n)) (h : u * v = w) :
    ∃ i : Fin (w.length + 1), wordSplit w i = (u, v) := by
  subst w
  have hu : u.length < (u * v).length + 1 := by rw [FreeMonoid.length_mul]; omega
  refine ⟨⟨u.length, hu⟩, ?_⟩
  apply Prod.ext <;> apply FreeMonoid.toList.injective
  · simp [wordSplit, FreeMonoid.length]
  · simp [wordSplit, FreeMonoid.length]

theorem word_coeff_mul (p q : RationalWords n) (w : FreeMonoid (Fin n)) :
    (p * q).coeff w = ∑ i : Fin (w.length + 1),
      p.coeff (wordSplit w i).1 * q.coeff (wordSplit w i).2 := by
  classical
  let s := Finset.univ.image (wordSplit w)
  have hs {z : FreeMonoid (Fin n) × FreeMonoid (Fin n)} : z ∈ s ↔ z.1 * z.2 = w := by
    constructor
    · intro hz
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
      exact wordSplit_mul w i
    · intro hz
      obtain ⟨i, hi⟩ := exists_wordSplit w z.1 z.2 hz
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩
  rw [MonoidAlgebra.coeff_mul_antidiag p q w s (fun {_} => hs)]
  exact Finset.sum_image (fun _ _ _ _ h => wordSplit_injective w h)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_WordMinimumDegree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Vanishing below the degree of an augmentation-ideal power -/

noncomputable section
namespace PolycyclicRecognition

variable {n : ℕ}

def WordMinimumDegree (p : RationalWords n) (k : ℕ) : Prop :=
  ∀ w, w.length < k → p.coeff w = 0

theorem WordMinimumDegree.mul {p q : RationalWords n} {k l : ℕ}
    (hp : WordMinimumDegree p k) (hq : WordMinimumDegree q l) :
    WordMinimumDegree (p * q) (k + l) := by
  intro w hw
  rw [word_coeff_mul]
  apply Finset.sum_eq_zero
  intro i _
  have hlen : (wordSplit w i).1.length + (wordSplit w i).2.length = w.length := by
    rw [← FreeMonoid.length_mul, wordSplit_mul]
  by_cases hi : (wordSplit w i).1.length < k
  · rw [hp _ hi, zero_mul]
  · have hj : (wordSplit w i).2.length < l := by omega
    rw [hq _ hj, mul_zero]

theorem wordMinimumDegree_one_of_emptyCoeff {p : RationalWords n} (hp : p.coeff 1 = 0) :
    WordMinimumDegree p 1 := by
  intro w hw
  have hz : w.length = 0 := by omega
  have he : w = 1 := FreeMonoid.length_eq_zero.mp hz
  simpa only [he] using hp

theorem wordMinimumDegree_pow {p : RationalWords n} (hp : p.coeff 1 = 0) (k : ℕ) :
    WordMinimumDegree (p ^ k) k := by
  induction k with
  | zero => intro w hw; omega
  | succ k ih =>
    rw [pow_succ]
    exact ih.mul (wordMinimumDegree_one_of_emptyCoeff hp)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FiniteLogCoefficientBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coefficient bounds for the finite logarithm of a word polynomial -/

noncomputable section
namespace PolycyclicRecognition

open scoped BigOperators

theorem finiteNilpotentLog_sum {A : Type*} [Ring A] [Algebra ℚ A] (p : A) (c : ℕ) :
    finiteNilpotentLog (c + 1) p =
      ∑ k : Fin c, ((-1 : ℚ) ^ (k.val + 2) / (k.val + 1)) • p ^ (k.val + 1) := by
  rw [finiteNilpotentLog, Polynomial.aeval_def, PowerSeries.eval₂_trunc_eq_sum_range,
    ← Fin.sum_univ_eq_sum_range, Fin.sum_univ_succ]
  simp only [Fin.val_zero, PowerSeries.coeff_log, ite_true, if_true, map_zero, zero_mul,
    Fin.val_succ, Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false, if_false,
    Algebra.algebraMap_self, RingHom.id_apply, zero_add, ← Algebra.smul_def,
    Nat.cast_add, Nat.cast_one, Nat.add_assoc, Nat.reduceAdd]

theorem sum_choose_initial_le (a c : ℕ) (ha : a ≤ c) :
    (∑ k ∈ Finset.range c, a.choose k) ≤ 2 ^ c := by
  calc
    _ ≤ ∑ k ∈ Finset.range c, c.choose k :=
      Finset.sum_le_sum (fun k _ => Nat.choose_le_choose k ha)
    _ ≤ ∑ k ∈ Finset.range (c + 1), c.choose k := by
      rw [Finset.sum_range_succ]
      exact Nat.le_add_right _ _
    _ = _ := Nat.sum_range_choose c

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_FiniteProjectivePresentations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite projective covers of finitely generated representations -/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
open scoped MonoidAlgebra
variable {G : Type} [Group G]

structure FiniteIntegralProjectivePresentation (A : Rep.{0} ℤ G)
    extends ProjectivePresentation A where
  finite : IntegralRepresentationFinite G p

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ControlledChainRepresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Equivariant control of finite chains

Left translation preserves every relative-position bound. Consequently an
equivariant image of a finitely generated representation lies at one finite
scale in the homogeneous standard chains.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
open scoped MonoidAlgebra
variable {R G : Type} [CommRing R] [Group G] {n : ℕ}

theorem IsControlledTuple.left_translate {S : Set G} {x : Fin (n + 1) → G}
    (hx : IsControlledTuple S x) (g : G) : IsControlledTuple S (g • x) := by
  intro i j
  simpa using hx i j

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolyZ
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cyclic series with torsion-free factors

Trivial factors are allowed. Removing them gives the usual poly-Z series.
The predicate records an actual series and is stable under subgroups.
-/

noncomputable section
namespace PolycyclicRecognition

open ChromaticCyclic

variable {G J : Type} [Group G] [Group J]

def TorsionFreeCyclicFactors {H K : Subgroup G} {n : ℕ} (c : CyclicSeries H K n) : Prop :=
  ∀ i (hi : i < n), letI := (c.step i hi).normal
    HasNoNontrivialTorsion (c.group (i + 1) ⧸ (c.group i).subgroupOf (c.group (i + 1)))

def IsPolyZ (G : Type) [Group G] : Prop :=
  ∃ n, ∃ c : CyclicSeries (⊥ : Subgroup G) ⊤ n, TorsionFreeCyclicFactors c

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FiniteRationalLinearModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The rational linear quotient of a finite-dimensional solvable group

The vector space is the product of the rational upper central layers of an
actual maximal nilpotent normal subgroup. Its action is faithful on the
quotient. No finite generation of the nilpotent subgroup is assumed.
-/

noncomputable section
namespace PolycyclicRecognition

structure FiniteRationalLinearModel (Q : Type) [Group Q] where
  space : Type
  [addCommGroup : AddCommGroup space]
  [module : Module ℚ space]
  [finite : Module.Finite ℚ space]
  action : Q →* (space ≃ₗ[ℚ] space)
  faithful : Function.Injective action

attribute [instance] FiniteRationalLinearModel.addCommGroup
  FiniteRationalLinearModel.module FiniteRationalLinearModel.finite

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_GroupExtensionFactorSystem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A group extension is its actual section factor system -/

noncomputable section
namespace PolycyclicRecognition
variable {N G Q : Type*} [Group N] [Group G] [Group Q]

namespace GroupExtensionSection
variable (S : GroupExtension N G Q) (σ : S.Section) (hσ : σ 1 = 1)

def factorSystem : NonabelianFactorSystem N Q where
  action q := S.conjAct (σ q)
  factor := factor S σ
  action_one := by rw [hσ, map_one]
  factor_one_left := factor_one_left S σ hσ
  factor_one_right := factor_one_right S σ hσ
  action_mul := section_action_mul S σ
  cocycle := factor_cocycle S σ

/-- The kernel coordinate of an element relative to the chosen section. -/
def coordinate (g : G) : N :=
  Function.invFun S.inl (g * (σ (S.rightHom g))⁻¹)

@[simp] theorem inl_coordinate (g : G) :
    S.inl (coordinate S σ g) = g * (σ (S.rightHom g))⁻¹ := by
  apply Function.invFun_eq
  rw [← MonoidHom.mem_range, S.range_inl_eq_ker_rightHom, MonoidHom.mem_ker]
  simp only [map_mul, map_inv, σ.rightHom_section, mul_inv_cancel]

theorem coordinate_inl_mul (n : N) (q : Q) :
    coordinate S σ (S.inl n * σ q) = n := by
  apply S.inl_injective
  simp only [inl_coordinate, map_mul, S.rightHom_inl, σ.rightHom_section, one_mul,
    mul_inv_cancel_right]

/-- The underlying normal-form coordinates are bijective. -/
def normalFormEquiv : G ≃ FactorExtension (factorSystem S σ hσ) where
  toFun g := ⟨coordinate S σ g, S.rightHom g⟩
  invFun a := S.inl a.left * σ a.right
  left_inv g := by
    change S.inl (coordinate S σ g) * σ (S.rightHom g) = g
    rw [inl_coordinate, inv_mul_cancel_right]
  right_inv a := by
    apply FactorExtension.ext
    · exact coordinate_inl_mul S σ a.left a.right
    · simp only [map_mul, S.rightHom_inl, σ.rightHom_section, one_mul]

/-- Decoding the normal form respects the nonabelian multiplication. -/
def decode : FactorExtension (factorSystem S σ hσ) →* G where
  toFun a := S.inl a.left * σ a.right
  map_one' := by change S.inl 1 * σ 1 = 1; rw [map_one, hσ, one_mul]
  map_mul' a b := by
    change S.inl (a.left * S.conjAct (σ a.right) b.left * factor S σ a.right b.right) *
      σ (a.right * b.right) = _
    simp only [map_mul, S.inl_conjAct_comm, inl_factor]
    group

/-- No splitting is assumed: the section factor supplies the full group law. -/
def mulEquiv : G ≃* FactorExtension (factorSystem S σ hσ) :=
  (MulEquiv.ofBijective (decode S σ hσ) (normalFormEquiv S σ hσ).symm.bijective).symm

end GroupExtensionSection
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_GaugeExtensionSection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Explicit kernel corrections of an actual extension section -/

noncomputable section
namespace PolycyclicRecognition.GroupExtensionSection
variable {N G Q : Type*} [Group N] [Group G] [Group Q]

def gaugeSection (E : GroupExtension N G Q) (σ : E.Section) (b : Q → N) : E.Section where
  toFun q := E.inl (b q) * σ q
  rightInverse_rightHom q := by rw [map_mul, E.rightHom_inl, σ.rightHom_section, one_mul]

end PolycyclicRecognition.GroupExtensionSection

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_Packing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Packing estimates and intrinsic word balls

This is the finite counting step in Lemma `height-kernel-growth` of
*Quasi-isometric recognition of virtually polycyclic groups*. A metric cover of
orbit points and a bound on the number of source points in a small target ball
give a cardinal bound on the original finite set. Applying this to intrinsic
word balls does not require the subgroup to be undistorted in an ambient group.
-/

namespace PolycyclicRecognition

universe u v

section WordBalls

variable {H : Type u} [Monoid H] [DecidableEq H]

/-- Products of at most `n` letters from `T`. Choosing `T` symmetric gives the
usual intrinsic word ball of radius `n` in the subgroup generated by `T`. -/
def wordBall (T : Finset H) : ℕ → Finset H
  | 0 => {1}
  | n + 1 => wordBall T n ∪ T.biUnion (fun t => (wordBall T n).image (t * ·))

@[simp]
theorem wordBall_zero (T : Finset H) : wordBall T 0 = {1} := rfl

end WordBalls

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_GromovInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The polynomial-growth input in height-kernel recognition

Published input: M. Gromov, *Groups of polynomial growth and expanding maps*,
Publications Mathématiques de l'IHÉS **53** (1981), 53–78, Main Theorem, p. 54,
DOI: `10.1007/BF02698687`.

`GromovPolynomialGrowthInput J` is precisely the implication needed here: a
finite symmetric generating set with polynomially bounded intrinsic word balls
gives a nilpotent subgroup of finite index. The supporting covering-to-cardinality
argument uses concrete finite word balls, with this implication as an explicit
hypothesis.
-/

namespace PolycyclicRecognition

universe u v

variable (J : Type u) [Group J]

/-- Virtual nilpotency means the existence of a nilpotent subgroup of finite index. -/
abbrev IsVirtuallyNilpotent : Prop := Group.IsVirtuallyNilpotent J

/-- Gromov's Main Theorem (1981, p. 54), specialized to the finite symmetric
word-ball formulation used by the height-kernel argument. -/
def GromovPolynomialGrowthInput [DecidableEq J] : Prop :=
  ∀ T : Finset J,
    (∀ t ∈ T, t⁻¹ ∈ T) →
    Subgroup.closure (T : Set J) = ⊤ →
    (∃ C b : ℕ, ∀ n, (wordBall T n).card ≤ C * (1 + n) ^ b) →
    IsVirtuallyNilpotent J

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RationalWordCoproduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The primitive coproduct on rational words -/

noncomputable section
namespace PolycyclicRecognition

open TensorProduct
open scoped TensorProduct

variable {n : ℕ}

def rationalWordCoproduct : RationalWords n →ₐ[ℚ] RationalWords n ⊗[ℚ] RationalWords n :=
  rationalWordEvaluation (fun i =>
    rationalWordLetter i ⊗ₜ[ℚ] (1 : RationalWords n) +
      (1 : RationalWords n) ⊗ₜ[ℚ] rationalWordLetter i)

def IsPrimitiveRationalWord (p : RationalWords n) : Prop :=
  rationalWordCoproduct p = p ⊗ₜ[ℚ] (1 : RationalWords n) + (1 : RationalWords n) ⊗ₜ[ℚ] p

theorem rationalWordCoproduct_letter (i : Fin n) :
    IsPrimitiveRationalWord (rationalWordLetter i) := by
  unfold IsPrimitiveRationalWord rationalWordCoproduct rationalWordLetter
  rw [rationalWordEvaluation_single]
  simp

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RationalWordOperators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Degree and signed reversal on rational words -/

noncomputable section
namespace PolycyclicRecognition

variable {n : ℕ}

def rationalWordDegree : RationalWords n →ₗ[ℚ] RationalWords n :=
  (Finsupp.linearCombination ℚ (fun w : FreeMonoid (Fin n) =>
    (w.length : ℚ) • MonoidAlgebra.single w 1)).comp
    (MonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap

def rationalWordAntipode : RationalWords n →ₗ[ℚ] RationalWords n :=
  (Finsupp.linearCombination ℚ (fun w : FreeMonoid (Fin n) =>
    (-1 : ℚ) ^ w.length • MonoidAlgebra.single (FreeMonoid.ofList w.toList.reverse) 1)).comp
    (MonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap

theorem rationalWordDegree_single (w : FreeMonoid (Fin n)) (q : ℚ) :
    rationalWordDegree (MonoidAlgebra.single w q) =
      q • ((w.length : ℚ) • MonoidAlgebra.single w 1) := by
  change Finsupp.linearCombination ℚ _ (Finsupp.single w q) = _
  exact Finsupp.linearCombination_single (R := ℚ)
    (v := fun w : FreeMonoid (Fin n) => (w.length : ℚ) • MonoidAlgebra.single w 1) q w

theorem rationalWordAntipode_single (w : FreeMonoid (Fin n)) (q : ℚ) :
    rationalWordAntipode (MonoidAlgebra.single w q) =
      q • ((-1 : ℚ) ^ w.length • MonoidAlgebra.single (FreeMonoid.ofList w.toList.reverse) 1) := by
  change Finsupp.linearCombination ℚ _ (Finsupp.single w q) = _
  exact Finsupp.linearCombination_single (R := ℚ)
    (v := fun w : FreeMonoid (Fin n) =>
      (-1 : ℚ) ^ w.length • MonoidAlgebra.single (FreeMonoid.ofList w.toList.reverse) 1) q w

theorem rationalWordDegree_letter_mul (i : Fin n) (p : RationalWords n) :
    rationalWordDegree (rationalWordLetter i * p) =
      rationalWordLetter i * p + rationalWordLetter i * rationalWordDegree p := by
  induction p using MonoidAlgebra.induction_on with
  | of w =>
    change rationalWordDegree (rationalWordLetter i * MonoidAlgebra.single w 1) =
      rationalWordLetter i * MonoidAlgebra.single w 1 +
        rationalWordLetter i * rationalWordDegree (MonoidAlgebra.single w 1)
    simp only [rationalWordLetter, MonoidAlgebra.single_mul_single, one_mul,
      rationalWordDegree_single, one_smul, Algebra.mul_smul_comm]
    simp only [FreeMonoid.length, FreeMonoid.toList_of_mul, List.length_cons,
      Nat.cast_add, Nat.cast_one, add_smul, one_smul]
    exact add_comm _ _
  | add p q hp hq =>
    simp only [mul_add, map_add, hp, hq]
    abel
  | smul r p hp =>
    simp only [Algebra.mul_smul_comm, map_smul, hp, smul_add]

theorem rationalWordAntipode_letter_mul (i : Fin n) (p : RationalWords n) :
    rationalWordAntipode (rationalWordLetter i * p) =
      -(rationalWordAntipode p * rationalWordLetter i) := by
  induction p using MonoidAlgebra.induction_on with
  | of w =>
    change rationalWordAntipode (rationalWordLetter i * MonoidAlgebra.single w 1) =
      -(rationalWordAntipode (MonoidAlgebra.single w 1) * rationalWordLetter i)
    simp only [rationalWordLetter, MonoidAlgebra.single_mul_single, one_mul,
      rationalWordAntipode_single, one_smul, smul_mul_assoc]
    simp only [FreeMonoid.length, FreeMonoid.toList_of_mul, List.length_cons,
      List.reverse_cons, FreeMonoid.ofList_append, FreeMonoid.ofList_singleton,
      pow_succ, mul_neg, mul_one, neg_smul]
  | add p q hp hq => simp only [mul_add, map_add, hp, hq, add_mul, neg_add_rev]; abel
  | smul r p hp =>
    simp only [Algebra.mul_smul_comm, map_smul, hp, smul_mul_assoc, smul_neg]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_WordTensorConvolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The antipode and degree convolutions for rational words -/

noncomputable section
namespace PolycyclicRecognition

open TensorProduct
open scoped TensorProduct

variable {n : ℕ}

def wordAntipodeConvolution :
    RationalWords n ⊗[ℚ] RationalWords n →ₗ[ℚ] RationalWords n :=
  (LinearMap.mul' ℚ (RationalWords n)).comp
    (TensorProduct.map LinearMap.id rationalWordAntipode)

def wordDegreeConvolution :
    RationalWords n ⊗[ℚ] RationalWords n →ₗ[ℚ] RationalWords n :=
  (LinearMap.mul' ℚ (RationalWords n)).comp
    (TensorProduct.map rationalWordDegree rationalWordAntipode)

@[simp] theorem wordAntipodeConvolution_tmul (p q : RationalWords n) :
    wordAntipodeConvolution (p ⊗ₜ[ℚ] q) = p * rationalWordAntipode q := rfl

@[simp] theorem wordDegreeConvolution_tmul (p q : RationalWords n) :
    wordDegreeConvolution (p ⊗ₜ[ℚ] q) =
      rationalWordDegree p * rationalWordAntipode q := rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PrimitiveWordProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The Dynkin projection identity for primitive rational words -/

noncomputable section
namespace PolycyclicRecognition

open TensorProduct
open scoped TensorProduct

variable {n : ℕ}

@[simp] theorem rationalWordDegree_one : rationalWordDegree (1 : RationalWords n) = 0 := by
  rw [MonoidAlgebra.one_def, rationalWordDegree_single]
  simp [FreeMonoid.length]

@[simp] theorem rationalWordAntipode_one :
    rationalWordAntipode (1 : RationalWords n) = 1 := by
  rw [MonoidAlgebra.one_def, rationalWordAntipode_single]
  simp [FreeMonoid.length, ← MonoidAlgebra.one_def]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_HomogeneousWordProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Homogeneous primitive words and their right-nested Lie expressions -/

noncomputable section
namespace PolycyclicRecognition

variable {n : ℕ}

def IsHomogeneousRationalWord (p : RationalWords n) (d : ℕ) : Prop :=
  ∀ w, p.coeff w ≠ 0 → w.length = d

theorem rationalWordDegree_coeff (p : RationalWords n) (w : FreeMonoid (Fin n)) :
    (rationalWordDegree p).coeff w = (w.length : ℚ) * p.coeff w := by
  induction p using MonoidAlgebra.induction_on with
  | of v =>
    change (rationalWordDegree (MonoidAlgebra.single v 1)).coeff w =
      (w.length : ℚ) * (MonoidAlgebra.single v (1 : ℚ)).coeff w
    rw [rationalWordDegree_single]
    by_cases h : v = w
    · subst v; simp
    · simp [MonoidAlgebra.coeff_single, h]
  | add p q hp hq =>
    simp only [map_add, MonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hq, mul_add]
  | smul r p hp =>
    simp only [map_smul, MonoidAlgebra.coeff_smul, Finsupp.smul_apply, hp, smul_eq_mul]
    ring

theorem IsHomogeneousRationalWord.degree_eq {p : RationalWords n} {d : ℕ}
    (hp : IsHomogeneousRationalWord p d) : rationalWordDegree p = (d : ℚ) • p := by
  ext w
  rw [rationalWordDegree_coeff]
  by_cases h : p.coeff w = 0
  · simp [h]
  · simp [hp w h]

variable {A : Type*} [Ring A] [Algebra ℚ A] (X : Fin n → A)

theorem rationalWordEvaluation_letter (i : Fin n) :
    rationalWordEvaluation X (rationalWordLetter i) = X i := by
  simp [rationalWordLetter, rationalWordEvaluation_single]

theorem rationalWordEvaluation_wordRightLie (l : List (Fin n)) :
    rationalWordEvaluation X (wordRightLie rationalWordLetter l) = wordRightLie X l := by
  induction l with
  | nil => simp [wordRightLie]
  | cons i l ih =>
    cases l with
    | nil => simpa [wordRightLie] using rationalWordEvaluation_letter X i
    | cons j l =>
      simp only [wordRightLie, map_sub, map_mul, rationalWordEvaluation_letter] at ih ⊢
      rw [ih]

theorem rationalWordEvaluation_projection (p : RationalWords n) :
    rationalWordEvaluation X (wordLieProjection rationalWordLetter p) =
      wordLieProjection X p := by
  induction p using MonoidAlgebra.induction_on with
  | of w =>
    change rationalWordEvaluation X (wordLieProjection rationalWordLetter
      (MonoidAlgebra.single w 1)) = wordLieProjection X (MonoidAlgebra.single w 1)
    simp only [wordLieProjection_single, one_smul, rationalWordEvaluation_wordRightLie]
  | add p q hp hq => simp only [map_add, hp, hq]
  | smul r p hp => simp only [map_smul, hp]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_MonoidCoefficientLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coefficientwise rational linear maps on monoid algebras -/

noncomputable section
namespace PolycyclicRecognition

variable {R S M : Type*} [Semiring R] [Semiring S] [Module ℚ R] [Module ℚ S]

def monoidCoefficientLinear (f : R →ₗ[ℚ] S) : MonoidAlgebra R M →ₗ[ℚ] MonoidAlgebra S M :=
  (MonoidAlgebra.coeffLinearEquiv ℚ).symm.toLinearMap.comp
    ((Finsupp.mapRange.linearMap f).comp (MonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap)

@[simp] theorem monoidCoefficientLinear_coeff (f : R →ₗ[ℚ] S) (p : MonoidAlgebra R M) (m : M) :
    (monoidCoefficientLinear f p).coeff m = f (p.coeff m) := rfl

@[simp] theorem monoidCoefficientLinear_single (f : R →ₗ[ℚ] S) (m : M) (r : R) :
    monoidCoefficientLinear f (MonoidAlgebra.single m r) = MonoidAlgebra.single m (f r) := by
  classical
  ext m'
  by_cases h : m = m'
  · subst m'; simp
  · simp [MonoidAlgebra.coeff_single, h]

variable [Monoid M]

theorem monoidCoefficientLinear_single_mul (f : R →ₗ[ℚ] S) (m : M) (p : MonoidAlgebra R M) :
    monoidCoefficientLinear f (MonoidAlgebra.single m 1 * p) =
      MonoidAlgebra.single m 1 * monoidCoefficientLinear f p := by
  induction p using MonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [mul_add, map_add, hp, hq]
  | single n r => simp

theorem monoidCoefficientLinear_mapDomain {N : Type*} (f : R →ₗ[ℚ] S) (g : M → N)
    (p : MonoidAlgebra R M) :
    monoidCoefficientLinear f (MonoidAlgebra.mapDomain g p) =
      MonoidAlgebra.mapDomain g (monoidCoefficientLinear f p) := by
  induction p using MonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [MonoidAlgebra.mapDomain_add, map_add, hp, hq]
  | single m r => simp

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_MonoidTensorCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Multiplicative coordinates for tensors of monoid algebras -/

noncomputable section
namespace PolycyclicRecognition

open TensorProduct
open scoped TensorProduct

variable (R M N : Type*) [CommRing R] [Monoid M] [Monoid N]

def monoidLeft : MonoidAlgebra R M →ₐ[R] MonoidAlgebra R (M × N) :=
  MonoidAlgebra.mapDomainAlgHom R R (MonoidHom.inl M N)

def monoidRight : MonoidAlgebra R N →ₐ[R] MonoidAlgebra R (M × N) :=
  MonoidAlgebra.mapDomainAlgHom R R (MonoidHom.inr M N)

theorem monoidLeft_single (m : M) (a : R) :
    monoidLeft R M N (MonoidAlgebra.single m a) = MonoidAlgebra.single (m, 1) a := by
  simp [monoidLeft]

theorem monoidRight_single (n : N) (a : R) :
    monoidRight R M N (MonoidAlgebra.single n a) = MonoidAlgebra.single (1, n) a := by
  simp [monoidRight]

theorem monoidLeft_commute_right (p : MonoidAlgebra R M) (q : MonoidAlgebra R N) :
    Commute (monoidLeft R M N p) (monoidRight R M N q) := by
  induction p using MonoidAlgebra.induction_linear with
  | zero => simp
  | add p p' hp hp' => simpa only [map_add] using hp.add_left hp'
  | single m a =>
    induction q using MonoidAlgebra.induction_linear with
    | zero => simp
    | add q q' hq hq' => simpa only [map_add] using hq.add_right hq'
    | single n b =>
      rw [monoidLeft_single, monoidRight_single]
      apply MonoidAlgebra.single_commute_single _ (.all _ _)
      show (m, (1 : N)) * (1, n) = (1, n) * (m, 1)
      simp

def monoidTensorCoordinates :
    MonoidAlgebra R M ⊗[R] MonoidAlgebra R N →ₐ[R] MonoidAlgebra R (M × N) :=
  Algebra.TensorProduct.lift (monoidLeft R M N) (monoidRight R M N)
    (monoidLeft_commute_right R M N)

theorem monoidTensorCoordinates_single (m : M) (a : R) (n : N) (b : R) :
    monoidTensorCoordinates R M N
      (MonoidAlgebra.single m a ⊗ₜ[R] MonoidAlgebra.single n b) =
        MonoidAlgebra.single (m, n) (a * b) := by
  rw [monoidTensorCoordinates, Algebra.TensorProduct.lift_tmul,
    monoidLeft_single, monoidRight_single]
  simp

theorem monoidTensorCoordinates_tmul_one (p : MonoidAlgebra R M) :
    monoidTensorCoordinates R M N (p ⊗ₜ[R] (1 : MonoidAlgebra R N)) =
      MonoidAlgebra.mapDomain (fun m => (m, (1 : N))) p := by
  rw [monoidTensorCoordinates, Algebra.TensorProduct.lift_tmul, map_one, mul_one]
  rfl

theorem monoidTensorCoordinates_one_tmul (p : MonoidAlgebra R N) :
    monoidTensorCoordinates R M N ((1 : MonoidAlgebra R M) ⊗ₜ[R] p) =
      MonoidAlgebra.mapDomain (fun n => ((1 : M), n)) p := by
  rw [monoidTensorCoordinates, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
  rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PairedWordCoproduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coefficient extraction commutes with the primitive word coproduct -/

noncomputable section
namespace PolycyclicRecognition

variable (R : Type*) [CommRing R] (n : ℕ)

def pairedWordCoproduct : MonoidAlgebra R (FreeMonoid (Fin n)) →ₐ[R]
    MonoidAlgebra R (FreeMonoid (Fin n) × FreeMonoid (Fin n)) :=
  MonoidAlgebra.lift _ _ _ (FreeMonoid.lift (fun i =>
    MonoidAlgebra.single (FreeMonoid.of i, 1) 1 +
      MonoidAlgebra.single (1, FreeMonoid.of i) 1))

theorem pairedWordCoproduct_letter (i : Fin n) :
    pairedWordCoproduct R n (MonoidAlgebra.single (FreeMonoid.of i) 1) =
      MonoidAlgebra.single (FreeMonoid.of i, 1) 1 +
        MonoidAlgebra.single (1, FreeMonoid.of i) 1 := by
  simp [pairedWordCoproduct, MonoidAlgebra.lift_single, FreeMonoid.lift_apply]

variable {R n} [Module ℚ R]

theorem coefficientLinear_pairedWordCoproduct (f : R →ₗ[ℚ] ℚ)
    (p : MonoidAlgebra R (FreeMonoid (Fin n))) :
    monoidCoefficientLinear f (pairedWordCoproduct R n p) =
      pairedWordCoproduct ℚ n (monoidCoefficientLinear f p) := by
  induction p using MonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | single w r =>
    rw [monoidCoefficientLinear_single]
    induction w using FreeMonoid.recOn with
    | one =>
      simp [pairedWordCoproduct, MonoidAlgebra.lift_single, FreeMonoid.lift_apply,
        MonoidAlgebra.one_def, smul_eq_mul]
    | of_mul i w ih =>
      have hR : MonoidAlgebra.single (FreeMonoid.of i * w) r =
          MonoidAlgebra.single (FreeMonoid.of i) (1 : R) * MonoidAlgebra.single w r := by simp
      have hQ : MonoidAlgebra.single (FreeMonoid.of i * w) (f r) =
          MonoidAlgebra.single (FreeMonoid.of i) (1 : ℚ) * MonoidAlgebra.single w (f r) := by simp
      rw [hR, hQ, map_mul (pairedWordCoproduct R n), map_mul (pairedWordCoproduct ℚ n),
        pairedWordCoproduct_letter, pairedWordCoproduct_letter]
      simp only [add_mul, map_add, monoidCoefficientLinear_single_mul, ih]

theorem pairedWordCoproduct_eq_rational (p : RationalWords n) :
    pairedWordCoproduct ℚ n p =
      monoidTensorCoordinates ℚ (FreeMonoid (Fin n)) (FreeMonoid (Fin n))
        (rationalWordCoproduct p) := by
  change pairedWordCoproduct ℚ n p =
    ((monoidTensorCoordinates ℚ (FreeMonoid (Fin n)) (FreeMonoid (Fin n))).comp
      rationalWordCoproduct) p
  apply congrArg (fun F : RationalWords n →ₐ[ℚ] _ => F p)
  apply MonoidAlgebra.algHom_ext'
  · apply FreeMonoid.hom_eq
    intro i
    change pairedWordCoproduct ℚ n (rationalWordLetter i) =
      monoidTensorCoordinates ℚ _ _ (rationalWordCoproduct (rationalWordLetter i))
    rw [rationalWordCoproduct_letter, map_add]
    simp only [rationalWordLetter, pairedWordCoproduct_letter, MonoidAlgebra.one_def,
      monoidTensorCoordinates_single, one_mul]
  · exact Subsingleton.elim _ _

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_TruncatedRationalScalars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite scalar ring used for universal nilpotent series -/

noncomputable section
namespace PolycyclicRecognition

abbrev TruncatedRationalScalars (c : ℕ) :=
  AdjoinRoot ((Polynomial.X : Polynomial ℚ) ^ (c + 1))

def truncatedScalarParameter (c : ℕ) : TruncatedRationalScalars c :=
  AdjoinRoot.root _

theorem truncatedScalarParameter_pow (c : ℕ) :
    truncatedScalarParameter c ^ (c + 1) = 0 := by
  simpa only [Polynomial.eval₂_pow, Polynomial.eval₂_X, truncatedScalarParameter] using
    AdjoinRoot.eval₂_root ((Polynomial.X : Polynomial ℚ) ^ (c + 1))

def truncatedScalarCoefficient (c k : ℕ) : TruncatedRationalScalars c →ₗ[ℚ] ℚ :=
  (Polynomial.lcoeff ℚ k).comp (AdjoinRoot.modByMonicHom (Polynomial.monic_X_pow (c + 1)))

theorem truncatedScalarCoefficient_parameter_pow (c j k : ℕ) (hj : j ≤ c) :
    truncatedScalarCoefficient c k (truncatedScalarParameter c ^ j) =
      if j = k then 1 else 0 := by
  change ((AdjoinRoot.modByMonicHom (Polynomial.monic_X_pow (c + 1)))
    (AdjoinRoot.root _ ^ j)).coeff k = _
  rw [AdjoinRoot.root, ← map_pow, AdjoinRoot.modByMonicHom_mk]
  have hd : (Polynomial.X ^ j : Polynomial ℚ).degree <
      (Polynomial.X ^ (c + 1) : Polynomial ℚ).degree := by
    simpa only [Polynomial.degree_X_pow, Nat.cast_lt] using Nat.lt_succ_of_le hj
  rw [(Polynomial.modByMonic_eq_self_iff (Polynomial.monic_X_pow (c + 1))).mpr hd]
  simpa only [eq_comm] using Polynomial.coeff_X_pow j k

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_PrimitiveNilpotentExponential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Products of exponentials in the primitive tensor coproduct -/

noncomputable section
namespace PolycyclicRecognition

open TensorProduct
open scoped TensorProduct

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A] [Algebra ℚ A]

theorem nilpotentExp_primitive (Δ : A →ₐ[R] A ⊗[R] A) (a : A)
    (ha : IsNilpotent a) (hΔ : Δ a = a ⊗ₜ[R] (1 : A) + (1 : A) ⊗ₜ[R] a) :
    Δ (IsNilpotent.exp a) = IsNilpotent.exp a ⊗ₜ[R] IsNilpotent.exp a := by
  let l : A →+* A ⊗[R] A := Algebra.TensorProduct.includeLeftRingHom
  let r : A →+* A ⊗[R] A := Algebra.TensorProduct.includeRight.toRingHom
  have hc : Commute (l a) (r a) := by
    change (a ⊗ₜ[R] (1 : A)) * ((1 : A) ⊗ₜ[R] a) =
      ((1 : A) ⊗ₜ[R] a) * (a ⊗ₜ[R] (1 : A))
    simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  change Δ.toRingHom (IsNilpotent.exp a) = _
  rw [IsNilpotent.map_exp ha]
  change IsNilpotent.exp (Δ a) = _
  rw [hΔ]
  change IsNilpotent.exp (l a + r a) = _
  rw [IsNilpotent.exp_add_of_commute hc (ha.map l) (ha.map r),
    ← IsNilpotent.map_exp ha l, ← IsNilpotent.map_exp ha r]
  change (IsNilpotent.exp a ⊗ₜ[R] (1 : A)) *
    ((1 : A) ⊗ₜ[R] IsNilpotent.exp a) = _
  simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem product_nilpotentExp_primitive (Δ : A →ₐ[R] A ⊗[R] A) (L : List A)
    (hL : ∀ a ∈ L, IsNilpotent a ∧ Δ a = a ⊗ₜ[R] (1 : A) + (1 : A) ⊗ₜ[R] a) :
    Δ (L.map IsNilpotent.exp).prod =
      (L.map IsNilpotent.exp).prod ⊗ₜ[R] (L.map IsNilpotent.exp).prod := by
  induction L with
  | nil => simp [Algebra.TensorProduct.one_def]
  | cons a L ih =>
    have ha := hL a (List.mem_cons_self ..)
    have htail := ih (fun b hb => hL b (List.mem_cons_of_mem a hb))
    simp only [List.map_cons, List.prod_cons, map_mul,
      nilpotentExp_primitive Δ a ha.1 ha.2, htail, Algebra.TensorProduct.tmul_mul_tmul]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_TruncatedWordExponential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The universal exponential product over truncated rational scalars -/

noncomputable section
namespace PolycyclicRecognition

open TensorProduct
open scoped TensorProduct

abbrev TruncatedWords (c n : ℕ) :=
  MonoidAlgebra (TruncatedRationalScalars c) (FreeMonoid (Fin n))

variable (c n : ℕ)

def truncatedWordLetter (i : Fin n) : TruncatedWords c n :=
  MonoidAlgebra.single (FreeMonoid.of i) 1

def truncatedWordCoproduct : TruncatedWords c n →ₐ[TruncatedRationalScalars c]
    TruncatedWords c n ⊗[TruncatedRationalScalars c] TruncatedWords c n :=
  MonoidAlgebra.lift _ _ _ (FreeMonoid.lift (fun i =>
    truncatedWordLetter c n i ⊗ₜ[TruncatedRationalScalars c] (1 : TruncatedWords c n) +
      (1 : TruncatedWords c n) ⊗ₜ[TruncatedRationalScalars c] truncatedWordLetter c n i))

theorem truncatedWordCoproduct_letter (i : Fin n) :
    truncatedWordCoproduct c n (truncatedWordLetter c n i) =
      truncatedWordLetter c n i ⊗ₜ[TruncatedRationalScalars c] (1 : TruncatedWords c n) +
        (1 : TruncatedWords c n) ⊗ₜ[TruncatedRationalScalars c] truncatedWordLetter c n i := by
  simp [truncatedWordCoproduct, truncatedWordLetter, MonoidAlgebra.lift_single,
    FreeMonoid.lift_apply]

theorem truncatedWordCoproduct_parameter_letter (i : Fin n) :
    truncatedWordCoproduct c n (truncatedScalarParameter c • truncatedWordLetter c n i) =
      (truncatedScalarParameter c • truncatedWordLetter c n i) ⊗ₜ[TruncatedRationalScalars c]
        (1 : TruncatedWords c n) + (1 : TruncatedWords c n) ⊗ₜ[TruncatedRationalScalars c]
        (truncatedScalarParameter c • truncatedWordLetter c n i) := by
  simp only [map_smul, truncatedWordCoproduct_letter, smul_add,
    ← smul_tmul', tmul_smul]

def truncatedWordExponentialProduct : TruncatedWords c n :=
  (List.ofFn (fun i : Fin n =>
    IsNilpotent.exp (truncatedScalarParameter c • truncatedWordLetter c n i))).prod

def truncatedWordLogarithm : TruncatedWords c n :=
  finiteNilpotentLog (c + 1) (truncatedWordExponentialProduct c n - 1)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_TruncatedPrimitiveCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Primitive rational coefficients of the truncated universal logarithm -/

noncomputable section
namespace PolycyclicRecognition

open TensorProduct
open scoped TensorProduct

variable (c n : ℕ)

theorem pairedWordCoproduct_eq_truncated (p : TruncatedWords c n) :
    pairedWordCoproduct (TruncatedRationalScalars c) n p =
      monoidTensorCoordinates (TruncatedRationalScalars c) _ _ (truncatedWordCoproduct c n p) := by
  change pairedWordCoproduct (TruncatedRationalScalars c) n p =
    ((monoidTensorCoordinates (TruncatedRationalScalars c) _ _).comp
      (truncatedWordCoproduct c n)) p
  apply congrArg (fun F : TruncatedWords c n →ₐ[TruncatedRationalScalars c] _ => F p)
  apply MonoidAlgebra.algHom_ext'
  · apply FreeMonoid.hom_eq
    intro i
    change pairedWordCoproduct (TruncatedRationalScalars c) n (truncatedWordLetter c n i) =
      monoidTensorCoordinates (TruncatedRationalScalars c) _ _
        (truncatedWordCoproduct c n (truncatedWordLetter c n i))
    rw [truncatedWordCoproduct_letter, map_add]
    simp only [truncatedWordLetter, pairedWordCoproduct_letter, MonoidAlgebra.one_def,
      monoidTensorCoordinates_single, one_mul]
  · exact Subsingleton.elim _ _

def universalLogarithmCoefficient (d : ℕ) : RationalWords n :=
  monoidCoefficientLinear (truncatedScalarCoefficient c d) (truncatedWordLogarithm c n)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_WeightedWordSubalgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Word length equals scalar degree in the universal construction -/

noncomputable section
namespace PolycyclicRecognition

variable (c n : ℕ)

def weightedWord (w : FreeMonoid (Fin n)) : TruncatedWords c n :=
  MonoidAlgebra.single w (truncatedScalarParameter c ^ w.length)

@[simp] theorem weightedWord_one : weightedWord c n 1 = 1 := by
  simp [weightedWord, FreeMonoid.length, MonoidAlgebra.one_def]

theorem weightedWord_mul (u v : FreeMonoid (Fin n)) :
    weightedWord c n (u * v) = weightedWord c n u * weightedWord c n v := by
  simp [weightedWord, FreeMonoid.length, pow_add]

def weightedWordSpan : Submodule ℚ (TruncatedWords c n) :=
  Submodule.span ℚ (Set.range (weightedWord c n))

theorem weightedWordSpan_mul {p q : TruncatedWords c n}
    (hp : p ∈ weightedWordSpan c n) (hq : q ∈ weightedWordSpan c n) :
    p * q ∈ weightedWordSpan c n := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨u, rfl⟩ := hp
    induction hq using Submodule.span_induction with
    | mem q hq =>
      obtain ⟨v, rfl⟩ := hq
      rw [← weightedWord_mul]
      exact Submodule.subset_span ⟨u * v, rfl⟩
    | zero => rw [mul_zero]; exact (weightedWordSpan c n).zero_mem
    | add q r _ _ hq hr =>
      rw [mul_add]
      exact (weightedWordSpan c n).add_mem hq hr
    | smul a q _ hq =>
      rw [Algebra.mul_smul_comm]
      exact (weightedWordSpan c n).smul_mem a hq
  | zero => rw [zero_mul]; exact (weightedWordSpan c n).zero_mem
  | add p r _ _ hp hr =>
    rw [add_mul]
    exact (weightedWordSpan c n).add_mem hp hr
  | smul a p _ hp =>
    rw [smul_mul_assoc]
    exact (weightedWordSpan c n).smul_mem a hp

def weightedWordSubalgebra : Subalgebra ℚ (TruncatedWords c n) where
  carrier := weightedWordSpan c n
  add_mem' := (weightedWordSpan c n).add_mem
  mul_mem' := weightedWordSpan_mul c n
  algebraMap_mem' q := by
    rw [Algebra.algebraMap_eq_smul_one]
    apply (weightedWordSpan c n).smul_mem
    rw [← weightedWord_one c n]
    exact Submodule.subset_span ⟨1, rfl⟩

theorem weightedWordSubalgebra_parameter_letter (i : Fin n) :
    truncatedScalarParameter c • truncatedWordLetter c n i ∈ weightedWordSubalgebra c n := by
  change _ ∈ weightedWordSpan c n
  have h : truncatedScalarParameter c • truncatedWordLetter c n i =
      weightedWord c n (FreeMonoid.of i) := by
    simp [truncatedWordLetter, weightedWord, FreeMonoid.length]
  rw [h]
  exact Submodule.subset_span ⟨_, rfl⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_WeightedWordLogarithm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The universal logarithm preserves the scalar/word grading -/

noncomputable section
namespace PolycyclicRecognition

variable (c n : ℕ)

theorem weightedWordSubalgebra_aeval {a : TruncatedWords c n}
    (ha : a ∈ weightedWordSubalgebra c n) (p : Polynomial ℚ) :
    Polynomial.aeval a p ∈ weightedWordSubalgebra c n := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact (weightedWordSubalgebra c n).add_mem hp hq
  | monomial k q =>
    rw [Polynomial.aeval_monomial]
    exact (weightedWordSubalgebra c n).mul_mem
      ((weightedWordSubalgebra c n).algebraMap_mem q)
      ((weightedWordSubalgebra c n).pow_mem ha k)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_HomogeneousUniversalLogarithm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Homogeneous Lie expansions of the universal logarithm coefficients -/

noncomputable section
namespace PolycyclicRecognition

variable {n d : ℕ}

theorem IsHomogeneousRationalWord.zero : IsHomogeneousRationalWord (0 : RationalWords n) d := by
  intro w hw
  simp at hw

theorem IsHomogeneousRationalWord.add {p q : RationalWords n}
    (hp : IsHomogeneousRationalWord p d) (hq : IsHomogeneousRationalWord q d) :
    IsHomogeneousRationalWord (p + q) d := by
  intro w hw
  by_contra hd
  have hp0 : p.coeff w = 0 := by by_contra h; exact hd (hp w h)
  have hq0 : q.coeff w = 0 := by by_contra h; exact hd (hq w h)
  exact hw (by simp [hp0, hq0])

theorem IsHomogeneousRationalWord.smul {p : RationalWords n}
    (hp : IsHomogeneousRationalWord p d) (a : ℚ) : IsHomogeneousRationalWord (a • p) d := by
  intro w hw
  by_contra hd
  have hp0 : p.coeff w = 0 := by by_contra h; exact hd (hp w h)
  exact hw (by simp [hp0])

theorem homogeneousRationalWord_single (w : FreeMonoid (Fin n)) (a : ℚ)
    (h : a ≠ 0 → w.length = d) : IsHomogeneousRationalWord (MonoidAlgebra.single w a) d := by
  classical
  intro v hv
  by_cases hw : w = v
  · subst v
    apply h
    simpa using hv
  · exact (hv (by simp [MonoidAlgebra.coeff_single, hw])).elim

theorem weightedWord_coefficient_homogeneous (c d : ℕ) (w : FreeMonoid (Fin n)) :
    IsHomogeneousRationalWord
      (monoidCoefficientLinear (truncatedScalarCoefficient c d) (weightedWord c n w)) d := by
  rw [weightedWord, monoidCoefficientLinear_single]
  apply homogeneousRationalWord_single
  intro ha
  by_contra hd
  apply ha
  by_cases hc : w.length ≤ c
  · rw [truncatedScalarCoefficient_parameter_pow c w.length d hc, ite_eq_right hd]
  · have hz : truncatedScalarParameter c ^ w.length = 0 :=
      pow_eq_zero_of_le (Nat.lt_of_not_ge hc) (truncatedScalarParameter_pow c)
    rw [hz, map_zero]

theorem weightedWordSpan_coefficient_homogeneous (c n d : ℕ) (p : TruncatedWords c n)
    (hp : p ∈ weightedWordSpan c n) :
    IsHomogeneousRationalWord (monoidCoefficientLinear (truncatedScalarCoefficient c d) p) d := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨w, rfl⟩ := hp
    exact weightedWord_coefficient_homogeneous c d w
  | zero => simpa only [map_zero] using IsHomogeneousRationalWord.zero (n := n) (d := d)
  | add p q _ _ hp hq => simpa only [map_add] using hp.add hq
  | smul a p _ hp => simpa only [map_smul] using hp.smul a

attribute [local instance 100] LieRing.ofAssociativeRing

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_IndependentSwitchParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The measurable event of successful independent switch parameters -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set
open scoped ENNReal

universe u

/-- Two independent samples per switch, in their prescribed order. -/
abbrev SwitchParameters (G : Type u) : ℕ → Type u
  | 0 => PUnit
  | k + 1 => G × G × SwitchParameters G k

variable {G : Type*} [Group G] [MeasurableSpace G]

/-- A parameter is successful precisely when every intermediate state
belongs to the next retained set. -/
def SwitchSuccessful (S : ℕ → Set G) :
    (n k : ℕ) → G → SwitchParameters G k → Prop
  | _, 0, _, _ => True
  | n, k + 1, x, p =>
    x * p.1 * p.2.1⁻¹ ∈ S (n + 1) ∧
      SwitchSuccessful S (n + 1) k (x * p.1 * p.2.1⁻¹) p.2.2

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_InvariantFactor
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

/-- The measurable factor, without imposing any quotient topology. -/
structure InvariantFactor (G X : Type*) where
  val : X

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_InvariantLinearLayer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Endomorphisms on an invariant subquotient

This is the concrete linear bridge used on successive lower-central factors.
Commutation modulo the smaller subspace becomes exact commutation, and
unipotence survives restriction and quotient.
-/

noncomputable section
namespace PolycyclicRecognition
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

abbrev InvariantLinearLayer (U W : Submodule ℝ V) := U ⧸ W.comap U.subtype

def invariantLayerEnd (U W : Submodule ℝ V) (f : Module.End ℝ V)
    (hU : ∀ x ∈ U, f x ∈ U) (hW : ∀ x ∈ W, f x ∈ W) :
    Module.End ℝ (InvariantLinearLayer U W) :=
  (W.comap U.subtype).mapQ (W.comap U.subtype) (f.restrict hU) (fun x hx => hW x hx)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_LinearConjugationCentralizer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Commutation through invertible linear factors -/

namespace PolycyclicRecognition
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem linear_commute_symm (e : V ≃ₗ[ℝ] V) (T : Module.End ℝ V)
    (h : Commute T e.toLinearMap) : Commute T e.symm.toLinearMap := by
  apply LinearMap.ext
  intro x
  change T (e.symm x) = e.symm (T x)
  apply e.injective
  rw [e.apply_symm_apply]
  have hh : T (e (e.symm x)) = e (T (e.symm x)) := LinearMap.congr_fun h.eq _
  rw [e.apply_symm_apply] at hh
  exact hh.symm

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_LocallyBoundedDerivedSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A uniform derived-series bound passes from finitely generated subgroups -/
noncomputable section
namespace PolycyclicRecognition
open scoped commutatorElement
variable {G : Type} [Group G]

def ambientDerivedSeries (H : Subgroup G) (n : ℕ) : Subgroup G :=
  (derivedSeries H n).map H.subtype

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_WordCoefficientAgreement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Agreement of word coefficients below a fixed degree -/

noncomputable section
namespace PolycyclicRecognition

variable {n k : ℕ}

def WordCoefficientAgreement (p q : RationalWords n) (k : ℕ) : Prop :=
  ∀ w, w.length < k → p.coeff w = q.coeff w

theorem WordCoefficientAgreement.refl (p : RationalWords n) (k : ℕ) :
    WordCoefficientAgreement p p k := fun _ _ => rfl

theorem WordCoefficientAgreement.sub {p q r s : RationalWords n}
    (hp : WordCoefficientAgreement p q k) (hr : WordCoefficientAgreement r s k) :
    WordCoefficientAgreement (p - r) (q - s) k := by
  intro w hw
  simp only [MonoidAlgebra.coeff_sub, Finsupp.sub_apply, hp w hw, hr w hw]

theorem WordCoefficientAgreement.mul {p q r s : RationalWords n}
    (hp : WordCoefficientAgreement p q k) (hr : WordCoefficientAgreement r s k) :
    WordCoefficientAgreement (p * r) (q * s) k := by
  intro w hw
  rw [word_coeff_mul, word_coeff_mul]
  apply Finset.sum_congr rfl
  intro i _
  have hlen : (wordSplit w i).1.length + (wordSplit w i).2.length = w.length := by
    rw [← FreeMonoid.length_mul, wordSplit_mul]
  rw [hp _ (by omega), hr _ (by omega)]

theorem WordCoefficientAgreement.pow {p q : RationalWords n}
    (hp : WordCoefficientAgreement p q k) (a : ℕ) :
    WordCoefficientAgreement (p ^ a) (q ^ a) k := by
  induction a with
  | zero => exact .refl _ _
  | succ a ha => simpa only [pow_succ] using ha.mul hp

theorem wordCoefficientAgreement_list_prod
    (l : List (RationalWords n × RationalWords n))
    (h : ∀ p ∈ l, WordCoefficientAgreement p.1 p.2 k) :
    WordCoefficientAgreement (l.map Prod.fst).prod (l.map Prod.snd).prod k := by
  induction l with
  | nil => exact .refl _ _
  | cons p l ih =>
    simp only [List.map_cons, List.prod_cons]
    exact (h p (List.mem_cons_self ..)).mul
      (ih (fun q hq => h q (List.mem_cons_of_mem _ hq)))

theorem wordCoefficientAgreement_ofFn_prod {a : ℕ}
    (p q : Fin a → RationalWords n)
    (h : ∀ i, WordCoefficientAgreement (p i) (q i) k) :
    WordCoefficientAgreement (List.ofFn p).prod (List.ofFn q).prod k := by
  have hh := wordCoefficientAgreement_list_prod (List.ofFn (fun i => (p i, q i))) (by
    intro z hz
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
    exact h i)
  simpa only [List.map_ofFn, Function.comp_def] using hh

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_LogarithmCoefficientStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Stable coefficients of a finite logarithm in the augmentation ideal -/

noncomputable section
namespace PolycyclicRecognition

theorem finiteNilpotentLog_succ {A : Type*} [Ring A] [Algebra ℚ A] (p : A) (c : ℕ) :
    finiteNilpotentLog (c + 2) p = finiteNilpotentLog (c + 1) p +
      ((-1 : ℚ) ^ (c + 2) / (c + 1)) • p ^ (c + 1) := by
  rw [show c + 2 = (c + 1) + 1 from rfl, finiteNilpotentLog_sum, Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last]
  rw [← finiteNilpotentLog_sum]

theorem WordCoefficientAgreement.finiteLog {n k : ℕ} {p q : RationalWords n}
    (h : WordCoefficientAgreement p q k) (c : ℕ) :
    WordCoefficientAgreement (finiteNilpotentLog (c + 1) p)
      (finiteNilpotentLog (c + 1) q) k := by
  intro w hw
  rw [finiteNilpotentLog_sum, finiteNilpotentLog_sum]
  simp only [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    MonoidAlgebra.coeff_smul, Finsupp.smul_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [h.pow (i.val + 1) w hw]

theorem finiteLog_coefficient_stable {c d n : ℕ} (h : c ≤ d)
    (p : RationalWords n) (hp : p.coeff 1 = 0)
    (w : FreeMonoid (Fin n)) (hw : w.length ≤ c) :
    (finiteNilpotentLog (c + 1) p).coeff w = (finiteNilpotentLog (d + 1) p).coeff w := by
  induction d, h using Nat.le_induction with
  | base => rfl
  | succ d h ih =>
    rw [show d + 1 + 1 = d + 2 from rfl, finiteNilpotentLog_succ]
    simp only [MonoidAlgebra.coeff_add, Finsupp.add_apply,
      MonoidAlgebra.coeff_smul, Finsupp.smul_apply]
    rw [wordMinimumDegree_pow hp (d + 1) w (by omega), smul_zero, add_zero]
    exact ih

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_MidpointGrids
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite dyadic grids obtained by inserting metric midpoints -/

noncomputable section
namespace PolycyclicRecognition

variable {X : Type*} [MetricSpace X]

def HasMetricMidpoints (X : Type*) [MetricSpace X] : Prop :=
  ∀ x y : X, ∃ z : X, dist x z ≤ dist x y / 2 ∧ dist z y ≤ dist x y / 2

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NilpotentCodimensionOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Splitting off one dimension from a nilpotent Lie algebra

The kernel of a nonzero character is a smaller nilpotent ideal. Choosing a
vector of character one gives the concrete coordinates for the inductive
semidirect-product construction.
-/

noncomputable section
namespace PolycyclicRecognition

open LieModule Module

variable (L : Type*) [LieRing L] [LieAlgebra ℝ L]

structure LieCodimensionOneData where
  character : L →ₗ[ℝ] ℝ
  unit : L
  character_unit : character unit = 1
  character_lie : ∀ (x y : L), character ⁅x, y⁆ = 0

variable {L}

namespace LieCodimensionOneData

variable (D : LieCodimensionOneData L)

def ideal : LieIdeal ℝ L where
  toSubmodule := D.character.ker
  lie_mem := by
    intro x y _
    exact D.character_lie x y

theorem ideal_lt_top : D.ideal < ⊤ := by
  rw [lt_top_iff_ne_top]
  intro h
  have hu : D.unit ∈ D.ideal := by rw [h]; exact LieSubmodule.mem_top _
  change D.character D.unit = 0 at hu
  rw [D.character_unit] at hu
  exact one_ne_zero hu

theorem finrank_ideal_lt [FiniteDimensional ℝ L] : finrank ℝ D.ideal < finrank ℝ L := by
  have hh := Submodule.finrank_lt_finrank_of_lt (s := D.ideal.toSubmodule)
    (t := ⊤) D.ideal_lt_top
  let e : D.ideal ≃ₗ[ℝ] D.ideal.toSubmodule :=
    { toFun := fun x => ⟨x, x.2⟩
      invFun := fun x => ⟨x, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  rw [e.finrank_eq]
  simpa using hh

def split : (D.ideal × ℝ) ≃ₗ[ℝ] L where
  toFun p := p.1 + p.2 • D.unit
  invFun x := (⟨x - D.character x • D.unit, by
    change D.character (x - D.character x • D.unit) = 0
    simp [D.character_unit]⟩, D.character x)
  left_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      have hp : D.character p.1 = 0 := p.1.2
      simp [hp, D.character_unit]
    · have hp : D.character p.1 = 0 := p.1.2
      simp [hp, D.character_unit]
  right_inv x := sub_add_cancel _ _
  map_add' p q := by
    change ((p.1 : L) + (q.1 : L)) + (p.2 + q.2) • D.unit =
      ((p.1 : L) + p.2 • D.unit) + ((q.1 : L) + q.2 • D.unit)
    rw [add_smul]
    abel
  map_smul' a p := by simp [smul_add, smul_smul]

end LieCodimensionOneData

theorem exists_nilpotentCodimensionOneData [FiniteDimensional ℝ L]
    [LieRing.IsNilpotent L] [Nontrivial L] : Nonempty (LieCodimensionOneData L) := by
  have hp : (LieAlgebra.derivedSeries ℝ L 1).toSubmodule < ⊤ :=
    LieAlgebra.derivedSeries_lt_top_of_solvable ℝ L
  obtain ⟨f, hf, hker⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top hp inferInstance
  have hex : ∃ x, f x ≠ 0 := by
    by_contra! h
    exact hf (LinearMap.ext h)
  obtain ⟨x, hx⟩ := hex
  refine ⟨⟨f, (f x)⁻¹ • x, ?_, ?_⟩⟩
  · simp [hx]
  · intro y z
    have hb : ⁅y, z⁆ ∈ LieAlgebra.derivedSeries ℝ L 1 := by
      change ⁅y, z⁆ ∈ ⁅(⊤ : LieIdeal ℝ L), ⊤⁆
      exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top _) (LieSubmodule.mem_top _)
    have hm : f ⁅y, z⁆ ∈ (LieAlgebra.derivedSeries ℝ L 1).toSubmodule.map f :=
      Submodule.mem_map_of_mem hb
    rw [hker] at hm
    exact hm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NilpotentIdealDerivation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The nilpotent derivation in a codimension-one decomposition -/

noncomputable section
namespace PolycyclicRecognition.LieCodimensionOneData

open LieModule

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] (D : LieCodimensionOneData L)

def derivation : LieDerivation ℝ D.ideal D.ideal where
  toLinearMap := LieModule.toEnd ℝ L D.ideal D.unit
  leibniz' x y := by
    apply Subtype.ext
    change ⁅D.unit, ⁅(x : L), (y : L)⁆⁆ =
      ⁅(x : L), ⁅D.unit, (y : L)⁆⁆ - ⁅(y : L), ⁅D.unit, (x : L)⁆⁆
    rw [← lie_skew (y : L) ⁅D.unit, (x : L)⁆, sub_neg_eq_add, add_comm]
    exact leibniz_lie D.unit (x : L) (y : L)

theorem ideal_nilpotent_module [LieRing.IsNilpotent L] : LieModule.IsNilpotent L D.ideal := by
  have : LieModule.IsNilpotent L (⊤ : LieSubmodule ℝ L L) :=
    (LieModule.isNilpotent_of_top_iff' (R := ℝ) (L := L) (M := L)).mpr inferInstance
  exact LieModule.isNilpotent_of_le ℝ L L D.ideal ⊤ le_top

theorem ideal_nilpotent [LieRing.IsNilpotent L] : LieRing.IsNilpotent D.ideal := by
  have := D.ideal_nilpotent_module
  infer_instance

theorem derivation_nilpotent [LieRing.IsNilpotent L] : IsNilpotent D.derivation.toLinearMap := by
  have := D.ideal_nilpotent_module
  exact LieModule.isNilpotent_toEnd_of_isNilpotent ℝ L D.ideal D.unit

/-- In the split coordinates the bracket is the semidirect-product bracket. -/
theorem split_lie (x y : D.ideal) (s t : ℝ) :
    ⁅D.split (x, s), D.split (y, t)⁆ =
      D.split (⁅x, y⁆ + s • D.derivation y - t • D.derivation x, 0) := by
  change ⁅(x : L) + s • D.unit, (y : L) + t • D.unit⁆ =
    (⁅(x : L), (y : L)⁆ + s • ⁅D.unit, (y : L)⁆ - t • ⁅D.unit, (x : L)⁆) +
      (0 : ℝ) • D.unit
  simp only [add_lie, lie_add, smul_lie, lie_smul, lie_self, smul_zero, zero_smul,
    add_zero]
  rw [← lie_skew (x : L) D.unit, smul_neg]
  abel

end PolycyclicRecognition.LieCodimensionOneData

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NilpotentRepresentationProducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A common product bound for nilpotent Lie representations

Engel's theorem supplies a terminating lower central series for the module.
Every product of represented operators of sufficient length is therefore zero.
-/

noncomputable section
namespace PolycyclicRecognition

attribute [local instance 100] LieRing.ofAssociativeRing

variable {L V : Type*} [LieRing L] [LieAlgebra ℝ L]
  [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

theorem exists_vanishing_products_of_pointwise_nilpotent
    (j : L →ₗ⁅ℝ⁆ Module.End ℝ V) (hj : ∀ x, IsNilpotent (j x)) :
    ∃ c : ℕ, ∀ l : List L, c ≤ l.length → (l.map j).prod = 0 := by
  let := LieRingModule.compLieHom V j
  let := LieModule.compLieHom V j
  have hn : LieModule.IsNilpotent L V :=
    (LieModule.isNilpotent_iff_forall' (R := ℝ)).mpr hj
  obtain ⟨c, hc⟩ := (LieModule.isNilpotent_iff ℝ L V).mp hn
  have hmem (l : List L) (v : V) :
      (l.map j).prod v ∈ LieModule.lowerCentralSeries ℝ L V l.length := by
    induction l with
    | nil => simp
    | cons x l hl =>
      rw [List.map_cons, List.prod_cons, List.length_cons, LieModule.lowerCentralSeries_succ]
      exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top x) hl
  refine ⟨c, fun l hl => ?_⟩
  ext v
  have h := (LieModule.antitone_lowerCentralSeries ℝ L V hl) (hmem l v)
  rw [hc] at h
  exact (LieSubmodule.mem_bot _).mp h

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NilpotentMatrixProducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniformly vanishing products in a nilpotent matrix representation -/

noncomputable section
namespace PolycyclicRecognition

attribute [local instance 100] LieRing.ofAssociativeRing

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] {m : ℕ}

theorem exists_vanishing_matrix_products_of_pointwise_nilpotent
    (j : L →ₗ⁅ℝ⁆ Matrix (Fin m) (Fin m) ℝ) (hj : ∀ x, IsNilpotent (j x)) :
    ∃ c : ℕ, ∀ l : List L, c ≤ l.length → (l.map j).prod = 0 := by
  let E : Matrix (Fin m) (Fin m) ℝ ≃ₐ[ℝ] Module.End ℝ (Fin m → ℝ) :=
    Matrix.toLinAlgEquiv'
  let k : L →ₗ⁅ℝ⁆ Module.End ℝ (Fin m → ℝ) := E.toLieEquiv.toLieHom.comp j
  have hk (x : L) : IsNilpotent (k x) := (hj x).map E.toRingHom
  obtain ⟨c, hc⟩ := exists_vanishing_products_of_pointwise_nilpotent k hk
  refine ⟨c, fun l hl => ?_⟩
  apply E.injective
  rw [map_zero, map_list_prod]
  have heq : (l.map j).map E = l.map k := by
    rw [List.map_map]
    rfl
  rw [heq]
  exact hc l hl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NilpotentSpanningOperators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Nilpotent operators spanning a complex nilpotent Lie algebra

Every weight vanishes on the spanning set, hence on the entire Lie algebra.
The zero weight space is therefore the whole representation.
-/

noncomputable section
namespace PolycyclicRecognition

variable {L V : Type*} [LieRing L] [LieAlgebra ℂ L] [LieRing.IsNilpotent L]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [LieRingModule L V] [LieModule ℂ L V]

theorem nilpotent_operators_of_spanning_set (S : Set L)
    (hS : Submodule.span ℂ S = ⊤)
    (h : ∀ x ∈ S, IsNilpotent (LieModule.toEnd ℂ L V x)) (x : L) :
    IsNilpotent (LieModule.toEnd ℂ L V x) := by
  have hweight (χ : LieModule.Weight ℂ L V) : (χ : L → ℂ) = 0 := by
    funext y
    change χ y = 0
    have hy : y ∈ Submodule.span ℂ S := by rw [hS]; trivial
    induction hy using Submodule.span_induction with
    | mem y hy => exact χ.apply_eq_zero_of_isNilpotent y (h y hy)
    | zero => exact map_zero (χ.toLinear ℂ L V)
    | add y z _ _ hy hz =>
        change χ (y + z) = 0
        rw [map_add, hy, hz, add_zero]
    | smul a y _ hy =>
        change χ (a • y) = 0
        rw [map_smul, hy, smul_zero]
  have htop : LieModule.genWeightSpace V (0 : L → ℂ) = ⊤ := by
    apply le_antisymm le_top
    rw [← LieModule.iSup_genWeightSpace_eq_top' ℂ L V]
    apply iSup_le
    intro χ
    rw [hweight χ]
  obtain ⟨k, hk⟩ := LieModule.exists_genWeightSpace_zero_le_ker_of_isNoetherian ℂ V x
  refine ⟨k, ?_⟩
  ext v
  exact hk (by rw [htop]; trivial)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RealNilpotentSpanningOperators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Real nilpotent representations detected on a spanning set

Complexification allows the weight argument; a real-part retraction reflects
the resulting nilpotence back to the original module.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped TensorProduct

variable {L V : Type*} [LieRing L] [LieAlgebra ℝ L] [LieRing.IsNilpotent L]
  [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule L V] [LieModule ℝ L V]

theorem real_nilpotent_operators_of_spanning_set (S : Set L)
    (hS : Submodule.span ℝ S = ⊤)
    (h : ∀ x ∈ S, IsNilpotent (LieModule.toEnd ℝ L V x)) (x : L) :
    IsNilpotent (LieModule.toEnd ℝ L V x) := by
  let T : Set (ℂ ⊗[ℝ] L) := TensorProduct.mk ℝ ℂ L 1 '' S
  have hT : Submodule.span ℂ T = ⊤ := by
    rw [← Submodule.baseChange_span, hS, Submodule.baseChange_top]
  have hgen (z : ℂ ⊗[ℝ] L) (hz : z ∈ T) :
      IsNilpotent (LieModule.toEnd ℂ (ℂ ⊗[ℝ] L) (ℂ ⊗[ℝ] V) z) := by
    obtain ⟨y, hy, rfl⟩ := hz
    change IsNilpotent (LieModule.toEnd ℂ (ℂ ⊗[ℝ] L) (ℂ ⊗[ℝ] V) (1 ⊗ₜ[ℝ] y))
    rw [LieModule.toEnd_baseChange ℝ ℂ L V y]
    exact (h y hy).map (Module.End.baseChangeHom ℝ ℂ V).toRingHom
  have hn := nilpotent_operators_of_spanning_set T hT hgen (1 ⊗ₜ[ℝ] x)
  rw [LieModule.toEnd_baseChange] at hn
  obtain ⟨k, hk⟩ := hn
  have hz : ((LieModule.toEnd ℝ L V x) ^ k).baseChange ℂ = 0 := by
    rw [LinearMap.baseChange_pow, hk]
  let r : (ℂ ⊗[ℝ] V) →ₗ[ℝ] V :=
    (TensorProduct.lid ℝ V).toLinearMap.comp
      (TensorProduct.map Complex.reLm (LinearMap.id : V →ₗ[ℝ] V))
  refine ⟨k, ?_⟩
  ext v
  have hv := LinearMap.congr_fun hz (1 ⊗ₜ[ℝ] v)
  have hr := congrArg r hv
  simpa [r] using hr

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NilpotentMatrixSpanning
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Nilpotence of a matrix representation from spanning generators -/

noncomputable section
namespace PolycyclicRecognition

attribute [local instance 100] LieRing.ofAssociativeRing

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [LieRing.IsNilpotent L] {m : ℕ}

theorem matrix_nilpotent_of_spanning_set
    (j : L →ₗ⁅ℝ⁆ Matrix (Fin m) (Fin m) ℝ) (S : Set L)
    (hS : Submodule.span ℝ S = ⊤) (h : ∀ x ∈ S, IsNilpotent (j x)) (x : L) :
    IsNilpotent (j x) := by
  let E : Matrix (Fin m) (Fin m) ℝ ≃ₐ[ℝ] Module.End ℝ (Fin m → ℝ) := Matrix.toLinAlgEquiv'
  let k : L →ₗ⁅ℝ⁆ Module.End ℝ (Fin m → ℝ) := E.toLieEquiv.toLieHom.comp j
  let := LieRingModule.compLieHom (Fin m → ℝ) k
  let := LieModule.compLieHom (Fin m → ℝ) k
  have hk (y : L) (hy : y ∈ S) : IsNilpotent (LieModule.toEnd ℝ L (Fin m → ℝ) y) :=
    (h y hy).map E.toRingHom
  obtain ⟨c, hc⟩ := real_nilpotent_operators_of_spanning_set S hS hk x
  refine ⟨c, E.injective ?_⟩
  rw [map_pow, map_zero]
  exact hc

theorem matrix_products_vanish_of_spanning_nilpotents
    (j : L →ₗ⁅ℝ⁆ Matrix (Fin m) (Fin m) ℝ) (S : Set L)
    (hS : Submodule.span ℝ S = ⊤) (h : ∀ x ∈ S, IsNilpotent (j x)) :
    ∃ c : ℕ, ∀ l : List L, c ≤ l.length → (l.map j).prod = 0 :=
  exists_vanishing_matrix_products_of_pointwise_nilpotent j
    (matrix_nilpotent_of_spanning_set j S hS h)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_WeightedWordSubstitution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Substitution in a nilpotent associative algebra -/

noncomputable section
namespace PolycyclicRecognition

variable {A : Type*} [Ring A] [Algebra ℚ A] {c n : ℕ} (X : Fin n → A)

def weightedWordSubstitution : TruncatedWords c n →ₗ[ℚ] A :=
  (Finsupp.lsum ℚ (fun w : FreeMonoid (Fin n) =>
    (truncatedScalarCoefficient c w.length).smulRight (FreeMonoid.lift X w))).comp
      (MonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap

theorem weightedWordSubstitution_single (w : FreeMonoid (Fin n))
    (a : TruncatedRationalScalars c) :
    weightedWordSubstitution X (MonoidAlgebra.single w a) =
      truncatedScalarCoefficient c w.length a • FreeMonoid.lift X w := by
  change Finsupp.lsum ℚ _ (Finsupp.single w a) = _
  rw [Finsupp.lsum_single]
  rfl

theorem weightedWordSubstitution_weightedWord
    (hX : ∀ w : FreeMonoid (Fin n), c < w.length → FreeMonoid.lift X w = 0)
    (w : FreeMonoid (Fin n)) :
    weightedWordSubstitution X (weightedWord c n w) = FreeMonoid.lift X w := by
  rw [weightedWord, weightedWordSubstitution_single]
  by_cases hw : w.length ≤ c
  · rw [truncatedScalarCoefficient_parameter_pow c w.length w.length hw]
    simp
  · rw [hX w (Nat.lt_of_not_ge hw), smul_zero]

theorem weightedWordSubstitution_mul
    (hX : ∀ w : FreeMonoid (Fin n), c < w.length → FreeMonoid.lift X w = 0)
    {p q : TruncatedWords c n} (hp : p ∈ weightedWordSpan c n) (hq : q ∈ weightedWordSpan c n) :
    weightedWordSubstitution X (p * q) =
      weightedWordSubstitution X p * weightedWordSubstitution X q := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨u, rfl⟩ := hp
    induction hq using Submodule.span_induction with
    | mem q hq =>
      obtain ⟨v, rfl⟩ := hq
      rw [← weightedWord_mul, weightedWordSubstitution_weightedWord X hX,
        weightedWordSubstitution_weightedWord X hX, weightedWordSubstitution_weightedWord X hX,
        map_mul]
    | zero => simp
    | add q r _ _ hq hr => simp only [mul_add, map_add, hq, hr]
    | smul a q _ hq => simp only [Algebra.mul_smul_comm, map_smul, hq]
  | zero => simp
  | add p r _ _ hp hr => simp only [add_mul, map_add, hp, hr]
  | smul a p _ hp => simp only [smul_mul_assoc, map_smul, hp]

theorem weightedWordSubstitution_one
    (hX : ∀ w : FreeMonoid (Fin n), c < w.length → FreeMonoid.lift X w = 0) :
    weightedWordSubstitution X (1 : TruncatedWords c n) = 1 := by
  rw [← weightedWord_one c n, weightedWordSubstitution_weightedWord X hX, map_one]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NilpotentWordEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exponential and logarithm identities under nilpotent substitution -/

noncomputable section
namespace PolycyclicRecognition

variable {A : Type*} [Ring A] [Algebra ℚ A] {c n : ℕ} (X : Fin n → A)
  (hX : ∀ w : FreeMonoid (Fin n), c < w.length → FreeMonoid.lift X w = 0)

include hX

omit [Algebra ℚ A] in
theorem nilpotent_word_letter_pow (i : Fin n) : X i ^ (c + 1) = 0 := by
  have hlen (k : ℕ) : (FreeMonoid.of i ^ k).length = k := by
    induction k with
    | zero => simp
    | succ k hk => simp only [pow_succ, FreeMonoid.length_mul, FreeMonoid.length_of, hk]
  have h := hX (FreeMonoid.of i ^ (c + 1)) (by rw [hlen]; omega)
  simpa using h

theorem weightedWordSubstitution_pow {a : TruncatedWords c n}
    (ha : a ∈ weightedWordSubalgebra c n) (k : ℕ) :
    weightedWordSubstitution X (a ^ k) = weightedWordSubstitution X a ^ k := by
  induction k with
  | zero => simpa only [pow_zero] using weightedWordSubstitution_one X hX
  | succ k hk =>
    rw [pow_succ a k, weightedWordSubstitution_mul X hX
      ((weightedWordSubalgebra c n).pow_mem ha k) ha, hk,
      pow_succ (weightedWordSubstitution X a) k]

theorem weightedWordSubstitution_aeval {a : TruncatedWords c n}
    (ha : a ∈ weightedWordSubalgebra c n) (p : Polynomial ℚ) :
    weightedWordSubstitution X (Polynomial.aeval a p) =
      Polynomial.aeval (weightedWordSubstitution X a) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | monomial k q =>
    simp only [Polynomial.aeval_monomial, ← Algebra.smul_def, map_smul,
      weightedWordSubstitution_pow X hX ha]

theorem weightedWordSubstitution_parameter_letter (i : Fin n) :
    weightedWordSubstitution X (truncatedScalarParameter c • truncatedWordLetter c n i) = X i := by
  have h : truncatedScalarParameter c • truncatedWordLetter c n i =
      weightedWord c n (FreeMonoid.of i) := by
    simp [truncatedWordLetter, weightedWord, FreeMonoid.length]
  rw [h, weightedWordSubstitution_weightedWord X hX]
  simp

theorem weightedWordSubstitution_list_prod (L : List (TruncatedWords c n))
    (hL : ∀ a ∈ L, a ∈ weightedWordSubalgebra c n) :
    weightedWordSubstitution X L.prod = (L.map (weightedWordSubstitution X)).prod := by
  induction L with
  | nil => exact weightedWordSubstitution_one X hX
  | cons a L ih =>
    have ht : ∀ b ∈ L, b ∈ weightedWordSubalgebra c n :=
      fun b hb => hL b (List.mem_cons_of_mem a hb)
    rw [List.prod_cons, List.map_cons, List.prod_cons,
      weightedWordSubstitution_mul X hX (hL a (List.mem_cons_self ..))
        ((weightedWordSubalgebra c n).toSubmonoid.list_prod_mem ht), ih ht]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RationalUniversalLogarithm
attribute [-simp] _root_.OAI.PolycyclicRecognition.rationalWordAntipode_one _root_.OAI.PolycyclicRecognition.rationalWordDegree_one _root_.OAI.PolycyclicRecognition.wordAntipodeConvolution_tmul _root_.OAI.PolycyclicRecognition.wordDegreeConvolution_tmul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The rational polynomial underlying the universal truncated logarithm -/

noncomputable section
namespace PolycyclicRecognition

variable (c n : ℕ)

def weightedWordHom : FreeMonoid (Fin n) →* TruncatedWords c n where
  toFun := weightedWord c n
  map_one' := weightedWord_one c n
  map_mul' := weightedWord_mul c n

def rationalWordWeight : RationalWords n →ₐ[ℚ] TruncatedWords c n :=
  MonoidAlgebra.lift ℚ _ _ (weightedWordHom c n)

theorem rationalWordWeight_single (w : FreeMonoid (Fin n)) (q : ℚ) :
    rationalWordWeight c n (MonoidAlgebra.single w q) = q • weightedWord c n w := by
  rw [rationalWordWeight, MonoidAlgebra.lift_single]
  rfl

theorem rationalWordWeight_letter (i : Fin n) :
    rationalWordWeight c n (rationalWordLetter i) =
      truncatedScalarParameter c • truncatedWordLetter c n i := by
  rw [rationalWordLetter, rationalWordWeight_single, one_smul]
  simp [weightedWord, FreeMonoid.length, truncatedWordLetter]

def rationalWordExponential (i : Fin n) : RationalWords n :=
  Polynomial.aeval (rationalWordLetter i) (PowerSeries.trunc (c + 1) (PowerSeries.exp ℚ))

def rationalExponentialProduct : RationalWords n :=
  (List.ofFn (rationalWordExponential c n)).prod

def rationalUniversalLogarithm : RationalWords n :=
  finiteNilpotentLog (c + 1) (rationalExponentialProduct c n - 1)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_WeightedWordComponents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Explicit degree components of weighted words -/

noncomputable section
namespace PolycyclicRecognition

variable {c n d : ℕ}

theorem weightedWord_coefficient (w : FreeMonoid (Fin n)) (hd : d ≤ c) :
    monoidCoefficientLinear (truncatedScalarCoefficient c d) (weightedWord c n w) =
      if w.length = d then MonoidAlgebra.single w 1 else 0 := by
  rw [weightedWord, monoidCoefficientLinear_single]
  by_cases hw : w.length ≤ c
  · rw [truncatedScalarCoefficient_parameter_pow c w.length d hw]
    split_ifs <;> simp
  · have hz : truncatedScalarParameter c ^ w.length = 0 :=
      pow_eq_zero_of_le (Nat.lt_of_not_ge hw) (truncatedScalarParameter_pow c)
    have hwd : w.length ≠ d := by omega
    rw [hz, map_zero, MonoidAlgebra.single_zero, ite_eq_right hwd]

theorem homogeneous_degree_zero_eq_single {p : RationalWords n}
    (hp : IsHomogeneousRationalWord p 0) : p = MonoidAlgebra.single 1 (p.coeff 1) := by
  classical
  ext w
  by_cases hw : w = 1
  · subst w; simp
  · have hz : p.coeff w = 0 := by
      by_contra h
      have hlen := hp w h
      have hlist : w.toList = [] := List.length_eq_zero_iff.mp hlen
      exact hw (FreeMonoid.toList.injective hlist)
    simp [hz, MonoidAlgebra.coeff_single, hw]

theorem primitive_homogeneous_degree_zero {p : RationalWords n}
    (hp : IsPrimitiveRationalWord p) (hd : IsHomogeneousRationalWord p 0) : p = 0 := by
  have he := homogeneous_degree_zero_eq_single hd
  have h := congrArg (monoidTensorCoordinates ℚ (FreeMonoid (Fin n)) (FreeMonoid (Fin n))) hp
  rw [← pairedWordCoproduct_eq_rational, map_add, monoidTensorCoordinates_tmul_one,
    monoidTensorCoordinates_one_tmul] at h
  rw [he] at h
  have hc := congrArg (fun q => q.coeff (1, 1)) h
  simp [pairedWordCoproduct, MonoidAlgebra.lift_single, FreeMonoid.lift_apply,
    MonoidAlgebra.one_def, smul_eq_mul] at hc
  have hs : (Finsupp.single (1 : FreeMonoid (Fin n) × FreeMonoid (Fin n))
      (p.coeff 1)) (1, 1) = p.coeff 1 := Finsupp.single_eq_same
  rw [hs] at hc
  have hq : p.coeff 1 = 0 := add_eq_left.mp hc.symm
  rw [he, hq]
  exact MonoidAlgebra.single_zero _

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_UniversalLogarithmWordCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rational coefficients of the universal logarithm -/

noncomputable section
namespace PolycyclicRecognition

variable {c n d : ℕ}

theorem rationalWordWeight_coefficient (p : RationalWords n) (hd : d ≤ c)
    (w : FreeMonoid (Fin n)) :
    (monoidCoefficientLinear (truncatedScalarCoefficient c d) (rationalWordWeight c n p)).coeff w =
      if w.length = d then p.coeff w else 0 := by
  induction p using MonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq =>
    simp only [map_add, MonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hq]
    split_ifs <;> simp
  | single v q =>
    rw [rationalWordWeight_single, map_smul, weightedWord_coefficient v hd]
    by_cases hvw : v = w
    · subst v
      by_cases hw : w.length = d <;> simp [hw]
    · by_cases hv : v.length = d <;> simp [hv, MonoidAlgebra.coeff_single, hvw]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RationalWordTruncationEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Evaluation through finitely many homogeneous word degrees -/

noncomputable section
namespace PolycyclicRecognition

open scoped BigOperators

variable {A : Type*} [Ring A] [Algebra ℚ A] {c n : ℕ} (X : Fin n → A)

theorem rationalWordWeight_single_component (w : FreeMonoid (Fin n)) (q : ℚ) (d : ℕ)
    (hd : d ≤ c) :
    monoidCoefficientLinear (truncatedScalarCoefficient c d)
      (rationalWordWeight c n (MonoidAlgebra.single w q)) =
      if w.length = d then MonoidAlgebra.single w q else 0 := by
  rw [rationalWordWeight_single, map_smul, weightedWord_coefficient w hd]
  split_ifs <;> simp [MonoidAlgebra.smul_single, smul_eq_mul]

theorem rationalWord_evaluation_by_degrees
    (hX : ∀ w : FreeMonoid (Fin n), c < w.length → FreeMonoid.lift X w = 0)
    (p : RationalWords n) :
    rationalWordEvaluation X p = ∑ d : Fin (c + 1), rationalWordEvaluation X
      (monoidCoefficientLinear (truncatedScalarCoefficient c d.val) (rationalWordWeight c n p)) := by
  classical
  induction p using MonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, Finset.sum_add_distrib, hp, hq]
  | single w q =>
    have hd (d : Fin (c + 1)) : rationalWordEvaluation X
        (monoidCoefficientLinear (truncatedScalarCoefficient c d.val)
          (rationalWordWeight c n (MonoidAlgebra.single w q))) =
        if w.length = d.val then q • FreeMonoid.lift X w else 0 := by
      rw [rationalWordWeight_single_component w q d.val (Nat.le_of_lt_succ d.isLt)]
      split_ifs <;> simp only [rationalWordEvaluation_single, ← FreeMonoid.lift_apply, map_zero]
    rw [rationalWordEvaluation_single, ← FreeMonoid.lift_apply]
    simp_rw [hd]
    by_cases hw : w.length ≤ c
    · let k : Fin (c + 1) := ⟨w.length, Nat.lt_succ_of_le hw⟩
      have hk (d : Fin (c + 1)) : w.length = d.val ↔ d = k := by
        constructor
        · intro h; exact Fin.ext h.symm
        · intro h; subst d; rfl
      simp_rw [hk]
      simp
    · have hne (d : Fin (c + 1)) : w.length ≠ d.val := by omega
      simp only [hne, ite_false, if_false, Finset.sum_const_zero, hX w (Nat.lt_of_not_ge hw), smul_zero]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NilpotentUniversalLogarithm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The universal logarithm evaluates to the actual finite logarithm -/

noncomputable section
namespace PolycyclicRecognition

variable {A : Type*} [Ring A] [Algebra ℚ A] {c n : ℕ} (X : Fin n → A)
  (hX : ∀ w : FreeMonoid (Fin n), c < w.length → FreeMonoid.lift X w = 0)

include hX

theorem weightedWordSubstitution_weight (p : RationalWords n) :
    weightedWordSubstitution X (rationalWordWeight c n p) = rationalWordEvaluation X p := by
  induction p using MonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | single w q =>
    rw [rationalWordWeight_single, map_smul, weightedWordSubstitution_weightedWord X hX,
      rationalWordEvaluation_single, FreeMonoid.lift_apply]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_OrderedCentralWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Ordered integral coordinates and their central collection factor -/

namespace PolycyclicRecognition
open scoped commutatorElement
variable {G A : Type*} [Group G] [CommGroup A] {d : ℕ}

def orderedWord (a : Fin d → G) (x : Fin d → ℤ) : G :=
  (List.ofFn (fun i => a i ^ x i)).prod

@[simp] theorem orderedWord_zero (a : Fin d → G) : orderedWord a 0 = 1 := by
  simp [orderedWord]

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ChartContraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Controlled contraction from locally Lipschitz exponential coordinates

This is the elementary metric bridge in the replacement construction. The
local metric compatibility of a chosen Lie chart is an explicit premise here;
it does not follow from a merely topological exponential chart.
-/

noncomputable section
namespace PolycyclicRecognition

open Set Metric

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [ProperSpace E] [MetricSpace G] [ProperSpace G] [One G]

def chartContraction (φ : E ≃ₜ G) (s : ℝ) (z : G) : G := φ (s • φ.symm z)

omit [ProperSpace E] [ProperSpace G] in
@[simp] theorem chartContraction_zero (φ : E ≃ₜ G) (hφ : φ 0 = 1) (z : G) :
    chartContraction φ 0 z = 1 := by simp [chartContraction, hφ]

omit [ProperSpace E] [ProperSpace G] [One G] in
@[simp] theorem chartContraction_one (φ : E ≃ₜ G) (z : G) :
    chartContraction φ 1 z = z := by simp [chartContraction]

/-- On a fixed metric ball, radial contraction has a uniform time bound
and a spatial bound proportional to the radial parameter. -/
theorem chartContraction_bounds (φ : E ≃ₜ G) (hφ : φ 0 = 1)
    (hforward : LocallyLipschitz φ) (hbackward : LocallyLipschitz φ.symm)
    {R : ℝ} (hR : 0 ≤ R) :
    ∃ C : ℝ, 1 ≤ C ∧
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        ∀ z ∈ closedBall (1 : G) R,
        dist (chartContraction φ s z) (chartContraction φ t z) ≤ C * |s - t|) ∧
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ z ∈ closedBall (1 : G) R,
        ∀ w ∈ closedBall (1 : G) R,
        dist (chartContraction φ s z) (chartContraction φ s w) ≤ C * s * dist z w) := by
  obtain ⟨L, hL⟩ := hbackward.locallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (isCompact_closedBall (1 : G) R)
  have hinv : φ.symm 1 = 0 := by rw [← hφ, φ.symm_apply_apply]
  have hlog (z : G) (hz : z ∈ closedBall (1 : G) R) : ‖φ.symm z‖ ≤ L * R := by
    have h := hL.dist_le_mul z hz 1 (mem_closedBall_self hR)
    rw [hinv, dist_zero_right] at h
    exact h.trans (mul_le_mul_of_nonneg_left hz L.2)
  have hB : 0 ≤ (L : ℝ) * R := mul_nonneg L.2 hR
  obtain ⟨P, hP⟩ := hforward.locallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (isCompact_closedBall (0 : E) ((L : ℝ) * R))
  have hscaled (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (z : G)
      (hz : z ∈ closedBall (1 : G) R) : s • φ.symm z ∈ closedBall (0 : E) ((L : ℝ) * R) := by
    rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
    exact (mul_le_mul_of_nonneg_left (hlog z hz) hs.1).trans
      (mul_le_of_le_one_left hB hs.2)
  let C : ℝ := 1 + (P : ℝ) * ((L : ℝ) * R + L)
  have hCt : (P : ℝ) * ((L : ℝ) * R) ≤ C := by dsimp [C] <;> nlinarith [P.2, L.2]
  have hCs : (P : ℝ) * L ≤ C := by dsimp [C] <;> nlinarith [P.2, hB]
  refine ⟨C, by dsimp [C]; exact le_add_of_nonneg_right (mul_nonneg P.2 (add_nonneg hB L.2)), ?_, ?_⟩
  · intro s hs t ht z hz
    have h := hP.dist_le_mul _ (hscaled s hs z hz) _ (hscaled t ht z hz)
    have he : dist (s • φ.symm z) (t • φ.symm z) = |s - t| * ‖φ.symm z‖ := by
      rw [dist_eq_norm, ← sub_smul, norm_smul, Real.norm_eq_abs]
    rw [he] at h
    calc
      _ ≤ (P : ℝ) * (|s - t| * ‖φ.symm z‖) := h
      _ ≤ (P : ℝ) * (|s - t| * ((L : ℝ) * R)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hlog z hz) (abs_nonneg _)) P.2
      _ ≤ C * |s - t| := by nlinarith only [mul_le_mul_of_nonneg_right hCt (abs_nonneg (s - t))]
  · intro s hs z hz w hw
    have h := hP.dist_le_mul _ (hscaled s hs z hz) _ (hscaled s hs w hw)
    have he : dist (s • φ.symm z) (s • φ.symm w) = s * dist (φ.symm z) (φ.symm w) := by
      rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1, dist_eq_norm]
    rw [he] at h
    calc
      _ ≤ (P : ℝ) * (s * dist (φ.symm z) (φ.symm w)) := h
      _ ≤ (P : ℝ) * (s * ((L : ℝ) * dist z w)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hL.dist_le_mul z hz w hw) hs.1) P.2
      _ ≤ C * s * dist z w := by
        nlinarith only [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCs hs.1) (dist_nonneg (x := z) (y := w))]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ControlledContraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform contractions about arbitrary centers -/

noncomputable section
namespace PolycyclicRecognition

open Set Metric

variable (G : Type*) [MetricSpace G]

/-- The quantitative contraction data used by the interpolation algorithm.
It is constructed from coordinates below, rather than assumed to supply
a quasi-isometry representative. -/
structure ControlledContraction where
  contract : G → ℝ → G → G
  zero : ∀ p z, contract p 0 z = p
  one : ∀ p z, contract p 1 z = z
  bounds : ∀ R : ℝ, 0 ≤ R → ∃ C : ℝ, 1 ≤ C ∧
    ∀ p z w : G, dist z p ≤ R → dist w p ≤ R →
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      dist (contract p s z) (contract p t w) ≤
        C * (|s - t| + min s t * dist z w)

namespace ControlledContraction

variable {G}

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [ProperSpace E] [Group G] [ProperSpace G] [IsIsometricSMul G G]

/-- Left translation of radial contraction makes the same constants work
about every center of a left-invariant metric. -/
def ofChart (φ : E ≃ₜ G) (hφ : φ 0 = 1)
    (hf : LocallyLipschitz φ) (hb : LocallyLipschitz φ.symm) : ControlledContraction G where
  contract p s z := p * chartContraction φ s (p⁻¹ * z)
  zero p z := by simp [hφ]
  one p z := by simp
  bounds R hR := by
    obtain ⟨C, hC, htime, hspace⟩ := chartContraction_bounds φ hφ hf hb hR
    refine ⟨C, hC, ?_⟩
    intro p z w hz hw s hs t ht
    have hzp : p⁻¹ * z ∈ closedBall (1 : G) R := by
      change dist (p⁻¹ * z) 1 ≤ R
      calc
        _ = dist z p := by simpa using dist_mul_left p⁻¹ z p
        _ ≤ R := hz
    have hwp : p⁻¹ * w ∈ closedBall (1 : G) R := by
      change dist (p⁻¹ * w) 1 ≤ R
      calc
        _ = dist w p := by simpa using dist_mul_left p⁻¹ w p
        _ ≤ R := hw
    rw [dist_mul_left]
    rcases le_total s t with hst | hts
    · have h₁ := hspace s hs _ hzp _ hwp
      have h₂ := htime s hs t ht _ hwp
      rw [dist_mul_left] at h₁
      have h := dist_triangle (chartContraction φ s (p⁻¹ * z))
        (chartContraction φ s (p⁻¹ * w)) (chartContraction φ t (p⁻¹ * w))
      rw [min_eq_left hst]
      linarith
    · have h₁ := htime s hs t ht _ hzp
      have h₂ := hspace t ht _ hzp _ hwp
      rw [dist_mul_left] at h₂
      have h := dist_triangle (chartContraction φ s (p⁻¹ * z))
        (chartContraction φ t (p⁻¹ * z)) (chartContraction φ t (p⁻¹ * w))
      rw [min_eq_right hts]
      linarith

end ControlledContraction
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_OrderedInterpolation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Ordered interpolation of finitely many nonnegative masses

Zero masses can be omitted. Thus one fixed order on the net gives compatible
interpolations on different finite supports without a simplicial-complex API.
-/

noncomputable section
namespace PolycyclicRecognition

variable {I G : Type*} [MetricSpace G]

def listMass (a : I → ℝ) : List I → ℝ
  | [] => 0
  | i :: l => a i + listMass a l

def listVariation (a b : I → ℝ) (l : List I) : ℝ :=
  listMass (fun i => |a i - b i|) l

def orderedCenter (c : ControlledContraction G) (p₀ : G) (v : I → G) (a : I → ℝ) : List I → G
  | [] => p₀
  | i :: l => c.contract (v i) (listMass a l / listMass a (i :: l)) (orderedCenter c p₀ v a l)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_OrderedInterpolationRadius
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform radius of interpolation on a bounded number of vertices -/

namespace PolycyclicRecognition

variable {I G : Type*} [MetricSpace G]

def InterpolationRadius (c : ControlledContraction G) (D : ℝ) (n : ℕ) (R : ℝ) : Prop :=
  ∀ (l : List I) (p₀ : G) (v : I → G) (a : I → ℝ),
    l ≠ [] → l.length ≤ n → (∀ i ∈ l, 0 ≤ a i) →
    (∀ i ∈ l, ∀ j ∈ l, dist (v i) (v j) ≤ D) →
    ∀ p : G, (∀ i ∈ l, dist (v i) p ≤ D) → dist (orderedCenter c p₀ v a l) p ≤ R

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_OrderedPowerWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Unique ordered products of powers of distinct letters -/

noncomputable section
namespace PolycyclicRecognition

open scoped BigOperators

variable {I : Type*} [DecidableEq I] {n : ℕ}

def wordLetterCount (a : I) (w : FreeMonoid I) : ℕ :=
  (FreeMonoid.lift (fun b => Multiplicative.ofAdd (if b = a then (1 : ℕ) else 0)) w).toAdd

def orderedPowerWord (f : Fin n → I) (k : Fin n → ℕ) : FreeMonoid I :=
  (List.ofFn (fun i => FreeMonoid.of (f i) ^ k i)).prod

theorem wordLetterCount_orderedPowerWord (f : Fin n → I) (hf : Function.Injective f)
    (k : Fin n → ℕ) (j : Fin n) : wordLetterCount (f j) (orderedPowerWord f k) = k j := by
  simp only [wordLetterCount, orderedPowerWord, map_list_prod, List.map_ofFn, Function.comp_def,
    List.prod_ofFn, toAdd_prod, map_pow, FreeMonoid.lift_eval_of,
    toAdd_pow, toAdd_ofAdd, hf.eq_iff]
  simp

theorem orderedPowerWord_injective (f : Fin n → I) (hf : Function.Injective f) :
    Function.Injective (orderedPowerWord f) := by
  intro k l h
  funext j
  have hc := congrArg (wordLetterCount (f j)) h
  simpa only [wordLetterCount_orderedPowerWord f hf] using hc

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_OrderedProductSums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Expanding a finite ordered product of finite sums -/

noncomputable section
namespace PolycyclicRecognition

open scoped BigOperators

theorem ordered_product_sums {A J : Type*} [Semiring A] [Fintype J]
    {n : ℕ} (a : Fin n → J → A) :
    (List.ofFn (fun i => ∑ j, a i j)).prod =
      ∑ k : Fin n → J, (List.ofFn (fun i => a i (k i))).prod := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.prod_cons, ih, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    symm
    calc
      _ = ∑ p : J × (Fin n → J),
          (List.ofFn (fun i => a i ((Fin.consEquiv (fun _ : Fin (n + 1) => J)) p i))).prod :=
        (Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n + 1) => J))
          (fun k => (List.ofFn (fun i => a i (k i))).prod)).symm
      _ = _ := by simp [Fintype.sum_prod_type, List.ofFn_succ]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_FiniteCoordinateSmoothness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Smoothness in a finite-dimensional space of functions

Point evaluations span the dual of a finite-dimensional function space.
Consequently scalar pointwise smoothness detects smoothness into that space.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped ContDiff

variable {G V X : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [NormedAddCommGroup X] [NormedSpace ℝ X]
  (e : V →ₗ[ℝ] (G → ℝ))

def coordinateEvaluation (g : G) : Module.Dual ℝ V where
  toFun v := e v g
  map_add' v w := by simp
  map_smul' a v := by simp

theorem span_coordinateEvaluation (he : Function.Injective e) :
    Submodule.span ℝ (Set.range (coordinateEvaluation e)) = ⊤ := by
  let S := Submodule.span ℝ (Set.range (coordinateEvaluation e))
  have hS : S.dualCoannihilator = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro v hv
    change v = 0
    apply he
    ext g
    have h := ((Submodule.mem_dualCoannihilator v).mp hv) (coordinateEvaluation e g)
      (Submodule.subset_span (Set.mem_range_self g))
    simpa only [coordinateEvaluation, LinearMap.coe_mk, AddHom.coe_mk, map_zero,
      Pi.zero_apply] using h
  calc
    S = S.dualCoannihilator.dualAnnihilator :=
      Subspace.dualCoannihilator_dualAnnihilator_eq.symm
    _ = ⊤ := by rw [hS, Submodule.dualAnnihilator_bot]

theorem contDiff_of_coordinateEvaluations (he : Function.Injective e)
    {r : ℕ∞ω} {F : X → V} (hF : ∀ g, ContDiff ℝ r (fun x => e (F x) g)) :
    ContDiff ℝ r F := by
  have hlin (f : Module.Dual ℝ V) : ContDiff ℝ r (fun x => f (F x)) := by
    have hf : f ∈ Submodule.span ℝ (Set.range (coordinateEvaluation e)) := by
      rw [span_coordinateEvaluation e he]
      trivial
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨g, rfl⟩ := hf
      exact hF g
    | zero => exact contDiff_const
    | add f g _ _ hf hg => exact hf.add hg
    | smul a f _ hf => exact hf.const_smul a
  let b := Module.finBasis ℝ V
  let E := b.equivFun.toContinuousLinearEquiv
  have hc : ContDiff ℝ r (fun x => E (F x)) := by
    apply contDiff_pi.mpr
    intro i
    exact hlin ((LinearMap.proj i).comp b.equivFun.toLinearMap)
  have hh := E.symm.contDiff.comp hc
  simpa only [Function.comp_def, ContinuousLinearEquiv.symm_apply_apply] using hh

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialCoordinateEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial maps detected by point evaluations

A finite-dimensional function space is separated by evaluations. Their span
is the whole dual, so polynomiality at every point gives polynomial coordinates.
-/

noncomputable section
namespace PolycyclicRecognition

def multivariatePolynomialEvaluation (I : Type*) :
    MvPolynomial I ℝ →ₗ[ℝ] ((I → ℝ) → ℝ) where
  toFun p x := MvPolynomial.eval x p
  map_add' p q := by ext x; exact map_add _ p q
  map_smul' a p := by
    ext x
    change MvPolynomial.eval x (a • p) = a * MvPolynomial.eval x p
    rw [Algebra.smul_def, MvPolynomial.algebraMap_eq, map_mul, MvPolynomial.eval_C]

def multivariatePolynomialFunctions (I : Type*) :
    Submodule ℝ ((I → ℝ) → ℝ) := (multivariatePolynomialEvaluation I).range

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialCoordinateOrbit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite-dimensional coordinate orbits from polynomial multiplication

The coefficients may be arbitrary functions of the right factor. Only the
finite polynomial dependence on the left coordinates is needed here.
-/

noncomputable section
namespace PolycyclicRecognition

variable {G I : Type*} [Group G] (q : I → G → ℝ)

def coordinateMonomial (d : I →₀ ℕ) : G → ℝ :=
  fun x => ∏ i ∈ d.support, q i x ^ d i

def coordinatePolynomialEvaluation (p : MvPolynomial I (G → ℝ)) (g : G) : G → ℝ :=
  fun x => p.eval₂ (Pi.evalRingHom (fun _ : G => ℝ) g) (fun i => q i x)

omit [Group G] in
theorem coordinatePolynomialEvaluation_eq_sum (p : MvPolynomial I (G → ℝ)) (g : G) :
    coordinatePolynomialEvaluation q p g =
      ∑ d ∈ p.support, (p.coeff d g) • coordinateMonomial q d := by
  classical
  funext x
  rw [coordinatePolynomialEvaluation, MvPolynomial.eval₂_eq]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, coordinateMonomial]
  rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialCoordinateTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The topology carried by an actual polynomial coordinate group -/

noncomputable section

namespace PolycyclicRecognition.PolynomialCoordinateGroup

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

instance instTopologicalSpace (m : V → V → V) (h : PolynomialGroupLaws m) :
    TopologicalSpace (PolynomialCoordinateGroup m h) := inferInstanceAs (TopologicalSpace V)

instance instMeasurableSpace [MeasurableSpace V] (m : V → V → V) (h : PolynomialGroupLaws m) :
    MeasurableSpace (PolynomialCoordinateGroup m h) := inferInstanceAs (MeasurableSpace V)

instance instBorelSpace [MeasurableSpace V] [BorelSpace V] (m : V → V → V) (h : PolynomialGroupLaws m) :
    BorelSpace (PolynomialCoordinateGroup m h) := inferInstanceAs (BorelSpace V)

def expHomeomorph (m : V → V → V) (h : PolynomialGroupLaws m) :
    V ≃ₜ PolynomialCoordinateGroup m h where
  toEquiv := exp m h
  continuous_toFun := continuous_id
  continuous_invFun := continuous_id

end PolycyclicRecognition.PolynomialCoordinateGroup

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialFunctionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The space of real polynomial functions -/

noncomputable section
namespace PolycyclicRecognition

def polynomialEvaluationLinear : Polynomial ℝ →ₗ[ℝ] (ℝ → ℝ) where
  toFun p t := p.eval t
  map_add' p q := by ext t; exact Polynomial.eval_add
  map_smul' a p := by ext t; exact Polynomial.eval_smul a p t

def polynomialFunctions : Submodule ℝ (ℝ → ℝ) := polynomialEvaluationLinear.range

theorem mem_polynomialFunctions_iff {f : ℝ → ℝ} :
    f ∈ polynomialFunctions ↔ ∃ p : Polynomial ℝ, ∀ t, p.eval t = f t := by
  change (∃ p, polynomialEvaluationLinear p = f) ↔ _
  simp only [funext_iff]
  rfl

theorem polynomialFunctions_const (a : ℝ) : (fun _ : ℝ => a) ∈ polynomialFunctions :=
  mem_polynomialFunctions_iff.mpr ⟨Polynomial.C a, fun _ => Polynomial.eval_C⟩

theorem polynomialFunctions_linear (a : ℝ) : (fun t : ℝ => t * a) ∈ polynomialFunctions :=
  mem_polynomialFunctions_iff.mpr ⟨Polynomial.X * Polynomial.C a, by
    intro t
    rw [Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]⟩

variable {G V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

theorem polynomial_of_coordinateEvaluations (e : V →ₗ[ℝ] (G → ℝ))
    (he : Function.Injective e) (F : ℝ → V)
    (hF : ∀ g, (fun t => e (F t) g) ∈ polynomialFunctions)
    (f : Module.Dual ℝ V) : (fun t => f (F t)) ∈ polynomialFunctions := by
  have hf : f ∈ Submodule.span ℝ (Set.range (coordinateEvaluation e)) := by
    rw [span_coordinateEvaluation e he]
    trivial
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨g, rfl⟩ := hf
    exact hF g
  | zero => exact polynomialFunctions.zero_mem
  | add f g _ _ hf hg => exact polynomialFunctions.add_mem hf hg
  | smul a f _ hf => exact polynomialFunctions.smul_mem a hf

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ExponentialTangentUniqueness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Recovering tangent vectors from exponential curves -/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]

omit [LieGroup (𝓘(ℝ, E)) ⊤ G] in
theorem IsGroupExponential.eq_of_oneParameter_eq
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    {v w : GroupLieAlgebra (𝓘(ℝ, E)) G}
    (h : ∀ t : ℝ, Exp (t • v) = Exp (t • w)) : v = w := by
  have hw := hExp.hasMFDerivAt_zero w
  rw [← funext h] at hw
  have hd := hasMFDerivAt_unique (hExp.hasMFDerivAt_zero v) hw
  have he := congrArg (fun D : ℝ →L[ℝ] E => D 1) hd
  change (1 : ℝ) • (v : E) = (1 : ℝ) • (w : E) at he
  simpa only [one_smul] using he

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_TranslationLocalHomeomorph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Propagating local coordinates by translations -/

noncomputable section
namespace PolycyclicRecognition

open Set Filter Topology

variable {V G : Type*} [TopologicalSpace V] [Zero V]
  [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  (f : V → G) (L : V → V ≃ₜ V)
  (hL0 : ∀ a, L a 0 = a)
  (hprod : ∀ a x, f (L a x) = f a * f x)
  (hmap : Filter.map f (𝓝 0) = 𝓝 (1 : G))

include L hL0 hprod hmap

theorem map_nhds_of_translations (a : V) : Filter.map f (𝓝 a) = 𝓝 (f a) := by
  have heq : f ∘ L a = (Homeomorph.mulLeft (f a)) ∘ f := funext (hprod a)
  calc
    Filter.map f (𝓝 a) = Filter.map f (Filter.map (L a) (𝓝 0)) := by
      rw [(L a).map_nhds_eq, hL0]
    _ = Filter.map (f ∘ L a) (𝓝 0) := Filter.map_map
    _ = Filter.map (Homeomorph.mulLeft (f a) ∘ f) (𝓝 0) := by rw [heq]
    _ = Filter.map (Homeomorph.mulLeft (f a)) (Filter.map f (𝓝 0)) := Filter.map_map.symm
    _ = 𝓝 (f a) := by rw [hmap, (Homeomorph.mulLeft (f a)).map_nhds_eq]; simp

theorem localHomeomorph_of_translations
    (hinj : ∃ U ∈ 𝓝 (0 : V), InjOn f U) : IsLocalHomeomorph f := by
  have hm := map_nhds_of_translations f L hL0 hprod hmap
  have hc : Continuous f := continuous_iff_continuousAt.mpr fun a => (hm a).le
  have ho : IsOpenMap f := IsOpenMap.of_nhds_le fun a => (hm a).ge
  obtain ⟨U, hU, hi⟩ := hinj
  obtain ⟨W, hWU, hW, h0W⟩ := mem_nhds_iff.mp hU
  apply IsLocalHomeomorph.mk
  intro a
  let S : Set V := L a '' W
  have hS : IsOpen S := (L a).isOpenMap W hW
  have haS : a ∈ S := ⟨0, h0W, hL0 a⟩
  have hiS : InjOn f S := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ he
    apply congrArg (L a)
    apply hi (hWU hx) (hWU hy)
    rw [hprod, hprod] at he
    exact mul_left_cancel he
  let e := OpenPartialHomeomorph.ofContinuousOpen hiS.toPartialEquiv hc.continuousOn ho hS
  exact ⟨e, haS, fun _ _ => rfl⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_TranslationCovering
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A covering from two-sided translation coordinates

A local group parameterization whose left and right translations are global
homeomorphisms is a covering map. No associativity on the parameter space is
needed for this step.
-/

noncomputable section
namespace PolycyclicRecognition

open Set Filter Topology

variable {V G : Type*} [TopologicalSpace V] [Zero V]
  [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  (f : V → G) (R : V → V ≃ₜ V)
  (hR : ∀ a x, f (R a x) = f x * f a)
  (hzero : f 0 = 1) (hf : IsLocalHomeomorph f)
  (hRinv : Continuous (fun p : V × V => (R p.1).symm p.2))
  (hRcont : Continuous (fun p : V × V => R p.1 p.2))

/-- A covering of a simply connected space from a connected space has a
continuous global inverse. -/
def homeomorphOfSimplyConnectedCovering [PreconnectedSpace V]
    [SimplyConnectedSpace G] [LocallyPathConnectedSpace G]
    (cov : IsCoveringMap f) : V ≃ₜ G := by
  let hlift := cov.existsUnique_continuousMap_lifts (ContinuousMap.id G) (f 0) 0 rfl
  let q := Classical.choose hlift
  have hq0 := (Classical.choose_spec hlift).1.1
  have hq := (Classical.choose_spec hlift).1.2
  have hleft : q ∘ f = id := by
    apply cov.eq_of_comp_eq (q.continuous.comp cov.continuous) continuous_id
      (a := 0) (ha := hq0)
    funext x
    exact congrFun hq (f x)
  exact
    { toFun := f
      invFun := q
      left_inv := fun x => congrFun hleft x
      right_inv := fun y => congrFun hq y
      continuous_toFun := cov.continuous
      continuous_invFun := q.continuous }

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_LocalParameterSmoothness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Testing smoothness in local parameters

A smooth parametrization with invertible derivative supplies local smooth
coordinates, by the ordinary inverse function theorem.
-/

noncomputable section
namespace PolycyclicRecognition

open Set Filter Function
open scoped Manifold Topology ContDiff

variable {V E A M : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]

theorem contMDiffAt_of_local_parameterization
    {P : V → M} {x₀ : V} {d : V ≃L[ℝ] E} {f : M → A}
    (hP : ContMDiffAt (𝓘(ℝ, V)) (𝓘(ℝ, E)) ∞ P x₀)
    (hd : HasMFDerivAt (𝓘(ℝ, V)) (𝓘(ℝ, E)) P x₀ d.toContinuousLinearMap)
    (hfP : ContDiffAt ℝ ∞ (f ∘ P) x₀) :
    ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, A)) ∞ f (P x₀) := by
  let φ := extChartAt (𝓘(ℝ, E)) (P x₀)
  let Q : V → E := φ ∘ P
  have hφ : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) ∞ φ (P x₀) :=
    contMDiffAt_extChartAt
  have hQ : ContDiffAt ℝ ∞ Q x₀ := (hφ.comp x₀ hP).contDiffAt
  have hchart : HasMFDerivAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) φ (P x₀)
      (ContinuousLinearMap.id ℝ E) := by
    have hh := hφ.mdifferentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) |>.hasMFDerivAt
    apply hh.congr_mfderiv
    change mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (extChartAt (𝓘(ℝ, E)) (P x₀)) (P x₀) = _
    rw [mfderiv_extChartAt_self]
    rfl
  have hQd : HasFDerivAt Q d.toContinuousLinearMap x₀ := by
    have hh : HasFDerivAt Q ((ContinuousLinearMap.id ℝ E).comp d.toContinuousLinearMap) x₀ :=
      (hchart.comp x₀ hd).hasFDerivAt
    simpa only [ContinuousLinearMap.id_comp] using hh
  let q : E → V := hQ.localInverse hQd (by simp)
  have hq : ContDiffAt ℝ ∞ q (Q x₀) := hQ.to_localInverse hQd (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hq₀ : q (φ (P x₀)) = x₀ := hQ.localInverse_apply_image hQd (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hright : ∀ᶠ y in 𝓝 (Q x₀), Q (q y) = y :=
    (hQ.hasStrictFDerivAt' hQd (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).eventually_right_inverse
  let r : M → V := q ∘ φ
  have hr : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, V)) ∞ r (P x₀) :=
    hq.contMDiffAt.comp (P x₀) hφ
  have hr₀ : r (P x₀) = x₀ := hq₀
  have hPr : ContinuousAt (P ∘ r) (P x₀) :=
    hP.continuousAt.comp_of_eq hr.continuousAt hr₀
  have hsource : ∀ᶠ x in 𝓝 (P x₀), x ∈ φ.source :=
    extChartAt_source_mem_nhds (I := 𝓘(ℝ, E)) (P x₀)
  have hPrsource : ∀ᶠ x in 𝓝 (P x₀), P (r x) ∈ φ.source :=
    hPr.preimage_mem_nhds (by
      rw [show (P ∘ r) (P x₀) = P x₀ from congrArg P hr₀]
      exact extChartAt_source_mem_nhds (I := 𝓘(ℝ, E)) (P x₀))
  have heq : ∀ᶠ x in 𝓝 (P x₀), P (r x) = x := by
    filter_upwards [hsource, hPrsource, hφ.continuousAt.tendsto.eventually hright] with x hx hPx hQx
    exact φ.injOn hPx hx hQx
  have hresult := hfP.contMDiffAt.comp_of_eq hr hr₀
  apply hresult.congr_of_eventuallyEq
  filter_upwards [heq] with x hx
  exact congrArg f hx.symm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_UnitParameterInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Recovering a map from local parameters with identity derivative -/

noncomputable section
namespace PolycyclicRecognition

open Filter
open scoped Manifold Topology ContDiff

variable {V E M : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

theorem regularity_of_unit_parameter
    (P : V → V) (hP : ContDiffAt ℝ ∞ P 0)
    (hd : HasFDerivAt P (ContinuousLinearMap.id ℝ V) 0) (hzero : P 0 = 0)
    (f : V → M) (D : V →L[ℝ] E)
    (hcomp : ContMDiffAt (𝓘(ℝ, V)) (𝓘(ℝ, E)) ∞ (f ∘ P) 0)
    (hdcomp : HasMFDerivAt (𝓘(ℝ, V)) (𝓘(ℝ, E)) (f ∘ P) 0 D) :
    ContMDiffAt (𝓘(ℝ, V)) (𝓘(ℝ, E)) ∞ f 0 ∧
      HasMFDerivAt (𝓘(ℝ, V)) (𝓘(ℝ, E)) f 0 D := by
  let d : V ≃L[ℝ] V := ContinuousLinearEquiv.refl ℝ V
  have hd' : HasFDerivAt P d.toContinuousLinearMap 0 := hd
  let q := hP.localInverse hd' (by simp)
  have hq0 : q 0 = 0 := by
    have hh := hP.localInverse_apply_image hd' (by simp)
    rwa [hzero] at hh
  have hq : ContDiffAt ℝ ∞ q 0 := by
    have hh := hP.to_localInverse hd' (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    rwa [hzero] at hh
  have hqd : HasFDerivAt q (ContinuousLinearMap.id ℝ V) 0 := by
    have hh := (hP.hasStrictFDerivAt' hd' (by simp)).to_localInverse.hasFDerivAt
    simpa only [q, ContDiffAt.localInverse, d, hzero, ContinuousLinearEquiv.refl_symm,
      ContinuousLinearEquiv.coe_refl] using hh
  have hright : ∀ᶠ x in 𝓝 (0 : V), P (q x) = x := by
    have hh := (hP.hasStrictFDerivAt' hd' (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).eventually_right_inverse
    simpa only [q, ContDiffAt.localInverse, d, hzero, ContinuousLinearEquiv.refl_symm,
      ContinuousLinearEquiv.coe_refl] using hh
  have heq : (f ∘ P) ∘ q =ᶠ[𝓝 0] f := hright.mono fun x hx => congrArg f hx
  constructor
  · exact (hcomp.comp_of_eq hq.contMDiffAt hq0).congr_of_eventuallyEq heq.symm
  · have hdcomp' : HasMFDerivAt (𝓘(ℝ, V)) (𝓘(ℝ, E)) (f ∘ P) (q 0) D := by
      rwa [hq0]
    have hh := hdcomp'.comp 0 hqd.hasMFDerivAt
    have hh' : HasMFDerivAt (𝓘(ℝ, V)) (𝓘(ℝ, E)) ((f ∘ P) ∘ q) 0 D :=
      hh.congr_mfderiv (by ext v; rfl)
    exact hh'.congr_of_eventuallyEq heq.symm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_LieProductDifferential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The differential of group multiplication at the identity -/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold

variable {E G F H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
  [TopologicalSpace M] [ChartedSpace H M]

theorem mfderiv_mul_one (v : TangentSpace ((𝓘(ℝ, E)).prod (𝓘(ℝ, E)))
    ((1 : G), (1 : G))) :
    mfderiv ((𝓘(ℝ, E)).prod (𝓘(ℝ, E))) (𝓘(ℝ, E))
      (fun p : G × G => p.1 * p.2) (1, 1) v = v.1 + v.2 := by
  have hmul : MDifferentiableAt ((𝓘(ℝ, E)).prod (𝓘(ℝ, E))) (𝓘(ℝ, E))
      (fun p : G × G => p.1 * p.2) (1, 1) :=
    (contMDiff_mul (I := 𝓘(ℝ, E)) (n := ⊤)).mdifferentiableAt (by simp)
  have hl : (fun z : G => z * 1) = id := funext mul_one
  have hr : (fun z : G => 1 * z) = id := funext one_mul
  have hp := mfderiv_prod_eq_add_apply (v := v) hmul
  have hL : mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun z : G => z * 1) 1 =
      ContinuousLinearMap.id ℝ E := by
    rw [hl, mfderiv_id]
    rfl
  have hR : mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun z : G => 1 * z) 1 =
      ContinuousLinearMap.id ℝ E := by
    rw [hr, mfderiv_id]
    rfl
  let v₁ : E := v.1
  let v₂ : E := v.2
  exact hp.trans (congrArg₂ (fun a b : E => a + b)
    (congrArg (fun l : E →L[ℝ] E => l v₁) hL)
    (congrArg (fun l : E →L[ℝ] E => l v₂) hR))

theorem HasMFDerivAt.mul_at_one {f g : M → G} {x : M}
    {df dg : TangentSpace I x →L[ℝ] E}
    (hf : HasMFDerivAt I (𝓘(ℝ, E)) f x df)
    (hg : HasMFDerivAt I (𝓘(ℝ, E)) g x dg)
    (hf1 : f x = 1) (hg1 : g x = 1) :
    HasMFDerivAt I (𝓘(ℝ, E)) (fun y => f y * g y) x (df + dg) := by
  have hmul : MDifferentiableAt ((𝓘(ℝ, E)).prod (𝓘(ℝ, E))) (𝓘(ℝ, E))
      (fun p : G × G => p.1 * p.2) (f x, g x) :=
    (contMDiff_mul (I := 𝓘(ℝ, E)) (n := ⊤)).mdifferentiableAt (by simp)
  have hh := hmul.hasMFDerivAt.comp x (hf.prodMk hg)
  apply hh.congr_mfderiv
  ext w
  change mfderiv ((𝓘(ℝ, E)).prod (𝓘(ℝ, E))) (𝓘(ℝ, E))
    (fun p : G × G => p.1 * p.2) (f x, g x) (df w, dg w) = df w + dg w
  rw [hf1, hg1]
  exact mfderiv_mul_one _

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_LocalExponentialOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Local injectivity and openness from an invertible manifold derivative -/

noncomputable section
namespace PolycyclicRecognition

open Set Filter
open scoped Manifold Topology ContDiff

variable {V E M : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]

theorem locally_injective_open_of_mfderiv_equiv
    {f : V → M} {x : V} (d : V ≃L[ℝ] E)
    (hf : ContMDiffAt (𝓘(ℝ, V)) (𝓘(ℝ, E)) ∞ f x)
    (hd : HasMFDerivAt (𝓘(ℝ, V)) (𝓘(ℝ, E)) f x d.toContinuousLinearMap) :
    (∃ U ∈ 𝓝 x, InjOn f U) ∧ Filter.map f (𝓝 x) = 𝓝 (f x) := by
  let φ := extChartAt (𝓘(ℝ, E)) (f x)
  let Q := φ ∘ f
  have hφ : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) ∞ φ (f x) :=
    contMDiffAt_extChartAt
  have hQ : ContDiffAt ℝ ∞ Q x := (hφ.comp x hf).contDiffAt
  have hφd : HasMFDerivAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) φ (f x)
      (ContinuousLinearMap.id ℝ E) := by
    apply (hφ.mdifferentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasMFDerivAt.congr_mfderiv
    rw [mfderiv_extChartAt_self]
    rfl
  have hQd : HasFDerivAt Q d.toContinuousLinearMap x := by
    have hh : HasFDerivAt Q ((ContinuousLinearMap.id ℝ E).comp d.toContinuousLinearMap) x :=
      (hφd.comp x hd).hasFDerivAt
    simpa only [ContinuousLinearMap.id_comp] using hh
  have hstrict := hQ.hasStrictFDerivAt' hQd (by simp)
  let e := hstrict.toOpenPartialHomeomorph Q
  have hx : x ∈ e.source := hstrict.mem_toOpenPartialHomeomorph_source
  constructor
  · refine ⟨e.source, e.open_source.mem_nhds hx, ?_⟩
    intro a ha b hb hab
    apply e.injOn ha hb
    exact congrArg φ hab
  · have hQmap : Filter.map Q (𝓝 x) = 𝓝 (Q x) :=
      hstrict.map_nhds_eq_of_surj (LinearMap.range_eq_top.mpr d.surjective)
    have hsource : ∀ᶠ y in 𝓝 x, f y ∈ φ.source :=
      hf.continuousAt.preimage_mem_nhds (extChartAt_source_mem_nhds (I := 𝓘(ℝ, E)) (f x))
    have hcomp : φ.symm ∘ Q =ᶠ[𝓝 x] f := hsource.mono fun y hy => φ.left_inv hy
    calc
      Filter.map f (𝓝 x) = Filter.map (φ.symm ∘ Q) (𝓝 x) := Filter.map_congr hcomp.symm
      _ = Filter.map φ.symm (Filter.map Q (𝓝 x)) := (Filter.map_map).symm
      _ = Filter.map φ.symm (𝓝 (Q x)) := by rw [hQmap]
      _ = 𝓝 (f x) := by
        simpa only [Q, φ, modelWithCornersSelf_coe, Set.range_id, nhdsWithin_univ,
          Function.comp_apply] using
          map_extChartAt_symm_nhdsWithin_range (I := 𝓘(ℝ, E)) (f x)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ManifoldRelatedBracket
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Brackets of related vector fields on manifolds

Both source and target charts are local. This extends the vector-space
calculation only as far as needed to differentiate Lie-group homomorphisms.
-/

noncomputable section
namespace PolycyclicRecognition

open Set Filter Function Bundle VectorField
open scoped Manifold ContDiff Topology

variable {E F M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold (𝓘(ℝ, F)) ∞ N]

theorem fderiv_double_chart
    {f : M → N} (hf : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, F)) ∞ f)
    (x₀ : M) {y : E} (hy : y ∈ (extChartAt (𝓘(ℝ, E)) x₀).target)
    (hfy : f ((extChartAt (𝓘(ℝ, E)) x₀).symm y) ∈
      (extChartAt (𝓘(ℝ, F)) (f x₀)).source) :
    fderiv ℝ (extChartAt (𝓘(ℝ, F)) (f x₀) ∘ f ∘
        (extChartAt (𝓘(ℝ, E)) x₀).symm) y =
      (mfderiv (𝓘(ℝ, F)) (𝓘(ℝ, F)) (extChartAt (𝓘(ℝ, F)) (f x₀))
        (f ((extChartAt (𝓘(ℝ, E)) x₀).symm y))).comp
        ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) f ((extChartAt (𝓘(ℝ, E)) x₀).symm y)).comp
          (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (extChartAt (𝓘(ℝ, E)) x₀).symm y)) := by
  have hi : MDifferentiableAt (𝓘(ℝ, E)) (𝓘(ℝ, E))
      (extChartAt (𝓘(ℝ, E)) x₀).symm y := by
    simpa only [mfld_simps, mdifferentiableWithinAt_univ] using
      mdifferentiableWithinAt_extChartAt_symm hy
  have ho : MDifferentiableAt (𝓘(ℝ, F)) (𝓘(ℝ, F))
      (extChartAt (𝓘(ℝ, F)) (f x₀)) (f ((extChartAt (𝓘(ℝ, E)) x₀).symm y)) :=
    mdifferentiableAt_extChartAt (by simpa only [mfld_simps] using hfy)
  let D : E →L[ℝ] F :=
    (mfderiv (𝓘(ℝ, F)) (𝓘(ℝ, F)) (extChartAt (𝓘(ℝ, F)) (f x₀))
      (f ((extChartAt (𝓘(ℝ, E)) x₀).symm y)) : F →L[ℝ] F).comp
      ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) f ((extChartAt (𝓘(ℝ, E)) x₀).symm y) :
        E →L[ℝ] F).comp
        (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (extChartAt (𝓘(ℝ, E)) x₀).symm y))
  have hd : HasFDerivAt (extChartAt (𝓘(ℝ, F)) (f x₀) ∘ f ∘
      (extChartAt (𝓘(ℝ, E)) x₀).symm) D y :=
    (ho.hasMFDerivAt.comp y
      (((hf _).mdifferentiableAt (by simp)).hasMFDerivAt.comp y hi.hasMFDerivAt)).hasFDerivAt
  exact hd.fderiv

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_SmoothHomLieDifferential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Differentiating smooth Lie-group homomorphisms

The differential preserves brackets because the associated invariant
vector fields are related by the homomorphism.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold ContDiff

variable {E G F H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [TopologicalSpace H] [ChartedSpace F H] [Group H] [LieGroup (𝓘(ℝ, F)) ⊤ H]

def homDifferentialLinear (φ : G →* H) :
    GroupLieAlgebra (𝓘(ℝ, E)) G →ₗ[ℝ] GroupLieAlgebra (𝓘(ℝ, F)) H :=
  (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) φ 1 : E →L[ℝ] F).toLinearMap

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_PolynomialLieWordCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coordinate polynomials for finite Lie expressions -/

noncomputable section
namespace PolycyclicRecognition

open scoped BigOperators

variable {L I J S A : Type*} [LieRing L] [LieAlgebra ℝ L] [Fintype J]
  [CommRing A] [Algebra ℝ A] (b : Module.Basis J ℝ L)

def bracketCoordinatePolynomial (X : I → J → MvPolynomial S A) :
    FreeMagma I → J → MvPolynomial S A
  | .of i => X i
  | .mul u v => fun j => ∑ k, ∑ l,
      MvPolynomial.C (algebraMap ℝ A (b.repr ⁅b k, b l⁆ j)) *
        bracketCoordinatePolynomial X u k * bracketCoordinatePolynomial X v l

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialCurveOperations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial curves under linear maps and nilpotent derivation flows -/

noncomputable section
namespace PolycyclicRecognition

theorem polynomialFunctions_mul {f g : ℝ → ℝ}
    (hf : f ∈ polynomialFunctions) (hg : g ∈ polynomialFunctions) :
    (fun t => f t * g t) ∈ polynomialFunctions := by
  obtain ⟨p, hp⟩ := mem_polynomialFunctions_iff.mp hf
  obtain ⟨q, hq⟩ := mem_polynomialFunctions_iff.mp hg
  exact mem_polynomialFunctions_iff.mpr ⟨p * q, fun t => by rw [Polynomial.eval_mul, hp, hq]⟩

theorem polynomialFunctions_pow {f : ℝ → ℝ} (hf : f ∈ polynomialFunctions) (k : ℕ) :
    (fun t => f t ^ k) ∈ polynomialFunctions := by
  obtain ⟨p, hp⟩ := mem_polynomialFunctions_iff.mp hf
  exact mem_polynomialFunctions_iff.mpr ⟨p ^ k, fun t => by rw [Polynomial.eval_pow, hp]⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialMatrixFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial matrix exponentials and logarithms with uniform truncation -/

noncomputable section
namespace PolycyclicRecognition
open scoped BigOperators Matrix.Norms.Operator

def HasPolynomialMatrixEntries {I : Type*} {n : ℕ}
    (A : (I → ℝ) → Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i j, (fun x => A x i j) ∈ multivariatePolynomialFunctions I

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialMatrixScalarExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Faithful extension of scalars for concrete matrix groups -/

noncomputable section
namespace PolycyclicRecognition.PolynomialMatrixGroup

variable {K L : Type*} [Field K] [Field L] {n : ℕ}

def scalarExtension (f : K →+* L) : PolynomialMatrixGroup K n →* PolynomialMatrixGroup L n :=
  mulEquivGL.symm.toMonoidHom.comp ((Matrix.GeneralLinearGroup.map f).comp mulEquivGL.toMonoidHom)

@[simp] theorem scalarExtension_entries (f : K →+* L)
    (g : PolynomialMatrixGroup K n) (i j : Fin n) :
    entries (scalarExtension f g) i j = f (entries g i j) := rfl

def scalarVector (f : K →+* L) : (Fin n → K) →+ (Fin n → L) where
  toFun v := fun i => f (v i)
  map_zero' := by ext i; exact f.map_zero
  map_add' v w := by ext i; exact f.map_add _ _

end PolycyclicRecognition.PolynomialMatrixGroup

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialOneParameterNilpotent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial matrix one-parameter groups have nilpotent derivative

Successive derivatives are left multiplication by successive powers of the
initial derivative. A polynomial degree bound therefore forces one power to
vanish. This argument uses neither eigenvalues nor triangularization.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Matrix.Norms.Operator

variable {I : Type*} [Fintype I] [DecidableEq I]

def matrixEntryLinear (i j : I) : Matrix I I ℝ →L[ℝ] ℝ :=
  ({ toFun := fun A => A i j
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } : Matrix I I ℝ →ₗ[ℝ] ℝ).toContinuousLinearMap

omit [DecidableEq I] in
theorem matrixEntryLinear_apply (i j : I) (A : Matrix I I ℝ) :
    matrixEntryLinear i j A = A i j := rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialQuotientAction
attribute [-simp] _root_.OAI.PolycyclicRecognition.PolynomialMatrixGroup.scalarExtension_entries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial coordinates for induced quotient actions

Choose lifts of a quotient basis. Every forward and inverse matrix entry
of the induced action is then one linear functional of an ambient translate.
This gives continuity for the concrete polynomial matrix topology.
-/

noncomputable section
namespace PolycyclicRecognition.PolynomialMatrixGroup

variable {K G U : Type*} [Field K] [Group G] [AddCommGroup U] [Module K U]
    {m n : ℕ}

def coordinateLinearAction (ρ : G →* (U ≃ₗ[K] U)) (e : U ≃ₗ[K] (Fin m → K)) :
    G →* PolynomialMatrixGroup K m where
  toFun g := linearAction.symm ((e.symm.trans (ρ g)).trans e)
  map_one' := by
    apply linearAction.injective
    apply LinearEquiv.ext
    intro v
    simp
  map_mul' g h := by
    apply linearAction.injective
    apply LinearEquiv.ext
    intro v
    simp [LinearEquiv.mul_apply]

@[simp] theorem coordinateLinearAction_apply (ρ : G →* (U ≃ₗ[K] U))
    (e : U ≃ₗ[K] (Fin m → K)) (g : G) (v : Fin m → K) :
    linearAction (coordinateLinearAction ρ e g) v = e (ρ g (e.symm v)) := by
  simp [coordinateLinearAction]

def functionalPolynomialAt (b : Bool) (φ : Module.Dual K (Fin n → K))
    (v : Fin n → K) : MvPolynomial (Coord n) K :=
  ∑ i, ∑ j, MvPolynomial.C (φ (fun k => if i = k then 1 else 0)) *
    MvPolynomial.X (b, i, j) * MvPolynomial.C (v j)

end PolycyclicRecognition.PolynomialMatrixGroup

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ProjectedFactorSystem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The factor system induced by a surjective equivariant kernel map -/

namespace PolycyclicRecognition
variable {N K Q : Type*} [Group N] [Group K] [Group Q]

def NonabelianFactorSystem.mapSurjective (S : NonabelianFactorSystem N Q)
    (p : N →* K) (hp : Function.Surjective p) (a : Q → MulAut K)
    (ha : ∀ q x, p (S.action q x) = a q (p x)) : NonabelianFactorSystem K Q where
  action := a
  factor q r := p (S.factor q r)
  action_one := by
    apply DFunLike.ext
    intro k
    obtain ⟨x, rfl⟩ := hp k
    rw [← ha, S.action_one]
    rfl
  factor_one_left q := by rw [S.factor_one_left, map_one]
  factor_one_right q := by rw [S.factor_one_right, map_one]
  action_mul q r := by
    apply DFunLike.ext
    intro k
    obtain ⟨x, rfl⟩ := hp k
    change a q (a r (p x)) = p (S.factor q r) * a (q * r) (p x) * (p (S.factor q r))⁻¹
    rw [← ha, ← ha, S.action_mul_apply, map_mul, map_mul, map_inv, ha]
  cocycle q r s := by
    have h := congrArg p (S.cocycle q r s)
    simpa only [map_mul, ha] using h

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RationalCompleteIdentity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rational vanishing gives an integral annihilator of the complete identity

This is the coefficient step in the torsion endgame. Rational vanishing remains
an explicit intermediate premise until the hierarchical argument supplies it.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable (G : Type) [Group G]

instance groupCohomology_integral_additive (n : ℕ) :
    (groupCohomology.functor ℤ G n).Additive where
  map_add {X Y f g} := by
    change HomologicalComplex.homologyMap ((groupCohomology.cochainsFunctor ℤ G).map (f + g)) n =
      HomologicalComplex.homologyMap ((groupCohomology.cochainsFunctor ℤ G).map f) n +
        HomologicalComplex.homologyMap ((groupCohomology.cochainsFunctor ℤ G).map g) n
    rw [CategoryTheory.Functor.map_add, HomologicalComplex.homologyMap_add]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SubgroupInductionCoordinates
attribute [-instance] _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Direct-sum coordinates for induction from an arbitrary subgroup

Right cosets, with a chosen representative, are sufficient. No normality of
the subgroup is required for exact induction or for the rational base case.
-/
noncomputable section
namespace PolycyclicRecognition
open Representation
open scoped MonoidAlgebra TensorProduct
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G] (H : Subgroup G)

abbrev subgroupRightCosets := Quotient (QuotientGroup.rightRel H)
def subgroupRightCoset (g : G) : subgroupRightCosets H := Quotient.mk _ g
def subgroupRightRepresentative (c : subgroupRightCosets H) : G := c.out

@[simp]
theorem subgroupRightRepresentative_coset (c : subgroupRightCosets H) :
    subgroupRightCoset H (subgroupRightRepresentative H c) = c := Quotient.out_eq _

@[simp]
theorem subgroupRightCoset_mul (h : H) (g : G) :
    subgroupRightCoset H ((h : G) * g) = subgroupRightCoset H g := by
  apply Quotient.sound
  exact (QuotientGroup.rightRel_apply).mpr (by simp)

def subgroupRightPart (g : G) : H :=
  ⟨g * (subgroupRightRepresentative H (subgroupRightCoset H g))⁻¹,
    (QuotientGroup.rightRel_apply).mp
      (Quotient.exact (subgroupRightRepresentative_coset H (subgroupRightCoset H g)))⟩

@[simp]
theorem subgroupRightPart_decompose (g : G) :
    (subgroupRightPart H g : G) * subgroupRightRepresentative H (subgroupRightCoset H g) = g := by
  simp [subgroupRightPart]

@[simp]
theorem subgroupRightPart_mul (h : H) (g : G) :
    subgroupRightPart H ((h : G) * g) = h * subgroupRightPart H g := by
  apply Subtype.ext
  simp [subgroupRightPart, mul_assoc]

@[simp]
theorem subgroupRightPart_representative (c : subgroupRightCosets H) :
    subgroupRightPart H (subgroupRightRepresentative H c) = 1 := by
  apply Subtype.ext
  simp [subgroupRightPart]

variable (k : Type) [CommRing k] (A : Rep k H)

def subgroupInductionTensorCoordinates :
    k[G] ⊗[k] A →ₗ[k] (subgroupRightCosets H →₀ A) :=
  TensorProduct.lift <|
    (Finsupp.lift _ _ _ fun g =>
      (Finsupp.lsingle (subgroupRightCoset H g)).comp (A.ρ (subgroupRightPart H g)⁻¹))
      ∘ₗ (MonoidAlgebra.coeffLinearEquiv k).toLinearMap

@[simp]
theorem subgroupInductionTensorCoordinates_single (g : G) (a : A) :
    subgroupInductionTensorCoordinates H k A (MonoidAlgebra.single g 1 ⊗ₜ[k] a) =
      Finsupp.single (subgroupRightCoset H g) (A.ρ (subgroupRightPart H g)⁻¹ a) := by
  simp [subgroupInductionTensorCoordinates]

theorem subgroupInductionTensorCoordinates_invariant (h : H) :
    subgroupInductionTensorCoordinates H k A ∘ₗ
      (Representation.tprod ((Representation.leftRegular k G).comp H.subtype) A.ρ) h =
        subgroupInductionTensorCoordinates H k A := by
  apply TensorProduct.ext
  apply MonoidAlgebra.lhom_ext'
  intro g
  apply LinearMap.ext_ring
  apply LinearMap.ext
  intro a
  simp [map_mul, mul_inv_rev, Module.End.mul_apply]

def subgroupInductionCoordinates : Rep.ind H.subtype A →ₗ[k] (subgroupRightCosets H →₀ A) :=
  Coinvariants.lift _ (subgroupInductionTensorCoordinates H k A)
    (subgroupInductionTensorCoordinates_invariant H k A)

@[simp]
theorem subgroupInductionCoordinates_mk (g : G) (a : A) :
    subgroupInductionCoordinates H k A (IndV.mk H.subtype A.ρ g a) =
      Finsupp.single (subgroupRightCoset H g) (A.ρ (subgroupRightPart H g)⁻¹ a) :=
  subgroupInductionTensorCoordinates_single H k A g a

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_RationalFiniteResolution
attribute [-instance] _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite rational group resolution needed for the homology bound -/
noncomputable section
namespace PolycyclicRecognition.RationalResolution
open CategoryTheory CategoryTheory.Limits
variable {G : Type} [Group G] (P : ProjectiveResolution (Rep.trivial ℚ G ℚ))

def resolutionOpcyclesSequence (n : ℕ) : ShortComplex (Rep ℚ G) :=
  ShortComplex.mk (P.complex.fromOpcycles (n + 1) n) (P.complex.pOpcycles n) (by
    rw [← cancel_epi (P.complex.pOpcycles (n + 1)),
      P.complex.p_fromOpcycles_assoc, P.complex.d_pOpcycles, comp_zero])

theorem resolutionOpcyclesSequence_shortExact (n : ℕ) :
    (resolutionOpcyclesSequence P n).ShortExact := by
  have hsc : (P.complex.sc' (n + 2) (n + 1) n).Exact := P.exact_succ n
  let e := P.complex.opcyclesIsoSc' (n + 2) (n + 1) n (by simp) (by simp)
  have : Mono (P.complex.sc' (n + 2) (n + 1) n).fromOpcycles := hsc.mono_fromOpcycles
  have he : P.complex.fromOpcycles (n + 1) n =
      e.hom ≫ (P.complex.sc' (n + 2) (n + 1) n).fromOpcycles := by
    exact (e.inv_comp_eq).mp
      (P.complex.opcyclesIsoSc'_inv_fromOpcycles (n + 2) (n + 1) n (by simp) (by simp))
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · let S := ShortComplex.mk (P.complex.d (n + 1) n) (P.complex.pOpcycles n)
      (P.complex.d_pOpcycles (n + 1) n)
    have hS : S.Exact := ShortComplex.exact_of_g_is_cokernel _
      (P.complex.opcyclesIsCokernel (n + 1) n (by simp))
    let φ : S ⟶ resolutionOpcyclesSequence P n :=
      { τ₁ := P.complex.pOpcycles (n + 1)
        τ₂ := 𝟙 _
        τ₃ := 𝟙 _
        comm₁₂ := by simp [S, resolutionOpcyclesSequence]
        comm₂₃ := by simp [S, resolutionOpcyclesSequence] }
    have : Epi φ.τ₁ := by
      change Epi (P.complex.pOpcycles (n + 1))
      infer_instance
    have : IsIso φ.τ₂ := by
      change IsIso (𝟙 _)
      infer_instance
    have : Mono φ.τ₃ := by
      change Mono (𝟙 _)
      infer_instance
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mp hS
  · change Mono (P.complex.fromOpcycles (n + 1) n)
    have hmono : Mono (e.hom ≫ (P.complex.sc' (n + 2) (n + 1) n).fromOpcycles) :=
      inferInstance
    exact he.symm ▸ hmono
  · change Epi (P.complex.pOpcycles n)
    infer_instance

def resolutionOpcyclesZeroIso : P.complex.opcycles 0 ≅ Rep.trivial ℚ G ℚ :=
  (P.complex.opcyclesIsCokernel 1 0 (by simp)).coconePointUniqueUpToIso
    P.isColimitCokernelCofork

theorem resolutionOpcycles_projectiveDimension (n d : ℕ)
    [hdim : HasProjectiveDimensionLE (Rep.trivial ℚ G ℚ) (n + d)] :
    HasProjectiveDimensionLE (P.complex.opcycles n) d := by
  induction n generalizing d with
  | zero =>
    have : HasProjectiveDimensionLT (Rep.trivial ℚ G ℚ) (d + 1) := by
      simpa only [Nat.zero_add] using hdim
    exact hasProjectiveDimensionLT_of_iso (resolutionOpcyclesZeroIso P).symm (d + 1)
  | succ n ih =>
    have : HasProjectiveDimensionLE (Rep.trivial ℚ G ℚ) (n + (d + 1)) := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        hdim
    have hq := ih (d + 1)
    exact (resolutionOpcyclesSequence_shortExact P n).hasProjectiveDimensionLT_X₁ (d + 1)
      (hasProjectiveDimensionLT_of_ge (P.complex.X n) 1 (d + 1) (by omega)) hq

theorem resolutionOpcycles_projective (d : ℕ)
    [hdim : HasProjectiveDimensionLE (Rep.trivial ℚ G ℚ) d] : Projective (P.complex.opcycles d) := by
  have : HasProjectiveDimensionLE (Rep.trivial ℚ G ℚ) (d + 0) := by simpa using hdim
  exact (projective_iff_hasProjectiveDimensionLE_zero _).mpr
    (resolutionOpcycles_projectiveDimension P d 0)

variable {G : Type} [Group G] (P : ProjectiveResolution (Rep.trivial ℚ G ℚ)) (d : ℕ)

def finiteTruncation : ChainComplex (Rep ℚ G) ℕ :=
  P.complex.truncGE (finiteResolutionEmbedding d)

theorem finiteTruncation_isZero (i : ℕ) (hi : d < i) :
    IsZero ((finiteTruncation P d).X i) := by
  apply P.complex.truncGE (finiteResolutionEmbedding d) |>.isZero_X_of_isStrictlySupported
    (finiteResolutionEmbedding d) i
  intro j hj
  change j.val = i at hj
  omega

def finiteTruncationIso (i : ℕ) (hi : i < d) :
    (finiteTruncation P d).X i ≅ P.complex.X i :=
  P.complex.truncGEXIso (finiteResolutionEmbedding d) (i := ⟨i, by omega⟩) rfl
    (by rw [finiteResolutionEmbedding_boundary]; change i ≠ d; omega)

def finiteTruncationTopIso :
    (finiteTruncation P d).X d ≅ P.complex.opcycles d :=
  P.complex.truncGEXIsoOpcycles (finiteResolutionEmbedding d)
    (i := ⟨d, by omega⟩) rfl ((finiteResolutionEmbedding_boundary d _).mpr rfl)

theorem finiteTruncation_projective
    [HasProjectiveDimensionLE (Rep.trivial ℚ G ℚ) d] (i : ℕ) :
    Projective ((finiteTruncation P d).X i) := by
  rcases lt_trichotomy i d with hi | hi | hi
  · exact Projective.of_iso (finiteTruncationIso P d i hi).symm inferInstance
  · subst i
    exact Projective.of_iso (finiteTruncationTopIso P d).symm
      (resolutionOpcycles_projective P d)
  · exact (finiteTruncation_isZero P d i hi).projective

instance finiteResolution_single_supported :
    ((ChainComplex.single₀ (Rep ℚ G)).obj (Rep.trivial ℚ G ℚ)).IsStrictlySupported
      (finiteResolutionEmbedding d) where
  isZero i hi := by
    apply HomologicalComplex.isZero_single_obj_X
    intro h
    subst i
    exact hi ⟨0, by omega⟩ rfl

def finiteTruncationAugmentation :
    finiteTruncation P d ⟶ (ChainComplex.single₀ (Rep ℚ G)).obj (Rep.trivial ℚ G ℚ) :=
  HomologicalComplex.truncGEMap P.π (finiteResolutionEmbedding d) ≫
    inv (((ChainComplex.single₀ (Rep ℚ G)).obj (Rep.trivial ℚ G ℚ)).πTruncGE
      (finiteResolutionEmbedding d))

instance finiteTruncationAugmentation_quasiIso :
    QuasiIso (finiteTruncationAugmentation P d) := by
  have : QuasiIso (HomologicalComplex.truncGEMap P.π (finiteResolutionEmbedding d)) :=
    (HomologicalComplex.quasiIso_truncGEMap_iff P.π (finiteResolutionEmbedding d)).mpr
      (fun _ _ _ => inferInstance)
  exact quasiIso_comp (HomologicalComplex.truncGEMap P.π (finiteResolutionEmbedding d))
    (inv (((ChainComplex.single₀ (Rep ℚ G)).obj (Rep.trivial ℚ G ℚ)).πTruncGE
      (finiteResolutionEmbedding d)))

def finiteProjectiveResolution [HasProjectiveDimensionLE (Rep.trivial ℚ G ℚ) d] :
    ProjectiveResolution (Rep.trivial ℚ G ℚ) where
  complex := finiteTruncation P d
  projective := finiteTruncation_projective P d
  π := finiteTruncationAugmentation P d


end PolycyclicRecognition.RationalResolution

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_RationalHomologyDimension
attribute [-instance] _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Detecting dimension using rational homology with coefficients

Shapiro's lemma passes a uniform bound to subgroups. The orientation module
detects the dimension of an integral Poincare duality group even after
rationalization. No finiteness of coefficient representations is required.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
attribute [local instance 2000] Rep.hV2 Rep.instLinear ModuleCat.isModule
attribute [local instance 2300] TensorProduct.instModule
variable {G : Type} [Group G]

def RationalHomologyDimensionLE (G : Type) [Group G] (d : ℕ) : Prop :=
  ∀ (A : Rep ℤ G) (i : ℕ), d < i →
    IsZero (ModuleCat.of ℚ (ℚ ⊗[ℤ] groupHomology A i))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_ProjectiveKernelStableMap
attribute [-instance] _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Maps between projective presentations preserve stable zero maps -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

def projectivePresentationMap
    (S T : ShortComplex (Rep.{0} ℤ G)) (_hS : S.ShortExact) (hT : T.ShortExact)
    [Projective S.X₂] (f : S.X₃ ⟶ T.X₃) : S ⟶ T := by
  let : Mono T.f := hT.mono_f
  let : Epi T.g := hT.epi_g
  let l := Projective.factorThru (S.g ≫ f) T.g
  have hl : l ≫ T.g = S.g ≫ f := Projective.factorThru_comp _ _
  have hk : (S.f ≫ l) ≫ T.g = 0 := by
    rw [Category.assoc, hl, ← Category.assoc, S.zero, zero_comp]
  exact { τ₁ := hT.exact.lift (S.f ≫ l) hk
          τ₂ := l
          τ₃ := f
          comm₁₂ := hT.exact.lift_f _ _
          comm₂₃ := hl }

@[simp]
theorem projectivePresentationMap_τ₃
    (S T : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) (hT : T.ShortExact)
    [Projective S.X₂] (f : S.X₃ ⟶ T.X₃) :
    (projectivePresentationMap S T hS hT f).τ₃ = f := rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_IntegralProjectiveTower
attribute [-instance] _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integral projective syzygy towers

This records the successive projective presentations used by the normalized
and horseshoe constructions. Maps lift recursively, and their induced stable
maps depend only on the stable map at the initial coefficient.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

structure IntegralProjectiveTower (G : Type) [Group G] where
  obj : ℕ → Rep.{0} ℤ G
  projectiveObj : ℕ → Rep.{0} ℤ G
  projective : ∀ n, Projective (projectiveObj n)
  ι : ∀ n, obj (n + 1) ⟶ projectiveObj n
  π : ∀ n, projectiveObj n ⟶ obj n
  zero : ∀ n, ι n ≫ π n = 0
  shortExact : ∀ n, (ShortComplex.mk (ι n) (π n) (zero n)).ShortExact

namespace IntegralProjectiveTower

def sequence (T : IntegralProjectiveTower G) (n : ℕ) : ShortComplex (Rep.{0} ℤ G) :=
  ShortComplex.mk (T.ι n) (T.π n) (T.zero n)

instance instProjectiveRepIntProjectiveObj (T : IntegralProjectiveTower G) (n : ℕ) : Projective (T.projectiveObj n) := T.projective n

instance instProjectiveRepIntX₂Sequence (T : IntegralProjectiveTower G) (n : ℕ) : Projective (T.sequence n).X₂ := T.projective n

structure Map (T U : IntegralProjectiveTower G) where
  app : ∀ n, T.obj n ⟶ U.obj n
  cover : ∀ n, T.projectiveObj n ⟶ U.projectiveObj n
  comm_left : ∀ n, app (n + 1) ≫ U.ι n = T.ι n ≫ cover n
  comm_right : ∀ n, cover n ≫ U.π n = T.π n ≫ app n

namespace Map
variable {T U V : IntegralProjectiveTower G}

def sequenceMap (f : Map T U) (n : ℕ) : T.sequence n ⟶ U.sequence n where
  τ₁ := f.app (n + 1)
  τ₂ := f.cover n
  τ₃ := f.app n
  comm₁₂ := f.comm_left n
  comm₂₃ := f.comm_right n

def identity (T : IntegralProjectiveTower G) : Map T T where
  app _ := 𝟙 _
  cover _ := 𝟙 _
  comm_left _ := by rw [Category.id_comp, Category.comp_id]
  comm_right _ := by rw [Category.id_comp, Category.comp_id]

def comp (f : Map T U) (g : Map U V) : Map T V where
  app n := f.app n ≫ g.app n
  cover n := f.cover n ≫ g.cover n
  comm_left n := by
    rw [Category.assoc, g.comm_left, ← Category.assoc, f.comm_left, Category.assoc]
  comm_right n := by
    rw [Category.assoc, g.comm_right, ← Category.assoc, f.comm_right, Category.assoc]

end Map

def liftedApp (T U : IntegralProjectiveTower G) (f : T.obj 0 ⟶ U.obj 0) :
    (n : ℕ) → T.obj n ⟶ U.obj n
  | 0 => f
  | n + 1 => (projectivePresentationMap (T.sequence n) (U.sequence n)
      (T.shortExact n) (U.shortExact n) (liftedApp T U f n)).τ₁

def liftMap (T U : IntegralProjectiveTower G) (f : T.obj 0 ⟶ U.obj 0) : Map T U where
  app := liftedApp T U f
  cover n := (projectivePresentationMap (T.sequence n) (U.sequence n)
    (T.shortExact n) (U.shortExact n) (liftedApp T U f n)).τ₂
  comm_left n := (projectivePresentationMap (T.sequence n) (U.sequence n)
    (T.shortExact n) (U.shortExact n) (liftedApp T U f n)).comm₁₂
  comm_right n := (projectivePresentationMap (T.sequence n) (U.sequence n)
    (T.shortExact n) (U.shortExact n) (liftedApp T U f n)).comm₂₃

@[simp]
theorem liftMap_zero (T U : IntegralProjectiveTower G) (f : T.obj 0 ⟶ U.obj 0) :
    (liftMap T U f).app 0 = f := rfl

end IntegralProjectiveTower
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_SmallCoefficientRing
attribute [-instance] _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A small ring of bounded functions with finite-subgroup projectivity

For each finite subgroup choose its right-coset transversal. Take the Boolean
algebra generated by every left translate of these transversals and of
subgroup coset partitions inside finitely generated subgroups. When the group
is countable, this uses countably many coordinates. Its step-function ring is
projective over the integers and has a trace-one element for every finite
subgroup.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
attribute [local instance] Classical.propDecidable
variable (G : Type) [Group G]

set_option synthInstance.maxHeartbeats 400000 in
abbrev finiteSubgroupIndex := {H : Subgroup G // Finite H}

set_option synthInstance.maxHeartbeats 400000 in
def finiteSubgroupElements (H : finiteSubgroupIndex G) : Finset G := by
  let := H.property
  exact (Set.toFinite (H.val : Set G)).toFinset

set_option synthInstance.maxHeartbeats 400000 in
@[simp]
theorem finiteSubgroupElements_coe (H : finiteSubgroupIndex G) :
    (finiteSubgroupElements G H : Set G) = H.val := by
  simp [finiteSubgroupElements]

set_option synthInstance.maxHeartbeats 400000 in
abbrev finitelyGeneratedSubgroupIndex := {H : Subgroup G // H.FG}

set_option synthInstance.maxHeartbeats 400000 in
abbrev smallCoefficientBase := finiteSubgroupIndex G ⊕
  (Σ J : finitelyGeneratedSubgroupIndex G, finitelyGeneratedSubgroupIndex J.val)

set_option synthInstance.maxHeartbeats 400000 in
abbrev smallCoefficientIndex := smallCoefficientBase G × G

set_option synthInstance.maxHeartbeats 400000 in
def smallCoefficientFeature (i : smallCoefficientIndex G) (x : G) : Bool := by
  classical
  exact match i.1 with
    | .inl H => decide (subgroupRightPart H.val (i.2⁻¹ * x) = 1)
    | .inr JN => decide (subgroupRightPart JN.1.val (i.2⁻¹ * x) ∈ JN.2.val)

set_option synthInstance.maxHeartbeats 400000 in
def smallCoefficientTranslate (g : G) (i : smallCoefficientIndex G) : smallCoefficientIndex G :=
  (i.1, g * i.2)

set_option synthInstance.maxHeartbeats 400000 in
theorem smallCoefficientFeature_translate (g : G) (i : smallCoefficientIndex G) (x : G) :
    smallCoefficientFeature G i (g⁻¹ * x) =
      smallCoefficientFeature G (smallCoefficientTranslate G g i) x := by
  dsimp only [smallCoefficientFeature, smallCoefficientTranslate]
  simp only [mul_inv_rev, mul_assoc]

set_option synthInstance.maxHeartbeats 400000 in
abbrev SmallCoefficientRing := booleanStepRing (smallCoefficientFeature G)

set_option synthInstance.maxHeartbeats 400000 in
instance smallCoefficientRing_mulSemiringAction : MulSemiringAction G (SmallCoefficientRing G) :=
  booleanStepMulSemiringAction (smallCoefficientFeature G) (smallCoefficientTranslate G)
    (smallCoefficientFeature_translate G)

set_option synthInstance.maxHeartbeats 400000 in
@[simp]
theorem smallCoefficientRing_smul_apply (g x : G) (f : SmallCoefficientRing G) :
    (g • f).val x = f.val (g⁻¹ * x) := rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_ProjectiveTowerCohomology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cohomology along a projective syzygy tower -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

namespace IntegralProjectiveTower

abbrev cohomologyStage (T : IntegralProjectiveTower G) (p n : ℕ) : Type :=
  groupCohomology (T.obj n) (n + p)

def connecting (T : IntegralProjectiveTower G) (p n : ℕ) :
    groupCohomology (T.obj n) (n + p) ⟶ groupCohomology (T.obj (n + 1)) (n + 1 + p) :=
  groupCohomology.δ (T.shortExact n) (n + p) (n + 1 + p) (by omega)

def forward (T : IntegralProjectiveTower G) (p i j : ℕ) (h : i ≤ j) :
    T.cohomologyStage p i →ₗ[ℤ] T.cohomologyStage p j where
  toFun := Nat.leRecOn h (fun {k} => (T.connecting p k).hom)
  map_add' x y := by
    induction h with
    | refl => simp only [Nat.leRecOn_self]
    | @step j h ih => simp only [Nat.leRecOn_succ h, map_add, ih]
  map_smul' r x := by
    induction h with
    | refl => simp only [Nat.leRecOn_self, RingHom.id_apply]
    | @step j h ih =>
      simp only [Nat.leRecOn_succ h, ih, RingHom.id_apply]
      exact (T.connecting p j).hom.map_smul r _

instance instDirectedSystemNatCohomologyStageCoeLinearMapIntIdForward (T : IntegralProjectiveTower G) (p : ℕ) :
    DirectedSystem (T.cohomologyStage p) (fun i j h => T.forward p i j h) where
  map_self := by intro i x; exact Nat.leRecOn_self x
  map_map := by intro k j i hij hjk x; exact (Nat.leRecOn_trans hij hjk x).symm

abbrev Cohomology (T : IntegralProjectiveTower G) (p : ℕ) :=
  Module.DirectLimit (T.cohomologyStage p) (T.forward p)

namespace Map
variable {T U : IntegralProjectiveTower G}

def stageMap (f : Map T U) (p n : ℕ) : T.cohomologyStage p n →ₗ[ℤ] U.cohomologyStage p n :=
  ((groupCohomology.functor ℤ G (n + p)).map (f.app n)).hom

theorem connecting_natural (f : Map T U) (p n : ℕ) :
    T.connecting p n ≫ (groupCohomology.functor ℤ G (n + 1 + p)).map (f.app (n + 1)) =
      (groupCohomology.functor ℤ G (n + p)).map (f.app n) ≫ U.connecting p n :=
  groupCohomology.δ_naturality (T.shortExact n) (U.shortExact n)
    (f.sequenceMap n) (n + p) (n + 1 + p) (by omega)

theorem forward_natural (f : Map T U) (p i j : ℕ) (h : i ≤ j) (x : T.cohomologyStage p i) :
    f.stageMap p j (T.forward p i j h x) = U.forward p i j h (f.stageMap p i x) := by
  induction h with
  | refl =>
    simp only [forward, Nat.leRecOn_self]
    rfl
  | @step j h ih =>
    change f.stageMap p (j + 1)
      (Nat.leRecOn (C := T.cohomologyStage p) _ (fun {k} => (T.connecting p k).hom) x) =
      Nat.leRecOn (C := U.cohomologyStage p) _ (fun {k} => (U.connecting p k).hom) _
    rw [Nat.leRecOn_succ h, Nat.leRecOn_succ h]
    have hn := ConcreteCategory.congr_hom (f.connecting_natural p j) (T.forward p i j h x)
    change f.stageMap p (j + 1) ((T.connecting p j).hom _) =
      (U.connecting p j).hom (f.stageMap p j (T.forward p i j h x)) at hn
    change f.stageMap p (j + 1) ((T.connecting p j).hom (T.forward p i j h x)) =
      (U.connecting p j).hom (U.forward p i j h (f.stageMap p i x))
    rw [hn, ih]

def cohomologyMap (f : Map T U) (p : ℕ) : T.Cohomology p →ₗ[ℤ] U.Cohomology p :=
  Module.DirectLimit.map (f := T.forward p) (f' := U.forward p) (f.stageMap p)
    (fun i j h => by apply LinearMap.ext; exact f.forward_natural p i j h)

@[simp]
theorem cohomologyMap_of (f : Map T U) (p n : ℕ) (x : T.cohomologyStage p n) :
    f.cohomologyMap p (Module.DirectLimit.of ℤ ℕ _ (T.forward p) n x) =
      Module.DirectLimit.of ℤ ℕ _ (U.forward p) n (f.stageMap p n x) :=
  Module.DirectLimit.map_apply_of (f.stageMap p)
    (fun i j h => by apply LinearMap.ext; exact f.forward_natural p i j h) x

end Map
end IntegralProjectiveTower
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_ProjectiveTowerComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Independence of the projective syzygy tower -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]
namespace IntegralProjectiveTower
namespace Map
variable {T U V : IntegralProjectiveTower G}

theorem cohomologyMap_identity (T : IntegralProjectiveTower G) (p : ℕ) :
    (identity T).cohomologyMap p = LinearMap.id := by
  apply LinearMap.ext
  intro x
  obtain ⟨n, z, rfl⟩ := Module.DirectLimit.exists_of x
  rw [cohomologyMap_of]
  change Module.DirectLimit.of ℤ ℕ _ (T.forward p) n
    (((groupCohomology.functor ℤ G (n + p)).map (𝟙 (T.obj n))).hom z) = _
  rw [CategoryTheory.Functor.map_id]
  rfl

theorem cohomologyMap_comp (f : Map T U) (g : Map U V) (p : ℕ) :
    (f.comp g).cohomologyMap p = (g.cohomologyMap p).comp (f.cohomologyMap p) := by
  apply LinearMap.ext
  intro x
  obtain ⟨n, z, rfl⟩ := Module.DirectLimit.exists_of x
  simp only [cohomologyMap_of, LinearMap.comp_apply]
  change Module.DirectLimit.of ℤ ℕ _ (V.forward p) n
    (((groupCohomology.functor ℤ G (n + p)).map (f.app n ≫ g.app n)).hom z) = _
  rw [CategoryTheory.Functor.map_comp]
  rfl

end Map

end IntegralProjectiveTower
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RepresentationDirectSum
attribute [-instance] _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete sums of integral representations for the telescope resolution -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2300] DirectSum.instModule
variable {G : Type} [Group G] {ι : Type}

abbrev integralRepresentationSum (A : ι → Rep.{0} ℤ G) : Rep.{0} ℤ G :=
  Rep.of (Representation.directSum (fun i => (A i).ρ))

abbrev integralRepresentationSumInclusion (A : ι → Rep.{0} ℤ G) (i : ι) :
    A i ⟶ integralRepresentationSum A := by
  classical
  exact Rep.ofHom ⟨DirectSum.lof ℤ ι (fun i => (A i).V) i, fun g => by
    ext x
    simp [Representation.directSum]⟩

@[simp]
theorem integralRepresentationSumInclusion_apply [DecidableEq ι] (A : ι → Rep.{0} ℤ G) (i : ι)
    (x : A i) : (integralRepresentationSumInclusion A i).hom x =
      DirectSum.of (fun i => (A i).V) i x := by
  simp [integralRepresentationSumInclusion, DirectSum.lof_eq_of]
  ext j
  simp [DirectSum.of_apply]

@[simp]
theorem integralRepresentationSumInclusion_same [DecidableEq ι]
    (A : ι → Rep.{0} ℤ G) (i : ι) (x : A i) :
    ((integralRepresentationSumInclusion A i).hom x) i = x := by
  have h := congrArg (fun y : integralRepresentationSum A => y i)
    (integralRepresentationSumInclusion_apply A i x)
  exact h.trans (by simp)

theorem integralRepresentationSumInclusion_ne [DecidableEq ι]
    (A : ι → Rep.{0} ℤ G) (i j : ι) (hij : i ≠ j) (x : A i) :
    ((integralRepresentationSumInclusion A i).hom x) j = 0 := by
  have h := congrArg (fun y : integralRepresentationSum A => y j)
    (integralRepresentationSumInclusion_apply A i x)
  exact h.trans (by simp [DirectSum.of_apply, hij])

def integralRepresentationSumDesc (A : ι → Rep.{0} ℤ G) (B : Rep.{0} ℤ G)
    (f : ∀ i, A i ⟶ B) : integralRepresentationSum A ⟶ B := by
  classical
  exact Rep.ofHom ⟨DirectSum.toModule ℤ ι B (fun i => (f i).hom.toLinearMap), fun g => by
    apply DirectSum.linearMap_ext
    intro i
    ext x
    change DirectSum.toModule ℤ ι B (fun i => (f i).hom.toLinearMap)
      ((DirectSum.lmap (fun i => (A i).ρ g)) (DirectSum.lof ℤ ι _ i x)) =
      B.ρ g (DirectSum.toModule ℤ ι B (fun i => (f i).hom.toLinearMap)
        (DirectSum.lof ℤ ι _ i x))
    rw [DirectSum.lmap_lof, DirectSum.toModule_lof, DirectSum.toModule_lof]
    exact Rep.hom_comm_apply (f i) g x⟩

@[reassoc (attr := simp)]
theorem integralRepresentationSumInclusion_desc (A : ι → Rep.{0} ℤ G)
    (B : Rep.{0} ℤ G) (f : ∀ i, A i ⟶ B) (i : ι) :
    integralRepresentationSumInclusion A i ≫ integralRepresentationSumDesc A B f = f i := by
  classical
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  change DirectSum.toModule ℤ ι B (fun i => (f i).hom.toLinearMap)
    (DirectSum.lof ℤ ι _ i x) = (f i).hom x
  simp only [DirectSum.toModule_lof]
  rfl

theorem integralRepresentationSum_hom_ext {A : ι → Rep.{0} ℤ G} {B : Rep.{0} ℤ G}
    {f g : integralRepresentationSum A ⟶ B}
    (h : ∀ i, integralRepresentationSumInclusion A i ≫ f =
      integralRepresentationSumInclusion A i ≫ g) : f = g := by
  classical
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply DirectSum.linearMap_ext
  intro i
  exact congrArg (fun k : A i ⟶ B => k.hom.toLinearMap) (h i)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_SequentialProjectiveTelescope
attribute [-instance] _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A length-one projective resolution of a sequential projective colimit

The differential is identity minus the forward shift. Its injectivity uses
induction on coordinates, and the cokernel is the given concrete colimit.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2300] DirectSum.instModule
variable {G : Type} [Group G]
namespace SequentialRepresentationDiagram
variable (D : SequentialRepresentationDiagram G)

abbrev telescopeSum := integralRepresentationSum D.obj

def telescopeShift : D.telescopeSum ⟶ D.telescopeSum :=
  integralRepresentationSumDesc D.obj D.telescopeSum
    (fun i => D.map i (i + 1) (Nat.le_succ i) ≫ integralRepresentationSumInclusion D.obj (i + 1))

def telescopeDifferential : D.telescopeSum ⟶ D.telescopeSum := 𝟙 _ - D.telescopeShift

@[simp]
theorem telescopeShift_inclusion (i : ℕ) (x : D.obj i) :
    D.telescopeShift.hom ((integralRepresentationSumInclusion D.obj i).hom x) =
      (integralRepresentationSumInclusion D.obj (i + 1)).hom
        ((D.map i (i + 1) (Nat.le_succ i)).hom x) := by
  exact ConcreteCategory.congr_hom (integralRepresentationSumInclusion_desc D.obj
    D.telescopeSum (fun i => D.map i (i + 1) (Nat.le_succ i) ≫
      integralRepresentationSumInclusion D.obj (i + 1)) i) x

@[simp]
theorem telescopeShift_zero (x : D.telescopeSum) : D.telescopeShift.hom x 0 = 0 := by
  classical
  induction x using DirectSum.induction_on with
  | zero => simp
  | add x y hx hy =>
    rw [map_add]
    change ((D.telescopeShift.hom x) 0 + (D.telescopeShift.hom y) 0) = 0
    rw [hx, hy, add_zero]
  | of i x =>
    rw [← integralRepresentationSumInclusion_apply D.obj i x]
    rw [telescopeShift_inclusion]
    exact integralRepresentationSumInclusion_ne D.obj (i + 1) 0 (by omega) _

@[simp]
theorem telescopeShift_succ (x : D.telescopeSum) (i : ℕ) :
    D.telescopeShift.hom x (i + 1) = (D.map i (i + 1) (Nat.le_succ i)).hom (x i) := by
  classical
  induction x using DirectSum.induction_on with
  | zero => simp
  | add x y hx hy =>
    rw [map_add]
    change (D.telescopeShift.hom x) (i + 1) + (D.telescopeShift.hom y) (i + 1) =
      (D.map i (i + 1) (Nat.le_succ i)).hom (x i + y i)
    rw [hx, hy, map_add]
  | of j x =>
    rw [← integralRepresentationSumInclusion_apply D.obj j x]
    rw [telescopeShift_inclusion]
    by_cases h : j = i
    · subst j
      rw [integralRepresentationSumInclusion_same, integralRepresentationSumInclusion_same]
    · have h' : j + 1 ≠ i + 1 := by omega
      rw [integralRepresentationSumInclusion_ne D.obj (j + 1) (i + 1) h',
        integralRepresentationSumInclusion_ne D.obj j i h, map_zero]

namespace ColimitCocone
variable {D} {A : Rep.{0} ℤ G} (c : D.ColimitCocone A)

def telescopeAugmentation : D.telescopeSum ⟶ A :=
  integralRepresentationSumDesc D.obj A c.ι

theorem telescopeDifferential_augmentation :
    D.telescopeDifferential ≫ c.telescopeAugmentation = 0 := by
  apply integralRepresentationSum_hom_ext
  intro i
  simp only [telescopeDifferential, Preadditive.comp_sub, Preadditive.sub_comp,
    Category.id_comp, Category.assoc, telescopeShift, telescopeAugmentation,
    integralRepresentationSumInclusion_desc_assoc, integralRepresentationSumInclusion_desc,
    c.comm, sub_self, comp_zero]

instance telescopeAugmentation_epi : Epi c.telescopeAugmentation := by
  apply (Rep.epi_iff_surjective _).mpr
  intro a
  obtain ⟨i, x, rfl⟩ := c.surj a
  exact ⟨(integralRepresentationSumInclusion D.obj i).hom x,
    ConcreteCategory.congr_hom (integralRepresentationSumInclusion_desc _ _ _ i) x⟩


def telescopeSequence : ShortComplex (Rep.{0} ℤ G) :=
  ShortComplex.mk D.telescopeDifferential c.telescopeAugmentation
    c.telescopeDifferential_augmentation

theorem telescopeCokernelCompatible (i j : ℕ) (h : i ≤ j) :
    D.map i j h ≫ integralRepresentationSumInclusion D.obj j ≫
        cokernel.π D.telescopeDifferential =
      integralRepresentationSumInclusion D.obj i ≫ cokernel.π D.telescopeDifferential := by
  induction h with
  | refl => rw [D.map_id, Category.id_comp]
  | @step j h ih =>
    have he : (integralRepresentationSumInclusion D.obj j -
        D.map j (j + 1) (Nat.le_succ j) ≫
          integralRepresentationSumInclusion D.obj (j + 1)) ≫
            cokernel.π D.telescopeDifferential = 0 := by
      have hz : (integralRepresentationSumInclusion D.obj j ≫ D.telescopeDifferential) ≫
          cokernel.π D.telescopeDifferential = 0 := by
        rw [Category.assoc, cokernel.condition, comp_zero]
      simpa only [← Category.assoc, telescopeDifferential, Preadditive.comp_sub,
        Category.comp_id, telescopeShift, integralRepresentationSumInclusion_desc,
        Preadditive.sub_comp] using hz
    have hj : D.map j (j + 1) (Nat.le_succ j) ≫
        integralRepresentationSumInclusion D.obj (j + 1) ≫
          cokernel.π D.telescopeDifferential =
        integralRepresentationSumInclusion D.obj j ≫ cokernel.π D.telescopeDifferential := by
      rw [Preadditive.sub_comp, sub_eq_zero] at he
      exact he.symm
    rw [← D.map_comp i j (j + 1) h (Nat.le_succ j), Category.assoc, hj]
    exact ih

def telescopeCokernelDescent : A ⟶ cokernel D.telescopeDifferential :=
  c.desc _ (fun i => integralRepresentationSumInclusion D.obj i ≫
    cokernel.π D.telescopeDifferential) (telescopeCokernelCompatible (D := D))

end ColimitCocone
end SequentialRepresentationDiagram
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SmallCoefficientMean
attribute [-instance] _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An invariant mean on the actual bounded coefficient ring

Every ring element has finite range. Evaluation as a real bounded function is
therefore defined without any extra boundedness premise.
-/
noncomputable section
namespace PolycyclicRecognition
open ThompsonNonamenability
open scoped ENNReal
variable {G : Type} [Group G]

def smallCoefficientBoundedReal (f : SmallCoefficientRing G) : BoundedReal G := by
  refine ⟨fun x => (f.val x : ℝ), memℓp_infty ?_⟩
  apply ((booleanStepRing_finite_range (smallCoefficientFeature G) f).image
    (fun z : ℤ => ‖(z : ℝ)‖)).bddAbove.mono
  rintro _ ⟨x, rfl⟩
  exact ⟨f.val x, ⟨x, rfl⟩, rfl⟩

@[simp]
theorem smallCoefficientBoundedReal_apply (f : SmallCoefficientRing G) (x : G) :
    smallCoefficientBoundedReal f x = (f.val x : ℝ) := rfl

def smallCoefficientBoundedRealLinear : SmallCoefficientRing G →ₗ[ℤ] BoundedReal G where
  toFun := smallCoefficientBoundedReal
  map_add' f h := by
    apply lp.ext
    funext x
    change ((f.val x + h.val x : ℤ) : ℝ) = (f.val x : ℝ) + (h.val x : ℝ)
    exact Int.cast_add _ _
  map_smul' n f := by
    apply lp.ext
    funext x
    change ((n • f.val x : ℤ) : ℝ) = n • (f.val x : ℝ)
    simp [zsmul_eq_mul]

@[simp]
theorem smallCoefficientBoundedReal_one :
    smallCoefficientBoundedReal (1 : SmallCoefficientRing G) = 1 := by
  apply lp.ext
  funext x
  exact Int.cast_one

def smallCoefficientRealMean (M : InvariantMean G) : SmallCoefficientRing G →ₗ[ℤ] ℝ :=
  (M.toLinearMap.restrictScalars ℤ).comp smallCoefficientBoundedRealLinear

@[simp]
theorem smallCoefficientRealMean_one (M : InvariantMean G) :
    smallCoefficientRealMean M 1 = 1 := by
  change M.toLinearMap (smallCoefficientBoundedReal 1) = 1
  rw [smallCoefficientBoundedReal_one, M.normalized]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SmallCoefficientRationalMean
attribute [-instance] _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An invariant rational functional on the rationalized coefficient ring

The real mean proves that the constant class is nonzero in coinvariants.
Linear separation over the rationals then supplies a rational functional;
no rational-valued positive mean on all bounded functions is assumed.
-/
noncomputable section
namespace PolycyclicRecognition
open ThompsonNonamenability Representation
open scoped TensorProduct
attribute [local instance 2300] TensorProduct.instModule
variable {G : Type} [Group G]

set_option synthInstance.maxHeartbeats 400000 in
abbrev SmallCoefficientRationalSpace := ℚ ⊗[ℤ] SmallCoefficientRing G

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SequentialModuleTail
attribute [-instance] _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing the first stage of a sequential integral module colimit -/
noncomputable section
namespace PolycyclicRecognition
attribute [local instance 2300] Module.DirectLimit.module
variable (M : ℕ → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module ℤ (M i)]
  (f : ∀ i j, i ≤ j → M i →ₗ[ℤ] M j)
  [DirectedSystem M (fun i j h => f i j h)]

abbrev moduleTailMap (i j : ℕ) (h : i ≤ j) : M (i + 1) →ₗ[ℤ] M (j + 1) :=
  f (i + 1) (j + 1) (Nat.add_le_add_right h 1)

abbrev ModuleTailLimit := Module.DirectLimit (fun i => M (i + 1)) (moduleTailMap M f)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RationalFiniteQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rational dimension under a finite normal quotient -/
noncomputable section
namespace PolycyclicRecognition.RationalQuotient
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2300] Representation.Coinvariants.instModule
variable {G : Type} [Group G] (N : Subgroup G) [N.Normal]

def normalCoinvariantsInflationCounit (B : Rep.{0} ℚ (G ⧸ N)) :
    (Rep.res (QuotientGroup.mk' N) B).quotientToCoinvariants N ⟶ B :=
  Rep.ofHom {
    toLinearMap := Representation.Coinvariants.lift _ LinearMap.id (fun n => by
      apply LinearMap.ext
      intro x
      change B.ρ (QuotientGroup.mk' N (n : G)) x = x
      have hn : QuotientGroup.mk' N (n : G) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr n.property
      rw [hn, map_one]
      rfl)
    isIntertwining' q := by
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N q
      apply LinearMap.ext
      intro x
      induction x using Representation.Coinvariants.induction_on with
      | h x => rfl }

@[simp] theorem normalCoinvariantsInflationCounit_mk (B : Rep.{0} ℚ (G ⧸ N)) (x : B.V) :
    normalCoinvariantsInflationCounit N B
      (Representation.Coinvariants.mk ((Rep.res (QuotientGroup.mk' N) B).ρ.comp N.subtype) x) = x := rfl

def normalCoinvariantsInflationAdjunction :
    Rep.quotientToCoinvariantsFunctor.{0} ℚ N ⊣ Rep.resFunctor (QuotientGroup.mk' N) where
  unit := {
    app A := A.toCoinvariantsMkQ N
    naturality := by intros; ext; rfl }
  counit := {
    app B := normalCoinvariantsInflationCounit N B
    naturality := by
      intro A B f
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro x
      induction x using Representation.Coinvariants.induction_on with
      | h x => rfl }
  left_triangle_components := by
    intro A
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    induction x using Representation.Coinvariants.induction_on with
    | h x => rfl
  right_triangle_components := by intros; ext; rfl

instance normalCoinvariants_preservesProjective :
    (Rep.quotientToCoinvariantsFunctor.{0} ℚ N).PreservesProjectiveObjects :=
  Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms
    (normalCoinvariantsInflationAdjunction N)


instance quotientCoinvariants_additive :
    (Rep.quotientToCoinvariantsFunctor.{0} ℚ N).Additive where
  map_add := by
    intro X Y f g
    ext x
    induction x using Representation.Coinvariants.induction_on with
    | h x => rfl

instance instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions : (Rep.quotientToCoinvariantsFunctor.{0} ℚ N).IsLeftAdjoint :=
  (normalCoinvariantsInflationAdjunction N).isLeftAdjoint

def trivialCoinvariantsIso :
    (Rep.trivial ℚ G ℚ).quotientToCoinvariants N ≅ Rep.trivial ℚ (G ⧸ N) ℚ := by
  let e : (Rep.trivial ℚ G ℚ).quotientToCoinvariants N ⟶
      Rep.trivial ℚ (G ⧸ N) ℚ :=
    normalCoinvariantsInflationCounit N (Rep.trivial ℚ (G ⧸ N) ℚ)
  let : Mono e := by
    apply (Rep.mono_iff_injective e).mpr
    intro x y hxy
    induction x using Representation.Coinvariants.induction_on with
    | h x =>
      induction y using Representation.Coinvariants.induction_on with
      | h y => exact congrArg (Representation.Coinvariants.mk _) hxy
  let : Epi e := by
    apply (Rep.epi_iff_surjective e).mpr
    intro q
    exact ⟨Representation.Coinvariants.mk _ q, rfl⟩
  let : IsIso e := isIso_of_mono_of_epi e
  exact asIso e

end PolycyclicRecognition.RationalQuotient

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SequenceSubexponential
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Subexponential estimates along the actual sequence of profile scales -/

noncomputable section

namespace PolycyclicRecognition

open Filter
open scoped Topology

def HasSubexponentialLowerBoundSeq (scale f : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, Real.exp (-ε * scale n) ≤ f n

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_TransferredAction
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Transferring translations across a coarse inverse pair

For maps `f : H → X` and `r : X → H`, the maps `x ↦ f (h * r x)` form the
uniform quasi-action used in Proposition `recognition-from-height` of the
manuscript. These estimates retain the errors of the coarse inverse pair and
require only the stated metric inequalities.
-/

namespace PolycyclicRecognition

universe u v

variable {H : Type u} [Group H]
variable {X : Type v}

/-- The left translation by `h`, transferred using `f` and `r`. -/
def transferredMap (f : H → X) (r : X → H) (h : H) (x : X) : X :=
  f (h * r x)

@[simp]
theorem transferredMap_apply (f : H → X) (r : X → H) (h : H) (x : X) :
    transferredMap f r h x = f (h * r x) := rfl

variable [PseudoMetricSpace X]

variable [PseudoMetricSpace H]

/-- The error in the transferred action law is uniform in both group elements. -/
theorem transferredMap_mul_close (f : H → X) (r : X → H)
    (hleft : ∀ h a b : H, dist (h * a) (h * b) = dist a b)
    (K C E : ℝ) (hK : 0 ≤ K)
    (hf : ∀ a b, dist (f a) (f b) ≤ K * dist a b + C)
    (hrf : ∀ a, dist (r (f a)) a ≤ E) (h k : H) (x : X) :
    dist (transferredMap f r h (transferredMap f r k x))
      (transferredMap f r (h * k) x) ≤ K * E + C := by
  change dist (f (h * r (f (k * r x)))) (f ((h * k) * r x)) ≤ _
  rw [mul_assoc]
  calc
    dist (f (h * r (f (k * r x)))) (f (h * (k * r x))) ≤
        K * dist (h * r (f (k * r x))) (h * (k * r x)) + C := hf _ _
    _ = K * dist (r (f (k * r x))) (k * r x) + C := by rw [hleft]
    _ ≤ K * E + C :=
      add_le_add (mul_le_mul_of_nonneg_left (hrf (k * r x)) hK) le_rfl

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_TruncatedEnvelopingAlgebra
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite truncated enveloping algebra and its faithful generators

A given nilpotent representation bounds the truncation degree and certifies
injectivity. No PBW theorem or additional representation input is assumed.
-/

noncomputable section
namespace PolycyclicRecognition

open Module

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

attribute [local instance 100] LieRing.ofAssociativeRing

abbrev TruncatedEnvelopingAlgebra (R L : Type*) [CommRing R] [LieRing L]
    [LieAlgebra R L] (c : ℕ) :=
  (envelopingTruncationIdeal (R := R) (L := L) c).ringCon.Quotient

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_TwoImageLimits
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Simultaneous limits of two box embeddings

The bounded embeddings and their bounded generator preimages are retained
alongside the normalized Lie law. Thus every limiting generator belongs to
one of the limiting images, and the full alternating product is submersive.
-/

noncomputable section
namespace PolycyclicRecognition

open Set Metric Module Filter
open scoped Topology

abbrev TwoImageData (I : Type*) (n : ℕ) :=
  ((((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) × (I → Fin n → ℝ)) ×
    (((Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) × ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ)))) ×
      ((I → Fin n → ℝ) × (I → Fin n → ℝ))

def TwoImageData.generatorsCovered {I : Type*} {n : ℕ} (q : TwoImageData I n) : Prop :=
  ∀ i, q.1.2.1 (q.2.1 i) = q.1.1.2 i ∨ q.1.2.2 (q.2.2 i) = q.1.1.2 i

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_UniformCosetBound
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A finite tuple criterion for bounded subgroup index -/
noncomputable section
namespace PolycyclicRecognition
variable {G : Type} [Group G]

def CosetCollisionBound (H : Subgroup G) (b : ℕ) : Prop :=
  ∀ f : Fin (b + 1) → G, ∃ i j, i ≠ j ∧ (f i)⁻¹ * f j ∈ H

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_UnipotentGroupNilpotent
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Nilpotence from a faithful upper-unipotent representation

The entry filtration records the diagonal on which a matrix can first be
nonzero. Commutators advance this filtration. The finite matrix size then
bounds the lower central series of the represented group.
-/

namespace PolycyclicRecognition

open scoped commutatorElement

variable {n : ℕ} {R : Type*} [Ring R]

/-- Vanishing on all diagonals strictly below the `k`-th upper diagonal. -/
def MatrixDepth (k : ℕ) (X : Matrix (Fin n) (Fin n) R) : Prop :=
  ∀ i j : Fin n, (j : ℕ) < (i : ℕ) + k → X i j = 0

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ExponentialProductCoefficients
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive
attribute [-simp] _root_.OAI.PolycyclicRecognition.rationalWordAntipode_one _root_.OAI.PolycyclicRecognition.rationalWordDegree_one _root_.OAI.PolycyclicRecognition.wordAntipodeConvolution_tmul _root_.OAI.PolycyclicRecognition.wordDegreeConvolution_tmul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coefficients in a product of exponentials of distinct free letters -/

noncomputable section
namespace PolycyclicRecognition

open scoped BigOperators

local instance instDecidableEqFreeMonoidFin_solutions (n : ℕ) : DecidableEq (FreeMonoid (Fin n)) := Classical.decEq _

theorem rationalWordExponential_sum (c n : ℕ) (i : Fin n) :
    rationalWordExponential c n i =
      ∑ j : Fin (c + 1), MonoidAlgebra.single (FreeMonoid.of i ^ j.val)
        ((j.val.factorial : ℚ)⁻¹) := by
  rw [rationalWordExponential, Polynomial.aeval_def, PowerSeries.eval₂_trunc_eq_sum_range,
    ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  simp [PowerSeries.coeff_exp, rationalWordLetter, MonoidAlgebra.single_pow]

theorem ordered_single_product {M : Type*} [Monoid M] {n : ℕ}
    (w : Fin n → M) (q : Fin n → ℚ) :
    (List.ofFn (fun i => MonoidAlgebra.single (w i) (q i))).prod =
      MonoidAlgebra.single (List.ofFn w).prod (∏ i, q i) := by
  induction n with
  | zero => simp [MonoidAlgebra.one_def]
  | succ n ih =>
    simp only [List.ofFn_succ, List.prod_cons, ih, MonoidAlgebra.single_mul_single,
      Fin.prod_univ_succ]

theorem rationalExponentialProduct_sum (c n : ℕ) :
    rationalExponentialProduct c n =
      ∑ k : Fin n → Fin (c + 1),
        MonoidAlgebra.single (orderedPowerWord id (fun i => (k i).val))
          (∏ i, ((k i).val.factorial : ℚ)⁻¹) := by
  change (List.ofFn (fun i => rationalWordExponential c n i)).prod = _
  simp only [rationalWordExponential_sum]
  rw [ordered_product_sums]
  apply Finset.sum_congr rfl
  intro k _
  exact ordered_single_product _ _

theorem bounded_orderedPowerWord_injective (c n : ℕ) :
    Function.Injective (fun k : Fin n → Fin (c + 1) =>
      orderedPowerWord id (fun i => (k i).val)) := by
  intro k l h
  have he := orderedPowerWord_injective id Function.injective_id h
  funext i
  exact Fin.ext (congrFun he i)

theorem rationalExponentialProduct_coeff (c n : ℕ) (w : FreeMonoid (Fin n)) :
    (rationalExponentialProduct c n).coeff w =
      ∑ k : Fin n → Fin (c + 1),
        if orderedPowerWord id (fun i => (k i).val) = w
        then ∏ i, ((k i).val.factorial : ℚ)⁻¹ else 0 := by
  rw [rationalExponentialProduct_sum]
  simp only [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, MonoidAlgebra.coeff_single,
    Finsupp.single_apply]

theorem rationalExponentialProduct_ordered_coeff (c n : ℕ) (k : Fin n → Fin (c + 1)) :
    (rationalExponentialProduct c n).coeff (orderedPowerWord id (fun i => (k i).val)) =
      ∏ i, ((k i).val.factorial : ℚ)⁻¹ := by
  rw [rationalExponentialProduct_coeff]
  simp only [(bounded_orderedPowerWord_injective c n).eq_iff]
  simp

theorem rationalExponentialProduct_empty_coeff (c n : ℕ) :
    (rationalExponentialProduct c n).coeff 1 = 1 := by
  have h := rationalExponentialProduct_ordered_coeff c n (fun _ => 0)
  simpa [orderedPowerWord] using h

theorem rationalExponentialProduct_coefficient_bound (c n : ℕ) (w : FreeMonoid (Fin n)) :
    |(rationalExponentialProduct c n).coeff w| ≤ 1 := by
  by_cases hw : ∃ k : Fin n → Fin (c + 1), orderedPowerWord id (fun i => (k i).val) = w
  · obtain ⟨k, rfl⟩ := hw
    rw [rationalExponentialProduct_ordered_coeff, abs_of_nonneg]
    · calc
        _ ≤ ∏ _ : Fin n, (1 : ℚ) := Finset.prod_le_prod
          (fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _)) (fun i _ => by
            exact inv_le_one_of_one_le₀ (by exact_mod_cast Nat.factorial_pos (k i).val))
        _ = 1 := by simp
    · exact Finset.prod_nonneg (fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _))
  · rw [rationalExponentialProduct_coeff]
    have hz : (∑ k : Fin n → Fin (c + 1),
        if orderedPowerWord id (fun i => (k i).val) = w
        then ∏ i, ((k i).val.factorial : ℚ)⁻¹ else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      exact ite_eq_right (fun h => hw ⟨k, h⟩)
    rw [hz, abs_zero]
    exact zero_le_one

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_UniversalBCHCoefficientBound
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The uniform bound on the universal finite BCH coefficients -/

noncomputable section
namespace PolycyclicRecognition

theorem rationalExponentialProduct_sub_one_empty (c n : ℕ) :
    (rationalExponentialProduct c n - 1).coeff 1 = 0 := by
  simp [rationalExponentialProduct_empty_coeff, MonoidAlgebra.one_def]

theorem rationalExponentialProduct_sub_one_bound (c n : ℕ) (w : FreeMonoid (Fin n)) :
    |(rationalExponentialProduct c n - 1).coeff w| ≤ 1 := by
  by_cases hw : w = 1
  · subst w
    rw [rationalExponentialProduct_sub_one_empty, abs_zero]
    exact zero_le_one
  · simpa [MonoidAlgebra.one_def, hw, Ne.symm hw] using
      rationalExponentialProduct_coefficient_bound c n w

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ExponentialCoefficientStability
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Stable low-degree coefficients of the universal exponential product -/

noncomputable section
namespace PolycyclicRecognition

theorem freeMonoid_length_pow {I : Type*} (w : FreeMonoid I) (k : ℕ) :
    (w ^ k).length = k * w.length := by
  induction k with
  | zero => simp only [pow_zero, FreeMonoid.length_one, Nat.zero_mul]
  | succ k ih => rw [pow_succ, FreeMonoid.length_mul, ih, Nat.succ_mul]

theorem rationalWordExponential_succ (c n : ℕ) (i : Fin n) :
    rationalWordExponential (c + 1) n i = rationalWordExponential c n i +
      MonoidAlgebra.single (FreeMonoid.of i ^ (c + 1)) (((c + 1).factorial : ℚ)⁻¹) := by
  rw [rationalWordExponential_sum, Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last]
  rw [← rationalWordExponential_sum]

theorem rationalWordExponential_coefficient_stable {c d n : ℕ} (h : c ≤ d)
    (i : Fin n) (w : FreeMonoid (Fin n)) (hw : w.length ≤ c) :
    (rationalWordExponential c n i).coeff w = (rationalWordExponential d n i).coeff w := by
  classical
  induction d, h using Nat.le_induction with
  | base => rfl
  | succ d h ih =>
    rw [rationalWordExponential_succ, MonoidAlgebra.coeff_add, Finsupp.add_apply]
    have hne : FreeMonoid.of i ^ (d + 1) ≠ w := by
      intro he
      have hh := congrArg FreeMonoid.length he
      simp only [freeMonoid_length_pow, FreeMonoid.length_of, mul_one] at hh
      omega
    rw [MonoidAlgebra.coeff_single, Finsupp.single_eq_of_ne hne.symm, add_zero]
    exact ih

theorem rationalExponentialProduct_coefficient_stable {c d n : ℕ} (h : c ≤ d) :
    WordCoefficientAgreement (rationalExponentialProduct c n)
      (rationalExponentialProduct d n) (c + 1) := by
  apply wordCoefficientAgreement_ofFn_prod
  intro i w hw
  exact rationalWordExponential_coefficient_stable h i w (by omega)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_UniversalCoefficientStability
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Independence of the low-degree universal BCH coefficients

Increasing the finite exponential and logarithm truncations changes only
higher word degrees. Thus the universal coefficients can be restricted to
the actual nilpotency class.
-/

noncomputable section
namespace PolycyclicRecognition

theorem rationalUniversalLogarithm_stable {c d n : ℕ} (h : c ≤ d) :
    WordCoefficientAgreement (rationalUniversalLogarithm c n)
      (rationalUniversalLogarithm d n) (c + 1) := by
  have hp := (rationalExponentialProduct_coefficient_stable (n := n) h).sub
    (WordCoefficientAgreement.refl 1 (c + 1))
  intro w hw
  exact (hp.finiteLog c w hw).trans
    (finiteLog_coefficient_stable h (rationalExponentialProduct d n - 1)
      (rationalExponentialProduct_sub_one_empty d n) w (by omega))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_AffineAction
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact linear parts of a uniformly affine height quasi-action

A bounded error on a surjective real height quotient forces the linear parts
of a quasi-action to multiply exactly. This is the algebraic argument in
Proposition `prop:recognition-from-height` of *Quasi-isometric recognition of
virtually polycyclic groups*, Section 11.
-/

noncomputable section

namespace PolycyclicRecognition

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- A real linear map that is uniformly bounded on its entire domain vanishes. -/
theorem linear_eq_zero_of_uniform_bound (L : W →L[ℝ] W)
    (C : ℝ) (hC : ∀ w, ‖L w‖ ≤ C) : L = 0 := by
  have hC0 : 0 ≤ C := by simpa using hC 0
  ext w
  apply norm_eq_zero.mp
  by_contra hne
  have hp : 0 < ‖L w‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
  have ht : 0 < (C + 1) / ‖L w‖ := div_pos (by linarith) hp
  have h := hC (((C + 1) / ‖L w‖) • w)
  rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos ht,
    div_mul_cancel₀ _ (ne_of_gt hp)] at h
  linarith

/-- Two affine maps a bounded distance apart have identical linear parts. -/
theorem linear_parts_eq_of_bounded_affine_difference
    (L M : W →L[ℝ] W) (b : W) (C : ℝ)
    (h : ∀ w, ‖b + L w - M w‖ ≤ C) : L = M := by
  have hz : L - M = 0 := linear_eq_zero_of_uniform_bound (L - M) (C + ‖b‖) fun w => by
    calc
      ‖(L - M) w‖ = ‖(b + L w - M w) - b‖ := by congr 1; simp; abel
      _ ≤ ‖b + L w - M w‖ + ‖b‖ := norm_sub_le _ _
      _ ≤ C + ‖b‖ := add_le_add (h w) le_rfl
  exact sub_eq_zero.mp hz

variable {H X : Type*} [Group H]

/-- Height-coordinate data for a quasi-action. All geometric estimates are
recorded explicitly, and no exact action law for `F` is assumed. -/
structure HeightQuasiAction (H X W : Type*) [Group H]
    [NormedAddCommGroup W] [NormedSpace ℝ W] where
  height : X → W
  height_surjective : Function.Surjective height
  maps : H → X → X
  shift : H → W
  linear : H → W ≃L[ℝ] W
  error : ℝ
  error_nonneg : 0 ≤ error
  affine_error : ∀ h x,
    ‖height (maps h x) - (shift h + linear h (height x))‖ ≤ error
  composition_error : ℝ
  composition_nonneg : 0 ≤ composition_error
  composition_close : ∀ h k x,
    ‖height (maps h (maps k x)) - height (maps (h * k) x)‖ ≤ composition_error

namespace HeightQuasiAction

variable (Q : HeightQuasiAction H X W)

/-- The composition defect of the affine approximations has a bound independent
of the height argument. The bound may depend on the first linear map. -/
theorem affine_composition_bound (h k : H) (x : X) :
    ‖(Q.shift h + Q.linear h (Q.shift k) - Q.shift (h * k)) +
      Q.linear h (Q.linear k (Q.height x)) - Q.linear (h * k) (Q.height x)‖ ≤
      Q.error + ‖(Q.linear h).toContinuousLinearMap‖ * Q.error +
        Q.composition_error + Q.error := by
  let a := Q.height (Q.maps h (Q.maps k x))
  let b := Q.height (Q.maps (h * k) x)
  let c := Q.height (Q.maps k x)
  let u := Q.shift h + Q.linear h c
  let v := Q.shift h + Q.linear h (Q.shift k + Q.linear k (Q.height x))
  let z := Q.shift (h * k) + Q.linear (h * k) (Q.height x)
  have huv : ‖u - v‖ ≤ ‖(Q.linear h).toContinuousLinearMap‖ * Q.error := by
    calc
      ‖u - v‖ = ‖Q.linear h (c - (Q.shift k + Q.linear k (Q.height x)))‖ := by
        congr 1
        dsimp [u, v]
        rw [map_sub]
        abel
      _ ≤ ‖(Q.linear h).toContinuousLinearMap‖ *
          ‖c - (Q.shift k + Q.linear k (Q.height x))‖ :=
        (Q.linear h).toContinuousLinearMap.le_opNorm _
      _ ≤ ‖(Q.linear h).toContinuousLinearMap‖ * Q.error :=
        mul_le_mul_of_nonneg_left (Q.affine_error k x) (norm_nonneg _)
  have hva : ‖v - a‖ ≤ Q.error + ‖(Q.linear h).toContinuousLinearMap‖ * Q.error := by
    calc
      ‖v - a‖ ≤ ‖v - u‖ + ‖u - a‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ = ‖u - v‖ + ‖a - u‖ := by rw [norm_sub_rev v u, norm_sub_rev u a]
      _ ≤ ‖(Q.linear h).toContinuousLinearMap‖ * Q.error + Q.error :=
        add_le_add huv (Q.affine_error h (Q.maps k x))
      _ = _ := add_comm _ _
  have hvz : ‖v - z‖ ≤ Q.error + ‖(Q.linear h).toContinuousLinearMap‖ * Q.error +
      Q.composition_error + Q.error := by
    calc
      ‖v - z‖ ≤ ‖v - a‖ + ‖a - z‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ ‖v - a‖ + (‖a - b‖ + ‖b - z‖) :=
        add_le_add le_rfl (norm_sub_le_norm_sub_add_norm_sub a b z)
      _ ≤ (Q.error + ‖(Q.linear h).toContinuousLinearMap‖ * Q.error) +
          (Q.composition_error + Q.error) :=
        add_le_add hva (add_le_add (Q.composition_close h k x) (Q.affine_error (h * k) x))
      _ = _ := by ring
  convert hvz using 1
  all_goals try with_reducible_and_instances rfl
  dsimp [v, z]
  rw [map_add]
  congr 1
  abel

/-- Bounded quasi-action errors force the linear parts to compose exactly. -/
theorem linear_mul (h k : H) : Q.linear (h * k) = Q.linear h * Q.linear k := by
  have hc : (Q.linear h).toContinuousLinearMap.comp (Q.linear k).toContinuousLinearMap =
      (Q.linear (h * k)).toContinuousLinearMap := by
    apply linear_parts_eq_of_bounded_affine_difference _ _
      (Q.shift h + Q.linear h (Q.shift k) - Q.shift (h * k))
      (Q.error + ‖(Q.linear h).toContinuousLinearMap‖ * Q.error +
        Q.composition_error + Q.error)
    intro w
    obtain ⟨x, rfl⟩ := Q.height_surjective w
    exact Q.affine_composition_bound h k x
  ext w
  exact (congrArg (fun L : W →L[ℝ] W => L w) hc).symm

/-- The exact homomorphism of linear height parts. -/
def linearHom : H →* W ≃L[ℝ] W :=
  MonoidHom.mk' Q.linear Q.linear_mul

@[simp]
theorem linearHom_apply (h : H) : Q.linearHom h = Q.linear h := rfl

/-- Uniform defect bound for translations on the kernel of the linear action. -/
def translationDefect : ℝ :=
  Q.error + ‖(ContinuousLinearMap.id ℝ W)‖ * Q.error + Q.composition_error + Q.error

end HeightQuasiAction

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_LinearMetricChains
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Linear metric chains and coarse Lipschitz bounds

An explicit large-scale geodesic condition allows one to sum local bounds
along a chain. For continuous homomorphisms out of proper metric groups,
the local bound comes from compactness. This is the elementary metric step
in the proper cocompact homomorphism form of the Milnor--Švarc argument.
-/

noncomputable section

namespace PolycyclicRecognition

open Metric Set

variable {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]

/-- A uniform bound on single steps becomes an affine metric bound by
summing along the actual chains. -/
theorem LinearMetricChains.coarseLipschitz (C : LinearMetricChains X) (f : X → Y)
    {D : ℝ} (hD : 0 ≤ D)
    (hstep : ∀ x y, dist x y ≤ C.step → dist (f x) (f y) ≤ D) :
    ∀ x y, dist (f x) (f y) ≤ (D * C.slope) * dist x y + D * C.error := by
  intro x y
  obtain ⟨n, p, hp0, hpn, hn, hp⟩ := C.chain x y
  have hdist : dist (f (p 0)) (f (p n)) ≤ (n : ℝ) * D := by
    calc
      dist (f (p 0)) (f (p n)) ≤
          ∑ i ∈ Finset.range n, dist (f (p i)) (f (p (i + 1))) :=
        dist_le_range_sum_dist (f ∘ p) n
      _ ≤ ∑ _i ∈ Finset.range n, D := by
        exact Finset.sum_le_sum (fun i hi => hstep _ _ (hp i (Finset.mem_range.mp hi)))
      _ = (n : ℝ) * D := by simp
  rw [hp0, hpn] at hdist
  calc
    dist (f x) (f y) ≤ (n : ℝ) * D := hdist
    _ ≤ (C.slope * dist x y + C.error) * D := mul_le_mul_of_nonneg_right hn hD
    _ = (D * C.slope) * dist x y + D * C.error := by ring

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_MetricQuasiEquivalence
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Composing the metric comparisons in a Lie-model reduction

The proper cocompact homomorphism reduction has arrows in both directions.
We keep actual coarse inverse maps and their affine bounds, so that the
three-arrow zigzag can be composed without assuming a recognition result.
-/

noncomputable section

namespace PolycyclicRecognition

/-- Actual coarse inverse maps with affine metric bounds in both directions. -/
structure MetricQuasiEquivalence (X Y : Type*) [PseudoMetricSpace X] [PseudoMetricSpace Y] where
  toFun : X → Y
  invFun : Y → X
  toFun_control : ∃ K C : ℝ, 0 ≤ K ∧ 0 ≤ C ∧
    ∀ x y, dist (toFun x) (toFun y) ≤ K * dist x y + C
  invFun_control : ∃ K C : ℝ, 0 ≤ K ∧ 0 ≤ C ∧
    ∀ x y, dist (invFun x) (invFun y) ≤ K * dist x y + C
  left_close : ∃ E : ℝ, 0 ≤ E ∧ ∀ x, dist x (invFun (toFun x)) ≤ E
  right_close : ∃ E : ℝ, 0 ≤ E ∧ ∀ y, dist y (toFun (invFun y)) ≤ E

namespace MetricQuasiEquivalence

variable {X Y Z : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y] [PseudoMetricSpace Z]

/-- Reverse a comparison using its specified coarse inverse. -/
def symm (e : MetricQuasiEquivalence X Y) : MetricQuasiEquivalence Y X where
  toFun := e.invFun
  invFun := e.toFun
  toFun_control := e.invFun_control
  invFun_control := e.toFun_control
  left_close := e.right_close
  right_close := e.left_close

/-- Compose actual comparisons, including explicit bounds for the errors
of their composite inverse maps. -/
def trans (e : MetricQuasiEquivalence X Y) (e' : MetricQuasiEquivalence Y Z) :
    MetricQuasiEquivalence X Z where
  toFun := e'.toFun ∘ e.toFun
  invFun := e.invFun ∘ e'.invFun
  toFun_control := by
    obtain ⟨K, C, hK, hC, hf⟩ := e.toFun_control
    obtain ⟨K', C', hK', hC', hf'⟩ := e'.toFun_control
    refine ⟨K' * K, K' * C + C', mul_nonneg hK' hK,
      add_nonneg (mul_nonneg hK' hC) hC', fun x y => ?_⟩
    calc
      dist (e'.toFun (e.toFun x)) (e'.toFun (e.toFun y))
          ≤ K' * dist (e.toFun x) (e.toFun y) + C' := hf' _ _
      _ ≤ K' * (K * dist x y + C) + C' := by gcongr; exact hf x y
      _ = (K' * K) * dist x y + (K' * C + C') := by ring
  invFun_control := by
    obtain ⟨K, C, hK, hC, hf⟩ := e.invFun_control
    obtain ⟨K', C', hK', hC', hf'⟩ := e'.invFun_control
    refine ⟨K * K', K * C' + C, mul_nonneg hK hK',
      add_nonneg (mul_nonneg hK hC') hC, fun x y => ?_⟩
    calc
      dist (e.invFun (e'.invFun x)) (e.invFun (e'.invFun y))
          ≤ K * dist (e'.invFun x) (e'.invFun y) + C := hf _ _
      _ ≤ K * (K' * dist x y + C') + C := by gcongr; exact hf' x y
      _ = (K * K') * dist x y + (K * C' + C) := by ring
  left_close := by
    obtain ⟨E, hE, he⟩ := e.left_close
    obtain ⟨E', hE', he'⟩ := e'.left_close
    obtain ⟨K, C, hK, hC, hf⟩ := e.invFun_control
    refine ⟨E + (K * E' + C), add_nonneg hE (add_nonneg (mul_nonneg hK hE') hC),
      fun x => ?_⟩
    calc
      dist x (e.invFun (e'.invFun (e'.toFun (e.toFun x))))
          ≤ dist x (e.invFun (e.toFun x)) +
              dist (e.invFun (e.toFun x))
                (e.invFun (e'.invFun (e'.toFun (e.toFun x)))) := dist_triangle _ _ _
      _ ≤ E + (K * E' + C) := by
        exact add_le_add (he x) ((hf _ _).trans
          (add_le_add (mul_le_mul_of_nonneg_left (he' (e.toFun x)) hK) le_rfl))
  right_close := by
    obtain ⟨E, hE, he⟩ := e.right_close
    obtain ⟨E', hE', he'⟩ := e'.right_close
    obtain ⟨K, C, hK, hC, hf⟩ := e'.toFun_control
    refine ⟨E' + (K * E + C), add_nonneg hE' (add_nonneg (mul_nonneg hK hE) hC),
      fun y => ?_⟩
    calc
      dist y (e'.toFun (e.toFun (e.invFun (e'.invFun y))))
          ≤ dist y (e'.toFun (e'.invFun y)) +
              dist (e'.toFun (e'.invFun y))
                (e'.toFun (e.toFun (e.invFun (e'.invFun y)))) := dist_triangle _ _ _
      _ ≤ E' + (K * E + C) := by
        exact add_le_add (he' y) ((hf _ _).trans
          (add_le_add (mul_le_mul_of_nonneg_left (he (e'.invFun y)) hK) le_rfl))

/-- Choose a coarse inverse from the coarse-surjectivity part of a
quasi-isometry, and prove its affine bound using the lower inequality. -/
def ofQuasiIsometry (f : X → Y) {K C K' C' E : ℝ}
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hK' : 0 ≤ K') (hC' : 0 ≤ C') (hE : 0 ≤ E)
    (hupper : ∀ x y, dist (f x) (f y) ≤ K * dist x y + C)
    (hlower : ∀ x y, dist x y ≤ K' * dist (f x) (f y) + C')
    (hsurj : ∀ y, ∃ x, dist y (f x) ≤ E) : MetricQuasiEquivalence X Y := by
  choose r hr using hsurj
  refine ⟨f, r, ⟨K, C, hK, hC, hupper⟩, ?_, ?_, ⟨E, hE, hr⟩⟩
  · refine ⟨K', K' * (E + E) + C', hK',
      add_nonneg (mul_nonneg hK' (add_nonneg hE hE)) hC', fun x y => ?_⟩
    have hd : dist (f (r x)) (f (r y)) ≤ dist x y + (E + E) := by
      calc
        dist (f (r x)) (f (r y)) ≤
            dist (f (r x)) x + dist x y + dist y (f (r y)) := dist_triangle4 _ _ _ _
        _ ≤ E + dist x y + E := by
          exact add_le_add (add_le_add ((dist_comm _ _).trans_le (hr x)) le_rfl) (hr y)
        _ = dist x y + (E + E) := by ring
    calc
      dist (r x) (r y) ≤ K' * dist (f (r x)) (f (r y)) + C' := hlower _ _
      _ ≤ K' * (dist x y + (E + E)) + C' := by gcongr
      _ = K' * dist x y + (K' * (E + E) + C') := by ring
  · refine ⟨K' * E + C', add_nonneg (mul_nonneg hK' hE) hC', fun x => ?_⟩
    exact (hlower x (r (f x))).trans
      (add_le_add (mul_le_mul_of_nonneg_left (hr (f x)) hK') le_rfl)

end MetricQuasiEquivalence

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CoarseEquivalenceMetric
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive
attribute [-simp] _root_.OAI.PolycyclicRecognition.controlledCochainMap_apply _root_.OAI.PolycyclicRecognition.controlledCochainPullback_apply _root_.OAI.PolycyclicRecognition.controlledPrismHom_succ _root_.OAI.PolycyclicRecognition.controlledPrismTerm_apply _root_.OAI.PolycyclicRecognition.controlledPrism_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Passing from finite-difference control to metric coarse inverses -/

noncomputable section
namespace PolycyclicRecognition

open Metric Set

variable {G H : Type*} [Group G] [Group H] [MetricSpace G] [MetricSpace H]
  [IsIsometricSMul G G] [IsIsometricSMul H H]

theorem GroupBornologous.bounded_metric_steps {f : G → H}
    (hf : GroupBornologous f)
    (hfinite : ∀ R : ℝ, (closedBall (1 : G) R).Finite) (R : ℝ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x y, dist x y ≤ R → dist (f x) (f y) ≤ D := by
  obtain ⟨T, hT, hmap⟩ := hf _ (hfinite R)
  obtain ⟨D, hD⟩ := hT.isBounded.subset_closedBall (1 : H)
  refine ⟨max D 0, le_max_right _ _, fun x y hxy => ?_⟩
  have hx : x⁻¹ * y ∈ closedBall (1 : G) R := by
    simpa only [mem_closedBall, dist_comm (x⁻¹ * y), dist_one_groupDifference] using hxy
  have hd := hD (hmap x y hx)
  rw [mem_closedBall, dist_comm, dist_one_groupDifference] at hd
  exact hd.trans (le_max_left _ _)

theorem GroupBornologous.coarseLipschitz {f : G → H}
    (hf : GroupBornologous f) (C : LinearMetricChains G)
    (hfinite : ∀ R : ℝ, (closedBall (1 : G) R).Finite) :
    ∃ K B : ℝ, 0 ≤ K ∧ 0 ≤ B ∧
      ∀ x y, dist (f x) (f y) ≤ K * dist x y + B := by
  obtain ⟨D, hD, hstep⟩ := hf.bounded_metric_steps hfinite C.step
  exact ⟨D * C.slope, D * C.error, mul_nonneg hD C.slope_nonneg,
    mul_nonneg hD C.error_nonneg, C.coarseLipschitz f hD hstep⟩

theorem finite_groupDifference_bounded_error {r : G → G}
    (hr : (range fun x => x⁻¹ * r x).Finite) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ x, dist x (r x) ≤ E := by
  obtain ⟨E, hE⟩ := hr.isBounded.subset_closedBall (1 : G)
  refine ⟨max E 0, le_max_right _ _, fun x => ?_⟩
  have hx := hE (mem_range_self x)
  rw [mem_closedBall, dist_comm, dist_one_groupDifference] at hx
  exact hx.trans (le_max_left _ _)

/-- On metrics with linear chains and finite balls, an actual discrete
coarse equivalence is a metric quasi-equivalence. -/
def GroupCoarseEquivalence.metric (e : GroupCoarseEquivalence G H)
    (CG : LinearMetricChains G) (CH : LinearMetricChains H)
    (hG : ∀ R : ℝ, (closedBall (1 : G) R).Finite)
    (hH : ∀ R : ℝ, (closedBall (1 : H) R).Finite) : MetricQuasiEquivalence G H where
  toFun := e.toFun
  invFun := e.invFun
  toFun_control := e.bornologous_toFun.coarseLipschitz CG hG
  invFun_control := e.bornologous_invFun.coarseLipschitz CH hH
  left_close := finite_groupDifference_bounded_error e.left_error
  right_close := finite_groupDifference_bounded_error e.right_error

/-- An isomorphism is also a discrete coarse equivalence, with exact inverses. -/
def MulEquiv.groupCoarseEquivalence (e : G ≃* H) : GroupCoarseEquivalence G H where
  toFun := e
  invFun := e.symm
  bornologous_toFun := groupBornologous_hom e.toMonoidHom
  bornologous_invFun := groupBornologous_hom e.symm.toMonoidHom
  left_error := by simp
  right_error := by simp

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CoarsePathConcatenation
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coarse metric bounds under path concatenation

The additive error is retained explicitly. This allows logarithmic-diameter
switches and coarse-speed one-parameter legs to use a fixed finite mesh.
-/

namespace PolycyclicRecognition

open scoped unitInterval

variable {X : Type*} [PseudoMetricSpace X] {x y z : X}

def PathMetricBound (p : Path x y) (L κ : ℝ) : Prop :=
  ∀ s t : unitInterval, dist (p s) (p t) ≤ L * |(s : ℝ) - t| + κ

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CommutingIntegralHom
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The homomorphism determined by commuting integral generators -/

noncomputable section
namespace PolycyclicRecognition
open scoped IsMulCommutative
variable {H : Type} [Group H] {n : ℕ}

def commutingIntegralHom (a : Fin n → H) (ha : ∀ i j, Commute (a i) (a j)) :
    IntegralLatticeGroup n →* H := by
  classical
  let K := Subgroup.closure (Set.range a)
  have hc : (Set.range a).Pairwise Commute := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _
    exact ha i j
  -- d13f23b's lemma takes `Set.Pairwise Commute`; ours, commutation of every pair
  letI : IsMulCommutative K := Subgroup.isMulCommutative_closure fun x hx y hy =>
    (em (x = y)).elim (fun h => h ▸ rfl) (fun h => hc hx hy h)
  let b : Fin n → K := fun i => ⟨a i, Subgroup.subset_closure (Set.mem_range_self i)⟩
  let f : IntegralLatticeGroup n →* K :=
    { toFun := fun z => ∏ i, b i ^ z.toAdd i
      map_one' := by simp
      map_mul' := by
        intro z w
        change (∏ i, b i ^ (z.toAdd i + w.toAdd i)) = _
        simp only [zpow_add, Finset.prod_mul_distrib] }
  exact K.subtype.comp f

@[simp] theorem commutingIntegralHom_generator
    (a : Fin n → H) (ha : ∀ i j, Commute (a i) (a j)) (j : Fin n) :
    commutingIntegralHom a ha (integralLatticeGenerator n j) = a j := by
  classical
  unfold commutingIntegralHom
  simp only [MonoidHom.comp_apply, integralLatticeGenerator,
    Pi.basisFun_apply]
  simp [Pi.single_apply]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_LieModelMetric
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Compatible metrics for the solvable Lie model

The metric existence input is the precise specialization of Cornulier–de
la Harpe, *Metric Geometry of Locally Compact Groups*, EMS Tracts in
Mathematics 25 (2016), Proposition 4.B.9, p.108: a second-countable locally
compact group is compactly generated if and only if it admits a proper
compatible left-invariant large-scale-geodesic metric.

We prove compact generation from a compact identity neighborhood and
connectedness. The metric-existence input is separate from Dekimpe's
lattice-realization theorem and contains no recognition assertion.
-/

noncomputable section

namespace PolycyclicRecognition

open Set Filter Topology
open scoped Manifold

namespace ProperChainMetric

variable {G : Type*} [Group G] [TopologicalSpace G] (d : ProperChainMetric G)

theorem compatibleMetric_eq : d.compatibleMetric = d.metric :=
  d.metric.replaceTopology_eq d.topology_eq.symm

def chains_compatibleMetric : letI := d.compatibleMetric; LinearMetricChains G := by
  rw [d.compatibleMetric_eq]
  exact d.chains

end ProperChainMetric

/-- Any compact identity neighborhood in a connected topological group
generates the entire group. -/
theorem closure_eq_top_of_mem_nhds_one
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [ConnectedSpace G] {K : Set G} (hK : K ∈ 𝓝 (1 : G)) :
    Subgroup.closure K = ⊤ := by
  let J := Subgroup.closure K
  have hopen : IsOpen (J : Set G) := J.isOpen_of_mem_nhds
    (Filter.mem_of_superset hK Subgroup.subset_closure)
  have hclopen : IsClopen (J : Set G) := ⟨J.isClosed_of_isOpen hopen, hopen⟩
  have hall : (J : Set G) = Set.univ := hclopen.eq_univ ⟨1, J.one_mem⟩
  exact SetLike.coe_injective hall

/-- A connected locally compact group has a compact generating set. -/
theorem exists_compact_generating_set
    (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [ConnectedSpace G] [LocallyCompactSpace G] :
    ∃ K : Set G, IsCompact K ∧ Subgroup.closure K = ⊤ := by
  obtain ⟨K, hK, hnhds⟩ := exists_compact_mem_nhds (1 : G)
  exact ⟨K, hK, closure_eq_top_of_mem_nhds_one hnhds⟩

/-- The implication (i)⇒(ii) of Cornulier–de la Harpe (2016),
Proposition 4.B.9, with the chain witnesses retained. -/
def GeodesicMetricExistenceInput : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G],
    (∃ K : Set G, IsCompact K ∧ Subgroup.closure K = ⊤) →
      Nonempty (ProperChainMetric G)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_TriangulableLieModel
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The published reduction to a real-triangulable Lie model

Y. Cornulier and R. Tessera, *Geometric presentations of Lie groups and
their Dehn functions*, Publications Mathématiques de l'IHÉS 125 (2017),
79–219, Lemma 3.A.1, p.108, gives proper continuous homomorphisms with
cocompact images `G ← G₁ → G₂ ← G₃`, with `G₃` real triangulable.
Definition 1.1, p.83, identifies this last property with being isomorphic
to a closed connected group of invertible upper triangular real matrices.

The input below keeps precisely that topological reduction. Its metric
consequence is proved using the separately identified compatible-metric
existence input and the explicit inverse-map composition lemmas. No
adjoint basis, height control, or recognition conclusion is placed in the
published input.
-/

noncomputable section

namespace PolycyclicRecognition

/-- The actual closed triangular matrix realization from CT Definition 1.1. -/
def IsRealTriangulable (S : SimplyConnectedSolvableLieModel) : Prop :=
  ∃ (n : ℕ) (ρ : S.carrier →* Matrix.GeneralLinearGroup (Fin n) ℝ),
    Topology.IsClosedEmbedding ρ ∧
      ∀ g, (ρ g : Matrix (Fin n) (Fin n) ℝ).IsUpperTriangular

/-- A proper continuous homomorphism whose image has a compact coset
cover, the cocompactness condition in the CT arrows. -/
structure ProperCocompactHom (A B : Type*) [Group A] [Group B]
    [TopologicalSpace A] [TopologicalSpace B] where
  hom : A →* B
  proper : IsProperMap hom
  cover : ∃ K : Set B, IsCompact K ∧
    ∀ b : B, ∃ (a : A) (k : B), k ∈ K ∧ hom a * k = b

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CompactExtensionModels
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The locally compact models in the compact-extension comparison -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold
attribute [local instance] semidirectProductTopology

def ProperCocompactHom.id (G : Type*) [Group G] [TopologicalSpace G] : ProperCocompactHom G G where
  hom := MonoidHom.id G
  proper := isProperMap_id
  cover := ⟨{1},isCompact_singleton,fun g => ⟨g,1,Set.mem_singleton _,mul_one g⟩⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_MetricTent
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compact metric cutoffs for controlled Følner pairs -/

noncomputable section
namespace PolycyclicRecognition

open Metric Set MeasureTheory

variable {X : Type*} [MetricSpace X]

def metricTent (S : Set X) (r : ℝ) (x : X) : ℝ := max (1 - infDist x S / r) 0

theorem metricTent_nonneg (S : Set X) (r : ℝ) (x : X) : 0 ≤ metricTent S r x :=
  le_max_right _ _

theorem metricTent_eq_one {S : Set X} (r : ℝ) {x : X} (hx : x ∈ S) :
    metricTent S r x = 1 := by simp [metricTent, infDist_zero_of_mem hx]

theorem continuous_metricTent (S : Set X) (r : ℝ) : Continuous (metricTent S r) :=
  (continuous_const.sub ((continuous_infDist_pt S).div_const r)).max continuous_const

theorem abs_metricTent_sub_le (S : Set X) {r : ℝ} (hr : 0 < r) (x y : X) :
    |metricTent S r x - metricTent S r y| ≤ dist x y / r := by
  calc
    _ ≤ |(1 - infDist x S / r) - (1 - infDist y S / r)| :=
      abs_max_sub_max_le_abs _ _ 0
    _ = |infDist x S - infDist y S| / r := by
      have he : (1 - infDist x S / r) - (1 - infDist y S / r) =
          -(infDist x S - infDist y S) / r := by ring
      rw [he, abs_div, abs_neg, abs_of_pos hr]
    _ ≤ dist x y / r := div_le_div_of_nonneg_right
      (by simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using
        (lipschitz_infDist_pt S).dist_le_mul x y) hr.le

theorem metricTent_support_subset {S : Set X} (hS : S.Nonempty) {r : ℝ} (hr : 0 < r) :
    Function.support (metricTent S r) ⊆ cthickening r S := by
  intro x hx
  have hpos : 0 < metricTent S r x := lt_of_le_of_ne
    (metricTent_nonneg S r x) (Ne.symm hx)
  have hd : infDist x S < r := by
    have h : 0 < 1 - infDist x S / r := (lt_max_iff.mp hpos).resolve_right (lt_irrefl 0)
    exact (div_lt_one hr).mp (by linarith)
  exact thickening_subset_cthickening r S ((mem_thickening_iff_infDist_lt hS).2 hd)

theorem metricTent_compact_support [ProperSpace X] {S : Set X}
    (hS : IsCompact S) (hne : S.Nonempty) {r : ℝ} (hr : 0 < r) :
    HasCompactSupport (metricTent S r) :=
  (hS.cthickening (r := r)).of_isClosed_subset (isClosed_tsupport _)
    (closure_minimal (metricTent_support_subset hne hr) isClosed_cthickening)

variable [ProperSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsFiniteMeasureOnCompacts μ]

theorem metricTent_integral_lower {S : Set X} (hS : IsCompact S) (hne : S.Nonempty)
    {r : ℝ} (hr : 0 < r) : μ.real S ≤ ∫ x, metricTent S r x ∂μ := by
  have hi := (continuous_metricTent S r).integrable_of_hasCompactSupport
    (metricTent_compact_support hS hne hr) (μ := μ)
  calc
    μ.real S = ∫ x in S, metricTent S r x ∂μ := by
      rw [setIntegral_congr_fun hS.measurableSet (fun x hx => metricTent_eq_one r hx)]
      simp
    _ ≤ ∫ x, metricTent S r x ∂μ :=
      setIntegral_le_integral hi (Filter.Eventually.of_forall (metricTent_nonneg S r))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_NormalizedMetricTent
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Normalized inverse-coordinate metric cutoffs -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Metric Set

variable {G : Type*} [Group G] [MetricSpace G] [IsTopologicalGroup G]
  [IsIsometricSMul G G] [ProperSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [μ.IsInvInvariant]

def normalizedMetricTent (S : Set G) (r : ℝ) (x : G) : ℝ :=
  metricTent S r x⁻¹ / (∫ y, metricTent S r y ∂μ)

omit [Group G] [IsTopologicalGroup G] [IsIsometricSMul G G] [μ.IsInvInvariant] in
theorem metricTent_mass_pos {S : Set G} (hS : IsCompact S) (hne : S.Nonempty)
    (hμ : 0 < μ.real S) {r : ℝ} (hr : 0 < r) :
    0 < ∫ y, metricTent S r y ∂μ :=
  hμ.trans_le (metricTent_integral_lower μ hS hne hr)

omit [IsIsometricSMul G G] [ProperSpace G] [BorelSpace G]
  [IsFiniteMeasureOnCompacts μ] [μ.IsInvInvariant] in
theorem continuous_normalizedMetricTent (S : Set G) (r : ℝ) :
    Continuous (normalizedMetricTent μ S r) :=
  ((continuous_metricTent S r).comp continuous_inv).div_const _

omit [IsIsometricSMul G G] [BorelSpace G] [IsFiniteMeasureOnCompacts μ] [μ.IsInvInvariant] in
theorem normalizedMetricTent_compact_support {S : Set G} (hS : IsCompact S)
    (hne : S.Nonempty) {r : ℝ} (hr : 0 < r) :
    HasCompactSupport (normalizedMetricTent μ S r) := by
  have h := (metricTent_compact_support hS hne hr).comp_homeomorph (Homeomorph.inv G)
  apply h.mono
  intro x hx
  change metricTent S r x⁻¹ ≠ 0
  intro hz
  apply hx
  change metricTent S r x⁻¹ / _ = 0
  rw [hz, zero_div]

omit [IsTopologicalGroup G] [IsIsometricSMul G G] [ProperSpace G] [BorelSpace G]
  [IsFiniteMeasureOnCompacts μ] [μ.IsInvInvariant] in
theorem normalizedMetricTent_nonneg (S : Set G) (r : ℝ) (x : G) :
    0 ≤ normalizedMetricTent μ S r x :=
  div_nonneg (metricTent_nonneg _ _ _) (integral_nonneg (metricTent_nonneg S r))

omit [IsIsometricSMul G G] in
theorem integral_normalizedMetricTent {S : Set G} (hS : IsCompact S)
    (hne : S.Nonempty) (hμ : 0 < μ.real S) {r : ℝ} (hr : 0 < r) :
    ∫ x, normalizedMetricTent μ S r x ∂μ = 1 := by
  simp only [normalizedMetricTent]
  rw [integral_div, integral_inv_eq_self]
  exact div_self (metricTent_mass_pos μ hS hne hμ hr).ne'

omit [IsTopologicalGroup G] [μ.IsInvInvariant] in
theorem normalizedMetricTent_translation_bound {S : Set G} (hS : IsCompact S)
    (hne : S.Nonempty) (hμ : 0 < μ.real S) {r : ℝ} (hr : 0 < r) (q x : G) :
    |normalizedMetricTent μ S r (q⁻¹ * x) - normalizedMetricTent μ S r x| ≤
      dist 1 q / (r * (∫ y, metricTent S r y ∂μ)) := by
  have hmass := metricTent_mass_pos μ hS hne hμ hr
  have hd : dist (x⁻¹ * q) x⁻¹ = dist 1 q := by
    simpa only [mul_one, dist_comm] using dist_mul_left x⁻¹ q (1 : G)
  calc
    _ = |metricTent S r (x⁻¹ * q) - metricTent S r x⁻¹| /
        (∫ y, metricTent S r y ∂μ) := by
      simp only [normalizedMetricTent, mul_inv_rev, inv_inv, ← sub_div, abs_div,
        abs_of_pos hmass]
    _ ≤ (dist 1 q / r) / (∫ y, metricTent S r y ∂μ) :=
      div_le_div_of_nonneg_right (by simpa only [hd] using abs_metricTent_sub_le S hr (x⁻¹ * q) x⁻¹)
        hmass.le
    _ = _ := by rw [div_div]

omit [IsTopologicalGroup G] [ProperSpace G] [BorelSpace G]
  [IsFiniteMeasureOnCompacts μ] [μ.IsInvInvariant] in
theorem normalizedMetricTent_translation_support {S : Set G} (hS : S.Nonempty)
    {r : ℝ} (hr : 0 < r) {q : G} (hq : dist 1 q ≤ r) :
    Function.support (fun x => normalizedMetricTent μ S r (q⁻¹ * x) -
      normalizedMetricTent μ S r x) ⊆ Inv.inv ⁻¹' cthickening (2 * r) S := by
  intro x hx
  have ht : infDist x⁻¹ S < 2 * r := by
    by_cases h0 : metricTent S r x⁻¹ = 0
    · have h1 : metricTent S r (x⁻¹ * q) ≠ 0 := by
        intro hh
        exact hx (by simp [normalizedMetricTent, mul_inv_rev, h0, hh])
      have hp : 0 < metricTent S r (x⁻¹ * q) :=
        lt_of_le_of_ne (metricTent_nonneg _ _ _) h1.symm
      have hi : infDist (x⁻¹ * q) S < r := by
        have he := (lt_max_iff.mp hp).resolve_right (lt_irrefl 0)
        exact (div_lt_one hr).1 (by linarith)
      have hd : dist x⁻¹ (x⁻¹ * q) = dist 1 q := by
        simpa only [mul_one] using dist_mul_left x⁻¹ (1 : G) q
      have hdist := infDist_le_infDist_add_dist (s := S) (x := x⁻¹) (y := x⁻¹ * q)
      rw [hd] at hdist
      linarith
    · have hp := lt_of_le_of_ne (metricTent_nonneg S r x⁻¹) (Ne.symm h0)
      have he := (lt_max_iff.mp hp).resolve_right (lt_irrefl 0)
      have hi := (div_lt_one hr).1 (show infDist x⁻¹ S / r < 1 by linarith)
      linarith
  exact thickening_subset_cthickening _ S ((mem_thickening_iff_infDist_lt hS).2 ht)

theorem normalizedMetricTent_translation_integral_le {S : Set G} (hS : IsCompact S)
    (hne : S.Nonempty) (hμ : 0 < μ.real S) {r : ℝ} (hr : 0 < r)
    {q : G} (hq : dist 1 q ≤ r) :
    (∫ x, |normalizedMetricTent μ S r (q⁻¹ * x) - normalizedMetricTent μ S r x| ∂μ) ≤
      dist 1 q / (r * (∫ y, metricTent S r y ∂μ)) * μ.real (cthickening (2 * r) S) := by
  let f := fun x => |normalizedMetricTent μ S r (q⁻¹ * x) - normalizedMetricTent μ S r x|
  let K := Inv.inv ⁻¹' cthickening (2 * r) S
  have hK : IsCompact K := (Homeomorph.inv G).isClosedEmbedding.isCompact_preimage hS.cthickening
  have he : (∫ x in K, f x ∂μ) = ∫ x, f x ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (by
      intro x hx
      have hz : normalizedMetricTent μ S r (q⁻¹ * x) - normalizedMetricTent μ S r x = 0 := by
        by_contra hz
        exact hx (normalizedMetricTent_translation_support μ hne hr hq hz)
      exact abs_eq_zero.mpr hz)
  have hbound := norm_setIntegral_le_of_norm_le_const (f := f) (μ := μ) (s := K) hK.measure_lt_top
    (fun x (_hx : x ∈ K) => by
      simpa only [f, Real.norm_eq_abs, abs_abs] using
        normalizedMetricTent_translation_bound μ hS hne hμ hr q x)
  rw [he, Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun x => abs_nonneg _))] at hbound
  have hmeasure : μ.real K = μ.real (cthickening (2 * r) S) :=
    congrArg ENNReal.toReal (Measure.measure_preimage_inv μ _)
  simpa only [hmeasure] using hbound

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ControlledMetricFolner
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compact Følner pairs supply controlled averaging densities

Only a bounded volume ratio between a compact set and its thickening is
needed. Normalized inverse-coordinate tents produce continuous probability
densities with the required support and translation estimates.
-/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Metric Set Filter

variable {G : Type*} [Group G] [MetricSpace G] [IsTopologicalGroup G]
  [IsIsometricSMul G G] [ProperSpace G] [MeasurableSpace G] [BorelSpace G]

structure ControlledMetricFolnerPairs (μ : Measure G) where
  scale : ℕ → ℝ
  scale_pos : ∀ n, 0 < scale n
  scale_tendsto : Tendsto scale atTop atTop
  sets : ℕ → Set G
  compact : ∀ n, IsCompact (sets n)
  nonempty : ∀ n, (sets n).Nonempty
  positive : ∀ n, 0 < μ.real (sets n)
  radiusConstant : ℝ
  radius_nonneg : 0 ≤ radiusConstant
  radius_bound : ∀ n x, x ∈ sets n → dist 1 x ≤ radiusConstant * scale n
  volumeConstant : ℝ
  volume_nonneg : 0 ≤ volumeConstant
  volume_bound : ∀ n, μ.real (cthickening (2 * scale n) (sets n)) ≤
    volumeConstant * μ.real (sets n)

variable (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [μ.IsInvInvariant]

def ControlledMetricFolnerPairs.toReiter (F : ControlledMetricFolnerPairs μ) :
    ControlledReiterFamily μ (fun g => dist 1 g) where
  scale := F.scale
  scale_pos := F.scale_pos
  scale_tendsto := F.scale_tendsto
  weight n := normalizedMetricTent μ (F.sets n) (F.scale n)
  continuous_weight n := continuous_normalizedMetricTent μ _ _
  compact_support n := normalizedMetricTent_compact_support μ (F.compact n)
    (F.nonempty n) (F.scale_pos n)
  nonneg n x := normalizedMetricTent_nonneg μ _ _ x
  mass n := integral_normalizedMetricTent μ (F.compact n) (F.nonempty n)
    (F.positive n) (F.scale_pos n)
  control Q hQ := by
    obtain ⟨D₀, hD₀⟩ := hQ.exists_bound_of_continuousOn
      (continuous_const.dist continuous_id).continuousOn
    let D := max D₀ 0
    have hD : 0 ≤ D := le_max_right _ _
    have hdist (q : G) (hq : q ∈ Q) : dist 1 q ≤ D := by
      have h := hD₀ q hq
      simpa only [D, id_eq, Real.norm_eq_abs, abs_of_nonneg dist_nonneg] using
        h.trans (le_max_left D₀ 0)
    refine ⟨F.radiusConstant + 2, D * F.volumeConstant, by linarith [F.radius_nonneg],
      mul_nonneg hD F.volume_nonneg, ?_⟩
    filter_upwards [F.scale_tendsto.eventually (eventually_ge_atTop D)] with n hn
    intro q hq
    have hr := F.scale_pos n
    have hqr : dist 1 q ≤ F.scale n := (hdist q hq).trans hn
    have hm := metricTent_mass_pos μ (F.compact n) (F.nonempty n) (F.positive n) hr
    refine ⟨?_, ?_⟩
    · intro x hx
      have hmem := normalizedMetricTent_translation_support μ (F.nonempty n) hr hqr hx
      change infEDist x⁻¹ (F.sets n) ≤ ENNReal.ofReal (2 * F.scale n) at hmem
      have hi : infDist x⁻¹ (F.sets n) ≤ 2 * F.scale n := by
        have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmem
        simpa only [infDist, ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * F.scale n)] using h
      obtain ⟨y, hy, he⟩ := (F.compact n).exists_infDist_eq_dist (F.nonempty n) x⁻¹
      have hinv : dist 1 x = dist 1 x⁻¹ := by
        calc
          dist 1 x = dist x⁻¹ 1 := by
            simpa only [mul_one, inv_mul_cancel] using (dist_mul_left x⁻¹ (1 : G) x).symm
          _ = dist 1 x⁻¹ := dist_comm _ _
      rw [hinv]
      have htri := dist_triangle (1 : G) y x⁻¹
      rw [dist_comm y x⁻¹, ← he] at htri
      have hyb := F.radius_bound n y hy
      nlinarith
    · have hfirst := normalizedMetricTent_translation_integral_le μ (F.compact n)
        (F.nonempty n) (F.positive n) hr hqr
      have hvolume : μ.real (cthickening (2 * F.scale n) (F.sets n)) ≤
          F.volumeConstant * (∫ y, metricTent (F.sets n) (F.scale n) y ∂μ) :=
        (F.volume_bound n).trans (mul_le_mul_of_nonneg_left
          (metricTent_integral_lower μ (F.compact n) (F.nonempty n) hr) F.volume_nonneg)
      calc
        _ ≤ dist 1 q / (F.scale n * (∫ y, metricTent (F.sets n) (F.scale n) y ∂μ)) *
            μ.real (cthickening (2 * F.scale n) (F.sets n)) := hfirst
        _ ≤ D / (F.scale n * (∫ y, metricTent (F.sets n) (F.scale n) y ∂μ)) *
            (F.volumeConstant * (∫ y, metricTent (F.sets n) (F.scale n) y ∂μ)) :=
          mul_le_mul (div_le_div_of_nonneg_right (hdist q hq) (by positivity)) hvolume
            ENNReal.toReal_nonneg (by positivity)
        _ = (D * F.volumeConstant) / F.scale n := by field_simp

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ErgodicDecompositionInput
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Ergodic decomposition of invariant probabilities

Greschonig--Schmidt, *Ergodic decomposition of quasi-invariant probability
measures*, Colloquium Mathematicum 84/85 (2000), 495--514, Theorem 5.2(1),
specialized to the zero Radon--Nikodym cocycle. Components are invariant
ergodic probabilities and their barycenter is the original measure. The
formalization records setwise measurability, the barycenter identity, and
invariance of the component map.

Source: https://www.mat.univie.ac.at/~kschmidt/Publications/decomposition.pdf
-/

namespace PolycyclicRecognition

open MeasureTheory

/-- The invariant specialization of Greschonig--Schmidt Theorem 5.2.
All topological and standard-Borel hypotheses are retained in the binder. -/
def ErgodicDecompositionInput (G X : Type*)
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G]
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [StandardBorelSpace X]
    [MulAction G X] [ContinuousSMul G X] : Prop :=
  ∀ μ : Measure X, IsProbabilityMeasure μ → SMulInvariantMeasure G X μ →
    ∃ κ : X → Measure X,
      (∀ x, IsProbabilityMeasure (κ x) ∧ ErgodicSMul G X (κ x)) ∧
      (∀ (g : G) (x : X), κ (g • x) = κ x) ∧
      ∀ s : Set X, MeasurableSet s →
        Measurable (fun x => κ x s) ∧ μ s = ∫⁻ x, κ x s ∂μ

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_IntegralQuotientKernel
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive
attribute [-simp] _root_.OAI.PolycyclicRecognition.commutingIntegralHom_generator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing one coordinate from an integral abelian quotient -/

noncomputable section
namespace PolycyclicRecognition

def integralQuotientDrop (n : ℕ) : IntegralLatticeGroup (n + 1) →* IntegralLatticeGroup n where
  toFun z := Multiplicative.ofAdd (fun j => z.toAdd j.castSucc)
  map_one' := rfl
  map_mul' _ _ := rfl

def integralQuotientLast (n : ℕ) : IntegralLatticeGroup (n + 1) →* Multiplicative ℤ where
  toFun z := Multiplicative.ofAdd (z.toAdd (Fin.last n))
  map_one' := rfl
  map_mul' _ _ := rfl

def integralQuotientInsert (n : ℕ) (z : IntegralLatticeGroup n) (k : Multiplicative ℤ) :
    IntegralLatticeGroup (n + 1) := Multiplicative.ofAdd (Fin.lastCases k.toAdd z.toAdd)

@[simp] theorem integralQuotientDrop_insert (n : ℕ) (z : IntegralLatticeGroup n)
    (k : Multiplicative ℤ) : integralQuotientDrop n (integralQuotientInsert n z k) = z := by
  apply Multiplicative.ext
  funext j
  change Fin.lastCases k.toAdd z.toAdd j.castSucc = z.toAdd j
  exact Fin.lastCases_castSucc j

@[simp] theorem integralQuotientLast_insert (n : ℕ) (z : IntegralLatticeGroup n)
    (k : Multiplicative ℤ) : integralQuotientLast n (integralQuotientInsert n z k) = k := by
  apply Multiplicative.ext
  change Fin.lastCases k.toAdd z.toAdd (Fin.last n) = k.toAdd
  exact Fin.lastCases_last

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_OneParameterIntegralCurve
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Recovering a one-parameter subgroup from its tangent vector -/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]

theorem oneParameter_isMIntegralCurve {γ : ℝ → G}
    (hzero : γ 0 = 1) (hmul : ∀ s t, γ (s + t) = γ s * γ t)
    (v : GroupLieAlgebra (𝓘(ℝ, E)) G)
    (hd : HasMFDerivAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) γ 0
      ((ContinuousLinearMap.id ℝ ℝ).smulRight v)) :
    IsMIntegralCurve (I := 𝓘(ℝ, E)) γ (mulInvariantVectorField v) := by
  intro t
  have hbase : HasMFDerivAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) γ (t - t)
      ((ContinuousLinearMap.id ℝ ℝ).smulRight v) := by rw [sub_self]; exact hd
  have hshift : HasMFDerivAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) (fun s : ℝ => s - t) t
      (ContinuousLinearMap.id ℝ ℝ) := by
    have hD : ContinuousLinearMap.toSpanSingleton ℝ (1 : ℝ) =
        ContinuousLinearMap.id ℝ ℝ := by ext; simp
    simpa only [id_eq, hD] using ((hasDerivAt_id t).sub_const t).hasFDerivAt.hasMFDerivAt
  have hl : HasMFDerivAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun g : G => γ t * g)
      (γ (t - t)) (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun g : G => γ t * g) 1) := by
    rw [sub_self, hzero]
    exact (contMDiff_mul_left (I := 𝓘(ℝ, E)) (a := γ t) :
      ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) ⊤ (fun g : G => γ t * g)).mdifferentiableAt
        (by simp) |>.hasMFDerivAt
  have hh := hl.comp t (HasMFDerivAt.comp t (f := fun s : ℝ => s - t) hbase hshift)
  have heq : (fun s : ℝ => γ t * γ (s - t)) = γ := by
    funext s
    rw [← hmul]
    congr 1
    ring
  change HasMFDerivAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) (fun s : ℝ => γ t * γ (s - t)) t _ at hh
  rw [heq] at hh
  apply hh.congr_mfderiv
  apply ContinuousLinearMap.ext
  intro r
  let s : ℝ := r
  change (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun g : G => γ t * g) 1) (s • v) =
    s • (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun g : G => γ t * g) 1) v
  exact map_smul _ s v

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SelfQuasiIsometry
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform coarse inverse bounds for self quasi-isometries -/

noncomputable section
namespace PolycyclicRecognition

variable (G : Type*) [PseudoMetricSpace G] (K C : ℝ)

variable {G K C}

def SelfQuasiIsometry.inverse (f : SelfQuasiIsometry G K C) : G → G :=
  fun y => Classical.choose (f.surjective y)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SuccessfulWordPaths
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Prescribed word paths through the successful sheets -/

noncomputable section

namespace PolycyclicRecognition

variable {G : Type*} [Group G]

/-- All the states at which a support leg is traversed are in the good set. -/
def WordSheetsGood (A : Set G) : G → List G → Prop
  | n, [] => n ∈ A
  | n, g :: u => n ∈ A ∧ WordSheetsGood A (n * g) u

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_UnitaryReducedVanishing
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The unitary formulation of reduced cocycle vanishing -/

noncomputable section

namespace PolycyclicRecognition

universe u v

open Set

def UnitaryReducedVanishing (G : Type u) [Group G] [TopologicalSpace G] : Prop :=
  ∀ (E : Type v) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)),
    (∀ x : E, (∀ g, ρ g x = x) → x = 0) →
    (∀ x : E, Continuous (fun g => ρ g x)) →
    ∀ b : G → E, Continuous b → IsUnitaryCocycle ρ b →
    ∀ Q : Set G, IsCompact Q → ∀ ε : ℝ, 0 < ε →
      ∃ φ : E, ∀ q ∈ Q, ‖b q + ρ q φ - φ‖ ≤ ε

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_AlgebraHomLieDifferential
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual differential of an algebra-unit homomorphism

Left-invariant vector fields are related to left multiplication in the
algebra. Preservation of their brackets gives the matrix commutator law.
-/

noncomputable section
namespace PolycyclicRecognition

open Function VectorField
open scoped Manifold ContDiff

variable {E G A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]
  [NormedRing A] [NormedAlgebra ℝ A]

def unitsHomDifferential (ρ : G →* Aˣ) (g : G) : E →L[ℝ] A :=
  mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, A)) (fun x => (ρ x : A)) g

theorem mfderiv_unitsHom_invariant
    (ρ : G →* Aˣ)
    (hf : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, A)) ∞ (fun g => (ρ g : A)))
    (v : GroupLieAlgebra (𝓘(ℝ, E)) G) (g : G) :
    unitsHomDifferential (E := E) ρ g (mulInvariantVectorField v g) =
      (ρ g : A) * unitsHomDifferential (E := E) ρ 1 v := by
  let f : G → A := fun x => (ρ x : A)
  let L : A →L[ℝ] A := ContinuousLinearMap.mul ℝ A (ρ g : A)
  have hl : MDifferentiableAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun x : G => g * x) 1 :=
    (contMDiff_mul_left (I := 𝓘(ℝ, E)) (a := g) :
      ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) ∞ (fun x : G => g * x)).mdifferentiableAt (by simp)
  have h₁ := ((hf (g * 1)).mdifferentiableAt (by simp)).hasMFDerivAt.comp 1 hl.hasMFDerivAt
  have h₂ := L.hasFDerivAt.hasMFDerivAt.comp (1 : G)
    ((hf 1).mdifferentiableAt (by simp)).hasMFDerivAt
  have heq : f ∘ (fun x : G => g * x) = L ∘ f := by
    funext x
    exact congrArg (fun u : Aˣ => (u : A)) (ρ.map_mul g x)
  change HasMFDerivAt (𝓘(ℝ, E)) (𝓘(ℝ, A)) (f ∘ (fun x : G => g * x)) 1 _ at h₁
  rw [heq] at h₁
  have hd := h₁.mfderiv.symm.trans h₂.mfderiv
  have hv := congrArg (fun D : E →L[ℝ] A => D v) hd
  have hbase : (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, A)) f (g * 1) : E →L[ℝ] A) =
      mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, A)) f g := by
    congr 1
    exact mul_one g
  change (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, A)) f (g * 1))
      ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun x : G => g * x) 1) v) =
      L ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, A)) f 1) v) at hv
  rw [hbase] at hv
  exact hv

theorem lieBracket_rightMultiplication (v w a : A) :
    lieBracket ℝ (fun x : A => x * v) (fun x : A => x * w) a =
      a * (v * w - w * v) := by
  let Rv : A →L[ℝ] A := (ContinuousLinearMap.mul ℝ A).flip v
  let Rw : A →L[ℝ] A := (ContinuousLinearMap.mul ℝ A).flip w
  have hv : fderiv ℝ (fun x : A => x * v) a = Rv := Rv.hasFDerivAt.fderiv
  have hw : fderiv ℝ (fun x : A => x * w) a = Rw := Rw.hasFDerivAt.fderiv
  unfold lieBracket
  rw [hv, hw]
  change (a * v) * w - (a * w) * v = a * (v * w - w * v)
  noncomm_ring

attribute [local instance 100] LieRing.ofAssociativeRing

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_AnalyticNilpotentExponential
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Agreement of analytic and finite nilpotent exponentials -/

noncomputable section
namespace PolycyclicRecognition

variable {A : Type*} [NormedRing A] [NormedAlgebra ℚ A]

theorem analytic_exp_eq_nilpotent_exp {a : A} (ha : IsNilpotent a) :
    NormedSpace.exp a = IsNilpotent.exp a := by
  obtain ⟨n, hn⟩ := ha
  rw [IsNilpotent.exp_eq_sum hn, NormedSpace.exp_eq_tsum ℚ]
  apply tsum_eq_sum
  intro k hk
  have hnk : n ≤ k := by simpa using hk
  rw [pow_eq_zero_of_le hnk hn, smul_zero]

theorem isNilpotent_analytic_exp_sub_one {a : A} (ha : IsNilpotent a) :
    IsNilpotent (NormedSpace.exp a - 1) := by
  rw [analytic_exp_eq_nilpotent_exp ha]
  exact ha.isNilpotent_exp_sub_one

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_AnalyticRepresentationAtlas
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Analytic charts supplied by a local matrix representation

A local coordinate obtained by projecting a representation, with analytic
matrix entries in those coordinates, supplies analytic translated charts.
-/

noncomputable section
namespace PolycyclicRecognition
open Set
open scoped Manifold ContDiff

variable {G E A : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing A] [NormedAlgebra ℝ A]

/-- Only the concrete local chart data needed for the analytic atlas. -/
structure RepresentedLocalChart (ρ : G →* Aˣ) where
  chart : OpenPartialHomeomorph G E
  one_mem : (1 : G) ∈ chart.source
  at_one : chart 1 = 0
  coordinate : A →L[ℝ] E
  coordinate_eq : ∀ g ∈ chart.source, chart g = coordinate ((ρ g : A) - 1)
  realization : E → A
  realization_contDiff : ContDiffOn ℝ ω realization chart.target
  realization_eq : ∀ x ∈ chart.target, realization x = (ρ (chart.symm x) : A)
  inverseRealization : E → A
  inverseRealization_contDiff : ContDiffOn ℝ ω inverseRealization chart.target
  inverseRealization_eq : ∀ x ∈ chart.target,
    inverseRealization x = ((ρ (chart.symm x))⁻¹ : Aˣ)

namespace RepresentedLocalChart
variable {ρ : G →* Aˣ} (C : RepresentedLocalChart (E := E) ρ)

def translated (g : G) : OpenPartialHomeomorph G E :=
  (Homeomorph.mulLeft g⁻¹).toOpenPartialHomeomorph.trans C.chart

@[simp] theorem translated_apply (g x : G) : C.translated g x = C.chart (g⁻¹ * x) := rfl

@[simp] theorem translated_symm_apply (g : G) (x : E) :
    (C.translated g).symm x = g * C.chart.symm x := by
  change g⁻¹⁻¹ * C.chart.symm x = _
  rw [inv_inv]

@[simp] theorem translated_target (g : G) : (C.translated g).target = C.chart.target := by
  ext x
  change x ∈ C.chart.target ∧ C.chart.symm x ∈ (Set.univ : Set G) ↔ _
  simp

@[instance_reducible]
def chartedSpace : ChartedSpace E G where
  atlas := Set.range C.translated
  chartAt := C.translated
  mem_chart_source g := by
    change g ∈ (Set.univ : Set G) ∧ g⁻¹ * g ∈ C.chart.source
    exact ⟨Set.mem_univ _, by simpa only [inv_mul_cancel] using C.one_mem⟩
  chart_mem_atlas g := ⟨g,rfl⟩

theorem transition_contDiff (a b : G) :
    ContDiffOn ℝ ω ((C.translated a).symm ≫ₕ C.translated b)
      ((C.translated a).symm ≫ₕ C.translated b).source := by
  let s := ((C.translated a).symm ≫ₕ C.translated b).source
  have hs : s ⊆ C.chart.target := by
    intro x hx
    exact (C.translated_target a) ▸ hx.1
  have hf : ContDiffOn ℝ ω
      (fun x => (((ρ b)⁻¹ : Aˣ) : A) * ((ρ a : A) * C.realization x) - 1) s :=
    (contDiffOn_const.mul (contDiffOn_const.mul
      (C.realization_contDiff.mono hs))).sub contDiffOn_const
  have hh := C.coordinate.contDiff.comp_contDiffOn hf
  apply hh.congr
  intro x hx
  simp only [OpenPartialHomeomorph.trans_apply, translated_apply,
    translated_symm_apply, Function.comp_apply]
  have hx' : (C.translated a).symm x ∈ (C.translated b).source := hx.2
  have hx'' : b⁻¹ * ((C.translated a).symm x) ∈ C.chart.source := hx'.2
  rw [translated_symm_apply] at hx''
  rw [C.coordinate_eq _ hx'']
  rw [map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul,
    ← C.realization_eq x (hs hx)]

theorem isManifold : letI := C.chartedSpace; IsManifold (𝓘(ℝ,E)) ω G := by
  let cs : ChartedSpace E G := C.chartedSpace
  apply isManifold_of_contDiffOn
  rintro e e' ⟨a,rfl⟩ ⟨b,rfl⟩
  simpa only [mfld_simps] using C.transition_contDiff a b

end RepresentedLocalChart
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_AnalyticRepresentationGroup
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Analytic group operations in representation coordinates -/

noncomputable section
namespace PolycyclicRecognition
open Set Filter
open scoped Manifold ContDiff Topology

variable {G E A : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing A] [NormedAlgebra ℝ A]
  {ρ : G →* Aˣ} (C : RepresentedLocalChart (E := E) ρ)

namespace RepresentedLocalChart

omit [IsTopologicalGroup G] in
theorem zero_mem_target : (0 : E) ∈ C.chart.target := by
  rw [← C.at_one]
  exact C.chart.map_source C.one_mem

omit [IsTopologicalGroup G] in
theorem symm_zero : C.chart.symm (0 : E) = 1 := by
  rw [← C.at_one]
  exact C.chart.left_inv C.one_mem

theorem contMDiff_mul : letI := C.chartedSpace;
    ContMDiff ((𝓘(ℝ,E)).prod (𝓘(ℝ,E))) (𝓘(ℝ,E)) ω (fun p : G × G => p.1 * p.2) := by
  let cs : ChartedSpace E G := C.chartedSpace
  let ms : IsManifold (𝓘(ℝ,E)) ω G := C.isManifold
  have ht : C.chart.target ∈ 𝓝 (0 : E) := C.chart.open_target.mem_nhds C.zero_mem_target
  have hF : ContDiffAt ℝ ω C.realization 0 := C.realization_contDiff.contDiffAt ht
  have hc : ContinuousAt C.chart.symm (0 : E) := C.chart.continuousAt_symm C.zero_mem_target
  intro p
  rw [contMDiffAt_iff]
  refine ⟨continuous_mul.continuousAt, ?_⟩
  simp only [mfld_simps, Function.comp_def]
  have hchart (g : G) : chartAt E g = C.translated g := rfl
  have hrange : Set.range (Prod.map id id : E × E → E × E) = Set.univ := by
    ext x
    exact ⟨fun _ => Set.mem_univ _, fun _ => ⟨x,rfl⟩⟩
  simp only [hchart, hrange]
  change ContDiffWithinAt ℝ ω
    (fun q : E × E => (C.translated (p.1 * p.2))
      ((C.translated p.1).symm q.1 * (C.translated p.2).symm q.2)) Set.univ
    ((C.translated p.1) p.1, (C.translated p.2) p.2)
  simp only [translated_apply, translated_symm_apply, inv_mul_cancel, C.at_one]
  rw [contDiffWithinAt_univ]
  have hf : ContDiffAt ℝ ω (fun q : E × E => C.coordinate
      ((((ρ (p.1 * p.2))⁻¹ : Aˣ) : A) *
        (((ρ p.1 : A) * C.realization q.1) * ((ρ p.2 : A) * C.realization q.2)) - 1)) (0,0) :=
    C.coordinate.contDiff.contDiffAt.comp _
      ((contDiffAt_const.mul ((contDiffAt_const.mul (hF.comp (f := Prod.fst) (0,0) contDiffAt_fst)).mul
        (contDiffAt_const.mul (hF.comp (f := Prod.snd) (0,0) contDiffAt_snd)))).sub contDiffAt_const)
  apply hf.congr_of_eventuallyEq
  have hq1 : ∀ᶠ q : E × E in 𝓝 (0,0), q.1 ∈ C.chart.target :=
    continuousAt_fst.tendsto.eventually ht
  have hq2 : ∀ᶠ q : E × E in 𝓝 (0,0), q.2 ∈ C.chart.target :=
    continuousAt_snd.tendsto.eventually ht
  have hw : ContinuousAt (fun q : E × E => (p.1 * p.2)⁻¹ *
      ((p.1 * C.chart.symm q.1) * (p.2 * C.chart.symm q.2))) (0,0) :=
    continuousAt_const.mul ((continuousAt_const.mul (hc.comp (f := Prod.fst) continuousAt_fst)).mul
      (continuousAt_const.mul (hc.comp (f := Prod.snd) continuousAt_snd)))
  have hw0 : (p.1 * p.2)⁻¹ * ((p.1 * C.chart.symm 0) * (p.2 * C.chart.symm 0)) = 1 := by
    rw [C.symm_zero, mul_one, mul_one, inv_mul_cancel]
  have hws := hw.tendsto.eventually (hw0 ▸ C.chart.open_source.mem_nhds C.one_mem)
  filter_upwards [hq1,hq2,hws] with q hq1 hq2 hq
  rw [C.coordinate_eq _ hq]
  simp only [map_mul, map_inv, Units.val_mul]
  rw [← C.realization_eq q.1 hq1, ← C.realization_eq q.2 hq2]

theorem contMDiff_inv : letI := C.chartedSpace;
    ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) ω (fun g : G => g⁻¹) := by
  let cs : ChartedSpace E G := C.chartedSpace
  let ms : IsManifold (𝓘(ℝ,E)) ω G := C.isManifold
  have ht : C.chart.target ∈ 𝓝 (0 : E) := C.chart.open_target.mem_nhds C.zero_mem_target
  have hF : ContDiffAt ℝ ω C.inverseRealization 0 := C.inverseRealization_contDiff.contDiffAt ht
  have hc : ContinuousAt C.chart.symm (0 : E) := C.chart.continuousAt_symm C.zero_mem_target
  intro g
  rw [contMDiffAt_iff]
  refine ⟨continuous_inv.continuousAt, ?_⟩
  simp only [mfld_simps, Function.comp_def]
  have hchart (g : G) : chartAt E g = C.translated g := rfl
  simp only [hchart, translated_apply, translated_symm_apply, inv_mul_cancel, C.at_one]
  change ContDiffWithinAt ℝ ω
    (fun x : E => C.chart ((g⁻¹)⁻¹ * (g * C.chart.symm x)⁻¹)) Set.univ 0
  rw [contDiffWithinAt_univ]
  have hf : ContDiffAt ℝ ω (fun x : E => C.coordinate
      ((ρ g : A) * C.inverseRealization x * (((ρ g)⁻¹ : Aˣ) : A) - 1)) 0 :=
    C.coordinate.contDiff.contDiffAt.comp _
      (((contDiffAt_const.mul hF).mul contDiffAt_const).sub contDiffAt_const)
  apply hf.congr_of_eventuallyEq
  have hw : ContinuousAt (fun x : E => (g⁻¹)⁻¹ * (g * C.chart.symm x)⁻¹) 0 :=
    continuousAt_const.mul (continuousAt_const.mul hc).inv
  have hw0 : (g⁻¹)⁻¹ * (g * C.chart.symm 0)⁻¹ = 1 := by
    rw [C.symm_zero, mul_one, inv_inv, mul_inv_cancel]
  have hws := hw.tendsto.eventually (hw0 ▸ C.chart.open_source.mem_nhds C.one_mem)
  filter_upwards [ht,hws] with x hx hsource
  rw [C.coordinate_eq _ hsource, inv_inv, mul_inv_rev, map_mul, map_mul, map_inv,
    Units.val_mul, Units.val_mul, ← C.inverseRealization_eq x hx]
  simp only [map_inv, mul_assoc]

/-- These representation coordinates give an actual analytic Lie group. -/
theorem lieGroup : letI := C.chartedSpace; LieGroup (𝓘(ℝ,E)) ω G := by
  let cs : ChartedSpace E G := C.chartedSpace
  exact { C.isManifold with
    contMDiff_mul := C.contMDiff_mul
    contMDiff_inv := C.contMDiff_inv }

end RepresentedLocalChart
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CompactRotationalTwist
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compact rotational modifications

An invariant character into a compact abelian automorphism group has a closed
graph inside the semidirect extension. The original group and this graph both
have proper cocompact inclusions.
-/

noncomputable section
namespace PolycyclicRecognition

open Set Topology

variable {G K : Type*} [Group G] [CommGroup K]
  [TopologicalSpace G] [TopologicalSpace K]
  (α : K →* MulAut G) (τ : G →* K)
  (hinv : ∀ k g, τ (α k g) = τ g)

attribute [local instance] semidirectProductTopology

/-- The inverse-character graph, with the multiplication inherited from the
semidirect extension. The character is invariant under the compact action. -/
def rotationalTwist : Subgroup (G ⋊[α] K) where
  carrier := {p | p.right = (τ p.left)⁻¹}
  one_mem' := by simp
  mul_mem' := by
    intro p q hp hq
    change p.right * q.right = (τ (p.left * α p.right q.left))⁻¹
    rw [map_mul, hinv, hp, hq, mul_inv_rev, mul_comm]
  inv_mem' := by
    intro p hp
    change p.right⁻¹ = (τ (α p.right⁻¹ p.left⁻¹))⁻¹
    rw [hinv, map_inv, inv_inv, hp, inv_inv]

/-- Removing a rotation changes multiplication, while preserving the
underlying topological space. -/
def rotationalTwistHomeomorph [IsTopologicalGroup K] (hτ : Continuous τ) :
    rotationalTwist α τ hinv ≃ₜ G where
  toFun p := p.val.left
  invFun g := ⟨⟨g, (τ g)⁻¹⟩, rfl⟩
  left_inv p := by
    apply Subtype.ext
    apply SemidirectProduct.ext
    · rfl
    · exact p.property.symm
  right_inv _ := rfl
  continuous_toFun := (continuous_semidirect_left α).comp continuous_subtype_val
  continuous_invFun :=
    ((semidirectProductHomeomorph α).symm.continuous.comp
      (continuous_id.prodMk hτ.inv)).subtype_mk (fun _ => rfl)

variable [IsTopologicalGroup G] [IsTopologicalGroup K] [T2Space K]

omit [IsTopologicalGroup G] in
include hinv in
theorem rotationalTwist_isClosed (hτ : Continuous τ) :
    IsClosed (rotationalTwist α τ hinv : Set (G ⋊[α] K)) :=
  isClosed_eq (continuous_semidirect_right α)
    (hτ.comp (continuous_semidirect_left α)).inv

omit [IsTopologicalGroup G] [IsTopologicalGroup K] in
/-- The original group has a proper inclusion into its semidirect extension. -/
theorem semidirect_inl_isProperMap :
    IsProperMap (SemidirectProduct.inl : G → G ⋊[α] K) := by
  have hc : IsClosed (range (fun g : G => (g, (1 : K)))) := by
    have he : range (fun g : G => (g, (1 : K))) = {p : G × K | p.2 = 1} := by
      ext ⟨g, k⟩
      simp [eq_comm]
    rw [he]
    exact isClosed_eq continuous_snd continuous_const
  exact ((semidirectProductHomeomorph α).symm.isClosedEmbedding.comp
    ⟨isEmbedding_prodMkLeft (1 : K), hc⟩).isProperMap

omit [IsTopologicalGroup G] in
/-- The modified group is likewise properly included. -/
theorem rotationalTwist_subtype_isProperMap (hτ : Continuous τ) :
    IsProperMap (rotationalTwist α τ hinv).subtype :=
  (rotationalTwist_isClosed α τ hinv hτ).isClosedEmbedding_subtypeVal.isProperMap

variable [CompactSpace K]

/-- The rotation subgroup is one fixed compact right-coset cover. -/
def semidirect_inl_properCocompact : ProperCocompactHom G (G ⋊[α] K) where
  hom := SemidirectProduct.inl
  proper := semidirect_inl_isProperMap α
  cover := ⟨range (SemidirectProduct.inr : K → G ⋊[α] K),
    isCompact_range (continuous_semidirect_inr α), fun p =>
      ⟨p.left, SemidirectProduct.inr p.right, mem_range_self _,
        SemidirectProduct.inl_left_mul_inr_right p⟩⟩

/-- The same compact subgroup covers the inverse-character graph, so no
metric estimate or triangulability assertion is hidden in this arrow. -/
def rotationalTwist_properCocompact (hτ : Continuous τ) :
    ProperCocompactHom (rotationalTwist α τ hinv) (G ⋊[α] K) where
  hom := (rotationalTwist α τ hinv).subtype
  proper := rotationalTwist_subtype_isProperMap α τ hinv hτ
  cover := by
    refine ⟨range (SemidirectProduct.inr : K → G ⋊[α] K),
      isCompact_range (continuous_semidirect_inr α), fun p => ?_⟩
    refine ⟨⟨⟨p.left, (τ p.left)⁻¹⟩, rfl⟩,
      SemidirectProduct.inr (τ p.left * p.right), mem_range_self _, ?_⟩
    apply SemidirectProduct.ext <;> simp

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_LieIntegrationNaturality
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing exponential compatibility from the integration input

Only existence of a smooth homomorphism with the prescribed differential
remains from Lee's integration theorem. The exponential maps and their
compatibility are supplied by the proved integral-curve construction.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold ContDiff

variable {EN N EG G : Type*}
  [NormedAddCommGroup EN] [NormedSpace ℝ EN] [FiniteDimensional ℝ EN]
  [TopologicalSpace N] [ChartedSpace EN N] [Group N] [LieGroup (𝓘(ℝ, EN)) ⊤ N]
  [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
  [TopologicalSpace G] [ChartedSpace EG G] [Group G] [LieGroup (𝓘(ℝ, EG)) ⊤ G]

/-- The still-undischarged existence assertion of Lee (2013), Theorem 20.19,
in precisely the nilpotent-source specialization used in the application. -/
def NilpotentSmoothIntegrationInput : Prop :=
  SimplyConnectedSpace N → LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, EN)) N) →
    ∀ j : GroupLieAlgebra (𝓘(ℝ, EN)) N →ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EG)) G,
      ∃ ι : N →* G, ContMDiff (𝓘(ℝ, EN)) (𝓘(ℝ, EG)) ∞ ι ∧
        ∀ x, mfderiv (𝓘(ℝ, EN)) (𝓘(ℝ, EG)) ι 1 x = j x

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_MinimizingLieMetric
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The published minimizing metric on the connected Lie model

The sole input is the connected Lie-group specialization of J. M. Lee,
*Introduction to Riemannian Manifolds*, second edition, GTM 176 (2018):
Lemma 3.10(b), p. 68 constructs a left-invariant Riemannian metric;
Problem 6-12(c), p. 188 gives completeness of homogeneous metrics;
Corollary 6.21, p. 170 gives minimizing segments; Problem 6-14(a), p. 188
(or the compact exponential-ball argument in Lemma 6.18) gives properness.
Only the resulting metric and normalized minimizing paths are retained.
The large-scale chain property is proved here rather than included in the
published hypothesis.
-/

noncomputable section
namespace PolycyclicRecognition

open Set

/-- The metric consequences of a complete left-invariant Riemannian metric. -/
structure ProperMinimizingMetric (G : Type*) [Group G] [TopologicalSpace G] where
  metric : MetricSpace G
  topology_eq : metric.toUniformSpace.toTopologicalSpace = ‹TopologicalSpace G›
  proper : letI := metric; ProperSpace G
  leftInvariant : letI := metric; IsIsometricSMul G G
  minimizing : letI := metric
    ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_NormalizedWeightRays
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Deduplicating positive weight rays

Unit normalization gives a concrete finite set of positive rays, even when
the original generator list repeats some rays with different multiplicities.
-/

noncomputable section

namespace PolycyclicRecognition

open Set

variable {W I : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [Fintype I]

def normalizedWeight (φ : W →L[ℝ] ℝ) : W →L[ℝ] ℝ := ‖φ‖⁻¹ • φ

def NormalizedWeightRays (α : I → W →L[ℝ] ℝ) :=
  ↥(Set.range fun i => normalizedWeight (α i))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_OrderedInterpolationWeights
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Stability of ordered interpolation under changes of mass -/

namespace PolycyclicRecognition

variable {I G : Type*} [MetricSpace G]

def InterpolationWeightControl (c : ControlledContraction G) (D : ℝ) (n : ℕ) (K : ℝ) : Prop :=
  ∀ (l : List I) (p₀ : G) (v : I → G) (a b : I → ℝ),
    l.length ≤ n → (∀ i ∈ l, 0 ≤ a i) → (∀ i ∈ l, 0 ≤ b i) →
    (∀ i ∈ l, ∀ j ∈ l, dist (v i) (v j) ≤ D) →
    min (listMass a l) (listMass b l) *
        dist (orderedCenter c p₀ v a l) (orderedCenter c p₀ v b l) ≤
      K * listVariation a b l

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ProductLieAlgebra
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Tangent projections of a product Lie group

The jointly injective projections detect nilpotence and transport a single
finite BCH identity to both factors.
-/

noncomputable section
namespace PolycyclicRecognition

open LieModule
open scoped Manifold ContDiff

variable {E G F H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [TopologicalSpace H] [ChartedSpace F H] [Group H] [LieGroup (𝓘(ℝ, F)) ⊤ H]

@[instance_reducible] def productSelfChartedSpace : ChartedSpace (E × F) (G × H) :=
  prodChartedSpace E G F H

attribute [local instance] productSelfChartedSpace

instance productSelfLieGroup : LieGroup (𝓘(ℝ, E × F)) ⊤ (G × H) := by
  rw [modelWithCornersSelf_prod]
  exact Prod.instLieGroup (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, F))

omit [CompleteSpace E] [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]
  [CompleteSpace F] [Group H] [LieGroup (𝓘(ℝ, F)) ⊤ H] in
theorem contMDiff_product_fst :
    ContMDiff (𝓘(ℝ, E × F)) (𝓘(ℝ, E)) ∞ (Prod.fst : G × H → G) := by
  rw [modelWithCornersSelf_prod]
  exact contMDiff_fst

omit [CompleteSpace E] [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]
  [CompleteSpace F] [Group H] [LieGroup (𝓘(ℝ, F)) ⊤ H] in
theorem contMDiff_product_snd :
    ContMDiff (𝓘(ℝ, E × F)) (𝓘(ℝ, F)) ∞ (Prod.snd : G × H → H) := by
  rw [modelWithCornersSelf_prod]
  exact contMDiff_snd

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_TriangularProducts
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Polynomial products with bounded diagonal prefixes

For an upper triangular matrix path, remove the diagonal of each prefix.
The resulting increments are unipotent. If the original increments are bounded
and all diagonal prefixes and their inverses are bounded, the unipotent
increments are uniformly bounded. Their products therefore have polynomial
size. This is the coordinate estimate behind bounded-height path packing.
-/

namespace PolycyclicRecognition

section Matrix

open scoped Matrix.Norms.Operator

variable {n : ℕ}

/-- A diagonal unit is represented by a genuine invertible diagonal matrix. -/
def diagonalUnit (d : Fin n → ℝˣ) : (Matrix (Fin n) (Fin n) ℝ)ˣ where
  val := Matrix.diagonal fun i => (d i : ℝ)
  inv := Matrix.diagonal fun i => (↑(d i)⁻¹ : ℝ)
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    simp [Matrix.diagonal, Matrix.one_apply]
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    simp [Matrix.diagonal, Matrix.one_apply]

end Matrix
end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_TriangularMatrixHeight
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual logarithmic height on positive triangular matrices

The logarithms of positive diagonal entries form a group homomorphism.
Bounded logarithmic height bounds both diagonal frames and their inverses,
which are the hypotheses in the polynomial product estimate.
-/

namespace PolycyclicRecognition

open scoped Matrix.Norms.Operator

variable {n : ℕ}

theorem triangular_mul_diag (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsUpperTriangular) (hB : B.IsUpperTriangular) (i : Fin n) :
    (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_single i
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with h | h
    · rw [hA h, zero_mul]
    · rw [hB h, mul_zero]
  · simp

/-- Positive invertible upper triangular real matrices, as an actual subgroup. -/
def positiveTriangular (n : ℕ) : Subgroup (Matrix (Fin n) (Fin n) ℝ)ˣ where
  carrier := {u | (u : Matrix (Fin n) (Fin n) ℝ).IsUpperTriangular ∧
    ∀ i, 0 < (u : Matrix (Fin n) (Fin n) ℝ) i i}
  one_mem' := by
    refine ⟨?_, ?_⟩
    · intro i j hij
      exact Matrix.one_apply_ne (ne_of_gt hij)
    · intro i
      simp
  mul_mem' := by
    intro a b ha hb
    refine ⟨ha.1.mul hb.1, ?_⟩
    intro i
    change 0 < ((a : Matrix (Fin n) (Fin n) ℝ) * (b : Matrix (Fin n) (Fin n) ℝ)) i i
    rw [triangular_mul_diag _ _ ha.1 hb.1]
    exact mul_pos (ha.2 i) (hb.2 i)
  inv_mem' := by
    intro a ha
    have hu : (↑a⁻¹ : Matrix (Fin n) (Fin n) ℝ).IsUpperTriangular := by
      rw [Matrix.coe_units_inv]
      exact Matrix.blockTriangular_inv_of_blockTriangular ha.1
    refine ⟨hu, fun i => ?_⟩
    have hi : (a : Matrix (Fin n) (Fin n) ℝ) i i *
        (↑a⁻¹ : Matrix (Fin n) (Fin n) ℝ) i i = 1 := by
      rw [← triangular_mul_diag _ _ ha.1 hu, Units.mul_inv]
      simp
    exact (mul_pos_iff_of_pos_left (ha.2 i)).mp (hi ▸ zero_lt_one)

namespace PositiveTriangular

abbrev matrix (g : positiveTriangular n) : Matrix (Fin n) (Fin n) ℝ := g.val

theorem upper (g : positiveTriangular n) : (matrix g).IsUpperTriangular := g.property.1

theorem diagonal_pos (g : positiveTriangular n) (i : Fin n) : 0 < matrix g i i := g.property.2 i

/-- The diagonal characters with their actual unit values. -/
noncomputable def diagonal : positiveTriangular n →* (Fin n → ℝˣ) where
  toFun g i := Units.mk0 (matrix g i i) (diagonal_pos g i).ne'
  map_one' := by
    ext i
    simp [matrix]
  map_mul' g h := by
    ext i
    exact triangular_mul_diag (matrix g) (matrix h) (upper g) (upper h) i

@[simp] theorem diagonal_val (g : positiveTriangular n) (i : Fin n) :
    (diagonal g i : ℝ) = matrix g i i := rfl

/-- The logarithmic diagonal is a homomorphism to an additive real vector space. -/
noncomputable def height : positiveTriangular n →* Multiplicative (Fin n → ℝ) where
  toFun g := Multiplicative.ofAdd fun i => Real.log (matrix g i i)
  map_one' := by
    apply Multiplicative.ext
    funext i
    simp [matrix]
  map_mul' g h := by
    apply Multiplicative.ext
    funext i
    change Real.log (matrix (g * h) i i) = Real.log (matrix g i i) + Real.log (matrix h i i)
    change Real.log ((matrix g * matrix h) i i) = _
    rw [triangular_mul_diag _ _ (upper g) (upper h),
      Real.log_mul (diagonal_pos g i).ne' (diagonal_pos h i).ne']

@[simp] theorem height_apply (g : positiveTriangular n) (i : Fin n) :
    (height g).toAdd i = Real.log (matrix g i i) := rfl

/-- The exact diagonal frame used to normalize triangular products. -/
noncomputable def frame (g : positiveTriangular n) : (Matrix (Fin n) (Fin n) ℝ)ˣ :=
  diagonalUnit (diagonal g)

end PositiveTriangular
end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_TriangularWordBounds
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Polynomial coordinate bounds for bounded-height triangular words

We use the actual prefix diagonals of a word in positive triangular matrices.
Every normalized increment is unipotent. Thus bounded heights at every prefix,
with bounded step matrices, imply a polynomial endpoint bound. No endpoint-only
height assumption is substituted for the path condition.
-/

namespace PolycyclicRecognition.PositiveTriangular

open scoped Matrix.Norms.Operator

variable {n : ℕ}

/-- The increments seen in the diagonal frame at each prefix. -/
noncomputable def framedSteps (g : positiveTriangular n) :
    List (positiveTriangular n) → List (Matrix (Fin n) (Fin n) ℝ)
  | [] => []
  | a :: l => ((frame g : Matrix (Fin n) (Fin n) ℝ) * matrix a *
      (↑(frame (g * a))⁻¹ : Matrix (Fin n) (Fin n) ℝ)) :: framedSteps (g * a) l

@[simp] theorem framedSteps_length (g : positiveTriangular n) (l : List (positiveTriangular n)) :
    (framedSteps g l).length = l.length := by
  induction l generalizing g with
  | nil => rfl
  | cons a l ih => simp [framedSteps, ih]

@[simp] theorem frame_one : frame (1 : positiveTriangular n) = 1 := by
  apply Units.ext
  ext i j
  simp [frame, diagonalUnit, Matrix.diagonal, Matrix.one_apply]

end PolycyclicRecognition.PositiveTriangular

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_TriangularLocalLogarithm
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The local logarithm in the full real upper triangular algebra -/

noncomputable section
namespace PolycyclicRecognition

open Filter Topology
open scoped Matrix.Norms.Operator

abbrev RealTriangularAlgebra (n : ℕ) :=
  ↥(Matrix.blockTriangularSubalgebra ℝ ℝ (id : Fin n → Fin n))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_TriangularLieDifferential
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The differential of a triangular Lie-group realization

The differential of a continuous injective matrix-group homomorphism
is a Lie algebra homomorphism. Precisely, John M. Lee, *Introduction
to Smooth Manifolds*, second edition, GTM 218 (2013), Problem 20-11(b),
pp.537–538, gives automatic smoothness; Theorem 8.44, p.195, gives the
induced Lie algebra homomorphism; Proposition 8.41, pp.193–195, identifies
the matrix-group Lie algebra with the matrix commutator algebra. Its
injectivity follows from Proposition 7.17, pp.157–158 (see its proof using
Theorem 7.5 and the Global Rank Theorem 4.14(b)).

The input retains only the Lie homomorphism and its equality to the
matrix-valued derivative. Its injectivity is proved using faithful
one-parameter subgroups. The derivative is upper triangular and solvable, and admits a
simultaneous adjoint basis.
-/

noncomputable section

namespace PolycyclicRecognition

open scoped Manifold Matrix.Norms.Elementwise

attribute [local instance 100] LieRing.ofAssociativeRing

-- The norm-induced and entrywise matrix topologies are definitionally equal,
-- but their different heads prevent inference of the self chart.
local instance matrixModelChartedSpace (n : ℕ) :
    @ChartedSpace (Matrix (Fin n) (Fin n) ℝ)
      (@UniformSpace.toTopologicalSpace _ (@PseudoMetricSpace.toUniformSpace _
        (@SeminormedAddCommGroup.toPseudoMetricSpace _
          (@NormedAddCommGroup.toSeminormedAddCommGroup _
            (Matrix.normedAddCommGroup (m := Fin n) (n := Fin n) (α := ℝ))))))
      (Matrix (Fin n) (Fin n) ℝ) inferInstance := by
  convert chartedSpaceSelf (Matrix (Fin n) (Fin n) ℝ) using 1
  all_goals try with_reducible_and_instances rfl
  rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RepresentedSolvableLieModel
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The solvable Lie model carried by analytic representation charts -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold Matrix.Norms.Operator

variable {G E : Type} [Group G] [MetricSpace G] [IsTopologicalGroup G]
  [SecondCountableTopology G] [SimplyConnectedSpace G] [Group.IsSolvable G]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {m : ℕ} {ρ : G →* (Matrix (Fin m) (Fin m) ℝ)ˣ}

def RepresentedLocalChart.solvableLieModel (C : RepresentedLocalChart (E := E) ρ) :
    SimplyConnectedSolvableLieModel where
  modelSpace := E
  carrier := G
  chartedSpace := C.chartedSpace
  lieGroup := C.lieGroup

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_TransportedManifold
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Pulling a smooth atlas back through a homeomorphism -/

noncomputable section
namespace PolycyclicRecognition
open Set
open scoped Manifold ContDiff

variable {E M X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [TopologicalSpace X] [ChartedSpace E M]

/-- A pullback atlas whose preferred charts have explicit formulas. -/
@[instance_reducible]
def pullbackChartedSpace (e : X ≃ₜ M) : ChartedSpace E X where
  atlas := {c | ∃ y : M, c = e.transOpenPartialHomeomorph (chartAt E y)}
  chartAt x := e.transOpenPartialHomeomorph (chartAt E (e x))
  mem_chart_source x := mem_chart_source E (e x)
  chart_mem_atlas x := ⟨e x,rfl⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_SmoothRotationalTwist
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The smooth group structure on an invariant rotational graph -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff

variable {E G K : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ,E)) ⊤ G]
  [CommGroup K] [TopologicalSpace K] [IsTopologicalGroup K]
  (α : K →* MulAut G) (τ : G →* K)
  (hinv : ∀ k g, τ (α k g) = τ g) [hτ : Fact (Continuous τ)]

attribute [local instance] semidirectProductTopology

/-- The atlas comes from the original group through the graph projection. -/
@[instance_reducible]
def rotationalTwistChartedSpace : ChartedSpace E (rotationalTwist α τ hinv) :=
  pullbackChartedSpace (rotationalTwistHomeomorph α τ hinv hτ.out)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RotationalTwistLift
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Subgroups whose multiplication is preserved by a rotational twist -/

noncomputable section
namespace PolycyclicRecognition

variable {A G K : Type*} [Group A] [Group G] [CommGroup K]
  [TopologicalSpace G] [TopologicalSpace K]
  (α : K →* MulAut G) (τ : G →* K)
  (hinv : ∀ k g, τ (α k g) = τ g)
  (f : A →* G) (hfix : ∀ a b, α ((τ (f a))⁻¹) (f b) = f b)

/-- The inverse-character graph is multiplicative on this subgroup. -/
def rotationalTwistLift : A →* rotationalTwist α τ hinv where
  toFun a := ⟨⟨f a, (τ (f a))⁻¹⟩, rfl⟩
  map_one' := by
    apply Subtype.ext
    apply SemidirectProduct.ext <;> simp
  map_mul' a b := by
    apply Subtype.ext
    apply SemidirectProduct.ext
    · change f (a * b) = f a * α ((τ (f a))⁻¹) (f b)
      rw [hfix, map_mul]
    · change (τ (f (a * b)))⁻¹ = (τ (f a))⁻¹ * (τ (f b))⁻¹
      rw [map_mul, map_mul, mul_inv_rev, mul_comm]

omit [TopologicalSpace G] [TopologicalSpace K] in
@[simp] theorem rotationalTwistLift_left (a : A) :
    (rotationalTwistLift α τ hinv f hfix a).val.left = f a := rfl

attribute [local instance] semidirectProductTopology

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RotationFactorLifts
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original nilpotent factors inside the actual rotational graph -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff

set_option maxHeartbeats 1000000 in
theorem rotation_inv_apply_of_eq_one {K U : Type*} [Group K] [Group U]
    (α : K →* MulAut U) {k : K} (hk : k = 1) (g : U) : α k⁻¹ g = g := by
  rw [hk, inv_one, map_one]
  rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RotationalTwistCharacter
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Characters preserved by a rotational twist -/

noncomputable section
namespace PolycyclicRecognition

variable {G K A : Type*} [Group G] [CommGroup K] [Monoid A]
  (α : K →* MulAut G) (τ : G →* K) (hinv : ∀ k g, τ (α k g) = τ g)
  (π : G →* A) (hπ : ∀ k g, π (α k g) = π g)

/-- An invariant character is still a homomorphism on the modified group. -/
def rotationalTwistCharacter : rotationalTwist α τ hinv →* A where
  toFun p := π p.val.left
  map_one' := π.map_one
  map_mul' p q := by
    change π (p.val.left * α p.val.right q.val.left) = π p.val.left * π q.val.left
    rw [map_mul, hπ]

@[simp] theorem rotationalTwistCharacter_apply (p : rotationalTwist α τ hinv) :
    rotationalTwistCharacter α τ hinv π hπ p = π p.val.left := rfl

attribute [local instance] semidirectProductTopology

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_TransferredHeight
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A height homomorphism from the transferred translation action

Coarse maps and a Lipschitz height map define a height quasi-action. An affine
height bound permits invariant-mean correction to a genuine homomorphism.
-/

noncomputable section

namespace PolycyclicRecognition
namespace TransferredHeight

open ThompsonNonamenability

universe u v w

variable {H : Type u} [Group H] [PseudoMetricSpace H]
variable {X : Type v} [PseudoMetricSpace X]
variable {W : Type w} [NormedAddCommGroup W]

/-- The Lipschitz height map turns the metric action defect into a uniform
height defect with the stated constant. -/
theorem composition_close (f : H → X) (r : X → H) (π : X → W)
    (hleft : ∀ h a b : H, dist (h * a) (h * b) = dist a b)
    (L K C E : ℝ) (hL : 0 ≤ L) (hK : 0 ≤ K)
    (hπ : ∀ x y, ‖π x - π y‖ ≤ L * dist x y)
    (hf : ∀ a b, dist (f a) (f b) ≤ K * dist a b + C)
    (hrf : ∀ a, dist (r (f a)) a ≤ E) (h k : H) (x : X) :
    ‖π (transferredMap f r h (transferredMap f r k x)) -
      π (transferredMap f r (h * k) x)‖ ≤ L * (K * E + C) := by
  exact (hπ _ _).trans
    (mul_le_mul_of_nonneg_left
      (transferredMap_mul_close f r hleft K C E hK hf hrf h k x) hL)

variable [NormedSpace ℝ W]

/-- The concrete quasi-action induced by `f ∘ L_h ∘ r`, with shifts `π (f h)`.
Surjectivity belongs to the height map; no exact action law is assumed. -/
def quasiAction (f : H → X) (r : X → H) (π : X → W)
    (A : H → W ≃L[ℝ] W) (hπsurj : Function.Surjective π)
    (hleft : ∀ h a b : H, dist (h * a) (h * b) = dist a b)
    (L K C E B : ℝ) (hL : 0 ≤ L) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hE : 0 ≤ E) (hB : 0 ≤ B)
    (hπ : ∀ x y, ‖π x - π y‖ ≤ L * dist x y)
    (hf : ∀ a b, dist (f a) (f b) ≤ K * dist a b + C)
    (hrf : ∀ a, dist (r (f a)) a ≤ E)
    (haffine : ∀ h x, ‖π (transferredMap f r h x) - (π (f h) + A h (π x))‖ ≤ B) :
    HeightQuasiAction H X W where
  height := π
  height_surjective := hπsurj
  maps := transferredMap f r
  shift := fun h => π (f h)
  linear := A
  error := B
  error_nonneg := hB
  affine_error := haffine
  composition_error := L * (K * E + C)
  composition_nonneg := mul_nonneg hL (add_nonneg (mul_nonneg hK hE) hC)
  composition_close := composition_close f r π hleft L K C E hL hK hπ hf hrf

end TransferredHeight
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_WeightChamberAction
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # From weight-sign agreement to chamber-image agreement -/

noncomputable section

namespace PolycyclicRecognition

open Set

variable {W I : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

def PreservesPositiveWeightRays (α : I → W →L[ℝ] ℝ) (A : W ≃ₗ[ℝ] W) : Prop :=
  ∀ i, ∃ (j : I) (r : ℝ), 0 < r ∧
    (α i).toLinearMap.comp A.toLinearMap = r • (α j).toLinearMap

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_SolvableLatticeRecognition
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The algebraic endgame for recognition of solvable Lie lattices

B. Farb and S. Weinberger, *Isometries, rigidity and universal covers*,
Annals of Mathematics 168 (2008), 915–940, Proposition 3.4, p.932,
states that every lattice in a connected solvable Lie group is polycyclic.
The lattice-polycyclicity predicate specializes this statement to uniform
lattices in connected simply connected solvable Lie groups.

Elementary amenability and the finiteness and duality theorems give virtual
polycyclicity. Dekimpe's realization then produces a finite-index lattice in
a possibly different solvable Lie group. Elementary amenability remains an
explicit premise of these conditional recognition theorems.
-/

namespace PolycyclicRecognition

/-- The simply connected uniform-lattice specialization of
Farb–Weinberger (2008), Proposition 3.4. -/
def FarbWeinbergerLatticeInput : Prop :=
  ∀ (S : SimplyConnectedSolvableLieModel) (Λ : Subgroup S.carrier),
    IsUniformLattice Λ → IsPolycyclic Λ

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_RecognitionLatticeAssembly
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Recognition from bounded-height hypotheses

Metric comparison with the virtually polycyclic group supplies the invariant
mean and the cohomological coarse comparison.

The conditional recognition theorems retain polynomial bounded-height packing
and a uniform affine height estimate as explicit geometric hypotheses.
-/

noncomputable section

namespace PolycyclicRecognition

namespace MetricQuasiEquivalence

variable {P H : Type} [Group P] [Group H] [MetricSpace P] [MetricSpace H]
  [IsIsometricSMul P P] [IsIsometricSMul H H]

/-- Finite metric balls turn the specified coarse inverse maps into the
finite-difference comparison required by the cohomological inputs. -/
def groupCoarseEquivalence (e : MetricQuasiEquivalence P H)
    (hPfinite : ∀ R : ℝ, (Metric.closedBall (1 : P) R).Finite)
    (hHfinite : ∀ R : ℝ, (Metric.closedBall (1 : H) R).Finite) :
    GroupCoarseEquivalence P H where
  toFun := e.toFun
  invFun := e.invFun
  bornologous_toFun := by
    obtain ⟨K, C, hK, _, hf⟩ := e.toFun_control
    exact groupBornologous_of_metric_bound e.toFun hHfinite hK hf
  bornologous_invFun := by
    obtain ⟨K, C, hK, _, hr⟩ := e.invFun_control
    exact groupBornologous_of_metric_bound e.invFun hPfinite hK hr
  left_error := by
    obtain ⟨E, _, hleft⟩ := e.left_close
    exact finite_groupDifference_range_of_metric_bound (e.invFun ∘ e.toFun) hPfinite hleft
  right_error := by
    obtain ⟨E, _, hright⟩ := e.right_close
    exact finite_groupDifference_range_of_metric_bound (e.toFun ∘ e.invFun) hHfinite hright

end MetricQuasiEquivalence

end PolycyclicRecognition

end

end OAI
end


