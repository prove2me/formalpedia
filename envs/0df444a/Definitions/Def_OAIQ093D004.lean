-- Prove2me | Definitions.Def_OAIQ093D004
-- name    : OAIQ093D004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T16:02:43.652045+00:00
-- url     : https://prove2.me/theorems/5830d2ef-2edf-47f9-b44c-a38eb8faa51d
-- title:
--   Definitions bundle OAIQ093D004 of the split of OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 480 declarations of OpenAI's Lean: 260 definitions, 11 instances and 209 theorems. The definitions and types are `OAI.PolycyclicRecognition.ZeroMeanL2`, `OAI.PolycyclicRecognition.actionOperatorWord`, `OAI.PolycyclicRecognition.affineProfileClass`, `OAI.PolycyclicRecognition.alternatingTupleSplit`, `OAI.PolycyclicRecognition.alternatingWordBlockEquiv`, `OAI.PolycyclicRecognition.alternatingWordIndex`, `OAI.PolycyclicRecognition.ambientUpperCentralSeries`, `OAI.PolycyclicRecognition.ambientUpperCentralToF`, `OAI.PolycyclicRecognition.appendParameterLinear`, `OAI.PolycyclicRecognition.augmentationDifference`, `OAI.PolycyclicRecognition.barAutomorphismFreeMap`, `OAI.PolycyclicRecognition.barAutomorphismMap`, `OAI.PolycyclicRecognition.basedImage`, `OAI.PolycyclicRecognition.basedTuplePosition`, `OAI.PolycyclicRecognition.basisDerivativeField`, `OAI.PolycyclicRecognition.basisExponentialProduct`, `OAI.PolycyclicRecognition.basisProductLog`, `OAI.PolycyclicRecognition.basisVolumeMultiplier`, `OAI.PolycyclicRecognition.basisWithQuotientLifts`, `OAI.PolycyclicRecognition.bilateralCochainTranslation`, `OAI.PolycyclicRecognition.bilateralCochainTwist`, `OAI.PolycyclicRecognition.bilateralDifference`, `OAI.PolycyclicRecognition.bilateralFunctorTranslation`, `OAI.PolycyclicRecognition.bilateralGauge`, `OAI.PolycyclicRecognition.bilateralPowerMap`, `OAI.PolycyclicRecognition.bilateralSum`, `OAI.PolycyclicRecognition.bilateralTranslation`, `OAI.PolycyclicRecognition.bilinearAdjointWord`, `OAI.PolycyclicRecognition.bilinearOrbitSpan`, `OAI.PolycyclicRecognition.boundedDegreeEvaluation`, `OAI.PolycyclicRecognition.boundedSchemeNormedAddCommGroup`, `OAI.PolycyclicRecognition.boundedSchemeNormedSpace`, `OAI.PolycyclicRecognition.boundedWordProducts`, `OAI.PolycyclicRecognition.boxCoordinateChange`, `OAI.PolycyclicRecognition.bundleConjugator`, `OAI.PolycyclicRecognition.bundleOutputChart`, `OAI.PolycyclicRecognition.bundleParameterChart`, `OAI.PolycyclicRecognition.bundleParameterIndex`, `OAI.PolycyclicRecognition.canonicalAffineLabel`, `OAI.PolycyclicRecognition.cartanLog` and 220 more.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory, in whole or in part: `PolycyclicRecognition_Algebra_ActionWordFiltration`, `PolycyclicRecognition_Algebra_ActiveRayConstraints`, `PolycyclicRecognition_Algebra_AlgebraGroupTangent`, `PolycyclicRecognition_Algebra_AlternatingTupleCoordinates`, `PolycyclicRecognition_Algebra_AlternatingWordOrder`, `PolycyclicRecognition_Algebra_BarAutomorphism`, `PolycyclicRecognition_Algebra_BasisQuotientLifts`, `PolycyclicRecognition_Algebra_BilateralDifference`, `PolycyclicRecognition_Algebra_BilinearGeneratorOrbit`, `PolycyclicRecognition_Algebra_BoundedGeneratorSchemes`, `PolycyclicRecognition_Algebra_BoundedWordAlgebra`, `PolycyclicRecognition_Algebra_BundleParameterCharts`, `PolycyclicRecognition_Algebra_CentralCocycleSplitting`, `PolycyclicRecognition_Algebra_CentralLayerPairing`, `PolycyclicRecognition_Algebra_CentralLayerTensor`, `PolycyclicRecognition_Algebra_CentralizerExtensionSplitting`, `PolycyclicRecognition_Algebra_ChamberBase`, `PolycyclicRecognition_Algebra_ChamberExtremeDirections`, `PolycyclicRecognition_Algebra_CharacteristicQuotientAction`, `PolycyclicRecognition_Algebra_ClassTwoCommutatorPairing`, `PolycyclicRecognition_Algebra_CofiberConnecting`, `PolycyclicRecognition_Algebra_CokernelHomModule`, `PolycyclicRecognition_Algebra_CommonEigenvectors`, `PolycyclicRecognition_Algebra_CommutingSubgroupProduct`, `PolycyclicRecognition_Algebra_ComplexMatrixExtension`, `PolycyclicRecognition_Algebra_ConjugateCharacterLog`, `PolycyclicRecognition_Algebra_ControlledProductPairs`, `PolycyclicRecognition_Algebra_CoordinateBilinearExpansion`, `PolycyclicRecognition_Algebra_CoordinateConjugation`, `PolycyclicRecognition_Algebra_CountableFreeRetract`, `PolycyclicRecognition_Algebra_CoupledBundleStates`, `PolycyclicRecognition_Algebra_CyclicCoinvariants`, `PolycyclicRecognition_Algebra_CyclicJoinDimension`, `PolycyclicRecognition_Algebra_CyclicKernelSplitting`, `PolycyclicRecognition_Algebra_CyclicParameterBasis`, `PolycyclicRecognition_Algebra_DerivationEigenvectors`, `PolycyclicRecognition_Algebra_DirectedLowerCentral`, `PolycyclicRecognition_Algebra_DynkinProductTails`, `PolycyclicRecognition_Algebra_EnvelopingDerivation`, `PolycyclicRecognition_Algebra_ExhaustiveCharacter`, `PolycyclicRecognition_Algebra_ExpandedSchemeAmplitudes`, `PolycyclicRecognition_Algebra_FactorQuotientAction`, `PolycyclicRecognition_Algebra_FilteredNilpotentPerturbation`, `PolycyclicRecognition_Algebra_FiniteCofiber`, `PolycyclicRecognition_Algebra_FiniteCutoffPartition`, `PolycyclicRecognition_Algebra_FreeAbelianLogarithm`, `PolycyclicRecognition_Algebra_GoodFiniteWordVertices`, `PolycyclicRecognition_Algebra_InducedBarTranslation`, `PolycyclicRecognition_Algebra_InducedCyclicDifference`, `PolycyclicRecognition_Algebra_InducedTranslation`, `PolycyclicRecognition_Algebra_InductionSemilinear`, `PolycyclicRecognition_Algebra_InductionTrivial`, `PolycyclicRecognition_Algebra_InfiniteCyclicDifference`, `PolycyclicRecognition_Algebra_InnerBarTranslation`, `PolycyclicRecognition_Algebra_IntegerQuotientStructure`, `PolycyclicRecognition_Algebra_InvariantDisintegration`, `PolycyclicRecognition_Algebra_LeftTangentTrivialization`, `PolycyclicRecognition_Algebra_LocallyNilpotentDimension`, `PolycyclicRecognition_Algebra_MaximalNilpotentCentralAction`, `PolycyclicRecognition_Algebra_NormalEigencharacters`, `PolycyclicRecognition_Algebra_NormalInductionCoordinates`, `PolycyclicRecognition_Algebra_NormalInductionExact`, `PolycyclicRecognition_Algebra_NormalQuotientCoordinates`, `PolycyclicRecognition_Algebra_PairCharts`, `PolycyclicRecognition_Algebra_PolyZNormalExtension`, `PolycyclicRecognition_Algebra_PolynomialCoefficientContinuity`, `PolycyclicRecognition_Algebra_PullbackInnerProduct`, `PolycyclicRecognition_Algebra_QuotientGroupAction`, `PolycyclicRecognition_Algebra_RationalCoefficientSequence`, `PolycyclicRecognition_Algebra_RegularCoefficientAction`, `PolycyclicRecognition_Algebra_RegularDualFree`, `PolycyclicRecognition_Algebra_RegularDualPairing`, `PolycyclicRecognition_Algebra_RegularDualRepresentation`, `PolycyclicRecognition_Algebra_RegularFreeEvaluation`, `PolycyclicRecognition_Algebra_RepCofiber`, `PolycyclicRecognition_Algebra_RestrictionEquivalence`, `PolycyclicRecognition_Algebra_RingTraceProjectivity`, `PolycyclicRecognition_Algebra_SpectralLogValue`, `PolycyclicRecognition_Algebra_TwistedBilateralDifference`, `PolycyclicRecognition_Algebra_UnitaryCentralFixed`, `PolycyclicRecognition_Algebra_UnitaryMautner`, `PolycyclicRecognition_Algebra_UnitaryQuotientCocycle`, `PolycyclicRecognition_Algebra_UnitarySubspaceAction`, `PolycyclicRecognition_Algebra_UpperCentralLayerMap`, `PolycyclicRecognition_Algebra_WordExtension`, `PolycyclicRecognition_Analysis_AffineProfileConcentration`, `PolycyclicRecognition_Analysis_AmenableCorrection`, `PolycyclicRecognition_Analysis_BasedImagePaths`, `PolycyclicRecognition_Analysis_BoxCoordinateChanges`, `PolycyclicRecognition_Analysis_CenteredImagePaths`, `PolycyclicRecognition_Analysis_CenteredTuplePaths`, `PolycyclicRecognition_Analysis_ChainSuccessor`, `PolycyclicRecognition_Analysis_CofiberChainConnecting`, `PolycyclicRecognition_Analysis_CofiberChainSequence`, `PolycyclicRecognition_Analysis_CompactSamplingMean`, `PolycyclicRecognition_Analysis_CompactWordCost`, `PolycyclicRecognition_Analysis_ConeProbeEndpoints`, `PolycyclicRecognition_Analysis_ConnectedEMetric`, `PolycyclicRecognition_Analysis_CountableMeasureTests`, `PolycyclicRecognition_Analysis_FactorProductPacking`, `PolycyclicRecognition_Analysis_FiniteAffineSelection`, `PolycyclicRecognition_Analysis_HaarAveraging`, `PolycyclicRecognition_Analysis_IntegralFinsuppFunctor`, `PolycyclicRecognition_Analysis_LeftInvariantRiemannianMetric`, `PolycyclicRecognition_Analysis_LinearProfilesOnBall`, `PolycyclicRecognition_Analysis_MeanSubgroup`, `PolycyclicRecognition_Analysis_OccupationSampling`, `PolycyclicRecognition_Analysis_ProbeSectionRestrictions`, `PolycyclicRecognition_Analysis_RightFolnerExpansion`, `PolycyclicRecognition_Analysis_ScaleExtension`, `PolycyclicRecognition_Analysis_StationaryCentered`, `PolycyclicRecognition_Analysis_StationarySlope`, `PolycyclicRecognition_Analysis_SupportedProbabilityRestriction`, `PolycyclicRecognition_Analysis_UniformIntervalSamples`, `PolycyclicRecognition_Finiteness_BilateralCochainShift`, `PolycyclicRecognition_Finiteness_CochainSuccessor`, `PolycyclicRecognition_Finiteness_CofiberChainHomology`, `PolycyclicRecognition_Finiteness_CofiberCochainSequence`, `PolycyclicRecognition_Finiteness_CokernelResolution`, `PolycyclicRecognition_Finiteness_ConjugationCochains`, `PolycyclicRecognition_Finiteness_CyclicExtensionFiniteness`, `PolycyclicRecognition_Finiteness_FiniteAugmentationKernel`, `PolycyclicRecognition_Finiteness_HomogeneousCochainCoordinates`, `PolycyclicRecognition_Finiteness_HomogeneousRepresentationCochains`, `PolycyclicRecognition_Finiteness_InducedBarHomology`, `PolycyclicRecognition_Finiteness_InducedResolutionHomology`, `PolycyclicRecognition_Finiteness_InducedTranslationAugmentation`, `PolycyclicRecognition_Finiteness_InfiniteCyclicResolution`, `PolycyclicRecognition_Finiteness_IntegerExtensionDuality`, `PolycyclicRecognition_Finiteness_IntegralAugmentation`, `PolycyclicRecognition_Finiteness_NestedNormalHomology`, `PolycyclicRecognition_Finiteness_NormalHomologyAction`, `PolycyclicRecognition_Finiteness_RationalExteriorHomology`, `PolycyclicRecognition_Finiteness_RepCochainMaps`, `PolycyclicRecognition_Finiteness_ResolutionHomologyNaturality`, `PolycyclicRecognition_Finiteness_ShiftedCohomologyDimensionShift`, `PolycyclicRecognition_Finiteness_SubgroupBarResolution`, `PolycyclicRecognition_Finiteness_SubsingletonGroupProjective`, `PolycyclicRecognition_Finiteness_TopHomologyKernel`, `PolycyclicRecognition_Geometry_BasisDerivativeField`, `PolycyclicRecognition_Geometry_CartanWordLogarithms`, `PolycyclicRecognition_Geometry_CompactSemidirectModel`, `PolycyclicRecognition_Geometry_ComplexTriangularExponential`, `PolycyclicRecognition_Geometry_ComplexWeightLift`, `PolycyclicRecognition_Geometry_ComplexifiedLieAutomorphism`, `PolycyclicRecognition_Geometry_CoordinateFlowDerivative`, `PolycyclicRecognition_Geometry_CoupledRootIntervals`, `PolycyclicRecognition_Geometry_ExponentialProductChart`, `PolycyclicRecognition_Geometry_ExponentialTupleCoordinates`, `PolycyclicRecognition_Geometry_IndependentWeightCone`, `PolycyclicRecognition_Geometry_NilpotentCoordinateFlow`, `PolycyclicRecognition_Geometry_NilpotentFiniteRankRootCore`, `PolycyclicRecognition_Geometry_NilpotentLinearFlow`, `PolycyclicRecognition_Geometry_OrderedSemidirectWords`, `PolycyclicRecognition_Geometry_PolynomialMinorDifferential`, `PolycyclicRecognition_Geometry_RayGroupContraction`, `PolycyclicRecognition_Geometry_RootIntervalSampling`, `PolycyclicRecognition_Geometry_SemidirectPrefixTuples`, `PolycyclicRecognition_Geometry_TriangularMatrixExponential`, `PolycyclicRecognition_Geometry_WeightChambers`, `PolycyclicRecognition_Geometry_WeightedWordNorm`, `PolycyclicRecognition_Lattices_IntegerSemidirectLattice`, `PolycyclicRecognition_Lattices_UniformLatticeTransport`, `Thompson_FiniteAverage`.
--
--   **Imports.** It imports the published bundle `Def_PolycyclicRecognition`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ093D009`, `OAIQ093D010` and `OAIQ093D011`; the statements `OAI.PolycyclicRecognition.CartanWordModel.exists_controlled_increment_volume`, `OAI_PolycyclicRecognition_CartanWordModel_exists_coupled_profile_comparison_region`, `OAI_PolycyclicRecognition_CartanWordModel_exists_metric_basepoint_comparison`, `OAI.PolycyclicRecognition.CartanWordModel.exists_sequence_path_tuple_lifts`, `OAI.PolycyclicRecognition.CartanWordModel.terminal_product_exponent_le` and `OAI_PolycyclicRecognition_cartan_cocycle_compact_words`; the proof of `OAI_PolycyclicRecognition_CartanWordModel_exists_directional_visit_bound`.
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
theorem dite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : ¬c) :
    dite c a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ActionWordFiltration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Operator words and the action filtration

The image-span filtration is controlled by products of the operators. This
turns any uniform vanishing length into the dimension bound proved for that
filtration.
-/

noncomputable section
namespace PolycyclicRecognition

variable {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]

def actionOperatorWord (D : I → Module.End K V) (w : List I) : Module.End K V :=
  (w.map D).prod

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ActiveRayConstraints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The active hyperplanes of a polyhedral extreme ray

If a direction annihilates every inequality active at an extreme ray, small
positive and negative perturbations stay in the cone. Extremality therefore
forces that direction onto the ray's line. The cone inequalities choose the
nonnegative half-line.
-/

noncomputable section

namespace PolycyclicRecognition

open Set Filter
open scoped Topology

variable {W I : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [Finite I]

def linearInequalityCone (α : I → W →L[ℝ] ℝ) : Set W := {w | ∀ i, 0 ≤ α i w}

def nonnegativeRay (w : W) : Set W := {x | ∃ r : ℝ, 0 ≤ r ∧ x = r • w}

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_AlgebraGroupTangent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Infinitesimal commutators of matrix groups

The finite-dimensional span of derivatives of curves in a subgroup records
its infinitesimal action. Differentiating group commutators twice puts the
algebra commutator into the tangent span of the derived subgroup.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Topology commutatorElement
open Filter

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
  [FiniteDimensional ℝ A] [CompleteSpace A]

omit [FiniteDimensional ℝ A] in
/-- Differentiating an inverse curve at the identity negates the tangent. -/
theorem hasDerivAt_units_inverse_at_one {c : ℝ → Aˣ} {X : A}
    (h0 : c 0 = 1) (hc : HasDerivAt (fun t => (c t : A)) X 0) :
    HasDerivAt (fun t => (((c t)⁻¹ : Aˣ) : A)) (-X) 0 := by
  have h := (hasFDerivAt_ringInverse (𝕜 := ℝ) (c 0)).comp_hasDerivAt 0 hc
  simpa only [Function.comp_def, Ring.inverse_unit, h0, inv_one, Units.val_one,
    neg_apply, ContinuousLinearMap.mulLeftRight_apply,
    one_mul, mul_one] using h

omit [CompleteSpace A] in
/-- A derivative of a curve in a finite-dimensional linear subspace stays
in that subspace. -/
theorem submodule_mem_of_hasDerivAt (M : Submodule ℝ A) {f : ℝ → A} {X : A}
    (hf : HasDerivAt f X 0) (hmem : ∀ t, f t ∈ M) : X ∈ M := by
  exact M.closed_of_finiteDimensional.mem_of_tendsto hf.tendsto_slope
    (Filter.Eventually.of_forall (fun t => M.smul_mem _ (M.sub_mem (hmem t) (hmem 0))))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_HaarAveraging
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

/-- The group length associated to the left-invariant metric used in the
Lie-group application. -/
def distanceLength [PseudoMetricSpace G] [IsIsometricSMul G G] : GroupSeminorm G where
  toFun g := dist 1 g
  map_one' := dist_self _
  mul_le' x y := by
    calc
      dist 1 (x * y) ≤ dist 1 x + dist x (x * y) := dist_triangle _ _ _
      _ = dist 1 x + dist 1 y := by
        congr 1
        simpa only [mul_one] using dist_mul_left x 1 y
  inv' x := by
    calc
      dist 1 x⁻¹ = dist x 1 := by
        simpa only [mul_one, mul_inv_cancel] using (dist_mul_left x 1 x⁻¹).symm
      _ = dist 1 x := dist_comm _ _

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_AlternatingTupleCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # From an ordered tuple to alternating pairs of coordinates -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

def alternatingTupleSplit (h : ℕ) : (Fin (h + h) → V) ≃L[ℝ] (Fin h → V × V) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun u j => (u (Fin.castAdd h j), u (Fin.natAdd h j))
      invFun := fun z => Fin.append (fun j => (z j).1) (fun j => (z j).2)
      left_inv := by
        intro u
        funext i
        refine Fin.addCases ?_ ?_ i <;> intro j <;> simp only [Fin.append_left, Fin.append_right]
      right_inv := by intro z; funext j; simp only [Fin.append_left, Fin.append_right]
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

@[simp] theorem alternatingTupleSplit_apply (h : ℕ) (u : Fin (h + h) → V) (j : Fin h) :
    alternatingTupleSplit h u j = (u (Fin.castAdd h j), u (Fin.natAdd h j)) := rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_BilinearGeneratorOrbit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Generator adjoint orbits in a fixed coordinate norm

This is the coordinate version of the spanning argument. Its exponential
operators use the fixed norm on the parameter space, so they vary
continuously with the bilinear bracket, including at limiting laws.
-/

noncomputable section

namespace PolycyclicRecognition

open Module

variable {V I : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

def bilinearAdjointWord (B : V →L[ℝ] V →L[ℝ] V) (X : I → V)
    (w : List (I × ℝ)) : V →L[ℝ] V :=
  (w.map (fun p => NormedSpace.exp (p.2 • B (X p.1)))).prod

def bilinearOrbitSpan (B : V →L[ℝ] V →L[ℝ] V) (X : I → V) : Submodule ℝ V :=
  Submodule.span ℝ (Set.range (fun p : List (I × ℝ) × I =>
    bilinearAdjointWord B X p.1 (X p.2)))

end PolycyclicRecognition

end

end OAI
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

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]

local instance coordinateConjugationNormedAddCommGroup : NormedAddCommGroup L :=
  NormedAddCommGroup.induced _ _ (Module.finBasis ℝ L).equivFun.toLinearMap
    (Module.finBasis ℝ L).equivFun.injective
local instance coordinateConjugationNormedSpace : NormedSpace ℝ L :=
  NormedSpace.induced ℝ _ _ (Module.finBasis ℝ L).equivFun.toLinearMap

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

/-- The ordered basis-exponential endpoint map. -/
def basisExponentialProduct {L G : Type*} [AddCommGroup L] [Module ℝ L]
    [Monoid G] {n : ℕ} (Exp : L → G) (b : Basis (Fin n) ℝ L) (t : Fin n → ℝ) : G :=
  (List.ofFn (fun i => Exp (t i • b i))).prod

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]

local instance exponentialProductNormedAddCommGroup : NormedAddCommGroup L :=
  NormedAddCommGroup.induced _ _ (finBasis ℝ L).equivFun.toLinearMap
    (finBasis ℝ L).equivFun.injective
local instance exponentialProductNormedSpace : NormedSpace ℝ L :=
  NormedSpace.induced ℝ _ _ (finBasis ℝ L).equivFun.toLinearMap

variable {G : Type*} [Group G] {n : ℕ} (Exp : L → G) (b : Basis (Fin n) ℝ L)

/-- Its logarithm in a global exponential bijection. -/
def basisProductLog (hExp : Function.Bijective Exp) (t : Fin n → ℝ) : L :=
  (Equiv.ofBijective Exp hExp).symm (basisExponentialProduct Exp b t)

variable (hExp : Function.Bijective Exp) (hzero : Exp 0 = 1)

include hzero in
@[simp] theorem basisProductLog_zero : basisProductLog Exp b hExp 0 = 0 := by
  apply hExp.injective
  rw [show Exp (basisProductLog Exp b hExp 0) = basisExponentialProduct Exp b 0 from
    (Equiv.ofBijective Exp hExp).apply_symm_apply _]
  simp [basisExponentialProduct, hzero]

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

def evaluateAmplitudeSlot (t : Fin n → ℝ) : ℝ ⊕ Fin n → ℝ :=
  Sum.elim id t

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_PolynomialMinorDifferential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A polynomial minor is the determinant of the actual slice derivative -/

noncomputable section

namespace PolycyclicRecognition

open MvPolynomial Matrix
open scoped BigOperators

def appendParameterLinear (n k : ℕ) : (Fin n → ℝ) →L[ℝ] (Fin (n + k) → ℝ) :=
  ContinuousLinearMap.pi (fun i => Fin.addCases
    (fun j => ContinuousLinearMap.proj j) (fun _ => 0) i)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_BundleParameterCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual global interval coordinates, grouped into source bundles -/

noncomputable section
namespace PolycyclicRecognition

/-- A coordinate permutation followed by currying. -/
def rectangularCoordinateChart {h n M : ℕ} (e : Fin h × Fin n ≃ Fin M) :
    (Fin M → ℝ) ≃L[ℝ] (Fin h → Fin n → ℝ) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun t i j => t (e (i, j))
      invFun := fun t k => t (e.symm k).1 (e.symm k).2
      left_inv := by intro t; funext k; simp
      right_inv := by intro t; funext i j; simp
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

@[simp] theorem rectangularCoordinateChart_apply {h n M : ℕ} (e : Fin h × Fin n ≃ Fin M)
    (t : Fin M → ℝ) (i : Fin h) (j : Fin n) :
    rectangularCoordinateChart e t i j = t (e (i, j)) := rfl

/-- First all first samples, then all second samples; each block is grouped
by bundle before the generator position. -/
def bundleParameterIndex (h m : ℕ) :
    Fin h × Fin (m + m) ≃ Fin (h * m + h * m) :=
  (Equiv.prodCongr (Equiv.refl (Fin h)) finSumFinEquiv.symm).trans
    ((Equiv.prodSumDistrib (Fin h) (Fin m) (Fin m)).trans
      ((Equiv.sumCongr finProdFinEquiv finProdFinEquiv).trans finSumFinEquiv))

def bundleParameterChart (h m : ℕ) :
    (Fin (h * m + h * m) → ℝ) ≃L[ℝ] (Fin h → Fin (m + m) → ℝ) :=
  rectangularCoordinateChart (bundleParameterIndex h m)

def bundleOutputChart (h n : ℕ) :
    (Fin (h * n) → ℝ) ≃L[ℝ] (Fin h → Fin n → ℝ) :=
  rectangularCoordinateChart finProdFinEquiv

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_UniformIntervalSamples
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform interval sampling has a fixed density on the full parameter cube -/

noncomputable section

namespace PolycyclicRecognition

open Set Metric MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

def uniformIntervalLaw (R : ℝ) : Measure ℝ :=
  ProbabilityTheory.cond volume (closedBall 0 R)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_AlternatingWordOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Chronological alternating words and the two polynomial input blocks -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set

def alternatingWordIndex (h : ℕ) : Fin (h * 2) ≃ Fin (h + h) :=
  finProdFinEquiv.symm.trans ((bundleParameterIndex h 1).trans (finCongr (by omega)))

variable {G : Type*} [MeasurableSpace G]

def alternatingWordBlockEquiv (h : ℕ) :
    (Fin (h * 2) → G) ≃ᵐ (Fin (h + h) → G) :=
  MeasurableEquiv.piCongrLeft (fun _ => G) (alternatingWordIndex h)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_ResolutionHomologyNaturality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A coefficient-natural comparison with a projective resolution

The comparison uses the bar resolution and a fixed homotopy equivalence of
projective resolutions, so changing coefficients commutes with it.
-/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits HomologicalComplex Rep
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G] {A B : Rep ℤ G}

def coefficientTensorChainMap (P : ChainComplex (Rep ℤ G) ℕ) (f : A ⟶ B) :
    P.coinvariantsTensorObj A ⟶ P.coinvariantsTensorObj B :=
  (NatTrans.mapHomologicalComplex ((Rep.coinvariantsTensor ℤ G).map f)
    (ComplexShape.down ℕ)).app P

def coefficientNaturalHomologyIso [DecidableEq G]
    (P : ProjectiveResolution (Rep.trivial ℤ G ℤ)) (A : Rep ℤ G) (n : ℕ) :
    groupHomology A n ≅ (P.complex.coinvariantsTensorObj A).homology n :=
  (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n).mapIso
      (groupHomology.inhomogeneousChainsIso A) ≪≫
    isoOfQuasiIsoAt
      (((Rep.coinvariantsTensor ℤ G).obj A).mapHomotopyEquiv
        (ProjectiveResolution.homotopyEquiv (barResolution ℤ G) P)).hom n

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_SubgroupBarResolution
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

omit H in
theorem barResolution_pi_single (x : Fin 0 → G) (g : G) (r : ℤ) :
    ((Rep.barResolution ℤ G).π.f 0).hom
      (Finsupp.single x (MonoidAlgebra.single g r)) = r := by
  change (Rep.standardComplex.ε ℤ G).hom
    ((Rep.diagonalSuccIsoFree ℤ G 0).inv.hom
      (Finsupp.single x (MonoidAlgebra.single g r))) = r
  have hx : (Rep.diagonalSuccIsoFree ℤ G 0).inv.hom
      (Finsupp.single x (MonoidAlgebra.single g r)) =
      MonoidAlgebra.single (g • Fin.partialProd x) r := by
    simp only [Rep.diagonalSuccIsoFree, Rep.diagonalSuccIsoTensorTrivial, Iso.trans_inv,
      Rep.hom_comp, Representation.IntertwiningMap.comp_apply]
    have hs : (Rep.leftRegularTensorTrivialIsoFree ℤ G (Fin 0 → G)).inv.hom
        (Finsupp.single x (MonoidAlgebra.single g r)) =
        MonoidAlgebra.single g 1 ⊗ₜ[ℤ] MonoidAlgebra.single x r :=
      Representation.leftRegularTensorTrivialIsoFree_symm_apply_single_single x g r
    rw [hs]
    simp only [Action.tensorObj_V, Rep.tensor_V, Rep.tensor_ρ]
    have hμ := Representation.LinearizeMonoidal.μ_apply_single_single (k := ℤ)
      (X := Action.leftRegular G) (Y := Action.trivial G (Fin 0 → G)) g x 1 r
    have hm := Representation.linearizeMap_single (k := ℤ)
      (Action.diagonalSuccIsoTensorTrivial G 0).inv (g, x) ((1 : ℤ) * r)
    refine ((congrArg (fun z => Representation.linearizeMap
      (Action.diagonalSuccIsoTensorTrivial G 0).inv z) hμ).trans hm).trans ?_
    simp only [one_mul]
    congr 1
    exact Action.diagonalSuccIsoTensorTrivial_inv_hom_apply g x
  rw [hx]
  simp [Rep.standardComplex.ε]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_InnerBarTranslation
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

theorem bar_d_single_single (n : ℕ) (x : Fin (n + 1) → G) (h : G) (r : ℤ) :
    (Rep.barComplex.d ℤ G n).hom (Finsupp.single x (MonoidAlgebra.single h r)) =
      Finsupp.single (fun i => x i.succ) (MonoidAlgebra.single (h * x 0) r) +
      ∑ j : Fin (n + 1), Finsupp.single (j.contractNth (· * ·) x)
        (MonoidAlgebra.single h (r * (-1 : ℤ) ^ (j.val + 1))) := by
  have he : Finsupp.single x (MonoidAlgebra.single h r) =
      r • (Rep.free ℤ G (Fin (n + 1) → G)).ρ h
        (Finsupp.single x (MonoidAlgebra.single 1 1)) := by
    rw [Representation.free_single_single, mul_one]
    simp
  rw [he, map_zsmul, Rep.hom_comm_apply, Rep.barComplex.d_single]
  simp only [map_add, map_sum, Representation.free_single_single, smul_add, Finset.smul_sum,
    Finsupp.smul_single, MonoidAlgebra.smul_single, smul_eq_mul, mul_one]


end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_BarAutomorphism
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The bar-resolution map induced by a group automorphism -/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

def barAutomorphismFreeMap (e : G ≃* G) (n : ℕ) :
    Rep.free ℤ G (Fin n → G) ⟶ Rep.res e.toMonoidHom (Rep.free ℤ G (Fin n → G)) :=
  Rep.freeLift ℤ G _ (fun x => Finsupp.single (e ∘ x) (MonoidAlgebra.single 1 1))

theorem barAutomorphismFreeMap_single (e : G ≃* G) (n : ℕ)
    (x : Fin n → G) (g : G) (r : ℤ) :
    (barAutomorphismFreeMap e n).hom (Finsupp.single x (MonoidAlgebra.single g r)) =
      Finsupp.single (e ∘ x) (MonoidAlgebra.single (e g) r) := by
  change Representation.freeLift (Rep.res e.toMonoidHom (Rep.free ℤ G (Fin n → G))).ρ
    (fun y => Finsupp.single (e ∘ y) (MonoidAlgebra.single 1 1))
      (Finsupp.single x (MonoidAlgebra.single g r)) = _
  rw [Representation.freeLift_single_single]
  change r • Representation.free ℤ G (Fin n → G) (e g)
      (Finsupp.single (e ∘ x) (MonoidAlgebra.single 1 1)) = _
  rw [Representation.free_single_single, mul_one]
  simp

theorem barAutomorphismFreeMap_d (e : G ≃* G) (n : ℕ) :
    barAutomorphismFreeMap e (n + 1) ≫ (Rep.resFunctor e.toMonoidHom).map
        (Rep.barComplex.d ℤ G n) =
      Rep.barComplex.d ℤ G n ≫ barAutomorphismFreeMap e n := by
  apply Rep.free_ext
  intro x
  change (Rep.barComplex.d ℤ G n).hom
      ((barAutomorphismFreeMap e (n + 1)).hom (Finsupp.single x (MonoidAlgebra.single 1 1))) =
    (barAutomorphismFreeMap e n).hom
      ((Rep.barComplex.d ℤ G n).hom (Finsupp.single x (MonoidAlgebra.single 1 1)))
  rw [barAutomorphismFreeMap_single, map_one, Rep.barComplex.d_single,
    Rep.barComplex.d_single, map_add, map_sum, barAutomorphismFreeMap_single]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [barAutomorphismFreeMap_single, map_one]
  congr 1
  exact (Fin.comp_contractNth (· * ·) (· * ·) (f := e.toMonoidHom)
    (map_mul _) j x).symm

def barAutomorphismMap (e : G ≃* G) : Rep.barComplex ℤ G ⟶
    ((Rep.resFunctor e.toMonoidHom).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (Rep.barComplex ℤ G) :=
  ChainComplex.ofHom (barAutomorphismFreeMap e) (fun n => by
    change barAutomorphismFreeMap e (n + 1) ≫
        (Rep.resFunctor e.toMonoidHom).map ((Rep.barComplex ℤ G).d (n + 1) n) =
      (Rep.barComplex ℤ G).d (n + 1) n ≫ barAutomorphismFreeMap e n
    simpa only [ChainComplex.of_d] using barAutomorphismFreeMap_d e n)

theorem barAutomorphismFreeMap_augmentation (e : G ≃* G) :
    barAutomorphismFreeMap e 0 ≫ Rep.resMap e.toMonoidHom ((Rep.barResolution ℤ G).π.f 0) =
      (Rep.barResolution ℤ G).π.f 0 := by
  apply Rep.free_ext
  intro x
  change ((Rep.barResolution ℤ G).π.f 0).hom
      ((barAutomorphismFreeMap e 0).hom (Finsupp.single x (MonoidAlgebra.single 1 1))) =
    ((Rep.barResolution ℤ G).π.f 0).hom (Finsupp.single x (MonoidAlgebra.single 1 1))
  rw [barAutomorphismFreeMap_single, barResolution_pi_single, barResolution_pi_single]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_BasisQuotientLifts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A basis adapted to specified quotient lifts -/

noncomputable section
namespace PolycyclicRecognition

open Module Set

variable {𝕜 : Type*} [Field 𝕜]

variable {V I J : Type*} [AddCommGroup V] [Module 𝕜 V] (U : Submodule 𝕜 V)
  (bU : Basis I 𝕜 U) (bQ : Basis J 𝕜 (V ⧸ U))
  (lift : J → V) (hlift : ∀ j, U.mkQ (lift j) = bQ j)

def basisWithQuotientLifts : Basis (I ⊕ J) 𝕜 V := by
  let v : I ⊕ J → V := Sum.elim (fun i => (bU i : V)) lift
  apply Basis.mk (v := v)
  · apply LinearIndependent.sumElim_of_quotient
    · exact bU.linearIndependent
    · change LinearIndependent 𝕜 (fun j => U.mkQ (lift j))
      simpa only [hlift] using bQ.linearIndependent
  · dsimp only [v]
    rw [Set.Sum.elim_range, Submodule.span_union,
      show range (fun i => (bU i : V)) = U.subtype '' range bU by
        ext x; simp only [mem_range, mem_image]; aesop,
      ← Submodule.map_span, bU.span_eq, Submodule.map_top, Submodule.range_subtype,
      top_le_iff, ← Submodule.map_mkQ_eq_top, Submodule.map_span, ← Set.range_comp]
    simpa only [Function.comp_def, hlift] using bQ.span_eq

@[simp] theorem basisWithQuotientLifts_inl (i : I) :
    basisWithQuotientLifts U bU bQ lift hlift (Sum.inl i) = (bU i : V) := by
  simp only [basisWithQuotientLifts, Basis.coe_mk, Sum.elim_inl]

@[simp] theorem basisWithQuotientLifts_inr (j : J) :
    basisWithQuotientLifts U bU bQ lift hlift (Sum.inr j) = lift j := by
  simp only [basisWithQuotientLifts, Basis.coe_mk, Sum.elim_inr]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CyclicCoinvariants
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coinvariants of an infinite or finite cyclic group -/

noncomputable section
namespace PolycyclicRecognition

open Representation

variable {k G V : Type*} [CommRing k] [Group G] [AddCommGroup V] [Module k V]

theorem cyclic_coinvariantsKer_eq_range (ρ : Representation k G V) (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    Coinvariants.ker ρ = LinearMap.range (ρ g - LinearMap.id) := by
  have hnat (n : ℕ) (v : V) :
      ρ (g ^ n) v - v ∈ LinearMap.range (ρ g - LinearMap.id) := by
    cases n with
    | zero => simp
    | succ n =>
        exact ⟨_, ρ.apply_sub_id_partialSum_eq n g v⟩
  have hint (n : ℤ) (v : V) :
      ρ (g ^ n) v - v ∈ LinearMap.range (ρ g - LinearMap.id) := by
    obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
    · simpa only [zpow_natCast] using hnat m v
    · have hc : ρ (g ^ m) (ρ ((g ^ m)⁻¹) v) = v := by
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
      have hp := hnat m (ρ ((g ^ m)⁻¹) v)
      rw [hc] at hp
      simpa only [zpow_neg, zpow_natCast, neg_sub] using
        (LinearMap.range (ρ g - LinearMap.id)).neg_mem hp
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨a, v⟩, rfl⟩
    obtain ⟨n, rfl⟩ := hg a
    exact hint n v
  · rintro _ ⟨v, rfl⟩
    exact Coinvariants.sub_mem_ker g v

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_BilateralDifference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The difference operator on a bilateral direct sum

This is the algebraic calculation needed in the cyclic-extension duality
argument. It applies to arbitrary coefficient modules.
-/

noncomputable section
namespace PolycyclicRecognition

open Representation

variable (k M : Type*) [CommRing k] [AddCommGroup M] [Module k M]

def bilateralTranslation : Representation k (Multiplicative ℤ) (ℤ →₀ M) where
  toFun z := (Finsupp.domLCongr (Equiv.addLeft z.toAdd)).toLinearMap
  map_one' := by
    apply LinearMap.ext
    intro f
    ext i
    change f (-(0 : ℤ) + i) = f i
    simp
  map_mul' x y := by
    apply LinearMap.ext
    intro f
    ext i
    change f (-(x.toAdd + y.toAdd) + i) = f (-y.toAdd + (-x.toAdd + i))
    congr 1
    omega

@[simp] theorem bilateralTranslation_apply (z : Multiplicative ℤ) (f : ℤ →₀ M) (i : ℤ) :
    bilateralTranslation k M z f i = f (-z.toAdd + i) := rfl

@[simp] theorem bilateralTranslation_single (z : Multiplicative ℤ) (i : ℤ) (m : M) :
    bilateralTranslation k M z (Finsupp.single i m) = Finsupp.single (z.toAdd + i) m :=
  Finsupp.domLCongr_single _ _ _

def bilateralSum : (ℤ →₀ M) →ₗ[k] M :=
  Finsupp.lsum k fun _ => LinearMap.id

@[simp] theorem bilateralSum_single (i : ℤ) (m : M) :
    bilateralSum k M (Finsupp.single i m) = m := by simp [bilateralSum]

theorem bilateralSum_translation (z : Multiplicative ℤ) (f : ℤ →₀ M) :
    bilateralSum k M (bilateralTranslation k M z f) = bilateralSum k M f := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [hf, hg]
  | single i m => simp

theorem bilateral_sub_sum_mem_coinvariants (f : ℤ →₀ M) :
    f - Finsupp.single 0 (bilateralSum k M f) ∈ Coinvariants.ker (bilateralTranslation k M) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
      rw [map_add, Finsupp.single_add]
      convert (Coinvariants.ker (bilateralTranslation k M)).add_mem hf hg using 1
      all_goals try with_reducible_and_instances rfl
      abel
  | single i m =>
      rw [bilateralSum_single]
      simpa using Coinvariants.sub_mem_ker (ρ := bilateralTranslation k M)
        (Multiplicative.ofAdd i) (Finsupp.single 0 m)

theorem bilateralSum_ker :
    LinearMap.ker (bilateralSum k M) = Coinvariants.ker (bilateralTranslation k M) := by
  apply le_antisymm
  · intro f hf
    have hz : bilateralSum k M f = 0 := hf
    simpa only [hz, Finsupp.single_zero, sub_zero] using bilateral_sub_sum_mem_coinvariants k M f
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨z, f⟩, rfl⟩
    change bilateralSum k M (bilateralTranslation k M z f - f) = 0
    rw [map_sub, bilateralSum_translation, sub_self]

theorem multiplicativeInt_generator (z : Multiplicative ℤ) :
    z ∈ Subgroup.zpowers (Multiplicative.ofAdd (1 : ℤ)) := by
  refine ⟨z.toAdd, ?_⟩
  apply Multiplicative.toAdd.injective
  simp

def bilateralDifference : (ℤ →₀ M) →ₗ[k] (ℤ →₀ M) :=
  bilateralTranslation k M (Multiplicative.ofAdd 1) - LinearMap.id

theorem bilateralSum_ker_eq_range :
    LinearMap.ker (bilateralSum k M) = LinearMap.range (bilateralDifference k M) :=
  (bilateralSum_ker k M).trans
    (cyclic_coinvariantsKer_eq_range _ _ multiplicativeInt_generator)

theorem bilateral_fixed_eq_zero (f : ℤ →₀ M)
    (hf : bilateralTranslation k M (Multiplicative.ofAdd 1) f = f) : f = 0 := by
  have hinv : f ∈ (bilateralTranslation k M).invariants :=
    (mem_invariants_iff_of_forall_mem_zpowers _ _ multiplicativeInt_generator f).mpr hf
  obtain ⟨a, ha⟩ := f.support.exists_notMem
  have hzero : f a = 0 := Finsupp.notMem_support_iff.mp ha
  ext b
  have hb := congrArg (fun u : ℤ →₀ M => u b)
    (hinv (Multiplicative.ofAdd (b - a)))
  simp only [bilateralTranslation_apply, toAdd_ofAdd] at hb
  have he : -(b - a) + b = a := by omega
  rw [he, hzero] at hb
  exact hb.symm

theorem bilateralDifference_injective : Function.Injective (bilateralDifference k M) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm ?_ bot_le
  intro f hf
  exact bilateral_fixed_eq_zero k M f (sub_eq_zero.mp hf)

theorem bilateralSum_surjective : Function.Surjective (bilateralSum k M) :=
  fun m => ⟨Finsupp.single 0 m, bilateralSum_single k M 0 m⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_BoundedGeneratorSchemes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quantitative bounds for a fixed generator scheme

The fixed conjugating words give a common amplitude bound; scaling a
logarithm into the local product chart and repeating the resulting word
covers any prescribed bounded logarithmic set.
-/

noncomputable section

namespace PolycyclicRecognition

open Module

variable {I : Type*}

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {G : Type*} [Group G]

local instance boundedSchemeNormedAddCommGroup : NormedAddCommGroup L :=
  NormedAddCommGroup.induced _ _ (finBasis ℝ L).equivFun.toLinearMap
    (finBasis ℝ L).equivFun.injective
local instance boundedSchemeNormedSpace : NormedSpace ℝ L :=
  NormedSpace.induced ℝ _ _ (finBasis ℝ L).equivFun.toLinearMap

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_BoundedWordAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite algebras from a bound on generator products

This is the finite-dimensionality step for the truncated enveloping algebra
used to extend a nilpotent representation by derivations.
-/

noncomputable section
namespace PolycyclicRecognition

open Set

variable {R A : Type*} [Field R] [Ring A] [Algebra R A]
  {ι : Type*} [Fintype ι] (j : ι → A) (c : ℕ)

/-- Products with at most the specified number of letters. -/
def boundedWordProducts : Set A :=
  Set.range (fun w : Σ k : Fin (c + 1), Fin k → ι => (List.ofFn (fun i => j (w.2 i))).prod)

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

variable [NormedSpace ℝ W] [CompleteSpace W]

omit [CompleteSpace W] in
/-- The averaging operator is bounded by one on a probability space. -/
theorem norm_integral_le_l2 [IsProbabilityMeasure μ] (v : Lp W 2 μ) :
    ‖∫ x, v x ∂μ‖ ≤ ‖v‖ := by
  calc
    ‖∫ x, v x ∂μ‖ ≤ (∫⁻ x, ENNReal.ofReal ‖v x‖ ∂μ).toReal :=
      norm_integral_le_lintegral_norm _
    _ = (eLpNorm v 1 μ).toReal := by
      rw [eLpNorm_one_eq_lintegral_enorm]
      simp only [ofReal_norm]
    _ ≤ (eLpNorm v 2 μ).toReal := ENNReal.toReal_mono (Lp.eLpNorm_ne_top v)
      (eLpNorm_le_eLpNorm_of_exponent_le (hf := by first | fun_prop | assumption | solve_by_elim | exact Lp.aestronglyMeasurable _ | (apply Measurable.aestronglyMeasurable; solve_by_elim) | (apply Continuous.aestronglyMeasurable; solve_by_elim) | (apply Measurable.aestronglyMeasurable; measurability) | measurability) (by norm_num))
    _ = ‖v‖ := rfl

/-- Averaging as an actual bounded linear operator on `L²`. -/
def stationaryL2Mean [IsProbabilityMeasure μ] : Lp W 2 μ →L[ℝ] W :=
  LinearMap.mkContinuous
    { toFun := fun v => ∫ x, v x ∂μ
      map_add' := fun v w => by
        calc
          (∫ x, (v + w) x ∂μ) = ∫ x, v x + w x ∂μ := integral_congr_ae (Lp.coeFn_add v w)
          _ = _ := integral_add ((Lp.memLp v).integrable (by norm_num))
            ((Lp.memLp w).integrable (by norm_num))
      map_smul' := fun r v => by
        calc
          (∫ x, (r • v) x ∂μ) = ∫ x, r • v x ∂μ := integral_congr_ae (Lp.coeFn_smul r v)
          _ = _ := integral_smul r _ }
    1 (fun v => by change ‖∫ x, v x ∂μ‖ ≤ 1 * ‖v‖; simpa using norm_integral_le_l2 μ v)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_UnitaryCentralFixed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The central fixed subspace in a unitary representation

The central fixed subspace is closed and invariant under the whole group.
Its orthogonal projection therefore commutes with the representation. These
are the concrete splitting facts for the nilpotent cohomology induction.
-/

noncomputable section

namespace PolycyclicRecognition

open Set

variable {G E : Type*} [Group G] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (ρ : G →* (E ≃ₗᵢ[ℝ] E))

def unitaryCentralFixed : Submodule ℝ E where
  carrier := {x | ∀ z : Subgroup.center G, ρ z x = x}
  zero_mem' := fun z => map_zero (ρ z)
  add_mem' hx hy z := by rw [map_add, hx z, hy z]
  smul_mem' c x hx z := by rw [map_smul, hx z]

theorem isClosed_unitaryCentralFixed : IsClosed (unitaryCentralFixed ρ : Set E) := by
  have h := isClosed_iInter (fun z : Subgroup.center G =>
    isClosed_eq (ρ z).continuous continuous_id)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  simp [unitaryCentralFixed]

theorem unitaryCentralFixed_map (g : G) {x : E} (hx : x ∈ unitaryCentralFixed ρ) :
    ρ g x ∈ unitaryCentralFixed ρ := by
  intro z
  have hz := Subgroup.mem_center_iff.mp z.property g
  calc
    ρ z (ρ g x) = ρ ((z : G) * g) x := by rw [map_mul]; rfl
    _ = ρ (g * (z : G)) x := by rw [hz]
    _ = ρ g (ρ z x) := by rw [map_mul]; rfl
    _ = ρ g x := by rw [hx z]

theorem unitaryCentralFixed_map_eq (g : G) :
    (unitaryCentralFixed ρ).map (ρ g).toLinearEquiv.toLinearMap = unitaryCentralFixed ρ := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact unitaryCentralFixed_map ρ g hx
  · intro hy
    refine ⟨ρ g⁻¹ y, unitaryCentralFixed_map ρ g⁻¹ hy, ?_⟩
    change ρ g (ρ g⁻¹ y) = y
    have he : ρ g * ρ g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    exact congrArg (fun f : E ≃ₗᵢ[ℝ] E => f y) he

theorem unitaryCentralFixed_orthogonal_map (g : G) {x : E}
    (hx : x ∈ (unitaryCentralFixed ρ)ᗮ) : ρ g x ∈ (unitaryCentralFixed ρ)ᗮ := by
  have he := (unitaryCentralFixed ρ).map_orthogonal_equiv (ρ g)
  rw [unitaryCentralFixed_map_eq ρ g] at he
  rw [← he]
  exact Submodule.mem_map_of_mem hx

instance unitaryCentralFixed_complete [CompleteSpace E] : CompleteSpace (unitaryCentralFixed ρ) :=
  (isClosed_unitaryCentralFixed ρ).completeSpace_coe

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_UnitarySubspaceAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Restricting a unitary representation to an invariant closed summand -/

noncomputable section

namespace PolycyclicRecognition

variable {G E : Type*} [Group G] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (K : Submodule ℝ E)
  (hK : ∀ (g : G) (x : E), x ∈ K → ρ g x ∈ K)

def unitarySubspaceEquiv (g : G) : K ≃ₗᵢ[ℝ] K where
  toFun x := ⟨ρ g x, hK g x x.property⟩
  invFun x := ⟨ρ g⁻¹ x, hK g⁻¹ x x.property⟩
  left_inv x := by
    apply Subtype.ext
    change ρ g⁻¹ (ρ g x) = x
    have he : ρ g⁻¹ * ρ g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
    exact congrArg (fun f : E ≃ₗᵢ[ℝ] E => f x) he
  right_inv x := by
    apply Subtype.ext
    change ρ g (ρ g⁻¹ x) = x
    have he : ρ g * ρ g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    exact congrArg (fun f : E ≃ₗᵢ[ℝ] E => f x) he
  map_add' x y := by apply Subtype.ext; exact map_add (ρ g) (x : E) (y : E)
  map_smul' c x := by apply Subtype.ext; exact map_smul (ρ g) c (x : E)
  norm_map' x := (ρ g).norm_map x

def unitarySubspaceAction : G →* (K ≃ₗᵢ[ℝ] K) where
  toFun := unitarySubspaceEquiv ρ K hK
  map_one' := by
    ext x
    change ρ 1 x = x
    rw [map_one]
    rfl
  map_mul' g h := by
    ext x
    change ρ (g * h) x = ρ g (ρ h x)
    rw [map_mul]
    rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_UnitaryQuotientCocycle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Descending a central-trivial unitary cocycle to the central quotient -/

noncomputable section

namespace PolycyclicRecognition

variable {G E : Type*} [Group G] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (hz : ∀ z : Subgroup.center G, ρ z = 1)

def centerQuotientUnitary : (G ⧸ Subgroup.center G) →* (E ≃ₗᵢ[ℝ] E) :=
  QuotientGroup.lift (Subgroup.center G) ρ (fun g hg => hz ⟨g, hg⟩)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CentralCocycleSplitting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Splitting a cocycle into central fixed and moving summands -/

noncomputable section

namespace PolycyclicRecognition

variable {G E : Type*} [Group G] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (ρ : G →* (E ≃ₗᵢ[ℝ] E))

def centralFixedUnitary : G →* ((unitaryCentralFixed ρ) ≃ₗᵢ[ℝ] (unitaryCentralFixed ρ)) :=
  unitarySubspaceAction ρ (unitaryCentralFixed ρ) (fun g _ hx => unitaryCentralFixed_map ρ g hx)

def centralMovingUnitary : G →* ((unitaryCentralFixed ρ)ᗮ ≃ₗᵢ[ℝ] (unitaryCentralFixed ρ)ᗮ) :=
  unitarySubspaceAction ρ (unitaryCentralFixed ρ)ᗮ
    (fun g _ hx => unitaryCentralFixed_orthogonal_map ρ g hx)

variable [CompleteSpace E]

def centralFixedProjection : E →L[ℝ] unitaryCentralFixed ρ :=
  (unitaryCentralFixed ρ).orthogonalProjectionOnto

def centralMovingProjection : E →L[ℝ] (unitaryCentralFixed ρ)ᗮ :=
  (unitaryCentralFixed ρ)ᗮ.orthogonalProjectionOnto

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ClassTwoCommutatorPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual central commutator pairing

For a group of class at most two, the commutator is a bilinear alternating
map on its abelianization. The target here is the actual center, not a
formal copy of the abelianization. This is the first central-layer map
needed in the nilpotent homology argument.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped commutatorElement IsMulCommutative
variable {G : Type} [Group G]

theorem commutator_mul_left_of_central (a b c : G)
    (hb : ⁅b, c⁆ ∈ Subgroup.center G) :
    ⁅a * b, c⁆ = ⁅a, c⁆ * ⁅b, c⁆ := by
  have hc : Commute a ⁅b, c⁆ := Subgroup.mem_center_iff.mp hb a
  rw [commutatorElement_mul_left_eq_conj_mul, hc.eq, mul_inv_cancel_right]
  exact (Subgroup.mem_center_iff.mp hb ⁅a, c⁆).symm

theorem commutator_mul_right_of_central (a b c : G)
    (hc : ⁅a, c⁆ ∈ Subgroup.center G) :
    ⁅a, b * c⁆ = ⁅a, b⁆ * ⁅a, c⁆ := by
  have hb : Commute b ⁅a, c⁆ := Subgroup.mem_center_iff.mp hc b
  rw [commutatorElement_mul_right_eq_mul_conj, hb.right_comm, mul_inv_cancel_right]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CentralLayerPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bilinear commutators at an actual central-series step

If commutators with `N` are central, they factor through the abelianization
of the ambient group and any central quotient of `N`. This applies at the
last nonzero step of a lower central series.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped commutatorElement IsMulCommutative
variable {G : Type} [Group G] (N : Subgroup G)

def centralLayerCommutatorLeft (h : ⁅(⊤ : Subgroup G), N⁆ ≤ Subgroup.center G)
    (b : N) : G →* Subgroup.center G where
  toFun a := ⟨⁅a, (b : G)⁆, h (Subgroup.commutator_mem_commutator
    (Subgroup.mem_top _) b.property)⟩
  map_one' := Subtype.ext (commutatorElement_one_left _)
  map_mul' a c := Subtype.ext (commutator_mul_left_of_central a c b
    (h (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) b.property)))

def centralLayerCommutatorRight (h : ⁅(⊤ : Subgroup G), N⁆ ≤ Subgroup.center G)
    (a : Abelianization G) : N →* Subgroup.center G where
  toFun b := Abelianization.lift (centralLayerCommutatorLeft N h b) a
  map_one' := by
    induction a using QuotientGroup.induction_on with | H a =>
      exact Subtype.ext (commutatorElement_one_right a)
  map_mul' b c := by
    induction a using QuotientGroup.induction_on with | H a =>
      exact Subtype.ext (commutator_mul_right_of_central a b c
        (h (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) c.property)))

def centralLayerQuotientHom (h : ⁅(⊤ : Subgroup G), N⁆ ≤ Subgroup.center G)
    (K : Subgroup N) [K.Normal] (hK : K.map N.subtype ≤ Subgroup.center G)
    (a : Abelianization G) : (N ⧸ K) →* Subgroup.center G :=
  QuotientGroup.lift K (centralLayerCommutatorRight N h a) (by
    intro b hb
    induction a using QuotientGroup.induction_on with | H a =>
      apply Subtype.ext
      exact (show Commute a (b : G) from
        Subgroup.mem_center_iff.mp (hK ⟨b, hb, rfl⟩) a).commutator_eq)

def centralLayerPairing (h : ⁅(⊤ : Subgroup G), N⁆ ≤ Subgroup.center G)
    (K : Subgroup N) [K.Normal] [IsMulCommutative (N ⧸ K)]
    (hK : K.map N.subtype ≤ Subgroup.center G) :
    Additive (Abelianization G) →ₗ[ℤ]
      Additive (N ⧸ K) →ₗ[ℤ] Additive (Subgroup.center G) where
  toFun a := (centralLayerQuotientHom N h K hK a.toMul).toAdditive.toIntLinearMap
  map_add' a b := by
    apply LinearMap.ext
    intro c
    induction c using QuotientGroup.induction_on with | H c =>
      change Additive.ofMul (Abelianization.lift (centralLayerCommutatorLeft N h c)
        (a.toMul * b.toMul)) = _
      exact congrArg Additive.ofMul (map_mul
        (Abelianization.lift (centralLayerCommutatorLeft N h c)) a.toMul b.toMul)
  map_smul' n a := by
    apply LinearMap.ext
    intro c
    induction c using QuotientGroup.induction_on with | H c =>
      change Additive.ofMul (Abelianization.lift (centralLayerCommutatorLeft N h c)
        (a.toMul ^ n)) = _
      exact congrArg Additive.ofMul (map_zpow
        (Abelianization.lift (centralLayerCommutatorLeft N h c)) a.toMul n)

@[simp] theorem centralLayerPairing_value
    (h : ⁅(⊤ : Subgroup G), N⁆ ≤ Subgroup.center G)
    (K : Subgroup N) [K.Normal] [IsMulCommutative (N ⧸ K)]
    (hK : K.map N.subtype ≤ Subgroup.center G) (a : G) (b : N) :
    centralLayerPairing N h K hK (Additive.ofMul (Abelianization.of a))
      (Additive.ofMul ((QuotientGroup.mk' K) b)) =
      Additive.ofMul ⟨⁅a, (b : G)⁆, h (Subgroup.commutator_mem_commutator
        (Subgroup.mem_top _) b.property)⟩ := rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CentralLayerTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Tensor generators of a central commutator layer -/

noncomputable section
namespace PolycyclicRecognition
open scoped TensorProduct commutatorElement IsMulCommutative
variable {G : Type} [Group G] (N : Subgroup G)
variable (h : ⁅(⊤ : Subgroup G), N⁆ ≤ Subgroup.center G)
  (K : Subgroup N) [K.Normal] [IsMulCommutative (N ⧸ K)]
  (hK : K.map N.subtype ≤ Subgroup.center G)

def centralLayerSubmodule : Submodule ℤ (Additive (Subgroup.center G)) :=
  (⁅(⊤ : Subgroup G), N⁆.subgroupOf (Subgroup.center G)).toAddSubgroup.toIntSubmodule

theorem centralLayerPairing_mem (a : Additive (Abelianization G)) (b : Additive (N ⧸ K)) :
    centralLayerPairing N h K hK a b ∈ centralLayerSubmodule N := by
  induction a using QuotientGroup.induction_on with | H a =>
    induction b using QuotientGroup.induction_on with | H b =>
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) b.property

def centralLayerTensor :
    (Additive (Abelianization G) ⊗[ℤ] Additive (N ⧸ K)) →ₗ[ℤ]
      Additive (Subgroup.center G) :=
  TensorProduct.lift (centralLayerPairing N h K hK)

def centralLayerAddEquiv [IsMulCommutative (⁅(⊤ : Subgroup G), N⁆ : Subgroup G)] :
    centralLayerSubmodule N ≃+ Additive (⁅(⊤ : Subgroup G), N⁆ : Subgroup G) where
  toFun z := Additive.ofMul ⟨z.val.toMul.val, z.property⟩
  invFun z := ⟨Additive.ofMul ⟨z.toMul.val, h z.toMul.property⟩, z.toMul.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CentralizerExtensionSplitting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Splitting an extension using a bijective twisted-difference map

A central quotient element with bijective Lang map on the kernel selects a
unique commuting lift in every quotient fiber. These lifts form a subgroup.
-/

noncomputable section
namespace PolycyclicRecognition
variable {N G Q : Type*} [Group N] [Group G] [Group Q]
  (S : GroupExtension N G Q) (t : G)

/-- The twisted difference on the kernel, with the order needed for correcting
left coset representatives. -/
def extensionLangMap (n : N) : N := n⁻¹ * S.conjAct t n

@[simp] theorem extensionLangMap_one : extensionLangMap S t 1 = 1 := by
  simp [extensionLangMap]

def centralizerProjection : Subgroup.centralizer ({t} : Set G) →* Q :=
  S.rightHom.comp (Subgroup.centralizer ({t} : Set G)).subtype

theorem centralizerProjection_surjective
    (ht : ∀ q : Q, Commute (S.rightHom t) q)
    (hLang : Function.Surjective (extensionLangMap S t)) :
    Function.Surjective (centralizerProjection S t) := by
  intro q
  obtain ⟨g, hg⟩ := S.rightHom_surjective q
  have hdmem : t * g * t⁻¹ * g⁻¹ ∈ S.inl.range := by
    rw [S.range_inl_eq_ker_rightHom, MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    rw [(ht (S.rightHom g)).eq]
    group
  obtain ⟨d, hd⟩ := hdmem
  obtain ⟨n, hn⟩ := hLang d⁻¹
  have hn' : S.conjAct t n = n * d⁻¹ := inv_mul_eq_iff_eq_mul.mp hn
  have htg : t * g = S.inl d * g * t := by rw [hd]; group
  have hcomm : t * (S.inl n * g) = (S.inl n * g) * t := by
    calc
      _ = (t * S.inl n * t⁻¹) * (t * g) := by group
      _ = S.inl (S.conjAct t n) * (S.inl d * g * t) := by
        rw [S.inl_conjAct_comm, htg]
      _ = _ := by rw [hn', map_mul, map_inv]; group
  refine ⟨⟨S.inl n * g, Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm⟩, ?_⟩
  change S.rightHom (S.inl n * g) = q
  rw [map_mul, S.rightHom_inl, one_mul, hg]

theorem centralizerProjection_injective
    (hLang : Function.Injective (extensionLangMap S t)) :
    Function.Injective (centralizerProjection S t) := by
  intro a b hab
  have hab' : S.rightHom (a : G) = S.rightHom (b : G) := hab
  have hx : (a : G) * (b : G)⁻¹ ∈ S.inl.range := by
    rw [S.range_inl_eq_ker_rightHom, MonoidHom.mem_ker, map_mul, map_inv, hab', mul_inv_cancel]
  obtain ⟨n, hn⟩ := hx
  have hcomm : t * S.inl n = S.inl n * t := by
    rw [hn]
    exact (Subgroup.mem_centralizer_singleton_iff.mp
      ((Subgroup.centralizer ({t} : Set G)).mul_mem a.property
        ((Subgroup.centralizer ({t} : Set G)).inv_mem b.property))).symm
  have hfix : S.conjAct t n = n := by
    apply S.inl_injective
    rw [S.inl_conjAct_comm, hcomm, mul_inv_cancel_right]
  have hn0 : n = 1 := hLang (by
    rw [extensionLangMap, hfix, inv_mul_cancel, extensionLangMap_one])
  have he : (a : G) * (b : G)⁻¹ = 1 := by rw [← hn, hn0, map_one]
  exact Subtype.ext (mul_inv_eq_one.mp he)

/-- The centralizer provides an actual homomorphic section of the extension. -/
def centralizerSplitting
    (ht : ∀ q : Q, Commute (S.rightHom t) q)
    (hLang : Function.Bijective (extensionLangMap S t)) : S.Splitting := by
  let e : Subgroup.centralizer ({t} : Set G) ≃* Q :=
    MulEquiv.ofBijective (centralizerProjection S t)
      ⟨centralizerProjection_injective S t hLang.1,
        centralizerProjection_surjective S t ht hLang.2⟩
  let f := (Subgroup.centralizer ({t} : Set G)).subtype.comp e.symm.toMonoidHom
  exact { f with rightInverse_rightHom := fun q => e.apply_symm_apply q }

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_WeightChambers
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

def orientedWeight (α : I → W →L[ℝ] ℝ) (σ : I → Bool) (i : I) : W →L[ℝ] ℝ :=
  if σ i then α i else -α i

def closedWeightChamber (α : I → W →L[ℝ] ℝ) (σ : I → Bool) : Set W :=
  linearInequalityCone (orientedWeight α σ)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ChamberBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A compact normalized base of a pointed weight chamber -/

noncomputable section

namespace PolycyclicRecognition

open Set

variable {W I : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [Fintype I]

def chamberFunctional (α : I → W →L[ℝ] ℝ) (σ : I → Bool) : W →L[ℝ] ℝ :=
  ∑ i, orientedWeight α σ i

def chamberBase (α : I → W →L[ℝ] ℝ) (σ : I → Bool) : Set W :=
  {w | w ∈ closedWeightChamber α σ ∧ chamberFunctional α σ w = 1}

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ChamberExtremeDirections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Extreme directions span a full-dimensional weight chamber -/

noncomputable section

namespace PolycyclicRecognition

open Set

variable {W I : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [Fintype I]

def chamberExtremeDirections (α : I → W →L[ℝ] ℝ) (σ : I → Bool) : Set W :=
  {w | w ≠ 0 ∧ IsExtreme ℝ (closedWeightChamber α σ) (nonnegativeRay w)}

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_IntegralAugmentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The augmentation kernel of the integral group ring -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory Representation
open scoped MonoidAlgebra

variable (G : Type) [Group G]

def integralAugmentation : ℤ[G] →ₗ[ℤ] ℤ :=
  (Rep.leftRegularHom (Rep.trivial ℤ G ℤ) 1).hom.toLinearMap

@[simp] theorem integralAugmentation_single (g : G) (r : ℤ) :
    integralAugmentation G (MonoidAlgebra.single g r) = r := by
  exact (Rep.leftRegularHom_hom_single g 1 r).trans (by simp)

theorem integralAugmentation_leftRegular (g : G) (x : ℤ[G]) :
    integralAugmentation G (Representation.leftRegular ℤ G g x) =
      integralAugmentation G x := by
  simpa only [integralAugmentation, Rep.trivial_ρ, Representation.trivial_apply,
    Representation.leftRegular, Representation.IntertwiningMap.toLinearMap_apply] using
    Rep.hom_comm_apply (Rep.leftRegularHom (Rep.trivial ℤ G ℤ) 1) g x

theorem sub_augmentation_mem_coinvariants (x : ℤ[G]) :
    x - MonoidAlgebra.single 1 (integralAugmentation G x) ∈
      Coinvariants.ker (Representation.leftRegular ℤ G) := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy =>
      rw [map_add, MonoidAlgebra.single_add]
      convert (Coinvariants.ker (Representation.leftRegular ℤ G)).add_mem hx hy using 1
      all_goals try with_reducible_and_instances rfl
      abel
  | single g r =>
      rw [integralAugmentation_single]
      simpa using Coinvariants.sub_mem_ker (ρ := Representation.leftRegular ℤ G)
        g (MonoidAlgebra.single 1 r)

theorem integralAugmentation_ker :
    LinearMap.ker (integralAugmentation G) =
      Coinvariants.ker (Representation.leftRegular ℤ G) := by
  apply le_antisymm
  · intro x hx
    have hz : integralAugmentation G x = 0 := hx
    simpa only [hz, MonoidAlgebra.single_zero, sub_zero] using
      sub_augmentation_mem_coinvariants G x
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨g, x⟩, rfl⟩
    change integralAugmentation G (Representation.leftRegular ℤ G g x - x) = 0
    rw [map_sub, integralAugmentation_leftRegular, sub_self]

theorem integralAugmentation_ker_of_cyclic (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    LinearMap.ker (integralAugmentation G) =
      LinearMap.range (Representation.leftRegular ℤ G g - LinearMap.id) :=
  (integralAugmentation_ker G).trans (cyclic_coinvariantsKer_eq_range _ g hg)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_InfiniteCyclicDifference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Injectivity of the difference map for an infinite cyclic group -/

noncomputable section
namespace PolycyclicRecognition

open Representation
open scoped MonoidAlgebra

variable {G : Type} [Group G] [Infinite G]

theorem leftRegular_fixed_generator_eq_zero (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) (x : ℤ[G])
    (hx : Representation.leftRegular ℤ G g x = x) : x = 0 := by
  obtain ⟨a, ha⟩ := x.coeff.support.exists_notMem
  have hcoeff : x.coeff g = 0 :=
    (coeff_of_leftRegular_of_generator g hg x hx a).symm.trans
      (Finsupp.notMem_support_iff.mp ha)
  ext b
  exact (coeff_of_leftRegular_of_generator g hg x hx b).trans hcoeff

theorem leftRegular_difference_injective (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    Function.Injective
      ((Representation.leftRegular ℤ G g - LinearMap.id) : ℤ[G] →ₗ[ℤ] ℤ[G]) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm ?_ bot_le
  intro x hx
  change x = 0
  apply leftRegular_fixed_generator_eq_zero g hg x
  exact sub_eq_zero.mp hx

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_InfiniteCyclicResolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A finite free resolution for an infinite cyclic group -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits ZeroObject
open scoped MonoidAlgebra

-- Use the scalar structure stored in a representation, including for integer scalars.
attribute [local instance 2000] Rep.hV2

variable (G : Type) [CommGroup G]

def cyclicDifference (g : G) : Rep.leftRegular ℤ G ⟶ Rep.leftRegular ℤ G :=
  (Rep.leftRegular ℤ G).applyAsHom g - 𝟙 _

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NormalQuotientCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coset coordinates for induction from a normal subgroup -/

noncomputable section
namespace PolycyclicRecognition

variable {G : Type} [Group G] (N : Subgroup G) [N.Normal]

def normalQuotientRepresentative (c : G ⧸ N) : G :=
  (QuotientGroup.mk'_surjective N c).choose

@[simp] theorem normalQuotientRepresentative_mk (c : G ⧸ N) :
    QuotientGroup.mk' N (normalQuotientRepresentative N c) = c :=
  (QuotientGroup.mk'_surjective N c).choose_spec

@[simp] theorem normalQuotient_mk_subgroup (n : N) :
    QuotientGroup.mk' N (n : G) = 1 :=
  (QuotientGroup.eq_one_iff (n : G)).mpr n.property

def normalQuotientPart (g : G) : N :=
  ⟨g * (normalQuotientRepresentative N (QuotientGroup.mk' N g))⁻¹, by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' N
      (g * (normalQuotientRepresentative N (QuotientGroup.mk' N g))⁻¹) = 1
    rw [map_mul, map_inv, normalQuotientRepresentative_mk, mul_inv_cancel]⟩

@[simp] theorem normalQuotientPart_mul (n : N) (g : G) :
    normalQuotientPart N ((n : G) * g) = n * normalQuotientPart N g := by
  apply Subtype.ext
  change ((n : G) * g) *
      (normalQuotientRepresentative N (QuotientGroup.mk' N ((n : G) * g)))⁻¹ =
    (n : G) * (g * (normalQuotientRepresentative N (QuotientGroup.mk' N g))⁻¹)
  rw [map_mul, normalQuotient_mk_subgroup, one_mul, mul_assoc]

@[simp] theorem normalQuotientPart_representative (c : G ⧸ N) :
    normalQuotientPart N (normalQuotientRepresentative N c) = 1 := by
  apply Subtype.ext
  change normalQuotientRepresentative N c *
    (normalQuotientRepresentative N
      (QuotientGroup.mk' N (normalQuotientRepresentative N c)))⁻¹ = 1
  rw [normalQuotientRepresentative_mk, mul_inv_cancel]

theorem normalQuotientPart_decompose (g : G) :
    (normalQuotientPart N g : G) *
      normalQuotientRepresentative N (QuotientGroup.mk' N g) = g := by
  simp [normalQuotientPart, mul_assoc]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NormalInductionCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Direct-sum coordinates for induction from a normal subgroup

The coordinates give a linear equivalence, used below with integral coefficients. The group
action remains the induced action; no invariance of the chosen section is
asserted.
-/

noncomputable section
namespace PolycyclicRecognition

open Representation
open scoped MonoidAlgebra TensorProduct
attribute [local instance 2000] Rep.hV2

variable (k : Type) [CommRing k] {G : Type} [Group G]
  (N : Subgroup G) [N.Normal] (A : Rep k N)

def inductionTensorCoordinates :
    k[G] ⊗[k] A →ₗ[k] ((G ⧸ N) →₀ A) :=
  TensorProduct.lift <|
    (Finsupp.lift _ _ _ fun g =>
      (Finsupp.lsingle (QuotientGroup.mk' N g)).comp (A.ρ (normalQuotientPart N g)⁻¹))
      ∘ₗ (MonoidAlgebra.coeffLinearEquiv k).toLinearMap

@[simp] theorem inductionTensorCoordinates_single (g : G) (a : A) :
    inductionTensorCoordinates k N A (MonoidAlgebra.single g 1 ⊗ₜ[k] a) =
      Finsupp.single (QuotientGroup.mk' N g) (A.ρ (normalQuotientPart N g)⁻¹ a) := by
  simp [inductionTensorCoordinates]

theorem inductionTensorCoordinates_invariant (n : N) :
    inductionTensorCoordinates k N A ∘ₗ
      (Representation.tprod ((Representation.leftRegular k G).comp N.subtype) A.ρ) n =
      inductionTensorCoordinates k N A := by
  apply TensorProduct.ext
  apply MonoidAlgebra.lhom_ext'
  intro g
  apply LinearMap.ext_ring
  apply LinearMap.ext
  intro a
  simp [map_mul, mul_inv_rev, Module.End.mul_apply]
  congr 1
  change QuotientGroup.mk' N ((n : G) * g) = QuotientGroup.mk' N g
  rw [map_mul, normalQuotient_mk_subgroup, one_mul]

def inductionCoordinates : Rep.ind N.subtype A →ₗ[k] ((G ⧸ N) →₀ A) :=
  Coinvariants.lift _ (inductionTensorCoordinates k N A)
    (inductionTensorCoordinates_invariant k N A)

@[simp] theorem inductionCoordinates_mk (g : G) (a : A) :
    inductionCoordinates k N A (IndV.mk N.subtype A.ρ g a) =
      Finsupp.single (QuotientGroup.mk' N g) (A.ρ (normalQuotientPart N g)⁻¹ a) := by
  exact inductionTensorCoordinates_single k N A g a

def inductionCoordinatesInv : ((G ⧸ N) →₀ A) →ₗ[k] Rep.ind N.subtype A :=
  Finsupp.lsum k fun c => IndV.mk N.subtype A.ρ (normalQuotientRepresentative N c)

@[simp] theorem inductionCoordinatesInv_single (c : G ⧸ N) (a : A) :
    inductionCoordinatesInv k N A (Finsupp.single c a) =
      IndV.mk N.subtype A.ρ (normalQuotientRepresentative N c) a := by
  simp [inductionCoordinatesInv]

theorem inductionCoordinates_right_inv :
    (inductionCoordinates k N A).comp (inductionCoordinatesInv k N A) = LinearMap.id := by
  apply Finsupp.lhom_ext'
  intro c
  apply LinearMap.ext
  intro a
  change inductionCoordinates k N A (inductionCoordinatesInv k N A (Finsupp.single c a)) = _
  rw [inductionCoordinatesInv_single, inductionCoordinates_mk,
    normalQuotientRepresentative_mk, normalQuotientPart_representative]
  simp

theorem inductionCoordinates_left_inv :
    (inductionCoordinatesInv k N A).comp (inductionCoordinates k N A) = LinearMap.id := by
  apply IndV.hom_ext
  intro g
  apply LinearMap.ext
  intro a
  change inductionCoordinatesInv k N A
    (inductionCoordinates k N A (IndV.mk N.subtype A.ρ g a)) = IndV.mk N.subtype A.ρ g a
  rw [inductionCoordinates_mk, inductionCoordinatesInv_single]
  change Coinvariants.mk (Representation.tprod ((Representation.leftRegular k G).comp N.subtype) A.ρ)
    (MonoidAlgebra.single (normalQuotientRepresentative N (QuotientGroup.mk' N g)) (1 : k) ⊗ₜ[k]
      A.ρ (normalQuotientPart N g)⁻¹ a) =
    Coinvariants.mk (Representation.tprod ((Representation.leftRegular k G).comp N.subtype) A.ρ)
      (MonoidAlgebra.single g (1 : k) ⊗ₜ[k] a)
  rw [Coinvariants.mk_tmul_inv]
  simp only [MonoidHom.comp_apply, Representation.leftRegular, Representation.ofMulAction_single,
    Subgroup.subtype_apply, smul_eq_mul, normalQuotientPart_decompose]

def normalInductionEquiv : Rep.ind N.subtype A ≃ₗ[k] ((G ⧸ N) →₀ A) :=
  LinearEquiv.ofLinearMap (inductionCoordinates k N A) (inductionCoordinatesInv k N A)
    (inductionCoordinates_right_inv k N A) (inductionCoordinates_left_inv k N A)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_InductionTrivial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Inducing the trivial module gives the quotient permutation module -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory Representation
open scoped MonoidAlgebra TensorProduct
attribute [local instance 2000] Rep.hV2

variable (k : Type) [CommRing k] {G : Type} [Group G]
  (N : Subgroup G) [N.Normal]

def inductionTrivialLinearEquiv :
    Rep.ind N.subtype (Rep.trivial k N k) ≃ₗ[k] k[G ⧸ N] :=
  (normalInductionEquiv k N (Rep.trivial k N k)).trans
    ((Finsupp.domLCongr (Equiv.inv (G ⧸ N))).trans (MonoidAlgebra.coeffLinearEquiv k).symm)

@[simp] theorem inductionTrivialLinearEquiv_mk (g : G) (r : k) :
    inductionTrivialLinearEquiv k N
      (IndV.mk N.subtype (Rep.trivial k N k).ρ g r) =
        MonoidAlgebra.single (QuotientGroup.mk' N g)⁻¹ r := by
  change (MonoidAlgebra.coeffLinearEquiv k).symm
    (Finsupp.domLCongr (Equiv.inv (G ⧸ N))
      (inductionCoordinates k N (Rep.trivial k N k) (IndV.mk N.subtype _ g r))) = _
  rw [inductionCoordinates_mk, Rep.trivial_ρ_apply, Finsupp.domLCongr_single]
  rfl

def inductionTrivialEquiv :
    (Rep.ind N.subtype (Rep.trivial k N k)).ρ.Equiv
      (Rep.res (QuotientGroup.mk' N) (Rep.leftRegular k (G ⧸ N))).ρ :=
  Representation.Equiv.mk (inductionTrivialLinearEquiv k N) fun h => by
    apply IndV.hom_ext
    intro g
    apply LinearMap.ext
    intro r
    change inductionTrivialLinearEquiv k N
        (Representation.ind N.subtype (Rep.trivial k N k).ρ h (IndV.mk N.subtype _ g r)) =
      Representation.leftRegular k (G ⧸ N) (QuotientGroup.mk' N h)
        (inductionTrivialLinearEquiv k N (IndV.mk N.subtype _ g r))
    rw [Representation.ind_mk, inductionTrivialLinearEquiv_mk, inductionTrivialLinearEquiv_mk]
    simp [map_mul, map_inv, mul_inv_rev]

def inductionTrivialIso :
    Rep.ind N.subtype (Rep.trivial k N k) ≅
      Rep.res (QuotientGroup.mk' N) (Rep.leftRegular k (G ⧸ N)) :=
  Rep.mkIso (inductionTrivialEquiv k N)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NormalInductionExact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact induction along the normal subgroup in a cyclic extension -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits Representation
open scoped MonoidAlgebra TensorProduct
attribute [local instance 2000] Rep.hV2

variable (k : Type) [CommRing k] {G : Type} [Group G]
  (N : Subgroup G) [N.Normal]

omit [N.Normal] in
@[simp] theorem normalInductionMap_mk {A B : Rep k N} (f : A ⟶ B) (g : G) (a : A) :
    (Rep.indMap N.subtype f).hom (IndV.mk N.subtype A.ρ g a) =
      IndV.mk N.subtype B.ρ g (f.hom a) := by
  simp [Rep.indMap, IndV.mk]

theorem inductionCoordinates_naturality {A B : Rep k N} (f : A ⟶ B) :
    (inductionCoordinates k N B).comp (Rep.indMap N.subtype f).hom.toLinearMap =
      (Finsupp.mapRange.linearMap f.hom.toLinearMap).comp (inductionCoordinates k N A) := by
  apply IndV.hom_ext
  intro g
  apply LinearMap.ext
  intro a
  change inductionCoordinates k N B ((Rep.indMap N.subtype f).hom
      (IndV.mk N.subtype A.ρ g a)) = _
  rw [normalInductionMap_mk k N f g a, inductionCoordinates_mk k N B g (f.hom a)]
  change _ = Finsupp.mapRange.linearMap f.hom.toLinearMap
    (inductionCoordinates k N A (IndV.mk N.subtype A.ρ g a))
  rw [inductionCoordinates_mk k N A g a]
  simp only [Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single]
  congr 1
  exact (Rep.hom_comm_apply f (normalQuotientPart N g)⁻¹ a).symm

theorem normalInductionMap_injective {A B : Rep k N} (f : A ⟶ B)
    (hf : Function.Injective f.hom) : Function.Injective (Rep.indMap N.subtype f).hom := by
  intro x y hxy
  apply (normalInductionEquiv k N A).injective
  have h := congrArg (inductionCoordinates k N B) hxy
  have hx := LinearMap.congr_fun (inductionCoordinates_naturality k N f) x
  have hy := LinearMap.congr_fun (inductionCoordinates_naturality k N f) y
  simp only [LinearMap.comp_apply, IntertwiningMap.toLinearMap_apply] at hx hy
  change inductionCoordinates k N B ((Rep.indMap N.subtype f).hom x) =
    inductionCoordinates k N B ((Rep.indMap N.subtype f).hom y) at h
  rw [hx, hy] at h
  exact Finsupp.mapRange_injective _ (map_zero f.hom) hf h

instance normalInduction_preservesMonomorphisms :
    (Rep.indFunctor k N.subtype).PreservesMonomorphisms where
  preserves f hf := by
    rw [Rep.mono_iff_injective]
    exact normalInductionMap_injective k N f ((Rep.mono_iff_injective f).mp hf)

instance normalInduction_preservesHomology :
    (Rep.indFunctor k N.subtype).PreservesHomology :=
  Functor.preservesHomology_of_preservesMonos_and_cokernels _

instance normalInduction_preservesProjectives :
    (Rep.indFunctor k N.subtype).PreservesProjectiveObjects :=
  Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms
    (Rep.indResAdjunction k N.subtype)

instance normalInduction_additive : (Rep.indFunctor k N.subtype).Additive where
  map_add {A B} f h := by
    apply Rep.hom_ext
    apply IntertwiningMap.ext
    apply IndV.hom_ext
    intro g
    apply LinearMap.ext
    intro a
    simp [Rep.indMap, IndV.mk, Rep.add_hom]

def normalInducedResolution {A : Rep k N} (P : ProjectiveResolution A) :
    ProjectiveResolution (Rep.ind N.subtype A) :=
  (Rep.indFunctor k N.subtype).mapProjectiveResolution P

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RestrictionEquivalence
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives
attribute [-simp] _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Restriction along a group isomorphism -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory Representation
attribute [local instance 2000] Rep.hV2

variable (k : Type) [CommRing k] {G J : Type} [Group G] [Group J]

def restrictionRoundtripIso (e : G ≃* J) (A : Rep k G) :
    Rep.res e.toMonoidHom (Rep.res e.symm.toMonoidHom A) ≅ A :=
  Rep.mkIso (Representation.Equiv.mk (LinearEquiv.refl k A) fun g => by
    ext a
    simp)

def restrictionEquivalence (e : G ≃* J) : Rep k J ≌ Rep k G where
  functor := Rep.resFunctor e.toMonoidHom
  inverse := Rep.resFunctor e.symm.toMonoidHom
  unitIso := NatIso.ofComponents (fun A => (restrictionRoundtripIso k e.symm A).symm)
    (by intro A B f; ext a; rfl)
  counitIso := NatIso.ofComponents (fun A => restrictionRoundtripIso k e A)
    (by intro A B f; ext a; rfl)
  functor_unitIso_comp A := by ext a; rfl

end PolycyclicRecognition

end

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

variable {P Q : ChainComplex (Rep k G) ℕ} (φ : P ⟶ Q)

abbrev repCofiber := homotopyCofiber φ
abbrev repCofiberFst (i : ℕ) : (repCofiber φ).X (i + 1) ⟶ P.X i :=
  homotopyCofiber.fstX φ (i + 1) i (by rfl)
abbrev repCofiberSnd (i : ℕ) : (repCofiber φ).X i ⟶ Q.X i :=
  homotopyCofiber.sndX φ i
abbrev repCofiberInl (i : ℕ) : P.X i ⟶ (repCofiber φ).X (i + 1) :=
  homotopyCofiber.inlX φ i (i + 1) (by rfl)
abbrev repCofiberInr (i : ℕ) : Q.X i ⟶ (repCofiber φ).X i :=
  homotopyCofiber.inrX φ i

theorem repCofiber_zero_decompose (x : (repCofiber φ).X 0) :
    (repCofiberInr φ 0).hom ((repCofiberSnd φ 0).hom x) = x :=
  congrArg (fun f => f.hom x) (homotopyCofiber.sndX_inrX φ 0 (by simp))

theorem repCofiber_ext_zero {x y : (repCofiber φ).X 0}
    (h : (repCofiberSnd φ 0).hom x = (repCofiberSnd φ 0).hom y) : x = y := by
  rw [← repCofiber_zero_decompose φ x, ← repCofiber_zero_decompose φ y, h]

theorem repCofiber_decompose (i : ℕ) (x : (repCofiber φ).X (i + 1)) :
    (repCofiberInl φ i).hom ((repCofiberFst φ i).hom x) +
      (repCofiberInr φ (i + 1)).hom ((repCofiberSnd φ (i + 1)).hom x) = x := by
  have h : repCofiberFst φ i ≫ repCofiberInl φ i +
      repCofiberSnd φ (i + 1) ≫ repCofiberInr φ (i + 1) = 𝟙 _ := by
    apply homotopyCofiber.ext_to_X φ (i + 1) i (by rfl)
    · simp only [Preadditive.add_comp, Category.assoc, Category.id_comp]
      rw [homotopyCofiber.inlX_fstX φ i (i + 1) (by rfl),
        homotopyCofiber.inrX_fstX φ (i + 1) i (by rfl)]
      simp
    · simp only [Preadditive.add_comp, Category.assoc, Category.id_comp]
      rw [homotopyCofiber.inlX_sndX φ i (i + 1) (by rfl),
        homotopyCofiber.inrX_sndX φ (i + 1)]
      simp
  exact congrArg (fun f => f.hom x) h

theorem repCofiber_snd_d (i : ℕ) (x : (repCofiber φ).X (i + 1)) :
    (repCofiberSnd φ i).hom (((repCofiber φ).d (i + 1) i).hom x) =
      (φ.f i).hom ((repCofiberFst φ i).hom x) +
        (Q.d (i + 1) i).hom ((repCofiberSnd φ (i + 1)).hom x) := by
  exact congrArg (fun f => f.hom x) (homotopyCofiber.d_sndX φ (i + 1) i (by rfl))

theorem repCofiber_fst_d (i : ℕ) (x : (repCofiber φ).X (i + 2)) :
    (repCofiberFst φ i).hom (((repCofiber φ).d (i + 2) (i + 1)).hom x) =
      -(P.d (i + 1) i).hom ((repCofiberFst φ (i + 1)).hom x) := by
  exact congrArg (fun f => f.hom x)
    (homotopyCofiber.d_fstX φ (i + 2) (i + 1) i (by rfl) (by rfl))

theorem repCofiber_fst_inl (i : ℕ) (x : P.X i) :
    (repCofiberFst φ i).hom ((repCofiberInl φ i).hom x) = x :=
  congrArg (fun f => f.hom x) (homotopyCofiber.inlX_fstX φ i (i + 1) (by rfl))

theorem repCofiber_snd_inl (i : ℕ) (x : P.X i) :
    (repCofiberSnd φ (i + 1)).hom ((repCofiberInl φ i).hom x) = 0 :=
  congrArg (fun f => f.hom x) (homotopyCofiber.inlX_sndX φ i (i + 1) (by rfl))

theorem repCofiber_fst_inr (i : ℕ) (x : Q.X (i + 1)) :
    (repCofiberFst φ i).hom ((repCofiberInr φ (i + 1)).hom x) = 0 :=
  congrArg (fun f => f.hom x) (homotopyCofiber.inrX_fstX φ (i + 1) i (by rfl))

theorem repCofiber_snd_inr (i : ℕ) (x : Q.X i) :
    (repCofiberSnd φ i).hom ((repCofiberInr φ i).hom x) = x :=
  congrArg (fun f => f.hom x) (homotopyCofiber.inrX_sndX φ i)

theorem repCofiber_ext (i : ℕ) {x y : (repCofiber φ).X (i + 1)}
    (h₁ : (repCofiberFst φ i).hom x = (repCofiberFst φ i).hom y)
    (h₂ : (repCofiberSnd φ (i + 1)).hom x = (repCofiberSnd φ (i + 1)).hom y) : x = y := by
  rw [← repCofiber_decompose φ i x, ← repCofiber_decompose φ i y, h₁, h₂]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FiniteCofiber
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Projectivity and finiteness of the cyclic-extension mapping cone -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2

variable {G : Type} [Group G]

variable {A B : Rep ℤ G} (P : ProjectiveResolution A) (Q : ProjectiveResolution B)
  (φ : P.complex ⟶ Q.complex)

instance repCofiber_projective (i : ℕ) : Projective ((repCofiber φ).X i) := by
  cases i with
  | zero =>
      exact Projective.of_iso (homotopyCofiber.XIso φ 0 (by simp)).symm inferInstance
  | succ i =>
      exact Projective.of_iso
        (homotopyCofiber.XIsoBiprod φ (i + 1) i (by rfl)).symm inferInstance

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_CokernelResolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A finite projective resolution for the cokernel in the cyclic extension -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance 2000] Rep.hV2

variable {G : Type} [Group G] (S : ShortComplex (Rep ℤ G))
  (P : ProjectiveResolution S.X₁) (Q : ProjectiveResolution S.X₂)

abbrev cokernelResolutionMap := ProjectiveResolution.lift S.f P Q

def cokernelResolutionAugmentation : repCofiber (cokernelResolutionMap S P Q) ⟶
    (ChainComplex.single₀ (Rep ℤ G)).obj S.X₃ :=
  homotopyCofiber.desc (cokernelResolutionMap S P Q)
    (Q.π ≫ (ChainComplex.single₀ (Rep ℤ G)).map S.g) (Homotopy.ofEq (by
      rw [← Category.assoc, ProjectiveResolution.lift_commutes, Category.assoc,
        ← Functor.map_comp, S.zero, Functor.map_zero, comp_zero]))

theorem cokernelResolutionAugmentation_apply (x : (repCofiber
    (cokernelResolutionMap S P Q)).X 0) :
    ((cokernelResolutionAugmentation S P Q).f 0).hom x =
      S.g.hom ((Q.π.f 0).hom ((repCofiberSnd (cokernelResolutionMap S P Q) 0).hom x)) := by
  unfold cokernelResolutionAugmentation
  rw [homotopyCofiber.desc_f' _ _ _ 0 (by simp)]
  rfl

theorem cokernelResolutionAugmentation_surjective (hS : S.ShortExact) :
    Function.Surjective ((cokernelResolutionAugmentation S P Q).f 0).hom := by
  let := hS.epi_g
  intro c
  obtain ⟨b, rfl⟩ := ((Rep.epi_iff_surjective S.g).mp inferInstance) c
  obtain ⟨y, rfl⟩ := ((Rep.epi_iff_surjective (Q.π.f 0)).mp inferInstance) b
  refine ⟨(repCofiberInr (cokernelResolutionMap S P Q) 0).hom y, ?_⟩
  rw [cokernelResolutionAugmentation_apply, repCofiber_snd_inr]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_CyclicExtensionFiniteness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite projective resolutions through infinite cyclic extensions -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2

variable {G : Type} [Group G]

def projectiveResolutionAlongIso {A B : Rep ℤ G} (P : ProjectiveResolution A)
    (e : A ≅ B) : ProjectiveResolution B where
  complex := P.complex
  π := P.π ≫ (ChainComplex.single₀ (Rep ℤ G)).map e.hom

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_TwistedBilateralDifference
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives
attribute [-simp] _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing the coefficient twist from a bilateral shift -/

noncomputable section
namespace PolycyclicRecognition

open Representation
variable (k M : Type*) [CommRing k] [AddCommGroup M] [Module k M]

def bilateralPowerMap (e : M ≃ₗ[k] M) : (ℤ →₀ M) →ₗ[k] (ℤ →₀ M) :=
  Finsupp.lsum k fun i => (Finsupp.lsingle i).comp (e ^ i).toLinearMap

@[simp] theorem bilateralPowerMap_single (e : M ≃ₗ[k] M) (i : ℤ) (m : M) :
    bilateralPowerMap k M e (Finsupp.single i m) = Finsupp.single i ((e ^ i) m) := by
  simp [bilateralPowerMap]

theorem bilateralPowerMap_inv_comp (e : M ≃ₗ[k] M) :
    (bilateralPowerMap k M e⁻¹).comp (bilateralPowerMap k M e) = LinearMap.id := by
  apply Finsupp.lhom_ext'
  intro i
  apply LinearMap.ext
  intro m
  change bilateralPowerMap k M e⁻¹ (bilateralPowerMap k M e (Finsupp.single i m)) = _
  simp only [bilateralPowerMap_single]
  rw [← LinearEquiv.mul_apply, inv_zpow, inv_mul_cancel]
  rfl

def bilateralGauge (e : M ≃ₗ[k] M) : (ℤ →₀ M) ≃ₗ[k] (ℤ →₀ M) :=
  LinearEquiv.ofLinearMap (bilateralPowerMap k M e⁻¹) (bilateralPowerMap k M e)
    (bilateralPowerMap_inv_comp k M e)
    (by simpa only [inv_inv] using bilateralPowerMap_inv_comp k M e⁻¹)

@[simp] theorem bilateralGauge_single (e : M ≃ₗ[k] M) (i : ℤ) (m : M) :
    bilateralGauge k M e (Finsupp.single i m) = Finsupp.single i ((e ^ (-i)) m) := by
  change bilateralPowerMap k M e⁻¹ (Finsupp.single i m) = _
  rw [bilateralPowerMap_single, inv_zpow, zpow_neg]

def twistedBilateralShift (e : M ≃ₗ[k] M) : (ℤ →₀ M) →ₗ[k] (ℤ →₀ M) :=
  (Finsupp.mapRange.linearMap e.toLinearMap).comp
    (bilateralTranslation k M (Multiplicative.ofAdd 1))

@[simp] theorem twistedBilateralShift_single (e : M ≃ₗ[k] M) (i : ℤ) (m : M) :
    twistedBilateralShift k M e (Finsupp.single i m) = Finsupp.single (i + 1) (e m) := by
  simp [twistedBilateralShift, add_comm]

theorem bilateralGauge_shift (e : M ≃ₗ[k] M) (f : ℤ →₀ M) :
    bilateralGauge k M e (twistedBilateralShift k M e f) =
      bilateralTranslation k M (Multiplicative.ofAdd 1) (bilateralGauge k M e f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [hf, hg]
  | single i m =>
      rw [twistedBilateralShift_single, bilateralGauge_single, bilateralGauge_single,
        bilateralTranslation_single]
      have he : (e ^ (-(i + 1))) (e m) = (e ^ (-i)) m := by
        rw [← LinearEquiv.mul_apply, ← zpow_add_one]
        congr 2
        omega
      simpa only [toAdd_ofAdd, add_comm] using congrArg (Finsupp.single (i + 1)) he

def twistedBilateralDifference (e : M ≃ₗ[k] M) : (ℤ →₀ M) →ₗ[k] (ℤ →₀ M) :=
  twistedBilateralShift k M e - LinearMap.id

theorem bilateralGauge_difference (e : M ≃ₗ[k] M) (f : ℤ →₀ M) :
    bilateralGauge k M e (twistedBilateralDifference k M e f) =
      bilateralDifference k M (bilateralGauge k M e f) := by
  change bilateralGauge k M e (twistedBilateralShift k M e f - f) = _
  rw [map_sub, bilateralGauge_shift]
  rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_InductionSemilinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Lifting a semilinear map to the induced representation

Conjugating the normal subgroup by a chosen lift of the cyclic generator
produces the translation map used in the extension resolution.
-/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory Representation
open scoped MonoidAlgebra TensorProduct
attribute [local instance 2000] Rep.hV2

variable (k : Type) [CommRing k] {G : Type} [Group G]
  (N : Subgroup G) [N.Normal]

omit [N.Normal] in
@[simp] theorem induction_mk_left_inv (B : Rep k N) (n : N) (g : G) (a : B) :
    IndV.mk N.subtype B.ρ ((n : G)⁻¹ * g) a = IndV.mk N.subtype B.ρ g (B.ρ n a) := by
  simpa using Coinvariants.mk_inv_tmul
    (ρ := (Representation.leftRegular k G).comp N.subtype) (τ := B.ρ)
    (MonoidAlgebra.single g 1) a n

def inducedSemilinearUnit (t : G) (A B : Rep k N)
    (b : A ⟶ Rep.res (MulAut.conjNormal (H := N) t⁻¹).toMonoidHom B) :
    A ⟶ Rep.res N.subtype (Rep.ind N.subtype B) :=
  Rep.ofHom ⟨(IndV.mk N.subtype B.ρ t⁻¹).comp b.hom.toLinearMap, fun n => by
    ext a
    change IndV.mk N.subtype B.ρ t⁻¹ (b.hom (A.ρ n a)) =
      Representation.ind N.subtype B.ρ (n : G)
        (IndV.mk N.subtype B.ρ t⁻¹ (b.hom a))
    rw [Rep.hom_comm_apply b, Representation.ind_mk]
    change IndV.mk N.subtype B.ρ t⁻¹
        (B.ρ (MulAut.conjNormal (H := N) t⁻¹ n) (b.hom a)) = _
    rw [← induction_mk_left_inv]
    congr 2
    simp [mul_inv_rev, mul_assoc]⟩

def inducedSemilinearMap (t : G) (A B : Rep k N)
    (b : A ⟶ Rep.res (MulAut.conjNormal (H := N) t⁻¹).toMonoidHom B) :
    Rep.ind N.subtype A ⟶ Rep.ind N.subtype B :=
  (Rep.indResHomEquiv N.subtype A (Rep.ind N.subtype B)).symm
    (inducedSemilinearUnit k N t A B b)

@[simp] theorem inducedSemilinearMap_mk (t : G) (A B : Rep k N)
    (b : A ⟶ Rep.res (MulAut.conjNormal (H := N) t⁻¹).toMonoidHom B)
    (g : G) (a : A) :
    (inducedSemilinearMap k N t A B b).hom (IndV.mk N.subtype A.ρ g a) =
      IndV.mk N.subtype B.ρ (t⁻¹ * g) (b.hom a) := by
  simp [inducedSemilinearMap, Rep.indResHomEquiv, inducedSemilinearUnit]
  rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_InducedTranslation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The chain-level translation associated to a lift of a quotient generator -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits Representation
attribute [local instance 2000] Rep.hV2

variable (k : Type) [CommRing k] {G : Type} [Group G]
  (N : Subgroup G) [N.Normal]

theorem inductionMap_comp_semilinear (t : G) {A B C : Rep k N} (u : A ⟶ B)
    (b : B ⟶ Rep.res (MulAut.conjNormal (H := N) t⁻¹).toMonoidHom C) :
    Rep.indMap N.subtype u ≫ inducedSemilinearMap k N t B C b =
      inducedSemilinearMap k N t A C (u ≫ b) := by
  apply Rep.hom_ext
  apply IntertwiningMap.ext
  apply IndV.hom_ext
  intro g
  apply LinearMap.ext
  intro a
  change (inducedSemilinearMap k N t B C b).hom
      ((Rep.indMap N.subtype u).hom (IndV.mk N.subtype A.ρ g a)) =
    (inducedSemilinearMap k N t A C (u ≫ b)).hom (IndV.mk N.subtype A.ρ g a)
  rw [normalInductionMap_mk, inducedSemilinearMap_mk, inducedSemilinearMap_mk]
  rfl

theorem semilinear_comp_inductionMap (t : G) {A B C : Rep k N}
    (b : A ⟶ Rep.res (MulAut.conjNormal (H := N) t⁻¹).toMonoidHom B) (u : B ⟶ C) :
    inducedSemilinearMap k N t A B b ≫ Rep.indMap N.subtype u =
      inducedSemilinearMap k N t A C
        (b ≫ Rep.resMap (MulAut.conjNormal (H := N) t⁻¹).toMonoidHom u) := by
  apply Rep.hom_ext
  apply IntertwiningMap.ext
  apply IndV.hom_ext
  intro g
  apply LinearMap.ext
  intro a
  change (Rep.indMap N.subtype u).hom
      ((inducedSemilinearMap k N t A B b).hom (IndV.mk N.subtype A.ρ g a)) =
    (inducedSemilinearMap k N t A C
      (b ≫ Rep.resMap (MulAut.conjNormal (H := N) t⁻¹).toMonoidHom u)).hom
        (IndV.mk N.subtype A.ρ g a)
  rw [inducedSemilinearMap_mk, normalInductionMap_mk, inducedSemilinearMap_mk]
  rfl

def conjugatedResolution (t : G) (P : ProjectiveResolution (Rep.trivial k N k)) :
    ProjectiveResolution (Rep.trivial k N k) := by
  let e := MulAut.conjNormal (H := N) t⁻¹
  let F : Rep k N ⥤ Rep k N := Rep.resFunctor e.toMonoidHom
  let : F.IsEquivalence := (restrictionEquivalence k e).isEquivalence_functor
  exact F.mapProjectiveResolution P

def conjugationResolutionLift (t : G) (P : ProjectiveResolution (Rep.trivial k N k)) :
    P.complex ⟶ (conjugatedResolution k N t P).complex :=
  ProjectiveResolution.lift (𝟙 _) P (conjugatedResolution k N t P)

def inducedTranslation (t : G) (P : ProjectiveResolution (Rep.trivial k N k)) :
    (normalInducedResolution k N P).complex ⟶ (normalInducedResolution k N P).complex where
  f i := inducedSemilinearMap k N t (P.complex.X i) (P.complex.X i)
    ((conjugationResolutionLift k N t P).f i)
  comm' i j _ := by
    change inducedSemilinearMap k N t _ _ ((conjugationResolutionLift k N t P).f i) ≫
        Rep.indMap N.subtype (P.complex.d i j) =
      Rep.indMap N.subtype (P.complex.d i j) ≫
        inducedSemilinearMap k N t _ _ ((conjugationResolutionLift k N t P).f j)
    erw [inductionMap_comp_semilinear, semilinear_comp_inductionMap]
    congr 1
    exact (conjugationResolutionLift k N t P).comm i j

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_RepCochainMaps
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives
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

def repCochainPostcomp (P : ChainComplex (Rep k G) ℕ) {A B : Rep k G} (u : A ⟶ B) :
    P.linearYonedaObj k A ⟶ P.linearYonedaObj k B where
  f i := ModuleCat.ofHom (Linear.rightComp k (P.X i) u)
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    change P.d j i ≫ (f ≫ u) = (P.d j i ≫ f) ≫ u
    exact (Category.assoc _ _ _).symm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_ConjugationCochains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The automorphism of kernel cohomology induced by conjugation -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory Representation
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2
attribute [local instance 2000] Rep.instLinear
attribute [local instance 2100] Linear.homModule

variable (k : Type) [CommRing k] {H : Type} [Group H]

def restrictionHomEquiv (e : H ≃* H) (A B : Rep k H) :
    (A ⟶ B) ≃ₗ[k] (Rep.res e.toMonoidHom A ⟶ Rep.res e.toMonoidHom B) where
  toFun := Rep.resMap e.toMonoidHom
  invFun := Rep.liftHomOfSurj e.toMonoidHom e.surjective
  left_inv f := by apply Rep.hom_ext; apply IntertwiningMap.ext; rfl
  right_inv f := by apply Rep.hom_ext; apply IntertwiningMap.ext; rfl
  map_add' f g := by apply Rep.hom_ext; apply IntertwiningMap.ext; rfl
  map_smul' r f := by apply Rep.hom_ext; apply IntertwiningMap.ext; rfl

def restrictionCochainsIso (e : H ≃* H) (P : ChainComplex (Rep k H) ℕ) (A : Rep k H) :
    P.linearYonedaObj k A ≅
      ChainComplex.linearYonedaObj (((Rep.resFunctor e.toMonoidHom).mapHomologicalComplex _).obj P) k
        (Rep.res e.toMonoidHom A) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => (restrictionHomEquiv k e (P.X i) A).toModuleIso) (by
      intro i j _
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      rfl)

def regularRestrictionIso (e : H ≃* H) :
    Rep.res e.toMonoidHom (Rep.leftRegular k H) ≅ Rep.leftRegular k H :=
  Rep.mkIso (Representation.Equiv.mk (MonoidAlgebra.domCongr k k e.symm).toLinearEquiv
    (fun h => by
      apply MonoidAlgebra.lhom_ext'
      intro a
      apply LinearMap.ext_ring
      simp [map_mul]))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_IntegralFinsuppFunctor
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact direct sums of integral modules -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits

def moduleFinsuppFunctor (k : Type) [Ring k] (α : Type) : ModuleCat k ⥤ ModuleCat k where
  obj M := ModuleCat.of k (α →₀ M)
  map f := ModuleCat.ofHom (Finsupp.mapRange.linearMap f.hom)
  map_id _ := by ext x i; rfl
  map_comp _ _ := by ext x i; rfl

instance instAdditiveModuleCatModuleFinsuppFunctor (k : Type) [Ring k] (α : Type) : (moduleFinsuppFunctor k α).Additive where
  map_add {X Y} f g := by
    dsimp only [moduleFinsuppFunctor]
    ext x i
    rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_BilateralCochainShift
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Translation on direct sums of cochain complexes and their cohomology -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory

variable (k : Type) [CommRing k]

def bilateralFunctorTranslation (z : Multiplicative ℤ) :
    moduleFinsuppFunctor k ℤ ⟶ moduleFinsuppFunctor k ℤ where
  app M := ModuleCat.ofHom (bilateralTranslation k M z)
  naturality {M N} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Finsupp.ext
    intro i
    rfl

variable (C : CochainComplex (ModuleCat k) ℕ)

def bilateralCochainTranslation (z : Multiplicative ℤ) :=
  ((bilateralFunctorTranslation k z).mapHomologicalComplex (ComplexShape.up ℕ)).app C

def bilateralCochainTwist (f : C ⟶ C) :=
  bilateralCochainTranslation k C (Multiplicative.ofAdd 1) ≫
    ((moduleFinsuppFunctor k ℤ).mapHomologicalComplex _).map f

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_InducedTranslationAugmentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The induced translation lifts right translation on the quotient module -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory Representation
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2

variable (k : Type) [CommRing k] {G : Type} [Group G]
  (N : Subgroup G) [N.Normal]

def inducedTrivialTranslation (t : G) :
    Rep.ind N.subtype (Rep.trivial k N k) ⟶ Rep.ind N.subtype (Rep.trivial k N k) :=
  inducedSemilinearMap k N t _ _ (𝟙 _)

def quotientRightTranslation (t : G) :
    Rep.res (QuotientGroup.mk' N) (Rep.leftRegular k (G ⧸ N)) ⟶
      Rep.res (QuotientGroup.mk' N) (Rep.leftRegular k (G ⧸ N)) :=
  Rep.ofHom ⟨MonoidAlgebra.mapDomainLinearMap k k (fun q => q * QuotientGroup.mk' N t),
    fun g => by
      apply MonoidAlgebra.lhom_ext'
      intro c
      apply LinearMap.ext_ring
      simp [mul_assoc]⟩

@[simp] theorem inducedTrivialTranslation_mk (t g : G) (a : k) :
    (inducedTrivialTranslation k N t).hom
      (IndV.mk N.subtype (Rep.trivial k N k).ρ g a) =
        IndV.mk N.subtype (Rep.trivial k N k).ρ (t⁻¹ * g) a := by
  exact inducedSemilinearMap_mk k N t (Rep.trivial k N k) (Rep.trivial k N k)
    (𝟙 (Rep.trivial k N k)) g a

@[simp] theorem quotientRightTranslation_single (t : G) (c : G ⧸ N) (a : k) :
    (quotientRightTranslation k N t).hom (MonoidAlgebra.single c a) =
      MonoidAlgebra.single (c * QuotientGroup.mk' N t) a := by
  simp [quotientRightTranslation]

theorem inducedTrivialTranslation_quotient (t : G) :
    inducedTrivialTranslation k N t ≫ (inductionTrivialIso k N).hom =
      (inductionTrivialIso k N).hom ≫ quotientRightTranslation k N t := by
  apply Rep.hom_ext
  apply IntertwiningMap.ext
  apply IndV.hom_ext
  intro g
  apply LinearMap.ext
  intro a
  change inductionTrivialLinearEquiv k N
      ((inducedTrivialTranslation k N t).hom (IndV.mk N.subtype (Rep.trivial k N k).ρ g a)) =
    (quotientRightTranslation k N t).hom
      (inductionTrivialLinearEquiv k N (IndV.mk N.subtype (Rep.trivial k N k).ρ g a))
  rw [inducedTrivialTranslation_mk, inductionTrivialLinearEquiv_mk,
    inductionTrivialLinearEquiv_mk, quotientRightTranslation_single]
  congr 1
  rw [map_mul, map_inv, mul_inv_rev, inv_inv]

theorem conjugatedResolution_augmentation_zero (t : G)
    (P : ProjectiveResolution (Rep.trivial k N k)) :
    (conjugatedResolution k N t P).π.f 0 =
      Rep.resMap (MulAut.conjNormal (H := N) t⁻¹).toMonoidHom (P.π.f 0) := by
  rfl

theorem inducedTranslation_augmentation_zero (t : G)
    (P : ProjectiveResolution (Rep.trivial k N k)) :
    (inducedTranslation k N t P).f 0 ≫ Rep.indMap N.subtype (P.π.f 0) =
      Rep.indMap N.subtype (P.π.f 0) ≫ inducedTrivialTranslation k N t := by
  change inducedSemilinearMap k N t _ _ ((conjugationResolutionLift k N t P).f 0) ≫
      Rep.indMap N.subtype (P.π.f 0) =
    Rep.indMap N.subtype (P.π.f 0) ≫
      inducedSemilinearMap k N t (Rep.trivial k N k) (Rep.trivial k N k)
        (𝟙 (Rep.trivial k N k))
  have h := ProjectiveResolution.lift_commutes_zero (𝟙 (Rep.trivial k N k)) P
    (conjugatedResolution k N t P)
  rw [conjugatedResolution_augmentation_zero] at h
  change (conjugationResolutionLift k N t P).f 0 ≫
      Rep.resMap (MulAut.conjNormal (H := N) t⁻¹).toMonoidHom (P.π.f 0) =
        P.π.f 0 ≫ 𝟙 (Rep.trivial k N k) at h
  calc
    _ = inducedSemilinearMap k N t (P.complex.X 0) (Rep.trivial k N k)
        ((conjugationResolutionLift k N t P).f 0 ≫
          Rep.resMap (MulAut.conjNormal (H := N) t⁻¹).toMonoidHom (P.π.f 0)) :=
      semilinear_comp_inductionMap k N t
        (A := P.complex.X 0) (B := P.complex.X 0) (C := Rep.trivial k N k) _ _
    _ = inducedSemilinearMap k N t (P.complex.X 0) (Rep.trivial k N k)
        (P.π.f 0 ≫ 𝟙 (Rep.trivial k N k)) :=
      congrArg (inducedSemilinearMap k N t (P.complex.X 0) (Rep.trivial k N k)) h
    _ = _ := (inductionMap_comp_semilinear k N t
      (A := P.complex.X 0) (B := Rep.trivial k N k) (C := Rep.trivial k N k) (P.π.f 0)
      (𝟙 (Rep.trivial k N k))).symm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_InducedCyclicDifference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The explicit translation difference lifts the cyclic augmentation map -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory Representation
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2

variable {G : Type} [Group G] (N : Subgroup G) [N.Normal] [IsCyclic (G ⧸ N)]

local instance instCommGroupQuotientSubgroup_solutions : CommGroup (G ⧸ N) := IsCyclic.commGroup

theorem quotientRightTranslation_sub (t : G) :
    quotientRightTranslation ℤ N t - 𝟙 _ =
      Rep.resMap (QuotientGroup.mk' N) (cyclicDifference (G ⧸ N) (QuotientGroup.mk' N t)) := by
  apply Rep.hom_ext
  apply IntertwiningMap.ext
  apply MonoidAlgebra.lhom_ext'
  intro c
  apply LinearMap.ext_ring
  change (quotientRightTranslation ℤ N t).hom (MonoidAlgebra.single c 1) -
      MonoidAlgebra.single c 1 =
    Representation.leftRegular ℤ (G ⧸ N) (QuotientGroup.mk' N t) (MonoidAlgebra.single c 1) -
      MonoidAlgebra.single c 1
  rw [quotientRightTranslation_single, Representation.ofMulAction_single, smul_eq_mul, mul_comm]

def quotientInducedResolution (P : ProjectiveResolution (Rep.trivial ℤ N ℤ)) :=
  projectiveResolutionAlongIso (normalInducedResolution ℤ N P) (inductionTrivialIso ℤ N)

omit [IsCyclic (G ⧸ N)] in
theorem quotientInducedResolution_augmentation (P : ProjectiveResolution (Rep.trivial ℤ N ℤ)) :
    (quotientInducedResolution N P).π.f 0 =
      Rep.indMap N.subtype (P.π.f 0) ≫ (inductionTrivialIso ℤ N).hom := rfl

theorem inducedDifference_augmentation (t : G) (P : ProjectiveResolution (Rep.trivial ℤ N ℤ)) :
    ((inducedTranslation ℤ N t P - 𝟙 _).f 0) ≫ (quotientInducedResolution N P).π.f 0 =
      (quotientInducedResolution N P).π.f 0 ≫
        Rep.resMap (QuotientGroup.mk' N) (cyclicDifference (G ⧸ N) (QuotientGroup.mk' N t)) := by
  let p : P.complex.X 0 ⟶ Rep.trivial ℤ N ℤ := P.π.f 0
  let I := Rep.indMap N.subtype p
  let e := (inductionTrivialIso ℤ N).hom
  let U := inducedTrivialTranslation ℤ N t
  let Q := quotientRightTranslation ℤ N t
  let T : Rep.ind N.subtype (P.complex.X 0) ⟶ Rep.ind N.subtype (P.complex.X 0) :=
    (inducedTranslation ℤ N t P).f 0
  have hT : T ≫ I = I ≫ U := inducedTranslation_augmentation_zero ℤ N t P
  have hU : U ≫ e = e ≫ Q := inducedTrivialTranslation_quotient ℤ N t
  rw [quotientInducedResolution_augmentation, ← quotientRightTranslation_sub]
  change (T - 𝟙 (Rep.ind N.subtype (P.complex.X 0))) ≫ (I ≫ e) =
    (I ≫ e) ≫ (Q - 𝟙 (Rep.res (QuotientGroup.mk' N) (Rep.leftRegular ℤ (G ⧸ N))))
  calc
    (T - 𝟙 (Rep.ind N.subtype (P.complex.X 0))) ≫ (I ≫ e) = (T ≫ I) ≫ e - I ≫ e := by
      simp only [Preadditive.sub_comp, Category.id_comp, Category.assoc]
    _ = (I ≫ U) ≫ e - I ≫ e := by rw [hT]
    _ = (I ≫ e) ≫ Q - I ≫ e := by rw [Category.assoc, hU, ← Category.assoc]
    _ = (I ≫ e) ≫ (Q - 𝟙 (Rep.res (QuotientGroup.mk' N) (Rep.leftRegular ℤ (G ⧸ N)))) := by rw [Preadditive.comp_sub, Category.comp_id]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_IntegerQuotientStructure
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual infinite cyclic quotient determined by a height homomorphism -/

noncomputable section
namespace PolycyclicRecognition

variable {G : Type} [Group G] (q : G →* Multiplicative ℤ)
  (t : G) (ht : q t = Multiplicative.ofAdd 1)

def integerQuotientEquiv : G ⧸ q.ker ≃* Multiplicative ℤ :=
  QuotientGroup.quotientKerEquivOfRightInverse q (fun z => t ^ z.toAdd) (by
    intro z
    apply Multiplicative.toAdd.injective
    simp [map_zpow, ht])

@[simp] theorem integerQuotientEquiv_mk (g : G) :
    integerQuotientEquiv q t ht (QuotientGroup.mk' q.ker g) = q g := rfl

include ht in
theorem integerQuotient_isCyclic : IsCyclic (G ⧸ q.ker) :=
  isCyclic_of_injective (integerQuotientEquiv q t ht).toMonoidHom
    (integerQuotientEquiv q t ht).injective

include ht in
theorem integerQuotient_infinite : Infinite (G ⧸ q.ker) :=
  Infinite.of_injective (integerQuotientEquiv q t ht).symm
    (integerQuotientEquiv q t ht).symm.injective

include ht in
theorem integerQuotient_generator (x : G ⧸ q.ker) :
    x ∈ Subgroup.zpowers (QuotientGroup.mk' q.ker t) := by
  refine ⟨(integerQuotientEquiv q t ht x).toAdd, ?_⟩
  apply (integerQuotientEquiv q t ht).injective
  rw [map_zpow, integerQuotientEquiv_mk, ht]
  apply Multiplicative.toAdd.injective
  simp

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_CochainSuccessor
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The successor shift of a nonnegative cochain complex -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits HomologicalComplex

variable {k : Type} [CommRing k]

def negativeCochainComplex (C : CochainComplex (ModuleCat k) ℕ) :
    CochainComplex (ModuleCat k) ℕ where
  X := C.X
  d i j := -C.d i j
  shape i j hij := by rw [C.shape i j hij, neg_zero]
  d_comp_d' i j l _ _ := by simp only [Preadditive.neg_comp, Preadditive.comp_neg,
    neg_neg, C.d_comp_d]

def moduleNegIdentityIso (M : ModuleCat k) : M ≅ M where
  hom := -𝟙 M
  inv := -𝟙 M
  hom_inv_id := by simp
  inv_hom_id := by simp

def negativeCochainShortComplexIso (C : CochainComplex (ModuleCat k) ℕ) (i : ℕ) :
    (negativeCochainComplex C).sc i ≅ C.sc i :=
  ShortComplex.isoMk
    (S₁ := (negativeCochainComplex C).sc i) (S₂ := C.sc i)
    (moduleNegIdentityIso _) (Iso.refl _) (moduleNegIdentityIso _)
    (by change (-𝟙 _) ≫ C.d _ _ = (-C.d _ _) ≫ 𝟙 _; simp)
    (by change 𝟙 _ ≫ C.d _ _ = (-C.d _ _) ≫ (-𝟙 _); simp)

def negativeCochainHomologyIso (C : CochainComplex (ModuleCat k) ℕ) (i : ℕ) :
    (negativeCochainComplex C).homology i ≅ C.homology i :=
  ShortComplex.homologyMapIso (negativeCochainShortComplexIso C i)

def cochainSuccessorEmbedding : (ComplexShape.up ℕ).Embedding (ComplexShape.up ℕ) where
  f n := n + 1
  injective_f := fun _ _ h => Nat.add_right_cancel h
  rel h := by simpa only [ComplexShape.up_Rel] using congrArg (fun n : ℕ => n + 1) h

def cochainSuccessor (C : CochainComplex (ModuleCat k) ℕ) :
    CochainComplex (ModuleCat k) ℕ :=
  (negativeCochainComplex C).extend cochainSuccessorEmbedding

def cochainSuccessorXIso (C : CochainComplex (ModuleCat k) ℕ) (i : ℕ) :
    (cochainSuccessor C).X (i + 1) ≅ C.X i :=
  (negativeCochainComplex C).extendXIso cochainSuccessorEmbedding rfl

def cochainSuccessorHomologyIso (C : CochainComplex (ModuleCat k) ℕ) (i : ℕ) :
    (cochainSuccessor C).homology (i + 1) ≅ C.homology i :=
  (negativeCochainComplex C).extendHomologyIso cochainSuccessorEmbedding rfl ≪≫
    negativeCochainHomologyIso C i

theorem cochainSuccessor_zero (C : CochainComplex (ModuleCat k) ℕ) :
    IsZero ((cochainSuccessor C).X 0) :=
  (negativeCochainComplex C).isZero_extend_X cochainSuccessorEmbedding 0 (by
    intro i
    simp [cochainSuccessorEmbedding])

theorem cochainSuccessor_d (C : CochainComplex (ModuleCat k) ℕ) (i : ℕ) :
    (cochainSuccessor C).d (i + 1) (i + 2) =
      (cochainSuccessorXIso C i).hom ≫ (-C.d i (i + 1)) ≫
        (cochainSuccessorXIso C (i + 1)).inv :=
  (negativeCochainComplex C).extend_d_eq cochainSuccessorEmbedding rfl rfl

def cochainSuccessorCyclesIso (C : CochainComplex (ModuleCat k) ℕ) (i : ℕ) :
    (cochainSuccessor C).cycles (i + 1) ≅ C.cycles i :=
  (negativeCochainComplex C).extendCyclesIso cochainSuccessorEmbedding rfl ≪≫
    ShortComplex.cyclesMapIso (negativeCochainShortComplexIso C i)

theorem cochainSuccessorCyclesIso_iCycles (C : CochainComplex (ModuleCat k) ℕ) (i : ℕ) :
    (cochainSuccessorCyclesIso C i).hom ≫ C.iCycles i =
      (cochainSuccessor C).iCycles (i + 1) ≫ (cochainSuccessorXIso C i).hom := by
  have hn : ShortComplex.cyclesMap (negativeCochainShortComplexIso C i).hom ≫
      C.iCycles i = (negativeCochainComplex C).iCycles i := by
    exact (ShortComplex.cyclesMap_i (negativeCochainShortComplexIso C i).hom).trans
      (Category.comp_id _)
  exact (Category.assoc
    ((negativeCochainComplex C).extendCyclesIso cochainSuccessorEmbedding (j := i) rfl).hom
    (ShortComplex.cyclesMap (negativeCochainShortComplexIso C i).hom) (C.iCycles i)).trans
      ((congrArg
        (fun f => ((negativeCochainComplex C).extendCyclesIso
          cochainSuccessorEmbedding (j := i) rfl).hom ≫ f) hn).trans
        ((negativeCochainComplex C).extendCyclesIso_hom_iCycles
          cochainSuccessorEmbedding (j := i) rfl))

theorem cochainSuccessorHomologyIso_π (C : CochainComplex (ModuleCat k) ℕ) (i : ℕ) :
    (cochainSuccessor C).homologyπ (i + 1) ≫ (cochainSuccessorHomologyIso C i).hom =
      (cochainSuccessorCyclesIso C i).hom ≫ C.homologyπ i := by
  have he := (negativeCochainComplex C).homologyπ_extendHomologyIso_hom
    cochainSuccessorEmbedding (j := i) rfl
  have hn := ShortComplex.homologyπ_naturality (negativeCochainShortComplexIso C i).hom
  exact (Category.assoc
    (((negativeCochainComplex C).extend cochainSuccessorEmbedding).homologyπ
      (cochainSuccessorEmbedding.f i))
    ((negativeCochainComplex C).extendHomologyIso cochainSuccessorEmbedding (j := i) rfl).hom
    (ShortComplex.homologyMap (negativeCochainShortComplexIso C i).hom)).symm.trans
    ((congrArg (fun f => f ≫ ShortComplex.homologyMap
      (negativeCochainShortComplexIso C i).hom) he).trans
      ((Category.assoc _ _ _).trans
        ((congrArg
          (fun f => ((negativeCochainComplex C).extendCyclesIso
            cochainSuccessorEmbedding (j := i) rfl).hom ≫ f) hn).trans
          (Category.assoc _ _ _).symm)))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_CofiberCochainSequence
attribute [-instance] _root_.OAI.PolycyclicRecognition.repCofiber_projective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The short exact sequence of cochains of a mapping cone -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance 2000] Rep.hV2
attribute [local instance 2000] Rep.instLinear
attribute [local instance 2100] Linear.homModule

variable {k G : Type} [CommRing k] [Group G]
  {P Q : ChainComplex (Rep k G) ℕ} (φ : P ⟶ Q) (A : Rep k G)

def cofiberCochainInclusionComponent (i : ℕ) :
    (cochainSuccessor (P.linearYonedaObj k A)).X i ⟶
      (ChainComplex.linearYonedaObj (repCofiber φ) k A).X i :=
  match i with
  | 0 => 0
  | n + 1 => (cochainSuccessorXIso (P.linearYonedaObj k A) n).hom ≫
      ModuleCat.ofHom (Linear.leftComp k A (repCofiberFst φ n))

def cofiberCochainInclusion :
    cochainSuccessor (P.linearYonedaObj k A) ⟶ ChainComplex.linearYonedaObj (repCofiber φ) k A where
  f := cofiberCochainInclusionComponent φ A
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    cases i with
    | zero => exact (cochainSuccessor_zero (P.linearYonedaObj k A)).eq_of_src _ _
    | succ i =>
      change ((cochainSuccessorXIso (P.linearYonedaObj k A) i).hom ≫ _) ≫ _ =
        (cochainSuccessor (P.linearYonedaObj k A)).d (i + 1) (i + 2) ≫
          ((cochainSuccessorXIso (P.linearYonedaObj k A) (i + 1)).hom ≫ _)
      rw [cochainSuccessor_d]
      simp only [Category.assoc]
      erw [Iso.inv_hom_id_assoc]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      let f : P.X i ⟶ A := (cochainSuccessorXIso (P.linearYonedaObj k A) i).hom.hom x
      change (repCofiber φ).d (i + 2) (i + 1) ≫ (repCofiberFst φ i ≫ f) =
        repCofiberFst φ (i + 1) ≫ (-(P.d (i + 1) i ≫ f))
      have hd : (repCofiber φ).d (i + 2) (i + 1) ≫ repCofiberFst φ i =
          -repCofiberFst φ (i + 1) ≫ P.d (i + 1) i :=
        homotopyCofiber.d_fstX φ (i + 2) (i + 1) i rfl rfl
      rw [← Category.assoc, hd]
      simp only [Preadditive.neg_comp, Preadditive.comp_neg, Category.assoc]

theorem cofiberCochainInclusion_injective (i : ℕ) :
    Function.Injective ((cofiberCochainInclusion φ A).f i).hom := by
  cases i with
  | zero =>
    let := ModuleCat.subsingleton_of_isZero (cochainSuccessor_zero (P.linearYonedaObj k A))
    exact fun _ _ _ => Subsingleton.elim _ _
  | succ i =>
    intro x y hxy
    let E : (cochainSuccessor (P.linearYonedaObj k A)).X (i + 1) ≃ₗ[k] (P.X i ⟶ A) :=
      (cochainSuccessorXIso (P.linearYonedaObj k A) i).toLinearEquiv
    apply E.injective
    change repCofiberFst φ i ≫ E x = repCofiberFst φ i ≫ E y at hxy
    have h := congrArg (fun f => repCofiberInl φ i ≫ f) hxy
    have hid : repCofiberInl φ i ≫ repCofiberFst φ i = 𝟙 _ :=
      homotopyCofiber.inlX_fstX φ i (i + 1) rfl
    simpa only [← Category.assoc, hid, Category.id_comp] using h

def cofiberCochainSectionComponent (i : ℕ) :
    (Q.linearYonedaObj k A).X i ⟶ (ChainComplex.linearYonedaObj (repCofiber φ) k A).X i :=
  ModuleCat.ofHom (Linear.leftComp k A (repCofiberSnd φ i))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CofiberConnecting
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The connecting homomorphism of the mapping-cone cochain sequence -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance 2000] Rep.hV2
attribute [local instance 2000] Rep.instLinear
attribute [local instance 2100] Linear.homModule

variable {k : Type} [CommRing k]

theorem cochainSuccessor_liftCycles_homology
    (C : CochainComplex (ModuleCat k) ℕ) (i : ℕ) {M : ModuleCat k}
    (x : M ⟶ C.X i) (hx : x ≫ C.d i (i + 1) = 0)
    (hs : (x ≫ (cochainSuccessorXIso C i).inv) ≫
      (cochainSuccessor C).d (i + 1) (i + 2) = 0) :
    (cochainSuccessor C).liftCycles (x ≫ (cochainSuccessorXIso C i).inv) (i + 2) (by simp) hs ≫
        (cochainSuccessor C).homologyπ (i + 1) ≫ (cochainSuccessorHomologyIso C i).hom =
      C.liftCycles x (i + 1) (by simp) hx ≫ C.homologyπ i := by
  rw [cochainSuccessorHomologyIso_π, ← Category.assoc]
  congr 1
  apply (cancel_mono (C.iCycles i)).mp
  rw [Category.assoc, cochainSuccessorCyclesIso_iCycles, ← Category.assoc,
    liftCycles_i, Category.assoc, Iso.inv_hom_id, Category.comp_id, liftCycles_i]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_IntegerExtensionDuality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The cohomological dimension shift for an infinite cyclic extension -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2

variable {G : Type} [Group G] (q : G →* Multiplicative ℤ)
  (t : G) (ht : q t = Multiplicative.ofAdd 1)

section Cyclic
variable [IsCyclic (G ⧸ q.ker)] [Infinite (G ⧸ q.ker)]
local instance instCommGroupQuotientSubgroupKerMultiplicativeInt_solutions : CommGroup (G ⧸ q.ker) := IsCyclic.commGroup

variable (P : ProjectiveResolution (Rep.trivial ℤ q.ker ℤ))

def integerExtensionMap :=
  ProjectiveResolution.lift
    (Rep.resMap (QuotientGroup.mk' q.ker)
      (cyclicDifference (G ⧸ q.ker) (QuotientGroup.mk' q.ker t)))
    (quotientInducedResolution q.ker P) (quotientInducedResolution q.ker P)

end Cyclic

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_MeanSubgroup
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Restricting invariant means to subgroups

The finite-index height kernel in the recognition argument inherits amenability
from the ambient group. The construction below works for an arbitrary subgroup:
choose representatives for right cosets, construct an equivariant map to the subgroup,
and extend each bounded function by composition with this map.
-/

noncomputable section

namespace PolycyclicRecognition

open scoped ENNReal

universe u

variable {G : Type u} [Group G]

/-- The representative selected for the right coset containing `g`. -/
def rightCosetRepresentative (K : Subgroup G) (g : G) : G :=
  (Quotient.mk'' g : Quotient (QuotientGroup.rightRel K)).out

/-- A right-coset transversal gives an equivariant coordinate in the subgroup. -/
def subgroupCoordinate (K : Subgroup G) (g : G) : K :=
  ⟨g * (rightCosetRepresentative K g)⁻¹,
    QuotientGroup.rightRel_apply.mp
      (Quotient.exact' (Quotient.out_eq' (Quotient.mk'' g :
        Quotient (QuotientGroup.rightRel K))))⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CharacteristicQuotientAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Automorphisms on a characteristic quotient -/

namespace PolycyclicRecognition

variable {G : Type} [Group G] (H : Subgroup G) [H.Characteristic]

def characteristicQuotientMap (e : MulAut G) : (G ⧸ H) →* G ⧸ H :=
  QuotientGroup.map H H e.toMonoidHom
    (Subgroup.characteristic_iff_le_comap.mp inferInstance e)

def characteristicQuotientAut : MulAut G →* MulAut (G ⧸ H) where
  toFun e :=
    { toFun := characteristicQuotientMap H e
      invFun := characteristicQuotientMap H e.symm
      left_inv := by
        intro x
        obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective H x
        change (QuotientGroup.mk' H) (e.symm (e g)) = (QuotientGroup.mk' H) g
        rw [e.symm_apply_apply]
      right_inv := by
        intro x
        obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective H x
        change (QuotientGroup.mk' H) (e (e.symm g)) = (QuotientGroup.mk' H) g
        rw [e.apply_symm_apply]
      map_mul' := (characteristicQuotientMap H e).map_mul }
  map_one' := by
    apply MulEquiv.ext
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective H x
    rfl
  map_mul' e f := by
    apply MulEquiv.ext
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective H x
    rfl

@[simp] theorem characteristicQuotientAut_mk (e : MulAut G) (g : G) :
    characteristicQuotientAut H e ((QuotientGroup.mk' H) g) =
      (QuotientGroup.mk' H) (e g) := rfl

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RegularDualRepresentation
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The contravariant regular dual of a group-ring representation

The regular dual is Hom over the group ring into the regular module, with
left action induced by inverse right translation on the target. This is the
representation used in the top-degree duality pairing.
-/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G]

def regularRightTranslation (g : G) : Rep.leftRegular ℤ G ⟶ Rep.leftRegular ℤ G :=
  Rep.leftRegularHom _ (MonoidAlgebra.single g⁻¹ 1)

@[simp] theorem regularRightTranslation_single (g h : G) (r : ℤ) :
    (regularRightTranslation g).hom (MonoidAlgebra.single h r) =
      MonoidAlgebra.single (h * g⁻¹) r := by
  rw [regularRightTranslation, Rep.leftRegularHom_hom_single]
  rw [Representation.ofMulAction_single]
  simp

@[simp] theorem regularRightTranslation_one :
    regularRightTranslation (1 : G) = 𝟙 (Rep.leftRegular ℤ G) := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply MonoidAlgebra.lhom_ext'
  intro h
  apply LinearMap.ext_ring
  change (regularRightTranslation (1 : G)).hom (MonoidAlgebra.single h 1) =
    MonoidAlgebra.single h 1
  simpa only [inv_one, mul_one] using regularRightTranslation_single (1 : G) h 1

theorem regularRightTranslation_mul (g h : G) :
    regularRightTranslation h ≫ regularRightTranslation g =
      regularRightTranslation (g * h) := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply MonoidAlgebra.lhom_ext'
  intro x
  apply LinearMap.ext_ring
  change (regularRightTranslation g).hom
    ((regularRightTranslation h).hom (MonoidAlgebra.single x 1)) =
      (regularRightTranslation (g * h)).hom (MonoidAlgebra.single x 1)
  rw [regularRightTranslation_single, regularRightTranslation_single,
    regularRightTranslation_single]
  simp only [mul_inv_rev, mul_assoc]

def regularDualRepresentation (P : Rep ℤ G) :
    Representation ℤ G (P ⟶ Rep.leftRegular ℤ G) where
  toFun g := Linear.rightComp ℤ P (regularRightTranslation g)
  map_one' := by
    apply LinearMap.ext
    intro f
    change f ≫ regularRightTranslation (1 : G) = f
    simp
  map_mul' g h := by
    apply LinearMap.ext
    intro f
    change (f ≫ regularRightTranslation (g * h)) =
      (f ≫ regularRightTranslation h) ≫ regularRightTranslation g
    rw [Category.assoc, regularRightTranslation_mul]

def regularDual (P : Rep ℤ G) : Rep ℤ G := Rep.of (regularDualRepresentation P)

def regularDualMap {P Q : Rep ℤ G} (f : P ⟶ Q) : regularDual Q ⟶ regularDual P :=
  Rep.ofHom ⟨Linear.leftComp ℤ (Rep.leftRegular ℤ G) f, by
    intro g
    apply LinearMap.ext
    intro q
    exact (Category.assoc f q (regularRightTranslation g)).symm⟩

@[simp] theorem regularDualMap_apply {P Q : Rep ℤ G} (f : P ⟶ Q)
    (q : Q ⟶ Rep.leftRegular ℤ G) : (regularDualMap f).hom q = f ≫ q := rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CokernelHomModule
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Maps from a cokernel as an integral kernel module -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G]

def cokernelHomAddEquiv {P Q : Rep ℤ G} (f : P ⟶ Q) (A : Rep ℤ G) :
    (cokernel f ⟶ A) ≃+ LinearMap.ker (Linear.leftComp ℤ A f) where
  toFun h := ⟨cokernel.π f ≫ h, by
    change f ≫ (cokernel.π f ≫ h) = 0
    simp⟩
  invFun h := cokernel.desc f h.val (by exact h.property)
  left_inv h := by
    apply (cancel_epi (cokernel.π f)).mp
    change cokernel.π f ≫ cokernel.desc f (cokernel.π f ≫ h) _ = _
    exact cokernel.π_desc _ _ _
  right_inv h := by
    apply Subtype.ext
    change cokernel.π f ≫ cokernel.desc f h.val _ = h.val
    exact cokernel.π_desc _ _ _
  map_add' h k := by
    apply Subtype.ext
    change cokernel.π f ≫ (h + k) = cokernel.π f ≫ h + cokernel.π f ≫ k
    exact Rep.comp_add _ _ _

def cokernelHomModuleEquiv {P Q : Rep ℤ G} (f : P ⟶ Q) (A : Rep ℤ G) :
    (cokernel f ⟶ A) ≃ₗ[ℤ] LinearMap.ker (Linear.leftComp ℤ A f) where
  __ := cokernelHomAddEquiv f A
  map_smul' r h := map_intCast_smul (cokernelHomAddEquiv f A) ℤ ℤ r h

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CommonEigenvectors
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite common eigenspaces and a common eigenvector

Common eigenspaces form an independent family even when the operators do
not commute. For commuting operators over an algebraically closed field,
a minimal nonzero invariant subspace supplies a common eigenvector.
-/

noncomputable section
namespace PolycyclicRecognition

variable {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]

def commonEigenspace (f : I → Module.End K V) (χ : I → K) : Submodule K V :=
  ⨅ i, (f i).eigenspace (χ i)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_FiniteAugmentationKernel
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The augmentation kernel for a finitely generated group

Differences corresponding to a finite group generating set generate the
integral augmentation kernel as a left group-ring module.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
open scoped MonoidAlgebra
variable {G : Type} [Group G]

def augmentationDifference (g : G) : (Representation.leftRegular ℤ G).asModule :=
  (Representation.leftRegular ℤ G).asModuleEquiv.symm
    (MonoidAlgebra.single g (1 : ℤ) - MonoidAlgebra.single 1 (1 : ℤ))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_LocallyNilpotentDimension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite integral dimension makes local nilpotence uniform

Every element of a lower-central term is witnessed in a finitely generated
subgroup. The common class bound from cohomological dimension therefore makes
a locally nilpotent group nilpotent, including groups not finitely generated.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped commutatorElement

variable {G : Type} [Group G]

def fgLowerCentralSubgroup (n : ℕ) : Subgroup G where
  carrier := {g | ∃ H : Subgroup G, H.FG ∧ g ∈ H.lowerCentralSeries n}
  one_mem' := ⟨⊥, Subgroup.FG.bot, Subgroup.one_mem _⟩
  mul_mem' := by
    rintro x y ⟨H, hH, hx⟩ ⟨K, hK, hy⟩
    exact ⟨H ⊔ K, hH.sup hK, Subgroup.mul_mem _
      (Subgroup.lowerCentralSeries_mono n le_sup_left hx)
      (Subgroup.lowerCentralSeries_mono n le_sup_right hy)⟩
  inv_mem' := by
    rintro x ⟨H, hH, hx⟩
    exact ⟨H, hH, Subgroup.inv_mem _ hx⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_DirectedLowerCentral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Directed unions with a uniform lower-central bound

The lower-central terms of a directed union are witnessed in its constituent
subgroups. The uniform bound from integral cohomological dimension therefore
allows Zorn's lemma to produce a maximal nilpotent normal subgroup.
-/

namespace PolycyclicRecognition

variable {G : Type} [Group G]

def directedLowerCentral (C : Set (Subgroup G)) (hC : C.Nonempty)
    (hdir : DirectedOn (· ≤ ·) C) (n : ℕ) : Subgroup G where
  carrier := {g | ∃ H ∈ C, g ∈ H.lowerCentralSeries n}
  one_mem' := by
    obtain ⟨H, hH⟩ := hC
    exact ⟨H, hH, Subgroup.one_mem _⟩
  mul_mem' := by
    rintro x y ⟨H, hH, hx⟩ ⟨K, hK, hy⟩
    obtain ⟨L, hL, hHL, hKL⟩ := hdir H hH K hK
    exact ⟨L, hL, Subgroup.mul_mem _
      (Subgroup.lowerCentralSeries_mono n hHL hx)
      (Subgroup.lowerCentralSeries_mono n hKL hy)⟩
  inv_mem' := by
    rintro x ⟨H, hH, hx⟩
    exact ⟨H, hH, Subgroup.inv_mem _ hx⟩

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CommutingSubgroupProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Products of commuting nilpotent subgroups

Multiplication is a surjective homomorphism from the direct product onto the
join when the two subgroups centralize each other. Nilpotence passes through
this explicit homomorphism.
-/

namespace PolycyclicRecognition

variable {G : Type} [Group G] (H K : Subgroup G)
  (hcomm : ∀ h : H, ∀ k : K, (h : G) * k = (k : G) * h)

def commutingProductHom : H × K →* G where
  toFun p := (p.1 : G) * p.2
  map_one' := one_mul _
  map_mul' p q := by
    change ((p.1 : G) * q.1) * ((p.2 : G) * q.2) =
      ((p.1 : G) * p.2) * ((q.1 : G) * q.2)
    calc
      _ = (p.1 : G) * (((q.1 : G) * p.2) * q.2) := by simp only [mul_assoc]
      _ = (p.1 : G) * (((p.2 : G) * q.1) * q.2) := by rw [hcomm q.1 p.2]
      _ = _ := by simp only [mul_assoc]

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_TriangularMatrixExponential
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Diagonal entries of an upper triangular matrix exponential -/

noncomputable section
namespace PolycyclicRecognition

open scoped Matrix.Norms.Operator

variable {n : ℕ}

theorem matrix_exp_entry_hasSum (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    HasSum (fun k : ℕ => (k.factorial : ℝ)⁻¹ * (A ^ k) i j) (NormedSpace.exp A i j) := by
  let ev : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ :=
    { toFun := fun B => B i j
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  let f := ev.toContinuousLinearMap
  have hs := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) A).map f f.continuous
  change HasSum (fun k : ℕ => (k.factorial : ℝ)⁻¹ * (A ^ k) i j)
    (NormedSpace.exp A i j) at hs
  exact hs

theorem matrix_exp_upperTriangular (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsUpperTriangular) : (NormedSpace.exp A).IsUpperTriangular := by
  intro i j hji
  have hs := matrix_exp_entry_hasSum A i j
  have hz : (fun k : ℕ => (k.factorial : ℝ)⁻¹ * (A ^ k) i j) = fun _ => 0 := by
    funext k
    rw [(hA.pow k) hji, mul_zero]
  rw [hz] at hs
  exact hs.unique hasSum_zero

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ComplexMatrixExtension
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Complex matrix coordinates for the intrinsic adjoint representation -/

noncomputable section
namespace PolycyclicRecognition

open Module
open scoped TensorProduct Manifold Matrix.Norms.Operator
attribute [local instance 100] LieRing.ofAssociativeRing

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] {m n : ℕ}

def complexMatrixExtension (b : Basis (Fin m) ℝ L)
    (c : Basis (Fin n) ℂ (ℂ ⊗[ℝ] L)) :
    Matrix (Fin m) (Fin m) ℝ →ₐ[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  ((LinearMap.toMatrixAlgEquiv c).restrictScalars ℝ).toAlgHom.comp
    (((LinearMap.toMatrixAlgEquiv (b.baseChange ℂ)).symm.restrictScalars ℝ).toAlgHom.comp
      (Algebra.ofId ℝ ℂ).mapMatrix)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FreeAbelianLogarithm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compatible logarithms of characters of free abelian groups

Choosing logarithms only on a basis preserves all multiplicative relations.
-/

noncomputable section
namespace PolycyclicRecognition

def complexUnitExp : Multiplicative ℂ →* ℂˣ := Complex.expMonoidHom.toHomUnits

@[simp] theorem complexUnitExp_val (z : Multiplicative ℂ) :
    (complexUnitExp z : ℂ) = Complex.exp z.toAdd := rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ConjugateCharacterLog
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conjugation-compatible logarithms after a finite power

Symmetrizing a compatible logarithm doubles its power and makes it respect
the involution. This will preserve real forms in the spectral construction.
-/

noncomputable section
namespace PolycyclicRecognition
variable {G : Type} [CommGroup G]

def conjugateCharacterLog (L : G →* Multiplicative ℂ) (c : G →* G) :
    G →* Multiplicative ℂ where
  toFun g := Multiplicative.ofAdd (star (L (c g)).toAdd)
  map_one' := by simp
  map_mul' g h := by
    apply Multiplicative.ext
    simp [map_mul, star_add]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ControlledProductPairs
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Controlled Følner pairs from compact product coordinates

The required estimate is an explicit right-product containment in a larger
rectangle, together with a bounded ratio of the two coordinate volumes.
-/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory MeasureTheory.Measure Metric Set Filter
open scoped ENNReal

variable {G N D : Type*} [Group G] [MetricSpace G] [IsTopologicalGroup G]
  [IsIsometricSMul G G] [ProperSpace G] [MeasurableSpace G] [BorelSpace G]
  [TopologicalSpace N] [TopologicalSpace D] [T2Space N] [T2Space D]
  [MeasurableSpace N] [MeasurableSpace D] [BorelSpace N] [BorelSpace D]
  [SecondCountableTopology N] [SecondCountableTopology D]
  (e : G ≃ₜ N × D) (μN : Measure N) (μD : Measure D)
  [SFinite μN] [SFinite μD] [IsFiniteMeasureOnCompacts μN] [IsFiniteMeasureOnCompacts μD]

omit [Group G] [IsTopologicalGroup G] [IsIsometricSMul G G] [ProperSpace G]
  [T2Space N] [T2Space D] [SFinite μN] [IsFiniteMeasureOnCompacts μN]
  [IsFiniteMeasureOnCompacts μD] [SecondCountableTopology N] in
theorem productCoordinateMeasure_rectangle {A : Set N} {B : Set D}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    (Measure.map e.symm (μN.prod μD)) (e ⁻¹' (A ×ˢ B)) = μN A * μD B := by
  rw [Measure.map_apply e.symm.measurable (e.measurable (hA.prod hB))]
  have he : e.symm ⁻¹' (e ⁻¹' (A ×ˢ B)) = A ×ˢ B := by
    ext p
    simp only [mem_preimage, e.apply_symm_apply]
  rw [he, Measure.prod_prod]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CoordinateBilinearExpansion
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite-coordinate expansion of the transported Lie bracket -/

noncomputable section

namespace PolycyclicRecognition

open Module
open scoped BigOperators

/-- A single elementary coordinate bilinear map. -/
def coordinateBilinearUnit {n : ℕ} (i j k : Fin n) :
    (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  (ContinuousLinearMap.proj i).smulRight
    ((ContinuousLinearMap.proj j).smulRight (Pi.single k (1 : ℝ)))

@[simp] theorem coordinateBilinearUnit_apply {n : ℕ} (i j k : Fin n)
    (x y : Fin n → ℝ) :
    coordinateBilinearUnit i j k x y = x i • y j • Pi.single k (1 : ℝ) := rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RationalCoefficientSequence
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The factorial coefficient system with colimit the rational numbers -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
attribute [local instance 2000] Rep.hV2 Rep.instLinear

def factorialMultiplier (i j : ℕ) : ℤ := ∏ k ∈ Finset.Ico i j, (k + 1 : ℤ)

theorem factorialMultiplier_comp (i j k : ℕ) (hij : i ≤ j) (hjk : j ≤ k) :
    factorialMultiplier i j * factorialMultiplier j k = factorialMultiplier i k :=
  Finset.prod_Ico_consecutive (fun n : ℕ => (n + 1 : ℤ)) hij hjk

@[simp]
theorem factorialMultiplier_self (i : ℕ) : factorialMultiplier i i = 1 := by
  simp [factorialMultiplier]

theorem factorialMultiplier_zero (j : ℕ) : factorialMultiplier 0 j = j.factorial := by
  simp only [factorialMultiplier, Nat.Ico_zero_eq_range, Nat.factorial_eq_prod_range_add_one,
    Nat.cast_prod, Nat.cast_add, Nat.cast_one]

theorem factorialMultiplier_factorial (i j : ℕ) (hij : i ≤ j) :
    (i.factorial : ℤ) * factorialMultiplier i j = j.factorial := by
  rw [← factorialMultiplier_zero i, ← factorialMultiplier_zero j]
  exact factorialMultiplier_comp 0 i j (Nat.zero_le i) hij

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_ShiftedCohomologyDimensionShift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Dimension shifting in the completed coefficient theory -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2300] Module.DirectLimit.module
variable {G : Type} [Group G]

theorem cohomologyConnecting_reindex (S : ShortComplex (Rep.{0} ℤ G))
    (hS : S.ShortExact) (i j k l : ℕ) (hij : i + 1 = j) (hkl : k + 1 = l)
    (hik : i = k) (hjl : j = l) :
    groupCohomology.δ hS i j hij ≫
        (eqToIso (congrArg (fun d => groupCohomology S.X₁ d) hjl)).hom =
      (eqToIso (congrArg (fun d => groupCohomology S.X₃ d) hik)).hom ≫
        groupCohomology.δ hS k l hkl := by
  subst k
  subst l
  simp only [eqToIso_refl, Iso.refl_hom, Category.comp_id, Category.id_comp]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CountableFreeRetract
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Countably generated free representations are retracts of one fixed free module -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {Q G : Type} [Group Q] [Group G]

def countableFreeRetract (α : Type) [Countable α] :
    Retract (Rep.free ℤ Q α) (Rep.free ℤ Q ℕ) := by
  classical
  let := Encodable.ofCountable α
  let i : Rep.free ℤ Q α ⟶ Rep.free ℤ Q ℕ :=
    Rep.freeLift ℤ Q _ (fun a => Finsupp.single (Encodable.encode a) (MonoidAlgebra.single 1 1))
  let r : Rep.free ℤ Q ℕ ⟶ Rep.free ℤ Q α :=
    Rep.freeLift ℤ Q _ (fun n => match Encodable.decode (α := α) n with
      | some a => Finsupp.single a (MonoidAlgebra.single 1 1)
      | none => 0)
  refine ⟨i, r, ?_⟩
  apply Rep.free_ext
  intro a
  change r.hom (i.hom (Finsupp.single a (MonoidAlgebra.single 1 1))) =
    Finsupp.single a (MonoidAlgebra.single 1 1)
  simp [i, r, Rep.freeLift, Representation.freeLift_single_single]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialCoefficientContinuity
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coefficients of a continuous bounded-degree polynomial family

Each coefficient is a fixed finite linear combination of evaluations on
the finite-dimensional space of bounded-degree polynomials. This supplies
uniform coefficient bounds from compact parameter sets, even when the
input cubes have growing radii.
-/

noncomputable section
namespace PolycyclicRecognition

open Module MvPolynomial

def boundedDegreeEvaluation {m : ℕ} (D : ℕ) (x : Fin m → ℝ) :
    restrictTotalDegree (Fin m) ℝ D →ₗ[ℝ] ℝ :=
  (aeval x).toLinearMap.comp (restrictTotalDegree (Fin m) ℝ D).subtype

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_BoxCoordinateChanges
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coordinate changes between the individual and union boxes

The target normalization uses a maximizing word basis. Inclusion of the
individual support costs gives a uniform bound on the coordinate change.
When a letter attains the union support on one side, its two normalized
vectors correspond exactly under this map.
-/

noncomputable section
namespace PolycyclicRecognition

open Module

variable {L I : Type*} [LieRing L] [LieAlgebra ℝ L]

def boxCoordinateChange {n : ℕ} (target source : Basis (Fin n) ℝ L) :
    (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  (source.equivFun.symm.trans target.equivFun).toLinearMap.toContinuousLinearMap

@[simp] theorem boxCoordinateChange_apply {n : ℕ}
    (target source : Basis (Fin n) ℝ L) (v : Fin n → ℝ) :
    boxCoordinateChange target source v = target.equivFun (source.equivFun.symm v) := rfl

@[simp] theorem boxCoordinateChange_coordinates {n : ℕ}
    (target source : Basis (Fin n) ℝ L) (v : L) :
    boxCoordinateChange target source (source.equivFun v) = target.equivFun v := by
  simp

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ExponentialTupleCoordinates
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact product volume under independent exponential coordinate charts -/

noncomputable section
namespace PolycyclicRecognition

open Module MeasureTheory Set
open scoped Manifold ENNReal NNReal BigOperators

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]
  {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [MeasurableSpace G] [BorelSpace G]

def basisVolumeMultiplier {n : ℕ} (b₀ b : Basis (Fin n) ℝ L) : ℝ≥0 :=
  ⟨|(b₀.toMatrix b).det|, abs_nonneg _⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RootIntervalSampling
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual independent interval laws for the root increments -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory

variable {L N I : Type*} [AddCommGroup L] [Module ℝ L] [Group N]

/-- Extend a fixed finite word by zero directions for the unused indices. -/
def rootIntervalDirection {m : ℕ} (letters : Fin m → I) (X : I → L)
    (s : I → ℝ) (r : ℝ) (j : ℕ) : L :=
  if h : j < m then Real.exp (r * s (letters ⟨j, h⟩)) • X (letters ⟨j, h⟩) else 0

def rootIntervalSample (Exp : L → N) {m : ℕ} (letters : Fin m → I)
    (X : I → L) (s : I → ℝ) (r : ℝ) (j : ℕ) (t : ℝ) : N :=
  Exp (t • rootIntervalDirection letters X s r j)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CoupledRootIntervals
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conjugated interval laws used by second-sheet source switches -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set Metric

variable {L N I : Type*} [AddCommGroup L] [Module ℝ L] [Group N]
  [TopologicalSpace N] [IsTopologicalGroup N] [MeasurableSpace N] [BorelSpace N] [T2Space N]

def coupledRootIntervalSample (Exp : L → N) {m : ℕ} (letters : Fin m → I)
    (X : I → L) (s : I → ℝ) (r : ℝ) (k : ℕ → N) (j : ℕ) (t : ℝ) : N :=
  k j * rootIntervalSample Exp letters X s r j t * (k j)⁻¹

def coupledRootIntervalLaw (Exp : L → N) {m : ℕ} (letters : Fin m → I)
    (X : I → L) (s : I → ℝ) (r ρ : ℝ) (k : ℕ → N) (j : ℕ) : Measure N :=
  Measure.map (coupledRootIntervalSample Exp letters X s r k j) (uniformIntervalLaw ρ)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CoupledBundleStates
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual bundle conjugations preserve joint Haar volume -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set

variable {N : Type*} [Group N] [TopologicalSpace N] [IsTopologicalGroup N]

def innerContinuousMulEquiv (k : N) : N ≃ₜ* N where
  toMulEquiv := MulAut.conj k
  continuous_toFun := IsTopologicalGroup.continuous_conj k
  continuous_invFun := by
    change Continuous (fun u : N => k⁻¹ * u * k)
    simpa only [inv_inv] using (IsTopologicalGroup.continuous_conj k⁻¹)

@[simp] theorem innerContinuousMulEquiv_apply (k u : N) :
    innerContinuousMulEquiv k u = k * u * k⁻¹ := rfl

variable [MeasurableSpace N] [BorelSpace N]

omit [TopologicalSpace N] [IsTopologicalGroup N] [MeasurableSpace N] [BorelSpace N] in
def bundleConjugator {h : ℕ} (m : ℕ) (k : Fin h → N) (j : ℕ) : N :=
  if hj : j < h * m then k (finProdFinEquiv.symm ⟨j, hj⟩).1 else 1

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CyclicJoinDimension
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Adjoining a lift of an infinite cyclic quotient

If the lift normalizes a subgroup of the kernel, its join with that subgroup
has precisely the expected kernel. This gives the dimension and solvability
bounds without imposing normality in the whole ambient group.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
open scoped Pointwise
variable {G : Type} [Group G] (q : G →* Multiplicative ℤ)
  (t : G) (ht : q t = Multiplicative.ofAdd 1) (A : Subgroup G)
include ht

theorem cyclicJoin_kernel_le (hA : A ≤ q.ker) (hnorm : t ∈ Subgroup.normalizer A) :
    (A ⊔ Subgroup.zpowers t) ⊓ q.ker ≤ A := by
  intro x hx
  have hp : x ∈ (A : Set G) * (Subgroup.zpowers t : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left A (Subgroup.zpowers t)
      (Subgroup.zpowers_le.mpr hnorm)]
    exact hx.1
  obtain ⟨a, ha, b, hb, hab⟩ := hp
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  have hqx : q x = 1 := hx.2
  have hqa : q a = 1 := hA ha
  have hn : n = 0 := by
    have h := congrArg Multiplicative.toAdd hqx
    rw [← hab, map_mul, hqa, one_mul, map_zpow, ht] at h
    simpa using h
  have he : x = a := by simpa [hn] using hab.symm
  rwa [he]

def cyclicJoinKernelMap (hA : A ≤ q.ker) (hnorm : t ∈ Subgroup.normalizer A) :
    (q.comp (A ⊔ Subgroup.zpowers t).subtype).ker →* A where
  toFun x := ⟨x.val.val, cyclicJoin_kernel_le q t ht A hA hnorm
    ⟨x.val.property, x.property⟩⟩
  map_one' := rfl
  map_mul' _ _ := rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_IntegerSemidirectLattice
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The integral semidirect product is the lattice in its real extension -/

noncomputable section
namespace PolycyclicRecognition
variable {H N : Type*} [Group H] [Group N]

def integerPowerAction (a : MulAut H) : Multiplicative ℤ →* MulAut H where
  toFun n := a ^ n.toAdd
  map_one' := zpow_zero a
  map_mul' n m := zpow_add a n.toAdd m.toAdd

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CyclicKernelSplitting
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Splitting an actual infinite cyclic quotient -/

noncomputable section
namespace PolycyclicRecognition
variable {G : Type*} [Group G]

def cyclicPowerHom (t : G) : Multiplicative ℤ →* G where
  toFun n := t ^ n.toAdd
  map_one' := zpow_zero t
  map_mul' n m := zpow_add t n.toAdd m.toAdd

def cyclicKernelLift (q : G →* Multiplicative ℤ) (t : G) :
    (q.ker ⋊[integerPowerAction (MulAut.conjNormal t)] Multiplicative ℤ) →* G :=
  SemidirectProduct.lift q.ker.subtype (cyclicPowerHom t) (by
    intro n
    ext x
    change (((MulAut.conjNormal t) ^ n.toAdd) x : G) =
      t ^ n.toAdd * (x : G) * (t ^ n.toAdd)⁻¹
    rw [← map_zpow]
    exact MulAut.conjNormal_apply _ _)

theorem cyclicKernelLift_apply (q : G →* Multiplicative ℤ) (t : G)
    (x : q.ker ⋊[integerPowerAction (MulAut.conjNormal t)] Multiplicative ℤ) :
    cyclicKernelLift q t x = (x.left : G) * t ^ x.right.toAdd := rfl

theorem cyclicKernelLift_height (q : G →* Multiplicative ℤ) (t : G)
    (ht : q t = Multiplicative.ofAdd 1)
    (x : q.ker ⋊[integerPowerAction (MulAut.conjNormal t)] Multiplicative ℤ) :
    q (cyclicKernelLift q t x) = x.right := by
  rw [cyclicKernelLift_apply, map_mul, x.left.property, one_mul, map_zpow, ht]
  apply Multiplicative.ext
  change x.right.toAdd • (1 : ℤ) = x.right.toAdd
  simp

def cyclicKernelEquiv (q : G →* Multiplicative ℤ) (t : G)
    (ht : q t = Multiplicative.ofAdd 1) :
    (q.ker ⋊[integerPowerAction (MulAut.conjNormal t)] Multiplicative ℤ) ≃* G :=
  MulEquiv.ofBijective (cyclicKernelLift q t) ⟨by
    intro x y h
    have hr : x.right = y.right := by
      rw [← cyclicKernelLift_height q t ht x, ← cyclicKernelLift_height q t ht y, h]
    apply SemidirectProduct.ext
    · apply Subtype.ext
      rw [cyclicKernelLift_apply, cyclicKernelLift_apply, hr] at h
      exact mul_right_cancel h
    · exact hr,
    by
      intro g
      let n := (q g).toAdd
      have hk : g * t ^ (-n) ∈ q.ker := by
        change q (g * t ^ (-n)) = 1
        rw [map_mul, map_zpow, ht]
        apply Multiplicative.ext
        change (q g).toAdd + (-n) • (1 : ℤ) = 0
        simp [n]
      refine ⟨⟨⟨g * t ^ (-n), hk⟩, q g⟩, ?_⟩
      rw [cyclicKernelLift_apply]
      change (g * t ^ (-n)) * t ^ n = g
      rw [zpow_neg, mul_assoc, inv_mul_cancel, mul_one]⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CyclicParameterBasis
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A basis with the added time coordinate last -/

noncomputable section
namespace PolycyclicRecognition
open Module
variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] {d : ℕ}

def cyclicCoordinateEquiv (b : Basis (Fin d) ℝ V) :
    (V × ℝ) ≃ₗ[ℝ] (Fin (d + 1) → ℝ) where
  toFun x := Fin.snoc (b.equivFun x.1) x.2
  invFun z := (b.equivFun.symm (fun i => z i.castSucc), z (Fin.last d))
  left_inv x := by
    simp only [Fin.snoc_castSucc, Fin.snoc_last, LinearEquiv.symm_apply_apply]
  right_inv z := by
    simp only [LinearEquiv.apply_symm_apply]
    exact Fin.snoc_init_self z
  map_add' x y := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.snoc_last, Prod.snd_add, Pi.add_apply]
    · simp only [Fin.snoc_castSucc, Prod.fst_add, map_add, Pi.add_apply]
  map_smul' r x := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.snoc_last, RingHom.id_apply, Prod.smul_snd, Pi.smul_apply]
    · simp only [Fin.snoc_castSucc, RingHom.id_apply, Prod.smul_fst, map_smul, Pi.smul_apply]

def cyclicParameterBasis (b : Basis (Fin d) ℝ V) (s : W ≃ₗ[ℝ] (V × ℝ)) :
    Basis (Fin (d + 1)) ℝ W :=
  Basis.ofEquivFun (s.trans (cyclicCoordinateEquiv b))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_DerivationEigenvectors
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Products of eigenvectors of an associative derivation

Real eigenvectors span a subalgebra. Thus an algebra generated by such
vectors inherits a spanning family of real eigenvectors.
-/

noncomputable section
namespace PolycyclicRecognition

variable {A : Type*} [Ring A] [Algebra ℝ A]
  (D : Module.End ℝ A)

def derivationEigenvectorSpan : Submodule ℝ A := ⨆ r : ℝ, D.eigenspace r

theorem derivationEigenvectorSpan_mul
    (hmul : ∀ a b, D (a * b) = a * D b + D a * b)
    {a b : A} (ha : a ∈ derivationEigenvectorSpan D)
    (hb : b ∈ derivationEigenvectorSpan D) : a * b ∈ derivationEigenvectorSpan D := by
  apply Submodule.iSup_induction (fun r : ℝ => D.eigenspace r)
    (motive := fun a => a * b ∈ derivationEigenvectorSpan D) ha
  · intro r a har
    apply Submodule.iSup_induction (fun s : ℝ => D.eigenspace s)
      (motive := fun b => a * b ∈ derivationEigenvectorSpan D) hb
    · intro s b hbs
      apply Submodule.mem_iSup_of_mem (r + s)
      rw [Module.End.mem_eigenspace_iff] at har hbs ⊢
      rw [hmul, har, hbs]
      simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, add_smul, add_comm]
    · simpa only [mul_zero] using (derivationEigenvectorSpan D).zero_mem
    · intro b c hb hc
      rw [mul_add]
      exact (derivationEigenvectorSpan D).add_mem hb hc
  · simpa only [zero_mul] using (derivationEigenvectorSpan D).zero_mem
  · intro a c ha hc
    rw [add_mul]
    exact (derivationEigenvectorSpan D).add_mem ha hc

def derivationEigenvectorSubalgebra (hone : D 1 = 0)
    (hmul : ∀ a b, D (a * b) = a * D b + D a * b) : Subalgebra ℝ A where
  carrier := derivationEigenvectorSpan D
  mul_mem' := derivationEigenvectorSpan_mul D hmul
  add_mem' := (derivationEigenvectorSpan D).add_mem
  algebraMap_mem' r := by
    apply Submodule.mem_iSup_of_mem (0 : ℝ)
    rw [Module.End.mem_eigenspace_iff, Algebra.algebraMap_eq_smul_one,
      map_smul, hone, smul_zero, zero_smul]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_DynkinProductTails
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Convergence of products with summable logarithmic increments

Finite BCH gives a common bound on every tail product in terms of the
sum of its logarithmic increments. The global exponential chart then
gives convergence, without identifying its coordinate metric with a
left invariant metric.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieModule Filter Metric
open scoped BigOperators Manifold Topology

variable {E G J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G] [Fintype J]

/-- The ordered product of the first `m` exponential increments. -/
def exponentialPartialProduct
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G)
    (X : ℕ → GroupLieAlgebra (𝓘(ℝ, E)) G) (m : ℕ) : G :=
  (List.ofFn (fun i : Fin m => Exp (X i))).prod

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_EnvelopingDerivation
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Extending Lie derivations to the enveloping algebra

The square-zero extension constructs the associative Leibniz extension. This
will act on the finite truncated enveloping representation of the nilradical.
-/

noncomputable section
namespace PolycyclicRecognition

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "U" => UniversalEnvelopingAlgebra R L
local notation "η" => UniversalEnvelopingAlgebra.ι R (L := L)

/-- Induction on scalar elements and Lie generators. -/
@[elab_as_elim]
theorem enveloping_induction {P : U → Prop}
    (hscalar : ∀ r, P (algebraMap R U r)) (hgen : ∀ x, P (η x))
    (hadd : ∀ a b, P a → P b → P (a + b))
    (hmul : ∀ a b, P a → P b → P (a * b)) (u : U) : P u := by
  obtain ⟨v, rfl⟩ := RingCon.mkₐ_surjective (α := R)
    (UniversalEnvelopingAlgebra.ringCon R L) u
  induction v using TensorAlgebra.induction with
  | algebraMap r => exact hscalar r
  | ι x => exact hgen x
  | add a b ha hb => exact hadd _ _ ha hb
  | mul a b ha hb => exact hmul _ _ ha hb

def envelopingDerivationLift (D : LieDerivation R L L) :
    L →ₗ⁅R⁆ TrivSqZeroExt U U where
  toFun x := ⟨η x, η (D x)⟩
  map_add' x y := by
    apply TrivSqZeroExt.ext
    · change η (x + y) = η x + η y
      exact map_add _ _ _
    · change η (D (x + y)) = η (D x) + η (D y)
      simp only [map_add]
  map_smul' r x := by
    apply TrivSqZeroExt.ext
    · change η (r • x) = r • η x
      exact map_smul _ _ _
    · change η (D (r • x)) = r • η (D x)
      simp only [map_smul]
  map_lie' {x y} := by
    apply TrivSqZeroExt.ext
    · exact (η).map_lie x y
    · change η (D ⁅x, y⁆) = _
      rw [D.apply_lie_eq_sub, map_sub, (η).map_lie, (η).map_lie]
      change (η x * η (D y) - η (D y) * η x) -
        (η y * η (D x) - η (D x) * η y) =
        (η x * η (D y) + η (D x) * η y) -
        (η y * η (D x) + η (D y) * η x)
      abel

theorem envelopingDerivationLift_fst (D : LieDerivation R L L) :
    (TrivSqZeroExt.fstHom R U U).comp
      (UniversalEnvelopingAlgebra.lift R (envelopingDerivationLift D)) = AlgHom.id R U := by
  apply UniversalEnvelopingAlgebra.hom_ext
  ext x
  change (UniversalEnvelopingAlgebra.lift R (envelopingDerivationLift D) (η x)).fst = η x
  rw [UniversalEnvelopingAlgebra.lift_ι_apply]
  rfl

/-- The unique associative derivation extending the given Lie derivation. -/
def envelopingDerivation (D : LieDerivation R L L) : U →ₗ[R] U :=
  (TrivSqZeroExt.sndHom U U).restrictScalars R ∘ₗ
    (UniversalEnvelopingAlgebra.lift R (envelopingDerivationLift D)).toLinearMap

@[simp]
theorem envelopingDerivation_generator (D : LieDerivation R L L) (x : L) :
    envelopingDerivation D (η x) = η (D x) := by
  change TrivSqZeroExt.snd
    (UniversalEnvelopingAlgebra.lift R (envelopingDerivationLift D) (η x)) = _
  rw [UniversalEnvelopingAlgebra.lift_ι_apply]
  rfl

@[simp]
theorem envelopingDerivation_scalar (D : LieDerivation R L L) (r : R) :
    envelopingDerivation D (algebraMap R U r) = 0 := by
  change TrivSqZeroExt.snd
    (UniversalEnvelopingAlgebra.lift R (envelopingDerivationLift D) (algebraMap R U r)) = _
  rw [AlgHom.commutes]
  rfl

theorem envelopingDerivation_mul (D : LieDerivation R L L) (a b : U) :
    envelopingDerivation D (a * b) =
      a * envelopingDerivation D b + envelopingDerivation D a * b := by
  have hf (x : U) :
      (UniversalEnvelopingAlgebra.lift R (envelopingDerivationLift D) x).fst = x :=
    DFunLike.congr_fun (envelopingDerivationLift_fst D) x
  change TrivSqZeroExt.snd
    (UniversalEnvelopingAlgebra.lift R (envelopingDerivationLift D) (a * b)) = _
  rw [map_mul, TrivSqZeroExt.snd_mul, hf, hf]
  rfl

theorem enveloping_derivation_ext (f g : U →ₗ[R] U)
    (hf : ∀ r, f (algebraMap R U r) = 0)
    (hg : ∀ r, g (algebraMap R U r) = 0)
    (hfm : ∀ a b, f (a * b) = a * f b + f a * b)
    (hgm : ∀ a b, g (a * b) = a * g b + g a * b)
    (hgen : ∀ x, f (η x) = g (η x)) : f = g := by
  ext u
  induction u using enveloping_induction with
  | hscalar r => rw [hf, hg]
  | hgen x => exact hgen x
  | hadd a b ha hb => simp only [map_add, ha, hb]
  | hmul a b ha hb => rw [hfm, hgm, ha, hb]

theorem envelopingDerivation_add (D E : LieDerivation R L L) :
    envelopingDerivation (D + E) = envelopingDerivation D + envelopingDerivation E := by
  apply enveloping_derivation_ext
  · exact envelopingDerivation_scalar _
  · intro r
    simp only [LinearMap.add_apply, envelopingDerivation_scalar, add_zero]
  · exact envelopingDerivation_mul _
  · intro a b
    simp only [LinearMap.add_apply, envelopingDerivation_mul]
    noncomm_ring
  · intro x
    simp only [envelopingDerivation_generator, LinearMap.add_apply,
      LieDerivation.add_apply, map_add]

theorem envelopingDerivation_smul (r : R) (D : LieDerivation R L L) :
    envelopingDerivation (r • D) = r • envelopingDerivation D := by
  apply enveloping_derivation_ext
  · exact envelopingDerivation_scalar _
  · intro t
    simp only [LinearMap.smul_apply, envelopingDerivation_scalar, smul_zero]
  · exact envelopingDerivation_mul _
  · intro a b
    simp only [LinearMap.smul_apply, envelopingDerivation_mul, smul_add,
      Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
  · intro x
    simp only [envelopingDerivation_generator, LinearMap.smul_apply,
      LieDerivation.smul_apply, map_smul]

theorem envelopingDerivation_lie (D E : LieDerivation R L L) :
    envelopingDerivation ⁅D, E⁆ = ⁅envelopingDerivation D, envelopingDerivation E⁆ := by
  apply enveloping_derivation_ext
  · exact envelopingDerivation_scalar _
  · intro r
    simp only [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply,
      envelopingDerivation_scalar, map_zero, sub_zero]
  · exact envelopingDerivation_mul _
  · intro a b
    simp only [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply,
      envelopingDerivation_mul, map_add]
    noncomm_ring
  · intro x
    simp only [envelopingDerivation_generator, Ring.lie_def, LinearMap.sub_apply,
      Module.End.mul_apply, LieDerivation.lie_apply, map_sub]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ExhaustiveCharacter
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Gluing compatible integral characters over an exhaustive subgroup chain -/

noncomputable section
namespace PolycyclicRecognition

attribute [local instance] Classical.propDecidable

variable {G : Type} [Group G] (S : ℕ → Subgroup G)
  (hS : Monotone S) (hcover : ∀ g, ∃ n, g ∈ S n) (χ : ∀ n, S n →* ℤ)
  (hχ : ∀ i j (hij : i ≤ j) (g : S i), χ j (Subgroup.inclusion (hS hij) g) = χ i g)

def exhaustiveCharacterValue (g : G) : ℤ :=
  χ (Nat.find (hcover g)) ⟨g, Nat.find_spec (hcover g)⟩

include hS hχ in
theorem exhaustiveCharacterValue_eq (g : G) (n : ℕ) (hg : g ∈ S n) :
    exhaustiveCharacterValue S hcover χ g = χ n ⟨g, hg⟩ := by
  let i := Nat.find (hcover g)
  have hi : g ∈ S i := Nat.find_spec (hcover g)
  have h₁ := hχ i (max i n) (le_max_left _ _) ⟨g, hi⟩
  have h₂ := hχ n (max i n) (le_max_right _ _) ⟨g, hg⟩
  exact h₁.symm.trans h₂

def exhaustiveCharacter : G →* ℤ where
  toFun := exhaustiveCharacterValue S hcover χ
  map_one' := by
    rw [exhaustiveCharacterValue_eq S hS hcover χ hχ 1 0 (S 0).one_mem]
    exact (χ 0).map_one
  map_mul' g h := by
    let i := Nat.find (hcover g)
    let j := Nat.find (hcover h)
    let n := max i j
    have hg : g ∈ S n := hS (le_max_left i j) (Nat.find_spec (hcover g))
    have hh : h ∈ S n := hS (le_max_right i j) (Nat.find_spec (hcover h))
    rw [exhaustiveCharacterValue_eq S hS hcover χ hχ (g * h) n ((S n).mul_mem hg hh),
      exhaustiveCharacterValue_eq S hS hcover χ hχ g n hg,
      exhaustiveCharacterValue_eq S hS hcover χ hχ h n hh]
    exact (χ n).map_mul ⟨g, hg⟩ ⟨h, hh⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_QuotientGroupAction
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Descending automorphisms through an actual surjective group map -/

noncomputable section
namespace PolycyclicRecognition

variable {N Q D : Type*} [Group N] [Group Q] [Group D]

/-- A kernel-preserving automorphism descends using any section of the
surjective quotient map. Its value on a projected point is independent of
the choice of section. -/
def descendQuotientAutomorphism (π : N →* Q) (s : Q → N)
    (hs : Function.RightInverse s π) (e : N ≃* N)
    (he : ∀ n, e n ∈ π.ker ↔ n ∈ π.ker) : Q ≃* Q := by
  let f : Q →* Q := π.liftOfRightInverse s hs
    ⟨π.comp e.toMonoidHom, fun n hn => (he n).mpr hn⟩
  let g : Q →* Q := π.liftOfRightInverse s hs
    ⟨π.comp e.symm.toMonoidHom, fun n hn => by
      have h := (he (e.symm n)).mp
      exact h (by simpa using hn)⟩
  have hf (n) : f (π n) = π (e n) := π.liftOfRightInverse_comp_apply s hs _ n
  have hg (n) : g (π n) = π (e.symm n) := π.liftOfRightInverse_comp_apply s hs _ n
  exact
    { f with
      invFun := g
      left_inv := fun q => by
        obtain ⟨n, rfl⟩ := hs.surjective q
        change g (f (π n)) = π n
        rw [hf, hg, e.symm_apply_apply]
      right_inv := fun q => by
        obtain ⟨n, rfl⟩ := hs.surjective q
        change f (g (π n)) = π n
        rw [hg, hf, e.apply_symm_apply] }

@[simp] theorem descendQuotientAutomorphism_project
    (π : N →* Q) (s : Q → N) (hs : Function.RightInverse s π) (e : N ≃* N)
    (he : ∀ n, e n ∈ π.ker ↔ n ∈ π.ker) (n : N) :
    descendQuotientAutomorphism π s hs e he (π n) = π (e n) := by
  change π (e (s (π n))) = π (e n)
  exact π.liftOfRightInverseAux_comp_apply s hs (π.comp e.toMonoidHom)
    (fun x hx => (he x).mpr hx) n

/-- A group of automorphisms preserving the kernel acts on the quotient. -/
def descendQuotientAction (π : N →* Q) (s : Q → N)
    (hs : Function.RightInverse s π) (a : D →* MulAut N)
    (ha : ∀ d n, a d n ∈ π.ker ↔ n ∈ π.ker) : D →* MulAut Q where
  toFun d := descendQuotientAutomorphism π s hs (a d) (ha d)
  map_one' := by
    ext q
    obtain ⟨n, rfl⟩ := hs.surjective q
    simp only [descendQuotientAutomorphism_project, map_one, MulAut.one_apply]
  map_mul' d e := by
    ext q
    obtain ⟨n, rfl⟩ := hs.surjective q
    simp only [descendQuotientAutomorphism_project, map_mul, MulAut.mul_apply]

@[simp] theorem descendQuotientAction_project
    (π : N →* Q) (s : Q → N) (hs : Function.RightInverse s π) (a : D →* MulAut N)
    (ha : ∀ d n, a d n ∈ π.ker ↔ n ∈ π.ker) (d : D) (n : N) :
    descendQuotientAction π s hs a ha d (π n) = π (a d n) :=
  descendQuotientAutomorphism_project π s hs (a d) (ha d) n

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FactorQuotientAction
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The quotient action descends through overlapping group factors

The factors need not form a direct or injective semidirect decomposition.
The only overlap condition is that the nilpotent quotient kills it.
-/

noncomputable section
namespace PolycyclicRecognition

variable {N D Q G : Type*} [Group N] [Group D] [Group Q] [Group G]

/-- Translations and quotient automorphisms form the affine action of the
actual semidirect product. -/
def factorQuotientAction (π : N →* Q) (s : Q → N)
    (hs : Function.RightInverse s π) (a : D →* MulAut N)
    (ha : ∀ d n, a d n ∈ π.ker ↔ n ∈ π.ker) : (N ⋊[a] D) →* Equiv.Perm Q where
  toFun p := ((descendQuotientAction π s hs a ha p.right).toEquiv).trans
    (Equiv.mulLeft (π p.left))
  map_one' := by
    ext q
    change π 1 * descendQuotientAction π s hs a ha 1 q = q
    simp only [map_one, MulAut.one_apply, one_mul]
  map_mul' p r := by
    ext q
    change π (p.left * a p.right r.left) *
        descendQuotientAction π s hs a ha (p.right * r.right) q =
      π p.left * descendQuotientAction π s hs a ha p.right
        (π r.left * descendQuotientAction π s hs a ha r.right q)
    simp only [map_mul, MulAut.mul_apply, descendQuotientAction_project, mul_assoc]

@[simp] theorem factorQuotientAction_apply (π : N →* Q) (s : Q → N)
    (hs : Function.RightInverse s π) (a : D →* MulAut N)
    (ha : ∀ d n, a d n ∈ π.ker ↔ n ∈ π.ker) (p : N ⋊[a] D) (q : Q) :
    factorQuotientAction π s hs a ha p q =
      π p.left * descendQuotientAction π s hs a ha p.right q := rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FilteredNilpotentPerturbation
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Nilpotent perturbations along a finite filtration

An operator which agrees with a nilpotent operator on each successive
quotient is nilpotent. No commutation of the two operators is required.
-/

namespace PolycyclicRecognition
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem nilpotent_of_raises_finite_filtration
    (F : ℕ → Submodule ℝ V) (hzero : F 0 = ⊤) {c : ℕ} (hc : F c = ⊥)
    (a : Module.End ℝ V) (ha : ∀ k x, x ∈ F k → a x ∈ F (k + 1)) :
    IsNilpotent a := by
  have hp (k : ℕ) (x : V) : (a ^ k) x ∈ F k := by
    induction k with
    | zero => rw [hzero]; trivial
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply]
      exact ha k _ ih
  refine ⟨c, LinearMap.ext fun x => ?_⟩
  exact (Submodule.mem_bot ℝ).mp (hc ▸ hp c x)

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FiniteCutoffPartition
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The quantitative cutoff partition used by Lipschitz replacement -/

noncomputable section
namespace PolycyclicRecognition

open scoped BigOperators

variable {X I : Type*} [MetricSpace X] [Fintype I]

/-- Unnormalized radius-two distance cutoffs in the sum norm. -/
def cutoffMass (v : I → X) (x : X) : PiLp 1 (fun _ : I => ℝ) :=
  WithLp.toLp 1 (fun i => max 0 (2 - dist x (v i)))

def cutoffPartition (v : I → X) (x : X) : PiLp 1 (fun _ : I => ℝ) :=
  ‖cutoffMass v x‖⁻¹ • cutoffMass v x

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanWordLogarithms
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cartan logarithms of bounded words

The Cartan group is nilpotent. The finite Dynkin identity therefore gives a
polynomial bound on the logarithm of every prefix of a bounded word. We also
record the exact semidirect-product word formula used to apply the controlled
Cartan estimates to such prefixes.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieModule
open scoped Manifold

set_option maxHeartbeats 1000000 in
/-- Ordered product of the first `m` letters of a word. -/
def wordPrefix {G : Type*} [Monoid G] (u : ℕ → G) (m : ℕ) : G :=
  (List.ofFn (fun i : Fin m => u i.val)).prod

set_option maxHeartbeats 1000000 in
@[simp] theorem wordPrefix_zero {G : Type*} [Monoid G] (u : ℕ → G) :
    wordPrefix u 0 = 1 := rfl

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]
  {ED D : Type*} [NormedAddCommGroup ED] [NormedSpace ℝ ED]
  [FiniteDimensional ℝ ED] [TopologicalSpace D] [ChartedSpace ED D] [Group D]
  [LieGroup (𝓘(ℝ, ED)) ⊤ D] [T2Space D]
  (eD : H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, ED)) D)
  (ExpD : GroupLieAlgebra (𝓘(ℝ, ED)) D → D) (hbijD : Function.Bijective ExpD)

set_option maxHeartbeats 1000000 in
/-- The Cartan logarithm in the actual nilpotent exponential coordinates. -/
def cartanLog (d : D) : H := eD.symm ((Equiv.ofBijective ExpD hbijD).symm d)

set_option maxHeartbeats 1000000 in
omit [FiniteDimensional ℝ L] [H.IsCartanSubalgebra] [T2Space D] in
@[simp] theorem cartanLog_exp (h : H) : cartanLog H eD ExpD hbijD (ExpD (eD h)) = h := by
  unfold cartanLog
  change eD.symm ((Equiv.ofBijective ExpD hbijD).symm
    ((Equiv.ofBijective ExpD hbijD) (eD h))) = h
  rw [Equiv.symm_apply_apply, eD.symm_apply_apply]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_WordExtension
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Extending controlled words by one increment -/

namespace PolycyclicRecognition

/-- Append a prescribed increment, with irrelevant later increments fixed to it. -/
def extendWord {A : Type*} (u : ℕ → A) (m : ℕ) (a : A) : ℕ → A :=
  fun i => if i < m then u i else a

@[simp] theorem extendWord_before {A : Type*} (u : ℕ → A) (m : ℕ) (a : A)
    {i : ℕ} (hi : i < m) : extendWord u m a i = u i := by simp [extendWord, hi]

@[simp] theorem extendWord_at {A : Type*} (u : ℕ → A) (m : ℕ) (a : A) :
    extendWord u m a m = a := by simp [extendWord]

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_SemidirectPrefixTuples
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact accumulated lifts of a finite tuple of transitions -/

noncomputable section
namespace PolycyclicRecognition

/-- The tuple positions with the identity adjoined at time zero. -/
def basedTuplePosition {G : Type*} [One G] {h : ℕ} (x : Fin h → G) (j : ℕ) : G :=
  if j = 0 then 1 else if hi : j - 1 < h then x ⟨j - 1, hi⟩ else 1

@[simp] theorem basedTuplePosition_zero {G : Type*} [One G] {h : ℕ} (x : Fin h → G) :
    basedTuplePosition x 0 = 1 := by simp [basedTuplePosition]

@[simp] theorem basedTuplePosition_succ {G : Type*} [One G] {h : ℕ}
    (x : Fin h → G) (i : Fin h) : basedTuplePosition x (i.val + 1) = x i := by
  simp [basedTuplePosition, i.isLt]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_GoodFiniteWordVertices
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual good vertices of a successful finite block -/

noncomputable section
namespace PolycyclicRecognition

variable {G : Type*} [Group G]

def finiteWordVertex {m : ℕ} (x : G) (u : Fin m → G) (j : Fin (m + 1)) : G :=
  x * ((List.ofFn u).take j.val).prod

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ChainSuccessor
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The successor shift of a nonnegative chain complex -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits HomologicalComplex

variable {k : Type} [CommRing k]

def negativeChainComplex (C : ChainComplex (ModuleCat k) ℕ) :
    ChainComplex (ModuleCat k) ℕ where
  X := C.X
  d i j := -C.d i j
  shape i j hij := by rw [C.shape i j hij, neg_zero]
  d_comp_d' i j l _ _ := by simp only [Preadditive.neg_comp, Preadditive.comp_neg,
    neg_neg, C.d_comp_d]

def chainModuleNegIdentityIso (M : ModuleCat k) : M ≅ M where
  hom := -𝟙 M
  inv := -𝟙 M
  hom_inv_id := by simp
  inv_hom_id := by simp

def negativeChainShortComplexIso (C : ChainComplex (ModuleCat k) ℕ) (i : ℕ) :
    (negativeChainComplex C).sc i ≅ C.sc i :=
  ShortComplex.isoMk
    (S₁ := (negativeChainComplex C).sc i) (S₂ := C.sc i)
    (chainModuleNegIdentityIso _) (Iso.refl _) (chainModuleNegIdentityIso _)
    (by change (-𝟙 _) ≫ C.d _ _ = (-C.d _ _) ≫ 𝟙 _; simp)
    (by change 𝟙 _ ≫ C.d _ _ = (-C.d _ _) ≫ (-𝟙 _); simp)

def negativeChainHomologyIso (C : ChainComplex (ModuleCat k) ℕ) (i : ℕ) :
    (negativeChainComplex C).homology i ≅ C.homology i :=
  ShortComplex.homologyMapIso (negativeChainShortComplexIso C i)

def chainSuccessorEmbedding : (ComplexShape.down ℕ).Embedding (ComplexShape.down ℕ) where
  f n := n + 1
  injective_f := fun _ _ h => Nat.add_right_cancel h
  rel h := by simpa only [ComplexShape.down_Rel] using congrArg (fun n : ℕ => n + 1) h

def chainSuccessor (C : ChainComplex (ModuleCat k) ℕ) :
    ChainComplex (ModuleCat k) ℕ :=
  (negativeChainComplex C).extend chainSuccessorEmbedding

def chainSuccessorXIso (C : ChainComplex (ModuleCat k) ℕ) (i : ℕ) :
    (chainSuccessor C).X (i + 1) ≅ C.X i :=
  (negativeChainComplex C).extendXIso chainSuccessorEmbedding rfl

def chainSuccessorHomologyIso (C : ChainComplex (ModuleCat k) ℕ) (i : ℕ) :
    (chainSuccessor C).homology (i + 1) ≅ C.homology i :=
  (negativeChainComplex C).extendHomologyIso chainSuccessorEmbedding rfl ≪≫
    negativeChainHomologyIso C i

theorem chainSuccessor_zero (C : ChainComplex (ModuleCat k) ℕ) :
    IsZero ((chainSuccessor C).X 0) :=
  (negativeChainComplex C).isZero_extend_X chainSuccessorEmbedding 0 (by
    intro i
    simp [chainSuccessorEmbedding])

theorem chainSuccessor_d (C : ChainComplex (ModuleCat k) ℕ) (i : ℕ) :
    (chainSuccessor C).d (i + 2) (i + 1) =
      (chainSuccessorXIso C (i + 1)).hom ≫ (-C.d (i + 1) i) ≫
        (chainSuccessorXIso C i).inv :=
  (negativeChainComplex C).extend_d_eq chainSuccessorEmbedding rfl rfl

def chainSuccessorCyclesIso (C : ChainComplex (ModuleCat k) ℕ) (i : ℕ) :
    (chainSuccessor C).cycles (i + 1) ≅ C.cycles i :=
  (negativeChainComplex C).extendCyclesIso chainSuccessorEmbedding rfl ≪≫
    ShortComplex.cyclesMapIso (negativeChainShortComplexIso C i)

theorem chainSuccessorCyclesIso_iCycles (C : ChainComplex (ModuleCat k) ℕ) (i : ℕ) :
    (chainSuccessorCyclesIso C i).hom ≫ C.iCycles i =
      (chainSuccessor C).iCycles (i + 1) ≫ (chainSuccessorXIso C i).hom := by
  change (_ ≫ ShortComplex.cyclesMap (negativeChainShortComplexIso C i).hom) ≫ _ = _
  erw [Category.assoc]
  have hn : ShortComplex.cyclesMap (negativeChainShortComplexIso C i).hom ≫
      C.iCycles i = (negativeChainComplex C).iCycles i := by
    exact (ShortComplex.cyclesMap_i (negativeChainShortComplexIso C i).hom).trans
      (Category.comp_id _)
  calc
    _ = ((negativeChainComplex C).extendCyclesIso chainSuccessorEmbedding rfl).hom ≫
        (negativeChainComplex C).iCycles i := congrArg _ hn
    _ = _ := (negativeChainComplex C).extendCyclesIso_hom_iCycles chainSuccessorEmbedding rfl

theorem chainSuccessorHomologyIso_π (C : ChainComplex (ModuleCat k) ℕ) (i : ℕ) :
    (chainSuccessor C).homologyπ (i + 1) ≫ (chainSuccessorHomologyIso C i).hom =
      (chainSuccessorCyclesIso C i).hom ≫ C.homologyπ i := by
  have he := (negativeChainComplex C).homologyπ_extendHomologyIso_hom
    chainSuccessorEmbedding (j := i) rfl
  have hn : (negativeChainComplex C).homologyπ i ≫
      ShortComplex.homologyMap (negativeChainShortComplexIso C i).hom =
      ShortComplex.cyclesMap (negativeChainShortComplexIso C i).hom ≫ C.homologyπ i :=
    ShortComplex.homologyπ_naturality (negativeChainShortComplexIso C i).hom
  change _ ≫ (_ ≫ ShortComplex.homologyMap (negativeChainShortComplexIso C i).hom) = _
  erw [← Category.assoc]
  exact (congrArg (fun f => f ≫ ShortComplex.homologyMap
    (negativeChainShortComplexIso C i).hom) he).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun f =>
          ((negativeChainComplex C).extendCyclesIso chainSuccessorEmbedding rfl).hom ≫ f)
          hn).trans (Category.assoc _ _ _).symm))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CofiberChainSequence
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The split-in-each-degree sequence of a chain mapping cone -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {P Q : ChainComplex (ModuleCat ℤ) ℕ} (φ : P ⟶ Q)

theorem chainDownSuccessorRel (i : ℕ) : (ComplexShape.down ℕ).Rel (i + 1) i := rfl

def cofiberChainProjectionComponent : ∀ i,
    (homotopyCofiber φ).X i ⟶ (chainSuccessor P).X i
  | 0 => 0
  | n + 1 => homotopyCofiber.fstX φ (n + 1) n (chainDownSuccessorRel n) ≫ (chainSuccessorXIso P n).inv

def cofiberChainProjection : homotopyCofiber φ ⟶ chainSuccessor P where
  f := cofiberChainProjectionComponent φ
  comm' i j hij := by
    obtain rfl : j + 1 = i := hij
    cases j with
    | zero => exact (chainSuccessor_zero P).eq_of_tgt _ _
    | succ j =>
      change (homotopyCofiber.fstX φ (j + 2) (j + 1) (chainDownSuccessorRel (j + 1)) ≫
        (chainSuccessorXIso P (j + 1)).inv) ≫ _ =
          (homotopyCofiber φ).d (j + 2) (j + 1) ≫
            (homotopyCofiber.fstX φ (j + 1) j (chainDownSuccessorRel j) ≫ (chainSuccessorXIso P j).inv)
      rw [chainSuccessor_d]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      have hd := homotopyCofiber.d_fstX φ (j + 2) (j + 1) j (chainDownSuccessorRel (j + 1)) (chainDownSuccessorRel j)
      change (homotopyCofiber φ).d (j + 2) (j + 1) ≫
        homotopyCofiber.fstX φ (j + 1) j (chainDownSuccessorRel j) = _ at hd
      rw [← Category.assoc ((homotopyCofiber φ).d _ _), hd]
      simp only [Preadditive.comp_neg, Preadditive.neg_comp, Category.assoc]

theorem cofiberChain_inclusion_projection :
    homotopyCofiber.inr φ ≫ cofiberChainProjection φ = 0 := by
  apply HomologicalComplex.Hom.ext
  funext i
  cases i with
  | zero => exact comp_zero
  | succ i =>
    change homotopyCofiber.inrX φ (i + 1) ≫
      (homotopyCofiber.fstX φ (i + 1) i (chainDownSuccessorRel i) ≫ (chainSuccessorXIso P i).inv) = 0
    simp

abbrev cofiberChainSequence : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
  ShortComplex.mk (homotopyCofiber.inr φ) (cofiberChainProjection φ)
    (cofiberChain_inclusion_projection φ)

def cofiberChainDegreeSplitting (i : ℕ) :
    ((HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) i).mapShortComplex.obj
      (cofiberChainSequence φ)).Splitting where
  r := homotopyCofiber.sndX φ i
  s := match i with
    | 0 => 0
    | n + 1 => (chainSuccessorXIso P n).hom ≫ homotopyCofiber.inlX φ n (n + 1) (chainDownSuccessorRel n)
  f_r := homotopyCofiber.inrX_sndX φ i
  s_g := by
    cases i with
    | zero => exact (chainSuccessor_zero P).eq_of_src _ _
    | succ i =>
      change ((chainSuccessorXIso P i).hom ≫ homotopyCofiber.inlX φ i (i + 1) (chainDownSuccessorRel i)) ≫
        (homotopyCofiber.fstX φ (i + 1) i (chainDownSuccessorRel i) ≫ (chainSuccessorXIso P i).inv) = 𝟙 _
      simp
  id := by
    cases i with
    | zero =>
      change homotopyCofiber.sndX φ 0 ≫ homotopyCofiber.inrX φ 0 +
        (0 : homotopyCofiber.X φ 0 ⟶ homotopyCofiber.X φ 0) = 𝟙 _
      rw [homotopyCofiber.sndX_inrX φ 0 (by simp)]
      simp
    | succ i =>
      change homotopyCofiber.sndX φ (i + 1) ≫ homotopyCofiber.inrX φ (i + 1) +
        (homotopyCofiber.fstX φ (i + 1) i (chainDownSuccessorRel i) ≫ (chainSuccessorXIso P i).inv) ≫
          ((chainSuccessorXIso P i).hom ≫ homotopyCofiber.inlX φ i (i + 1) (chainDownSuccessorRel i)) = 𝟙 _
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      apply homotopyCofiber.ext_from_X φ i (i + 1) (chainDownSuccessorRel i)
      · simp
      · simp

theorem cofiberChainSequence_shortExact : (cofiberChainSequence φ).ShortExact := by
  apply shortExact_of_degreewise_shortExact
  intro i
  exact (cofiberChainDegreeSplitting φ i).shortExact

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CofiberChainConnecting
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The connecting map of the chain mapping-cone sequence -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits HomologicalComplex

theorem chainSuccessor_liftCycles_homology
    (C : ChainComplex (ModuleCat ℤ) ℕ) (i : ℕ) {M : ModuleCat ℤ}
    (x : M ⟶ C.X i) (hx : x ≫ C.d i (i - 1) = 0)
    (hs : (x ≫ (chainSuccessorXIso C i).inv) ≫
      (chainSuccessor C).d (i + 1) i = 0) :
    (chainSuccessor C).liftCycles (x ≫ (chainSuccessorXIso C i).inv) i (by simp) hs ≫
        (chainSuccessor C).homologyπ (i + 1) ≫ (chainSuccessorHomologyIso C i).hom =
      C.liftCycles x (i - 1) (by cases i <;> simp) hx ≫ C.homologyπ i := by
  rw [chainSuccessorHomologyIso_π, ← Category.assoc]
  congr 1
  apply (cancel_mono (C.iCycles i)).mp
  rw [Category.assoc, chainSuccessorCyclesIso_iCycles, ← Category.assoc,
    liftCycles_i, Category.assoc, Iso.inv_hom_id, Category.comp_id, liftCycles_i]

variable {P Q : ChainComplex (ModuleCat ℤ) ℕ} (φ : P ⟶ Q)

theorem cofiberChain_connecting (i : ℕ) :
    (chainSuccessorHomologyIso P i).inv ≫
        (cofiberChainSequence_shortExact φ).δ (i + 1) i (by simp) =
      HomologicalComplex.homologyMap φ i := by
  have hid : P.liftCycles (P.iCycles i) (i - 1) (by cases i <;> simp)
      (P.iCycles_d i (i - 1)) = 𝟙 _ := by
    have he : P.liftCycles (P.iCycles i) (i - 1) (by cases i <;> simp)
        (P.iCycles_d i (i - 1)) ≫ P.iCycles i = (𝟙 (P.cycles i)) ≫ P.iCycles i := by
      rw [liftCycles_i, Category.id_comp]
    exact (cancel_mono (P.iCycles i)).mp he
  let x₃ := P.iCycles i ≫ (chainSuccessorXIso P i).inv
  let x₂ := P.iCycles i ≫ homotopyCofiber.inlX φ i (i + 1) (by simp)
  let x₁ := P.iCycles i ≫ φ.f i
  have hx₃ : x₃ ≫ (chainSuccessor P).d (i + 1) i = 0 := by
    cases i with
    | zero => exact (chainSuccessor_zero P).eq_of_tgt _ _
    | succ i =>
      dsimp only [x₃]
      rw [chainSuccessor_d]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [← Category.assoc, Preadditive.comp_neg, P.iCycles_d, neg_zero, zero_comp]
  have hx₂ : x₂ ≫ (cofiberChainProjection φ).f (i + 1) = x₃ := by
    dsimp only [x₂, x₃, cofiberChainProjection, cofiberChainProjectionComponent]
    simp only [Category.assoc, homotopyCofiber.inlX_fstX_assoc]
  have hx₁ : x₁ ≫ (homotopyCofiber.inr φ).f i =
      x₂ ≫ (homotopyCofiber φ).d (i + 1) i := by
    dsimp only [x₁, x₂]
    change (P.iCycles i ≫ φ.f i) ≫ homotopyCofiber.inrX φ i =
      (P.iCycles i ≫ homotopyCofiber.inlX φ i (i + 1) (by simp)) ≫
        homotopyCofiber.d φ (i + 1) i
    cases i with
    | zero =>
      have hd := homotopyCofiber.inlX_d' φ 1 0 (by simp) (by simp)
      exact (congrArg (fun f => P.iCycles 0 ≫ f) hd).symm
    | succ i =>
      have hd := homotopyCofiber.inlX_d φ (i + 1 + 1) (i + 1) i (by simp) (by simp)
      have he := congrArg (fun f => P.iCycles (i + 1) ≫ f) hd
      simpa only [Preadditive.comp_add, Preadditive.comp_neg, ← Category.assoc,
        P.iCycles_d, neg_zero, zero_comp, zero_add, Nat.add_assoc] using he.symm
  have hx : x₁ ≫ Q.d i (i - 1) = 0 := by
    dsimp only [x₁]
    rw [Category.assoc, φ.comm i (i - 1), ← Category.assoc, P.iCycles_d, zero_comp]
  have hd := (cofiberChainSequence_shortExact φ).δ_eq (i + 1) i (by simp)
    x₃ hx₃ x₂ hx₂ x₁ hx₁ (i - 1) (by cases i <;> simp)
  have hs := chainSuccessor_liftCycles_homology P i (P.iCycles i)
    (P.iCycles_d i (i - 1)) hx₃
  rw [hid, Category.id_comp] at hs
  apply (cancel_epi (P.homologyπ i)).mp
  rw [← Category.assoc, ← hs]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [hd]
  have hs' := congrArg (fun f => f ≫ HomologicalComplex.homologyMap φ i) hs
  simp only [Category.assoc] at hs'
  rw [hs', HomologicalComplex.homologyπ_naturality φ i]
  congr 1

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_CofiberChainHomology
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Top homology of a chain mapping cone -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {P Q : ChainComplex (ModuleCat ℤ) ℕ} (φ : P ⟶ Q)

def cofiberChainHomologyKernelIso (i : ℕ) (hQ : IsZero (Q.homology (i + 1))) :
    (homotopyCofiber φ).homology (i + 1) ≅
      kernel (HomologicalComplex.homologyMap φ i) := by
  let S := cofiberChainSequence φ
  let hS := cofiberChainSequence_shortExact φ
  have hm : Mono (HomologicalComplex.homologyMap S.g (i + 1)) :=
    (hS.homology_exact₂ (i + 1)).mono_g (hQ.eq_of_src _ _)
  let := hm
  let e := kernel.mapIso (hS.δ (i + 1) i rfl)
    (HomologicalComplex.homologyMap φ i) (chainSuccessorHomologyIso P i) (Iso.refl _)
    (by
      rw [← cofiberChain_connecting φ i]
      simp only [Iso.refl_hom, Iso.hom_inv_id_assoc, Category.comp_id])
  exact (hS.homology_exact₃ (i + 1) i rfl).fIsKernel.conePointUniqueUpToIso
    (kernelIsKernel _) ≪≫ e

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_InducedResolutionHomology
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Tensoring an induced resolution

The projection formula, with the tensor factors in resolution order, identifies
an induced resolution with subgroup homology for restricted coefficients.
-/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
attribute [local instance 2200] TensorProduct.instModule
attribute [local instance 2300] Representation.Coinvariants.instModule
variable {G : Type} [Group G] (N : Subgroup G) (A : Rep ℤ G)

theorem coinvariantsBraiding_mk (B C : Rep ℤ G) (b : B) (c : C) :
    ((Rep.coinvariantsFunctor ℤ G).map (β_ B C).hom)
      (Rep.coinvariantsTensorMk B C b c) = Rep.coinvariantsTensorMk C B c b := rfl

theorem coinvariantsTensorMap_mk {B C : Rep ℤ G} (f : B ⟶ C)
    (a : A) (b : B) :
    (((Rep.coinvariantsTensor ℤ G).obj A).map f)
      (Rep.coinvariantsTensorMk A B a b) = Rep.coinvariantsTensorMk A C a (f.hom b) := rfl

def inducedTensorRightIso (B : Rep ℤ N) :
    ((Rep.coinvariantsTensor ℤ G).obj A).obj (Rep.ind N.subtype B) ≅
      ((Rep.coinvariantsTensor ℤ N).obj (Rep.res N.subtype A)).obj B :=
  (Rep.coinvariantsFunctor ℤ G).mapIso (β_ A (Rep.ind N.subtype B)) ≪≫
    Rep.coinvariantsTensorIndIso N.subtype B A ≪≫
      (Rep.coinvariantsFunctor ℤ N).mapIso (β_ B (Rep.res N.subtype A))

@[simp] theorem inducedTensorRightIso_mk (B : Rep ℤ N) (a : A) (g : G) (b : B) :
    (inducedTensorRightIso N A B).hom
      (Rep.coinvariantsTensorMk A (Rep.ind N.subtype B) a
        (Representation.IndV.mk N.subtype B.ρ g b)) =
      Rep.coinvariantsTensorMk (Rep.res N.subtype A) B (A.ρ g a) b := by
  change ((Rep.coinvariantsFunctor ℤ N).map (β_ B (Rep.res N.subtype A)).hom)
    (Rep.coinvariantsTensorIndHom N.subtype B A
      (((Rep.coinvariantsFunctor ℤ G).map (β_ A (Rep.ind N.subtype B)).hom)
        (Rep.coinvariantsTensorMk A (Rep.ind N.subtype B) a
          (Representation.IndV.mk N.subtype B.ρ g b)))) = _
  rw [coinvariantsBraiding_mk, Rep.coinvariantsTensorIndHom_mk_tmul_indVMk,
    coinvariantsBraiding_mk]

def inducedTensorRightNatIso :
    Rep.indFunctor ℤ N.subtype ⋙ (Rep.coinvariantsTensor ℤ G).obj A ≅
      (Rep.coinvariantsTensor ℤ N).obj (Rep.res N.subtype A) :=
  NatIso.ofComponents (inducedTensorRightIso N A) (by
    intro B C f
    apply Rep.coinvariantsTensor_hom_ext
    apply DFunLike.ext
    intro a
    apply Representation.IndV.hom_ext
    intro g
    apply DFunLike.ext
    intro b
    change (inducedTensorRightIso N A C).hom
      ((((Rep.coinvariantsTensor ℤ G).obj A).map (Rep.indMap N.subtype f))
        (Rep.coinvariantsTensorMk A (Rep.ind N.subtype B) a
          (Representation.IndV.mk N.subtype B.ρ g b))) =
      (((Rep.coinvariantsTensor ℤ N).obj (Rep.res N.subtype A)).map f)
        ((inducedTensorRightIso N A B).hom
          (Rep.coinvariantsTensorMk A (Rep.ind N.subtype B) a
            (Representation.IndV.mk N.subtype B.ρ g b)))
    rw [coinvariantsTensorMap_mk, normalInductionMap_mk, inducedTensorRightIso_mk,
      inducedTensorRightIso_mk, coinvariantsTensorMap_mk])

section Normal
variable [N.Normal]

def inducedResolutionTensorIso
    (P : ProjectiveResolution (Rep.trivial ℤ N ℤ)) :
    (normalInducedResolution ℤ N P).complex.coinvariantsTensorObj A ≅
      P.complex.coinvariantsTensorObj (Rep.res N.subtype A) :=
  (NatIso.mapHomologicalComplex (inducedTensorRightNatIso N A) (ComplexShape.down ℕ)).app
    P.complex

def inducedResolutionHomologyIso
    (P : ProjectiveResolution (Rep.trivial ℤ N ℤ)) (i : ℕ) :
    ((normalInducedResolution ℤ N P).complex.coinvariantsTensorObj A).homology i ≅
      groupHomology (Rep.res N.subtype A) i := by
  classical
  exact (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) i).mapIso
    (inducedResolutionTensorIso N A P) ≪≫
      (groupHomologyIso (Rep.res N.subtype A) i P).symm

end Normal

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_InducedBarTranslation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option backward.isDefEq.respectTransparency false

namespace OAI

/-! # An explicit bar lift of translation in an infinite cyclic extension -/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G] (N : Subgroup G) [N.Normal] (t : G)

local instance instCommGroupQuotientSubgroupOfIsCyclic_solutions [IsCyclic (G ⧸ N)] : CommGroup (G ⧸ N) := IsCyclic.commGroup

def inducedBarTranslation :
    (normalInducedResolution ℤ N (Rep.barResolution ℤ N)).complex ⟶
      (normalInducedResolution ℤ N (Rep.barResolution ℤ N)).complex where
  f i := inducedSemilinearMap ℤ N t (Rep.free ℤ N (Fin i → N))
    (Rep.free ℤ N (Fin i → N))
    (barAutomorphismFreeMap (MulAut.conjNormal (H := N) t⁻¹) i)
  comm' i j _ := by
    change inducedSemilinearMap ℤ N t _ _
        ((barAutomorphismMap (MulAut.conjNormal (H := N) t⁻¹)).f i) ≫
          Rep.indMap N.subtype ((Rep.barComplex ℤ N).d i j) =
      Rep.indMap N.subtype ((Rep.barComplex ℤ N).d i j) ≫
        inducedSemilinearMap ℤ N t _ _
          ((barAutomorphismMap (MulAut.conjNormal (H := N) t⁻¹)).f j)
    rw [semilinear_comp_inductionMap, inductionMap_comp_semilinear]
    congr 1
    exact (barAutomorphismMap (MulAut.conjNormal (H := N) t⁻¹)).comm i j

theorem inducedBarTranslation_augmentation :
    (inducedBarTranslation N t).f 0 ≫ Rep.indMap N.subtype ((Rep.barResolution ℤ N).π.f 0) =
      Rep.indMap N.subtype ((Rep.barResolution ℤ N).π.f 0) ≫ inducedTrivialTranslation ℤ N t := by
  let P := Rep.barResolution ℤ N
  let b := barAutomorphismFreeMap (MulAut.conjNormal (H := N) t⁻¹) 0
  let p : P.complex.X 0 ⟶ Rep.trivial ℤ N ℤ := P.π.f 0
  change inducedSemilinearMap ℤ N t (P.complex.X 0) (P.complex.X 0) b ≫
      Rep.indMap N.subtype p = Rep.indMap N.subtype p ≫
        inducedSemilinearMap ℤ N t (Rep.trivial ℤ N ℤ) (Rep.trivial ℤ N ℤ)
          (𝟙 (Rep.trivial ℤ N ℤ))
  rw [semilinear_comp_inductionMap ℤ N t (A := P.complex.X 0)
    (B := P.complex.X 0) (C := Rep.trivial ℤ N ℤ) b p]
  have hb : b ≫ Rep.resMap (MulAut.conjNormal (H := N) t⁻¹).toMonoidHom p = p :=
    barAutomorphismFreeMap_augmentation _
  erw [hb, inductionMap_comp_semilinear ℤ N t (A := P.complex.X 0)
    (B := Rep.trivial ℤ N ℤ) (C := Rep.trivial ℤ N ℤ) p (𝟙 _), Category.comp_id]

theorem inducedBarTranslation_quotient_augmentation [IsCyclic (G ⧸ N)] :
    ((inducedBarTranslation N t - 𝟙 _).f 0) ≫
        (quotientInducedResolution N (Rep.barResolution ℤ N)).π.f 0 =
      (quotientInducedResolution N (Rep.barResolution ℤ N)).π.f 0 ≫
        Rep.resMap (QuotientGroup.mk' N)
          (cyclicDifference (G ⧸ N) (QuotientGroup.mk' N t)) := by
  let P := Rep.barResolution ℤ N
  let I : (normalInducedResolution ℤ N P).complex.X 0 ⟶
      Rep.ind N.subtype (Rep.trivial ℤ N ℤ) := Rep.indMap N.subtype (P.π.f 0)
  let e := (inductionTrivialIso ℤ N).hom
  let B := inducedBarTranslation N t
  let T := inducedTranslation ℤ N t P
  have hT : B.f 0 ≫ I = T.f 0 ≫ I :=
    (inducedBarTranslation_augmentation N t).trans
      (inducedTranslation_augmentation_zero ℤ N t P).symm
  have heq : (B - 𝟙 _).f 0 ≫ (quotientInducedResolution N P).π.f 0 =
      (T - 𝟙 _).f 0 ≫ (quotientInducedResolution N P).π.f 0 := by
    change (B.f 0 - 𝟙 _) ≫ (I ≫ e) = (T.f 0 - 𝟙 _) ≫ (I ≫ e)
    simp only [Preadditive.sub_comp, Category.id_comp, ← Category.assoc, hT]
    exact congrArg (fun z => (T.f 0 ≫ I) ≫ e - z ≫ e) (Category.id_comp I).symm
  exact heq.trans (inducedDifference_augmentation N t P)

def integerExtensionBarHomotopy (q : G →* Multiplicative ℤ)
    [IsCyclic (G ⧸ q.ker)] :
    Homotopy (integerExtensionMap q t (Rep.barResolution ℤ q.ker))
      (inducedBarTranslation q.ker t - 𝟙 _) := by
  letI : CommGroup (G ⧸ q.ker) := IsCyclic.commGroup
  let R := quotientInducedResolution q.ker (Rep.barResolution ℤ q.ker)
  let f := Rep.resMap (QuotientGroup.mk' q.ker)
    (cyclicDifference (G ⧸ q.ker) (QuotientGroup.mk' q.ker t))
  let u : ProjectiveResolution.Hom R R f :=
    ⟨inducedBarTranslation q.ker t - 𝟙 _, inducedBarTranslation_quotient_augmentation q.ker t⟩
  exact ProjectiveResolution.liftHomotopy f _ _ (ProjectiveResolution.lift_commutes f R R)
    u.hom_comp_π

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_InvariantDisintegration
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conditional measures over an invariant measurable factor

Disintegrating the graph of an invariant measurable map gives a measurable
probability kernel with the original measure as barycenter. Uniqueness of
conditional kernels proves invariance of its components almost everywhere,
for each acting element. No ergodicity is assumed here.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal ProbabilityTheory

variable {G X Y : Type*} [Group G] [MeasurableSpace X] [MeasurableSpace Y]
  [MulAction G X] [MeasurableConstSMul G X] [StandardBorelSpace X] [Nonempty X]
  (μ : Measure X) [IsProbabilityMeasure μ] (f : X → Y) (hf : Measurable f)

/-- The graph measure, with the factor in the first coordinate. -/
def factorGraphMeasure (_hf : Measurable f) : Measure (Y × X) := μ.map (fun x => (f x, x))

include hf

instance factorGraphMeasure_probability : IsProbabilityMeasure (factorGraphMeasure μ f hf) := by
  unfold factorGraphMeasure
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

/-- The actual conditional probability kernel supplied by disintegration. -/
def factorConditionalKernel (hf : Measurable f) : Kernel Y X := (factorGraphMeasure μ f hf).condKernel

instance factorConditionalKernel_markov : IsMarkovKernel (factorConditionalKernel μ f hf) := by
  unfold factorConditionalKernel
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_LeftTangentTrivialization
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
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

def leftLogDerivative (g : G) : E →L[ℝ] E :=
  mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun h : G => g⁻¹ * h) g

theorem contMDiffAt_leftLogDerivative (g₀ : G) :
    ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, E →L[ℝ] E)) ∞
      (inTangentCoordinates (𝓘(ℝ, E)) (𝓘(ℝ, E)) id (fun _ : G => (1 : G))
        (fun g => leftLogDerivative (E := E) g) g₀) g₀ := by
  have hmul : ContMDiff ((𝓘(ℝ, E)).prod (𝓘(ℝ, E))) (𝓘(ℝ, E)) ∞
      (fun p : G × G => p.1⁻¹ * p.2) := contMDiff_fst.inv.mul contMDiff_snd
  have hd := (hmul (g₀, g₀)).mfderiv (fun g h : G => g⁻¹ * h) id
    contMDiffAt_id (m := ∞) (by simp)
  have heq : inTangentCoordinates (𝓘(ℝ, E)) (𝓘(ℝ, E)) id
      (fun g : G => g⁻¹ * g)
      (fun g => mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun h : G => g⁻¹ * h) g) g₀ =
      inTangentCoordinates (𝓘(ℝ, E)) (𝓘(ℝ, E)) id (fun _ : G => (1 : G))
        (fun g => leftLogDerivative (E := E) g) g₀ := by
    funext g
    let B : G → G → (E →L[ℝ] E) := fun y₀ y =>
      (trivializationAt E (TangentSpace (𝓘(ℝ, E))) y₀).continuousLinearMapAt ℝ y
    have hb : B (g₀⁻¹ * g₀) (g⁻¹ * g) = B 1 1 :=
      congrArg₂ B (inv_mul_cancel g₀) (inv_mul_cancel g)
    exact congrArg (fun b : E →L[ℝ] E => b.comp
      ((leftLogDerivative (E := E) g).comp
        ((trivializationAt E (TangentSpace (𝓘(ℝ, E))) g₀).symmL ℝ g))) hb
  have hd' : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, E →L[ℝ] E)) ∞
      (inTangentCoordinates (𝓘(ℝ, E)) (𝓘(ℝ, E)) id
        (fun g : G => g⁻¹ * g)
        (fun g => mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun h : G => g⁻¹ * h) g) g₀) g₀ := hd
  rw [heq] at hd'
  exact hd'

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_MaximalNilpotentCentralAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Detecting the maximal nilpotent normal subgroup by its central factors -/

namespace PolycyclicRecognition

open scoped commutatorElement
variable {G : Type} [Group G]

def ambientUpperCentralSeries (F : Subgroup G) (n : ℕ) : Subgroup G :=
  (Subgroup.upperCentralSeries F n).map F.subtype

instance ambientUpperCentralSeries_normal (F : Subgroup G) [F.Normal] (n : ℕ) :
    (ambientUpperCentralSeries F n).Normal := by
  dsimp [ambientUpperCentralSeries]
  infer_instance

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NormalEigencharacters
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite-index stabilizers of normal-subgroup eigenspaces

Conjugation permutes the common eigenvalue functions of a normal subgroup.
There are only finitely many nonzero common eigenspaces. Consequently every
one of them is invariant under a subgroup of finite index in the ambient
group. This separates the finite permutation from the linear action.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped IsMulCommutative

variable {G K V : Type*} [Group G] [Field K] [AddCommGroup V] [Module K V]
  (A : Subgroup G) [A.Normal]

def conjugateWeightPerm : G →* Equiv.Perm (A → K) where
  toFun g :=
    { toFun := fun χ a => χ (MulAut.conjNormal (H := A) g⁻¹ a)
      invFun := fun χ a => χ (MulAut.conjNormal (H := A) g a)
      left_inv := by
        intro χ
        funext a
        apply congrArg χ
        apply Subtype.ext
        simp only [MulAut.conjNormal_apply, inv_inv]
        group
      right_inv := by
        intro χ
        funext a
        apply congrArg χ
        apply Subtype.ext
        simp only [MulAut.conjNormal_apply, inv_inv]
        group }
  map_one' := by
    ext χ a
    simp only [inv_one, map_one]
    rfl
  map_mul' g h := by
    ext χ a
    change χ (MulAut.conjNormal (H := A) (g * h)⁻¹ a) =
      χ (MulAut.conjNormal (H := A) h⁻¹ (MulAut.conjNormal (H := A) g⁻¹ a))
    rw [mul_inv_rev, map_mul]
    rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PairCharts
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!+# The two product charts of the space of quasi-inverse pairs

Target normalization gives `G × X`; inverse normalization gives `X × G`,
where the latter copy of `X` represents inverse maps. Their transition is
an actual homeomorphism. This is the geometric coordinate change used for
the inverse-coupling measure, before any disintegration or fiber averaging.
-/

noncomputable section

open scoped NNReal

namespace PolycyclicRecognition

variable {G : Type*} [Group G] [MetricSpace G] [ProperSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G] {Λ : ℝ≥0}

def targetTranslatePair (z : G) (p : C(G, G) × C(G, G)) : C(G, G) × C(G, G) :=
  (⟨fun t => z * p.1 t, continuous_const.mul p.1.continuous⟩,
    ⟨fun t => p.2 (z⁻¹ * t), p.2.continuous.comp (continuous_const.mul continuous_id)⟩)

omit [IsIsometricSMul G G] in
theorem continuous_targetTranslatePair :
    Continuous (fun q : G × (C(G, G) × C(G, G)) => targetTranslatePair q.1 q.2) := by
  apply Continuous.prodMk
  · apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun q : (G × (C(G, G) × C(G, G))) × G =>
      q.1.1 * q.1.2.1 q.2)
    fun_prop
  · apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun q : (G × (C(G, G) × C(G, G))) × G =>
      q.1.2.2 (q.1.1⁻¹ * q.2))
    fun_prop

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolyZNormalExtension
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Extensions of groups with torsion-free cyclic series -/

noncomputable section
namespace PolycyclicRecognition

open ChromaticCyclic
variable {G : Type} [Group G]

def cyclicSeriesJoin {H K L : Subgroup G} {n m : ℕ}
    (c : CyclicSeries H K n) (d : CyclicSeries K L m) : CyclicSeries H L (n + m) where
  group i := if i ≤ n then c.group i else d.group (i - n)
  first := by simpa using c.first
  last := by
    by_cases hm : m = 0
    · subst m
      simpa only [Nat.add_zero, ite_true, if_true, le_refl] using c.last.trans d.first.symm |>.trans d.last
    · simpa only [ite_false, if_false, show ¬ n + m ≤ n by omega, Nat.add_sub_cancel_left] using d.last
  step i hi := by
    by_cases hn : i < n
    · simpa only [ite_true, if_true, show i ≤ n by omega, show i + 1 ≤ n by omega] using c.step i hn
    · by_cases he : i = n
      · subst i
        simpa only [ite_true, if_true, le_refl, ite_false, if_false, show ¬ n + 1 ≤ n by omega,
          Nat.add_sub_cancel_left, c.last, d.first] using d.step 0 (by omega)
      · simpa only [ite_false, if_false, show ¬ i ≤ n by omega, show ¬ i + 1 ≤ n by omega,
          show i + 1 - n = (i - n) + 1 by omega] using d.step (i - n) (by omega)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PullbackInnerProduct
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Pulling an inner product back through a linear equivalence -/

noncomputable section
namespace PolycyclicRecognition

open Bornology Set
open scoped ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

def pullbackInner (A : E →L[ℝ] F) : E →L[ℝ] E →L[ℝ] ℝ :=
  (innerSL ℝ : F →L[ℝ] F →L[ℝ] ℝ).bilinearComp A A

theorem contDiff_pullbackInner : ContDiff ℝ ∞ (pullbackInner (E := E) (F := F)) := by
  let B : F →L[ℝ] F →L[ℝ] ℝ := innerSL ℝ
  change ContDiff ℝ ∞ (fun A : E →L[ℝ] F => ((B.comp A).flip.comp A).flip)
  have h₁ : ContDiff ℝ ∞ (fun A : E →L[ℝ] F =>
      B.comp A) :=
    contDiff_const.clm_comp contDiff_id
  let flipEF : (E →L[ℝ] F →L[ℝ] ℝ) →L[ℝ] (F →L[ℝ] E →L[ℝ] ℝ) :=
    (ContinuousLinearMap.flipₗᵢ ℝ E F ℝ).toLinearIsometry.toContinuousLinearMap
  let flipEE : (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) :=
    (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toLinearIsometry.toContinuousLinearMap
  have hfEF : ContDiff ℝ ∞ flipEF :=
    ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞) (E := E →L[ℝ] F →L[ℝ] ℝ)
      (F := F →L[ℝ] E →L[ℝ] ℝ) flipEF
  have hfEE : ContDiff ℝ ∞ flipEE :=
    ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞) (E := E →L[ℝ] E →L[ℝ] ℝ)
      (F := E →L[ℝ] E →L[ℝ] ℝ) flipEE
  have h₂ : ContDiff ℝ ∞ (fun A : E →L[ℝ] F => (B.comp A).flip) :=
    hfEF.comp h₁
  have h₃ := h₂.clm_comp contDiff_id
  exact hfEE.comp h₃

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RegularCoefficientAction
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Inverse coefficient action in the regular-dual pairing -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G]

def regularCoefficientAction (A : Rep ℤ G) : ℤ[G] →ₗ[ℤ] (A →ₗ[ℤ] A) :=
  (Finsupp.linearCombination ℤ (fun g : G => A.ρ g⁻¹)).comp
    (MonoidAlgebra.coeffLinearEquiv ℤ).toLinearMap

@[simp] theorem regularCoefficientAction_single (A : Rep ℤ G) (g : G) (r : ℤ) :
    regularCoefficientAction A (MonoidAlgebra.single g r) = r • A.ρ g⁻¹ := by
  simp [regularCoefficientAction]

theorem regularCoefficientAction_rightTranslation (A : Rep ℤ G) (g : G) (q : ℤ[G]) :
    regularCoefficientAction A ((regularRightTranslation g).hom q) =
      A.ρ g ∘ₗ regularCoefficientAction A q := by
  induction q using MonoidAlgebra.induction_on with
  | of h =>
    rw [MonoidAlgebra.of_apply, regularRightTranslation_single]
    simp only [regularCoefficientAction_single, one_smul, mul_inv_rev, inv_inv,
      map_mul, Module.End.mul_eq_comp]
  | add x y hx hy => simp only [map_add, hx, hy, LinearMap.comp_add]
  | smul r x hx =>
    simp only [map_smul, hx]
    ext a
    change r • (A.ρ g (regularCoefficientAction A x a)) =
      A.ρ g (r • regularCoefficientAction A x a)
    exact (map_zsmul (A.ρ g) r (regularCoefficientAction A x a)).symm

theorem regularCoefficientAction_leftTranslation (A : Rep ℤ G) (g : G) (q : ℤ[G]) :
    regularCoefficientAction A ((Rep.leftRegular ℤ G).ρ g q) =
      regularCoefficientAction A q ∘ₗ A.ρ g⁻¹ := by
  induction q using MonoidAlgebra.induction_on with
  | of h =>
    simp only [MonoidAlgebra.of_apply, Representation.ofMulAction_single,
      smul_eq_mul, regularCoefficientAction_single, one_smul, mul_inv_rev,
      map_mul, Module.End.mul_eq_comp]
  | add x y hx hy => simp only [map_add, hx, hy, LinearMap.add_comp]
  | smul r x hx => simp only [map_smul, hx, LinearMap.smul_comp]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RegularDualFree
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The regular dual of a finite free group-ring module -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G]

def regularInversion : ℤ[G] ≃ₗ[ℤ] ℤ[G] :=
  MonoidAlgebra.mapDomainLinearEquiv ℤ ℤ (Equiv.inv G)

@[simp] theorem regularInversion_single (g : G) (r : ℤ) :
    regularInversion (MonoidAlgebra.single g r) = MonoidAlgebra.single g⁻¹ r :=
  MonoidAlgebra.mapDomainLinearEquiv_single (R := ℤ) (S := ℤ) (Equiv.inv G) r g

theorem regularInversion_rightTranslation (g : G) (q : ℤ[G]) :
    regularInversion ((regularRightTranslation g).hom q) =
      (Rep.leftRegular ℤ G).ρ g (regularInversion q) := by
  induction q using MonoidAlgebra.induction_on with
  | of h =>
    rw [MonoidAlgebra.of_apply, regularRightTranslation_single]
    simp only [regularInversion_single, Representation.ofMulAction_single,
      smul_eq_mul, mul_inv_rev, inv_inv]
  | add x y hx hy => simp only [map_add, hx, hy]
  | smul r x hx => simp only [map_smul, hx]

def regularDualFreeEquiv (ι : Type) [Finite ι] :
    (regularDual (Rep.free ℤ G ι)).V ≃ₗ[ℤ] (Rep.free ℤ G ι).V :=
  (Rep.freeLiftLEquiv ℤ G ι (Rep.leftRegular ℤ G)).trans
    ((LinearEquiv.piCongrRight fun _ : ι => regularInversion).trans
      (Finsupp.linearEquivFunOnFinite ℤ ℤ[G] ι).symm)

@[simp] theorem regularDualFreeEquiv_apply (ι : Type) [Finite ι]
    (f : (regularDual (Rep.free ℤ G ι)).V) (j : ι) :
    regularDualFreeEquiv ι f j =
      regularInversion (f.hom (Finsupp.single j (MonoidAlgebra.single 1 1))) := rfl

def regularDualFreeIso (ι : Type) [Finite ι] :
    regularDual (Rep.free ℤ G ι) ≅ Rep.free ℤ G ι :=
  Rep.mkIso (Representation.Equiv.mk (regularDualFreeEquiv ι) (by
    intro g
    apply LinearMap.ext
    intro f
    apply Finsupp.ext
    intro j
    change regularInversion ((regularRightTranslation g).hom
        (f.hom (Finsupp.single j (MonoidAlgebra.single 1 1)))) =
      (Rep.free ℤ G ι).ρ g (regularDualFreeEquiv ι f) j
    rw [regularInversion_rightTranslation]
    simp only [Representation.finsupp_apply, Finsupp.lsum_apply]
    rw [Finsupp.sum_apply]
    rw [Finsupp.sum_eq_single j]
    · simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, Finsupp.single_eq_same]
      rfl
    · intro k hk hkj
      exact Finsupp.single_eq_of_ne hkj.symm
    · intro hj
      simp only [map_zero, Finsupp.zero_apply]))

theorem regularDualFreeIso_inv_single (ι : Type) [Finite ι]
    (x : (Rep.free ℤ G ι).V) (j : ι) (g : G) (r : ℤ) :
    ((regularDualFreeIso ι).inv.hom x).hom
        (Finsupp.single j (MonoidAlgebra.single g r)) =
      r • (Rep.leftRegular ℤ G).ρ g (regularInversion (x j)) := by
  change Representation.freeLift (Rep.leftRegular ℤ G).ρ
      (fun i => regularInversion (x i)) (Finsupp.single j (MonoidAlgebra.single g r)) = _
  exact Representation.freeLift_single_single (Rep.leftRegular ℤ G).ρ j g r _

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RegularDualPairing
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.regularDualFreeEquiv_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Evaluation pairing with the regular dual

Inverse coefficient action makes evaluation equivariant in the regular-dual
argument and invariant under the diagonal action on the other two arguments.
It therefore descends to coinvariant tensor products.
-/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
open scoped MonoidAlgebra TensorProduct
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
attribute [local instance 2200] TensorProduct.instModule
variable {G : Type} [Group G]

abbrev integralModuleComm {M : Type} [AddCommGroup M]
    (h₁ h₂ : Module ℤ M) :
    @SMulCommClass ℤ ℤ M h₁.toSMul h₂.toSMul :=
  @SMulCommClass.mk ℤ ℤ M h₁.toSMul h₂.toSMul (by
    intro r s x
    exact (show h₁.smul r (h₂.smul s x) = h₂.smul s (h₁.smul r x) from by
      rw [int_smul_eq_zsmul h₁, int_smul_eq_zsmul h₂,
        int_smul_eq_zsmul h₂, int_smul_eq_zsmul h₁]
      rw [smul_smul, smul_smul, mul_comm]))

def integralLinearMapOfAddHom {M N : Type} [AddCommGroup M] [AddCommGroup N]
    [Module ℤ M] [Module ℤ N] (f : M →+ N) : M →ₗ[ℤ] N where
  __ := f
  map_smul' r x := map_intCast_smul f ℤ ℤ r x

def regularDualEvaluation (P A : Rep ℤ G) (a : A) (p : P) : regularDual P ⟶ A :=
  Rep.ofHom ⟨integralLinearMapOfAddHom {
    toFun := fun f => regularCoefficientAction A (f.hom p) a
    map_zero' := by simp
    map_add' f h := by simp [Rep.add_hom]
    }, by
      intro g
      apply LinearMap.ext
      intro f
      change regularCoefficientAction A ((regularRightTranslation g).hom (f.hom p)) a =
        A.ρ g (regularCoefficientAction A (f.hom p) a)
      rw [regularCoefficientAction_rightTranslation]
      rfl⟩

@[simp] theorem regularDualEvaluation_apply (P A : Rep ℤ G) (a : A) (p : P)
    (f : P ⟶ Rep.leftRegular ℤ G) :
    (regularDualEvaluation P A a p).hom f = regularCoefficientAction A (f.hom p) a := rfl

def regularDualPairingInP (P A : Rep ℤ G) (a : A) : P →ₗ[ℤ] (regularDual P ⟶ A) :=
  integralLinearMapOfAddHom {
    toFun := regularDualEvaluation P A a
    map_zero' := by
      apply Rep.hom_ext
      apply DFunLike.ext
      intro f
      change regularCoefficientAction A (f.hom 0) a = 0
      simp
    map_add' p q := by
      apply Rep.hom_ext
      apply DFunLike.ext
      intro f
      change regularCoefficientAction A (f.hom (p + q)) a =
        regularCoefficientAction A (f.hom p) a + regularCoefficientAction A (f.hom q) a
      simp only [map_add, LinearMap.add_apply]
    }

def regularDualPairing (P A : Rep ℤ G) :=
  let h : Module ℤ (regularDual P ⟶ A) := inferInstance
  letI : Module ℤ (P →ₗ[ℤ] (regularDual P ⟶ A)) :=
    @LinearMap.module ℤ ℤ ℤ P (regularDual P ⟶ A)
      _ _ _ _ _ h (RingHom.id ℤ) _ h (integralModuleComm h h)
  integralLinearMapOfAddHom (M := A) (N := P →ₗ[ℤ] (regularDual P ⟶ A)) ({
  toFun := regularDualPairingInP P A
  map_zero' := by
    apply LinearMap.ext
    intro p
    apply Rep.hom_ext
    apply DFunLike.ext
    intro f
    change regularCoefficientAction A (f.hom p) 0 = 0
    exact map_zero _
  map_add' := fun a b => by
    apply LinearMap.ext
    intro p
    apply Rep.hom_ext
    apply DFunLike.ext
    intro f
    change regularCoefficientAction A (f.hom p) (a + b) =
      regularCoefficientAction A (f.hom p) a + regularCoefficientAction A (f.hom p) b
    exact map_add _ _ _
  } : A →+ (P →ₗ[ℤ] (regularDual P ⟶ A)))

theorem regularDualEvaluation_diagonal (P A : Rep ℤ G) (g : G) (a : A) (p : P) :
    regularDualEvaluation P A (A.ρ g a) (P.ρ g p) = regularDualEvaluation P A a p := by
  apply Rep.hom_ext
  apply DFunLike.ext
  intro f
  change regularCoefficientAction A (f.hom (P.ρ g p)) (A.ρ g a) =
    regularCoefficientAction A (f.hom p) a
  rw [Rep.hom_comm_apply f, regularCoefficientAction_leftTranslation]
  simp only [LinearMap.comp_apply, ← Module.End.mul_apply, ← map_mul,
    inv_mul_cancel, map_one, Module.End.one_apply]

def regularTensorEvaluation (P A : Rep ℤ G) :
    A ⊗[ℤ] P →ₗ[ℤ] (regularDual P ⟶ A) :=
  TensorProduct.lift (regularDualPairing P A)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RegularFreeEvaluation
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Evaluation for finite free group-ring modules -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
open scoped MonoidAlgebra TensorProduct
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
attribute [local instance 2200] TensorProduct.instModule
attribute [local instance 2300] Representation.Coinvariants.instModule Pi.Function.module
variable {G : Type} [Group G]

theorem freeLiftLEquiv_symm_apply (ι : Type) (A : Rep ℤ G) (f : ι → A) :
    (Rep.freeLiftLEquiv ℤ G ι A).symm f = Rep.freeLift ℤ G A f := by
  with_unfolding_all rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RingTraceProjectivity
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A norm-one element makes a ring coefficient projective

For a finite group acting on a ring which is projective over the integers,
an element with trace one gives an equivariant lift by averaging. Unlike
rational averaging, no division by the group order is used.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {H R : Type} [Group H] [Fintype H] [Ring R] [MulSemiringAction H R]

abbrev ringActionRepresentation : Rep ℤ H :=
  Rep.of (Representation.ofDistribMulAction ℤ H R)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SpectralLogValue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Scalar values of a compatible spectral logarithm -/

noncomputable section
namespace PolycyclicRecognition
variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem eigenvalue_ne_zero_of_isUnit (S : Module.End ℂ V) (hS : IsUnit S)
    {μ : ℂ} (hμ : S.HasEigenvalue μ) : μ ≠ 0 := by
  intro hz
  exact spectrum.zero_notMem ℂ hS (hz ▸ hμ.mem_spectrum)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_UnitaryMautner
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives
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

def contractedBy (H : Subgroup G) : Set G :=
  {u | ∃ a : ℕ → H, Tendsto (fun n => (a n : G)⁻¹ * u * a n) atTop (𝓝 1)}

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_HomogeneousCochainCoordinates
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coordinates for scalar homogeneous cochains

The first vertex records translation and the remaining vertices record
relative positions. This identifies controlled-support homogeneous cochains
with arbitrary cochains valued in the group ring.
-/

noncomputable section
namespace PolycyclicRecognition
open Function

variable {G : Type*} [Group G] {n : ℕ}

def homogeneousCoordinates : (Fin (n + 1) → G) ≃ (Fin n → G) × G where
  toFun x := ⟨fun i => (x 0)⁻¹ * x i.succ, (x 0)⁻¹⟩
  invFun p := Fin.cons p.2⁻¹ (fun i => p.2⁻¹ * p.1 i)
  left_inv x := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp
  right_inv p := by
    apply Prod.ext
    · funext i; simp
    · simp

@[simp] theorem homogeneousCoordinates_apply (x : Fin (n + 1) → G) :
    homogeneousCoordinates x = (fun i => (x 0)⁻¹ * x i.succ, (x 0)⁻¹) := rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_HomogeneousRepresentationCochains
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Controlled cochains as maps from the standard resolution

The coefficient at the identity of an equivariant group-ring-valued map
recovers the scalar cochain. Conversely diagonal translation reconstructs
that equivariant map, with finite support supplied by controlled-support estimates.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
variable {G R : Type} [Group G] [CommRing R] {n : ℕ}

theorem representationCochain_translate
    (F : (Rep.standardComplex R G).X n ⟶ Rep.leftRegular R G)
    (x : Fin (n + 1) → G) (g : G) :
    (F.hom (MonoidAlgebra.single (g • x) 1)).coeff 1 =
      (F.hom (MonoidAlgebra.single x 1)).coeff g⁻¹ := by
  have h := Rep.hom_comm_apply F g (MonoidAlgebra.single x 1)
  change F.hom (Representation.diagonal R G (n + 1) g (MonoidAlgebra.single x 1)) =
    Representation.leftRegular R G g (F.hom (MonoidAlgebra.single x 1)) at h
  rw [Representation.ofMulAction_single] at h
  have hc := congrArg (fun v : MonoidAlgebra R G => v.coeff 1) h
  change (F.hom (MonoidAlgebra.single (g • x) 1)).coeff 1 =
    (Representation.leftRegular R G g (F.hom (MonoidAlgebra.single x 1))).coeff 1 at hc
  simpa only [Representation.coeff_ofMulAction, smul_eq_mul, mul_one] using hc

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_UpperCentralLayerMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Equivariant rational maps from the actual upper central series -/

noncomputable section
namespace PolycyclicRecognition

open scoped IsMulCommutative
variable {G : Type} [Group G] (F : Subgroup G) [F.Normal]

def ambientUpperCentralToF (i : ℕ) : ambientUpperCentralSeries F i →* F :=
  Subgroup.inclusion (Subgroup.map_subtype_le (Subgroup.upperCentralSeries F i))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_AffineProfileConcentration
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concentration near a finite family of affine profiles -/

noncomputable section
namespace PolycyclicRecognition

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal

/-- Restrictions of the finitely many linear profiles, with arbitrary offsets. -/
def affineProfileClass {Z W L : Type*} [TopologicalSpace Z]
    [TopologicalSpace W] [Add W] (A : L → C(Z, W)) : Set C(Z, W) :=
  {f | ∃ a b, ∀ z, f z = A a z + b}

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_AmenableCorrection
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Correcting bounded height defects with an invariant mean

This is the averaging step in Proposition `recognition-from-height` of the
manuscript *Quasi-isometric recognition of virtually polycyclic groups*.
The mean is on the actual space of all bounded real functions. Neither the
height function itself nor its corrected homomorphism has to be bounded.
-/

noncomputable section

namespace PolycyclicRecognition

open scoped ENNReal

universe u v

variable {G : Type u} [Group G]

/-- Coordinate defects are bounded by the defect in the supremum norm. -/
theorem coordinate_defect_le {ι : Type v} [Fintype ι] (s : G → ι → ℝ) (D : ℝ)
    (hD : ∀ h k, ‖s (h * k) - s h - s k‖ ≤ D) (i : ι) (h k : G) :
    |s (h * k) i - s h i - s k i| ≤ D := by
  simpa only [Pi.sub_apply, Real.norm_eq_abs] using
    (norm_le_pi_norm (s (h * k) - s h - s k) i).trans (hD h k)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_BasedImagePaths
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Image paths centered at their actual common starting point -/

noncomputable section

namespace PolycyclicRecognition

open scoped NNReal

variable {G W : Type*} [Group G] [MetricSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

def basedImage (F : G → G) (a g : G) : G := (F a)⁻¹ * F g

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CenteredImagePaths
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Centered image paths for the two probe sheets -/

noncomputable section
namespace PolycyclicRecognition

open Set
open scoped NNReal

section Topological

variable {X G : Type*} [TopologicalSpace X] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

/-- Center the image path at its actual initial image. -/
def centeredImagePath (f : X → G) (hf : Continuous f) {a b : X} (γ : Path a b) :
    Path (1 : G) ((f a)⁻¹ * f b) where
  toFun t := (f a)⁻¹ * f (γ t)
  continuous_toFun := continuous_const.mul (hf.comp γ.continuous)
  source' := by simp
  target' := by simp

end Topological

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CenteredTuplePaths
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Centering every transition of the actual image tuple -/

noncomputable section
namespace PolycyclicRecognition

open Set
open scoped NNReal

variable {X G : Type*} [Group G]

def centeredVertexTuple (f : X → G) (v : ℕ → X) (h : ℕ) : Fin h → G :=
  fun i => (f (v 0))⁻¹ * f (v (i.val + 1))

theorem basedTuplePosition_centeredVertexTuple
    (f : X → G) (v : ℕ → X) (h : ℕ) {j : ℕ} (hj : j ≤ h) :
    basedTuplePosition (centeredVertexTuple f v h) j = (f (v 0))⁻¹ * f (v j) := by
  cases j with
  | zero => simp only [basedTuplePosition_zero, inv_mul_cancel]
  | succ j =>
    have hj' : j < h := by omega
    simpa only [centeredVertexTuple, Nat.add_sub_cancel] using
      basedTuplePosition_succ (centeredVertexTuple f v h) ⟨j, hj'⟩

theorem centeredVertexTuple_transition (f : X → G) (v : ℕ → X) {h : ℕ} (j : Fin h) :
    (basedTuplePosition (centeredVertexTuple f v h) j.val)⁻¹ *
        basedTuplePosition (centeredVertexTuple f v h) (j.val + 1) =
      (f (v j.val))⁻¹ * f (v (j.val + 1)) := by
  rw [basedTuplePosition_centeredVertexTuple f v h j.isLt.le,
    basedTuplePosition_centeredVertexTuple f v h j.isLt]
  group

variable [TopologicalSpace X] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The common centering cancels between successive coordinates, including
the first transition from the identity. -/
def centeredTuplePath (f : X → G) (hf : Continuous f) (v : ℕ → X) {h : ℕ}
    (path : ∀ j : Fin h, Path (v j.val) (v (j.val + 1))) (j : Fin h) :
    Path (1 : G) ((basedTuplePosition (centeredVertexTuple f v h) j.val)⁻¹ *
      basedTuplePosition (centeredVertexTuple f v h) (j.val + 1)) :=
  (centeredImagePath f hf (path j)).cast rfl (centeredVertexTuple_transition f v j)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_OccupationSampling
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual probability laws of independent chart samples -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Filter Set
open scoped Topology

/-- A nonnegative integrable density of mass one defines a probability. -/
def densityProbabilityMeasure {Z : Type*} [MeasurableSpace Z]
    (μ : Measure Z) (ρ : Z → ℝ) (hi : Integrable ρ μ)
    (hp : ∀ z, 0 ≤ ρ z) (hmass : ∫ z, ρ z ∂μ = 1) : ProbabilityMeasure Z :=
  ⟨μ.withDensity (fun z => ENNReal.ofReal (ρ z)), by
    constructor
    rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
      ← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall hp), hmass]
    exact ENNReal.ofReal_one⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_FiniteAffineSelection
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Canonical finite labels and separation from translated competitors -/

noncomputable section
namespace PolycyclicRecognition

open Filter Set
open scoped Topology

/-- Fix one minimizing label at every parameter value. -/
def minimizingFiniteLabel {L : Type*} [Fintype L] [Nonempty L] (cost : L → ℝ) : L :=
  (Finset.exists_min_image Finset.univ cost Finset.univ_nonempty).choose

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CompactSamplingMean
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Canonical affine choices for compactly carried sampling laws -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Filter Set
open scoped Topology

/-- The chosen label depends only on the law and the actual profile,
so different sequences use the same choice at any shared parameter. -/
def canonicalAffineLabel
    {X Y L : Type*} [MeasurableSpace X] [PseudoMetricSpace Y]
    [Finite L] [Nonempty L]
    (μ : Measure X) (f : X → Y) (A : L → Y) : L := by
  letI : Fintype L := Fintype.ofFinite L
  exact minimizingFiniteLabel (fun a => ∫ x, dist (f x) (A a) ∂μ)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_WeightedWordNorm
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Norms obtained by assigning costs to group elements

The infimum of the costs of finite product expressions is subadditive.
A pre-existing group norm below the costs guarantees separation.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped NNReal

open Set
variable {G : Type*} (c : G → ℝ≥0)

/-- Total cost of a product expression. -/
def productCost (l : List G) : ℝ≥0 := (l.map c).sum

@[simp] theorem productCost_nil : productCost c [] = 0 := rfl
@[simp] theorem productCost_cons (g : G) (l : List G) :
    productCost c (g :: l) = c g + productCost c l := rfl
@[simp] theorem productCost_append (l m : List G) :
    productCost c (l ++ m) = productCost c l + productCost c m := by
  simp [productCost]

variable [Group G]

/-- Weighted word norm, allowing every finite product expression. -/
def weightedWordNorm (g : G) : ℝ≥0 :=
  ⨅ l : {l : List G // l.prod = g}, productCost c l.val

instance productExpression_nonempty (g : G) : Nonempty {l : List G // l.prod = g} :=
  ⟨⟨[g], by simp⟩⟩

theorem weightedWordNorm_le_cost (l : List G) :
    weightedWordNorm c l.prod ≤ productCost c l :=
  by
    unfold weightedWordNorm
    exact ciInf_le (f := fun z : {w : List G // w.prod = l.prod} => productCost c z.val)
      (OrderBot.bddBelow _) ⟨l, rfl⟩

@[simp] theorem weightedWordNorm_one : weightedWordNorm c 1 = 0 := by
  exact le_antisymm (by simpa using weightedWordNorm_le_cost c []) (zero_le)

theorem weightedWordNorm_mul (g h : G) :
    weightedWordNorm c (g * h) ≤ weightedWordNorm c g + weightedWordNorm c h := by
  apply NNReal.le_iInf_add_iInf
  intro l m
  simpa only [List.prod_append, l.property, m.property, productCost_append] using
    weightedWordNorm_le_cost c (l.val ++ m.val)

theorem exists_productCost_lt (g : G) (ε : ℝ≥0) (hε : 0 < ε) :
    ∃ l : List G, l.prod = g ∧ productCost c l < weightedWordNorm c g + ε := by
  have h : weightedWordNorm c g < weightedWordNorm c g + ε := lt_add_of_pos_right _ hε
  rw [weightedWordNorm] at h
  obtain ⟨l, hl⟩ := (ciInf_lt_iff (OrderBot.bddBelow _)).mp h
  exact ⟨l.val, l.property, hl⟩

variable (hinv : ∀ g, c g⁻¹ = c g)

include hinv in
theorem productCost_inv_reverse (l : List G) :
    productCost c (l.map Inv.inv).reverse = productCost c l := by
  simp only [productCost, List.map_reverse, List.sum_reverse, List.map_map]
  congr 1
  apply List.map_congr_left
  intro g _
  exact hinv g

include hinv in
theorem weightedWordNorm_inv_le (g : G) : weightedWordNorm c g⁻¹ ≤ weightedWordNorm c g := by
  apply le_ciInf
  intro l
  have hp : (l.val.map Inv.inv).reverse.prod = g⁻¹ := by
    rw [← List.prod_inv_reverse, l.property]
  simpa only [hp, productCost_inv_reverse c hinv] using
    weightedWordNorm_le_cost c (l.val.map Inv.inv).reverse

include hinv in
@[simp] theorem weightedWordNorm_inv (g : G) : weightedWordNorm c g⁻¹ = weightedWordNorm c g := by
  exact le_antisymm (weightedWordNorm_inv_le c hinv g)
    (by simpa using weightedWordNorm_inv_le c hinv g⁻¹)

def weightedWordSeminorm : GroupSeminorm G where
  toFun g := weightedWordNorm c g
  map_one' := by simp
  inv' g := congrArg (fun r : ℝ≥0 => (r : ℝ)) (weightedWordNorm_inv c hinv g)
  mul_le' g h := by exact_mod_cast weightedWordNorm_mul c g h

theorem seminorm_product_le_cost (p : GroupSeminorm G) (hc : ∀ g, p g ≤ c g) (l : List G) :
    p l.prod ≤ productCost c l := by
  induction l with
  | nil => simp
  | cons g l ih =>
    change p (g * l.prod) ≤ (c g : ℝ) + (productCost c l : ℝ)
    exact (p.mul_le' _ _).trans (add_le_add (hc g) ih)

theorem seminorm_le_weightedWordNorm (p : GroupSeminorm G) (hc : ∀ g, p g ≤ c g) (g : G) :
    p g ≤ weightedWordNorm c g := by
  rw [weightedWordNorm, NNReal.coe_iInf]
  apply le_ciInf
  intro l
  simpa only [l.property] using seminorm_product_le_cost c p hc l.val

/-- A norm below the assigned costs makes the weighted seminorm a norm. -/
def weightedWordGroupNorm (p : GroupNorm G) (hc : ∀ g, p g ≤ c g) : GroupNorm G where
  toGroupSeminorm := weightedWordSeminorm c hinv
  eq_one_of_map_eq_zero' g hg := by
    apply p.eq_one_of_map_eq_zero'
    apply le_antisymm ?_ (apply_nonneg p g)
    exact (seminorm_le_weightedWordNorm c p.toGroupSeminorm hc g).trans_eq hg

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CompactWordCost
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Weighted costs attached to a compact generating neighborhood

Inside the generating neighborhood use the original metric; outside it use
word length. This preserves the local topology while controlling word length.
-/

noncomputable section
namespace PolycyclicRecognition

open Set Metric
open scoped NNReal

variable {G : Type*} [Group G] [MetricSpace G] [IsIsometricSMul G G]

def metricGroupNorm : GroupNorm G where
  toFun g := dist 1 g
  map_one' := dist_self 1
  inv' g := by simpa [dist_comm] using (dist_mul_left g (1 : G) g⁻¹).symm
  mul_le' g h := by
    calc
      dist 1 (g * h) ≤ dist 1 g + dist g (g * h) := dist_triangle _ _ _
      _ = dist 1 g + dist 1 h := by
        congr 1
        simpa only [mul_one] using dist_mul_left g (1 : G) h
  eq_one_of_map_eq_zero' g h := (dist_eq_zero.mp h).symm

variable (K : Set G) (hK : Subgroup.closure K = ⊤)

def compactWordGenerators : Group.Generators G K := Group.Generators.ofSet hK

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ConeProbeEndpoints
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The three actual endpoints used in the cone offset comparison -/

namespace PolycyclicRecognition

open Set
open scoped Pointwise

variable {N : Type*} [Group N]

/-- The endpoint carrying both the ideal probe and its quotient section. -/
def coneProbeFirst (S : MulAut N) (n i s : N) : N := n * S (i * s)

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ConnectedEMetric
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Extended distances on a connected space are finite -/

namespace PolycyclicRecognition

theorem edist_ne_top_of_connected {X : Type*} [EMetricSpace X] [ConnectedSpace X]
    (x y : X) : edist x y ≠ ⊤ := by
  have h : IsClopen (Metric.eball x ⊤) :=
    ⟨Metric.isClosed_eball_top, Metric.isOpen_eball⟩
  have hu : Metric.eball x ⊤ = Set.univ :=
    h.eq_univ ⟨x, by simp only [Metric.mem_eball, edist_self]; exact bot_lt_top⟩
  have hy : y ∈ Metric.eball x ⊤ := hu.symm ▸ Set.mem_univ y
  exact (show edist y x < ⊤ from hy).ne ∘ (edist_comm x y ▸ ·)

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CountableMeasureTests
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A countable determining family for finite measures

Finite intersections of a countable measurable generator form a countable
pi system. Equality on this family and equality of total mass determine a
finite measure. This permits simultaneous statements about conditional kernels.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory MeasurableSpace Set

variable (X : Type*) [mX : MeasurableSpace X] [CountablyGenerated X]

/-- Finite intersections, including the empty intersection. -/
def finiteMeasureTest (I : Finset ℕ) : Set X :=
  ⋂ i ∈ I, natGeneratingSequence X i

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_FactorProductPacking
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Packing through a possibly noninjective factor map

Left translations on a semidirect product act separately on its two factor
coordinates. Their product measure is preserved when the action preserves
the first factor's measure. Disjointness is tested after projection to the
ambient metric group, so no injectivity of that projection is required.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Metric Set
open scoped ENNReal

variable {N D G : Type*} [Group N] [Group D] [Group G]
  [MeasurableSpace N] [MeasurableSpace D] [MeasurableMul N] [MeasurableMul D]

/-- Semidirect left translation, written on the product of the factors. -/
def factorTranslate (φ : D →* MulAut N) (p z : N × D) : N × D :=
  (p.1 * φ p.2 z.1, p.2 * z.2)

/-- Measurable automorphisms give measurable product-coordinate translations. -/
def factorTranslationEquiv (φ : D →* MulAut N)
    (hφ : ∀ d, Measurable (φ d)) (p : N × D) : (N × D) ≃ᵐ (N × D) :=
  let e : N ≃ᵐ N := {
    toEquiv := (φ p.2).toEquiv
    measurable_toFun := hφ p.2
    measurable_invFun := by
      change Measurable (fun x => (φ p.2).symm x)
      have he : (fun x => (φ p.2).symm x) = (fun x => φ p.2⁻¹ x) := by
        funext x
        rw [map_inv, MulAut.inv_apply]
      rw [he]
      exact hφ p.2⁻¹ }
  (e.trans (MeasurableEquiv.mulLeft p.1)).prodCongr (MeasurableEquiv.mulLeft p.2)

@[simp] theorem factorTranslationEquiv_apply (φ : D →* MulAut N)
    (hφ : ∀ d, Measurable (φ d)) (p z : N × D) :
    factorTranslationEquiv φ hφ p z = factorTranslate φ p z := rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_LeftInvariantRiemannianMetric
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A left-invariant Riemannian metric

An inner product at the identity is transported by the actual differentials
of left translation. Its smoothness is checked in the tangent bundle charts.
-/

noncomputable section
namespace PolycyclicRecognition

open Bundle Bornology Set
open scoped Manifold ContDiff Topology

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ∞ G]

def leftInvariantInner (e : E ≃L[ℝ] F) (g : G) :
    TangentSpace (𝓘(ℝ, E)) g →L[ℝ] TangentSpace (𝓘(ℝ, E)) g →L[ℝ] ℝ :=
  pullbackInner (E := E) (e.toContinuousLinearMap.comp (leftLogDerivative (E := E) g))

def leftLogCoordinate (g₀ g : G) : E →L[ℝ] E :=
  (leftLogDerivative (E := E) g).comp
    ((trivializationAt E (TangentSpace (𝓘(ℝ, E))) g₀).symmL ℝ g)

theorem contMDiffAt_leftLogCoordinate (g₀ : G) :
    ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, E →L[ℝ] E)) ∞
      (leftLogCoordinate (E := E) g₀) g₀ := by
  have hb : (trivializationAt E (TangentSpace (𝓘(ℝ, E))) (1 : G)).continuousLinearMapAt ℝ 1 =
      ContinuousLinearMap.id ℝ E := by
    rw [TangentBundle.continuousLinearMapAt_trivializationAt (by simp), mfderiv_extChartAt_self]
    rfl
  have hs := contMDiffAt_leftLogDerivative (E := E) g₀
  apply hs.congr_of_eventuallyEq
  apply Filter.Eventually.of_forall
  intro g
  ext v
  dsimp only [leftLogCoordinate, inTangentCoordinates, ContinuousLinearMap.inCoordinates, id_eq]
  rw [hb]
  rfl

theorem leftInvariantInner_coordinates (e : E ≃L[ℝ] F) (g₀ g : G)
    (hg : g ∈ (trivializationAt E (TangentSpace (𝓘(ℝ, E))) g₀).baseSet) :
    (trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
      (fun g => TangentSpace (𝓘(ℝ, E)) g →L[ℝ] TangentSpace (𝓘(ℝ, E)) g →L[ℝ] ℝ)
      g₀ (TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) g (leftInvariantInner e g))).2 =
      pullbackInner (e.toContinuousLinearMap.comp (leftLogCoordinate (E := E) g₀ g)) := by
  have hg' : g ∈ (chartAt E g₀).source := hg
  ext v w
  simp [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates,
    leftInvariantInner, pullbackInner, leftLogCoordinate,
    Trivialization.linearMapAt_apply, hg']
  rfl

theorem contMDiff_leftInvariantInner (e : E ≃L[ℝ] F) :
    ContMDiff (𝓘(ℝ, E)) ((𝓘(ℝ, E)).prod (𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ))) ∞
      (fun g : G => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) g (leftInvariantInner e g)) := by
  intro g₀
  rw [contMDiffAt_section]
  have hco := (contMDiffAt_const (c := e.toContinuousLinearMap)).clm_comp
    (contMDiffAt_leftLogCoordinate (E := E) g₀)
  have hs := contDiff_pullbackInner.contDiffAt.comp_contMDiffAt hco
  apply hs.congr_of_eventuallyEq
  filter_upwards [(trivializationAt E (TangentSpace (𝓘(ℝ, E))) g₀).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt E (TangentSpace (𝓘(ℝ, E))) g₀)] with g hg
  exact leftInvariantInner_coordinates e g₀ g hg

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_LinearProfilesOnBall
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite linear profiles tested on one fixed ball -/

noncomputable section
namespace PolycyclicRecognition

open Set

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- A linear contraction restricts continuously to the same ball. -/
def closedBallLinearSelf (ψ : V →L[ℝ] V) (hψ : ∀ x, ‖ψ x‖ ≤ ‖x‖) (R : ℝ) :
    C(Metric.closedBall (0 : V) R, Metric.closedBall (0 : V) R) := by
  let f : Metric.closedBall (0 : V) R → Metric.closedBall (0 : V) R :=
    fun z => ⟨ψ z, by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact (hψ z).trans (by simpa only [Metric.mem_closedBall, dist_zero_right] using z.property)⟩
  exact ⟨f, (ψ.continuous.comp continuous_subtype_val).subtype_mk _⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ProbeSectionRestrictions
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two probe restrictions in the same section coordinates

The first path controls the quotient orbit point in the base frame. The
absorbed bridge controls the ideal residual in the tile-anchor frame.
These restrictions apply simultaneously to each point of the right cell.
-/

noncomputable section
namespace PolycyclicRecognition

open Module Set
open scoped Pointwise

def exponentialIdealKernelRegion {V N Q : Type*} [LieRing V] [LieAlgebra ℝ V]
    [Group N] [Group Q] (U : LieIdeal ℝ V) (π : N →* Q)
    (Exp : V → N) (I : Set U) : Set π.ker :=
  {n | ∃ i ∈ I, (n : N) = Exp (i : V)}

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.Thompson_FiniteAverage
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
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

def realAvg (A : Finset α) (f : α → ℝ) : ℝ :=
  (A.card : ℝ)⁻¹ * ∑ x ∈ A, f x

@[simp] theorem realAvg_zero (A : Finset α) : realAvg A (fun _ => 0) = 0 := by
  simp [realAvg]

theorem realAvg_add (A : Finset α) (f g : α → ℝ) :
    realAvg A (fun x => f x + g x) = realAvg A f + realAvg A g := by
  simp only [realAvg, Finset.sum_add_distrib, mul_add]

theorem realAvg_const_mul (A : Finset α) (c : ℝ) (f : α → ℝ) :
    realAvg A (fun x => c * f x) = c * realAvg A f := by
  simp only [realAvg, ← Finset.mul_sum, mul_left_comm]

end ThompsonNonamenability

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_RightFolnerExpansion
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Right finite expansions and metric Følner sets in the source group

Left-invariant metrics use right expansions of finite sets. Inversion
converts the left Følner sets supplied by an invariant mean into these sets.
-/

noncomputable section

namespace PolycyclicRecognition

open ThompsonNonamenability
open scoped symmDiff

variable {G : Type*} [Group G] [DecidableEq G]

def rightFiniteExpansion (E S : Finset G) : Finset G :=
  S.biUnion (fun g => E.image (· * g))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ScaleExtension
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Extending data from a strictly increasing sequence of scales

No regularity is imposed between the sampled scales. This bridge permits the
uniform real-scale estimates to be applied to the original sequence data.
-/

noncomputable section

namespace PolycyclicRecognition

open Filter
open scoped Topology

/-- Extend the data by a fixed value outside the sampled scales. -/
def extendOnScales {α : Type*} (r : ℕ → ℝ) (f : ℕ → α) (z : α) (t : ℝ) : α := by
  classical
  exact if h : ∃ n, r n = t then f h.choose else z

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_StationaryCentered
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The zero-mean Hilbert representation and stationary sublinearity

The closed kernel of integration is invariant under inverse pullback.
Ergodicity removes its invariant vectors. This constructs the representation
to which the published reduced-cohomology input is applied; the conclusion
is the manuscript's averaged sublinear estimate for a fixed measure.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory

variable {G X W : Type*} [Group G] [MeasurableSpace X] [MulAction G X]
  [MeasurableConstSMul G X] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W]
  (μ : Measure X) [IsProbabilityMeasure μ] [SMulInvariantMeasure G X μ]

/-- The actual closed zero-mean subspace of `L²`. -/
abbrev ZeroMeanL2 : Submodule ℝ (Lp W 2 μ) := (stationaryL2Mean (W := W) μ).ker

/-- Constants have their stated mean on a probability space. -/
theorem stationaryL2Mean_const (w : W) : stationaryL2Mean μ (Lp.const 2 μ w) = w := by
  change (∫ x, (Lp.const 2 μ w) x ∂μ) = w
  rw [integral_congr_ae (Lp.coeFn_const 2 μ w)]
  simp

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SupportedProbabilityRestriction
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Viewing a supported probability as a probability on its compact support -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set Filter
open scoped Topology

/-- A probability carried by a measurable set, viewed on that subtype. -/
def supportedProbabilityRestriction
    {X : Type*} [MeasurableSpace X] (μ : ProbabilityMeasure X)
    (K : Set X) (hK : MeasurableSet K) (hfull : ∀ᵐ x ∂(μ : Measure X), x ∈ K) :
    ProbabilityMeasure K :=
  ⟨(μ : Measure X).comap Subtype.val, by
    constructor
    rw [comap_subtype_coe_apply hK, image_univ, Subtype.range_coe]
    have he := congrArg (fun m : Measure X => m univ)
      (Measure.restrict_eq_self_of_ae_mem hfull)
    simpa only [Measure.restrict_apply_univ, measure_univ] using he⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_NormalHomologyAction
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conjugation on normal-subgroup homology with ambient coefficients -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
attribute [local instance 2000] Rep.hV2
variable (k : Type) [CommRing k] {G : Type} [Group G]
  (N : Subgroup G) [N.Normal] (A : Rep k G)

def normalHomologyCoefficient (g : G) :
    Rep.res N.subtype A ⟶
      Rep.res (MulAut.conjNormal (H := N) g).toMonoidHom (Rep.res N.subtype A) :=
  Rep.ofHom ⟨A.ρ g, by
    intro n
    change A.ρ g ∘ₗ A.ρ (n : G) = A.ρ (g * n * g⁻¹) ∘ₗ A.ρ g
    change A.ρ g * A.ρ (n : G) = A.ρ (g * n * g⁻¹) * A.ρ g
    rw [← map_mul, ← map_mul]
    congr 1
    group⟩

def normalHomologyMap (i : ℕ) (g : G) :
    groupHomology (Rep.res N.subtype A) i ⟶ groupHomology (Rep.res N.subtype A) i :=
  groupHomology.map (MulAut.conjNormal (H := N) g).toMonoidHom
    (normalHomologyCoefficient k N A g) i

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_InducedBarHomology
attribute [-instance] _root_.OAI.PolycyclicRecognition.productExpression_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Translation on induced bar homology is actual conjugation -/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory HomologicalComplex
open scoped TensorProduct
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
attribute [local instance 2200] TensorProduct.instModule
attribute [local instance 2300] Representation.Coinvariants.instModule Pi.Function.module
variable {G : Type} [Group G] (N : Subgroup G) [N.Normal] (A : Rep ℤ G)

omit [N.Normal] in
theorem inducedTensorRightIso_inv_mk (B : Rep ℤ N) (a : A) (b : B) :
    (inducedTensorRightIso N A B).inv
        (Rep.coinvariantsTensorMk (Rep.res N.subtype A) B a b) =
      Rep.coinvariantsTensorMk A (Rep.ind N.subtype B) a
        (Representation.IndV.mk N.subtype B.ρ 1 b) := by
  apply (ModuleCat.mono_iff_injective (inducedTensorRightIso N A B).hom).mp inferInstance
  rw [← ModuleCat.comp_apply, Iso.inv_hom_id, ModuleCat.id_apply,
    inducedTensorRightIso_mk, map_one, Module.End.one_apply]

def inducedBarChainsIso [DecidableEq N] :
    groupHomology.inhomogeneousChains (Rep.res N.subtype A) ≅
      (normalInducedResolution ℤ N (Rep.barResolution ℤ N)).complex.coinvariantsTensorObj A :=
  groupHomology.inhomogeneousChainsIso (Rep.res N.subtype A) ≪≫
    (inducedResolutionTensorIso N A (Rep.barResolution ℤ N)).symm

theorem inducedBarChainsIso_translation [DecidableEq N] (t : G) :
    groupHomology.chainsMap (MulAut.conjNormal (H := N) t⁻¹).toMonoidHom
        (normalHomologyCoefficient ℤ N A t⁻¹) ≫ (inducedBarChainsIso N A).hom =
      (inducedBarChainsIso N A).hom ≫
        (((Rep.coinvariantsTensor ℤ G).obj A).mapHomologicalComplex (ComplexShape.down ℕ)).map
          (inducedBarTranslation N t) := by
  apply (cancel_mono (inducedResolutionTensorIso N A (Rep.barResolution ℤ N)).hom).mp
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext'
  intro x
  apply LinearMap.ext
  intro v
  change (inducedTensorRightIso N A (Rep.free ℤ N (Fin i → N))).hom
      ((inducedTensorRightIso N A (Rep.free ℤ N (Fin i → N))).inv
        (Rep.finsuppToCoinvariantsTensorFree (Rep.res N.subtype A) (Fin i → N)
          ((groupHomology.chainsMap (MulAut.conjNormal (H := N) t⁻¹).toMonoidHom
            (normalHomologyCoefficient ℤ N A t⁻¹)).f i (Finsupp.single x v)))) =
    (inducedTensorRightIso N A (Rep.free ℤ N (Fin i → N))).hom
      ((((Rep.coinvariantsTensor ℤ G).obj A).map ((inducedBarTranslation N t).f i))
        ((inducedTensorRightIso N A (Rep.free ℤ N (Fin i → N))).inv
          (Rep.finsuppToCoinvariantsTensorFree (Rep.res N.subtype A) (Fin i → N)
            (Finsupp.single x v))))
  rw [← ModuleCat.comp_apply, Iso.inv_hom_id, ModuleCat.id_apply,
    groupHomology.chainsMap_f_single, Rep.finsuppToCoinvariantsTensorFree_single,
    Rep.finsuppToCoinvariantsTensorFree_single]
  change Rep.coinvariantsTensorMk (Rep.res N.subtype A) (Rep.free ℤ N (Fin i → N))
      (A.ρ t⁻¹ v) (Finsupp.single ((MulAut.conjNormal (H := N) t⁻¹) ∘ x)
        (MonoidAlgebra.single 1 1)) =
    (inducedTensorRightIso N A (Rep.free ℤ N (Fin i → N))).hom
      ((((Rep.coinvariantsTensor ℤ G).obj A).map ((inducedBarTranslation N t).f i))
        ((inducedTensorRightIso N A (Rep.free ℤ N (Fin i → N))).inv
          (Rep.coinvariantsTensorMk (Rep.res N.subtype A) (Rep.free ℤ N (Fin i → N)) v
            (Finsupp.single x (MonoidAlgebra.single 1 1)))))
  rw [inducedTensorRightIso_inv_mk]
  change _ = (inducedTensorRightIso N A (Rep.free ℤ N (Fin i → N))).hom
    (Rep.coinvariantsTensorMk A (Rep.ind N.subtype (Rep.free ℤ N (Fin i → N))) v
      ((inducedSemilinearMap ℤ N t _ _
        (barAutomorphismFreeMap (MulAut.conjNormal (H := N) t⁻¹) i)).hom
        (Representation.IndV.mk N.subtype (Rep.free ℤ N (Fin i → N)).ρ 1
          (Finsupp.single x (MonoidAlgebra.single 1 1)))))
  rw [inducedSemilinearMap_mk, mul_one, barAutomorphismFreeMap_single, map_one,
    inducedTensorRightIso_mk]

def inducedBarHomologyIso [DecidableEq N] (d : ℕ) :
    ((normalInducedResolution ℤ N (Rep.barResolution ℤ N)).complex.coinvariantsTensorObj A).homology d ≅
      groupHomology (Rep.res N.subtype A) d :=
  (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) d).mapIso
    (inducedBarChainsIso N A).symm

theorem inducedBarHomologyIso_translation [DecidableEq N] (t : G) (d : ℕ) :
    HomologicalComplex.homologyMap
        ((((Rep.coinvariantsTensor ℤ G).obj A).mapHomologicalComplex (ComplexShape.down ℕ)).map
          (inducedBarTranslation N t)) d ≫ (inducedBarHomologyIso N A d).hom =
      (inducedBarHomologyIso N A d).hom ≫ normalHomologyMap ℤ N A d t⁻¹ := by
  let C := inducedBarChainsIso N A
  let T := (((Rep.coinvariantsTensor ℤ G).obj A).mapHomologicalComplex (ComplexShape.down ℕ)).map
    (inducedBarTranslation N t)
  let f := groupHomology.chainsMap (MulAut.conjNormal (H := N) t⁻¹).toMonoidHom
    (normalHomologyCoefficient ℤ N A t⁻¹)
  have hc : f ≫ C.hom = C.hom ≫ T := inducedBarChainsIso_translation N A t
  have h : T ≫ C.inv = C.inv ≫ f := by
    apply (cancel_epi C.hom).mp
    rw [← Category.assoc]
    rw [← hc]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]
  change HomologicalComplex.homologyMap T d ≫ HomologicalComplex.homologyMap C.inv d =
    HomologicalComplex.homologyMap C.inv d ≫ HomologicalComplex.homologyMap f d
  simpa only [HomologicalComplex.homologyMap_comp] using
    congrArg (fun u => HomologicalComplex.homologyMap u d) h

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_NestedNormalHomology
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conjugation on homology under nested normal subgroups -/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G] (N K : Subgroup G) [N.Normal]
  (hNK : N ≤ K) (A : Rep ℤ G)

variable (M : Subgroup K) [M.Normal] (e : M ≃* N)
  (he : ∀ a : M, ((e a : N) : G) = ((a : K) : G))

def embeddedSubgroupHomologyIso (d : ℕ) :
    groupHomology (Rep.res M.subtype (Rep.res K.subtype A)) d ≅
      groupHomology (Rep.res N.subtype A) d :=
  groupHomology.mapIso (A := Rep.res M.subtype (Rep.res K.subtype A))
    (B := Rep.res N.subtype A) e (LinearEquiv.refl ℤ A.V)
    (by intro a; change A.ρ (a : G) = A.ρ (e a : G); rw [he]) d

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_RationalExteriorHomology
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rational second homology surjects onto the rational exterior square -/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
open scoped TensorProduct
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {A : Type} [CommGroup A]

def rationalLinearExtension {M V : Type} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup V] [Module ℚ V]
    (f : M →ₗ[ℤ] V) : (ℚ ⊗[ℤ] M) →ₗ[ℚ] V :=
  TensorProduct.AlgebraTensorModule.lift ((LinearMap.id : ℚ →ₗ[ℚ] ℚ).smulRight f)

@[simp] theorem rationalLinearExtension_tmul
    {M V : Type} [AddCommGroup M] [Module ℤ M] [AddCommGroup V] [Module ℚ V]
    (f : M →ₗ[ℤ] V) (q : ℚ) (m : M) :
    rationalLinearExtension f (q ⊗ₜ[ℤ] m) = q • f m := rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_SubsingletonGroupProjective
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Projectivity for the trivial group and underlying integer modules -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G] [Subsingleton G]

def subsingletonGroupRepHom {A B : Rep.{0} ℤ G} (f : A →ₗ[ℤ] B) : A ⟶ B :=
  Rep.ofHom ⟨f, fun g => by
    have hg : g = 1 := Subsingleton.elim _ _
    subst g
    simp only [map_one, Module.End.one_eq_id, LinearMap.comp_id, LinearMap.id_comp]⟩

theorem projective_rep_of_integer_projective (A : Rep.{0} ℤ G)
    [Module.Projective ℤ A] : Projective A where
  factors {E X} f p := by
    intro hp
    obtain ⟨l, hl⟩ := Module.projective_lifting_property p.hom.toLinearMap f.hom.toLinearMap
      ((Rep.epi_iff_surjective p).mp hp)
    refine ⟨subsingletonGroupRepHom l, ?_⟩
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    exact hl

theorem integer_projective_of_projective_rep (A : Rep.{0} ℤ G)
    [Projective A] : Module.Projective ℤ A := by
  apply Module.Projective.of_lifting_property''
  intro f hf
  let F : Rep ℤ G := Rep.trivial ℤ G (A →₀ ℤ)
  let p : F ⟶ A := subsingletonGroupRepHom f
  let : Epi p := (Rep.epi_iff_surjective p).mpr hf
  let l := Projective.factorThru (𝟙 A) p
  refine ⟨l.hom.toLinearMap, ?_⟩
  apply LinearMap.ext
  intro x
  exact ConcreteCategory.congr_hom (Projective.factorThru_comp (𝟙 A) p) x

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_TopHomologyKernel
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Top homology as the kernel of the last differential -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
attribute [local instance 2000] ModuleCat.isModule

def topHomologyKernelEquiv (C : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ)
    (h : C.d (n + 1) n = 0) :
    C.homology n ≃ₗ[ℤ] LinearMap.ker (C.d n (n - 1)).hom := by
  let e := (C.isoHomologyπ (n + 1) n (ChainComplex.prev ℕ n) h).symm ≪≫
    C.cyclesIsoSc' (n + 1) n (n - 1) (ChainComplex.prev ℕ n) (by cases n <;> simp) ≪≫
      (C.sc' (n + 1) n (n - 1)).moduleCatCyclesIso
  let a : C.homology n ≃+ LinearMap.ker (C.d n (n - 1)).hom := {
    toFun := e.hom
    invFun := e.inv
    left_inv := fun x => congrArg (fun f => f x) e.hom_inv_id
    right_inv := fun x => congrArg (fun f => f x) e.inv_hom_id
    map_add' := fun x y => map_add e.hom.hom x y }
  exact { a with map_smul' := fun r x => map_intCast_smul a ℤ ℤ r x }

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CoordinateFlowDerivative
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Weak derivatives in smooth polynomial group coordinates -/

noncomputable section

namespace PolycyclicRecognition

open Set MeasureTheory
open scoped NNReal ContDiff

def coordinateFlowDeriv {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (m : V → V → V) (f : V → W) (v g : V) : W :=
  deriv (fun t : ℝ => f (m g (t • v))) 0

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_BasisDerivativeField
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A finite basis assembles the actual horizontal derivative field -/

noncomputable section

namespace PolycyclicRecognition

open Set Filter MeasureTheory Module

def basisDerivativeField {I H G W : Type*} [AddCommGroup H] [Module ℝ H]
    [AddCommGroup W] [Module ℝ W] (b : Basis I ℝ H) (q : H → G → W) (g : G) : H →ₗ[ℝ] W :=
  b.constr ℝ (fun i => q (b i) g)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CompactSemidirectModel
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compact semidirect extensions used by the model comparison -/

noncomputable section
namespace PolycyclicRecognition
open Set

variable {G K : Type*} [Group G] [Group K] [TopologicalSpace G] [TopologicalSpace K]
  (α : K →* MulAut G)

omit [TopologicalSpace G] [TopologicalSpace K] in
theorem semidirect_solvable [Group.IsSolvable G] [Group.IsSolvable K] :
    Group.IsSolvable (G ⋊[α] K) :=
  Group.isSolvable_of_ker_le_range (SemidirectProduct.inl : G →* G ⋊[α] K)
    SemidirectProduct.rightHom SemidirectProduct.range_inl_eq_ker_rightHom.ge

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ComplexTriangularExponential
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Complex upper triangular matrix exponentials -/

noncomputable section
namespace PolycyclicRecognition
open scoped Matrix.Norms.Operator
variable {n : ℕ}

theorem complex_triangular_mul_diag (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsUpperTriangular) (hB : B.IsUpperTriangular) (i : Fin n) :
    (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_single i
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with h | h
    · rw [hA h, zero_mul]
    · rw [hB h, mul_zero]
  · simp

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ComplexWeightLift
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Simultaneous additive lifts of triangular matrix characters -/

noncomputable section
namespace PolycyclicRecognition

variable {G V : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [SimplyConnectedSpace G] [LocallyPathConnectedSpace G]
  [AddCommGroup V] [Module ℝ V] {n : ℕ}

def complexMatrixDiagonalHom (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (hu : ∀ g, (ρ g).IsUpperTriangular) (i : Fin n) : G →* ℂ where
  toFun g := ρ g i i
  map_one' := by simp
  map_mul' g h := by rw [map_mul, complex_triangular_mul_diag _ _ (hu g) (hu h)]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ComplexifiedLieAutomorphism
attribute [-instance] _root_.OAI.PolycyclicRecognition.productExpression_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Complexification of a real semisimple Lie automorphism -/

noncomputable section
namespace PolycyclicRecognition
open scoped TensorProduct

variable (L : Type) [LieRing L] [LieAlgebra ℝ L]

def complexifiedLieEquiv (S : L ≃ₗ⁅ℝ⁆ L) : (ℂ ⊗[ℝ] L) ≃ₗ⁅ℂ⁆ (ℂ ⊗[ℝ] L) :=
  { S.toLinearEquiv.baseChange ℝ ℂ L L with
    map_lie' := by
      intro x y
      exact (LieAlgebra.ExtendScalars.map (AlgHom.id ℝ ℂ) S.toLieHom).map_lie x y }

@[simp] theorem complexifiedLieEquiv_tmul (S : L ≃ₗ⁅ℝ⁆ L) (z : ℂ) (x : L) :
    complexifiedLieEquiv L S (z ⊗ₜ[ℝ] x) = z ⊗ₜ[ℝ] S x := rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_IndependentWeightCone
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The closed cones used by the neighboring-offset argument

A ray and a cone on two independent weights are closed. We construct them
as actual proper cones, so polar separation requires no closedness input.
-/

noncomputable section
namespace PolycyclicRecognition

open Set
open scoped BigOperators

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {I : Type*} [Fintype I]

/-- The nonnegative span of an independent finite family is closed. -/
def independentWeightCone (v : I → V) (hv : LinearIndependent ℝ v) : ProperCone ℝ V where
  toSubmodule := (PointedCone.positive ℝ (I → ℝ)).map (Fintype.linearCombination ℝ v)
  isClosed' := by
    have he := LinearMap.isClosedEmbedding_of_injective
      (LinearMap.ker_eq_bot.mpr
        (linearIndependent_iff_injective_fintypeLinearCombination.mp hv))
    exact he.isClosedMap _ isClosed_Ici

@[simp] theorem mem_independentWeightCone (v : I → V) (hv : LinearIndependent ℝ v)
    (x : V) : x ∈ independentWeightCone v hv ↔
      ∃ a : I → ℝ, (∀ i, 0 ≤ a i) ∧ ∑ i, a i • v i = x := by
  rfl

def closedWeightRay (α : V) (hα : α ≠ 0) : ProperCone ℝ V :=
  independentWeightCone (fun _ : Fin 1 => α) (by
    simpa using (linearIndependent_unique_iff (R := ℝ) (v := fun _ : Fin 1 => α)).mpr hα)

def closedTwoWeightCone (α η : V) (h : LinearIndependent ℝ ![α, η]) : ProperCone ℝ V :=
  independentWeightCone ![α, η] h

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_NilpotentCoordinateFlow
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Nilpotent linear flows in changing box coordinates -/

noncomputable section
namespace PolycyclicRecognition

open Module Filter
open scoped Topology BigOperators

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}

def coordinateEnd (b : Basis (Fin n) ℝ V) (D : Module.End ℝ V) :
    (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  LinearMap.toContinuousLinearMap (b.equivFun.conj D)

@[simp] theorem coordinateEnd_apply (b : Basis (Fin n) ℝ V) (D : Module.End ℝ V)
    (x : Fin n → ℝ) : coordinateEnd b D x = b.equivFun (D (b.equivFun.symm x)) := rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_NilpotentFiniteRankRootCore
attribute [-instance] _root_.OAI.PolycyclicRecognition.productExpression_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite root cores from the rational abelianization of a nilpotent group

Induction uses the last lower-central layer. Its commutator tensor
presentation is finite because the preceding layer is an abelian subgroup
of the quotient, where a finite root core has already been constructed.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped TensorProduct IsMulCommutative commutatorElement
variable {G Q : Type} [Group G] [Group Q]

theorem abelianization_map_surjective (f : G →* Q) (hf : Function.Surjective f) :
    Function.Surjective (Abelianization.map f) := by
  intro a
  induction a using QuotientGroup.induction_on with | H a =>
    obtain ⟨g, rfl⟩ := hf a
    exact ⟨Abelianization.of g, rfl⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_NilpotentLinearFlow
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial linear flows used in the logarithm of a lattice automorphism -/

noncomputable section
namespace PolycyclicRecognition

section Algebra
variable {V : Type*} [AddCommGroup V] [Module ℝ V]
local instance linearFlowRationalModule : Module ℚ V := Module.compHom V (algebraMap ℚ ℝ)

def nilpotentLinearFlow (D : Module.End ℝ V) (t : ℝ) : Module.End ℝ V :=
  IsNilpotent.exp (t • D)

theorem nilpotentLinearFlow_eq_sum (D : Module.End ℝ V) {k : ℕ} (hk : D ^ k = 0)
    (t : ℝ) (x : V) :
    nilpotentLinearFlow D t x =
      ∑ i ∈ Finset.range k, t ^ i • (((i.factorial : ℚ)⁻¹ • D ^ i) x) := by
  have ht : (t • D) ^ k = 0 := by rw [smul_pow, hk, smul_zero]
  rw [nilpotentLinearFlow, IsNilpotent.exp_eq_sum ht]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_pow]
  apply Finset.sum_congr rfl
  intro i _
  exact smul_comm _ _ _

end Algebra

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_OrderedSemidirectWords
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Ordered integral words in an infinite cyclic extension -/

namespace PolycyclicRecognition
variable {H G : Type*} [Group H] [Group G] {d : ℕ}

def cyclicExtensionGenerators (a : MulAut H) (X : Fin d → H) :
    Fin (d + 1) → H ⋊[integerPowerAction a] Multiplicative ℤ :=
  Fin.snoc (fun i => SemidirectProduct.inl (X i))
    (SemidirectProduct.inr (Multiplicative.ofAdd 1))

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RayGroupContraction
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Logarithmic contraction of the actual quotient-group action

The Lie-coordinate estimate is transported through the actual bijective
exponential. Compact subsets have bounded logarithmic coordinates. The
action is the exponential conjugate already identified with the descended
Cartan action in `ConeQuotientHaarAction`.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieAlgebra LieModule Set
open scoped Manifold

section Logarithm

variable {V E G : Type*} [LieRing V] [LieAlgebra ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]
  (e : V ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
  (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hbij : Function.Bijective Exp)

/-- The logarithm in a specified Lie-algebra realization of a bijective
group exponential. -/
def exponentialLog : G → V :=
  (Equiv.ofBijective (Exp ∘ e) (hbij.comp e.bijective)).symm

@[simp] theorem exponentialLog_exp (v : V) :
    exponentialLog e Exp hbij (Exp (e v)) = v :=
  (Equiv.ofBijective (Exp ∘ e) (hbij.comp e.bijective)).symm_apply_apply v

end Logarithm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_UniformLatticeTransport
attribute [-instance] _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Transporting a compact lattice cover through a group homeomorphism -/

noncomputable section
namespace PolycyclicRecognition
variable {G H : Type*} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]

omit [TopologicalSpace G] [TopologicalSpace H] in
def comapSubgroupEquiv (e : G ≃* H) (Λ : Subgroup H) :
    (Λ.comap e.toMonoidHom) ≃* Λ where
  toFun x := ⟨e x.val, x.property⟩
  invFun y := ⟨e.symm y.val, by change e (e.symm y.val) ∈ Λ; rw [e.apply_symm_apply]; exact y.property⟩
  left_inv x := by apply Subtype.ext; exact e.symm_apply_apply x.val
  right_inv y := by apply Subtype.ext; exact e.apply_symm_apply y.val
  map_mul' x y := by apply Subtype.ext; exact e.map_mul x.val y.val

end PolycyclicRecognition

end

end OAI
end


