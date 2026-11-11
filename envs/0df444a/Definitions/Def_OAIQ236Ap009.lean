-- Prove2me | Definitions.Def_OAIQ236Ap009
-- name    : OAIQ236Ap009
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T19:58:00.717662+00:00
-- url     : https://prove2.me/theorems/d8baed36-4d6d-42f0-9499-2f9f28f32224
-- title:
--   Definitions bundle OAIQ236Ap009 of the split of OpenAI, Parabolic intersections in Artin groups
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.HarmonicArtin.ParabolicIntersections.unconditional_arbitrary_intersections`, `OAI.HarmonicArtin.ParabolicIntersections.unconditional_nonclique_dynamics`, `OAI.HarmonicArtin.ParabolicIntersections.unconditional_parabolic_closure` and `OAI.HarmonicArtin.ParabolicIntersections.unconditional_parabolic_intersections`, carved from OpenAI's openai/math development (OpenAI, *Parabolic intersections in Artin groups*, OpenAI Math Release, September 23, 2026, result family 254, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 255 declarations of OpenAI's Lean: 81 definitions, 1 inductive type or structure, 1 instance and 172 theorems. The definitions and types are `OAI.HarmonicArtin.ParabolicIntersections.PublishedAcyclicTwist`, `OAI.HarmonicArtin.ReversibleQuiver.Iso.coefficientTopDual`, `OAI.HarmonicArtin.ReversibleQuiver.Iso.dualSupportedCycles`, `OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.termwiseSplitInjection`, `OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.coefficientTopLabelEquiv`, `OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.homDualSupportedCyclesEquiv`, `OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.leftSocleIndexEquiv`, `OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.leftTopTestEquiv`, `OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.truncationIndexEquiv`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.ChainIsomorphism.coefficientSocle`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.ChainIsomorphism.coefficientTopDual`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.ChainIsomorphism.pureDualSupportedCycles`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.ChainIsomorphism.pureSupportedCycles`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.ClassTestUpper`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.HomMonoFrom`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.HomotopyEquivalence.lowerTruncation`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.HomotopyEquivalence.ofPure`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.HomotopyEquivalence.pureLayer`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.Map.lowerTruncation`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.Map.pureLayer`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.TermwiseSplitInjection.colorTarget`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.adjacentTestFirstPivot`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.adjacentTestIndexEquiv`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.adjacentTestReduction`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.adjacentTestSecondPivot`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeIndexEquiv`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeIndexMap`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudePivot`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeTwistReduction`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.canonicalLowMap`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.canonicalLowSource`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.canonicalWordLow`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.cappedSummandInjection`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.classLayerTopDimension`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.classLayerTotalHomDimension`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.classLowerTruncation`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.coefficientSocleTestEquiv`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.coefficientTopSumEquiv`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.coefficientTopTestEquiv`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.coneLayerIsomorphism` and 42 more.
--
--   **Sources.** They come from these modules of lean/OAI/Topology, in whole or in part: `ArtinGroups_Complexes_ActedIndex`, `ArtinGroups_Complexes_ArrowShift`, `ArtinGroups_Complexes_CanonicalWordLow`, `ArtinGroups_Complexes_CoefficientTopDual`, `ArtinGroups_Complexes_ColorSupport`, `ArtinGroups_Complexes_DiagonalVertex`, `ArtinGroups_Complexes_DifferentialMulExtendLayer`, `ArtinGroups_Complexes_DownClosed`, `ArtinGroups_Complexes_EmptyTestIndex`, `ArtinGroups_Complexes_ExtendLayer`, `ArtinGroups_Complexes_FiniteFamilyLevelSupport`, `ArtinGroups_Complexes_GeneratorArray2`, `ArtinGroups_Complexes_HighConeIndex`, `ArtinGroups_Complexes_HighConeRetainedPure`, `ArtinGroups_Complexes_HomDetector`, `ArtinGroups_Complexes_HomDimension`, `ArtinGroups_Complexes_HomDimension2`, `ArtinGroups_Complexes_HomDimensionZeroCycles`, `ArtinGroups_Complexes_HomDimensionZeroHom`, `ArtinGroups_Complexes_HomInternalSupport`, `ArtinGroups_Complexes_HomMono`, `ArtinGroups_Complexes_HomPath`, `ArtinGroups_Complexes_HomSpace`, `ArtinGroups_Complexes_HomSpaceDuality`, `ArtinGroups_Complexes_HomSpacePairing`, `ArtinGroups_Complexes_HomStep`, `ArtinGroups_Complexes_InitialProbeTestUpper`, `ArtinGroups_Complexes_InverseHomMatrix`, `ArtinGroups_Complexes_InverseMatrix`, `ArtinGroups_Complexes_InverseWordAction`, `ArtinGroups_Complexes_IsolatedIndexCycle`, `ArtinGroups_Complexes_LayerTotalHomDimension`, `ArtinGroups_Complexes_LeftMatrix`, `ArtinGroups_Complexes_LevelArrayMinimalApply`, `ArtinGroups_Complexes_LowMatrix`, `ArtinGroups_Complexes_LowerTruncation`, `ArtinGroups_Complexes_MatrixOneMulExtend`, `ArtinGroups_Complexes_MinimalModel`, `ArtinGroups_Complexes_MinimalModelEquivalence`, `ArtinGroups_Complexes_NegativeAmplitudeCoreIndex`, `ArtinGroups_Complexes_NegativeConeIndex`, `ArtinGroups_Complexes_NegativeHomTransformReflect`, `ArtinGroups_Complexes_OutsideCap`, `ArtinGroups_Complexes_PlacedProjective`, `ArtinGroups_Complexes_PositiveConeIndex`, `ArtinGroups_Complexes_PositiveTwistLowerBound`, `ArtinGroups_Complexes_PositiveTwistOtherTest2`, `ArtinGroups_Complexes_PositiveTwistOtherTest3`, `ArtinGroups_Complexes_PositiveWord`, `ArtinGroups_Complexes_PositiveWordActionTest`, `ArtinGroups_Complexes_PositiveWordLowerBound`, `ArtinGroups_Complexes_ProbeFixedNoDiagonal`, `ArtinGroups_Complexes_PureCoefficientCohomology`, `ArtinGroups_Complexes_PureHomSpaceHomogeneous`, `ArtinGroups_Complexes_PureLayerSelf`, `ArtinGroups_Complexes_PureSupportedCycles`, `ArtinGroups_Complexes_ReducedAmplitudeTwistLevel`, `ArtinGroups_Complexes_ReducedNegativeAmplitudeTwist`, `ArtinGroups_Complexes_ReducedNoTopDivisor`, `ArtinGroups_Complexes_RestrictExtendLayerMul`, `ArtinGroups_Complexes_RestrictLayer`, `ArtinGroups_Complexes_ScalarExactNotZero`, `ArtinGroups_Complexes_ScalarSupportedCochainShift`, `ArtinGroups_Complexes_ScalarSupportedTokenShift`, `ArtinGroups_Complexes_SecondaryLayer`, `ArtinGroups_Complexes_Shift`, `ArtinGroups_Complexes_SumTestEquiv`, `ArtinGroups_Complexes_SumTruncationEquiv`, `ArtinGroups_Complexes_SummandSecondary`, `ArtinGroups_Complexes_TargetLow`, `ArtinGroups_Complexes_TermwiseSplitInjection`, `ArtinGroups_Complexes_TestExact`, `ArtinGroups_Complexes_TestUpperBound`, `ArtinGroups_Complexes_TokenShift`, `ArtinGroups_Complexes_WordInverseModel`, `ArtinGroups_Coxeter_OrdinaryCoxeterMatrix`, `ArtinGroups_Coxeter_PositiveBraidRel`, `ArtinGroups_Functors_ComplexLowerTruncation`, `ArtinGroups_Functors_ComplexPureLayer`, `ArtinGroups_Functors_HomDimensionFlexible`, `ArtinGroups_Functors_HomDualSupportedCycles`, `ArtinGroups_Functors_LeftSocleIndexEquiv`, `ArtinGroups_Functors_SupportedCycles`, `ArtinGroups_Functors_TermwiseSplitInjection`, `ArtinGroups_Functors_TruncationIndexEquiv`, `ArtinGroups_Functors_TwistProdGeneratorExterior`, `ArtinGroups_Harmonic_CanonicalFusionLow`, `ArtinGroups_Harmonic_FiniteArtinPositiveLeft`, `ArtinGroups_Harmonic_FusionExpressionAction`, `ArtinGroups_Harmonic_FusionExpressionOrbit`, `ArtinGroups_Harmonic_FusionQuiverSimpleEdge`, `ArtinGroups_Harmonic_FusionZeroLabel`, `ArtinGroups_Harmonic_Level`, `ArtinGroups_Harmonic_PositiveLiftSimple`, `ArtinGroups_ParabolicIntersections_AcyclicTwistInput`, `ArtinGroups_Quivers_ClosedNeighborhood`, `ArtinGroups_Quivers_CoefficientMatrix`, `ArtinGroups_Quivers_Level`, `ArtinGroups_Quivers_PathTwo`, `ArtinGroups_Quivers_PathTwoSelf`, `ArtinGroups_Quivers_TokenTestVector`, `ArtinGroups_Quivers_UnitTestVector`, `ArtinGroups_Quivers_VertexLinear`, `ArtinGroups_Realizations_FusionWeightedHom`.
--
--   **Imports.** It imports the published bundle `Def_ArtinParabolicIntersections`; the bundles `OAIQ236Ap005`, `OAIQ236Ap006` and `OAIQ236Ap007` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ236Ap011` and `OAIQ236Ap012`.
-- source:
--   OpenAI, Parabolic intersections in Artin groups, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 254; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Parabolic-intersections-in-Artin-groups-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Topology at commit adc7f12

import Mathlib
import Definitions.Def_ArtinParabolicIntersections
import Definitions.Def_OAIQ236Ap005
import Definitions.Def_OAIQ236Ap006
import Definitions.Def_OAIQ236Ap007

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_Level
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.instAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin

namespace ReversibleQuiver.Zigzag

variable {V A K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V]

namespace BasedComplex

variable {I : Type*} [Fintype I]

lemma pureLayer_linear (E : BasedComplex Q (K := K) I) (hE : E.IsMinimal Q)
    (d : ℤ) (i j : {i // (E.placement i).level = d}) :
    ((E.pureLayer Q hE d).differential i j).vertex = 0 ∧
    ((E.pureLayer Q hE d).differential i j).token = 0 := by
  change (E.differential i j).vertex = 0 ∧ (E.differential i j).token = 0
  refine ⟨hE i j, ?_⟩
  by_cases hz : E.differential i j = 0
  · rw [hz]
    rfl
  have hc : (E.placement j).cochain = (E.placement i).cochain + 1 := by
    by_contra h
    exact hz ((E.degree i j).1 h)
  have hi := i.property
  have hj := j.property
  dsimp only [GeneratorPlacement.level] at hi hj
  apply (E.degree i j).2.2.2
  omega

end BasedComplex
end ReversibleQuiver.Zigzag
end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_ActedIndex
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.linearMap_pathBasis _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_base _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_left _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_right _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.corner_val _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_reverse _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.selfCornerEquiv_false _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.selfCornerEquiv_true
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

variable {V A K I : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I]

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma unitTest_injective (E : BasedComplex Q (K := K) I) (α : V) :
    Function.Injective (unitTest Q E α) := by
  intro i j h
  exact Subtype.ext (congrArg Sigma.fst h)

def amplitudeIndexMap (E : BasedComplex Q (K := K) I) (α : V) :
    ActedIndex Q E α ⊕ ActedIndex Q E α ⊕ AmplitudeCoreIndex Q E α →
      TestIndex Q E.placement α ⊕ I
  | .inl i => .inl (unitTest Q E α i)
  | .inr (.inl i) => .inr i.val
  | .inr (.inr (.inl u)) => .inl u.val
  | .inr (.inr (.inr i)) => .inr i.val

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma amplitudeIndexMap_injective (E : BasedComplex Q (K := K) I) (α : V) :
    Function.Injective (amplitudeIndexMap Q E α) := by
  intro i j h
  rcases i with i | i | u | i <;> rcases j with j | j | v | j
  all_goals dsimp only [amplitudeIndexMap] at h
  all_goals try cases h
  · exact congrArg Sum.inl (unitTest_injective Q E α (Sum.inl.inj h))
  · have hv := v.property
    rw [← Sum.inl.inj h] at hv
    exact (hv rfl).elim
  · exact congrArg (fun x => Sum.inr (Sum.inl x)) (Subtype.ext (Sum.inr.inj h))
  · exact (j.property ((Sum.inr.inj h) ▸ i.property)).elim
  · have hu := u.property
    rw [Sum.inl.inj h] at hu
    exact (hu rfl).elim
  · exact congrArg (fun x => Sum.inr (Sum.inr (Sum.inl x))) (Subtype.ext (Sum.inl.inj h))
  · exact (i.property ((Sum.inr.inj h).symm ▸ j.property)).elim
  · exact congrArg (fun x => Sum.inr (Sum.inr (Sum.inr x))) (Subtype.ext (Sum.inr.inj h))

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma amplitudeIndexMap_surjective (E : BasedComplex Q (K := K) I) (α : V) :
    Function.Surjective (amplitudeIndexMap Q E α) := by
  intro u
  rcases u with ⟨i, ⟨v | a | v, hs, ht⟩⟩ | i
  · dsimp only [Path.source, Path.target] at hs ht
    subst v
    exact ⟨.inl ⟨i, ht.symm⟩, rfl⟩
  · exact ⟨.inr (.inr (.inl ⟨⟨i, ⟨.inr (.inl a), hs, ht⟩⟩, by norm_num [Path.length]⟩)), rfl⟩
  · exact ⟨.inr (.inr (.inl ⟨⟨i, ⟨.inr (.inr v), hs, ht⟩⟩, by norm_num [Path.length]⟩)), rfl⟩
  · by_cases hi : (E.placement i).color = α
    · exact ⟨.inr (.inl ⟨i, hi⟩), rfl⟩
    · exact ⟨.inr (.inr (.inr ⟨i, hi⟩)), rfl⟩

noncomputable def amplitudeIndexEquiv (E : BasedComplex Q (K := K) I) (α : V) :
    ActedIndex Q E α ⊕ ActedIndex Q E α ⊕ AmplitudeCoreIndex Q E α ≃
      TestIndex Q E.placement α ⊕ I :=
  Equiv.ofBijective (amplitudeIndexMap Q E α)
    ⟨amplitudeIndexMap_injective Q E α, amplitudeIndexMap_surjective Q E α⟩

noncomputable def normalizedAmplitudeTwist (E : BasedComplex Q (K := K) I) (α : V) :
    BasedComplex Q (K := K)
      (ActedIndex Q E α ⊕ ActedIndex Q E α ⊕ AmplitudeCoreIndex Q E α) :=
  (E.positiveTwist Q α).reindex Q (amplitudeIndexEquiv Q E α)

noncomputable def amplitudePivot (E : BasedComplex Q (K := K) I) (α : V) :
    BlockPivot Q (normalizedAmplitudeTwist Q E α) where
  coefficient := 1
  nonzero := one_ne_zero
  color i := i.property
  cochain i := by change (E.placement i.val).cochain = (E.placement i.val).cochain - 1 + 1; omega
  internal i := by change (E.placement i.val).internal = (E.placement i.val).internal + 0; omega
  entry i j := by
    change evaluationMatrix Q E.placement α (unitTest Q E α i) j.val =
      (1 : K) • projectiveIdentity Q
        (fun j => (normalizedAmplitudeTwist Q E α).placement (.inl j)) i j
    simp only [evaluationMatrix, unitTest, pathBasis_vertex, one_smul,
      projectiveIdentity, Matrix.diagonal_apply]
    change (if i.val = j.val then vertexId Q (K := K) α else 0) =
      (if i = j then vertexId Q (K := K) α else 0)
    simp only [Subtype.val_inj]

noncomputable def reducedAmplitudeTwist (E : BasedComplex Q (K := K) I) (α : V) :
    BasedComplex Q (K := K) (AmplitudeCoreIndex Q E α) :=
  (amplitudePivot Q E α).reduced Q

noncomputable def amplitudeTwistReduction (E : BasedComplex Q (K := K) I) (α : V) :
    HomotopyEquivalence Q (E.positiveTwist Q α) (reducedAmplitudeTwist Q E α) :=
  ((E.positiveTwist Q α).reindexHomotopyEquivalence Q (amplitudeIndexEquiv Q E α)).trans Q
    ((amplitudePivot Q E α).reductionEquivalence Q)

lemma reducedAmplitudeTwist_placement (E : BasedComplex Q (K := K) I) (α : V) :
    (reducedAmplitudeTwist Q E α).placement =
      fun i => match i with
      | .inl u => ⟨α, (E.placement u.val.1).cochain - 1,
          (E.placement u.val.1).internal + Path.length u.val.2.val⟩
      | .inr i => E.placement i.val := by
  funext i
  cases i <;> rfl

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_TokenShift
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

variable {V A K I : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I]

noncomputable def testShiftPivot (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) (α : V) :
    BlockPivot Q (normalizedTestTwist Q hn E α) where
  coefficient := 1
  nonzero := one_ne_zero
  color _ := rfl
  cochain i := by
    change (E.placement i.1).cochain = (E.placement i.1).cochain - 1 + 1
    omega
  internal i := by
    change (E.placement i.1).internal + Path.length i.2.val =
      ((E.placement i.1).internal + Path.length i.2.val) + 0
    omega
  entry i j := by
    rw [normalizedTestTwist_pivot_entry]
    simp only [one_smul]
    rfl

lemma testShift_reduced_eq (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) (α : V) :
    (testShiftPivot Q hn E α).reduced Q = (E.testComplex Q α).tokenShift Q := by
  apply ext_placement_differential Q
  · rfl
  · apply Matrix.ext
    intro u v
    rw [BlockPivot.reduced_differential, normalizedTestTwist_token_token]
    simp only [normalizedTestTwist_unit_token, MulZeroClass.mul_zero,
      Finset.sum_const_zero, sub_zero]
    rfl

noncomputable def positiveTwist_testShift (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) (α : V) :
    HomotopyEquivalence Q ((E.positiveTwist Q α).testComplex Q α)
      ((E.testComplex Q α).tokenShift Q) := by
  let e := ((E.positiveTwist Q α).testComplex Q α).reindexHomotopyEquivalence Q
    (testShiftIndexEquiv Q hn E α)
  let f := (testShiftPivot Q hn E α).reductionEquivalence Q
  rw [testShift_reduced_eq] at f
  exact e.trans Q f

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_ArrowShift
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K I : Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I]

noncomputable def adjacentTestIndexEquiv (hn:∀ a,Q.source a≠Q.target a)
    (E:BasedComplex Q (K:=K) I) {α β:V} (e:SimpleEdge Q α β) :
    AdjacentTestIndex Q E α β ≃
      TestIndex Q ((E.positiveTwist Q β).positiveTwist Q α).placement β where
  toFun
    | .inl u => ⟨.inr (.inl u),selfCornerEquiv Q hn β false⟩
    | .inr (.inl u) => ⟨.inr (.inr u.1),u.2⟩
    | .inr (.inr (.inl u)) => ⟨.inl ⟨.inl u,e.corner Q⟩,(e.reverse Q).corner Q⟩
    | .inr (.inr (.inr (.inl u))) => ⟨.inr (.inl u),selfCornerEquiv Q hn β true⟩
    | .inr (.inr (.inr (.inr u))) => ⟨.inl ⟨.inr u.1,u.2⟩,(e.reverse Q).corner Q⟩
  invFun
    | ⟨.inl ⟨.inl u,_⟩,_⟩ => .inr (.inr (.inl u))
    | ⟨.inl ⟨.inr i,p⟩,_⟩ => .inr (.inr (.inr (.inr ⟨i,p⟩)))
    | ⟨.inr (.inl u),p⟩ => if (selfCornerEquiv Q hn β).symm p then
        .inr (.inr (.inr (.inl u))) else .inl u
    | ⟨.inr (.inr i),p⟩ => .inr (.inl ⟨i,p⟩)
  left_inv u := by rcases u with u|u|u|u|u <;> rfl
  right_inv u := by
    rcases u with ⟨⟨u|i,p⟩|(u|i),q⟩
    · have hp:p=e.corner Q:=e.corner_unique Q p
      have hq:q=(e.reverse Q).corner Q := (e.reverse Q).corner_unique Q q
      cases hp; cases hq; rfl
    · have hq:q=(e.reverse Q).corner Q := (e.reverse Q).corner_unique Q q
      cases hq; rfl
    · have he:=(selfCornerEquiv Q hn β).apply_symm_apply q
      cases h:(selfCornerEquiv Q hn β).symm q
      · simp only [h,Bool.false_eq_true,↓reduceIte]
        congr 1
        change (selfCornerEquiv Q hn β false : Zigzag.CornerPath Q β β)=q
        simpa only [h] using he
      · simp only [h,↓reduceIte]
        congr 1
        change (selfCornerEquiv Q hn β true : Zigzag.CornerPath Q β β)=q
        simpa only [h] using he
    · rfl

noncomputable def normalizedAdjacentTest (hn:∀ a,Q.source a≠Q.target a)
    (E:BasedComplex Q (K:=K) I) {α β:V} (e:SimpleEdge Q α β) :=
  (((E.positiveTwist Q β).positiveTwist Q α).testComplex Q β).reindex Q
    (adjacentTestIndexEquiv Q hn E e)

lemma adjacentTest_first_pivot_entry (hn:∀ a,Q.source a≠Q.target a)
    (E:BasedComplex Q (K:=K) I) {α β:V} (e:SimpleEdge Q α β)
    (u v:TestIndex Q E.placement β) :
    (normalizedAdjacentTest Q hn E e).differential (.inl u) (.inr (.inl v))=
      projectiveIdentity Q (testPlacement Q E.placement β) u v := by
  exact normalizedTestTwist_pivot_entry Q hn E β u v

noncomputable def adjacentTestFirstPivot (hn:∀ a,Q.source a≠Q.target a)
    (E:BasedComplex Q (K:=K) I) {α β:V} (e:SimpleEdge Q α β) :
    BlockPivot Q (normalizedAdjacentTest Q hn E e) where
  coefficient := 1
  nonzero := one_ne_zero
  color _ := rfl
  cochain i := by change (E.placement i.1).cochain=(E.placement i.1).cochain-1+1; omega
  internal i := by
    change (E.placement i.1).internal+Path.length i.2.val=
      (E.placement i.1).internal+Path.length i.2.val+0
    omega
  entry i j := by rw [adjacentTest_first_pivot_entry]; simp only [one_smul]; rfl

omit [DecidableEq I] in
lemma adjacentTest_first_source_retained (hn:∀ a,Q.source a≠Q.target a)
    (E:BasedComplex Q (K:=K) I) {α β:V} (e:SimpleEdge Q α β)
    (u:TestIndex Q E.placement β)
    (v:TestIndex Q E.placement β ⊕ TestIndex Q E.placement β ⊕ TestIndex Q E.placement α) :
    (normalizedAdjacentTest Q hn E e).differential (.inl u) (.inr (.inr v))=0 := by
  rcases v with v|v|v
  · change (pathCoordinates Q (K:=K) (_ * 0) _) • vertexId Q β=0
    rw [MulZeroClass.mul_zero,coordinates_zero,zero_smul]
  · exact normalizedTestTwist_unit_token Q hn E β u v
  · change (pathCoordinates Q (K:=K) (_ * 0) _) • vertexId Q β=0
    rw [MulZeroClass.mul_zero,coordinates_zero,zero_smul]

lemma adjacentTest_first_reduced_entry (hn:∀ a,Q.source a≠Q.target a)
    (E:BasedComplex Q (K:=K) I) {α β:V} (e:SimpleEdge Q α β)
    (u v:TestIndex Q E.placement β ⊕ TestIndex Q E.placement β ⊕ TestIndex Q E.placement α) :
    ((adjacentTestFirstPivot Q hn E e).reduced Q).differential u v=
      (normalizedAdjacentTest Q hn E e).differential (.inr (.inr u)) (.inr (.inr v)) := by
  rw [BlockPivot.reduced_differential]
  simp only [adjacentTest_first_source_retained,MulZeroClass.mul_zero,Finset.sum_const_zero,sub_zero]

omit [DecidableEq I] in
lemma adjacentTest_second_pivot_entry (hn:∀ a,Q.source a≠Q.target a)
    (E:BasedComplex Q (K:=K) I) {α β:V} (e:SimpleEdge Q α β)
    (u v:TestIndex Q E.placement β) :
    (normalizedAdjacentTest Q hn E e).differential
      (.inr (.inr (.inl u))) (.inr (.inr (.inr (.inl v))))=
      projectiveIdentity Q (testPlacement Q E.placement β) u v := by
  change (pathCoordinates Q (K:=K) (pathBasis Q (e.reverse Q).corner.val *
    evaluationMatrix Q (E.positiveTwist Q β).placement α ⟨.inl u,e.corner Q⟩ (.inl v))
      (Sum.inr (Sum.inr β))) • vertexId Q β=_
  simp only [evaluationMatrix,SimpleEdge.corner_val,pathBasis_arrow,
    Sum.inl.injEq,projectiveIdentity,Matrix.diagonal_apply,testPlacement,
    SimpleEdge.reverse_arrow]
  by_cases h:u=v
  · simp only [ite_eq_left h]
    have harr : arrowBasis Q (K:=K) (Q.reverse e.arrow) * arrowBasis Q e.arrow=tokenBasis Q β := by
      simpa only [Q.reverse_reverse,Q.source_reverse,e.target] using
        (arrowBasis_reverse Q (K:=K) (Q.reverse e.arrow))
    rw [harr]
    rw [← pathBasis_token,pathBasis_coordinates,ite_eq_left rfl,one_smul]
  · simp only [ite_eq_right h,MulZeroClass.mul_zero,coordinates_zero,zero_smul]

noncomputable def adjacentTestSecondPivot (hn:∀ a,Q.source a≠Q.target a)
    (E:BasedComplex Q (K:=K) I) {α β:V} (e:SimpleEdge Q α β) :
    BlockPivot Q ((adjacentTestFirstPivot Q hn E e).reduced Q) where
  coefficient := 1
  nonzero := one_ne_zero
  color _ := rfl
  cochain u := by
    change (E.placement u.1).cochain-1=(E.placement u.1).cochain-1-1+1
    omega
  internal u := by
    change (E.placement u.1).internal+Path.length u.2.val+2=
      (E.placement u.1).internal+Path.length u.2.val+1+1
    omega
  entry u v := by
    rw [adjacentTest_first_reduced_entry,adjacentTest_second_pivot_entry]
    simp only [one_smul]
    rfl

omit [DecidableEq I] in
lemma adjacentTest_retained_to_second_target (hn:∀ a,Q.source a≠Q.target a)
    (E:BasedComplex Q (K:=K) I) {α β:V} (e:SimpleEdge Q α β)
    (u:TestIndex Q E.placement α) (v:TestIndex Q E.placement β) :
    (normalizedAdjacentTest Q hn E e).differential
      (.inr (.inr (.inr (.inr u)))) (.inr (.inr (.inr (.inl v))))=0 := by
  change (pathCoordinates Q (K:=K) (_ * evaluationMatrix Q (E.positiveTwist Q β).placement α
    ⟨.inr u.1,u.2⟩ (.inl v)) _) • vertexId Q β=0
  simp only [evaluationMatrix,Sum.inr_ne_inl,↓reduceIte,MulZeroClass.mul_zero,coordinates_zero,zero_smul]

omit [DecidableEq I] in
lemma adjacentTest_retained_entry (hn:∀ a,Q.source a≠Q.target a)
    (E:BasedComplex Q (K:=K) I) {α β:V} (e:SimpleEdge Q α β)
    (u v:TestIndex Q E.placement α) :
    (normalizedAdjacentTest Q hn E e).differential
      (.inr (.inr (.inr (.inr u)))) (.inr (.inr (.inr (.inr v))))=
      -(testMatrix Q E.placement E.placement α E.differential u v • vertexId Q (K:=K) β) := by
  change (pathCoordinates Q (K:=K) (pathBasis Q (e.reverse Q).corner.val *
    (-(testMatrix Q E.placement E.placement α E.differential u v • vertexId Q (K:=K) α)))
      (e.reverse Q).corner.val) • vertexId Q β=_
  rw [_root_.mul_neg,mul_smul,cornerPath_right]
  simp only [map_neg,Pi.neg_apply,coordinates_smul,pathBasis_coordinates,ite_true, if_true,
    _root_.mul_one,neg_smul]

lemma adjacentTest_second_reduced_differential (hn:∀ a,Q.source a≠Q.target a)
    (E:BasedComplex Q (K:=K) I) {α β:V} (e:SimpleEdge Q α β)
    (u v:TestIndex Q E.placement α) :
    ((adjacentTestSecondPivot Q hn E e).reduced Q).differential u v=
      -(testMatrix Q E.placement E.placement α E.differential u v • vertexId Q (K:=K) β) := by
  rw [BlockPivot.reduced_differential]
  simp only [adjacentTest_first_reduced_entry,adjacentTest_retained_to_second_target,
    smul_zero,MulZeroClass.zero_mul,Finset.sum_const_zero,sub_zero,adjacentTest_retained_entry]

noncomputable def adjacentTestReduction (hn:∀ a,Q.source a≠Q.target a)
    (E:BasedComplex Q (K:=K) I) {α β:V} (e:SimpleEdge Q α β) :
    HomotopyEquivalence Q (((E.positiveTwist Q β).positiveTwist Q α).testComplex Q β)
      ((adjacentTestSecondPivot Q hn E e).reduced Q) :=
  ((((E.positiveTwist Q β).positiveTwist Q α).testComplex Q β).reindexHomotopyEquivalence Q
    (adjacentTestIndexEquiv Q hn E e)).trans Q
      (((adjacentTestFirstPivot Q hn E e).reductionEquivalence Q).trans Q
        ((adjacentTestSecondPivot Q hn E e).reductionEquivalence Q))

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Quivers_Level
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.instAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag

variable {V A K I J L : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V]

namespace BasedComplex

variable [Fintype I] [Fintype J] [Fintype L]

lemma minimal_differential_level_bound (E : BasedComplex Q (K := K) I)
    (hE : E.IsMinimal Q) (i j : I) (h : E.differential i j ≠ 0) :
    (E.placement j).level ≤ (E.placement i).level := by
  have h := E.differential_level Q hE h
  omega

noncomputable def Map.pureLayer {E : BasedComplex Q (K := K) I}
    {F : BasedComplex Q (K := K) J} (f : Map Q E F)
    (hE : E.IsMinimal Q) (hF : F.IsMinimal Q) (d : ℤ) :
    Map Q (E.pureLayer Q hE d) (F.pureLayer Q hF d) where
  matrix := atLevel Q E.placement F.placement f.matrix d
  entries := ⟨fun i j => f.entries.1 i.val j.val, fun i j => f.entries.2 i.val j.val⟩
  degree := fun i j => f.degree i.val j.val
  commute := by
    change atLevel Q E.placement E.placement E.differential d *
        atLevel Q E.placement F.placement f.matrix d =
      atLevel Q E.placement F.placement f.matrix d *
        atLevel Q F.placement F.placement F.differential d
    rw [← atLevel_mul Q _ _ _ _ _ d (E.minimal_differential_level_bound Q hE)
      (map_level_bound Q f), ← atLevel_mul Q _ _ _ _ _ d (map_level_bound Q f)
      (F.minimal_differential_level_bound Q hF), f.commute]

lemma atLevel_homotopy_boundary (E : BasedComplex Q (K := K) I) (hE : E.IsMinimal Q)
    (H : Matrix I I (Q.Zigzag K)) (hH : MapDegree Q E.placement E.placement (-1) 0 H)
    (d : ℤ) : atLevel Q E.placement E.placement
      (E.differential * H + H * E.differential) d = 0 := by
  classical
  have hbound (i j : I) (h : H i j ≠ 0) :
      (E.placement j).level ≤ (E.placement i).level := by
    have hb := mapDegree_level_bound Q hH h
    omega
  rw [atLevel_add, atLevel_mul Q _ _ _ _ _ d
      (E.minimal_differential_level_bound Q hE) hbound,
    atLevel_mul Q _ _ _ _ _ d hbound (E.minimal_differential_level_bound Q hE),
    atLevel_degree_neg Q _ _ _ _ hH, Matrix.zero_mul, Matrix.mul_zero, add_zero]

noncomputable def HomotopyEquivalence.pureLayer [DecidableEq I] [DecidableEq J]
    {E : BasedComplex Q (K := K) I} {F : BasedComplex Q (K := K) J}
    (h : HomotopyEquivalence Q E F) (hE : E.IsMinimal Q) (hF : F.IsMinimal Q) (d : ℤ) :
    ChainIsomorphism Q (E.pureLayer Q hE d) (F.pureLayer Q hF d) where
  forward := h.forward.pureLayer Q hE hF d
  backward := h.backward.pureLayer Q hF hE d
  sourceEquation := by
    change atLevel Q _ _ h.forward.matrix d * atLevel Q _ _ h.backward.matrix d = _
    rw [← atLevel_mul Q _ _ _ _ _ d (map_level_bound Q h.forward)
      (map_level_bound Q h.backward), h.sourceEquation, atLevel_add,
      E.atLevel_homotopy_boundary Q hE h.sourceHomotopy h.sourceDegree,
      add_zero, atLevel_identity]
    rfl
  targetEquation := by
    change atLevel Q _ _ h.backward.matrix d * atLevel Q _ _ h.forward.matrix d = _
    rw [← atLevel_mul Q _ _ _ _ _ d (map_level_bound Q h.backward)
      (map_level_bound Q h.forward), h.targetEquation, atLevel_add,
      F.atLevel_homotopy_boundary Q hF h.targetHomotopy h.targetDegree,
      add_zero, atLevel_identity]
    rfl

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_HomSpace
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag

variable {V A K I J : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype A] [DecidableEq V]

namespace BasedComplex

variable [Fintype I] [Fintype J]

lemma homDifferential_mem (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (n v : ℤ)
    {f : Matrix I J (Q.Zigzag K)} (hf : f ∈ homSpace Q E F n v) :
    homDifferential Q E F n f ∈ homSpace Q E F (n + 1) v := by
  change ProjectiveEntries Q E.placement F.placement
      (E.differential * f - cochainSign (K := K) n • (f * F.differential)) ∧
    MapDegree Q E.placement F.placement (n + 1) v
      (E.differential * f - cochainSign (K := K) n • (f * F.differential))
  rw [sub_eq_add_neg]
  constructor
  · exact projectiveEntries_add Q (projectiveEntries_mul Q E.entries hf.1)
      (projectiveEntries_neg Q (projectiveEntries_smul Q _
        (projectiveEntries_mul Q hf.1 F.entries)))
  · have h₁ := mapDegree_mul Q E.degree hf.2
    have h₂ := mapDegree_mul Q hf.2 F.degree
    simp only [zero_add, add_zero] at h₁ h₂
    rw [add_comm 1 n] at h₁
    exact mapDegree_add Q h₁ (mapDegree_neg Q (mapDegree_smul Q _ h₂))

lemma homSpace_pure_total_degree_lower (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) {l k n v : ℤ}
    (hE : ∀ i, (E.placement i).level = l)
    (hF : ∀ j, (F.placement j).level = k)
    (h : n + v < k - l) : homSpace Q E F n v = ⊥ := by
  apply le_antisymm _ bot_le
  intro f hf
  change f = 0
  apply Matrix.ext
  intro i j
  by_contra he
  have hh := mapDegree_level_bound Q hf.2 he
  rw [hE i, hF j] at hh
  omega

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_HomSpacePairing
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def homSpacePairing (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (n v : ℤ) :
    homSpace Q E F n v →ₗ[K] homSpace Q F E (-n) (2-v) →ₗ[K] K where
  toFun f :=
    { toFun := fun g => supertrace Q E (f.val * g.val)
      map_add' g h := by
        change supertrace Q E (f.val * (g.val+h.val)) = _
        rw [Matrix.mul_add, map_add]
      map_smul' r g := by
        change supertrace Q E (f.val * (r • g.val)) = _
        rw [Matrix.mul_smul, map_smul]; rfl }
  map_add' f g := by
    ext h
    change supertrace Q E ((f.val+g.val)*h.val) = _
    rw [Matrix.add_mul, map_add]
    rfl
  map_smul' r f := by
    ext g
    change supertrace Q E ((r • f.val)*g.val) = _
    rw [Matrix.smul_mul, map_smul]
    rfl

lemma homSpacePairing_separatingLeft (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (n v : ℤ)
    (f : homSpace Q E F n v) (h : ∀ g, homSpacePairing Q E F n v f g = 0) : f = 0 := by
  classical
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  apply (pathCoordinates Q).injective
  funext p
  change pathCoordinates Q (f.val i j) p = pathCoordinates Q 0 p
  rw [coordinates_zero]
  by_contra hp
  have hcorner := coordinates_corner Q (f.property.1.1 i j) (f.property.1.2 i j) hp
  have hc : (F.placement j).cochain = (E.placement i).cochain + n := by
    by_contra hh
    exact hp (by rw [(f.property.2 i j).1 hh, coordinates_zero])
  have hl : Path.length p = v + (E.placement i).internal - (F.placement j).internal := by
    by_contra hh
    exact hp ((coordinates_homogeneous Q _ _).mp (f.property.2 i j).2 p hh)
  let z := pathBasis Q (K := K) (Path.dual Q p)
  have hz : Matrix.single j i z ∈ homSpace Q F E (-n) (2-v) := by
    constructor
    · apply projectiveEntries_single Q
      · simpa only [z, ← hcorner.2, ← Path.source_dual Q p] using
          pathBasis_left Q (K := K) (Path.dual Q p)
      · simpa only [z, ← hcorner.1, ← Path.target_dual Q p] using
          pathBasis_right Q (K := K) (Path.dual Q p)
    · apply mapDegree_single Q
      · omega
      · have hh := pathBasis_homogeneous Q (K := K) (Path.dual Q p)
        rw [Path.length_dual Q, hl] at hh
        convert hh using 1 <;> first | (with_reducible_and_instances rfl) | (omega)
  have hh := h ⟨_, hz⟩
  change supertrace Q E (f.val * Matrix.single j i z) = 0 at hh
  rw [supertrace_mul_single Q, ← coordinates_trace Q (f.val i j) p] at hh
  have hs : cochainSign (K := K) (E.placement i).cochain ≠ 0 := by
    intro he
    have := cochainSign_mul_self (K := K) (E.placement i).cochain
    rw [he, MulZeroClass.zero_mul] at this
    exact zero_ne_one this
  exact hp ((mul_eq_zero.mp hh).resolve_left hs)

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_HomSpaceDuality
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
variable {I J : Type*} [Fintype I] [Fintype J]

attribute [local instance] OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.zigzagFiniteDimensional
lemma homSpacePairing_separatingRight (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (n v : ℤ)
    (g : homSpace Q F E (-n) (2-v))
    (h : ∀ f, homSpacePairing Q E F n v f g = 0) : g = 0 := by
  apply homSpacePairing_separatingLeft Q F E (-n) (2-v) g
  intro f
  have hf : f.val ∈ homSpace Q E F n v := by
    simpa only [neg_neg, sub_sub_cancel] using f.property
  have hh := h ⟨f.val, hf⟩
  change supertrace Q E (f.val * g.val) = 0 at hh
  change supertrace Q F (g.val * f.val) = 0
  rw [supertrace_mul Q E F hf.2 g.val, hh, MulZeroClass.mul_zero]

instance homSpacePairing_perfect (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (n v : ℤ) :
    (homSpacePairing Q E F n v).IsPerfPair := by
  apply LinearMap.IsPerfPair.of_injective
  · apply LinearMap.ker_eq_bot.mp
    apply le_antisymm _ bot_le
    intro f hf
    change f = 0
    apply homSpacePairing_separatingLeft Q E F n v f
    intro g
    exact LinearMap.congr_fun hf g
  · apply LinearMap.ker_eq_bot.mp
    apply le_antisymm _ bot_le
    intro g hg
    change g = 0
    apply homSpacePairing_separatingRight Q E F n v g
    intro f
    exact LinearMap.congr_fun hg f

noncomputable def homSpaceDuality (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (n v : ℤ) :
    homSpace Q F E (-n) (2-v) ≃ₗ[K] Module.Dual K (homSpace Q E F n v) :=
  (homSpacePairing Q E F n v).flip.toPerfPair

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_DiagonalVertex
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V]

namespace BasedComplex
variable {I J : Type*} [Fintype I] [Fintype J]

omit [Fintype V] in
lemma homBoundary_positive (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (hE : E.IsMinimal Q) (hF : F.IsMinimal Q)
    (n v : ℤ) {f : Matrix I J (Q.Zigzag K)} (hf : f ∈ homBoundaries Q E F n v) :
    PositiveMatrix Q f := by
  obtain ⟨g, _, rfl⟩ := hf
  have hl := positiveMatrix_mul_right Q hE g
  have hr := positiveMatrix_mul_left Q g hF
  intro i j
  change ((E.differential * g) i j - cochainSign (K := K) (n - 1) • (g * F.differential) i j).vertex = 0
  change ((E.differential * g) i j).vertex - cochainSign (K := K) (n - 1) •
    ((g * F.differential) i j).vertex = 0
  rw [hl, hr, smul_zero, sub_zero]

omit [Fintype V] in
lemma diagonalVertex_boundary (E : BasedComplex Q (K := K) I) (hE : E.IsMinimal Q)
    (i : I) (n v : ℤ) {f : Matrix I I (Q.Zigzag K)}
    (hf : f ∈ homBoundaries Q E E n v) : diagonalVertex Q E i f = 0 := by
  exact congrFun (homBoundary_positive Q E E hE hE n v hf i i) (E.placement i).color

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_InverseHomMatrix
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

variable {V A K I J : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

omit [DecidableEq I] [DecidableEq J] in
lemma reverseHomMatrix_normalized (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J)
    (α : V) (n : ℤ) (f : Matrix I J (Q.Zigzag K)) :
    (negativeHomTransform Q (E.positiveTwist Q α) (F.positiveTwist Q α) α n
      (positiveHomTransform Q E F α n f)).submatrix
      (reverseTwistIndexEquiv Q hn E α) (reverseTwistIndexEquiv Q hn F α) =
      inverseHomMatrix Q E F α n f := by
  apply Matrix.ext
  intro i j
  rcases i with u | u | u | i | u <;> rcases j with v | v | v | j | v
  all_goals simp only [Matrix.submatrix_apply, reverseTwistIndexEquiv, Equiv.coe_fn_mk,
    inverseHomMatrix, positiveHomTransform, negativeHomTransform, Matrix.fromBlocks,
    Matrix.smul_apply,
    testTransform, scalarCornerMatrix, testMatrix, Matrix.of_apply,
    Matrix.zero_apply, Sum.elim_inl, Sum.elim_inr, MulZeroClass.mul_zero,
    coordinates_zero, zero_smul, smul_zero, selfCornerEquiv_false, selfCornerEquiv_true]
  all_goals simp only [mul_smul, coordinates_smul, pathBasis_vertex, pathBasis_token, smul_smul]
  all_goals (
    have ht : tokenBasis Q (K := K) α * vertexId Q α = tokenBasis Q α := by
      simpa only [Path.target, pathBasis_token] using
        (pathBasis_right Q (K := K) (.inr (.inr α)))
    simp only [vertexId_mul_self, ht, pathCoordinates_vertex, pathCoordinates_token]
    have hv : (vertexId Q (K := K) α).vertex α = 1 := by
      simp only [vertex_vertexId, Pi.single_eq_same]
    have htv : (tokenBasis Q (K := K) α).vertex α = 0 := rfl
    have htt : (tokenBasis Q (K := K) α).token α = 1 := by
      change (Pi.single α (1 : K) : V → K) α = 1
      exact Pi.single_eq_same α 1
    simp only [hv, htv, htt, token_vertexId, Pi.zero_apply,
      _root_.mul_one, MulZeroClass.mul_zero])
  all_goals first
    | exact zero_smul K (vertexId Q α)
    | exact congrArg (fun c : K => c • vertexId Q α)
        (by rw [← _root_.mul_assoc, cochainSign_mul_self]; exact _root_.one_mul _)

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_NegativeHomTransformReflect
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

variable {V A K I J : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

lemma negativeHomTransform_reflect_boundary (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J)
    (α : V) (n v : ℤ) {f : Matrix I J (Q.Zigzag K)}
    (hf : ProjectiveEntries Q E.placement F.placement f)
    (hb : negativeHomTransform Q E F α n f ∈
      homBoundaries Q (E.negativeTwist Q α) (F.negativeTwist Q α) n v) :
    f ∈ homBoundaries Q E F n v := by
  have h₁ := (positiveHomOperator Q (E.negativeTwist Q α)
    (F.negativeTwist Q α) α).map_boundaries n v hb
  have h₂ := (reindexHomOperator Q
    ((E.negativeTwist Q α).positiveTwist Q α)
    ((F.negativeTwist Q α).positiveTwist Q α)
    (inverseTwistIndexEquiv Q hn E α) (inverseTwistIndexEquiv Q hn F α)).map_boundaries n v h₁
  have h₃ := (sandwichHomOperator Q
    (normalizedInverseTwistHomotopyEquivalence Q hn E α).backward
    (normalizedInverseTwistHomotopyEquivalence Q hn F α).forward).map_boundaries n v h₂
  change inverseTwistInjection Q E α *
    (positiveHomTransform Q (E.negativeTwist Q α) (F.negativeTwist Q α) α n
      (negativeHomTransform Q E F α n f)).submatrix
      (inverseTwistIndexEquiv Q hn E α) (inverseTwistIndexEquiv Q hn F α) *
      inverseTwistProjection Q F α ∈ homBoundaries Q E F n v at h₃
  rw [inverseHomMatrix_normalized, inverseHomMatrix_extract Q E F α n hf] at h₃
  exact h₃

lemma positiveHomTransform_reflect_boundary (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J)
    (α : V) (n v : ℤ) {f : Matrix I J (Q.Zigzag K)}
    (hf : ProjectiveEntries Q E.placement F.placement f)
    (hb : positiveHomTransform Q E F α n f ∈
      homBoundaries Q (E.positiveTwist Q α) (F.positiveTwist Q α) n v) :
    f ∈ homBoundaries Q E F n v := by
  have h₁ := (negativeHomOperator Q (E.positiveTwist Q α)
    (F.positiveTwist Q α) α).map_boundaries n v hb
  have h₂ := (reindexHomOperator Q
    ((E.positiveTwist Q α).negativeTwist Q α)
    ((F.positiveTwist Q α).negativeTwist Q α)
    (reverseTwistIndexEquiv Q hn E α) (reverseTwistIndexEquiv Q hn F α)).map_boundaries n v h₁
  have h₃ := (sandwichHomOperator Q
    (normalizedReverseTwistHomotopyEquivalence Q hn E α).backward
    (normalizedReverseTwistHomotopyEquivalence Q hn F α).forward).map_boundaries n v h₂
  change reverseTwistInjection Q E α *
    (negativeHomTransform Q (E.positiveTwist Q α) (F.positiveTwist Q α) α n
      (positiveHomTransform Q E F α n f)).submatrix
      (reverseTwistIndexEquiv Q hn E α) (reverseTwistIndexEquiv Q hn F α) *
      reverseTwistProjection Q F α ∈ homBoundaries Q E F n v at h₃
  rw [reverseHomMatrix_normalized, reverseHomMatrix_extract Q E F α n hf] at h₃
  exact h₃

lemma negativeHomCohomology_injective (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J)
    (α : V) (n v : ℤ) :
    Function.Injective ((negativeHomOperator Q E F α).onCohomology n v) := by
  apply HomOperator.onCohomology_injective
  intro f hf hb
  exact negativeHomTransform_reflect_boundary Q hn E F α n v hf.1.1 hb

lemma positiveHomCohomology_injective (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J)
    (α : V) (n v : ℤ) :
    Function.Injective ((positiveHomOperator Q E F α).onCohomology n v) := by
  apply HomOperator.onCohomology_injective
  intro f hf hb
  exact positiveHomTransform_reflect_boundary Q hn E F α n v hf.1.1 hb

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_HomDimension
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag
universe u
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

namespace BasedComplex
variable {I J I' J' : Type*} [Fintype I] [Fintype J] [Fintype I'] [Fintype J']
  [DecidableEq I] [DecidableEq J] [DecidableEq I'] [DecidableEq J']

lemma positiveTwist_homDimension (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J)
    (α : V) (n v : ℤ) :
    homDimension Q (E.positiveTwist Q α) (F.positiveTwist Q α) n v = homDimension Q E F n v := by
  apply le_antisymm
  · have h := LinearMap.finrank_le_finrank_of_injective
      (negativeHomCohomology_injective Q hn (E.positiveTwist Q α) (F.positiveTwist Q α) α n v)
    change homDimension Q (E.positiveTwist Q α) (F.positiveTwist Q α) n v ≤
      homDimension Q ((E.positiveTwist Q α).negativeTwist Q α)
        ((F.positiveTwist Q α).negativeTwist Q α) n v at h
    rw [(negative_positive_homotopyEquivalence Q hn E α).homDimension_eq Q
      (negative_positive_homotopyEquivalence Q hn F α)] at h
    exact h
  · exact LinearMap.finrank_le_finrank_of_injective (positiveHomCohomology_injective Q hn E F α n v)

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_HomDetector
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V]
variable {I J : Type*} [Fintype I] [Fintype J]

lemma boundary_of_homDimension_zero (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (n v : ℤ)
    (hd : homDimension Q E F n v = 0)
    {f : Matrix I J (Q.Zigzag K)} (hf : f ∈ homCycles Q E F n v) :
    f ∈ homBoundaries Q E F n v := by
  have : Subsingleton (homCohomology Q E F n v) :=
    (Module.finrank_zero_iff.mp hd)
  have hz : (Submodule.Quotient.mk (⟨f, hf⟩ : homCycles Q E F n v) :
      homCohomology Q E F n v) = 0 := Subsingleton.elim _ _
  exact (Submodule.Quotient.mk_eq_zero
    ((homBoundaries Q E F n v).comap (homCycles Q E F n v).subtype)).mp hz

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_HomStep
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def homStep (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (n m v : ℤ) (hm : m = n+1) :
    homSpace Q E F n v →ₗ[K] homSpace Q E F m v :=
  (homDifferential Q E F n).restrict fun _ hf =>
    hm ▸ homDifferential_mem Q E F n v hf

noncomputable def homCycleKernelEquiv (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (n m v : ℤ) (hm : m = n+1) :
    homCycles Q E F n v ≃ₗ[K] LinearMap.ker (homStep Q E F n m v hm) where
  toFun f := ⟨⟨f.val, f.property.1⟩, Subtype.ext f.property.2⟩
  invFun f := ⟨f.val.val, f.val.property, congrArg Subtype.val f.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_HomInternalSupport
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def totalHomDimension (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (t : ℤ) : ℕ :=
  ∑ v ∈ homInternalSupport Q E F, homDimension Q E F (t-v) v

noncomputable def totalChainDimension (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (t : ℤ) : ℕ :=
  ∑ v ∈ homInternalSupport Q E F, Module.finrank K (homSpace Q E F (t-v) v)

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_ExtendLayer
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype A] [DecidableEq V]

namespace BasedComplex
variable {I J : Type*} [Fintype I] [Fintype J]

lemma extendLayer_homSpace (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (hE : E.IsMinimal Q) (hF : F.IsMinimal Q)
    (l k n v : ℤ)
    {f : Matrix {i // (E.placement i).level = l} {j // (F.placement j).level = k} (Q.Zigzag K)}
    (hf : f ∈ homSpace Q (E.pureLayer Q hE l) (F.pureLayer Q hF k) n v) :
    extendLayer Q E F l k f ∈ homSpace Q E F n v := by
  constructor
  · constructor <;> intro i j
    · simp only [extendLayer_entry]
      split_ifs with hi hj
      · exact hf.1.1 ⟨i, hi⟩ ⟨j, hj⟩
      · exact MulZeroClass.mul_zero _
      · exact MulZeroClass.mul_zero _
    · simp only [extendLayer_entry]
      split_ifs with hi hj
      · exact hf.1.2 ⟨i, hi⟩ ⟨j, hj⟩
      · exact MulZeroClass.zero_mul _
      · exact MulZeroClass.zero_mul _
  · intro i j
    simp only [extendLayer_entry]
    split_ifs with hi hj
    · exact hf.2 ⟨i, hi⟩ ⟨j, hj⟩
    · exact ⟨fun _ => rfl, homogeneous_zero Q _⟩
    · exact ⟨fun _ => rfl, homogeneous_zero Q _⟩

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Quivers_CoefficientMatrix
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype A] [DecidableEq V]
variable {I J : Type*} [Fintype I] [Fintype J]

namespace BasedComplex

lemma matrixZero_homDifferential (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (hE : E.IsMinimal Q) (hF : F.IsMinimal Q)
    (n : ℤ) (f : Matrix I J (Q.Zigzag K)) :
    matrixZero Q (homDifferential Q E F n f) = 0 := by
  change matrixZero Q (E.differential * f - cochainSign (K := K) n • (f * F.differential)) = 0
  rw [map_sub, map_smul, matrixZero_mul, matrixZero_mul,
    matrixZero_eq_zero Q hE, matrixZero_eq_zero Q hF,
    Matrix.zero_mul, Matrix.mul_zero, smul_zero, sub_zero]

lemma matrixZero_boundary (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (hE : E.IsMinimal Q) (hF : F.IsMinimal Q)
    (n v : ℤ) {f : Matrix I J (Q.Zigzag K)} (hf : f ∈ homBoundaries Q E F n v) :
    matrixZero Q f = 0 := by
  obtain ⟨g, _, rfl⟩ := hf
  exact matrixZero_homDifferential Q E F hE hF (n-1) g

lemma coefficient_eq_zero_of_same_differential [Fintype V]
    (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J)
    (hE : E.IsMinimal Q) (hF : F.IsMinimal Q) (n v : ℤ)
    (hd : homDimension Q E F n v = 0)
    {f g : Matrix I J (Q.Zigzag K)}
    (hf : f ∈ homSpace Q E F n v) (hg : g ∈ homSpace Q E F n v)
    (h₀ : CoefficientMatrix Q f) (h₁ : LinearMatrix Q g)
    (he : homDifferential Q E F n f = homDifferential Q E F n g) : f = 0 := by
  have hc : f - g ∈ homCycles Q E F n v := by
    refine ⟨Submodule.sub_mem _ hf hg, ?_⟩
    change homDifferential Q E F n (f - g) = 0
    rw [map_sub, he, sub_self]
  have hb := boundary_of_homDimension_zero Q E F n v hd hc
  have hz := matrixZero_boundary Q E F hE hF n v hb
  rw [map_sub, matrixZero_eq_self Q h₀, matrixZero_linear Q h₁, sub_zero] at hz
  exact hz

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Quivers_PathTwo
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype A] [DecidableEq V]

variable {I J L : Type*}

namespace BasedComplex
variable [Fintype I] [Fintype J]

noncomputable def tokenHomDifferential (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (n : ℤ) :
    Matrix I J (Q.Zigzag K) →ₗ[K] Matrix I J (Q.Zigzag K) :=
  homDifferential Q E F n - linearHomDifferential Q E F n

lemma tokenHomDifferential_apply (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (hE : E.IsMinimal Q) (hF : F.IsMinimal Q)
    (n : ℤ) (f : Matrix I J (Q.Zigzag K)) :
    tokenHomDifferential Q E F n f = matrixTwo Q E.differential * f -
      cochainSign (K := K) n • (f * matrixTwo Q F.differential) := by
  change (E.differential * f - cochainSign (K := K) n • (f * F.differential)) -
    (matrixOne Q E.differential * f - cochainSign (K := K) n • (f * matrixOne Q F.differential)) = _
  conv_lhs =>
    arg 1
    rw [← positive_matrix_decomposition Q hE, ← positive_matrix_decomposition Q hF]
  simp only [Matrix.add_mul, Matrix.mul_add, smul_add]
  abel

lemma homDifferential_eq_linear_add_token (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (n : ℤ) (f : Matrix I J (Q.Zigzag K)) :
    homDifferential Q E F n f =
      linearHomDifferential Q E F n f + tokenHomDifferential Q E F n f := by
  change homDifferential Q E F n f = linearHomDifferential Q E F n f +
    (homDifferential Q E F n f - linearHomDifferential Q E F n f)
  abel

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Quivers_PathTwoSelf
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype A] [DecidableEq V]

variable {I J L : Type*}

namespace BasedComplex
variable [Fintype I] [Fintype J]

lemma token_boundary_primitive (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (hE : LinearMatrix Q E.differential)
    (hF : LinearMatrix Q F.differential) (n v : ℤ)
    {f : Matrix I J (Q.Zigzag K)}
    (h₂ : ∀ i j, (f i j).vertex = 0 ∧ (f i j).arrow = 0)
    (hf : f ∈ homBoundaries Q E F n v) :
    ∃ g ∈ homSpace Q E F (n-1) v, LinearMatrix Q g ∧
      homDifferential Q E F (n-1) g = f := by
  obtain ⟨g, hg, rfl⟩ := hf
  refine ⟨matrixOne Q g, ⟨matrixOne_entries Q hg.1, matrixOne_degree Q hg.2⟩,
    fun _ _ => ⟨rfl, rfl⟩, ?_⟩
  have hfix : matrixTwo Q (homDifferential Q E F (n-1) g) = homDifferential Q E F (n-1) g := by
    apply Matrix.ext
    intro i j
    exact pathTwo_eq_self Q (h₂ i j).1 (h₂ i j).2
  rw [← hfix]
  change E.differential * matrixOne Q g -
    cochainSign (K := K) (n-1) • (matrixOne Q g * F.differential) =
    matrixTwo Q (E.differential * g - cochainSign (K := K) (n-1) • (g * F.differential))
  rw [map_sub, map_smul, matrixTwo_mul_linear_left Q hE, matrixTwo_mul_linear_right Q _ hF]

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Quivers_VertexLinear
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype A] [DecidableEq V]
variable {I J L : Type*}

namespace BasedComplex
variable [Fintype I] [Fintype J]

lemma tokenHomDifferential_tokenMatrix (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (hE : E.IsMinimal Q) (hF : F.IsMinimal Q)
    (n : ℤ) (f : Matrix I J (Q.Zigzag K)) :
    TokenMatrix Q (tokenHomDifferential Q E F n f) := by
  rw [tokenHomDifferential_apply Q E F hE hF]
  exact tokenMatrix_sub Q (tokenMatrix_matrixTwo_mul Q _ _)
    (tokenMatrix_smul Q _ (tokenMatrix_mul_matrixTwo Q _ _))

lemma homDifferential_tokenMatrix (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (hE : E.IsMinimal Q) (hF : F.IsMinimal Q)
    (n : ℤ) {f : Matrix I J (Q.Zigzag K)} (hf : TokenMatrix Q f) :
    homDifferential Q E F n f = 0 := by
  rw [← matrixTwo_eq_self Q hf]
  change E.differential * matrixTwo Q f - cochainSign (K := K) n •
    (matrixTwo Q f * F.differential) = 0
  rw [positive_mul_matrixTwo Q hE, matrixTwo_mul_positive Q _ hF, smul_zero, sub_zero]

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_PureHomSpaceHomogeneous
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.linearMap_pathBasis _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_base _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_left _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_right _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.corner_val _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_reverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype A] [DecidableEq V]
variable {I J : Type*} [Fintype I] [Fintype J]

lemma pure_homSpace_coefficient (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) {l k n v : ℤ}
    (hE : ∀ i, (E.placement i).level = l) (hF : ∀ j, (F.placement j).level = k)
    (h : n + v = k-l) {f : Matrix I J (Q.Zigzag K)}
    (hf : f ∈ homSpace Q E F n v) : CoefficientMatrix Q f := by
  intro i j
  have hh := pure_homSpace_homogeneous Q E F hE hF (r := 0) (by omega) hf i j
  exact ⟨hh.2.1 (by norm_num), hh.2.2 (by norm_num)⟩

lemma pure_coefficient_boundaries_zero (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) {l k n v : ℤ}
    (hE : ∀ i, (E.placement i).level = l) (hF : ∀ j, (F.placement j).level = k)
    (h : n + v = k-l) : homBoundaries Q E F n v = ⊥ := by
  apply le_antisymm _ bot_le
  intro f hf
  obtain ⟨g, hg, rfl⟩ := hf
  rw [homSpace_pure_total_degree_lower Q E F hE hF (by omega)] at hg
  have hg' : g = 0 := hg
  rw [hg', map_zero]
  exact Submodule.zero_mem _

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_LeftMatrix
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype A] [DecidableEq V]
variable {I J L : Type*} [Fintype I] [Fintype J] [Fintype L]

lemma pureMap_coefficient {E : BasedComplex Q (K := K) I}
    {F : BasedComplex Q (K := K) J} (f : Map Q E F) (q : ℤ)
    (hE : ∀ i, (E.placement i).level = q) (hF : ∀ j, (F.placement j).level = q) :
    CoefficientMatrix Q f.matrix :=
  pure_homSpace_coefficient Q E F hE hF (by omega) ⟨f.entries, f.degree⟩

omit [Fintype L] in
lemma pureMap_mul_support {E : BasedComplex Q (K := K) I}
    {F : BasedComplex Q (K := K) J} (f : Map Q E F) (q : ℤ)
    (hE : ∀ i, (E.placement i).level = q) (hF : ∀ j, (F.placement j).level = q)
    (U : Set V) (hU : ∀ j, (F.placement j).color ∈ U)
    (g : Matrix J L (Q.Zigzag K)) (i : I) (j : L)
    (hi : (E.placement i).color ∉ U) : (f.matrix * g) i j = 0 := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro t _
  rw [coefficientMap_row_support Q f (pureMap_coefficient Q f q hE hF) U hU i t hi,
    MulZeroClass.zero_mul]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_RestrictLayer
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype A] [DecidableEq V]

namespace BasedComplex
variable {I J : Type*} [Fintype I] [Fintype J]

lemma restrictLayer_homSpace (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (hE : E.IsMinimal Q) (hF : F.IsMinimal Q)
    (l k n v : ℤ) {f : Matrix I J (Q.Zigzag K)} (hf : f ∈ homSpace Q E F n v) :
    restrictLayer Q E F l k f ∈ homSpace Q (E.pureLayer Q hE l) (F.pureLayer Q hF k) n v :=
  ⟨⟨fun i j => hf.1.1 i.val j.val, fun i j => hf.1.2 i.val j.val⟩,
    fun i j => hf.2 i.val j.val⟩

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_DifferentialMulExtendLayer
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype A] [DecidableEq V]
variable {I J : Type*} [Fintype I] [Fintype J]

lemma differential_mul_extendLayer (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (hE : E.IsMinimal Q) (l k : ℤ)
    {f : Matrix {i // (E.placement i).level = l} {j // (F.placement j).level = k} (Q.Zigzag K)}
    (hf : LinearMatrix Q f) :
    E.differential * extendLayer Q E F l k f =
      extendLayer Q E F l k ((show Matrix {i // (E.placement i).level = l} {i // (E.placement i).level = l} (Q.Zigzag K) from (E.pureLayer Q hE l).differential) * f) := by
  classical
  apply Matrix.ext
  intro i j
  rw [Matrix.mul_apply, extendLayer_entry]
  split_ifs with hi hj
  · change (∑ t, E.differential i t * extendLayer Q E F l k f t j) =
      ∑ t : {i // (E.placement i).level = l}, E.differential i t * f t ⟨j, hj⟩
    symm
    apply Fintype.sum_of_injective Subtype.val Subtype.val_injective
    · intro t ht
      have hh : (E.placement t).level ≠ l := fun h => ht ⟨⟨t, h⟩, rfl⟩
      rw [extendLayer_entry, dite_eq_right hh, MulZeroClass.mul_zero]
    · intro t
      rw [extendLayer_entry, dite_eq_left t.property, dite_eq_left hj]
  · apply Finset.sum_eq_zero
    intro t _
    rw [extendLayer_entry]
    split_ifs <;> exact MulZeroClass.mul_zero _
  · apply Finset.sum_eq_zero
    intro t _
    rw [extendLayer_entry]
    split_ifs with ht hj
    · apply tokenOnly_mul_positive Q (hE i t) _ (hf ⟨t, ht⟩ ⟨j, hj⟩).1
      apply differential_arrow_level Q E
      intro he
      exact hi (he ▸ ht)
    · exact MulZeroClass.mul_zero _
    · exact MulZeroClass.mul_zero _

lemma extendLayer_mul_differential (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (hF : F.IsMinimal Q) (l k : ℤ)
    {f : Matrix {i // (E.placement i).level = l} {j // (F.placement j).level = k} (Q.Zigzag K)}
    (hf : LinearMatrix Q f) :
    extendLayer Q E F l k f * F.differential =
      extendLayer Q E F l k (f * (show Matrix {j // (F.placement j).level = k} {j // (F.placement j).level = k} (Q.Zigzag K) from (F.pureLayer Q hF k).differential)) := by
  classical
  apply Matrix.ext
  intro i j
  rw [Matrix.mul_apply, extendLayer_entry]
  split_ifs with hi hj
  · change (∑ t, extendLayer Q E F l k f i t * F.differential t j) =
      ∑ t : {j // (F.placement j).level = k}, f ⟨i, hi⟩ t * F.differential t j
    symm
    apply Fintype.sum_of_injective Subtype.val Subtype.val_injective
    · intro t ht
      have hh : (F.placement t).level ≠ k := fun h => ht ⟨⟨t, h⟩, rfl⟩
      rw [extendLayer_entry, dite_eq_left hi, dite_eq_right hh, MulZeroClass.zero_mul]
    · intro t
      rw [extendLayer_entry, dite_eq_left hi, dite_eq_left t.property]
  · apply Finset.sum_eq_zero
    intro t _
    rw [extendLayer_entry, dite_eq_left hi]
    split_ifs with ht
    · apply positive_mul_tokenOnly Q (hf ⟨i, hi⟩ ⟨t, ht⟩).1 (hF t j)
      apply differential_arrow_level Q F
      intro he
      exact hj (he.trans ht)
    · exact MulZeroClass.zero_mul _
  · apply Finset.sum_eq_zero
    intro t _
    rw [extendLayer_entry, dite_eq_right hi, MulZeroClass.zero_mul]

lemma homDifferential_extendLayer (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (hE : E.IsMinimal Q) (hF : F.IsMinimal Q)
    (l k n : ℤ)
    {f : Matrix {i // (E.placement i).level = l} {j // (F.placement j).level = k} (Q.Zigzag K)}
    (hf : LinearMatrix Q f) :
    homDifferential Q E F n (extendLayer Q E F l k f) = extendLayer Q E F l k
      (homDifferential Q (E.pureLayer Q hE l) (F.pureLayer Q hF k) n f) := by
  change E.differential * extendLayer Q E F l k f -
    cochainSign (K := K) n • (extendLayer Q E F l k f * F.differential) =
    extendLayer Q E F l k ((show Matrix {i // (E.placement i).level = l} {i // (E.placement i).level = l} (Q.Zigzag K) from (E.pureLayer Q hE l).differential) * f -
      cochainSign (K := K) n • (f * (show Matrix {j // (F.placement j).level = k} {j // (F.placement j).level = k} (Q.Zigzag K) from (F.pureLayer Q hF k).differential)))
  rw [map_sub, map_smul, differential_mul_extendLayer Q E F hE l k hf,
    extendLayer_mul_differential Q E F hF l k hf]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_MatrixOneMulExtend
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype A] [DecidableEq V]
variable {I J : Type*} [Fintype I] [Fintype J]

lemma matrixOne_mul_extendLayer (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (hE : E.IsMinimal Q) (l k : ℤ)
    {f : Matrix {i // (E.placement i).level = l} {j // (F.placement j).level = k} (Q.Zigzag K)}
    :
    matrixOne Q E.differential * extendLayer Q E F l k f =
      extendLayer Q E F l k ((show Matrix {i // (E.placement i).level = l} {i // (E.placement i).level = l} (Q.Zigzag K) from (E.pureLayer Q hE l).differential) * f) := by
  classical
  apply Matrix.ext
  intro i j
  rw [Matrix.mul_apply, extendLayer_entry]
  split_ifs with hi hj
  · change (∑ t, pathOne Q (E.differential i t) * extendLayer Q E F l k f t j) =
      ∑ t : {i // (E.placement i).level = l}, E.differential i t * f t ⟨j, hj⟩
    symm
    apply Fintype.sum_of_injective Subtype.val Subtype.val_injective
    · intro t ht
      have hh : (E.placement t).level ≠ l := fun h => ht ⟨⟨t, h⟩, rfl⟩
      rw [extendLayer_entry, dite_eq_right hh, MulZeroClass.mul_zero]
    · intro t
      rw [extendLayer_entry, dite_eq_left t.property, dite_eq_left hj]
      exact congrArg (fun z : Q.Zigzag K => z * f t ⟨j, hj⟩)
        (pathOne_eq_self Q (E.pureLayer_linear Q hE l ⟨i, hi⟩ t).1
          (E.pureLayer_linear Q hE l ⟨i, hi⟩ t).2).symm
  · apply Finset.sum_eq_zero
    intro t _
    rw [extendLayer_entry]
    split_ifs <;> exact MulZeroClass.mul_zero _
  · apply Finset.sum_eq_zero
    intro t _
    rw [extendLayer_entry]
    split_ifs with ht hj
    · have hz := differential_arrow_level Q E (i := i) (j := t) (fun he => hi (he ▸ ht))
      change pathOne Q (E.differential i t) * f ⟨t, ht⟩ ⟨j, hj⟩ = 0
      rw [pathOne_eq_zero Q hz, MulZeroClass.zero_mul]
    · exact MulZeroClass.mul_zero _
    · exact MulZeroClass.mul_zero _

lemma extendLayer_mul_matrixOne (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (hF : F.IsMinimal Q) (l k : ℤ)
    {f : Matrix {i // (E.placement i).level = l} {j // (F.placement j).level = k} (Q.Zigzag K)}
    :
    extendLayer Q E F l k f * matrixOne Q F.differential =
      extendLayer Q E F l k (f * (show Matrix {j // (F.placement j).level = k} {j // (F.placement j).level = k} (Q.Zigzag K) from (F.pureLayer Q hF k).differential)) := by
  classical
  apply Matrix.ext
  intro i j
  rw [Matrix.mul_apply, extendLayer_entry]
  split_ifs with hi hj
  · change (∑ t, extendLayer Q E F l k f i t * pathOne Q (F.differential t j)) =
      ∑ t : {j // (F.placement j).level = k}, f ⟨i, hi⟩ t * F.differential t j
    symm
    apply Fintype.sum_of_injective Subtype.val Subtype.val_injective
    · intro t ht
      have hh : (F.placement t).level ≠ k := fun h => ht ⟨⟨t, h⟩, rfl⟩
      rw [extendLayer_entry, dite_eq_left hi, dite_eq_right hh, MulZeroClass.zero_mul]
    · intro t
      rw [extendLayer_entry, dite_eq_left hi, dite_eq_left t.property]
      exact congrArg (fun z : Q.Zigzag K => f ⟨i, hi⟩ t * z)
        (pathOne_eq_self Q (F.pureLayer_linear Q hF k t ⟨j, hj⟩).1
          (F.pureLayer_linear Q hF k t ⟨j, hj⟩).2).symm
  · apply Finset.sum_eq_zero
    intro t _
    rw [extendLayer_entry, dite_eq_left hi]
    split_ifs with ht
    · have hz := differential_arrow_level Q F (i := t) (j := j) (fun he => hj (he.trans ht))
      change f ⟨i, hi⟩ ⟨t, ht⟩ * pathOne Q (F.differential t j) = 0
      rw [pathOne_eq_zero Q hz, MulZeroClass.mul_zero]
    · exact MulZeroClass.zero_mul _
  · apply Finset.sum_eq_zero
    intro t _
    rw [extendLayer_entry, dite_eq_right hi, MulZeroClass.zero_mul]

lemma linearHomDifferential_extendLayer (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (hE : E.IsMinimal Q) (hF : F.IsMinimal Q)
    (l k n : ℤ)
    (f : Matrix {i // (E.placement i).level = l} {j // (F.placement j).level = k} (Q.Zigzag K)) :
    linearHomDifferential Q E F n (extendLayer Q E F l k f) = extendLayer Q E F l k
      (homDifferential Q (E.pureLayer Q hE l) (F.pureLayer Q hF k) n f) := by
  change matrixOne Q E.differential * extendLayer Q E F l k f -
    cochainSign (K := K) n • (extendLayer Q E F l k f * matrixOne Q F.differential) =
    extendLayer Q E F l k ((show Matrix {i // (E.placement i).level = l} {i // (E.placement i).level = l} (Q.Zigzag K) from (E.pureLayer Q hE l).differential) * f -
      cochainSign (K := K) n • (f * (show Matrix {j // (F.placement j).level = k} {j // (F.placement j).level = k} (Q.Zigzag K) from (F.pureLayer Q hF k).differential)))
  rw [map_sub, map_smul, matrixOne_mul_extendLayer Q E F hE, extendLayer_mul_matrixOne Q E F hF]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_SecondaryLayer
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype A] [DecidableEq V]
variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def secondaryLayer (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (q d n : ℤ) :
    Matrix {i // (E.placement i).level = q} {j // (F.placement j).level = d} (Q.Zigzag K) →ₗ[K]
    Matrix {i // (E.placement i).level = q} {j // (F.placement j).level = d-1} (Q.Zigzag K) :=
  (restrictLayer Q E F q (d-1)).comp
    ((tokenHomDifferential Q E F n).comp (extendLayer Q E F q d))

lemma secondaryLayer_token (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (hE : E.IsMinimal Q) (hF : F.IsMinimal Q)
    (q d n : ℤ)
    (f : Matrix {i // (E.placement i).level = q} {j // (F.placement j).level = d} (Q.Zigzag K)) :
    TokenMatrix Q (secondaryLayer Q E F q d n f) := by
  intro i j
  exact tokenHomDifferential_tokenMatrix Q E F hE hF n (extendLayer Q E F q d f) i.val j.val

lemma capped_secondaryLayer_extension (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (hE : E.IsMinimal Q) (hF : F.IsMinimal Q)
    (U : Set V) (q d n : ℤ) (hcap : E.CappedOn Q U q)
    {f : Matrix {i // (E.placement i).level = q} {j // (F.placement j).level = d} (Q.Zigzag K)}
    (hs : ∀ i j, (E.placement i.val).color ∉ U → f i j = 0) :
    extendLayer Q E F q (d-1) (secondaryLayer Q E F q d n f) =
      tokenHomDifferential Q E F n (extendLayer Q E F q d f) := by
  change extendLayer Q E F q (d-1)
    (restrictLayer Q E F q (d-1)
      (tokenHomDifferential Q E F n (extendLayer Q E F q d f))) = _
  apply extend_restrictLayer Q E F q (d-1)
  intro i j hh
  rw [tokenHomDifferential_apply Q E F hE hF,
    capped_matrixTwo_mul_extend Q E F U q d hcap hs, zero_sub]
  change -(cochainSign (K := K) n •
    (extendLayer Q E F q d f * matrixTwo Q F.differential) i j) = 0
  rw [extend_mul_matrixTwo_support Q E F q d f i j hh, smul_zero, neg_zero]

lemma secondaryLayer_mem_cycles (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (hE : E.IsMinimal Q) (hF : F.IsMinimal Q)
    (q d n v : ℤ)
    {f : Matrix {i // (E.placement i).level = q} {j // (F.placement j).level = d} (Q.Zigzag K)}
    (hf : f ∈ homCycles Q (E.pureLayer Q hE q) (F.pureLayer Q hF d) n v) :
    secondaryLayer Q E F q d n f ∈
      homCycles Q (E.pureLayer Q hE q) (F.pureLayer Q hF (d-1)) (n+1) v := by
  have hlinear : linearHomDifferential Q E F n (extendLayer Q E F q d f) = 0 := by
    rw [linearHomDifferential_extendLayer Q E F hE hF q d n,
      show homDifferential Q (E.pureLayer Q hE q) (F.pureLayer Q hF d) n f = 0 from hf.2,
      map_zero]
  have hcomp : tokenHomDifferential Q E F n (extendLayer Q E F q d f) =
      homDifferential Q E F n (extendLayer Q E F q d f) := by
    rw [homDifferential_eq_linear_add_token, hlinear, zero_add]
  constructor
  · change restrictLayer Q E F q (d-1)
      (tokenHomDifferential Q E F n (extendLayer Q E F q d f)) ∈ _
    rw [hcomp]
    exact restrictLayer_homSpace Q E F hE hF q (d-1) (n+1) v
      (homDifferential_mem Q E F n v (extendLayer_homSpace Q E F hE hF q d n v hf.1))
  · change homDifferential Q (E.pureLayer Q hE q) (F.pureLayer Q hF (d-1)) (n+1)
      (secondaryLayer Q E F q d n f) = 0
    exact homDifferential_tokenMatrix Q _ _
      (fun i j => (E.pureLayer_linear Q hE q i j).1)
      (fun i j => (F.pureLayer_linear Q hF (d-1) i j).1) (n+1)
      (secondaryLayer_token Q E F hE hF q d n f)

lemma capped_secondary_kernel_zero [Fintype V]
    (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J)
    (hE : E.IsMinimal Q) (hF : F.IsMinimal Q) (U : Set V) (q d n v : ℤ)
    (hcap : E.CappedOn Q U q) (hd : homDimension Q E F n v = 0)
    {f : Matrix {i // (E.placement i).level = q} {j // (F.placement j).level = d} (Q.Zigzag K)}
    (hf : f ∈ homCycles Q (E.pureLayer Q hE q) (F.pureLayer Q hF d) n v)
    (h₀ : CoefficientMatrix Q f)
    (hs : ∀ i j, (E.placement i.val).color ∉ U → f i j = 0)
    (hb : secondaryLayer Q E F q d n f ∈
      homBoundaries Q (E.pureLayer Q hE q) (F.pureLayer Q hF (d-1)) (n+1) v) : f = 0 := by
  obtain ⟨g, hg, hlin, he⟩ := token_boundary_primitive Q
    (E.pureLayer Q hE q) (F.pureLayer Q hF (d-1))
    (E.pureLayer_linear Q hE q) (F.pureLayer_linear Q hF (d-1)) (n+1) v
    (secondaryLayer_token Q E F hE hF q d n f) hb
  have hn : n + 1 - 1 = n := by omega
  rw [hn] at hg he
  have hlinear : linearHomDifferential Q E F n (extendLayer Q E F q d f) = 0 := by
    rw [linearHomDifferential_extendLayer Q E F hE hF q d n,
      show homDifferential Q (E.pureLayer Q hE q) (F.pureLayer Q hF d) n f = 0 from hf.2,
      map_zero]
  have hfull : homDifferential Q E F n (extendLayer Q E F q d f) =
      homDifferential Q E F n (extendLayer Q E F q (d-1) g) := by
    rw [homDifferential_eq_linear_add_token Q E F n (extendLayer Q E F q d f),
      hlinear, zero_add, homDifferential_extendLayer Q E F hE hF q (d-1) n hlin, he,
      capped_secondaryLayer_extension Q E F hE hF U q d n hcap hs]
  have hz := coefficient_eq_zero_of_same_differential Q E F hE hF n v hd
    (extendLayer_homSpace Q E F hE hF q d n v hf.1)
    (extendLayer_homSpace Q E F hE hF q (d-1) n v hg)
    (extendLayer_coefficient Q E F q d h₀) (extendLayer_linear Q E F q (d-1) hlin) hfull
  have hh := congrArg (restrictLayer Q E F q d) hz
  rw [restrictLayer_extend, map_zero] at hh
  exact hh

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_RestrictExtendLayerMul
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype A] [DecidableEq V]
variable {I J : Type*} [Fintype I] [Fintype J]

lemma secondaryLayer_eq_target (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (hE : E.IsMinimal Q) (hF : F.IsMinimal Q)
    (U : Set V) (q d n : ℤ) (hcap : E.CappedOn Q U q)
    {f : Matrix {i // (E.placement i).level = q} {j // (F.placement j).level = d} (Q.Zigzag K)}
    (hs : ∀ i j, (E.placement i.val).color ∉ U → f i j = 0) :
    secondaryLayer Q E F q d n f = -(cochainSign (K := K) n •
      (f * restrictLayer Q F F d (d-1) (matrixTwo Q F.differential))) := by
  change restrictLayer Q E F q (d-1)
    (tokenHomDifferential Q E F n (extendLayer Q E F q d f)) = _
  rw [tokenHomDifferential_apply Q E F hE hF,
    capped_matrixTwo_mul_extend Q E F U q d hcap hs, zero_sub,
    map_neg, map_smul, restrict_extendLayer_mul]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_SummandSecondary
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype A] [DecidableEq V]
variable {I J T : Type*} [Fintype I] [Fintype J] [Fintype T]

noncomputable def summandSecondary (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (hE : E.IsMinimal Q)
    (M : BasedComplex Q (K := K) T) (q d n : ℤ)
    (ι : Map Q M (E.pureLayer Q hE q)) (π : Map Q (E.pureLayer Q hE q) M) :
    Matrix T {j // (F.placement j).level = d} (Q.Zigzag K) →ₗ[K]
      Matrix T {j // (F.placement j).level = d-1} (Q.Zigzag K) :=
  (leftMatrix Q ι.matrix).comp
    ((secondaryLayer Q E F q d n).comp (leftMatrix Q π.matrix))

lemma summandSecondary_cycles (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (hE : E.IsMinimal Q) (hF : F.IsMinimal Q)
    (M : BasedComplex Q (K := K) T) (q d n v : ℤ)
    (ι : Map Q M (E.pureLayer Q hE q)) (π : Map Q (E.pureLayer Q hE q) M)
    {f : Matrix T {j // (F.placement j).level = d} (Q.Zigzag K)}
    (hf : f ∈ homCycles Q M (F.pureLayer Q hF d) n v) :
    summandSecondary Q E F hE M q d n ι π f ∈
      homCycles Q M (F.pureLayer Q hF (d-1)) (n+1) v := by
  have hp : π.matrix * f ∈ homCycles Q (E.pureLayer Q hE q) (F.pureLayer Q hF d) n v := by
    simpa only [zero_add] using homCycles_mul Q (map_mem_homCycles Q π) hf
  change (show Matrix T {i // (E.placement i).level = q} (Q.Zigzag K) from ι.matrix) *
    secondaryLayer Q E F q d n (π.matrix * f) ∈ _
  simpa only [zero_add] using homCycles_mul Q (map_mem_homCycles Q ι)
    (secondaryLayer_mem_cycles Q E F hE hF q d n v hp)

lemma summandSecondary_kernel_zero [Fintype V] [DecidableEq T]
    (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J)
    (hE : E.IsMinimal Q) (hF : F.IsMinimal Q)
    (M : BasedComplex Q (K := K) T) (U : Set V) (q d n v : ℤ)
    (hM : ∀ i, (M.placement i).level = q) (hU : ∀ i, (M.placement i).color ∈ U)
    (ι : Map Q M (E.pureLayer Q hE q)) (π : Map Q (E.pureLayer Q hE q) M)
    (hret : ι.matrix * π.matrix = projectiveIdentity Q M.placement)
    (hcap : E.CappedOn Q U q) (hd : homDimension Q E F n v = 0)
    (hdeg : n+v = d-q)
    {f : Matrix T {j // (F.placement j).level = d} (Q.Zigzag K)}
    (hf : f ∈ homCycles Q M (F.pureLayer Q hF d) n v)
    (hb : summandSecondary Q E F hE M q d n ι π f ∈
      homBoundaries Q M (F.pureLayer Q hF (d-1)) (n+1) v) : f = 0 := by
  have hp : π.matrix * f ∈ homCycles Q (E.pureLayer Q hE q) (F.pureLayer Q hF d) n v := by
    simpa only [zero_add] using homCycles_mul Q (map_mem_homCycles Q π) hf
  have hs : ∀ i j, (E.placement i.val).color ∉ U → (π.matrix * f) i j = 0 := by
    intro i j hi
    exact pureMap_mul_support Q π q (fun i => i.property) hM U hU f i j hi
  have he : π.matrix * summandSecondary Q E F hE M q d n ι π f =
      secondaryLayer Q E F q d n (π.matrix * f) := by
    change π.matrix * ((show Matrix T {i // (E.placement i).level = q} (Q.Zigzag K) from ι.matrix) *
      secondaryLayer Q E F q d n (π.matrix * f)) = _
    rw [secondaryLayer_eq_target Q E F hE hF U q d n hcap hs]
    have hr : π.matrix * ι.matrix * π.matrix = π.matrix := by
      rw [Matrix.mul_assoc, hret]
      exact mul_projectiveIdentity Q π.entries
    calc
      _ = -(cochainSign (K := K) n • ((π.matrix * ι.matrix * π.matrix) * f *
        restrictLayer Q F F d (d-1) (matrixTwo Q F.differential))) := by
          simp only [Matrix.mul_neg, Matrix.mul_smul, Matrix.mul_assoc]
      _ = _ := by rw [hr]
  have hb' : secondaryLayer Q E F q d n (π.matrix * f) ∈
      homBoundaries Q (E.pureLayer Q hE q) (F.pureLayer Q hF (d-1)) (n+1) v := by
    rw [← he]
    simpa only [zero_add] using homCycle_mul_boundary Q (map_mem_homCycles Q π) hb
  have hz : π.matrix * f = 0 := capped_secondary_kernel_zero Q E F hE hF U q d n v hcap hd hp
    (pure_homSpace_coefficient Q _ _ (fun i => i.property) (fun j => j.property) hdeg hp.1) hs hb'
  calc
    f = ι.matrix * (π.matrix * f) := by
      rw [← Matrix.mul_assoc, hret]
      exact (projectiveIdentity_mul Q hf.1.1).symm
    _ = 0 := by rw [hz, Matrix.mul_zero]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_PureCoefficientCohomology
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype A] [DecidableEq V]
variable {I J T : Type*} [Fintype I] [Fintype J] [Fintype T]

noncomputable def pureCoefficientCohomology (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) {l k n v : ℤ}
    (hE : ∀ i, (E.placement i).level = l) (hF : ∀ j, (F.placement j).level = k)
    (h : n+v = k-l) : homCohomology Q E F n v ≃ₗ[K] homCycles Q E F n v :=
  Submodule.quotEquivOfEqBot _ (by
    rw [pure_coefficient_boundaries_zero Q E F hE hF h, Submodule.comap_bot]
    exact Submodule.ker_subtype _)

noncomputable def summandSecondaryOnCycles (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (hE : E.IsMinimal Q) (hF : F.IsMinimal Q)
    (M : BasedComplex Q (K := K) T) (q d n v : ℤ)
    (ι : Map Q M (E.pureLayer Q hE q)) (π : Map Q (E.pureLayer Q hE q) M) :
    homCycles Q M (F.pureLayer Q hF d) n v →ₗ[K]
      homCycles Q M (F.pureLayer Q hF (d-1)) (n+1) v :=
  (summandSecondary Q E F hE M q d n ι π).restrict fun _ hf =>
    summandSecondary_cycles Q E F hE hF M q d n v ι π hf

noncomputable def summandSecondaryClass (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (hE : E.IsMinimal Q) (hF : F.IsMinimal Q)
    (M : BasedComplex Q (K := K) T) (q d n v : ℤ)
    (ι : Map Q M (E.pureLayer Q hE q)) (π : Map Q (E.pureLayer Q hE q) M) :
    homCycles Q M (F.pureLayer Q hF d) n v →ₗ[K]
      homCohomology Q M (F.pureLayer Q hF (d-1)) (n+1) v :=
  ((homBoundaries Q M (F.pureLayer Q hF (d-1)) (n+1) v).comap
    (homCycles Q M (F.pureLayer Q hF (d-1)) (n+1) v).subtype).mkQ.comp
    (summandSecondaryOnCycles Q E F hE hF M q d n v ι π)

lemma summandSecondaryClass_injective [Fintype V] [DecidableEq T]
    (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J)
    (hE : E.IsMinimal Q) (hF : F.IsMinimal Q)
    (M : BasedComplex Q (K := K) T) (U : Set V) (q d n v : ℤ)
    (hM : ∀ i, (M.placement i).level = q) (hU : ∀ i, (M.placement i).color ∈ U)
    (ι : Map Q M (E.pureLayer Q hE q)) (π : Map Q (E.pureLayer Q hE q) M)
    (hret : ι.matrix * π.matrix = projectiveIdentity Q M.placement)
    (hcap : E.CappedOn Q U q) (hd : homDimension Q E F n v = 0)
    (hdeg : n+v = d-q) :
    Function.Injective (summandSecondaryClass Q E F hE hF M q d n v ι π) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro f hf
  change Submodule.Quotient.mk (summandSecondaryOnCycles Q E F hE hF M q d n v ι π f) = 0 at hf
  have hb := (Submodule.Quotient.mk_eq_zero _).mp hf
  change f = 0
  apply Subtype.ext
  exact summandSecondary_kernel_zero Q E F hE hF M U q d n v hM hU ι π hret hcap hd hdeg
    f.property hb

noncomputable def cappedSummandInjection [Fintype V] [DecidableEq T]
    (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J)
    (hE : E.IsMinimal Q) (hF : F.IsMinimal Q)
    (M : BasedComplex Q (K := K) T) (U : Set V) (q d n v : ℤ)
    (hM : ∀ i, (M.placement i).level = q) (hU : ∀ i, (M.placement i).color ∈ U)
    (ι : Map Q M (E.pureLayer Q hE q)) (π : Map Q (E.pureLayer Q hE q) M)
    (hret : ι.matrix * π.matrix = projectiveIdentity Q M.placement)
    (hcap : E.CappedOn Q U q) (hd : homDimension Q E F n v = 0)
    (hdeg : n+v = d-q) :
    { f : homCohomology Q M (F.pureLayer Q hF d) n v →ₗ[K]
      homCohomology Q M (F.pureLayer Q hF (d-1)) (n+1) v // Function.Injective f } :=
  ⟨ (summandSecondaryClass Q E F hE hF M q d n v ι π).comp
      (pureCoefficientCohomology Q M (F.pureLayer Q hF d) hM (fun i => i.property) hdeg).toLinearMap,
     (summandSecondaryClass_injective Q E F hE hF M U q d n v hM hU ι π hret hcap hd hdeg).comp
      (pureCoefficientCohomology Q M (F.pureLayer Q hF d) hM (fun i => i.property) hdeg).injective ⟩

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_CoefficientTopDual
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
variable {I J : Type*} [Fintype I] [Fintype J]

omit [Fintype V] [DecidableEq A] in
lemma topSocleMatrix_mem_homSpace (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) {l k : ℤ}
    (hE : ∀ i, (E.placement i).level = l) (hF : ∀ j, (F.placement j).level = k)
    (α : V) (c d : ℤ) {x : I → K} {y : J → K}
    (hx : x ∈ coefficientTopDual Q E α c) (hy : y ∈ coefficientSocle Q F α d) :
    topSocleMatrix Q α x y ∈ homSpace Q E F (d-c) (k-l-(d-c)) := by
  have hs i j : x i * y j ≠ 0 →
      (E.placement i).color = α ∧ (E.placement i).cochain = c ∧
      (F.placement j).color = α ∧ (F.placement j).cochain = d := by
    intro h
    obtain ⟨hi,hj⟩ := mul_ne_zero_iff.mp h
    exact ⟨not_ne_iff.mp (fun hh => hi (hx.1 i (Or.inl hh))),
      not_ne_iff.mp (fun hh => hi (hx.1 i (Or.inr hh))),
      not_ne_iff.mp (fun hh => hj (hy.1 j (Or.inl hh))),
      not_ne_iff.mp (fun hh => hj (hy.1 j (Or.inr hh)))⟩
  constructor
  · constructor
    · intro i j
      by_cases hh : x i * y j = 0
      · simp only [topSocleMatrix, hh, zero_smul, MulZeroClass.mul_zero]
      · rw [(hs i j hh).1]
        simp only [topSocleMatrix, mul_smul, vertexId_mul_self]
    · intro i j
      by_cases hh : x i * y j = 0
      · simp only [topSocleMatrix, hh, zero_smul, MulZeroClass.zero_mul]
      · rw [(hs i j hh).2.2.1]
        simp only [topSocleMatrix, smul_mul_assoc, vertexId_mul_self]
  · intro i j
    by_cases hh : x i * y j = 0
    · simp only [topSocleMatrix, hh, zero_smul]
      exact ⟨fun _ => trivial, ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩⟩
    · obtain ⟨_,hi,_,hj⟩ := hs i j hh
      constructor
      · intro h; exact (h (by omega)).elim
      · have hl := hE i
        have hk := hF j
        dsimp only [GeneratorPlacement.level] at hl hk
        have heq : k-l-(d-c)+(E.placement i).internal-(F.placement j).internal = 0 := by omega
        rw [heq]
        exact homogeneous_smul Q (homogeneous_vertexId Q α) _

omit [Fintype V] [DecidableEq A] [Fintype J] in
lemma differential_topSocleMatrix (E : BasedComplex Q (K := K) I) {l : ℤ}
    (hE : ∀ i, (E.placement i).level = l) (α : V) (c : ℤ)
    {x : I → K} (hx : x ∈ coefficientTopDual Q E α c) (y : J → K) :
    E.differential * topSocleMatrix Q α x y = 0 := by
  have hlin := pure_differential_linear Q E hE
  apply Matrix.ext
  intro i j
  apply ext
  · ext β
    simp only [Matrix.mul_apply, vertex_sum, Finset.sum_apply, vertex_mul,
      (hlin i _).1, Pi.zero_apply, MulZeroClass.zero_mul, Finset.sum_const_zero]
    rfl
  · ext a
    simp only [Matrix.mul_apply, arrow_sum, Finset.sum_apply, arrow_mul, Pi.add_apply,
      leftScale, rightScale, (hlin i _).1, Pi.zero_apply, MulZeroClass.zero_mul, zero_add,
      topSocleMatrix, vertex_smul, Pi.smul_apply, smul_eq_mul, vertexId_eval]
    by_cases ha : Q.target a = α
    · simp only [ha, ← _root_.mul_assoc, ← Finset.sum_mul, hx.2 i a,
        MulZeroClass.zero_mul]
      rfl
    · simp only [ite_eq_right ha, MulZeroClass.mul_zero, Finset.sum_const_zero]
      rfl
  · ext β
    simp only [Matrix.mul_apply, token_sum, Finset.sum_apply, token_mul,
      (hlin i _).1, (hlin i _).2, Pi.zero_apply, MulZeroClass.zero_mul,
      zero_add, topSocleMatrix, arrow_smul, arrow_vertexId, smul_zero, backtrack,
      Pi.zero_apply, MulZeroClass.mul_zero, ite_self, Finset.sum_const_zero]
    rfl

omit [Fintype V] [DecidableEq A] [Fintype I] in
lemma topSocleMatrix_differential (F : BasedComplex Q (K := K) J) {k : ℤ}
    (hF : ∀ j, (F.placement j).level = k) (α : V) (d : ℤ)
    (x : I → K) {y : J → K} (hy : y ∈ coefficientSocle Q F α d) :
    topSocleMatrix Q α x y * F.differential = 0 := by
  have hlin := pure_differential_linear Q F hF
  apply Matrix.ext
  intro i j
  apply ext
  · ext β
    simp only [Matrix.mul_apply, vertex_sum, Finset.sum_apply, vertex_mul,
      (hlin _ j).1, Pi.zero_apply, MulZeroClass.mul_zero, Finset.sum_const_zero]
    rfl
  · ext a
    simp only [Matrix.mul_apply, arrow_sum, Finset.sum_apply, arrow_mul, Pi.add_apply,
      leftScale, rightScale, (hlin _ j).1, Pi.zero_apply, MulZeroClass.mul_zero, add_zero,
      topSocleMatrix, vertex_smul, Pi.smul_apply, smul_eq_mul, vertexId_eval]
    by_cases ha : Q.source a = α
    · simp only [ite_eq_left ha, _root_.mul_one, _root_.mul_assoc, ← Finset.mul_sum, hy.2 j a ha,
        MulZeroClass.mul_zero]
      rfl
    · simp only [ite_eq_right ha, MulZeroClass.mul_zero, MulZeroClass.zero_mul, Finset.sum_const_zero]
      rfl
  · ext β
    simp only [Matrix.mul_apply, token_sum, Finset.sum_apply, token_mul,
      (hlin _ j).1, (hlin _ j).2, Pi.zero_apply, MulZeroClass.mul_zero,
      zero_add, topSocleMatrix, arrow_smul, arrow_vertexId, smul_zero, backtrack,
      Pi.zero_apply, MulZeroClass.zero_mul, ite_self, Finset.sum_const_zero]
    rfl

omit [Fintype V] [DecidableEq A] in
lemma topSocleMatrix_mem_homCycles (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) {l k : ℤ}
    (hE : ∀ i, (E.placement i).level = l) (hF : ∀ j, (F.placement j).level = k)
    (α : V) (c d : ℤ) {x : I → K} {y : J → K}
    (hx : x ∈ coefficientTopDual Q E α c) (hy : y ∈ coefficientSocle Q F α d) :
    topSocleMatrix Q α x y ∈ homCycles Q E F (d-c) (k-l-(d-c)) := by
  refine ⟨topSocleMatrix_mem_homSpace Q E F hE hF α c d hx hy, ?_⟩
  change E.differential * topSocleMatrix Q α x y -
    cochainSign (K := K) (d-c) • (topSocleMatrix Q α x y * F.differential) = 0
  rw [differential_topSocleMatrix Q E hE α c hx,
    topSocleMatrix_differential Q F hF α d x hy, smul_zero, sub_self]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_HomDimension2
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

lemma classPositiveTwist_homDimension (hn : ∀ a, Q.source a ≠ Q.target a)
    (α : V) (n v : ℤ) (E F : FiniteHomotopyClass Q (K := K)) :
    classHomDimension Q n v (classPositiveTwist Q α E) (classPositiveTwist Q α F) =
      classHomDimension Q n v E F := by
  induction E using Quotient.inductionOn with | _ E =>
    induction F using Quotient.inductionOn with | _ F =>
      exact positiveTwist_homDimension Q hn E.complex F.complex α n v

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_HomDimensionZeroHom
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

omit [DecidableEq A] in
lemma homDimension_zero_of_homSpace_zero {I J : Type*} [Fintype I] [Fintype J]
    (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J) (n v : ℤ)
    (h : homSpace Q E F n v = ⊥) : homDimension Q E F n v = 0 := by
  have hd := homDimension_le_homSpace Q E F n v
  rw [h] at hd
  simp only [finrank_bot] at hd
  exact Nat.eq_zero_of_le_zero hd

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_MinimalModel
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

omit [DecidableEq A] in
lemma minimalClassModel_homDimension (x y : FiniteHomotopyClass Q (K := K)) (n v : ℤ) :
    homDimension Q (minimalClassModel Q x).complex (minimalClassModel Q y).complex n v =
      classHomDimension Q n v x y := by
  change classHomDimension Q n v (Quotient.mk _ (minimalClassModel Q x))
    (Quotient.mk _ (minimalClassModel Q y)) = _
  rw [minimalClassModel_class, minimalClassModel_class]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_HomPath
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.Path.dual_dual _root_.OAI.HarmonicArtin.ReversibleQuiver.Path.source_dual _root_.OAI.HarmonicArtin.ReversibleQuiver.Path.target_dual _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.linearMap_pathBasis _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_base _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_left _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_right _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.corner_val _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_reverse _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.selfCornerEquiv_false _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.selfCornerEquiv_true
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
variable {I J : Type*} [Fintype I] [Fintype J]

omit [Fintype V] [DecidableEq A] in
lemma homPath_of_coordinate_ne_zero (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (n v : ℤ) (f : homSpace Q E F n v)
    (i : I) (j : J) (p : Path V A) (hp : pathCoordinates Q (f.val i j) p ≠ 0) :
    Path.source Q p = (E.placement i).color ∧ Path.target Q p = (F.placement j).color ∧
    (F.placement j).cochain = (E.placement i).cochain+n ∧
    Path.length p = v+(E.placement i).internal-(F.placement j).internal := by
  have hc := coordinates_corner Q (f.property.1.1 i j) (f.property.1.2 i j) hp
  refine ⟨hc.1, hc.2, ?_, ?_⟩
  · by_contra hh
    exact hp (by rw [(f.property.2 i j).1 hh, coordinates_zero])
  · by_contra hh
    exact hp ((coordinates_homogeneous Q _ _).mp (f.property.2 i j).2 p hh)

noncomputable def homPathBasis [DecidableEq I] [DecidableEq J]
    (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J)
    (n v : ℤ) (t : HomPath Q E F n v) : homSpace Q E F n v :=
  ⟨Matrix.single t.val.1 t.val.2.1 (pathBasis Q t.val.2.2), by
    constructor
    · apply projectiveEntries_single Q
      · simpa only [t.property.1] using pathBasis_left Q (K := K) t.val.2.2
      · simpa only [t.property.2.1] using pathBasis_right Q (K := K) t.val.2.2
    · apply mapDegree_single Q _ _ _ _ _ _ _ t.property.2.2.1
      simpa only [t.property.2.2.2] using pathBasis_homogeneous Q (K := K) t.val.2.2⟩

noncomputable def homCoordinates (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (n v : ℤ) :
    homSpace Q E F n v →ₗ[K] (HomPath Q E F n v → K) where
  toFun f t := pathCoordinates Q (f.val t.val.1 t.val.2.1) t.val.2.2
  map_add' f g := by
    funext t
    exact congrFun ((pathCoordinates Q).map_add (f.val t.val.1 t.val.2.1) (g.val t.val.1 t.val.2.1)) t.val.2.2
  map_smul' c f := by
    funext t
    exact (pathCoordinates Q).map_smul c (f.val t.val.1 t.val.2.1) |> congrFun <| t.val.2.2

omit [Fintype V] [DecidableEq A] in
lemma homCoordinates_injective (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (n v : ℤ) : Function.Injective (homCoordinates Q E F n v) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro f hf
  change f = 0
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  apply (pathCoordinates Q).injective
  funext p
  change pathCoordinates Q (f.val i j) p = pathCoordinates Q 0 p
  rw [coordinates_zero]
  by_contra hp
  let t : HomPath Q E F n v := ⟨(i,j,p), homPath_of_coordinate_ne_zero Q E F n v f i j p hp⟩
  have hh := congrFun hf t
  dsimp only [homCoordinates, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, t] at hh
  exact hp hh

lemma homPathBasis_coordinates [DecidableEq I] [DecidableEq J]
    (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J)
    (n v : ℤ) (s t : HomPath Q E F n v) :
    homCoordinates Q E F n v (homPathBasis Q E F n v s) t = if s=t then 1 else 0 := by
  classical
  dsimp only [homCoordinates, homPathBasis, LinearMap.coe_mk, AddHom.coe_mk]
  change pathCoordinates Q (Matrix.single s.val.1 s.val.2.1 (pathBasis Q (K := K) s.val.2.2)
    t.val.1 t.val.2.1) t.val.2.2 = _
  by_cases hi : s.val.1=t.val.1
  · by_cases hj : s.val.2.1=t.val.2.1
    · rw [hi, hj, Matrix.single_apply_same, pathBasis_coordinates]
      congr 1
      apply propext
      constructor
      · intro hp
        apply Subtype.ext
        exact Prod.ext hi (Prod.ext hj hp)
      · intro h
        exact congrArg (fun x : HomPath Q E F n v => x.val.2.2) h
    · have hs : s ≠ t := fun h => hj (congrArg (fun x : HomPath Q E F n v => x.val.2.1) h)
      simp only [Matrix.single_apply, hi, true_and, ite_eq_right hj, coordinates_zero,
        ite_eq_right hs]
  · have hs : s ≠ t := fun h => hi (congrArg (fun x : HomPath Q E F n v => x.val.1) h)
    simp only [Matrix.single_apply, hi, false_and, ite_false, if_false, coordinates_zero, ite_eq_right hs]

lemma homCoordinates_surjective (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (n v : ℤ) : Function.Surjective (homCoordinates Q E F n v) := by
  classical
  intro f
  refine ⟨∑ t, f t • homPathBasis Q E F n v t, ?_⟩
  ext t
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    homPathBasis_coordinates]
  simp

noncomputable def homCoordinatesEquiv (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (n v : ℤ) :
    homSpace Q E F n v ≃ₗ[K] (HomPath Q E F n v → K) :=
  LinearEquiv.ofBijective (homCoordinates Q E F n v)
    ⟨homCoordinates_injective Q E F n v, homCoordinates_surjective Q E F n v⟩

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Quivers_TokenTestVector
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.linearMap_pathBasis _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_base _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_left _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_right _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.corner_val _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_reverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag
variable {V A K I : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A] [Fintype I]

namespace BasedComplex

lemma tokenTestVector_top (E : BasedComplex Q (K := K) I) {l : ℤ}
    (hE : ∀ i, (E.placement i).level=l) (α:V) (c:ℤ)
    {x : I → K} (hx : x ∈ coefficientTopDual Q E α c) :
    tokenTestVector Q E.placement α x ∈ topTestCycles Q E α c := by
  constructor
  · intro i hi
    change x i.1 * pathCoordinates Q (tokenBasis Q α) i.2.val=0
    by_cases hc : (E.placement i.1).cochain=c
    · have hl : Path.length i.2.val≠2 := fun h => hi ⟨hc,h⟩
      rw [token_coordinates,ite_eq_right (fun he => hl (by rw [← he]; rfl)),MulZeroClass.mul_zero]
    · rw [hx.1 i.1 (Or.inr hc),MulZeroClass.zero_mul]
  · funext i
    rw [tokenTestVector_differential Q E α x (fun i h => hx.1 i (Or.inl h))]
    rcases i with ⟨i,⟨p,hs,ht⟩⟩
    rcases p with v|a|v
    · apply Finset.sum_eq_zero
      intro j hj
      change x j * (E.differential i j).token v=0
      rw [(pure_differential_linear Q E hE i j).2]
      simp
    · simpa only [Path.dual,pathCoordinates_arrow,mul_comm,Pi.zero_apply] using hx.2 i (Q.reverse a)
    · apply Finset.sum_eq_zero
      intro j hj
      change x j * (E.differential i j).vertex v=0
      rw [(pure_differential_linear Q E hE i j).1]
      simp

noncomputable def coefficientTopTestEquiv (E : BasedComplex Q (K := K) I) {l : ℤ}
    (hE : ∀ i, (E.placement i).level=l) (α:V) (c:ℤ) :
    coefficientTopDual Q E α c ≃ₗ[K] topTestCycles Q E α c where
  toFun x := ⟨tokenTestVector Q E.placement α x.val,tokenTestVector_top Q E hE α c x.property⟩
  invFun y := ⟨sumTokenTest Q E.placement α y.val,sumTokenTest_top Q E α c y.property⟩
  left_inv x := by
    apply Subtype.ext
    exact sumTokenTest_unit Q E.placement α x.val (fun i h => x.property.1 i (Or.inl h))
  right_inv y := by
    apply Subtype.ext
    exact tokenTestVector_sum Q E.placement α c y.val y.property.1
  map_add' x y := by apply Subtype.ext; exact map_add _ _ _
  map_smul' r x := by apply Subtype.ext; exact map_smul _ _ _

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Quivers_UnitTestVector
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.linearMap_pathBasis _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_base _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_left _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_right _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.corner_val _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_reverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag
variable {V A K I : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A] [Fintype I]

namespace BasedComplex

lemma unitTestVector_socle (E : BasedComplex Q (K := K) I) {l : ℤ}
    (hE : ∀ i, (E.placement i).level=l) (α:V) (c:ℤ)
    {x : I → K} (hx : x ∈ coefficientSocle Q E α c) :
    unitTestVector Q E.placement α x ∈ socleTestCycles Q E α c := by
  constructor
  · intro i hi
    change x i.1 * pathCoordinates Q (vertexId Q α) i.2.val=0
    by_cases hc : (E.placement i.1).cochain=c
    · have hl : Path.length i.2.val≠0 := fun h => hi ⟨hc,h⟩
      rw [vertex_coordinates,ite_eq_right (fun he => hl (by rw [← he]; rfl)),MulZeroClass.mul_zero]
    · rw [hx.1 i.1 (Or.inr hc),MulZeroClass.zero_mul]
  · funext j
    rw [unitTestVector_differential Q E α x (fun i h => hx.1 i (Or.inl h))]
    rcases j with ⟨j,⟨p,hs,ht⟩⟩
    rcases p with v|a|v
    · apply Finset.sum_eq_zero
      intro i hi
      change x i * (E.differential i j).vertex v=0
      rw [(pure_differential_linear Q E hE i j).1]
      simp
    · exact hx.2 j a hs
    · apply Finset.sum_eq_zero
      intro i hi
      change x i * (E.differential i j).token v=0
      rw [(pure_differential_linear Q E hE i j).2]
      simp

noncomputable def coefficientSocleTestEquiv (E : BasedComplex Q (K := K) I) {l : ℤ}
    (hE : ∀ i, (E.placement i).level=l) (α:V) (c:ℤ) :
    coefficientSocle Q E α c ≃ₗ[K] socleTestCycles Q E α c where
  toFun x := ⟨unitTestVector Q E.placement α x.val,unitTestVector_socle Q E hE α c x.property⟩
  invFun y := ⟨sumUnitTest Q E.placement α y.val,sumUnitTest_socle Q E α c y.property⟩
  left_inv x := by
    apply Subtype.ext
    exact sumUnitTest_unit Q E.placement α x.val (fun i h => x.property.1 i (Or.inl h))
  right_inv y := by
    apply Subtype.ext
    exact unitTestVector_sum Q E.placement α c y.val y.property.1
  map_add' x y := by apply Subtype.ext; exact map_add _ _ _
  map_smul' r x := by apply Subtype.ext; exact map_smul _ _ _

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_PureSupportedCycles
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag
variable {V A K I J : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

namespace BasedComplex

omit [DecidableEq I] [DecidableEq J] in
lemma pureMap_test_support {E : BasedComplex Q (K := K) I}
    {F : BasedComplex Q (K := K) J} (f : Map Q E F) {l : ℤ}
    (hE : ∀ i, (E.placement i).level=l) (hF : ∀ j, (F.placement j).level=l)
    (α : V) (c n : ℤ) (i : TestIndex Q E.placement α) (j : TestIndex Q F.placement α)
    (h : testMatrix Q E.placement F.placement α f.matrix i j ≠ 0) :
    ((E.placement i.1).cochain=c ∧ Path.length i.2.val=n) ↔
      ((F.placement j.1).cochain=c ∧ Path.length j.2.val=n) := by
  have he : (F.placement j.1).cochain = (E.placement i.1).cochain := by
    by_contra hh
    apply h
    unfold testMatrix
    rw [(f.degree i.1 j.1).1 (by simpa only [add_zero] using hh),
      MulZeroClass.mul_zero,coordinates_zero]
  have hh := pure_homSpace_homogeneous Q E F hE hF (n := 0) (v := 0) (r := 0)
    (by omega) ⟨f.entries,f.degree⟩ i.1 j.1
  have hp := coordinates_mul_degree Q (pathBasis_homogeneous Q i.2.val) hh h
  have hlen : Path.length j.2.val = Path.length i.2.val := by simpa only [add_zero] using hp
  rw [he,hlen]

noncomputable def ChainIsomorphism.pureSupportedCycles
    {E : BasedComplex Q (K := K) I} {F : BasedComplex Q (K := K) J}
    (f : ChainIsomorphism Q E F) {l : ℤ}
    (hE : ∀ i, (E.placement i).level=l) (hF : ∀ j, (F.placement j).level=l)
    (α : V) (c n : ℤ) :
    ScalarCycles.supportedKernel (testMatrix Q E.placement E.placement α E.differential)
      (fun i => (E.placement i.1).cochain=c ∧ Path.length i.2.val=n) ≃ₗ[K]
    ScalarCycles.supportedKernel (testMatrix Q F.placement F.placement α F.differential)
      (fun i => (F.placement i.1).cochain=c ∧ Path.length i.2.val=n) := by
  apply ScalarCycles.conjugateEquiv _ _ _ _
    (testMatrix Q E.placement F.placement α f.forward.matrix)
    (testMatrix Q F.placement E.placement α f.backward.matrix)
  · exact pureMap_test_support Q f.forward hE hF α c n
  · exact pureMap_test_support Q f.backward hF hE α c n
  · rw [testMatrix_mul Q α _ f.forward.entries,f.sourceEquation,testMatrix_identity]
  · rw [testMatrix_mul Q α _ f.backward.entries,f.targetEquation,testMatrix_identity]
  · rw [testMatrix_mul Q α _ E.entries,testMatrix_mul Q α _ f.forward.entries,f.forward.commute]

noncomputable def ChainIsomorphism.pureDualSupportedCycles
    {E : BasedComplex Q (K := K) I} {F : BasedComplex Q (K := K) J}
    (f : ChainIsomorphism Q E F) {l : ℤ}
    (hE : ∀ i, (E.placement i).level=l) (hF : ∀ j, (F.placement j).level=l)
    (α : V) (c n : ℤ) :
    ScalarCycles.supportedKernel (testMatrix Q E.placement E.placement α E.differential).transpose
      (fun i => (E.placement i.1).cochain=c ∧ Path.length i.2.val=n) ≃ₗ[K]
    ScalarCycles.supportedKernel (testMatrix Q F.placement F.placement α F.differential).transpose
      (fun i => (F.placement i.1).cochain=c ∧ Path.length i.2.val=n) := by
  apply ScalarCycles.transposeConjugateEquiv _ _ _ _
    (testMatrix Q E.placement F.placement α f.forward.matrix)
    (testMatrix Q F.placement E.placement α f.backward.matrix)
  · exact pureMap_test_support Q f.forward hE hF α c n
  · exact pureMap_test_support Q f.backward hF hE α c n
  · rw [testMatrix_mul Q α _ f.forward.entries,f.sourceEquation,testMatrix_identity]
  · rw [testMatrix_mul Q α _ f.backward.entries,f.targetEquation,testMatrix_identity]
  · rw [testMatrix_mul Q α _ F.entries,testMatrix_mul Q α _ f.backward.entries,f.backward.commute]

noncomputable def ChainIsomorphism.coefficientSocle
    {E : BasedComplex Q (K := K) I} {F : BasedComplex Q (K := K) J}
    (f : ChainIsomorphism Q E F) {l : ℤ}
    (hE : ∀ i, (E.placement i).level=l) (hF : ∀ j, (F.placement j).level=l)
    (α : V) (c : ℤ) :
    coefficientSocle Q E α c ≃ₗ[K] coefficientSocle Q F α c :=
  ((coefficientSocleTestEquiv Q E hE α c).trans
    (f.pureSupportedCycles Q hE hF α c 0)).trans
    (coefficientSocleTestEquiv Q F hF α c).symm

noncomputable def ChainIsomorphism.coefficientTopDual
    {E : BasedComplex Q (K := K) I} {F : BasedComplex Q (K := K) J}
    (f : ChainIsomorphism Q E F) {l : ℤ}
    (hE : ∀ i, (E.placement i).level=l) (hF : ∀ j, (F.placement j).level=l)
    (α : V) (c : ℤ) :
    coefficientTopDual Q E α c ≃ₗ[K] coefficientTopDual Q F α c :=
  ((coefficientTopTestEquiv Q E hE α c).trans
    (f.pureDualSupportedCycles Q hE hF α c 2)).trans
    (coefficientTopTestEquiv Q F hF α c).symm

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_MinimalModelEquivalence
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
attribute [local instance] Classical.propDecidable
variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I : Type u} [Fintype I] [DecidableEq I]

noncomputable def classLayerTopDimension (d : ℤ) (α : V) (c : ℤ)
    (x : FiniteHomotopyClass Q (K := K)) : ℕ :=
  Module.finrank K (coefficientTopDual Q
    ((minimalClassModel Q x).complex.pureLayer Q (minimalClassModel_minimal Q x) d) α c)

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_NegativeAmplitudeCoreIndex
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

variable {V A K I : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I]

noncomputable def negativeAmplitudePivot (E : BasedComplex Q (K := K) I) (α : V) :
    BlockPivot Q (normalizedNegativeAmplitudeTwist Q E α) where
  coefficient := 1
  nonzero := one_ne_zero
  color i := i.property.symm
  cochain i := by change (E.placement i.val).cochain + 1 = (E.placement i.val).cochain + 1; rfl
  internal i := by change (E.placement i.val).internal + 2 - 2 = (E.placement i.val).internal; omega
  entry i j := by
    change coevaluationMatrix Q E.placement α i.val (tokenTest Q E α j) =
      (1 : K) • projectiveIdentity Q
        (fun j => (normalizedNegativeAmplitudeTwist Q E α).placement (.inl j)) i j
    simp only [coevaluationMatrix, tokenTest, Path.dual, pathBasis_vertex, one_smul,
      projectiveIdentity, Matrix.diagonal_apply]
    change (if i.val = j.val then vertexId Q (K := K) α else 0) =
      (if i = j then vertexId Q (E.placement i.val).color else 0)
    rw [i.property]
    simp only [Subtype.val_inj]

noncomputable def reducedNegativeAmplitudeTwist (E : BasedComplex Q (K := K) I) (α : V) :
    BasedComplex Q (K := K) (NegativeAmplitudeCoreIndex Q E α) :=
  (negativeAmplitudePivot Q E α).reduced Q

noncomputable def negativeAmplitudeTwistReduction (E : BasedComplex Q (K := K) I) (α : V) :
    HomotopyEquivalence Q (E.negativeTwist Q α) (reducedNegativeAmplitudeTwist Q E α) :=
  ((E.negativeTwist Q α).reindexHomotopyEquivalence Q (negativeAmplitudeIndexEquiv Q E α)).trans Q
    ((negativeAmplitudePivot Q E α).reductionEquivalence Q)

lemma reducedNegativeAmplitudeTwist_placement (E : BasedComplex Q (K := K) I) (α : V) :
    (reducedNegativeAmplitudeTwist Q E α).placement =
      fun i => match i with
      | .inl u => ⟨α, (E.placement u.val.1).cochain + 1,
          (E.placement u.val.1).internal + Path.length u.val.2.val - 2⟩
      | .inr i => E.placement i.val := by
  funext i
  cases i <;> rfl

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_ReducedNegativeAmplitudeTwist
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

universe u

variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I : Type u} [Fintype I] [DecidableEq I]

lemma reducedNegativeAmplitudeTwist_level (E : BasedComplex Q (K := K) I) (α : V)
    (k : NegativeAmplitudeCoreIndex Q E α) :
    ∃ i : I,
      ((reducedNegativeAmplitudeTwist Q E α).placement k).level = (E.placement i).level ∨
      (((reducedNegativeAmplitudeTwist Q E α).placement k).level = (E.placement i).level - 1 ∧
        ((reducedNegativeAmplitudeTwist Q E α).placement k).color = α) := by
  rw [reducedNegativeAmplitudeTwist_placement]
  rcases k with u | i
  · refine ⟨u.val.1, ?_⟩
    have h := Path.length_cases u.val.2.val
    have hn := u.property
    dsimp only [GeneratorPlacement.level]
    rcases h with h | h | h
    · exact Or.inr ⟨by omega, rfl⟩
    · exact Or.inl (by omega)
    · exact (hn h).elim
  · exact ⟨i.val, Or.inl rfl⟩

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_PlacedProjective
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.linearMap_pathBasis _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_base _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_left _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I J:Type u} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

omit [Fintype V] [DecidableEq A] [DecidableEq I] [DecidableEq J] in
lemma homSpace_zero_of_layer_gap (E:BasedComplex Q (K:=K) I) (F:BasedComplex Q (K:=K) J)
    (a b:ℤ) (ha:∀ i,(E.placement i).level≤a) (hb:∀ j,b≤(F.placement j).level)
    (hab:a<b) : homSpace Q E F 0 0=⊥ := by
  apply le_antisymm _ bot_le
  intro f hf
  change f=0
  apply Matrix.ext
  intro i j
  by_contra hn
  have hh:=mapDegree_level_bound Q hf.2 hn
  have hi:=ha i
  have hj:=hb j
  omega

omit [DecidableEq A] in
lemma classHomDimension_zero_of_layer_gap (x y:FiniteHomotopyClass Q (K:=K))
    (a b:ℤ) (ha:ClassUpperBound Q a x) (hb:ClassLowerBound Q b y) (hab:a<b) :
    classHomDimension Q 0 0 x y=0 := by
  rw [← minimalClassModel_homDimension Q x y 0 0]
  exact homDimension_zero_of_homSpace_zero Q _ _ 0 0
    (homSpace_zero_of_layer_gap Q _ _ a b ha hb hab)

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma bottom_last_row_zero (E:BasedComplex Q (K:=K) I) (hE:E.IsMinimal Q) (i:I)
    (hlo:∀ j,(E.placement i).level≤(E.placement j).level)
    (hlast:∀ j,(E.placement j).level=(E.placement i).level→
      (E.placement j).cochain≤(E.placement i).cochain) :
    ∀ j,E.differential i j=0 := by
  intro j
  by_contra h
  have hl:=differential_level Q E hE h
  have hn:=hlo j
  have he:(E.placement j).level=(E.placement i).level:=by rcases hl with hl|hl <;> omega
  have hc:=hlast j he
  have hd:(E.placement j).cochain=(E.placement i).cochain+1 :=
    Classical.not_not.mp (fun hz=>h ((E.degree i j).1 hz))
  omega

omit [DecidableEq A] in
lemma placedGenerator_homDimension_ne_zero (E:BasedComplex Q (K:=K) I)
    (hE:E.IsMinimal Q) (i:I) (hi:∀ j,E.differential i j=0) :
    homDimension Q (placedProjective Q (E.placement i)) E 0 0≠0 := by
  intro hz
  let f:=placedGeneratorMap Q E i hi
  obtain ⟨g,hg,he⟩:=boundary_of_homDimension_zero Q _ _ 0 0 hz (map_mem_homCycles Q f)
  have hv:=positiveMatrix_mul_left Q g hE
  have hzero:(homDifferential Q (placedProjective Q (E.placement i)) E (-1) g
      PUnit.unit i).vertex (E.placement i).color=0 := by
    change (((0:Matrix PUnit.{u+1} PUnit.{u+1} (Q.Zigzag K))*g-cochainSign (K:=K) (-1) • (g*E.differential)) PUnit.unit i).vertex _=0
    rw [Matrix.zero_mul,zero_sub]
    change -(cochainSign (K:=K) (-1) * ((g*E.differential) PUnit.unit i).vertex _)=0
    rw [hv PUnit.unit i]
    simp
  have he':homDifferential Q (placedProjective Q (E.placement i)) E (-1) g=f.matrix:=he
  rw [he'] at hzero
  change (projectiveIdentity Q (K:=K) E.placement i i).vertex (E.placement i).color=0 at hzero
  simp [projectiveIdentity,vertexId_eval] at hzero

omit [DecidableEq A] in
theorem classLowerBound_of_placed_vanishing (x:FiniteHomotopyClass Q (K:=K)) (d:ℤ)
    (h:∀ p:GeneratorPlacement V,p.level<d→
      classHomDimension Q 0 0 (classOfComplex Q (placedProjective Q p)) x=0) :
    ClassLowerBound Q d x := by
  classical
  let E:=minimalClassModel Q x
  intro i
  by_contra hi
  change ¬d≤(E.complex.placement i).level at hi
  obtain ⟨j,hj,hmin⟩:=Finset.exists_min_image (Finset.univ:Finset E.Index)
    (fun j=>(E.complex.placement j).level) ⟨i,Finset.mem_univ i⟩
  have hm:∀ k,(E.complex.placement j).level≤(E.complex.placement k).level:=
    fun k=>hmin k (Finset.mem_univ k)
  let T:=Finset.univ.filter (fun k:E.Index=>(E.complex.placement k).level=(E.complex.placement j).level)
  obtain ⟨k,hk,hmax⟩:=Finset.exists_max_image T (fun k=>(E.complex.placement k).cochain)
    ⟨j,by simp [T]⟩
  have hlev:(E.complex.placement k).level=(E.complex.placement j).level:=(Finset.mem_filter.mp hk).2
  have hd:(E.complex.placement k).level<d:=by have hh:=hm i; omega
  have hrow:=bottom_last_row_zero Q E.complex (minimalClassModel_minimal Q x) k
    (fun z=>by rw [hlev]; exact hm z)
    (fun z hz=>hmax z (by simp [T,hz,hlev]))
  apply placedGenerator_homDimension_ne_zero Q E.complex (minimalClassModel_minimal Q x) k hrow
  have he:classOfComplex Q E.complex=x:=minimalClassModel_class Q x
  change classHomDimension Q 0 0 (classOfComplex Q (placedProjective Q (E.complex.placement k)))
    (classOfComplex Q E.complex)=0
  rw [he]
  exact h _ hd

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_ScalarSupportedCochainShift
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.linearMap_pathBasis _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_base _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_left _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_right _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_reverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K I : Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I]

theorem positiveTwist_adjacent_test_exact_iff (hn:∀ a,Q.source a≠Q.target a)
    (E:BasedComplex Q (K:=K) I) {α β:V} (e:SimpleEdge Q α β) (l c:ℤ) :
    ScalarExactAt Q (((E.positiveTwist Q β).positiveTwist Q α).testComplex Q β) β l c ↔
      ScalarExactAt Q (E.testComplex Q α) α l (c+1) := by
  let F:=(adjacentTestSecondPivot Q hn E e).reduced Q
  have hl:∀ i,(F.placement i).level=((E.testComplex Q α).placement i).level := by
    intro i
    change (E.placement i.1).cochain-1+
      ((E.placement i.1).internal+Path.length i.2.val+1)=
      (E.placement i.1).cochain+((E.placement i.1).internal+Path.length i.2.val)
    omega
  have hc:∀ i,(F.placement i).cochain=((E.testComplex Q α).placement i).cochain-1:=fun _=>rfl
  have hd:F.differential.map (vertexHom Q β)=
      -(E.testComplex Q α).differential.map (vertexHom Q α) := by
    rw [testComplex_vertex_differential]
    apply Matrix.ext
    intro i j
    change (vertexHom Q β) (F.differential i j)= -testMatrix Q E.placement E.placement α E.differential i j
    rw [adjacentTest_second_reduced_differential]
    rw [map_neg]
    congr 1
    change (testMatrix Q E.placement E.placement α E.differential i j • vertexId Q (K:=K) β).vertex β=_
    simp
  rw [← scalarExact_cochainShift_iff Q (E.testComplex Q α) F α β hl hc hd l c]
  have h:=adjacentTestReduction Q hn E e
  constructor
  · exact fun h0=>scalarExact_transport Q _ _ (h.symm Q) β (fun _=>rfl) h0
  · exact fun h0=>scalarExact_transport Q _ _ h β (fun _=>rfl) h0

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_PositiveTwistOtherTest2
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K I : Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
theorem positiveTwist_other_test_exact
    (E:BasedComplex Q (K:=K) I) (α β:V) (hne:β≠α) (l c:ℤ)
    (hα:ScalarExactAt Q (E.testComplex Q α) α l (c+1))
    (hβ:ScalarExactAt Q (E.testComplex Q β) β l c) :
    ScalarExactAt Q ((E.positiveTwist Q α).testComplex Q β) β l c := by
  classical
  intro y hs hd
  let T:=(E.positiveTwist Q α).testComplex Q β
  let D:=T.differential.map (vertexHom Q β)
  have hx:∀ p:Zigzag.CornerPath Q β α,∃ z:TestIndex Q E.placement α→K,
      ScalarSupported Q (E.testComplex Q α) (l-1) c z ∧
      Matrix.vecMul z ((E.testComplex Q α).differential.map (vertexHom Q α))=
        fun u=>y (twistNewTestIndex Q E α β p u) := by
    intro p
    have hl:=corner_other_length Q hne p
    suffices hh:∃ z:TestIndex Q E.placement α→K,
        ScalarSupported Q (E.testComplex Q α) (l-1) (c+1-1) z ∧
        Matrix.vecMul z ((E.testComplex Q α).differential.map (vertexHom Q α))=
          fun u=>y (twistNewTestIndex Q E α β p u) from by
      simpa only [add_sub_cancel_right] using hh
    apply hα
    · intro i hi
      apply hs
      intro hh
      apply hi
      change (E.placement i.1).cochain+((E.placement i.1).internal+Path.length i.2.val)=l ∧
        (E.placement i.1).cochain=c+1
      change (E.placement i.1).cochain-1+
        ((E.placement i.1).internal+Path.length i.2.val+Path.length p.val)=l ∧
        (E.placement i.1).cochain-1=c at hh
      omega
    · rw [testComplex_vertex_differential Q E α]
      funext v
      have hh:=congrFun hd (twistNewTestIndex Q E α β p v)
      rw [testComplex_vertex_differential Q (E.positiveTwist Q α) β,
        twistTest_new_differential Q E α β y p v] at hh
      exact neg_eq_zero.mp hh
  choose z hzs hzd using hx
  let Z:TestIndex Q (E.positiveTwist Q α).placement β→K :=
    fun ⟨i,p⟩=>match i with
    | .inl u=> -z p u
    | .inr _=>0
  have hZs:ScalarSupported Q T (l-1) (c-1) Z := by
    rintro ⟨i,p⟩ hi
    rcases i with u|i
    · change -z p u=0
      rw [hzs p u,neg_zero]
      intro hh
      apply hi
      have hl:=corner_other_length Q hne p
      change (E.placement u.1).cochain-1+
        ((E.placement u.1).internal+Path.length u.2.val+Path.length p.val)=l-1 ∧
        (E.placement u.1).cochain-1=c-1
      change (E.placement u.1).cochain+
        ((E.placement u.1).internal+Path.length u.2.val)=l-1 ∧
        (E.placement u.1).cochain=c at hh
      omega
    · rfl
  have hZn:∀ p u,Matrix.vecMul Z D (twistNewTestIndex Q E α β p u)=
      y (twistNewTestIndex Q E α β p u) := by
    intro p u
    dsimp only [D,T]
    rw [testComplex_vertex_differential Q (E.positiveTwist Q α) β,
      twistTest_new_differential Q E α β Z p u]
    change -Matrix.vecMul (-(z p)) (testMatrix Q E.placement E.placement α E.differential) u=_
    rw [Matrix.neg_vecMul,Pi.neg_apply,neg_neg]
    have hh:=congrFun (hzd p) u
    rwa [testComplex_vertex_differential Q E α] at hh
  let r:=y-Matrix.vecMul Z D
  have hrn:∀ p u,r (twistNewTestIndex Q E α β p u)=0 := by
    intro p u
    change y _-Matrix.vecMul Z D _=0
    rw [hZn,sub_self]
  have hrs:ScalarSupported Q T l c r := by
    apply scalarSupported_sub Q T hs
    convert scalarSupported_map Q T T β T.differential T.entries T.degree hZs using 1 <;>
      omega
  have hrd:Matrix.vecMul r D=0 := by
    change Matrix.vecMul (y-Matrix.vecMul Z D) D=0
    rw [Matrix.sub_vecMul,hd,Matrix.vecMul_vecMul,scalarDifferential_square Q T β,
      Matrix.vecMul_zero,sub_self]
  have hro:Matrix.vecMul (fun u=>r (twistOldTestIndex Q E α β u))
      ((E.testComplex Q β).differential.map (vertexHom Q β))=0 := by
    rw [testComplex_vertex_differential Q E β]
    funext v
    have hh:=congrFun hrd (twistOldTestIndex Q E α β v)
    change Matrix.vecMul r (T.differential.map (vertexHom Q β)) _=0 at hh
    rw [testComplex_vertex_differential Q (E.positiveTwist Q α) β,
      twistTest_old_differential Q E α β r hrn v] at hh
    exact hh
  obtain ⟨w,hws,hwd⟩:=hβ (fun u=>r (twistOldTestIndex Q E α β u))
    (fun u hu=>hrs _ hu) hro
  let W:TestIndex Q (E.positiveTwist Q α).placement β→K :=
    fun ⟨i,p⟩=>match i with
    | .inl _=>0
    | .inr i=>w ⟨i,p⟩
  have hWn:∀ p u,W (twistNewTestIndex Q E α β p u)=0:=fun _ _=>rfl
  have hWs:ScalarSupported Q T (l-1) (c-1) W := by
    rintro ⟨i,p⟩ hi
    rcases i with u|i
    · rfl
    · exact hws ⟨i,p⟩ hi
  have hWd:Matrix.vecMul W D=r := by
    funext i
    obtain ⟨i,p⟩:=i
    rcases i with u|i
    · change Zigzag.CornerPath Q β α at p
      change Matrix.vecMul W (T.differential.map (vertexHom Q β))
        (twistNewTestIndex Q E α β p u)=r (twistNewTestIndex Q E α β p u)
      rw [hrn,testComplex_vertex_differential Q (E.positiveTwist Q α) β,
        twistTest_new_differential Q E α β W p u]
      change -Matrix.vecMul (0:TestIndex Q E.placement α→K) _ u=0
      rw [Matrix.zero_vecMul,Pi.zero_apply,neg_zero]
    · change Zigzag.CornerPath Q β (E.placement i).color at p
      change Matrix.vecMul W (T.differential.map (vertexHom Q β))
        (twistOldTestIndex Q E α β ⟨i,p⟩)=r (twistOldTestIndex Q E α β ⟨i,p⟩)
      rw [testComplex_vertex_differential Q (E.positiveTwist Q α) β,
        twistTest_old_differential Q E α β W hWn ⟨i,p⟩]
      have hh:=congrFun hwd ⟨i,p⟩
      rwa [testComplex_vertex_differential Q E β] at hh
  refine ⟨Z+W,?_,?_⟩
  · intro i hi
    change Z i+W i=0
    rw [hZs i hi,hWs i hi,add_zero]
  · change Matrix.vecMul (Z+W) D=y
    rw [Matrix.add_vecMul,hWd]
    change Matrix.vecMul Z D+(y-Matrix.vecMul Z D)=y
    abel

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_PositiveTwistOtherTest3
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K I : Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
theorem positiveTwist_other_test_exact_reflect
    (E:BasedComplex Q (K:=K) I) (α β:V) (hne:β≠α) (l c:ℤ)
    (hα:ScalarExactAt Q (E.testComplex Q α) α (l-1) c)
    (hT:ScalarExactAt Q ((E.positiveTwist Q α).testComplex Q β) β l c) :
    ScalarExactAt Q (E.testComplex Q β) β l c := by
  classical
  intro x hs hd
  let T:=(E.positiveTwist Q α).testComplex Q β
  let D:=T.differential.map (vertexHom Q β)
  let X:TestIndex Q (E.positiveTwist Q α).placement β→K :=
    fun ⟨i,p⟩=>match i with
    | .inl _=>0
    | .inr i=>x ⟨i,p⟩
  have hXn:∀ p u,X (twistNewTestIndex Q E α β p u)=0:=fun _ _=>rfl
  have hXs:ScalarSupported Q T l c X := by
    rintro ⟨i,p⟩ hi
    rcases i with u|i
    · rfl
    · exact hs ⟨i,p⟩ hi
  have hXd:Matrix.vecMul X D=0 := by
    funext v
    obtain ⟨i,p⟩:=v
    rcases i with u|i
    · change Zigzag.CornerPath Q β α at p
      change Matrix.vecMul X (T.differential.map (vertexHom Q β))
        (twistNewTestIndex Q E α β p u)=0
      rw [testComplex_vertex_differential Q (E.positiveTwist Q α) β,
        twistTest_new_differential Q E α β X p u]
      change -Matrix.vecMul (0:TestIndex Q E.placement α→K) _ u=0
      rw [Matrix.zero_vecMul,Pi.zero_apply,neg_zero]
    · change Zigzag.CornerPath Q β (E.placement i).color at p
      change Matrix.vecMul X (T.differential.map (vertexHom Q β))
        (twistOldTestIndex Q E α β ⟨i,p⟩)=0
      rw [testComplex_vertex_differential Q (E.positiveTwist Q α) β,
        twistTest_old_differential Q E α β X hXn ⟨i,p⟩]
      have hh:=congrFun hd ⟨i,p⟩
      rwa [testComplex_vertex_differential Q E β] at hh
  obtain ⟨z,hzs,hzd⟩:=hT X hXs hXd
  have hx:∀ p:Zigzag.CornerPath Q β α,∃ a:TestIndex Q E.placement α→K,
      ScalarSupported Q (E.testComplex Q α) (l-1-1) (c-1) a ∧
      Matrix.vecMul a ((E.testComplex Q α).differential.map (vertexHom Q α))=
        fun u=>z (twistNewTestIndex Q E α β p u) := by
    intro p
    have hl:=corner_other_length Q hne p
    apply hα
    · intro i hi
      apply hzs
      intro hh
      apply hi
      change (E.placement i.1).cochain+((E.placement i.1).internal+Path.length i.2.val)=l-1 ∧
        (E.placement i.1).cochain=c
      change (E.placement i.1).cochain-1+
        ((E.placement i.1).internal+Path.length i.2.val+Path.length p.val)=l-1 ∧
        (E.placement i.1).cochain-1=c-1 at hh
      omega
    · rw [testComplex_vertex_differential Q E α]
      funext v
      have hh:=congrFun hzd (twistNewTestIndex Q E α β p v)
      rw [testComplex_vertex_differential Q (E.positiveTwist Q α) β,
        twistTest_new_differential Q E α β z p v,hXn p v] at hh
      exact neg_eq_zero.mp hh
  choose a has had using hx
  let B:TestIndex Q (E.positiveTwist Q α).placement β→K :=
    fun ⟨i,p⟩=>match i with
    | .inl u=> -a p u
    | .inr _=>0
  have hBs:ScalarSupported Q T (l-1-1) (c-1-1) B := by
    rintro ⟨i,p⟩ hi
    rcases i with u|i
    · change -a p u=0
      rw [has p u,neg_zero]
      intro hh
      apply hi
      have hl:=corner_other_length Q hne p
      change (E.placement u.1).cochain-1+
        ((E.placement u.1).internal+Path.length u.2.val+Path.length p.val)=l-1-1 ∧
        (E.placement u.1).cochain-1=c-1-1
      change (E.placement u.1).cochain+
        ((E.placement u.1).internal+Path.length u.2.val)=l-1-1 ∧
        (E.placement u.1).cochain=c-1 at hh
      omega
    · rfl
  have hBn:∀ p u,Matrix.vecMul B D (twistNewTestIndex Q E α β p u)=
      z (twistNewTestIndex Q E α β p u) := by
    intro p u
    dsimp only [D,T]
    rw [testComplex_vertex_differential Q (E.positiveTwist Q α) β,
      twistTest_new_differential Q E α β B p u]
    change -Matrix.vecMul (-(a p)) (testMatrix Q E.placement E.placement α E.differential) u=_
    rw [Matrix.neg_vecMul,Pi.neg_apply,neg_neg]
    have hh:=congrFun (had p) u
    rwa [testComplex_vertex_differential Q E α] at hh
  let r:=z-Matrix.vecMul B D
  have hrn:∀ p u,r (twistNewTestIndex Q E α β p u)=0 := by
    intro p u
    change z _-Matrix.vecMul B D _=0
    rw [hBn,sub_self]
  have hrs:ScalarSupported Q T (l-1) (c-1) r := by
    apply scalarSupported_sub Q T hzs
    convert scalarSupported_map Q T T β T.differential T.entries T.degree hBs using 1 <;>
      omega
  have hrd:Matrix.vecMul r D=X := by
    change Matrix.vecMul (z-Matrix.vecMul B D) D=X
    rw [Matrix.sub_vecMul,hzd,Matrix.vecMul_vecMul,scalarDifferential_square Q T β,
      Matrix.vecMul_zero,sub_zero]
  refine ⟨fun u=>r (twistOldTestIndex Q E α β u),fun u hu=>hrs _ hu,?_⟩
  rw [testComplex_vertex_differential Q E β]
  funext v
  have hh:=congrFun hrd (twistOldTestIndex Q E α β v)
  change Matrix.vecMul r (T.differential.map (vertexHom Q β)) _=x v at hh
  rw [testComplex_vertex_differential Q (E.positiveTwist Q α) β,
    twistTest_old_differential Q E α β r hrn v] at hh
  exact hh

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_ScalarSupportedTokenShift
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K I : Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I]

theorem positiveTwist_test_exact_iff (hn:∀ a,Q.source a≠Q.target a)
    (E:BasedComplex Q (K:=K) I) (α:V) (l c:ℤ) :
    ScalarExactAt Q ((E.positiveTwist Q α).testComplex Q α) α l c ↔
      ScalarExactAt Q (E.testComplex Q α) α (l-1) (c+1) := by
  have e:=positiveTwist_testShift Q hn E α
  rw [← scalarExact_tokenShift_iff Q (E.testComplex Q α) α l c]
  constructor
  · exact fun h=>scalarExact_transport Q _ _ (e.symm Q) α (fun _=>rfl) h
  · exact fun h=>scalarExact_transport Q _ _ e α (fun _=>rfl) h

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_TestUpperBound
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K I J : Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

theorem positiveTwist_testUpperBound (hn:∀ a,Q.source a≠Q.target a)
    (E:BasedComplex Q (K:=K) I) (U:Set V) (α:V) (hα:α∈U) {t:ℤ}
    (h:TestUpperBound Q E U t) : TestUpperBound Q (E.positiveTwist Q α) U (t+1) := by
  intro β hβ l hl c
  by_cases he:β=α
  · subst β
    apply (positiveTwist_test_exact_iff Q hn E α l c).mpr
    exact h α hα (l-1) (by omega) (c+1)
  · exact positiveTwist_other_test_exact Q E α β he l c
      (h α hα l (by omega) (c+1)) (h β hβ l (by omega) c)

theorem positiveTwist_testUpperBound_reflect (hn:∀ a,Q.source a≠Q.target a)
    (E:BasedComplex Q (K:=K) I) (U:Set V) (α:V) (hα:α∈U) {t:ℤ}
    (h:TestUpperBound Q (E.positiveTwist Q α) U t) : TestUpperBound Q E U t := by
  have ha:∀ l:ℤ,t<l+1→∀ c:ℤ,ScalarExactAt Q (E.testComplex Q α) α l c := by
    intro l hl c
    have hh:=(positiveTwist_test_exact_iff Q hn E α (l+1) (c-1)).mp
      (h α hα (l+1) hl (c-1))
    simpa only [add_sub_cancel_right,sub_add_cancel] using hh
  intro β hβ l hl c
  by_cases he:β=α
  · subst β
    exact ha l (by omega) c
  · exact positiveTwist_other_test_exact_reflect Q E α β he l c
      (ha (l-1) (by omega) c) (h β hβ l hl c)

theorem positiveTwist_testUpperBound_iff (hn:∀ a,Q.source a≠Q.target a)
    (E:BasedComplex Q (K:=K) I) (U:Set V) (α:V) (hα:α∈U) {t:ℤ}
    (h:TestUpperBound Q E U t) :
    TestUpperBound Q (E.positiveTwist Q α) U t ↔
      ∀ c,ScalarExactAt Q (E.testComplex Q α) α t c := by
  constructor
  · intro hh c
    have hz:=(positiveTwist_test_exact_iff Q hn E α (t+1) (c-1)).mp
      (hh α hα (t+1) (by omega) (c-1))
    simpa only [add_sub_cancel_right,sub_add_cancel] using hz
  · intro hh β hβ l hl c
    by_cases he:β=α
    · subst β
      apply (positiveTwist_test_exact_iff Q hn E α l c).mpr
      by_cases he:l-1=t
      · rw [he]; exact hh (c+1)
      · exact h α hα (l-1) (by omega) (c+1)
    · exact positiveTwist_other_test_exact Q E α β he l c
        (h α hα l hl (c+1)) (h β hβ l hl c)

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_TestExact
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

def ClassTestUpper (x:FiniteHomotopyClass Q (K:=K)) (U:Set V) (t:ℤ) : Prop :=
  ∀ α∈U,∀ l:ℤ,t<l→∀ c:ℤ,ClassTestExact Q α l c x

lemma classTestExact_positive_other (x:FiniteHomotopyClass Q (K:=K)) (α β:V)
    (hne:β≠α) (l c:ℤ)
    (ha:ClassTestExact Q α l (c+1) x) (hb:ClassTestExact Q β l c x) :
    ClassTestExact Q β l c (classPositiveTwist Q α x) := by
  induction x using Quotient.inductionOn with | _ E =>
    exact positiveTwist_other_test_exact Q E.complex α β hne l c ha hb

lemma classTestExact_positive_adjacent (hn:∀ a,Q.source a≠Q.target a)
    (x:FiniteHomotopyClass Q (K:=K)) {α β:V} (e:SimpleEdge Q α β) (l c:ℤ) :
    ClassTestExact Q β l c (classPositiveTwist Q α (classPositiveTwist Q β x)) ↔
      ClassTestExact Q α l (c+1) x := by
  induction x using Quotient.inductionOn with | _ E =>
    exact positiveTwist_adjacent_test_exact_iff Q hn E.complex e l c

lemma classPositiveTwist_testUpper (hn:∀ a,Q.source a≠Q.target a)
    (x:FiniteHomotopyClass Q (K:=K)) (U:Set V) (α:V) (hα:α∈U) {t:ℤ}
    (h:ClassTestUpper Q x U t) : ClassTestUpper Q (classPositiveTwist Q α x) U (t+1) := by
  induction x using Quotient.inductionOn with | _ E =>
    exact positiveTwist_testUpperBound Q hn E.complex U α hα h

lemma classPositiveTwist_testUpper_reflect (hn:∀ a,Q.source a≠Q.target a)
    (x:FiniteHomotopyClass Q (K:=K)) (U:Set V) (α:V) (hα:α∈U) {t:ℤ}
    (h:ClassTestUpper Q (classPositiveTwist Q α x) U t) : ClassTestUpper Q x U t := by
  induction x using Quotient.inductionOn with | _ E =>
    exact positiveTwist_testUpperBound_reflect Q hn E.complex U α hα h

lemma classPositiveTwist_testUpper_iff (hn:∀ a,Q.source a≠Q.target a)
    (x:FiniteHomotopyClass Q (K:=K)) (U:Set V) (α:V) (hα:α∈U) {t:ℤ}
    (h:ClassTestUpper Q x U t) :
    ClassTestUpper Q (classPositiveTwist Q α x) U t ↔
      ∀ c,ClassTestExact Q α t c x := by
  induction x using Quotient.inductionOn with | _ E =>
    exact positiveTwist_testUpperBound_iff Q hn E.complex U α hα h

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_OutsideCap
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I:Type u} [Fintype I] [DecidableEq I]

lemma classTestUpper_of_generator_cap (x:FiniteHomotopyClass Q (K:=K)) (d:ℤ)
    (h:ClassUpperBound Q d x) (U:Set V) : ClassTestUpper Q x U (d+2) := by
  rw [← minimalClassModel_class Q x]
  exact testUpperBound_of_generator_cap Q _ d h U

omit [Fintype V] [DecidableEq A] in
lemma classOutsideCap_of_upper (x:FiniteHomotopyClass Q (K:=K)) (U:Set V) (d:ℤ)
    (h:ClassUpperBound Q d x) : ClassOutsideCap Q x U d := fun i _=>h i

lemma classUpperBound_of_test_and_outside (x:FiniteHomotopyClass Q (K:=K))
    (U:Set V) (d:ℤ) (h:ClassTestUpper Q x U (d+2)) (ho:ClassOutsideCap Q x U d) :
    ClassUpperBound Q d x := by
  apply generatorBound_of_test_and_outside Q _ (minimalClassModel_minimal Q x) U d _ ho
  change ClassTestUpper Q (classOfComplex Q (minimalClassModel Q x).complex) U (d+2)
  have he:classOfComplex Q (minimalClassModel Q x).complex=x:=minimalClassModel_class Q x
  rw [he]
  exact h

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_ReducedAmplitudeTwistLevel
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

universe u

variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I : Type u} [Fintype I] [DecidableEq I]

lemma reducedAmplitudeTwist_level (E : BasedComplex Q (K := K) I) (α : V)
    (k : AmplitudeCoreIndex Q E α) :
    ∃ i : I,
      ((reducedAmplitudeTwist Q E α).placement k).level = (E.placement i).level ∨
      (((reducedAmplitudeTwist Q E α).placement k).level = (E.placement i).level + 1 ∧
        ((reducedAmplitudeTwist Q E α).placement k).color = α) := by
  rw [reducedAmplitudeTwist_placement]
  rcases k with u | i
  · refine ⟨u.val.1, ?_⟩
    have h := Path.length_cases u.val.2.val
    have hn := u.property
    dsimp only [GeneratorPlacement.level]
    rcases h with h | h | h
    · exact (hn h).elim
    · exact Or.inl (by omega)
    · exact Or.inr ⟨by omega, rfl⟩
  · exact ⟨i.val, Or.inl rfl⟩

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_PositiveTwistLowerBound
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I J:Type u} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

theorem positiveTwist_lower_bound
    (E:BasedComplex Q (K:=K) I) (F:BasedComplex Q (K:=K) J)
    {d:ℤ} (hE:∀ i,d≤(E.placement i).level) (α:V) (hF:F.IsMinimal Q)
    (e:HomotopyEquivalence Q (E.positiveTwist Q α) F) :
    ∀ j,d≤(F.placement j).level := by
  have reduction : HomotopyEquivalence Q (E.positiveTwist Q α)
      (reducedAmplitudeTwist Q E α) := by
    convert amplitudeTwistReduction Q E α using 1
    all_goals try with_reducible_and_instances rfl
  apply minimal_bound_transport Q (reducedAmplitudeTwist Q E α) F hF
    ((reduction.symm Q).trans Q e) (fun p=>d≤p.level)
  intro k
  obtain ⟨i,hi⟩:=reducedAmplitudeTwist_level Q E α k
  have hh:=hE i
  rcases hi with hi|⟨hi,_⟩ <;> omega

theorem classPositiveTwist_lower_bound
    (α:V) (x:FiniteHomotopyClass Q (K:=K)) {d:ℤ} (hx:ClassLowerBound Q d x) :
    ClassLowerBound Q d (classPositiveTwist Q α x) := by
  let E:=minimalClassModel Q x
  let y:=classPositiveTwist Q α x
  let F:=minimalClassModel Q y
  have he:classOfComplex Q (E.complex.positiveTwist Q α)=classOfComplex Q F.complex := by
    change classPositiveTwist Q α (classOfComplex Q E.complex)=classOfComplex Q F.complex
    have hE:classOfComplex Q E.complex=x:=minimalClassModel_class Q x
    have hF:classOfComplex Q F.complex=y:=minimalClassModel_class Q y
    rw [hE,hF]
  obtain ⟨e⟩:=Quotient.exact he
  exact positiveTwist_lower_bound Q E.complex F.complex hx α
    (minimalClassModel_minimal Q y) e

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Coxeter_PositiveBraidRel
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.linearMap_pathBasis _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_base _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_left _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A:Type u} (Q:ReversibleQuiver V A)

namespace PositiveBraidRel
lemma length_eq {v w:List V} (h:PositiveBraidRel Q v w) : v.length=w.length := by
  induction h with
  | refl => rfl
  | symm h ih => exact ih.symm
  | trans h k ih ik => exact ih.trans ik
  | cons α h ih => exact congrArg Nat.succ ih
  | orthogonal => rfl
  | adjacent => rfl

lemma mem_iff {v w:List V} (h:PositiveBraidRel Q v w) (s:V) : s∈v↔s∈w := by
  induction h with
  | refl => rfl
  | symm h ih => exact ih.symm
  | trans h k ih ik => exact ih.trans ik
  | cons α h ih => simpa only [List.mem_cons] using or_congr Iff.rfl ih
  | orthogonal => simp only [List.mem_cons]; tauto
  | adjacent => simp only [List.mem_cons]; tauto

lemma mem_set {v w:List V} (h:PositiveBraidRel Q v w) (U:Set V)
    (hv:∀ s∈v,s∈U) : ∀ s∈w,s∈U := fun s hs=>hv s ((h.mem_iff Q s).mpr hs)
end PositiveBraidRel

variable {K:Type*} [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

lemma positiveWordAction_testUpper_reflect (hn:∀ a,Q.source a≠Q.target a)
    (w:List V) (x:FiniteHomotopyClass Q (K:=K)) (U:Set V)
    (hw:∀ s∈w,s∈U) {t:ℤ} (h:ClassTestUpper Q (positiveWordAction Q w x) U t) :
    ClassTestUpper Q x U t := by
  induction w with
  | nil => exact h
  | cons α w ih =>
    apply ih (fun s hs=>hw s (List.mem_cons_of_mem _ hs))
    exact classPositiveTwist_testUpper_reflect Q hn _ U α (hw α (by simp)) h

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Coxeter_OrdinaryCoxeterMatrix
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A:Type u} (Q:ReversibleQuiver V A)

lemma PositiveBraidRel.coxeter_eq {v w:List V} (h:PositiveBraidRel Q v w) :
    (ordinaryCoxeterMatrix Q).toCoxeterSystem.wordProd v=
      (ordinaryCoxeterMatrix Q).toCoxeterSystem.wordProd w := by
  let cs := (ordinaryCoxeterMatrix Q).toCoxeterSystem
  change cs.wordProd v=cs.wordProd w
  induction h with
  | refl => rfl
  | symm h ih => exact ih.symm
  | trans h k ih ik => exact ih.trans ik
  | cons α h ih => simpa only [CoxeterSystem.wordProd_cons] using congrArg (cs.simple α*·) ih
  | @orthogonal α β h w =>
    have hb:=cs.wordProd_braidWord_eq α β
    have hab:ordinaryCoxeterMatrix Q α β=2:=ordinaryCoxeterMatrix_orthogonal Q h
    have hba:=ordinaryCoxeterMatrix_orthogonal Q (h.symm Q)
    simp only [CoxeterSystem.braidWord,hab,hba,CoxeterSystem.alternatingWord] at hb
    change cs.wordProd [α,β]=cs.wordProd [β,α] at hb
    simpa only [CoxeterSystem.wordProd_cons,CoxeterSystem.wordProd_nil,_root_.mul_one,_root_.mul_assoc]
      using congrArg (·*cs.wordProd w) hb
  | @adjacent α β e w =>
    have hb:=cs.wordProd_braidWord_eq α β
    have hab:=ordinaryCoxeterMatrix_adjacent Q e
    have hba:=ordinaryCoxeterMatrix_adjacent Q (e.reverse Q)
    simp only [CoxeterSystem.braidWord,hab,hba,CoxeterSystem.alternatingWord] at hb
    change cs.wordProd [β,α,β]=cs.wordProd [α,β,α] at hb
    simpa only [CoxeterSystem.wordProd_cons,CoxeterSystem.wordProd_nil,_root_.mul_one,_root_.mul_assoc]
      using congrArg (·*cs.wordProd w) hb.symm

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_ReducedNoTopDivisor
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

omit [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A] in
lemma reduced_no_top_divisor {α:V} {w v:List V}
    (hr:(ordinaryCoxeterMatrix Q).toCoxeterSystem.IsReduced (α::w))
    (h:PositiveBraidRel Q w (α::v)) : False := by
  let cs := (ordinaryCoxeterMatrix Q).toCoxeterSystem
  have he:cs.wordProd (α::w)=cs.wordProd v := by
    rw [CoxeterSystem.wordProd_cons,PositiveBraidRel.coxeter_eq Q h,
      CoxeterSystem.wordProd_cons,CoxeterSystem.simple_mul_simple_cancel_left]
  have hh:=cs.length_wordProd_le v
  have hl:=PositiveBraidRel.length_eq Q h
  change cs.length (cs.wordProd (α::w))=(α::w).length at hr
  rw [he] at hr
  simp only [List.length_cons] at hr hl
  omega

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_PositiveWordLowerBound
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

lemma positiveWord_lower_bound (w:List V) (x:FiniteHomotopyClass Q (K:=K))
    {d:ℤ} (hx:ClassLowerBound Q d x) : ClassLowerBound Q d (positiveWordAction Q w x) := by
  induction w with
  | nil => exact hx
  | cons α w ih => exact classPositiveTwist_lower_bound Q α _ ih

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_InverseWordAction
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I J:Type u} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

lemma negativeTwist_upper_bound
    (E:BasedComplex Q (K:=K) I) (F:BasedComplex Q (K:=K) J)
    {d:ℤ} (hE:∀ i,(E.placement i).level≤d) (α:V) (hF:F.IsMinimal Q)
    (e:HomotopyEquivalence Q (E.negativeTwist Q α) F) :
    ∀ j,(F.placement j).level≤d := by
  have reduction : HomotopyEquivalence Q (E.negativeTwist Q α)
      (reducedNegativeAmplitudeTwist Q E α) := by
    convert negativeAmplitudeTwistReduction Q E α using 1
    all_goals try with_reducible_and_instances rfl
  apply minimal_bound_transport Q (reducedNegativeAmplitudeTwist Q E α) F hF
    ((reduction.symm Q).trans Q e) (fun p=>p.level≤d)
  intro k
  obtain ⟨i,hi⟩:=reducedNegativeAmplitudeTwist_level Q E α k
  have hh:=hE i
  rcases hi with hi|⟨hi,_⟩ <;> omega

lemma classNegativeTwist_upper_bound (α:V) (x:FiniteHomotopyClass Q (K:=K))
    {d:ℤ} (hx:ClassUpperBound Q d x) : ClassUpperBound Q d (classNegativeTwist Q α x) := by
  let E:=minimalClassModel Q x
  let y:=classNegativeTwist Q α x
  let F:=minimalClassModel Q y
  have he:classOfComplex Q (E.complex.negativeTwist Q α)=classOfComplex Q F.complex := by
    change classNegativeTwist Q α (classOfComplex Q E.complex)=classOfComplex Q F.complex
    have hE:classOfComplex Q E.complex=x:=minimalClassModel_class Q x
    have hF:classOfComplex Q F.complex=y:=minimalClassModel_class Q y
    rw [hE,hF]
  obtain ⟨e⟩:=Quotient.exact he
  exact negativeTwist_upper_bound Q E.complex F.complex hx α (minimalClassModel_minimal Q y) e

lemma positive_inverseWord (hn:∀ a,Q.source a≠Q.target a)
    (w:List V) (x:FiniteHomotopyClass Q (K:=K)) :
    positiveWordAction Q w (inverseWordAction Q w x)=x := by
  induction w generalizing x with
  | nil => rfl
  | cons α w ih =>
    change classPositiveTwist Q α (positiveWordAction Q w
      (inverseWordAction Q w (classNegativeTwist Q α x)))=x
    rw [ih]
    exact (classTwistPerm Q hn α).apply_symm_apply x

lemma positiveWord_homDimension (hn:∀ a,Q.source a≠Q.target a)
    (w:List V) (x y:FiniteHomotopyClass Q (K:=K)) (n v:ℤ) :
    classHomDimension Q n v (positiveWordAction Q w x) (positiveWordAction Q w y)=
      classHomDimension Q n v x y := by
  induction w with
  | nil => rfl
  | cons α w ih =>
    change classHomDimension Q n v (classPositiveTwist Q α _) (classPositiveTwist Q α _)=_
    rw [classPositiveTwist_homDimension Q hn,ih]

lemma inverseWord_upper_bound (w:List V) (x:FiniteHomotopyClass Q (K:=K))
    {d:ℤ} (hx:ClassUpperBound Q d x) : ClassUpperBound Q d (inverseWordAction Q w x) := by
  induction w generalizing x with
  | nil => exact hx
  | cons α w ih => exact ih _ (classNegativeTwist_upper_bound Q α x hx)

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_HomDimensionZeroCycles
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

omit [Fintype V] [DecidableEq A] in

lemma homDimension_zero_of_cycles_boundary {I J : Type*} [Fintype I] [Fintype J]
    (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J) (n v : ℤ)
    (h : ∀ f ∈ homCycles Q E F n v, f ∈ homBoundaries Q E F n v) :
    homDimension Q E F n v = 0 := by
  have hb : (homBoundaries Q E F n v).comap (homCycles Q E F n v).subtype = ⊤ := by
    apply eq_top_iff.mpr
    intro f _
    exact h f.val f.property
  unfold homDimension homCohomology
  rw [hb]
  exact Module.finrank_zero_of_subsingleton

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_DownClosed
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K I:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I]
attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma levelDownClosed (E:BasedComplex Q (K:=K) I) (hE:E.IsMinimal Q) (d:ℤ) :
    DownClosed Q E (lowerLevelSet Q E d) := by
  intro i hi j hij
  have h:=differential_level Q E hE hij
  change (E.placement j).level≤d
  change (E.placement i).level≤d at hi
  rcases h with h|h <;> omega

noncomputable def lowerTruncation (E:BasedComplex Q (K:=K) I) (hE:E.IsMinimal Q) (d:ℤ) :=
  lowRestriction Q E (lowerLevelSet Q E d) (levelDownClosed Q E hE d)
noncomputable def upperTruncation (E:BasedComplex Q (K:=K) I) (hE:E.IsMinimal Q) (d:ℤ) :=
  highRestriction Q E (lowerLevelSet Q E d) (levelDownClosed Q E hE d)

noncomputable def lowConePivot (E:BasedComplex Q (K:=K) I) (T:Set I) (h:DownClosed Q E T) :
    BlockPivot Q (lowConeNormalized Q E T h) where
  coefficient:=1
  nonzero:=one_ne_zero
  color _:=rfl
  cochain i:=by change (E.placement i).cochain=(E.placement i).cochain-1+1; omega
  internal _:=rfl
  entry i j:=by
    change (if (i:I)=(j:I) then vertexId Q (K:=K) (E.placement i).color else 0)=
      1 • (if i=j then vertexId Q (K:=K) (E.placement i).color else 0)
    simp only [one_smul,Subtype.val_inj]

omit [Fintype V] [DecidableEq A] in
lemma lowCone_reduced_eq (E:BasedComplex Q (K:=K) I) (T:Set I) (h:DownClosed Q E T) :
    (lowConePivot Q E T h).reduced Q=highRestriction Q E T h := by
  apply ext_placement_differential Q
  · rfl
  · apply Matrix.ext
    intro i j
    rw [BlockPivot.reduced_differential]
    simp only [lowCone_source_retained,MulZeroClass.mul_zero,Finset.sum_const_zero,sub_zero]
    rfl

noncomputable def lowConeReduction (E:BasedComplex Q (K:=K) I) (T:Set I) (h:DownClosed Q E T) :
    HomotopyEquivalence Q ((lowInclusion Q E T h).cone Q) (highRestriction Q E T h) := by
  have e:=(((lowInclusion Q E T h).cone Q).reindexHomotopyEquivalence Q
    (Equiv.sumCongr (Equiv.refl T) (Equiv.Set.sumCompl T))).trans Q
      ((lowConePivot Q E T h).reductionEquivalence Q)
  rw [lowCone_reduced_eq] at e
  exact e

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_LowMatrix
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I J L:Type u} [Fintype I] [Fintype J] [Fintype L]
  [DecidableEq I] [DecidableEq J] [DecidableEq L]
attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable

noncomputable def Map.lowerTruncation {E:BasedComplex Q (K:=K) I}
    {F:BasedComplex Q (K:=K) J} (f:Map Q E F)
    (hE:E.IsMinimal Q) (hF:F.IsMinimal Q) (d:ℤ) :
    Map Q (lowerTruncation Q E hE d) (lowerTruncation Q F hF d) where
  matrix:=lowMatrix Q E F f.matrix d
  entries:=⟨fun i j=>f.entries.1 i j,fun i j=>f.entries.2 i j⟩
  degree:=fun i j=>f.degree i j
  commute:=by
    change lowMatrix Q E E E.differential d*lowMatrix Q E F f.matrix d=
      lowMatrix Q E F f.matrix d*lowMatrix Q F F F.differential d
    rw [← lowMatrix_mul Q E E F _ _ d (minimal_differential_level_bound Q E hE),
      ← lowMatrix_mul Q E F F _ _ d (map_level_bound Q f), f.commute]

noncomputable def HomotopyEquivalence.lowerTruncation
    {E:BasedComplex Q (K:=K) I} {F:BasedComplex Q (K:=K) J}
    (e:HomotopyEquivalence Q E F) (hE:E.IsMinimal Q) (hF:F.IsMinimal Q) (d:ℤ) :
    HomotopyEquivalence Q (lowerTruncation Q E hE d) (lowerTruncation Q F hF d) where
  forward:=e.forward.lowerTruncation Q hE hF d
  backward:=e.backward.lowerTruncation Q hF hE d
  sourceHomotopy:=lowMatrix Q E E e.sourceHomotopy d
  targetHomotopy:=lowMatrix Q F F e.targetHomotopy d
  sourceEntries:=⟨fun i j=>e.sourceEntries.1 i j,fun i j=>e.sourceEntries.2 i j⟩
  targetEntries:=⟨fun i j=>e.targetEntries.1 i j,fun i j=>e.targetEntries.2 i j⟩
  sourceDegree:=fun i j=>e.sourceDegree i j
  targetDegree:=fun i j=>e.targetDegree i j
  sourceEquation:=by
    change lowMatrix Q E F e.forward.matrix d*lowMatrix Q F E e.backward.matrix d=
      projectiveIdentity Q _+(lowMatrix Q E E E.differential d*lowMatrix Q E E e.sourceHomotopy d+
        lowMatrix Q E E e.sourceHomotopy d*lowMatrix Q E E E.differential d)
    rw [← lowMatrix_mul Q E F E _ _ d (map_level_bound Q e.forward),e.sourceEquation,
      lowMatrix_add,lowMatrix_identity,lowMatrix_add,
      lowMatrix_mul Q E E E _ _ d (minimal_differential_level_bound Q E hE),
      lowMatrix_mul Q E E E _ _ d (homotopy_level_bound Q E _ e.sourceDegree)]
    rfl
  targetEquation:=by
    change lowMatrix Q F E e.backward.matrix d*lowMatrix Q E F e.forward.matrix d=
      projectiveIdentity Q _+(lowMatrix Q F F F.differential d*lowMatrix Q F F e.targetHomotopy d+
        lowMatrix Q F F e.targetHomotopy d*lowMatrix Q F F F.differential d)
    rw [← lowMatrix_mul Q F E F _ _ d (map_level_bound Q e.backward),e.targetEquation,
      lowMatrix_add,lowMatrix_identity,lowMatrix_add,
      lowMatrix_mul Q F F F _ _ d (minimal_differential_level_bound Q F hF),
      lowMatrix_mul Q F F F _ _ d (homotopy_level_bound Q F _ e.targetDegree)]
    rfl

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_LowerTruncation
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I:Type u} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable

noncomputable def classLowerTruncation (d:ℤ) (x:FiniteHomotopyClass Q (K:=K)) :
    FiniteHomotopyClass Q (K:=K) :=
  classOfComplex Q (lowerTruncation Q (minimalClassModel Q x).complex (minimalClassModel_minimal Q x) d)

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_TargetLow
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I J:Type u} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma targetLow_inclusion (E:BasedComplex Q (K:=K) I) (F:BasedComplex Q (K:=K) J)
    (hF:F.IsMinimal Q) (d:ℤ) (f:Matrix I (lowerLevelSet Q F d) (Q.Zigzag K))
    (hf:ProjectiveEntries Q E.placement (lowerTruncation Q F hF d).placement f) :
    targetLow Q E F d (f*blockInclusion Q F (lowerLevelSet Q F d))=f := by
  apply Matrix.ext
  intro i j
  change (∑ k:lowerLevelSet Q F d,f i k*
    (if (k:J)=(j:J) then vertexId Q (K:=K) (F.placement k).color else 0))=f i j
  simp only [Subtype.val_inj,mul_ite,MulZeroClass.mul_zero,Fintype.sum_ite_eq']
  exact hf.2 i j

omit [Fintype V] [DecidableEq A] [DecidableEq I] [DecidableEq J] in
lemma targetLow_homSpace (E:BasedComplex Q (K:=K) I) (F:BasedComplex Q (K:=K) J)
    (hF:F.IsMinimal Q) (d n v:ℤ) {g:Matrix I J (Q.Zigzag K)}
    (hg:g∈homSpace Q E F n v) :
    targetLow Q E F d g∈homSpace Q E (lowerTruncation Q F hF d) n v :=
  ⟨⟨fun i j=>hg.1.1 i j,fun i j=>hg.1.2 i j⟩,fun i j=>hg.2 i j⟩

omit [Fintype V] [DecidableEq A] [DecidableEq I] [DecidableEq J] in
lemma targetLow_differential (E:BasedComplex Q (K:=K) I) (F:BasedComplex Q (K:=K) J)
    (hF:F.IsMinimal Q) (d n:ℤ) (g:Matrix I J (Q.Zigzag K))
    (hg:∀ i j,j∉lowerLevelSet Q F d → g i j=0) :
    targetLow Q E F d (homDifferential Q E F n g)=
      homDifferential Q E (lowerTruncation Q F hF d) n (targetLow Q E F d g) := by
  have hmul:targetLow Q E F d (g*F.differential)=
      targetLow Q E F d g*(lowerTruncation Q F hF d).differential := by
    apply Matrix.ext
    intro i j
    change (∑ k:J,g i k*F.differential k j)=
      ∑ k:lowerLevelSet Q F d,g i k*F.differential k j
    symm
    apply Fintype.sum_of_injective (Subtype.val:lowerLevelSet Q F d→J) Subtype.val_injective
    · intro k hk
      have hn:k∉lowerLevelSet Q F d:=fun hh=>hk ⟨⟨k,hh⟩,rfl⟩
      rw [hg i k hn,zero_mul]
    · intro k; rfl
  change targetLow Q E F d (E.differential*g-cochainSign (K:=K) n • (g*F.differential))=_
  rw [map_sub,map_smul,hmul]
  rfl

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
theorem low_boundary_of_inclusion_boundary (E:BasedComplex Q (K:=K) I)
    (F:BasedComplex Q (K:=K) J) (hF:F.IsMinimal Q) (d:ℤ)
    (hE:∀ i,(E.placement i).level≤d+1)
    {f:Matrix I (lowerLevelSet Q F d) (Q.Zigzag K)}
    (hf:ProjectiveEntries Q E.placement (lowerTruncation Q F hF d).placement f)
    (hb:f*blockInclusion Q F (lowerLevelSet Q F d)∈homBoundaries Q E F 0 0) :
    f∈homBoundaries Q E (lowerTruncation Q F hF d) 0 0 := by
  obtain ⟨g,hg,he⟩:=hb
  have hs:∀ i j,j∉lowerLevelSet Q F d → g i j=0 := by
    intro i j hj
    by_contra hn
    have hh:=mapDegree_level_bound Q hg.2 hn
    have hhE:=hE i
    exact hj (by change (F.placement j).level≤d; omega)
  refine ⟨targetLow Q E F d g,targetLow_homSpace Q E F hF d _ _ hg,?_⟩
  have h:=congrArg (targetLow Q E F d) he
  rw [targetLow_differential Q E F hF d _ _ hs,targetLow_inclusion Q E F hF d f hf] at h
  exact h

omit [DecidableEq A] [DecidableEq I] in
lemma lowerTruncation_homDimension_zero (E:BasedComplex Q (K:=K) I)
    (F:BasedComplex Q (K:=K) J) (hF:F.IsMinimal Q) (d:ℤ)
    (hE:∀ i,(E.placement i).level≤d+1) (hz:homDimension Q E F 0 0=0) :
    homDimension Q E (lowerTruncation Q F hF d) 0 0=0 := by
  apply homDimension_zero_of_cycles_boundary Q
  intro f hf
  apply low_boundary_of_inclusion_boundary Q E F hF d hE hf.1.1
  apply boundary_of_homDimension_zero Q E F 0 0 hz
  simpa only [add_zero,lowInclusion] using homCycles_mul Q hf
    (map_mem_homCycles Q (lowInclusion Q F (lowerLevelSet Q F d) (levelDownClosed Q F hF d)))

omit [DecidableEq A] in
lemma classLowerTruncation_homDimension_zero (x y:FiniteHomotopyClass Q (K:=K))
    (d:ℤ) (hx:ClassUpperBound Q (d+1) x) (hz:classHomDimension Q 0 0 x y=0) :
    classHomDimension Q 0 0 x (classLowerTruncation Q d y)=0 := by
  let E:=minimalClassModel Q x
  let F:=minimalClassModel Q y
  have hx':classOfComplex Q E.complex=x:=minimalClassModel_class Q x
  rw [← hx']
  change homDimension Q E.complex (lowerTruncation Q F.complex (minimalClassModel_minimal Q y) d) 0 0=0
  apply lowerTruncation_homDimension_zero Q E.complex F.complex (minimalClassModel_minimal Q y) d hx
  rw [minimalClassModel_homDimension]
  exact hz

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_CanonicalWordLow
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

noncomputable def canonicalWordLow (w:List V) (q:ℤ) (x:FiniteHomotopyClass Q (K:=K)) :
    FiniteHomotopyClass Q (K:=K) :=
  positiveWordAction Q w (classLowerTruncation Q (q-1) (inverseWordAction Q w x))

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_HomMono
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I J L:Type u} [Fintype I] [Fintype J] [Fintype L]
  [DecidableEq I] [DecidableEq J] [DecidableEq L]

def HomMonoFrom (T:BasedComplex Q (K:=K) I) {E:BasedComplex Q (K:=K) J}
    {F:BasedComplex Q (K:=K) L} (f:Map Q E F) : Prop :=
  ∀ g, g∈homCycles Q T E 0 0 → g*f.matrix∈homBoundaries Q T F 0 0 →
    g∈homBoundaries Q T E 0 0

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma lowInclusion_homMono (T:BasedComplex Q (K:=K) I)
    (E:BasedComplex Q (K:=K) J) (hE:E.IsMinimal Q) (d:ℤ)
    (hT:∀ i,(T.placement i).level≤d+1) :
    HomMonoFrom Q T (lowInclusion Q E (lowerLevelSet Q E d) (levelDownClosed Q E hE d)) := by
  intro g hg hb
  exact low_boundary_of_inclusion_boundary Q T E hE d hT hg.1.1 hb

lemma positiveHomCohomology_surjective (hn:∀ a,Q.source a≠Q.target a)
    (E:BasedComplex Q (K:=K) I) (F:BasedComplex Q (K:=K) J) (α:V) (n v:ℤ) :
    Function.Surjective ((positiveHomOperator Q E F α).onCohomology n v) :=
  (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (positiveTwist_homDimension Q hn E F α n v).symm).mp
      (positiveHomCohomology_injective Q hn E F α n v)

lemma positiveHom_cycle_lift (hn:∀ a,Q.source a≠Q.target a)
    (E:BasedComplex Q (K:=K) I) (F:BasedComplex Q (K:=K) J) (α:V) (n v:ℤ)
    {g:Matrix _ _ (Q.Zigzag K)}
    (hg:g∈homCycles Q (E.positiveTwist Q α) (F.positiveTwist Q α) n v) :
    ∃ f, f∈homCycles Q E F n v ∧
      positiveHomTransform Q E F α n f-g∈homBoundaries Q
        (E.positiveTwist Q α) (F.positiveTwist Q α) n v := by
  obtain ⟨x,hx⟩:=positiveHomCohomology_surjective Q hn E F α n v
    (Submodule.Quotient.mk ⟨g,hg⟩)
  obtain ⟨f,rfl⟩:=Submodule.Quotient.mk_surjective _ x
  refine ⟨f,f.property,?_⟩
  have hh:= (Submodule.Quotient.eq
    ((homBoundaries Q (E.positiveTwist Q α) (F.positiveTwist Q α) n v).comap
      (homCycles Q (E.positiveTwist Q α) (F.positiveTwist Q α) n v).subtype)).mp hx
  exact hh

omit [DecidableEq I] [DecidableEq J] [DecidableEq L] in
lemma positiveHom_zero_mul (E:BasedComplex Q (K:=K) I)
    (F:BasedComplex Q (K:=K) J) (G:BasedComplex Q (K:=K) L) (α:V)
    (f:Matrix I J (Q.Zigzag K)) (hf:ProjectiveEntries Q E.placement F.placement f)
    (g:Map Q F G) :
    positiveHomTransform Q E F α 0 f*(g.positiveTwist Q α).matrix=
      positiveHomTransform Q E G α 0 (f*g.matrix) := by
  change Matrix.fromBlocks _ 0 0 f * Matrix.fromBlocks _ 0 0 g.matrix=_
  simp only [positiveHomTransform,cochainSign_zero,one_smul,Matrix.fromBlocks_multiply,
    Matrix.mul_zero,Matrix.zero_mul,zero_add,add_zero,Map.test,testTransform_mul Q α _ hf]

lemma HomMonoFrom.positiveTwist (hn:∀ a,Q.source a≠Q.target a)
    {T:BasedComplex Q (K:=K) I} {E:BasedComplex Q (K:=K) J}
    {F:BasedComplex Q (K:=K) L} {f:Map Q E F}
    (h:HomMonoFrom Q T f) (α:V) :
    HomMonoFrom Q (T.positiveTwist Q α) (f.positiveTwist Q α) := by
  intro g hg hb
  obtain ⟨k,hk,hkg⟩:=positiveHom_cycle_lift Q hn T E α 0 0 hg
  have hh:=homBoundary_mul_cycle Q hkg (map_mem_homCycles Q (f.positiveTwist Q α))
  simp only [zero_add] at hh
  rw [Matrix.sub_mul,positiveHom_zero_mul Q T E F α k hk.1.1 f] at hh
  have hb':positiveHomTransform Q T F α 0 (k*f.matrix)∈homBoundaries Q
      (T.positiveTwist Q α) (F.positiveTwist Q α) 0 0 := by
    have hz:=(homBoundaries Q _ _ 0 0).add_mem hh hb
    simpa only [sub_add_cancel] using hz
  have hkf:ProjectiveEntries Q T.placement F.placement (k*f.matrix):=
    projectiveEntries_mul Q hk.1.1 f.entries
  have hk':=h k hk (positiveHomTransform_reflect_boundary Q hn T F α 0 0 hkf hb')
  have hkb:positiveHomTransform Q T E α 0 k∈homBoundaries Q
      (T.positiveTwist Q α) (E.positiveTwist Q α) 0 0 :=
    (positiveHomOperator Q T E α).map_boundaries 0 0 hk'
  have hz:=(homBoundaries Q (T.positiveTwist Q α) (E.positiveTwist Q α) 0 0).sub_mem hkb hkg
  simpa only [sub_sub_cancel] using hz

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_TermwiseSplitInjection
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
variable {I J T : Type*} [Fintype I] [Fintype J] [Fintype T] [DecidableEq I]

noncomputable def postcomposeOnCycles (E : BasedComplex Q (K := K) T)
    (F : BasedComplex Q (K := K) I) (G : BasedComplex Q (K := K) J)
    (ι : Map Q F G) (n v : ℤ) :
    homCycles Q E F n v →ₗ[K] homCycles Q E G n v where
  toFun f := ⟨f.val * ι.matrix, by
    simpa only [add_zero] using homCycles_mul Q f.property (map_mem_homCycles Q ι)⟩
  map_add' f g := by apply Subtype.ext; exact Matrix.add_mul _ _ _
  map_smul' r f := by apply Subtype.ext; exact Matrix.smul_mul _ _ _

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_Shift
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.linearMap_pathBasis _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_base _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_left _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I J L:Type u} [Fintype I] [Fintype J] [Fintype L]
  [DecidableEq I] [DecidableEq J] [DecidableEq L]

noncomputable def sourceShift (E:BasedComplex Q (K:=K) I) (n v:ℤ) :
    BasedComplex Q (K:=K) I where
  placement i:=⟨(E.placement i).color,(E.placement i).cochain+n,(E.placement i).internal+v⟩
  differential:=cochainSign (K:=K) n • E.differential
  entries:=projectiveEntries_smul Q _ E.entries
  degree i j:=by
    constructor
    · intro h
      change cochainSign (K:=K) n • E.differential i j=0
      rw [(E.degree i j).1 (by dsimp only at h; omega),smul_zero]
    · change Homogeneous Q (0+((E.placement i).internal+v)-((E.placement j).internal+v))
        (cochainSign (K:=K) n • E.differential i j)
      convert homogeneous_smul Q (E.degree i j).2 _ using 1 <;> first | (with_reducible_and_instances rfl) | (omega)
  square_zero:=by
    rw [Matrix.smul_mul,Matrix.mul_smul,smul_smul,cochainSign_mul_self,one_smul,E.square_zero]

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma sourceShift_pure (E:BasedComplex Q (K:=K) I) (n v:ℤ) {q:ℤ}
    (hE:∀ i,(E.placement i).level=q) :
    ∀ i,((sourceShift Q E n v).placement i).level=q+n+v := by
  intro i
  have hi:=hE i
  dsimp [sourceShift,GeneratorPlacement.level] at hi ⊢
  omega

omit [Fintype V] [DecidableEq A] [DecidableEq I] [DecidableEq J] in
lemma sourceShift_cycle (E:BasedComplex Q (K:=K) I) (F:BasedComplex Q (K:=K) J)
    (n v:ℤ) {f:Matrix I J (Q.Zigzag K)} (hf:f∈homCycles Q E F n v) :
    f∈homCycles Q (sourceShift Q E n v) F 0 0 := by
  refine ⟨⟨hf.1.1,?_⟩,?_⟩
  · intro i j
    constructor
    · intro h
      exact (hf.1.2 i j).1 (by dsimp [sourceShift] at h; omega)
    · change Homogeneous Q (0+((E.placement i).internal+v)-(F.placement j).internal) (f i j)
      convert (hf.1.2 i j).2 using 1 <;> first | (with_reducible_and_instances rfl) | (omega)
  · have hh:=congrArg (fun M:Matrix I J (Q.Zigzag K)=>cochainSign (K:=K) n • M) hf.2
    rw [smul_zero] at hh
    change cochainSign (K:=K) n • (E.differential*f-cochainSign (K:=K) n • (f*F.differential))=0 at hh
    rw [smul_sub,smul_smul,cochainSign_mul_self,one_smul] at hh
    change cochainSign (K:=K) n • E.differential*f-cochainSign (K:=K) 0 • (f*F.differential)=0
    simpa only [Matrix.smul_mul,cochainSign_zero,one_smul] using hh

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_PositiveWord
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

namespace FiniteModel

lemma positiveWord_class (w:List V) (E:FiniteModel.{u} Q (K:=K)) :
    classOfComplex Q (positiveWord Q w E).complex=positiveWordAction Q w (classOfComplex Q E.complex) := by
  induction w with
  | nil => rfl
  | cons α w ih =>
    change classPositiveTwist Q α (classOfComplex Q (positiveWord Q w E).complex)=
      classPositiveTwist Q α (positiveWordAction Q w (classOfComplex Q E.complex))
    rw [ih]

lemma positiveWord_homMono (hn:∀ a,Q.source a≠Q.target a) (w:List V)
    (T E F:FiniteModel.{u} Q (K:=K)) (f:Map Q E.complex F.complex)
    (h:HomMonoFrom Q T.complex f) :
    HomMonoFrom Q (positiveWord Q w T).complex (positiveWordMap Q w f) := by
  induction w with
  | nil => exact h
  | cons α w ih => exact ih.positiveTwist Q hn α
end FiniteModel

variable {I J L M:Type u} [Fintype I] [Fintype J] [Fintype L] [Fintype M]
  [DecidableEq I] [DecidableEq J] [DecidableEq L] [DecidableEq M]

omit [Fintype V] [DecidableEq A] [DecidableEq I] [DecidableEq J]
  [DecidableEq L] [DecidableEq M] in
lemma HomMonoFrom.comp {T:BasedComplex Q (K:=K) I} {E:BasedComplex Q (K:=K) J}
    {F:BasedComplex Q (K:=K) L} {G:BasedComplex Q (K:=K) M}
    {f:Map Q E F} {g:Map Q F G} (hf:HomMonoFrom Q T f) (hg:HomMonoFrom Q T g) :
    HomMonoFrom Q T (f.comp Q g) := by
  intro a ha hb
  apply hf a ha
  have hac:a*f.matrix∈homCycles Q T F 0 0 := by
    simpa only [zero_add] using homCycles_mul Q ha (map_mem_homCycles Q f)
  apply hg (a*f.matrix) hac
  simpa only [Map.comp,Matrix.mul_assoc] using hb

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma HomotopyEquivalence.homMonoFrom (T:BasedComplex Q (K:=K) I)
    {E:BasedComplex Q (K:=K) J} {F:BasedComplex Q (K:=K) L}
    (e:HomotopyEquivalence Q E F) : HomMonoFrom Q T e.forward := by
  intro g hg hb
  have hb':=homBoundary_mul_cycle Q hb (map_mem_homCycles Q e.backward)
  have hc:=homCycle_mul_boundary Q hg (e.sourceCorrection_boundary Q)
  simp only [zero_add] at hb' hc
  have hz:=(homBoundaries Q T E 0 0).sub_mem hb' hc
  rw [Matrix.mul_sub] at hz
  erw [mul_projectiveIdentity Q hg.1.1] at hz
  simpa only [Matrix.mul_assoc,sub_sub_cancel] using hz

omit [Fintype V] [DecidableEq A] [DecidableEq J] [DecidableEq L] in
lemma HomMonoFrom.sourceEquivalence
    {T:BasedComplex Q (K:=K) I} {T':BasedComplex Q (K:=K) M}
    {E:BasedComplex Q (K:=K) J} {F:BasedComplex Q (K:=K) L}
    (e:HomotopyEquivalence Q T T') {f:Map Q E F} (h:HomMonoFrom Q T f) :
    HomMonoFrom Q T' f := by
  intro g hg hb
  have hc:e.forward.matrix*g∈homCycles Q T E 0 0 := by
    simpa only [zero_add] using homCycles_mul Q (map_mem_homCycles Q e.forward) hg
  have hbc:e.forward.matrix*g*f.matrix∈homBoundaries Q T F 0 0 := by
    have hz:=homCycle_mul_boundary Q (map_mem_homCycles Q e.forward) hb
    simpa only [zero_add,Matrix.mul_assoc] using hz
  have hh:=h _ hc hbc
  have hh':=homCycle_mul_boundary Q (map_mem_homCycles Q e.backward) hh
  have hec:=homBoundary_mul_cycle Q ((e.symm Q).sourceCorrection_boundary Q) hg
  simp only [zero_add] at hh' hec
  have hz:=(homBoundaries Q T' E 0 0).sub_mem hh' hec
  change e.backward.matrix*(e.forward.matrix*g)-
    ((e.backward.matrix*e.forward.matrix-projectiveIdentity Q T'.placement)*g)∈
      homBoundaries Q T' E 0 0 at hz
  rw [Matrix.sub_mul] at hz
  erw [projectiveIdentity_mul Q hg.1.1] at hz
  simpa only [Matrix.mul_assoc,sub_sub_cancel] using hz

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_WordInverseModel
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

noncomputable def wordLowModel (w:List V) (q:ℤ) (x:FiniteHomotopyClass Q (K:=K)) :=
  FiniteModel.ofComplex Q (lowerTruncation Q (wordInverseModel Q w x).complex
    (minimalClassModel_minimal Q (inverseWordAction Q w x)) (q-1))

noncomputable def canonicalLowSource (w:List V) (q:ℤ) (x:FiniteHomotopyClass Q (K:=K)) :=
  FiniteModel.positiveWord Q w (wordLowModel Q w q x)

noncomputable def canonicalLowMap (w:List V) (q:ℤ) (x:FiniteHomotopyClass Q (K:=K)) :
    Map Q (canonicalLowSource Q w q x).complex (canonicalLowTarget Q w x).complex :=
  FiniteModel.positiveWordMap Q w (lowInclusion Q (wordInverseModel Q w x).complex
    (lowerLevelSet Q (wordInverseModel Q w x).complex (q-1))
    (levelDownClosed Q _ (minimalClassModel_minimal Q (inverseWordAction Q w x)) (q-1)))

lemma canonicalLowSource_class (w:List V) (q:ℤ) (x:FiniteHomotopyClass Q (K:=K)) :
    classOfComplex Q (canonicalLowSource Q w q x).complex=canonicalWordLow Q w q x := by
  rw [canonicalLowSource,FiniteModel.positiveWord_class]
  rfl

lemma canonicalLowTarget_class (hn:∀ a,Q.source a≠Q.target a)
    (w:List V) (x:FiniteHomotopyClass Q (K:=K)) :
    classOfComplex Q (canonicalLowTarget Q w x).complex=x := by
  rw [canonicalLowTarget,FiniteModel.positiveWord_class]
  change positiveWordAction Q w (classOfComplex Q (minimalClassModel Q (inverseWordAction Q w x)).complex)=x
  have he:classOfComplex Q (minimalClassModel Q (inverseWordAction Q w x)).complex=
      inverseWordAction Q w x:=minimalClassModel_class Q _
  rw [he,positive_inverseWord Q hn]

theorem canonicalLowMap_homMono (hn:∀ a,Q.source a≠Q.target a)
    (w:List V) (q:ℤ) (x:FiniteHomotopyClass Q (K:=K))
    (T:FiniteModel.{u} Q (K:=K)) (hT:ClassUpperBound Q q (classOfComplex Q T.complex)) :
    HomMonoFrom Q T.complex (canonicalLowMap Q w q x) := by
  let R:=wordInverseModel Q w (classOfComplex Q T.complex)
  have hR:∀ i,(R.complex.placement i).level≤(q-1)+1 := by
    intro i
    have hh:=inverseWord_upper_bound Q w (classOfComplex Q T.complex) hT i
    change (R.complex.placement i).level≤q at hh
    omega
  have hm:=FiniteModel.positiveWord_homMono Q hn w R (wordLowModel Q w q x)
    (wordInverseModel Q w x)
    (lowInclusion Q (wordInverseModel Q w x).complex
      (lowerLevelSet Q (wordInverseModel Q w x).complex (q-1))
      (levelDownClosed Q _ (minimalClassModel_minimal Q (inverseWordAction Q w x)) (q-1)))
    (lowInclusion_homMono Q R.complex (wordInverseModel Q w x).complex
      (minimalClassModel_minimal Q (inverseWordAction Q w x)) (q-1) hR)
  have he:classOfComplex Q (FiniteModel.positiveWord Q w R).complex=classOfComplex Q T.complex :=
    canonicalLowTarget_class Q hn w (classOfComplex Q T.complex)
  obtain ⟨e⟩:=Quotient.exact he
  exact hm.sourceEquivalence Q e

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_ColorSupport
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

lemma canonicalReducedWordLow_monic (hn:∀ a,Q.source a≠Q.target a)
    (U:Set V)
    (_hU:∀ α∈U,∀ β∈U,α=β ∨ OrthogonalVertices Q α β ∨ Nonempty (SimpleEdge Q α β))
    (x:FiniteHomotopyClass Q (K:=K)) (q:ℤ)
    (_hlo:ClassLowerBound Q q x) (_hhi:ClassUpperBound Q q x)
    (w:List V) (_hw:∀ s∈w,s∈U)
    (_hr:(ordinaryCoxeterMatrix Q).toCoxeterSystem.IsReduced w) :
    ∃ f:Map Q (minimalClassModel Q (canonicalWordLow Q w q x)).complex (minimalClassModel Q x).complex,
      ∀ T:FiniteModel.{u} Q (K:=K),ClassUpperBound Q q (classOfComplex Q T.complex)→
        HomMonoFrom Q T.complex f := by
  let E:=minimalClassModel Q (canonicalWordLow Q w q x)
  let F:=minimalClassModel Q x
  have he:classOfComplex Q E.complex=classOfComplex Q (canonicalLowSource Q w q x).complex :=
    (minimalClassModel_class Q _).trans (canonicalLowSource_class Q w q x).symm
  have hf:classOfComplex Q (canonicalLowTarget Q w x).complex=classOfComplex Q F.complex :=
    (canonicalLowTarget_class Q hn w x).trans (minimalClassModel_class Q x).symm
  obtain ⟨e⟩:=Quotient.exact he
  obtain ⟨f⟩:=Quotient.exact hf
  refine ⟨(e.forward.comp Q (canonicalLowMap Q w q x)).comp Q f.forward,?_⟩
  intro T hT
  exact ((e.homMonoFrom Q T.complex).comp Q
    (canonicalLowMap_homMono Q hn w q x T hT)).comp Q (f.homMonoFrom Q T.complex)

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Quivers_ClosedNeighborhood
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver
universe u
variable {V A : Type u} (Q : ReversibleQuiver V A)

lemma corner_target_mem_neighborhood {U : Set V} {α β : V} (hα : α∈U)
    (p : Zigzag.CornerPath Q α β) : β∈Q.closedNeighborhood U := by
  rcases p with ⟨x,hs,ht⟩
  rcases x with v|a|v
  · exact Or.inl (by simp only [Path.source, Path.target] at hs ht; exact ht ▸ hs.symm ▸ hα)
  · exact Or.inr ⟨α,hα,a,hs,ht⟩
  · exact Or.inl (by simp only [Path.source, Path.target] at hs ht; exact ht ▸ hs.symm ▸ hα)

end HarmonicArtin.ReversibleQuiver

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_EmptyTestIndex
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
attribute [local instance] Classical.propDecidable
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I:Type u} [Fintype I] [DecidableEq I]

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma far_test_empty (E:BasedComplex Q (K:=K) I) (U:Set V)
    (hE:∀ i,(E.placement i).color∉Q.closedNeighborhood U)
    (α:V) (hα:α∈U) : IsEmpty (TestIndex Q E.placement α) :=
  ⟨fun p=>hE p.1 (Q.corner_target_mem_neighborhood hα p.2)⟩

noncomputable def negativeTwistFar (E:BasedComplex Q (K:=K) I) (U:Set V)
    (hE:∀ i,(E.placement i).color∉Q.closedNeighborhood U)
    (α:V) (hα:α∈U) : HomotopyEquivalence Q (E.negativeTwist Q α) E := by
  let h:=far_test_empty Q E U hE α hα
  have e:=(E.negativeTwist Q α).reindexHomotopyEquivalence Q (emptyTestIndex Q E α h)
  rw [negativeTwist_empty_reindex] at e
  exact e

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_GeneratorArray2
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

universe u

variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

omit [Fintype V] [DecidableEq A] in
lemma class_eq_minimalRepresentative (E : FiniteModel.{u} Q (K := K)) :
    Quotient.mk (finiteHomotopySetoid Q) E =
      Quotient.mk (finiteHomotopySetoid Q) (E.minimalRepresentative Q) := by
  exact Quotient.sound ⟨E.minimalRepresentativeEquivalence Q⟩

lemma classPositiveTwist_exterior (x : FiniteHomotopyClass Q (K := K))
    (α : V) (a : GeneratorPlacement V) (hα : α ≠ a.color) :
    classGeneratorArray Q (classPositiveTwist Q α x) a = classGeneratorArray Q x a := by
  induction x using Quotient.inductionOn with | _ E =>
    rw [class_eq_minimalRepresentative Q E]
    let M := E.minimalRepresentative Q
    let T := FiniteModel.ofComplex Q (M.complex.positiveTwist Q α)
    change classGeneratorArray Q (Quotient.mk (finiteHomotopySetoid Q) T) a =
      classGeneratorArray Q (Quotient.mk (finiteHomotopySetoid Q) M) a
    rw [classGeneratorArray_of_minimal Q M (E.minimalRepresentative_minimal Q)]
    change (T.minimalRepresentative Q).complex.generatorArray Q a = M.complex.generatorArray Q a
    simp only [generatorArray_apply]
    refine positiveTwist_exterior_multiplicity Q M.complex _
      (E.minimalRepresentative_minimal Q) (T.minimalRepresentative_minimal Q) α
      ?_ a hα
    convert T.minimalRepresentativeEquivalence Q using 1 <;> rfl

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_SumTestEquiv
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A K I : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I]
  {T : I → Type*} [∀ i, Fintype (T i)] [∀ i, DecidableEq (T i)]

noncomputable def coefficientTopSumEquiv (E : (i:I) → BasedComplex Q (K := K) (T i))
    {l:ℤ} (hE : ∀ i x, ((E i).placement x).level=l) (α : V) (c : ℤ) :
    coefficientTopDual Q (finiteSum Q E) α c ≃ₗ[K] ((i:I) → coefficientTopDual Q (E i) α c) :=
  ((coefficientTopTestEquiv Q (finiteSum Q E) (fun x => hE x.1 x.2) α c).trans
    (finiteSumTopTestEquiv Q E α c)).trans
    (LinearEquiv.piCongrRight (fun i => (coefficientTopTestEquiv Q (E i) (hE i) α c).symm))

omit [Fintype V] [DecidableEq A] [∀ i, DecidableEq (T i)] in
lemma sumLayer_eq (E : (i:I) → BasedComplex Q (K := K) (T i))
    (hE : ∀ i, (E i).IsMinimal Q) (d : ℤ) :
    ((finiteSum Q E).pureLayer Q (finiteSum_minimal Q E hE) d).reindex Q (sumLayerEquiv Q E d) =
      finiteSum Q (fun i => (E i).pureLayer Q (hE i) d) := by
  apply ext_placement_differential Q
  · rfl
  · apply Matrix.ext
    rintro ⟨i,x⟩ ⟨j,y⟩
    change Matrix.blockDiagonal' (fun i => (E i).differential) ⟨i,x.val⟩ ⟨j,y.val⟩ =
      Matrix.blockDiagonal' (fun i => ((E i).pureLayer Q (hE i) d).differential) ⟨i,x⟩ ⟨j,y⟩
    by_cases h : i=j
    · subst j; simp only [Matrix.blockDiagonal'_apply_eq]; rfl
    · rw [Matrix.blockDiagonal'_apply_ne _ _ _ h,Matrix.blockDiagonal'_apply_ne _ _ _ h]

noncomputable def sumLayerComparison (E : (i:I) → BasedComplex Q (K := K) (T i))
    (hE : ∀ i, (E i).IsMinimal Q) (d : ℤ) :
    ChainIsomorphism Q ((finiteSum Q E).pureLayer Q (finiteSum_minimal Q E hE) d)
      (finiteSum Q (fun i => (E i).pureLayer Q (hE i) d)) := by
  have e := reindexChainIsomorphism Q
    ((finiteSum Q E).pureLayer Q (finiteSum_minimal Q E hE) d) (sumLayerEquiv Q E d)
  rw [sumLayer_eq] at e
  exact e

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_LevelArrayMinimalApply
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V]

lemma classLevelArray_minimal_apply (x:FiniteHomotopyClass Q (K:=K)) (α:V) (k:ℤ) :
    classLevelArray Q x (α,k)=Nat.card {i:(minimalClassModel Q x).Index //
      ((minimalClassModel Q x).complex.placement i).color=α ∧
      ((minimalClassModel Q x).complex.placement i).level=k} := by
  have h:=classLevelArray_complex_minimal Q (minimalClassModel Q x).complex
    (minimalClassModel_minimal Q x)
  have hx:classOfComplex Q (minimalClassModel Q x).complex=x:=minimalClassModel_class Q x
  rw [hx] at h
  rw [h,levelArray_apply]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_FiniteFamilyLevelSupport
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A:Type} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

omit [Fintype V] [DecidableEq A] in
lemma finiteFamily_level_support {R:Type} [Finite R]
    (x:R→FiniteHomotopyClass Q (K:=K)) :
    {k:ℤ | ∃ r α,classLevelArray Q (x r) (α,k)≠0}.Finite := by
  let F : Set ℤ := Set.range (fun z:Σ r:R,(minimalClassModel Q (x r)).Index=>
    ((minimalClassModel Q (x z.1)).complex.placement z.2).level)
  have hF:F.Finite:=Set.finite_range _
  apply hF.subset
  rintro k ⟨r,α,hk⟩
  rw [classLevelArray_minimal_apply] at hk
  have hn:Nonempty {i:(minimalClassModel Q (x r)).Index //
      ((minimalClassModel Q (x r)).complex.placement i).color=α ∧
      ((minimalClassModel Q (x r)).complex.placement i).level=k} :=
    Nat.card_ne_zero.mp hk |>.1
  obtain ⟨i⟩:=hn
  exact ⟨⟨r,i.val⟩,i.property.2⟩

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_HighConeIndex
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
attribute [local instance] Classical.propDecidable
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I:Type u} [Fintype I] [DecidableEq I]

noncomputable def highConePivot (E:BasedComplex Q (K:=K) I) (T:Set I)
    (h:DownClosed Q E T) : BlockPivot Q (highConeNormalized Q E T h) where
  coefficient:=1
  nonzero:=one_ne_zero
  color _:=rfl
  cochain i:=by change (E.placement i).cochain=(E.placement i).cochain-1+1; omega
  internal _:=rfl
  entry i j:=by
    change (if (i:I)=(j:I) then vertexId Q (K:=K) (E.placement i).color else 0)=
      1 • (if i=j then vertexId Q (K:=K) (E.placement i).color else 0)
    simp only [one_smul,Subtype.val_inj]

noncomputable def highConeReduction (E:BasedComplex Q (K:=K) I) (T:Set I)
    (h:DownClosed Q E T) : HomotopyEquivalence Q ((highProjection Q E T h).cone Q)
      ((highConePivot Q E T h).reduced Q) :=
  (((highProjection Q E T h).cone Q).reindexHomotopyEquivalence Q (highConeIndex T)).trans Q
    ((highConePivot Q E T h).reductionEquivalence Q)

omit [Fintype V] [DecidableEq A] in
lemma highConeRetained_level (E:BasedComplex Q (K:=K) I) (T:Set I)
    (h:DownClosed Q E T) (i:T) :
    (((highConePivot Q E T h).reduced Q).placement i).level=(E.placement i).level-1 := by
  change (E.placement i).cochain-1+(E.placement i).internal=
    (E.placement i).cochain+(E.placement i).internal-1
  omega

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_InverseMatrix
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.linearMap_pathBasis _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_base _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_left _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
open _root_.Matrix

attribute [local instance] Classical.propDecidable
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I J L:Type u} [Fintype I] [Fintype J] [Fintype L]
  [DecidableEq I] [DecidableEq J] [DecidableEq L]
  {E:BasedComplex Q (K:=K) I} {F:BasedComplex Q (K:=K) J}

omit [Fintype V] [DecidableEq A] in
lemma cone_layer_inverse_equations (f:Map Q E F) (hE:E.IsMinimal Q) (hF:F.IsMinimal Q)
    (D:BasedComplex Q (K:=K) L) (e:HomotopyEquivalence Q (f.cone Q) D)
    (q:ℤ) (hD:∀ j,(D.placement j).level≠q-1 ∧ (D.placement j).level≠q) :
    atLevel Q E.placement F.placement f.matrix q *
      atLevel Q F.placement E.placement (-e.sourceHomotopy.toBlocks₂₁) q=
        projectiveIdentity Q (E.pureLayer Q hE q).placement ∧
    atLevel Q F.placement E.placement (-e.sourceHomotopy.toBlocks₂₁) q *
      atLevel Q E.placement F.placement f.matrix q=
        projectiveIdentity Q (F.pureLayer Q hF q).placement := by
  have hdeg:=cone_homotopy_degree21 Q f e.sourceHomotopy e.sourceDegree
  have hb:∀ i j,e.sourceHomotopy.toBlocks₂₁ i j≠0→
      (E.placement j).level≤(F.placement i).level := by
    intro i j hij
    simpa using mapDegree_level_bound Q hdeg hij
  have hs:=congrArg (fun m=>atLevel Q E.placement E.placement m.toBlocks₁₁ q) e.sourceEquation
  have ht:=congrArg (fun m=>atLevel Q F.placement F.placement m.toBlocks₂₂ q) e.sourceEquation
  have hz₁:atLevel Q E.placement E.placement
      (e.forward.matrix*e.backward.matrix).toBlocks₁₁ q=0 := by
    apply Matrix.ext
    intro i j
    apply through_absent_level_zero Q D e.forward e.backward (q-1) (fun k=>(hD k).1) (.inl i.val) (.inl j.val)
    · change (E.placement i.val).cochain-1+(E.placement i.val).internal=q-1
      have hh:=i.property; dsimp [GeneratorPlacement.level] at hh; omega
    · change (E.placement j.val).cochain-1+(E.placement j.val).internal=q-1
      have hh:=j.property; dsimp [GeneratorPlacement.level] at hh; omega
  have hz₂:atLevel Q F.placement F.placement
      (e.forward.matrix*e.backward.matrix).toBlocks₂₂ q=0 := by
    apply Matrix.ext
    intro i j
    exact through_absent_level_zero Q D e.forward e.backward q (fun k=>(hD k).2)
      (.inr i.val) (.inr j.val) i.property j.property
  rw [hz₁] at hs
  rw [hz₂] at ht
  change 0=atLevel Q E.placement E.placement
    ((projectiveIdentity Q (f.cone Q).placement).toBlocks₁₁+
      ((f.cone Q).differential*e.sourceHomotopy+
        e.sourceHomotopy*(f.cone Q).differential).toBlocks₁₁) q at hs
  change 0=atLevel Q F.placement F.placement
    ((projectiveIdentity Q (f.cone Q).placement).toBlocks₂₂+
      ((f.cone Q).differential*e.sourceHomotopy+
        e.sourceHomotopy*(f.cone Q).differential).toBlocks₂₂) q at ht
  rw [cone_identity_blocks,Matrix.toBlocks_fromBlocks₁₁,cone_homotopy_source_block,
    atLevel_add,atLevel_add,atLevel_identity] at hs
  rw [cone_identity_blocks,Matrix.toBlocks_fromBlocks₂₂,cone_homotopy_target_block,
    atLevel_add,atLevel_add,atLevel_identity] at ht
  have he₁:=atLevel_homotopy_boundary Q E hE e.sourceHomotopy.toBlocks₁₁
    (cone_homotopy_degree11 Q f _ e.sourceDegree) q
  have he₂:=atLevel_homotopy_boundary Q F hF e.sourceHomotopy.toBlocks₂₂
    (cone_homotopy_degree22 Q f _ e.sourceDegree) q
  change 0=projectiveIdentity Q _+(-atLevel Q E.placement E.placement
    (E.differential*e.sourceHomotopy.toBlocks₁₁+e.sourceHomotopy.toBlocks₁₁*E.differential) q+
      atLevel Q E.placement E.placement (f.matrix*e.sourceHomotopy.toBlocks₂₁) q) at hs
  rw [he₁,neg_zero,zero_add,atLevel_mul Q _ _ _ _ _ q (map_level_bound Q f) hb] at hs
  rw [he₂,zero_add,atLevel_mul Q _ _ _ _ _ q hb (map_level_bound Q f)] at ht
  have hn : atLevel Q F.placement E.placement (-e.sourceHomotopy.toBlocks₂₁) q =
      -atLevel Q F.placement E.placement e.sourceHomotopy.toBlocks₂₁ q := by
    apply Matrix.ext
    intro i j
    rfl
  rw [hn]
  constructor
  ·
    rw [Matrix.mul_neg]
    exact (neg_eq_iff_eq_neg).mpr (eq_neg_of_add_eq_zero_right hs.symm)
  ·
    rw [Matrix.neg_mul]
    exact (neg_eq_iff_eq_neg).mpr (eq_neg_of_add_eq_zero_right ht.symm)

noncomputable def coneLayerIsomorphism (f:Map Q E F) (hE:E.IsMinimal Q) (hF:F.IsMinimal Q)
    (D:BasedComplex Q (K:=K) L) (e:HomotopyEquivalence Q (f.cone Q) D)
    (q:ℤ) (hD:∀ j,(D.placement j).level≠q-1 ∧ (D.placement j).level≠q) :
    ChainIsomorphism Q (E.pureLayer Q hE q) (F.pureLayer Q hF q) := by
  let a:=f.pureLayer Q hE hF q
  let b:=atLevel Q F.placement E.placement (-e.sourceHomotopy.toBlocks₂₁) q
  have he:ProjectiveEntries Q F.placement E.placement e.sourceHomotopy.toBlocks₂₁ :=
    ⟨fun i j=>e.sourceEntries.1 (.inr i) (.inl j),
      fun i j=>e.sourceEntries.2 (.inr i) (.inl j)⟩
  have heb:=projectiveEntries_neg Q he
  have hb:ProjectiveEntries Q (F.pureLayer Q hF q).placement
      (E.pureLayer Q hE q).placement b :=
    ⟨fun i j=>heb.1 i.val j.val,fun i j=>heb.2 i.val j.val⟩
  have hdeg:=mapDegree_neg Q (cone_homotopy_degree21 Q f _ e.sourceDegree)
  have hd:MapDegree Q (F.pureLayer Q hF q).placement
      (E.pureLayer Q hE q).placement 0 0 b :=fun i j=>hdeg i.val j.val
  have hh:=cone_layer_inverse_equations Q f hE hF D e q hD
  exact ⟨a,a.inverseMatrix Q b hb hd hh.1 hh.2,hh.1,hh.2⟩

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_PositiveConeIndex
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
open _root_.Matrix

attribute [local instance] Classical.propDecidable
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I J:Type u} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {E:BasedComplex Q (K:=K) I} {F:BasedComplex Q (K:=K) J}

noncomputable def positiveTwistCone (f:Map Q E F) (α:V) :
    ChainIsomorphism Q ((f.cone Q).positiveTwist Q α) ((f.positiveTwist Q α).cone Q) :=
  (reindexChainIsomorphism Q _ (positiveConeIndex Q f α)).trans Q
    (signChainIsomorphism Q _ _ (positiveConeSign Q α)
      (positiveCone_placement Q f α) (positiveCone_differential Q f α))

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_HighConeRetainedPure
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
attribute [local instance] Classical.propDecidable
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I J:Type u} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

omit [Fintype V] [DecidableEq A] in
lemma highConeRetained_differential (E:BasedComplex Q (K:=K) I) (T:Set I)
    (h:DownClosed Q E T) (i j:T) :
    ((highConePivot Q E T h).reduced Q).differential i j= -E.differential i j := by
  rw [BlockPivot.reduced_differential]
  have hz (k:(Tᶜ:Set I)) :
      (highConeNormalized Q E T h).differential (.inr (.inr i)) (.inr (.inl k))=0 := by
    change (highProjection Q E T h).matrix i k=0
    change (if (i:I)=(k:I) then vertexId Q (K:=K) (E.placement i).color else 0)=0
    have hne:(i:I)≠(k:I):=fun he=>k.property (he ▸ i.property)
    exact ite_eq_right hne
  simp only [hz,smul_zero,zero_mul,Finset.sum_const_zero,sub_zero]
  rfl

omit [Fintype V] [DecidableEq A] in
lemma highConeRetained_minimal (E:BasedComplex Q (K:=K) I) (hE:E.IsMinimal Q)
    (T:Set I) (h:DownClosed Q E T) :
    ((highConePivot Q E T h).reduced Q).IsMinimal Q := by
  intro i j
  funext α
  rw [highConeRetained_differential]
  change -(E.differential i j).vertex α=0
  have hh:=congrFun (hE i j) α
  change (E.differential i j).vertex α=0 at hh
  rw [hh,neg_zero]

noncomputable def highConeRetainedPureIndex (E:BasedComplex Q (K:=K) I)
    (hE:E.IsMinimal Q) (q:ℤ) :
    {i:I // (E.placement i).level=q-1} ≃
      {i:lowerLevelSet Q E (q-1) //
        (((highConePivot Q E _ (levelDownClosed Q E hE (q-1))).reduced Q).placement i).level=q-2} where
  toFun i:=⟨⟨i.val,le_of_eq i.property⟩,by
    rw [highConeRetained_level]
    have hi:=i.property
    change (E.placement i.val).level-1=q-2
    omega⟩
  invFun i:=⟨i.val.val,by
    have hi:=i.property
    rw [highConeRetained_level] at hi
    omega⟩
  left_inv _:=rfl
  right_inv _:=rfl

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_ScalarExactNotZero
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

lemma initialClass_test_not_exact (α β:V) (p:Zigzag.CornerPath Q α β) :
    ¬ClassTestExact Q α (Path.length p.val) 0 (initialClass Q (K:=K) β) := by
  let E:=initialProjective Q (K:=K) β
  change ¬ScalarExactAt Q (E.testComplex Q α) α _ _
  have hd:(E.testComplex Q α).differential=0 := by
    change scalarCornerMatrix Q α (testMatrix Q E.placement E.placement α 0)=0
    rw [testMatrix_zero,scalarCornerMatrix_zero]
  simpa only [E,testComplex,testPlacement,initialProjective,GeneratorPlacement.level,
    zero_add] using scalarExact_not_of_zero_differential Q (E.testComplex Q α) α hd ⟨PUnit.unit,p⟩

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_InitialProbeTestUpper
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.linearMap_pathBasis _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_base _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_left _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A:Type} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A]
  [DecidableEq (ProbeVertex V)] [DecidableEq (ProbeArrow V A)]
local notation "R" => probeQuiver Q

lemma initialProbe_test_upper (α:V) (b:Bool) (U:Set (ProbeVertex V))
    (hU:U⊆Set.range (Sum.inl:V→ProbeVertex V)) :
    ClassTestUpper R (initialClass R (K:=K) (.inr (α,b))) U 1 := by
  intro β hβ l hl c
  obtain ⟨β,rfl⟩:=hU hβ
  change ScalarExactAt R ((initialProjective R (.inr (α,b))).testComplex R (.inl β)) _ _ _
  apply scalarExact_of_absent_degree R
  rintro ⟨i,⟨p,hs,ht⟩⟩ he
  change Path.target R p=Sum.inr (α,b) at ht
  dsimp only [testComplex,testPlacement,initialProjective,GeneratorPlacement.level] at he
  rcases p with a|a|a
  · exact Sum.inl_ne_inr ((hs.symm.trans ht))
  · norm_num [Path.length] at he; omega
  · exact Sum.inl_ne_inr ((hs.symm.trans ht))

lemma initialProbe_top_not_exact (α:V) (b:Bool) :
    ¬ClassTestExact R (.inl α) 1 0 (initialClass R (K:=K) (.inr (α,b))) :=
  initialClass_test_not_exact R (.inl α) (.inr (α,b))
    ⟨.inr (.inl (.inr (α,b,false))),rfl,rfl⟩

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_IsolatedIndexCycle
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.linearMap_pathBasis _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_base _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_left _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_right _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.corner_val _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_reverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K I:Type*} (Q:ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A] [Fintype I] [DecidableEq I]

lemma eq_isolated_index (E:BasedComplex Q (K:=K) I) (hE:E.IsMinimal Q)
    (hd:homDimension Q E E 0 0≤1) (i:I)
    (hr:∀j,E.differential i j=0) (hc:∀j,E.differential j i=0) (j:I) : j=i := by
  by_contra hji
  let f:=Matrix.single i i (vertexId Q (K:=K) (E.placement i).color)
  have hf:=isolated_index_cycle Q E i hr hc
  have hb:f∈homBoundaries Q E E 0 0 := by
    apply boundary_of_homDimension_le_one Q E E 0 0 hd (diagonalVertex Q E j)
      (fun _ h=>diagonalVertex_boundary Q E hE j 0 0 h) (identity_mem_homCycles Q E)
    · rw [diagonalVertex_identity]; exact one_ne_zero
    · exact hf
    · change (f j j).vertex (E.placement j).color=0
      simp [f,Ne.symm hji]
  have hz:=diagonalVertex_boundary Q E hE i 0 0 hb
  change (f i i).vertex (E.placement i).color=0 at hz
  simp only [f,Matrix.single_apply_same,vertexId_eval] at hz
  exact one_ne_zero hz

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_LayerTotalHomDimension
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A:Type u} {K:Type*} [Field K] (Q:ReversibleQuiver V A)
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

noncomputable def classLayerTotalHomDimension (x y:FiniteHomotopyClass Q (K:=K))
    (l k t:ℤ) : ℕ :=
  totalHomDimension Q
    ((minimalClassModel Q x).complex.pureLayer Q (minimalClassModel_minimal Q x) l)
    ((minimalClassModel Q y).complex.pureLayer Q (minimalClassModel_minimal Q y) k) t

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_NegativeConeIndex
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
open _root_.Matrix

attribute [local instance] Classical.propDecidable
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I J:Type u} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {E:BasedComplex Q (K:=K) I} {F:BasedComplex Q (K:=K) J}

noncomputable def negativeTwistCone (f:Map Q E F) (α:V) :
    ChainIsomorphism Q ((f.cone Q).negativeTwist Q α) ((f.negativeTwist Q α).cone Q) :=
  (reindexChainIsomorphism Q _ (negativeConeIndex Q f α)).trans Q
    (signChainIsomorphism Q _ _ (negativeConeSign Q α)
      (negativeCone_placement Q f α) (negativeCone_differential Q f α))

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_PositiveWordActionTest
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.linearMap_pathBasis _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_base _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_left _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

lemma positiveWordAction_testUpper (hn:∀a,Q.source a≠Q.target a)
    (w:List V) (x:FiniteHomotopyClass Q (K:=K)) (U:Set V) (hw:∀s∈w,s∈U)
    (t:ℤ) (hx:ClassTestUpper Q x U t) :
    ClassTestUpper Q (positiveWordAction Q w x) U (t+w.length) := by
  induction w with
  | nil=>simpa only [positiveWordAction,List.length_nil,Int.natCast_zero,add_zero] using hx
  | cons α w ih=>
    have h:=classPositiveTwist_testUpper Q hn (positiveWordAction Q w x) U α (hw α (by simp))
      (ih (fun β hβ=>hw β (List.mem_cons_of_mem _ hβ)))
    simpa only [positiveWordAction,List.length_cons,Int.natCast_add,Int.natCast_one,add_assoc] using h

lemma exists_top_test (x:FiniteHomotopyClass Q (K:=K)) (U:Set V) (t:ℤ)
    (hex:∃n:ℕ,ClassTestUpper Q x U (t+n)) (hnot:¬ClassTestUpper Q x U t) :
    ∃l:ℤ,t<l ∧ ClassTestUpper Q x U l ∧ ∃α∈U,∃c,¬ClassTestExact Q α l c x := by
  let n:=Nat.find hex
  have hn:ClassTestUpper Q x U (t+n):=Nat.find_spec hex
  have hpos:0<n:=by
    by_contra hh
    have :n=0:=by omega
    apply hnot
    simpa only [this,Int.natCast_zero,add_zero] using hn
  have hprev:¬ClassTestUpper Q x U (t+n-1):=by
    intro hh
    have he:t+((n-1:ℕ):ℤ)=t+n-1:=by omega
    have :=Nat.find_min hex (show n-1<n by omega)
    exact this (by rw [he]; exact hh)
  refine ⟨t+n,by omega,hn,?_⟩
  by_contra hh
  apply hprev
  intro α hα l hl c
  by_cases he:l=t+n
  · subst l
    by_contra hc
    exact hh ⟨α,hα,c,hc⟩
  · exact hn α hα l (by omega) c

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_ProbeFixedNoDiagonal
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.linearMap_pathBasis _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_base _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_left _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A:Type} {K:Type*} [Field K] [Fintype V] [Fintype A]
  (Q:ReversibleQuiver V A) [DecidableEq (ProbeVertex V)]
attribute [local instance] Classical.decEq Classical.propDecidable
local notation "R" => probeQuiver Q

theorem probeClass_fixed_of_no_diagonal (x:FiniteHomotopyClass R (K:=K))
    (α:V) (b:Bool)
    (hz:∀n u,classGeneratorArray R x ⟨.inl α,n,u⟩=0)
    (hout:∀n u,classGeneratorArray R x ⟨.inr (α,b),n,u⟩=if n=0 ∧ u=0 then 1 else 0)
    (hdim:classHomDimension R 0 0 x x≤1) : x=initialClass R (.inr (α,b)) := by
  cases Subsingleton.elim (inferInstance : DecidableEq (ProbeVertex V))
    (@instDecidableEqSum V (V×Bool) (Classical.decEq V)
      (@instDecidableEqProd V Bool (Classical.decEq V) inferInstance))
  let : DecidableEq (ProbeVertex V) :=
    @instDecidableEqSum V (V×Bool) (Classical.decEq V)
      (@instDecidableEqProd V Bool (Classical.decEq V) inferInstance)
  let E:=minimalClassModel R x
  have hm:E.complex.IsMinimal R:=minimalClassModel_minimal R x
  have harray:E.complex.generatorArray R=classGeneratorArray R x := by
    calc
      _ = classGeneratorArray R (Quotient.mk (finiteHomotopySetoid R) E) :=
        (classGeneratorArray_of_minimal R E hm).symm
      _ = _ := congrArg (classGeneratorArray R) (minimalClassModel_class R x)
  have hpos:∀i,0 < classGeneratorArray R x (E.complex.placement i) := by
    intro i
    rw [← harray]
    exact generatorArray_placement_pos Q _ i
  have hone:E.complex.generatorArray R ⟨.inr (α,b),0,0⟩=1 := by
    rw [harray,hout]; simp
  rw [generatorArray_apply] at hone
  change Nat.card {i:E.Index // E.complex.placement i=⟨.inr (α,b),0,0⟩}=1 at hone
  have : Nonempty {i:E.Index // E.complex.placement i=⟨.inr (α,b),0,0⟩} :=
    (Nat.card_pos_iff.mp (show 0<Nat.card {i:E.Index // E.complex.placement i=⟨.inr (α,b),0,0⟩} by omega)).1
  obtain ⟨i,hi⟩:=‹Nonempty {i:E.Index // E.complex.placement i=⟨.inr (α,b),0,0⟩}›
  have hcore:∀j,(E.complex.placement j).color≠.inl α := by
    intro j hj
    have hp:=hpos j
    have hp' := hz (E.complex.placement j).cochain (E.complex.placement j).internal
    have he:E.complex.placement j=⟨.inl α,(E.complex.placement j).cochain,
        (E.complex.placement j).internal⟩ := by rw [← hj]
    rw [he] at hp
    change 0 < classGeneratorArray R x _ at hp
    omega
  have hf:∀j,(E.complex.placement j).color=.inr (α,b)→(E.complex.placement j).cochain=0 := by
    intro j hj
    have hp:=hpos j
    have he:E.complex.placement j=⟨.inr (α,b),(E.complex.placement j).cochain,
        (E.complex.placement j).internal⟩ := by rw [← hj]
    rw [he,hout] at hp
    split_ifs at hp with h
    · exact h.1
    · omega
  have hr:∀j,E.complex.differential i j=0:=
    probe_differential_row_zero Q E.complex α b hcore hf i (congrArg GeneratorPlacement.color hi)
  have hc:∀j,E.complex.differential j i=0:=
    probe_differential_col_zero Q E.complex α b hcore hf i (congrArg GeneratorPlacement.color hi)
  have hd:homDimension R E.complex E.complex 0 0≤1 := by
    change homDimension R (minimalClassModel R x).complex (minimalClassModel R x).complex 0 0≤1
    rw [minimalClassModel_homDimension]
    exact hdim
  have hall:∀j:E.Index,j=i:=eq_isolated_index R E.complex hm hd i hr hc
  let e:PUnit.{1}≃E.Index :=
    { toFun:=fun _=>i,invFun:=fun _=>PUnit.unit,
      left_inv:=fun _=>rfl,right_inv:=fun j=>(hall j).symm }
  have he:E.complex.reindex R e=initialProjective R (.inr (α,b)) := by
    apply ext_placement_differential R
    · funext j
      exact hi
    · apply Matrix.ext
      intro j k
      exact hr i
  have h₁ : x=classOfComplex R E.complex := (minimalClassModel_class R x).symm
  have h₂ : classOfComplex R E.complex=classOfComplex R (E.complex.reindex R e) :=
    classOfComplex_reindex R E.complex e
  have h₃ : classOfComplex R (E.complex.reindex R e)=initialClass R (.inr (α,b)) := by
    rw [he]; rfl
  exact h₁.trans (h₂.trans h₃)

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_PureLayerSelf
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
attribute [local instance] Classical.propDecidable
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I J T:Type u} [Fintype I] [Fintype J] [Fintype T]
  [DecidableEq I] [DecidableEq J] [DecidableEq T]

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma pure_minimal (E:BasedComplex Q (K:=K) I) {q:ℤ}
    (hE:∀ i,(E.placement i).level=q) : E.IsMinimal Q := by
  intro i j
  exact (pure_differential_linear Q E hE i j).1

noncomputable def pureLayerSelf (E:BasedComplex Q (K:=K) I) {q:ℤ}
    (hE:∀ i,(E.placement i).level=q) :
    ChainIsomorphism Q E (E.pureLayer Q (pure_minimal Q E hE) q) := by
  let e:=reindexChainIsomorphism Q (E.pureLayer Q (pure_minimal Q E hE) q) (allPureIndex Q E q hE)
  have he:(E.pureLayer Q (pure_minimal Q E hE) q).reindex Q (allPureIndex Q E q hE)=E := by
    apply ext_placement_differential Q <;> rfl
  rw [he] at e
  exact e.symm Q

noncomputable def HomotopyEquivalence.ofPure
    {E:BasedComplex Q (K:=K) I} {F:BasedComplex Q (K:=K) J}
    (e:HomotopyEquivalence Q E F) {q:ℤ}
    (hE:∀ i,(E.placement i).level=q) (hF:∀ j,(F.placement j).level=q) :
    ChainIsomorphism Q E F :=
  ((pureLayerSelf Q E hE).trans Q
    (e.pureLayer Q (pure_minimal Q E hE) (pure_minimal Q F hF) q)).trans Q
      ((pureLayerSelf Q F hF).symm Q)

omit [Fintype V] [DecidableEq A] [DecidableEq I] [DecidableEq J] in
lemma pureMap_zero_off_colors
    {E:BasedComplex Q (K:=K) I} {F:BasedComplex Q (K:=K) J}
    (f:Map Q E F) {q:ℤ} (hE:∀ i,(E.placement i).level=q) (hF:∀ j,(F.placement j).level=q)
    (U:Set V) (hs:∀ i,(E.placement i).color∈U)
    (i:I) (j:J) (hj:(F.placement j).color∉U) : f.matrix i j=0 := by
  rw [map_coefficient_entry Q f (pureMap_coefficient Q f q hE hF)]
  have hne:(F.placement j).color≠(E.placement i).color:=fun h=>hj (h.symm ▸ hs i)
  change (f.matrix i j).vertex (F.placement j).color • _=0
  rw [entry_vertex_left_support Q f.entries i j _ hne,zero_smul]

noncomputable def TermwiseSplitInjection.colorTarget
    {E:BasedComplex Q (K:=K) I} {F:BasedComplex Q (K:=K) J}
    (a:TermwiseSplitInjection Q E F) {q:ℤ}
    (hE:∀ i,(E.placement i).level=q) (hF:∀ j,(F.placement j).level=q)
    (U:Set V) (hs:∀ i,(E.placement i).color∈U)
    (hb:∀ j,(F.placement j).color∉colorBoundary Q U) :
    TermwiseSplitInjection Q E (colorRestriction Q F U hF hb) where
  inclusion:=Map.comp Q a.inclusion (blockProjectionMap Q F
    {j:J | (F.placement j).color∈U} (pure_color_block Q F U hF hb))
  retraction:=a.retraction.submatrix Subtype.val id
  split:=by
    apply Matrix.ext
    intro i j
    change (∑ k:{k:J // (F.placement k).color∈U},
      (a.inclusion.matrix*blockProjection Q F {j:J | (F.placement j).color∈U}) i k * a.retraction k j)=_
    rw [mul_blockProjection Q F {j:J | (F.placement j).color∈U} _ _ a.inclusion.entries,← a.split]
    change (∑ k:{k:J // (F.placement k).color∈U},a.inclusion.matrix i k*a.retraction k j)=
      ∑ k:J,a.inclusion.matrix i k*a.retraction k j
    apply Fintype.sum_of_injective (Subtype.val : {k:J // (F.placement k).color∈U}→J) Subtype.val_injective
    · intro k hk
      have hn:(F.placement k).color∉U:=fun h=>hk ⟨⟨k,h⟩,rfl⟩
      rw [pureMap_zero_off_colors Q a.inclusion hE hF U hs i k hn,zero_mul]
    · intro k;rfl

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_SumTruncationEquiv
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A K I : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I]
  {T : I → Type*} [∀ i, Fintype (T i)] [∀ i, DecidableEq (T i)]
attribute [local instance] Classical.decEq Classical.propDecidable

omit [Fintype V] [DecidableEq A] [∀ i, DecidableEq (T i)] in
lemma sumTruncation_eq (E : (i:I) → BasedComplex Q (K:=K) (T i))
    (hE:∀ i,(E i).IsMinimal Q) (d:ℤ) :
    (lowerTruncation Q (finiteSum Q E) (finiteSum_minimal Q E hE) d).reindex Q
      (sumTruncationEquiv Q E d)=finiteSum Q (fun i=>lowerTruncation Q (E i) (hE i) d) := by
  apply ext_placement_differential Q
  · rfl
  · apply Matrix.ext
    rintro ⟨i,x⟩ ⟨j,y⟩
    change Matrix.blockDiagonal' (fun i=>(E i).differential) ⟨i,x.val⟩ ⟨j,y.val⟩=
      Matrix.blockDiagonal' (fun i=>(lowerTruncation Q (E i) (hE i) d).differential) ⟨i,x⟩ ⟨j,y⟩
    by_cases h:i=j
    · subst j; simp only [Matrix.blockDiagonal'_apply_eq]; rfl
    · rw [Matrix.blockDiagonal'_apply_ne _ _ _ h,Matrix.blockDiagonal'_apply_ne _ _ _ h]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Functors_ComplexLowerTruncation
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Iso
attribute [local instance] Classical.decEq Classical.propDecidable
open Zigzag Zigzag.BasedComplex

universe u
variable {V A W B:Type u} {K:Type*} {Q:ReversibleQuiver V A} {R:ReversibleQuiver W B}
  (e:Iso Q R) [Field K] [Fintype V] [Fintype W] [Fintype A] [Fintype B]
  [DecidableEq V] [DecidableEq W] [DecidableEq A] [DecidableEq B]
  {I:Type u} [Fintype I] [DecidableEq I]

omit [Fintype V] [Fintype W] [DecidableEq A] [DecidableEq B] [DecidableEq I] in
lemma complex_lowerTruncation (E:BasedComplex Q (K:=K) I) (hE:E.IsMinimal Q) (d:ℤ) :
    e.complex (lowerTruncation Q E hE d)=lowerTruncation R (e.complex E) (e.complex_minimal hE) d := rfl

end HarmonicArtin.ReversibleQuiver.Iso

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Functors_SupportedCycles
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Iso
open Zigzag Zigzag.BasedComplex

variable {V A W B K : Type*} {Q : ReversibleQuiver V A} {R : ReversibleQuiver W B}
  (e : Iso Q R) [Field K] [Fintype V] [Fintype W] [Fintype A] [Fintype B]
  [DecidableEq V] [DecidableEq W] [DecidableEq A] [DecidableEq B]
  {I : Type*} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
lemma test_matrix_reindex (E:BasedComplex Q (K := K) I) (α:V) :
    (testMatrix R (e.complex E).placement (e.complex E).placement (e.vertex α) (e.complex E).differential).submatrix
      (e.testIndex E.placement α) (e.testIndex E.placement α) =
      testMatrix Q E.placement E.placement α E.differential := by
  apply Matrix.ext
  intro i j
  exact e.test_matrix _ _ _ _ i j

omit [Fintype V] [Fintype W] [DecidableEq A] [DecidableEq B] [DecidableEq I] in
lemma test_support_reindex (E:BasedComplex Q (K := K) I) (α:V) (c n:ℤ) :
    (fun i : TestIndex R (e.complex E).placement (e.vertex α) =>
      ((e.complex E).placement i.1).cochain=c ∧ Path.length i.2.val=n) ∘ e.testIndex E.placement α =
      (fun i : TestIndex Q E.placement α => (E.placement i.1).cochain=c ∧ Path.length i.2.val=n) := by
  funext i
  change (_ ∧ Path.length (e.path i.2.val)=n) = _
  rw [e.path_length]
  rfl

noncomputable def dualSupportedCycles (E:BasedComplex Q (K := K) I) (α:V) (c n:ℤ) :
    ScalarCycles.supportedKernel (testMatrix Q E.placement E.placement α E.differential).transpose
      (fun i => (E.placement i.1).cochain=c ∧ Path.length i.2.val=n) ≃ₗ[K]
    ScalarCycles.supportedKernel
      (testMatrix R (e.complex E).placement (e.complex E).placement (e.vertex α) (e.complex E).differential).transpose
      (fun i => ((e.complex E).placement i.1).cochain=c ∧ Path.length i.2.val=n) := by
  apply LinearEquiv.symm
  refine (ScalarCycles.reindexEquiv
    (testMatrix R (e.complex E).placement (e.complex E).placement (e.vertex α) (e.complex E).differential).transpose
    (fun i => ((e.complex E).placement i.1).cochain=c ∧ Path.length i.2.val=n) (e.testIndex E.placement α)).trans
    (ScalarCycles.congrEquiv _ _ _ _ ?_ (e.test_support_reindex E α c n))
  exact (Matrix.transpose_submatrix _ _ _).symm.trans (congrArg Matrix.transpose (e.test_matrix_reindex E α))

noncomputable def coefficientTopDual (E:BasedComplex Q (K := K) I) {l:ℤ}
    (hE:∀ i,(E.placement i).level=l) (α:V) (c:ℤ) :
    BasedComplex.coefficientTopDual Q E α c ≃ₗ[K]
      BasedComplex.coefficientTopDual R (e.complex E) (e.vertex α) c :=
  (coefficientTopTestEquiv Q E hE α c).trans ((e.dualSupportedCycles E α c 2).trans
    (coefficientTopTestEquiv R (e.complex E) hE (e.vertex α) c).symm)

end HarmonicArtin.ReversibleQuiver.Iso

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Functors_ComplexPureLayer
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Iso
open Zigzag Zigzag.BasedComplex

universe u
attribute [local instance] Classical.propDecidable
variable {V A W B : Type u} {K : Type*} {Q : ReversibleQuiver V A} {R : ReversibleQuiver W B}
  (e : Iso Q R) [Field K] [Fintype V] [Fintype W] [Fintype A] [Fintype B]
  [DecidableEq V] [DecidableEq W] [DecidableEq A] [DecidableEq B]
  {I : Type u} [Fintype I] [DecidableEq I]

omit [Fintype V] [Fintype W] [DecidableEq A] [DecidableEq B] [DecidableEq I] in
lemma complex_pureLayer (E:BasedComplex Q (K := K) I) (hE:E.IsMinimal Q) (d:ℤ) :
    e.complex (E.pureLayer Q hE d) =
      (e.complex E).pureLayer R (e.complex_minimal hE) d := rfl

end HarmonicArtin.ReversibleQuiver.Iso

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Functors_HomDimensionFlexible
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.ProbeEmbedding
open Zigzag Zigzag.BasedComplex

variable {V A:Type} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A]
  [DecidableEq V] [DecidableEq A] [DecidableEq (ProbeVertex V)] [DecidableEq (ProbeArrow V A)]
attribute [local instance] Classical.decEq Classical.propDecidable
local notation "R" => probeQuiver Q
variable (hn:∀a,Q.source a≠Q.target a)

omit [DecidableEq V] [DecidableEq A] in
lemma twistProd_homDimension (w:List V) (x y:FiniteHomotopyClass R (K:=K)) (n v:ℤ) :
    classHomDimension R n v
      (((w.map (fun v=>classTwistPerm R (probeQuiver_no_loops Q hn) (.inl v))).prod) x)
      (((w.map (fun v=>classTwistPerm R (probeQuiver_no_loops Q hn) (.inl v))).prod) y)=
      classHomDimension R n v x y := by
  induction w generalizing x y with
  | nil=>rfl
  | cons a w ih=>
    simp only [List.map_cons,List.prod_cons,Equiv.Perm.mul_apply]
    rw [show ∀x y,classHomDimension R n v
        (classTwistPerm R (probeQuiver_no_loops Q hn) (.inl a) x)
        (classTwistPerm R (probeQuiver_no_loops Q hn) (.inl a) y)=classHomDimension R n v x y
      from classPositiveTwist_homDimension R (probeQuiver_no_loops Q hn) (.inl a) n v]
    exact ih x y

end HarmonicArtin.ReversibleQuiver.ProbeEmbedding

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Functors_LeftSocleIndexEquiv
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.StringFunctor
attribute [local instance] Classical.propDecidable
variable {V B J K T : Type*} (Q : ReversibleQuiver V B)
  (step : B → Bool) (hstep : ∀ b, step (Q.reverse b) = step b)
  (N : J → J → Prop) (hN : ∀ ⦃first second⦄, N first second → N second first)
  [Fintype V] [Fintype B] [Fintype J]
  [DecidableEq V] [DecidableEq B] [DecidableEq J] [DecidableRel N] [Field K]
  (orient : B → Bool) (μ : J → K) (A : K)
local notation "U" => Q.stringQuiver step hstep N hN
variable [Fintype T] [DecidableEq T]

def leftSocleIndexEquiv (p : T → GeneratorPlacement (V × J)) (u:V) (c:J) :
    ((a : {a:J // N a c}) × Zigzag.TestIndex U p (u,a)) ≃
      LeftHomIndex Q step hstep N hN p u c where
  toFun x := ⟨x.2.1,x.1,x.2.2⟩
  invFun x := ⟨x.2.1,x.1,x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

omit [DecidableEq B] [Fintype T] [DecidableEq T] in
lemma leftSocle_differential (p : T → GeneratorPlacement (V × J)) (u:V) (c:J)
    (D : Matrix T T (Zigzag U K)) :
    (leftHomMatrix Q step hstep N hN p p u c D).submatrix
      (leftSocleIndexEquiv Q step hstep N hN p u c)
      (leftSocleIndexEquiv Q step hstep N hN p u c) =
    Matrix.blockDiagonal' (fun a : {a:J // N a c} => Zigzag.testMatrix U p p (u,a) D) := by
  apply Matrix.ext
  rintro ⟨a,i,x⟩ ⟨b,j,y⟩
  by_cases hab : a=b
  · subst b
    simp only [Matrix.submatrix_apply,leftSocleIndexEquiv,Equiv.coe_fn_mk,leftHomMatrix,
      ite_true, if_true,Matrix.blockDiagonal'_apply_eq,Zigzag.testMatrix]
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hab]
    exact ite_eq_right hab

end HarmonicArtin.ReversibleQuiver.StringFunctor

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Functors_HomDualSupportedCycles
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.StringFunctor
attribute [local instance] Classical.propDecidable
variable {V B J K T : Type*} (Q : ReversibleQuiver V B)
  (step : B → Bool) (hstep : ∀ b, step (Q.reverse b) = step b)
  (N : J → J → Prop) (hN : ∀ ⦃first second⦄, N first second → N second first)
  [Fintype V] [Fintype B] [Fintype J]
  [DecidableEq V] [DecidableEq B] [DecidableEq J] [DecidableRel N] [Field K]
  (orient : B → Bool) (μ : J → K) (A : K)
local notation "U" => Q.stringQuiver step hstep N hN
variable [Fintype T] [DecidableEq T]
    (ho : ∀ b, orient (Q.reverse b) = !(orient b))
    (hμ : ∀ a, μ a ≠ 0) (δ : K)
    (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
    (hPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, μ b = δ * μ a)

noncomputable def homDualSupportedCyclesEquiv
    (E : Zigzag.BasedComplex U (K := K) T) (u:V) (c:J) (b n : ℤ) :
    ScalarCycles.supportedKernel
      (leftHomMatrix Q step hstep N hN E.placement E.placement u c E.differential).transpose
      (fun x => (E.placement x.1).cochain=b ∧ Path.length x.2.2.val=n) ≃ₗ[K]
    ScalarCycles.supportedKernel
      (rightHomMatrix Q step hstep N hN orient μ A E.placement E.placement u c E.differential).transpose
      (fun x => (E.placement x.1).cochain=b ∧ Path.length x.2.2.val=n) := by
  apply ScalarCycles.transposeConjugateEquiv _ _ _ _
    (homSwitch Q step hstep N hN orient μ A E.placement u c)
    (homUnswitch Q step hstep N hN orient μ A E.placement u c)
  · rintro ⟨i,x⟩ ⟨j,y⟩ h
    by_cases hij : i=j
    · subst j
      have he := evaluationMatrix_length Q step hstep N hN orient μ A x y
        (by simpa only [homSwitch,Matrix.blockDiagonal'_apply_eq] using h)
      simp only [he]
    · exact (h (Matrix.blockDiagonal'_apply_ne _ _ _ hij)).elim
  · rintro ⟨i,x⟩ ⟨j,y⟩ h
    by_cases hij : i=j
    · subst j
      have he := inverseEvaluationMatrix_length Q step hstep N hN orient μ A x y
        (by simpa only [homUnswitch,Matrix.blockDiagonal'_apply_eq] using h)
      simp only [he]
    · exact (h (Matrix.blockDiagonal'_apply_ne _ _ _ hij)).elim
  · exact homSwitch_inverse Q step hstep N hN orient μ A hμ δ hA hroot hPF _ _ _
  · exact homUnswitch_inverse Q step hstep N hN orient μ A hμ δ hA hroot hPF _ _ _
  · exact homUnswitch_naturality Q step hstep N hN orient μ A ho hμ δ hA hroot hPF _ _ _ _ _ E.entries

noncomputable def leftTopTestEquiv (E : Zigzag.BasedComplex U (K := K) T)
    (u:V) (c:J) (b:ℤ) :
    ScalarCycles.supportedKernel
      (leftHomMatrix Q step hstep N hN E.placement E.placement u c E.differential).transpose
      (fun x => (E.placement x.1).cochain=b ∧ Path.length x.2.2.val=2) ≃ₗ[K]
    ((a : {a:J // N a c}) → Zigzag.BasedComplex.topTestCycles U E (u,a) b) := by
  let e := leftSocleIndexEquiv Q step hstep N hN E.placement u c
  let P := fun x : LeftHomIndex Q step hstep N hN E.placement u c =>
    (E.placement x.1).cochain=b ∧ Path.length x.2.2.val=2
  have h := ScalarCycles.reindexEquiv
    (leftHomMatrix Q step hstep N hN E.placement E.placement u c E.differential).transpose P e
  have ht : ((leftHomMatrix Q step hstep N hN E.placement E.placement u c E.differential).transpose).submatrix e e =
      Matrix.blockDiagonal' (fun a : {a:J // N a c} =>
        (Zigzag.testMatrix U E.placement E.placement (u,a) E.differential).transpose) := by
    rw [← Matrix.transpose_submatrix,show e=leftSocleIndexEquiv Q step hstep N hN E.placement u c from rfl,
      leftSocle_differential]
    apply Matrix.ext
    rintro ⟨a,i⟩ ⟨b,j⟩
    by_cases hab : a=b
    · subst b; simp only [Matrix.transpose_apply,Matrix.blockDiagonal'_apply_eq]
    · simp only [Matrix.transpose_apply,Matrix.blockDiagonal'_apply_ne _ _ _ hab,
        Matrix.blockDiagonal'_apply_ne _ _ _ (Ne.symm hab)]
  rw [ht] at h
  exact h.trans (ScalarCycles.blockEquiv
    (fun a : {a:J // N a c} => (Zigzag.testMatrix U E.placement E.placement (u,a) E.differential).transpose)
    (fun a x => (E.placement x.1).cochain=b ∧ Path.length x.2.val=2))

local notation "C" => complex Q step hstep N hN orient μ A ho hμ δ hA hroot hPF

noncomputable def coefficientTopLabelEquiv
    (E : Zigzag.BasedComplex U (K := K) T) {l:ℤ}
    (hE : ∀ i, (E.placement i).level=l) (u:V) (c:J) (b:ℤ) :
    Zigzag.BasedComplex.coefficientTopDual U (C E) (u,c) b ≃ₗ[K]
      ((a : {a:J // N a c}) → Zigzag.BasedComplex.coefficientTopDual U E (u,a) b) := by
  let e₀ := Zigzag.BasedComplex.coefficientTopTestEquiv U (C E) (fun i => hE i.1) (u,c) b
  let e₁ := ScalarCycles.reindexEquiv
    (Zigzag.testMatrix U (C E).placement (C E).placement (u,c) (C E).differential).transpose
    (fun x => ((C E).placement x.1).cochain=b ∧ Path.length x.2.val=2)
    (rightHomEquiv Q step hstep N hN E.placement u c)
  let e₂ := (homDualSupportedCyclesEquiv Q step hstep N hN orient μ A ho hμ δ hA hroot hPF E u c b 2).symm
  let e₃ := leftTopTestEquiv Q step hstep N hN E u c b
  let e₄ := LinearEquiv.piCongrRight (fun a : {a:J // N a c} =>
    (Zigzag.BasedComplex.coefficientTopTestEquiv U E hE (u,a) b).symm)
  exact (((e₀.trans e₁).trans e₂).trans e₃).trans e₄

end HarmonicArtin.ReversibleQuiver.StringFunctor

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Functors_TermwiseSplitInjection
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.ProbeEmbedding
open Zigzag Zigzag.BasedComplex

universe u
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [DecidableEq (ProbeVertex V)] [DecidableEq (ProbeArrow V A)]
  {I J:Type u} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
local notation "R" => probeQuiver Q

noncomputable def termwiseSplitInjection {E:BasedComplex Q (K:=K) I}
    {F:BasedComplex Q (K:=K) J} (ι:TermwiseSplitInjection Q E F) :
    TermwiseSplitInjection R (complex Q E) (complex Q F) where
  inclusion:=chainMap Q ι.inclusion
  retraction:=matrix Q ι.retraction
  split:=by
    change matrix Q ι.inclusion.matrix*matrix Q ι.retraction=_
    rw [← matrix_mul,ι.split,matrix_identity]
    rfl

end HarmonicArtin.ReversibleQuiver.ProbeEmbedding

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Functors_TruncationIndexEquiv
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.StringFunctor
universe u
attribute [local instance] Classical.propDecidable
variable {V B J : Type u} {K : Type*} (Q : ReversibleQuiver V B)
  (step : B → Bool) (hstep : ∀ b, step (Q.reverse b) = step b)
  (N : J → J → Prop) (hN : ∀ ⦃first second⦄, N first second → N second first)
  [Fintype V] [Fintype B] [Fintype J]
  [DecidableEq V] [DecidableEq B] [DecidableEq J] [DecidableRel N] [Field K]
  (orient : B → Bool) (μ : J → K) (A : K)
local notation "U" => Q.stringQuiver step hstep N hN
open Zigzag.BasedComplex

variable (ho : ∀ b, orient (Q.reverse b) = !(orient b))
    (hμ : ∀ a, μ a ≠ 0) (δ : K)
    (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
    (hPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, μ b = δ * μ a)
local notation "C" => complex Q step hstep N hN orient μ A ho hμ δ hA hroot hPF

variable {T : Type u} [Fintype T] [DecidableEq T]
def truncationIndexEquiv (E : Zigzag.BasedComplex U (K := K) T) (d : ℤ) :
    Index N (fun i : lowerLevelSet U E d => E.placement i) ≃
      lowerLevelSet U (C E) d where
  toFun x := ⟨⟨x.1.val,x.2⟩,x.1.property⟩
  invFun x := ⟨⟨x.1.1,x.2⟩,x.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end HarmonicArtin.ReversibleQuiver.StringFunctor

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Functors_TwistProdGeneratorExterior
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.linearMap_pathBasis _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_base _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_left _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.ProbeEmbedding
open Zigzag Zigzag.BasedComplex

variable {V A:Type} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A]
  [DecidableEq (ProbeVertex V)] [DecidableEq (ProbeArrow V A)]
local notation "R" => probeQuiver Q
lemma twistProd_generator_exterior (hn:∀a,Q.source a≠Q.target a) (w:List V)
    (x:FiniteHomotopyClass R (K:=K)) (p:GeneratorPlacement (ProbeVertex V))
    (hw:∀a∈w,Sum.inl a≠p.color) :
    classGeneratorArray R (((w.map (fun a=>classTwistPerm R (probeQuiver_no_loops Q hn) (.inl a))).prod) x) p=
      classGeneratorArray R x p := by
  induction w generalizing x with
  | nil=>rfl
  | cons a w ih=>
    simp only [List.map_cons,List.prod_cons,Equiv.Perm.mul_apply]
    change classGeneratorArray R (classPositiveTwist R (.inl a) _) p=_
    rw [classPositiveTwist_exterior R _ _ _ (hw a (by simp))]
    exact ih x (fun b hb=>hw b (by simp [hb]))
end HarmonicArtin.ReversibleQuiver.ProbeEmbedding

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_FusionExpressionAction
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {E V:Type} {K:Type*} [Field K]
  [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m:E→ℕ) (d:V→V→FusionEdge E) (hd:∀ s t,d s t=d t s)
  (hdiag:∀ s,d s s=.units 0)
local notation "Q" => fusionQuiver m d hd

noncomputable def fusionExpressionAction : LayerExpression V →
    FiniteHomotopyClass Q (K:=K) → FiniteHomotopyClass Q (K:=K)
  | .input,x=>x
  | .word w t,x=>fusionWordPacketPerm m d hd hdiag w (fusionExpressionAction t x)
  | .low k t,x=>classLowerTruncation Q k (fusionExpressionAction t x)
  | .layer k t,x=>classLayer Q k (fusionExpressionAction t x)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_CanonicalFusionLow
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.unfoldedMatrix_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {E V:Type} {K:Type*} [Field K]
  [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m:E→ℕ) (d:V→V→FusionEdge E) (hd:∀ s t,d s t=d t s)
  (hdiag:∀ s,d s s=.units 0)
local notation "Q" => fusionQuiver m d hd
local notation "P" => fusionWordPacketPerm m d hd hdiag (K:=K)

lemma fusionWordPacketPerm_append (w z:List (V×Bool)) : P (w++z)=P w*P z := by
  induction w with
  | nil => exact (_root_.one_mul _).symm
  | cons a w ih => simp only [List.cons_append,fusionWordPacketPerm,ih,_root_.mul_assoc]

lemma fusionSignedPacketPerm_inverse (a:V×Bool) :
    fusionSignedPacketPerm m d hd hdiag (K:=K) (a.1,!a.2)=
      (fusionSignedPacketPerm m d hd hdiag a)⁻¹ := by
  cases a with | mk v b => cases b <;> rfl

lemma fusionWordPacketPerm_inverse (w:List (V×Bool)) :
    P (w.reverse.map fun a=>(a.1,!a.2))=(P w)⁻¹ := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    simp only [List.reverse_cons,List.map_append,List.map_cons,List.map_nil,
      fusionWordPacketPerm_append,fusionWordPacketPerm,_root_.mul_one,ih,
      fusionSignedPacketPerm_inverse,mul_inv_rev]

noncomputable def canonicalFusionLow (w:List V) (q:ℤ) (x:FiniteHomotopyClass Q (K:=K)) :
    FiniteHomotopyClass Q (K:=K) :=
  let p:=P (w.map fun s=>(s,true))
  p (classLowerTruncation Q (q-1) (p.symm x))

lemma canonicalFusionExpression_action (w:List V) (z:List (V×Bool)) (q:ℤ)
    (x:FiniteHomotopyClass Q (K:=K)) :
    fusionExpressionAction m d hd hdiag (canonicalFusionExpression w z q) x=
      canonicalFusionLow m d hd hdiag w q (classLayer Q q (P z x)) := by
  dsimp [canonicalFusionExpression,fusionExpressionAction,canonicalFusionLow]
  rw [fusionWordPacketPerm_inverse]
  rfl

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_PositiveLiftSimple
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ParabolicIntersections.artinExponent_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.artinMap_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.mem_relativeStabilizer _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeArtinHom_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visualFromArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visualToArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visual_smul_vertex _root_.OAI.HarmonicArtin.artinCoxeter_generator _root_.OAI.HarmonicArtin.positiveToArtin_generator _root_.OAI.HarmonicArtin.positiveToArtin_word _root_.OAI.HarmonicArtin.restrictedArtinHom_generator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type*} [Fintype S] (M:CoxeterMatrix S)
local notation "cs" => M.toCoxeterSystem

lemma positiveLift_longest_conjugate (z:M.Group) (hz:∀w,M.toCoxeterSystem.length w≤M.toCoxeterSystem.length z)
    (s t:S) (hst:z*M.toCoxeterSystem.simple s*z=M.toCoxeterSystem.simple t) :
    positiveLift M z*generator M s=generator M t*positiveLift M z := by
  have hzz:=longest_mul_self cs z hz
  have hst':M.toCoxeterSystem.simple t*z=z*M.toCoxeterSystem.simple s := by rw [← hst,mul_assoc,mul_assoc,hzz,mul_one]
  have hr:=all_descents_of_longest cs z hz s
  have hl:=all_left_descents_of_longest cs z hz t
  have hp:positiveLift M z=positiveLift M (z*M.toCoxeterSystem.simple s)*generator M s := by
    have h:=positiveLift_mul M (z*M.toCoxeterSystem.simple s) (M.toCoxeterSystem.simple s) (by
      rw [mul_assoc,M.toCoxeterSystem.simple_mul_simple_self,mul_one,M.toCoxeterSystem.length_simple]; omega)
    simpa only [mul_assoc,M.toCoxeterSystem.simple_mul_simple_self,mul_one,positiveLift_simple] using h
  have hq:positiveLift M z=generator M t*positiveLift M (M.toCoxeterSystem.simple t*z) := by
    have h:=positiveLift_mul M (M.toCoxeterSystem.simple t) (M.toCoxeterSystem.simple t*z) (by
      rw [← mul_assoc,M.toCoxeterSystem.simple_mul_simple_self,one_mul,M.toCoxeterSystem.length_simple]; omega)
    simpa only [← mul_assoc,M.toCoxeterSystem.simple_mul_simple_self,one_mul,positiveLift_simple] using h
  calc
    positiveLift M z*generator M s=(generator M t*positiveLift M (z*M.toCoxeterSystem.simple s))*generator M s := by rw [hq,hst']
    _ = generator M t*positiveLift M z := by rw [mul_assoc,← hp]

lemma positiveLift_longest_square_commute_generator (z:M.Group)
    (hz:∀w,M.toCoxeterSystem.length w≤M.toCoxeterSystem.length z) (s:S) :
    Commute (positiveLift M z^2) (generator M s) := by
  obtain ⟨t,hst⟩:=longest_conjugates_simple cs z hz s
  have hts:z*M.toCoxeterSystem.simple t*z=M.toCoxeterSystem.simple s := by
    rw [← hst]
    have hzz:=longest_mul_self cs z hz
    calc z*(z*M.toCoxeterSystem.simple s*z)*z = (z*z)*M.toCoxeterSystem.simple s*(z*z) := by group
         _ = M.toCoxeterSystem.simple s := by rw [hzz,one_mul,mul_one]
  have h₁:=positiveLift_longest_conjugate M z hz s t hst
  have h₂:=positiveLift_longest_conjugate M z hz t s hts
  show positiveLift M z^2 * generator M s=generator M s*positiveLift M z^2
  rw [pow_two,mul_assoc,h₁,← mul_assoc,h₂,mul_assoc]

lemma positiveLift_longest_square_central (z:M.Group)
    (hz:∀w,M.toCoxeterSystem.length w≤M.toCoxeterSystem.length z) (g:Artin M) :
    Commute (positiveLift M z^2) g := by
  have hg:g∈Subgroup.closure (Set.range (generator M)) := by
    have hh : Subgroup.closure (Set.range (generator M))=⊤ := PresentedGroup.closure_range_of (braidRelators M)
    rw [hh]; trivial
  induction hg using Subgroup.closure_induction with
  | mem x hx => obtain ⟨s,rfl⟩:=hx; exact positiveLift_longest_square_commute_generator M z hz s
  | one => exact Commute.one_right _
  | mul a b ha hb ia ib => exact ia.mul_right ib
  | inv a ha ia => exact ia.inv_right

lemma positiveLift_longest_square_complement (z:M.Group)
    (hz:∀w,M.toCoxeterSystem.length w≤M.toCoxeterSystem.length z) (s:S) :
    ∃ u:List S,generator M s*wordArtin M u=positiveLift M z^2 := by
  let c:=M.toCoxeterSystem.simple s*z
  have hlen:=all_left_descents_of_longest cs z hz s
  have hp:positiveLift M z=generator M s*positiveLift M c := by
    have h:=positiveLift_mul M (M.toCoxeterSystem.simple s) c (by
      simp only [c]; rw [← mul_assoc,M.toCoxeterSystem.simple_mul_simple_self,one_mul,M.toCoxeterSystem.length_simple]; omega)
    simpa only [c,← mul_assoc,M.toCoxeterSystem.simple_mul_simple_self,one_mul,positiveLift_simple] using h
  refine ⟨reducedExpression M c++reducedExpression M z,?_⟩
  rw [wordArtin_append,pow_two,← mul_assoc]
  change (generator M s*positiveLift M c)*positiveLift M z=_
  rw [← hp]

lemma positive_fraction_longest (z:M.Group) (hz:∀w,M.toCoxeterSystem.length w≤M.toCoxeterSystem.length z)
    (g:Artin M) : ∃ n:ℕ,∃ u:List S,g=wordArtin M u*(positiveLift M z^2)^(- (n:ℤ)) := by
  let Ω:Artin M:=positiveLift M z^2
  have hg:g∈Subgroup.closure (Set.range (generator M)) := by
    have hh:Subgroup.closure (Set.range (generator M))=⊤:=PresentedGroup.closure_range_of (braidRelators M)
    rw [hh]; trivial
  change ∃ n:ℕ,∃ u:List S,g=wordArtin M u*Ω^(- (n:ℤ))
  induction hg using Subgroup.closure_induction_left with
  | one => exact ⟨0,[],by simp [wordArtin]⟩
  | mul_left a ha y hy ih =>
    obtain ⟨s,rfl⟩:=ha
    obtain ⟨n,u,rfl⟩:=ih
    exact ⟨n,s::u,by simp only [wordArtin,List.map_cons,List.prod_cons,mul_assoc]⟩
  | inv_mul_cancel a ha y hy ih =>
    obtain ⟨s,rfl⟩:=ha
    obtain ⟨n,u,rfl⟩:=ih
    obtain ⟨v,hv⟩:=positiveLift_longest_square_complement M z hz s
    have hinv:(generator M s)⁻¹=wordArtin M v*Ω⁻¹ := by
      apply (mul_left_cancel_iff (a:=generator M s)).mp
      rw [← mul_assoc,hv,mul_inv_cancel, mul_inv_cancel]
    refine ⟨n+1,v++u,?_⟩
    rw [hinv,wordArtin_append]
    have hp:Commute Ω⁻¹ (wordArtin M u):=(positiveLift_longest_square_central M z hz _).inv_left
    calc
      wordArtin M v*Ω⁻¹*(wordArtin M u*Ω^(-(n:ℤ))) =
          wordArtin M v*(Ω⁻¹*wordArtin M u)*Ω^(-(n:ℤ)) := by group
      _ = (wordArtin M v*wordArtin M u)*(Ω⁻¹*Ω^(-(n:ℤ))) := by rw [hp.eq]; group
      _ = (wordArtin M v*wordArtin M u)*Ω^(-((n+1:ℕ):ℤ)) := by
        congr 1
        rw [← zpow_neg_one,← zpow_add]
        congr 1
        omega

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_FiniteArtinPositiveLeft
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type*} [Fintype S] (M:CoxeterMatrix S)

theorem finiteArtin_positive_left_fraction [Finite M.Group] (g:Artin M) :
    ∃ u v:List S,g=(wordArtin M u)⁻¹*wordArtin M v := by
  obtain ⟨z,hz⟩:=exists_longest M.toCoxeterSystem
  obtain ⟨n,u,hu⟩:=positive_fraction_longest M z hz g
  obtain ⟨v,hv⟩:=positiveLift_longest_square_positive M z
  obtain ⟨v',hv'⟩:=wordArtin_positive_power M v n
  refine ⟨v',u,?_⟩
  rw [hu,hv',hv,zpow_neg,zpow_natCast]
  exact ((positiveLift_longest_square_central M z hz (wordArtin M u)).pow_left n).inv_left.eq.symm

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_FusionExpressionOrbit
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {E V:Type} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m:E→ℕ) (d:V→V→FusionEdge E) (hd:∀ s t,d s t=d t s)
  (hdiag:∀ s,d s s=.units 0)
local notation "Q" => fusionQuiver m d hd
local notation "P" => fusionExpressionAction m d hd hdiag (K:=ℂ)

noncomputable def fusionExpressionOrbit (t:LayerExpression V) (s:V) (L:FusionLabel m) :
    FiniteHomotopyClass Q (K:=ℂ) := P t (initialClass Q (s,L))

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_FusionQuiverSimpleEdge
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.instDecidableRelStringLabelStringAdjacent
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.labelSplit_apply _root_.OAI.HarmonicArtin.labelSplit_symm_at _root_.OAI.HarmonicArtin.labelSplit_symm_rest _root_.OAI.HarmonicArtin.unfoldedMatrix_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin

variable {E V : Type*} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m : E → ℕ) (d : V → V → FusionEdge E) (hd : ∀ s t, d s t = d t s)

omit [Fintype V] in
lemma fusionOrdinaryPresentation :
    ReversibleQuiver.Zigzag.BasedComplex.UnfoldedPresentation (fusionQuiver m d hd)
      (fusionOrdinaryMatrix m d hd) := by
  constructor
  intro α β
  by_cases hne : α=β
  · exact Or.inl hne
  by_cases h0 : (d α.1 β.1).multiplicity m α.2 β.2 = 0
  · exact Or.inr (Or.inr (Or.inl ⟨by simp [fusionOrdinaryMatrix, hne,h0],
      fusionQuiver_orthogonal m d hd α β hne h0⟩))
  by_cases h1 : (d α.1 β.1).multiplicity m α.2 β.2 = 1
  · exact Or.inr (Or.inr (Or.inr ⟨by simp [fusionOrdinaryMatrix, hne,h1],
      ⟨fusionQuiver_simpleEdge m d hd α β hne h1⟩⟩))
  exact Or.inr (Or.inl (by simp [fusionOrdinaryMatrix, hne,h0,h1]))

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_FusionZeroLabel
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {E V:Type} {K:Type*} [Field K]
  [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m:E→ℕ) (d:V→V→FusionEdge E) (hd:∀ s t,d s t=d t s)
  (hm:∀ e,2 ≤ m e)
local notation "Q" => fusionQuiver m d hd

lemma fusionFamilyMultiplicity_nonneg (x:FusionLabel m→FiniteHomotopyClass Q (K:=K))
    (q:ℤ) (v:V) : 0≤fusionFamilyMultiplicity m d hd hm x q v := by
  apply div_nonneg _ (fusionWeight_pos m hm _).le
  exact Finset.sum_nonneg (fun L _=>mul_nonneg (fusionWeight_pos m hm L).le
    (generatorVector_nonneg Q _ _))

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_AcyclicTwistInput
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The published acyclic-evaluation input

Seidel--Thomas, *Braid group actions on derived categories of coherent
sheaves*, Duke Math. J. 108 (2001), Definition 2.5 (equation (2.2)),
and the first sentence of the proof of Proposition 2.12:
https://arxiv.org/pdf/math/0001043, pp. 13 and 17.
A twist is the cone of evaluation. If the entire evaluated Hom complex
is acyclic, this cone is isomorphic to the original object. For bounded
projective complexes the resulting isomorphism is a homotopy equivalence.
Below is precisely this standard consequence in the existing vertex-test
notation. It is independent of the Artin stabilizer argument.
-/
namespace HarmonicArtin.ParabolicIntersections
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
attribute [local instance] Classical.decEq Classical.propDecidable

structure PublishedAcyclicTwist {V A : Type} (Q : ReversibleQuiver V A)
    [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A] : Prop where
  fix_of_exact : ∀ (x : FiniteHomotopyClass Q (K := ℂ)) (α : V),
    (∀ l c, ClassTestExact Q α l c x) → classPositiveTwist Q α x=x

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Realizations_FusionWeightedHom
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable
variable {E V:Type} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m:E → ℕ) (d:V → V → FusionEdge E) (hd:∀ s t,d s t=d t s)
  (hdiag:∀ s,d s s=.units 0)
local notation "Q" => fusionQuiver m d hd

noncomputable def fusionWeightedHom {T R:FusionLabel m → Type*}
    [∀ L,Fintype (T L)] [∀ H,Fintype (R H)]
    (P:∀ L,BasedComplex Q (K:=ℂ) (T L)) (F:∀ H,BasedComplex Q (K:=ℂ) (R H)) (t:ℤ) : ℝ :=
  ∑ L,∑ H,fusionWeight m L*fusionWeight m H*(totalHomDimension Q (P L) (F H) t:ℝ)

end HarmonicArtin

end OAI
end


