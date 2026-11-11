-- Prove2me | Definitions.Def_OAIQ225Ag010
-- name    : OAIQ225Ag010
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T17:28:50.051741+00:00
-- url     : https://prove2.me/theorems/c043921f-0871-43f1-abaf-703c6c98f8b9
-- title:
--   Definitions bundle OAIQ225Ag010 of the split of OpenAI, Harmonic heights and the Artin K(pi,1) conjecture
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.HarmonicArtin.salvetti_cover_contractible`, carved from OpenAI's openai/math development (OpenAI, *Harmonic heights and the Artin K(pi,1) conjecture*, OpenAI Math Release, September 23, 2026, result family 254, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 253 declarations of OpenAI's Lean: 78 definitions, 2 instances and 173 theorems. The definitions and types are `OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.coefficientTopLabelEquiv`, `OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.homDualSupportedCyclesEquiv`, `OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.leftSocleIndexEquiv`, `OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.leftTopTestEquiv`, `OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.truncationIndexEquiv`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.ChainIsomorphism.termwiseSplit`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.HomMonoFrom`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.TermwiseSplitInjection.trans`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.adjacentTestFirstPivot`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.adjacentTestIndexEquiv`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.adjacentTestReduction`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.adjacentTestSecondPivot`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeIndexEquiv`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeIndexMap`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudePivot`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.arrowCornerEquiv`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.classLayerTopDimension`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.classLayerTotalHomDimension`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.classSignedVector`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.coefficientTopSumEquiv`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.finiteSumTopTestEquiv`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.highConeNormalized`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.highConePivot`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.highConeReduction`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.highProjection`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.highPureIndex`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.highRestriction`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homCoordinates`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homCoordinatesEquiv`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homCycleKernelEquiv`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homDetector`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homPathBasis`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpaceDuality`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homStep`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.initialCoordinate`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.lowConeNormalized`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.lowConePivot`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.lowConeReduction`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.lowInclusion` and 38 more.
--
--   **Sources.** They come from these modules of lean/OAI/Topology, in whole or in part: `ArtinGroups_Complexes_ActedIndex`, `ArtinGroups_Complexes_ArrowShift`, `ArtinGroups_Complexes_Capped`, `ArtinGroups_Complexes_CoefficientTopDual`, `ArtinGroups_Complexes_CornerPath`, `ArtinGroups_Complexes_DiagonalVertex`, `ArtinGroups_Complexes_DifferentialMulExtendLayer`, `ArtinGroups_Complexes_DownClosed`, `ArtinGroups_Complexes_EmptyTestIndex`, `ArtinGroups_Complexes_EqualColorPair`, `ArtinGroups_Complexes_ExtendLayer`, `ArtinGroups_Complexes_FiniteFamilyLevelSupport`, `ArtinGroups_Complexes_GeneratorTokenTest`, `ArtinGroups_Complexes_GeneratorVector`, `ArtinGroups_Complexes_HighConeIndex`, `ArtinGroups_Complexes_HighConeRetainedPure`, `ArtinGroups_Complexes_HomDetector`, `ArtinGroups_Complexes_HomDimensionZeroCycles`, `ArtinGroups_Complexes_HomDimensionZeroHom`, `ArtinGroups_Complexes_HomInternalSupport`, `ArtinGroups_Complexes_HomMono`, `ArtinGroups_Complexes_HomPath`, `ArtinGroups_Complexes_HomSpace`, `ArtinGroups_Complexes_HomSpaceDuality`, `ArtinGroups_Complexes_HomSpacePairing`, `ArtinGroups_Complexes_HomStep`, `ArtinGroups_Complexes_InitialProbeTestUpper`, `ArtinGroups_Complexes_InitialProjective`, `ArtinGroups_Complexes_InverseMatrix`, `ArtinGroups_Complexes_InverseWordAction`, `ArtinGroups_Complexes_IsolatedIndexCycle`, `ArtinGroups_Complexes_LayerTotalHomDimension`, `ArtinGroups_Complexes_LeftMatrix`, `ArtinGroups_Complexes_LevelArrayMinimalApply`, `ArtinGroups_Complexes_MatrixOneMulExtend`, `ArtinGroups_Complexes_MinimalModel`, `ArtinGroups_Complexes_MinimalModelEquivalence`, `ArtinGroups_Complexes_NegativeConeIndex`, `ArtinGroups_Complexes_OutsideCap`, `ArtinGroups_Complexes_PacketPermExterior`, `ArtinGroups_Complexes_PlacedProjective`, `ArtinGroups_Complexes_PlacementSignedWeight`, `ArtinGroups_Complexes_PositiveConeIndex`, `ArtinGroups_Complexes_PositiveTwistModern`, `ArtinGroups_Complexes_PositiveWord`, `ArtinGroups_Complexes_PositiveWordActionTest`, `ArtinGroups_Complexes_ProbeFixedNoDiagonal`, `ArtinGroups_Complexes_PureCoefficientCohomology`, `ArtinGroups_Complexes_PureHomSpaceHomogeneous`, `ArtinGroups_Complexes_PureLayerSelf`, `ArtinGroups_Complexes_ReducedNoTopDivisor`, `ArtinGroups_Complexes_RestrictExtendLayerMul`, `ArtinGroups_Complexes_RestrictLayer`, `ArtinGroups_Complexes_ScalarKernel`, `ArtinGroups_Complexes_ScalarSupportedCochainShift`, `ArtinGroups_Complexes_ScalarSupportedTokenShift`, `ArtinGroups_Complexes_SecondaryLayer`, `ArtinGroups_Complexes_Shift`, `ArtinGroups_Complexes_SumTestEquiv`, `ArtinGroups_Complexes_SummandSecondary`, `ArtinGroups_Complexes_TargetLow`, `ArtinGroups_Complexes_TermwiseSplitInjection`, `ArtinGroups_Complexes_TestExact`, `ArtinGroups_Complexes_TestUpperBound`, `ArtinGroups_Complexes_TokenShift`, `ArtinGroups_Complexes_TotalVector`, `ArtinGroups_Complexes_WordInverseModel`, `ArtinGroups_Coxeter_OrdinaryCoxeterMatrix`, `ArtinGroups_Coxeter_PositiveBraidRel`, `ArtinGroups_Functors_HomDualSupportedCycles`, `ArtinGroups_Functors_LeftSocleIndexEquiv`, `ArtinGroups_Functors_TruncationIndexEquiv`, `ArtinGroups_Harmonic_CanonicalFusionLow`, `ArtinGroups_Harmonic_CosetBelow`, `ArtinGroups_Harmonic_FusionQuiverSimpleEdge`, `ArtinGroups_Harmonic_InitialProbe`, `ArtinGroups_Harmonic_Level`, `ArtinGroups_Harmonic_PositiveDescentSet`, `ArtinGroups_Harmonic_PositiveEarlierLinkUpper`, `ArtinGroups_Harmonic_PositiveHead`, `ArtinGroups_Harmonic_PositiveUpperBoundaryRestriction`, `ArtinGroups_Harmonic_ProbeCoreInclusion`, `ArtinGroups_Harmonic_ProbePacket`, `ArtinGroups_Harmonic_ProbePacketExterior`, `ArtinGroups_Harmonic_RestrictionHomRange`, `ArtinGroups_Harmonic_SphericalTypeReindex`, `ArtinGroups_Harmonic_UnfoldedInclusion`, `ArtinGroups_Quivers_ClosedNeighborhood`, `ArtinGroups_Quivers_CoefficientMatrix`, `ArtinGroups_Quivers_PathTwo`, `ArtinGroups_Quivers_PathTwoSelf`, `ArtinGroups_Quivers_ProbeLeaf`, `ArtinGroups_Quivers_ProbeSimpleEdge`, `ArtinGroups_Quivers_ProbeVertex`, `ArtinGroups_Quivers_VertexLinear`, `ArtinGroups_Realizations_FusionWeightedHom`, `ArtinGroups_Realizations_NoncriticalPositiveCell`, `ArtinGroups_Realizations_PositiveCellPoset2`, `ArtinGroups_Realizations_PositiveFullCell`.
--
--   **Imports.** It imports the published bundle `Def_HarmonicArtin`; the bundles `OAIQ225Ag005`, `OAIQ225Ag006`, `OAIQ225Ag007` and `OAIQ225Ag008` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ225Ag011` and `OAIQ225Ag012`; the statement `OAI.HarmonicArtin.IsolatedIterationData.separation`.
-- source:
--   OpenAI, Harmonic heights and the Artin K(pi,1) conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 254; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Harmonic-heights-and-the-Artin-K-pi-1-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Topology at commit adc7f12

import Mathlib
import Definitions.Def_HarmonicArtin
import Definitions.Def_OAIQ225Ag005
import Definitions.Def_OAIQ225Ag006
import Definitions.Def_OAIQ225Ag007
import Definitions.Def_OAIQ225Ag008

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_Level
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.instAlgebra
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_ActedIndex
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

noncomputable instance amplitudeCoreFintype (E : BasedComplex Q (K := K) I) (α : V) :
    Fintype (AmplitudeCoreIndex Q E α) := by
  classical
  unfold AmplitudeCoreIndex
  infer_instance

def unitTest (E : BasedComplex Q (K := K) I) (α : V) (i : ActedIndex Q E α) :
    TestIndex Q E.placement α :=
  ⟨i.val, ⟨.inl α, rfl, i.property.symm⟩⟩

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

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_TokenShift
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_ArrowShift
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_HomSpace
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.instPreorderLiftedCell _root_.OAI.HarmonicArtin.liftedPartialOrder
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_DiagonalVertex
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
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

variable [DecidableEq I]

omit [Fintype V] in
lemma identity_mem_homCycles (E : BasedComplex Q (K := K) I) :
    projectiveIdentity Q E.placement ∈ homCycles Q E E 0 0 := by
  exact map_mem_homCycles Q (HomotopyEquivalence.refl Q E).forward

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_HomDetector
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
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

noncomputable def homDetector (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (n v : ℤ)
    (L : Matrix I J (Q.Zigzag K) →ₗ[K] K)
    (hL : ∀ f ∈ homBoundaries Q E F n v, L f = 0) :
    homCohomology Q E F n v →ₗ[K] K :=
  Submodule.liftQ _ (L.comp (homCycles Q E F n v).subtype) (by
    intro f hf
    exact hL f hf)

lemma boundary_of_homDimension_le_one (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (n v : ℤ)
    (hd : homDimension Q E F n v ≤ 1)
    (L : Matrix I J (Q.Zigzag K) →ₗ[K] K)
    (hL : ∀ f ∈ homBoundaries Q E F n v, L f = 0)
    {u : Matrix I J (Q.Zigzag K)} (hu : u ∈ homCycles Q E F n v) (huL : L u ≠ 0)
    {f : Matrix I J (Q.Zigzag K)} (hf : f ∈ homCycles Q E F n v) (hfL : L f = 0) :
    f ∈ homBoundaries Q E F n v := by
  let T := homDetector Q E F n v L hL
  have hin := injective_of_finrank_le_one hd T
    (Submodule.Quotient.mk (⟨u, hu⟩ : homCycles Q E F n v)) huL
  have hz : (Submodule.Quotient.mk (⟨f, hf⟩ : homCycles Q E F n v) :
      homCohomology Q E F n v) = 0 := by
    apply hin
    change L f = T 0
    rw [map_zero]
    exact hfL
  exact (Submodule.Quotient.mk_eq_zero
    ((homBoundaries Q E F n v).comap (homCycles Q E F n v).subtype)).mp hz

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_ExtendLayer
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
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

lemma extendLayer_linear (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (l k : ℤ)
    {f : Matrix {i // (E.placement i).level = l} {j // (F.placement j).level = k} (Q.Zigzag K)}
    (hf : LinearMatrix Q f) : LinearMatrix Q (extendLayer Q E F l k f) := by
  intro i j
  simp only [extendLayer_entry]
  split_ifs with hi hj
  · exact hf ⟨i, hi⟩ ⟨j, hj⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_RestrictLayer
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Quivers_CoefficientMatrix
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype A] [DecidableEq V]
variable {I J : Type*} [Fintype I] [Fintype J]

omit [Fintype I] [Fintype J] in
lemma matrixZero_linear {f : Matrix I J (Q.Zigzag K)} (hf : LinearMatrix Q f) :
    matrixZero Q f = 0 := matrixZero_eq_zero Q fun i j => (hf i j).1

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
-- module Solutions.OAIQ225_AG.ArtinGroups_Quivers_PathTwo
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Quivers_PathTwoSelf
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype A] [DecidableEq V]

variable {I J L : Type*}

lemma matrixTwo_mul_linear_left [Fintype J]
    {f : Matrix I J (Q.Zigzag K)} (hf : LinearMatrix Q f)
    (g : Matrix J L (Q.Zigzag K)) :
    matrixTwo Q (f * g) = f * matrixOne Q g := by
  apply Matrix.ext
  intro i k
  change pathTwo Q (∑ j, f i j * g j k) = ∑ j, f i j * pathOne Q (g j k)
  rw [map_sum]
  exact Finset.sum_congr rfl fun j _ => pathTwo_mul_linear_left Q (hf i j).1 (hf i j).2 _

lemma matrixTwo_mul_linear_right [Fintype J]
    (f : Matrix I J (Q.Zigzag K)) {g : Matrix J L (Q.Zigzag K)} (hg : LinearMatrix Q g) :
    matrixTwo Q (f * g) = matrixOne Q f * g := by
  apply Matrix.ext
  intro i k
  change pathTwo Q (∑ j, f i j * g j k) = ∑ j, pathOne Q (f i j) * g j k
  rw [map_sum]
  exact Finset.sum_congr rfl fun j _ => pathTwo_mul_linear_right Q _ (hg j k).1 (hg j k).2

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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_Capped
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype A] [DecidableEq V]
variable {I J : Type*}

namespace BasedComplex
variable [Fintype I] [Fintype J]

lemma capped_incoming_token (E : BasedComplex Q (K := K) I) (U : Set V) (q : ℤ)
    (hcap : E.CappedOn Q U q) (j : I) (hj : (E.placement j).level = q)
    (hU : (E.placement j).color ∈ U) (i : I) :
    pathTwo Q (E.differential i j) = 0 := by
  apply pathTwo_eq_zero Q
  ext w
  by_contra hw
  obtain ⟨hi, hjc, hc, hu⟩ := degree_token_support Q E.entries E.degree i j w hw
  have h : (E.placement i).color ∈ U := by simpa only [hi, hjc] using hU
  have hb := hcap i h
  dsimp only [GeneratorPlacement.level] at hb hj
  omega

lemma capped_matrixTwo_mul_extend (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (U : Set V) (q d : ℤ)
    (hcap : E.CappedOn Q U q)
    {f : Matrix {i // (E.placement i).level = q} {j // (F.placement j).level = d} (Q.Zigzag K)}
    (hs : ∀ i j, (E.placement i.val).color ∉ U → f i j = 0) :
    matrixTwo Q E.differential * extendLayer Q E F q d f = 0 := by
  classical
  apply Matrix.ext
  intro i j
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro t _
  rw [extendLayer_entry]
  split_ifs with ht hj
  · by_cases hU : (E.placement t).color ∈ U
    · change pathTwo Q (E.differential i t) * f ⟨t, ht⟩ ⟨j, hj⟩ = 0
      rw [capped_incoming_token Q E U q hcap t ht hU i, MulZeroClass.zero_mul]
    · rw [hs ⟨t, ht⟩ ⟨j, hj⟩ hU, MulZeroClass.mul_zero]
  · exact MulZeroClass.mul_zero _
  · exact MulZeroClass.mul_zero _

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_HomSpacePairing
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_HomSpaceDuality
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.instPreorderLiftedCell _root_.OAI.HarmonicArtin.liftedPartialOrder
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_HomStep
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_HomInternalSupport
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Quivers_VertexLinear
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_PureHomSpaceHomogeneous
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.instPreorderLiftedCell _root_.OAI.HarmonicArtin.liftedPartialOrder
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_LeftMatrix
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_DifferentialMulExtendLayer
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_MatrixOneMulExtend
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_SecondaryLayer
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
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

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_RestrictExtendLayerMul
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_SummandSecondary
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
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

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_PureCoefficientCohomology
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
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

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_CoefficientTopDual
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
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

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_HomPath
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.instPreorderLiftedCell _root_.OAI.HarmonicArtin.liftedPartialOrder
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_CornerPath
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def purePathForget (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) {l k : ℤ}
    (hE : ∀ i, (E.placement i).level = l) (hF : ∀ j, (F.placement j).level = k) (r : ℤ) :
    (Σ v : {v // v ∈ homInternalSupport Q E F}, HomPath Q E F (k-l+r-v.val) v.val) →
      CornerPath Q E F r := fun x => ⟨x.2.val, x.2.property.1, x.2.property.2.1, by
        have hh := x.2.property.2.2
        have he := hE x.2.val.1
        have hf := hF x.2.val.2.1
        dsimp only [GeneratorPlacement.level] at he hf
        omega⟩

omit [Fintype V] [DecidableEq A] in
lemma purePathForget_injective (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) {l k : ℤ}
    (hE : ∀ i, (E.placement i).level = l) (hF : ∀ j, (F.placement j).level = k) (r : ℤ) :
    Function.Injective (purePathForget Q E F hE hF r) := by
  rintro ⟨⟨a,ha⟩,⟨ta,hta⟩⟩ ⟨⟨b,hb⟩,⟨tb,htb⟩⟩ hh
  have ht : ta=tb := congrArg Subtype.val hh
  subst tb
  have hab : a=b := by
    have h₁ := hta.2.2.2
    have h₂ := htb.2.2.2
    dsimp only at h₁ h₂
    omega
  subst b
  rfl

omit [Fintype V] [DecidableEq A] in
lemma purePathForget_surjective (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) {l k : ℤ}
    (hE : ∀ i, (E.placement i).level = l) (hF : ∀ j, (F.placement j).level = k) (r : ℤ) :
    Function.Surjective (purePathForget Q E F hE hF r) := by
  rintro ⟨⟨i,j,p⟩,hpt⟩
  let v := (F.placement j).internal - (E.placement i).internal + Path.length p
  have hv : v ∈ homInternalSupport Q E F := by
    rw [mem_homInternalSupport]
    rcases p with p | p | p
    · exact ⟨i,j,0,rfl⟩
    · exact ⟨i,j,1,rfl⟩
    · exact ⟨i,j,2,rfl⟩
  refine ⟨⟨⟨v,hv⟩, ⟨(i,j,p),hpt.1,hpt.2.1,?_,?check⟩⟩, rfl⟩
  · have he := hE i
    have hf := hF j
    have hp := hpt.2.2
    dsimp only [GeneratorPlacement.level] at he hf
    dsimp only at hp ⊢
    dsimp only [v]
    omega
  case check =>
    dsimp only [v]
    omega

noncomputable def purePathEquiv (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) {l k : ℤ}
    (hE : ∀ i, (E.placement i).level = l) (hF : ∀ j, (F.placement j).level = k) (r : ℤ) :
    (Σ v : {v // v ∈ homInternalSupport Q E F}, HomPath Q E F (k-l+r-v.val) v.val) ≃
      CornerPath Q E F r := Equiv.ofBijective (purePathForget Q E F hE hF r)
        ⟨purePathForget_injective Q E F hE hF r, purePathForget_surjective Q E F hE hF r⟩

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_DownClosed
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
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
lemma DownClosed.high_condition {E:BasedComplex Q (K:=K) I} {T:Set I}
    (h:DownClosed Q E T) : ∀ i∈Tᶜ,∀ j∈Tᶜ,∀ k∉Tᶜ,E.differential i k*E.differential k j=0 := by
  intro i _ j hj k hk
  have hk':k∈T:=Classical.not_not.mp hk
  have hz:E.differential k j=0 := Classical.not_not.mp (fun hn=>hj (h k hk' j hn))
  rw [hz,MulZeroClass.mul_zero]

noncomputable def highRestriction (E:BasedComplex Q (K:=K) I) (T:Set I) (h:DownClosed Q E T) :
    BasedComplex Q (K:=K) (Tᶜ:Set I) := E.restrict Q Tᶜ h.high_condition

omit [Fintype V] [DecidableEq A] in
lemma lowInclusion_commute (E:BasedComplex Q (K:=K) I) (T:Set I) (h:DownClosed Q E T) :
    (lowRestriction Q E T h).differential*blockInclusion Q E T=
      blockInclusion Q E T*E.differential := by
  rw [blockInclusion_mul Q E T _ _ E.entries]
  apply Matrix.ext
  intro i j
  change (∑ k:T,E.differential i k*(if (k:I)=j then vertexId Q (K:=K) (E.placement k).color else 0))=E.differential i j
  by_cases hj:j∈T
  · let j':T:=⟨j,hj⟩
    have he (k:T) : ((k:I)=j) ↔ k=j' := by simp only [j',Subtype.ext_iff]
    simp only [he,mul_ite,MulZeroClass.mul_zero,Fintype.sum_ite_eq']
    exact E.entries.2 i j
  · have hz:E.differential i j=0 := Classical.not_not.mp (fun hh=>hj (h i i.property j hh))
    rw [hz]
    apply Finset.sum_eq_zero
    intro k _
    have hne:(k:I)≠j := by intro he; exact hj (he ▸ k.property)
    rw [ite_eq_right hne,MulZeroClass.mul_zero]

omit [Fintype V] [DecidableEq A] in
lemma highProjection_commute (E:BasedComplex Q (K:=K) I) (T:Set I) (h:DownClosed Q E T) :
    E.differential*blockProjection Q E Tᶜ=
      blockProjection Q E Tᶜ*(highRestriction Q E T h).differential := by
  rw [mul_blockProjection Q E Tᶜ _ _ E.entries]
  apply Matrix.ext
  intro i j
  change E.differential i j=(∑ k:(Tᶜ:Set I),(if i=(k:I) then vertexId Q (K:=K) (E.placement i).color else 0)*E.differential k j)
  by_cases hi:i∈Tᶜ
  · let i':(Tᶜ:Set I):=⟨i,hi⟩
    have he (k:(Tᶜ:Set I)) : (i=(k:I)) ↔ i'=k := by simp only [i',Subtype.ext_iff]
    simp only [he,ite_mul,zero_mul,Fintype.sum_ite_eq]
    exact (E.entries.1 i j).symm
  · have hi':i∈T:=Classical.not_not.mp hi
    have hz:E.differential i j=0 := Classical.not_not.mp (fun hh=>j.property (h i hi' j hh))
    rw [hz]
    symm
    apply Finset.sum_eq_zero
    intro k _
    have hne:i≠(k:I) := by intro he; exact hi (he.symm ▸ k.property)
    rw [ite_eq_right hne,zero_mul]

noncomputable def lowInclusion (E:BasedComplex Q (K:=K) I) (T:Set I) (h:DownClosed Q E T) :
    Map Q (lowRestriction Q E T h) E where
  matrix:=blockInclusion Q E T
  entries:=blockInclusion_entries Q E T
  degree:=fun i j=>mapDegree_identity Q (i:I) j
  commute:=lowInclusion_commute Q E T h

noncomputable def highProjection (E:BasedComplex Q (K:=K) I) (T:Set I) (h:DownClosed Q E T) :
    Map Q E (highRestriction Q E T h) where
  matrix:=blockProjection Q E Tᶜ
  entries:=blockProjection_entries Q E Tᶜ
  degree:=fun i j=>mapDegree_identity Q i (j:I)
  commute:=highProjection_commute Q E T h

noncomputable def lowConeNormalized (E:BasedComplex Q (K:=K) I) (T:Set I) (h:DownClosed Q E T) :=
  ((lowInclusion Q E T h).cone Q).reindex Q (Equiv.sumCongr (Equiv.refl T) (Equiv.Set.sumCompl T))

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
lemma lowCone_source_retained (E:BasedComplex Q (K:=K) I) (T:Set I) (h:DownClosed Q E T)
    (i:T) (j:(Tᶜ:Set I)) : (lowConeNormalized Q E T h).differential (.inl i) (.inr (.inr j))=0 := by
  change (if (i:I)=(j:I) then vertexId Q (K:=K) (E.placement i).color else 0)=0
  have hn:(i:I)≠(j:I):=fun he=>j.property (he ▸ i.property)
  rw [ite_eq_right hn]

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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_InitialProjective
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.instPreorderLiftedCell _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

omit [DecidableEq A] in
lemma homDimension_le_homSpace {I J : Type*} [Fintype I] [Fintype J]
    (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J) (n v : ℤ) :
    homDimension Q E F n v ≤ Module.finrank K (homSpace Q E F n v) := by
  apply le_trans (Submodule.finrank_quotient_le _)
  exact Submodule.finrank_mono inf_le_left

lemma initial_self_entry_decomposition (hn : ∀ a, Q.source a ≠ Q.target a)
    (α : V) (n v : ℤ)
    {f : Matrix PUnit PUnit (Q.Zigzag K)}
    (hf : f ∈ homSpace Q (initialProjective Q α) (initialProjective Q α) n v)
    (i j : PUnit) :
    f i j = (f i j).vertex α • vertexId Q α + (f i j).token α • tokenBasis Q α :=
  diagonal_corner_decomposition Q hn α (f i j) (hf.1.1 i j) (hf.1.2 i j)

omit [Fintype V] [DecidableEq A] in
lemma initial_self_entry_homogeneous (α : V) (n v : ℤ)
    {f : Matrix PUnit PUnit (Q.Zigzag K)}
    (hf : f ∈ homSpace Q (initialProjective Q α) (initialProjective Q α) n v)
    (i j : PUnit) : Homogeneous Q v (f i j) := by
  simpa only [initialProjective, add_zero, sub_zero] using (hf.2 i j).2

noncomputable def initialCoordinate (α : V) (n v : ℤ) :
    homSpace Q (initialProjective Q (K := K) α) (initialProjective Q α) n v →ₗ[K] K where
  toFun f := if v = 0 then (f.val PUnit.unit PUnit.unit).vertex α
    else (f.val PUnit.unit PUnit.unit).token α
  map_add' f g := by split_ifs <;> rfl
  map_smul' r f := by split_ifs <;> rfl

lemma initialCoordinate_injective (hn : ∀ a, Q.source a ≠ Q.target a)
    (α : V) (n v : ℤ) : Function.Injective (initialCoordinate Q (K := K) α n v) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro f hf
  change (initialCoordinate Q α n v) f = 0 at hf
  change f = 0
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  have hi : i = PUnit.unit := Subsingleton.elim _ _
  have hj : j = PUnit.unit := Subsingleton.elim _ _
  subst i
  subst j
  rw [initial_self_entry_decomposition Q hn α n v f.property PUnit.unit PUnit.unit]
  have hh := initial_self_entry_homogeneous Q α n v f.property PUnit.unit PUnit.unit
  by_cases hv : v = 0
  · have hzero : (f.val PUnit.unit PUnit.unit).vertex α = 0 := by
      simpa only [initialCoordinate, LinearMap.coe_mk, AddHom.coe_mk, ite_eq_left hv] using hf
    rw [hzero, hh.2.2 (by omega)]
    simp only [Pi.zero_apply, zero_smul, add_zero]
    rfl
  · have hzero : (f.val PUnit.unit PUnit.unit).token α = 0 := by
      simpa only [initialCoordinate, LinearMap.coe_mk, AddHom.coe_mk, ite_eq_right hv] using hf
    rw [hzero, hh.1 hv]
    simp only [Pi.zero_apply, zero_smul, add_zero]
    rfl

lemma initial_homDimension_le_one (hn : ∀ a, Q.source a ≠ Q.target a)
    (α : V) (n v : ℤ) :
    homDimension Q (initialProjective Q (K := K) α) (initialProjective Q α) n v ≤ 1 := by
  apply le_trans (homDimension_le_homSpace Q _ _ n v)
  simpa only [Module.finrank_self] using LinearMap.finrank_le_finrank_of_injective
    (initialCoordinate_injective Q (K := K) hn α n v)

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_HomDimensionZeroHom
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_MinimalModel
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_MinimalModelEquivalence
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_PlacedProjective
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_ScalarSupportedCochainShift
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_GeneratorTokenTest
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.linearMap_pathBasis _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_base _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_left _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_right _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.corner_val _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_reverse
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
lemma test_token_row_zero (E:BasedComplex Q (K:=K) I) (hE:E.IsMinimal Q)
    (α:V) (i j:TestIndex Q E.placement α) (hi:Path.length i.2.val=2) :
    testMatrix Q E.placement E.placement α E.differential i j=0 := by
  have hp:=corner_length_two Q i.2 hi
  change pathCoordinates Q (pathBasis Q i.2.val * E.differential i.1 j.1) j.2.val=0
  rw [hp,pathBasis_token,coordinates_tokenBasis_mul]
  change (E.differential i.1 j.1).vertex α *
    (pathBasis Q (Path.dual Q j.2.val)).vertex α=0
  rw [congrFun (hE i.1 j.1) α,Pi.zero_apply,MulZeroClass.zero_mul]

omit [DecidableEq I] in
theorem highest_generator_test_not_exact
    (E:BasedComplex Q (K:=K) I) (hE:E.IsMinimal Q) (i:I)
    (hcap:∀ j,(E.placement j).level≤(E.placement i).level)
    (hfirst:∀ j,(E.placement j).level=(E.placement i).level→
      (E.placement i).cochain≤(E.placement j).cochain) :
    ¬ ScalarExactAt Q (E.testComplex Q (E.placement i).color) (E.placement i).color
      ((E.placement i).level+2) (E.placement i).cochain := by
  classical
  let α:=(E.placement i).color
  let T:=E.testComplex Q α
  let t:TestIndex Q E.placement α:=generatorTokenTest Q E i
  let D:=testMatrix Q E.placement E.placement α E.differential
  have ht:Path.length t.2.val=2:=rfl
  have hcol:∀ u,D u t=0 := by
    intro u
    by_contra hm
    have hm':(T.differential u t).vertex α≠0 := by
      change ((D u t) • vertexId Q (K:=K) α).vertex α≠0
      simpa [vertexId_eval] using hm
    obtain ⟨_,_,hc,hu⟩:=degree_vertex_support Q T.entries T.degree u t α hm'
    change (E.placement i).cochain=(E.placement u.1).cochain+1 at hc
    change (E.placement i).internal+2=
      (E.placement u.1).internal+Path.length u.2.val+0 at hu
    have hh:=hcap u.1
    rcases hp:u.2.val with v|a|v
    · have hl:Path.length u.2.val=0:=by rw [hp]; rfl
      dsimp only [GeneratorPlacement.level] at hh
      omega
    · have hl:Path.length u.2.val=1:=by rw [hp]; rfl
      have he:(E.placement u.1).level=(E.placement i).level := by
        dsimp only [GeneratorPlacement.level]; omega
      have hm:=hfirst u.1 he
      omega
    · exact hm (test_token_row_zero Q E hE α u t (by rw [hp]; rfl))
  intro he
  change ScalarExactAt Q T α ((E.placement i).level+2) (E.placement i).cochain at he
  let x:TestIndex Q E.placement α→K:=Pi.single t 1
  have hxs:ScalarSupported Q T ((E.placement i).level+2) (E.placement i).cochain x := by
    intro u hu
    have hut:u≠t := by
      intro hh
      subst u
      apply hu
      constructor
      · change (E.placement i).cochain+((E.placement i).internal+2)=
          (E.placement i).cochain+(E.placement i).internal+2
        omega
      · rfl
    exact Pi.single_eq_of_ne hut _
  have hxd:Matrix.vecMul x (T.differential.map (vertexHom Q α))=0 := by
    rw [testComplex_vertex_differential Q E α]
    funext u
    change (∑ v,x v * D v u)=0
    rw [Finset.sum_eq_single t]
    · exact mul_eq_zero.mpr (Or.inr (test_token_row_zero Q E hE α t u ht))
    · intro v hv hvt
      rw [show x v=0 from Pi.single_eq_of_ne hvt _,MulZeroClass.zero_mul]
    · simp
  obtain ⟨z,hzs,hzd⟩:=he x hxs hxd
  have hh:=congrFun hzd t
  rw [testComplex_vertex_differential Q E α] at hh
  have hz:Matrix.vecMul z D t=0 := by
    apply Finset.sum_eq_zero
    intro u hu
    exact mul_eq_zero.mpr (Or.inr (hcol u))
  change Matrix.vecMul z D t=x t at hh
  rw [hz] at hh
  have hx:x t=1:=Pi.single_eq_same _ _
  rw [hx] at hh
  exact zero_ne_one hh

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_ScalarSupportedTokenShift
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_TestUpperBound
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.linearMap_pathBasis _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_base _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_left _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_right _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.corner_val _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_reverse
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

omit [DecidableEq I] in
theorem generatorBound_of_test_and_outside
    (E:BasedComplex Q (K:=K) I) (hE:E.IsMinimal Q) (U:Set V) (d:ℤ)
    (h:TestUpperBound Q E U (d+2))
    (hout:∀ i,(E.placement i).color∉U→(E.placement i).level≤d) :
    ∀ i,(E.placement i).level≤d := by
  classical
  intro i
  by_contra hi
  obtain ⟨j,hj,hmax⟩:=Finset.exists_max_image (Finset.univ:Finset I)
    (fun j:I=>(E.placement j).level) ⟨i,Finset.mem_univ i⟩
  have hm:∀ k,(E.placement k).level≤(E.placement j).level:=
    fun k=>hmax k (Finset.mem_univ k)
  let F:=Finset.univ.filter (fun k:I=>(E.placement k).level=(E.placement j).level)
  have hjF:j∈F:=by simp [F]
  obtain ⟨k,hk,hmin⟩:=Finset.exists_min_image F (fun k:I=>(E.placement k).cochain) ⟨j,hjF⟩
  have hlev:(E.placement k).level=(E.placement j).level:= (Finset.mem_filter.mp hk).2
  have hkd:d<(E.placement k).level := by have hh:=hm i; omega
  have hku:(E.placement k).color∈U := by
    by_contra hn
    have hh:=hout k hn
    omega
  apply highest_generator_test_not_exact Q E hE k
    (fun z=>by rw [hlev]; exact hm z)
    (fun z hz=>hmin z (by simp [F,hz,hlev]))
  exact h (E.placement k).color hku ((E.placement k).level+2) (by omega)
    (E.placement k).cochain

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_TestExact
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_OutsideCap
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Coxeter_PositiveBraidRel
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.linearMap_pathBasis _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_base _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_left _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A:Type u} (Q:ReversibleQuiver V A)

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
-- module Solutions.OAIQ225_AG.ArtinGroups_Coxeter_OrdinaryCoxeterMatrix
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_ReducedNoTopDivisor
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_InverseWordAction
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

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Quivers_ClosedNeighborhood
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_EmptyTestIndex
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_EqualColorPair
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def zeroCornerEquiv (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) : CornerPath Q E F 0 ≃ EqualColorPair Q E F where
  toFun x := ⟨(x.val.1,x.val.2.1), by
    rcases x with ⟨⟨i,j,p⟩,hs,ht,hl⟩
    rcases p with p | p | p
    · exact hs.symm.trans ht
    · simp only [Path.length] at hl; omega
    · simp only [Path.length] at hl; omega⟩
  invFun x := ⟨(x.val.1,x.val.2,Sum.inl (E.placement x.val.1).color),rfl,x.property,rfl⟩
  left_inv x := by
    apply Subtype.ext
    rcases x with ⟨⟨i,j,p⟩,hs,ht,hl⟩
    dsimp only
    rcases p with p | p | p
    · dsimp only [Path.source] at hs
      subst p
      rfl
    · simp only [Path.length] at hl; omega
    · simp only [Path.length] at hl; omega
  right_inv x := by rfl

noncomputable def tokenCornerEquiv (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) : CornerPath Q E F 2 ≃ EqualColorPair Q E F where
  toFun x := ⟨(x.val.1,x.val.2.1), by
    rcases x with ⟨⟨i,j,p⟩,hs,ht,hl⟩
    rcases p with p | p | p
    · simp only [Path.length] at hl; omega
    · simp only [Path.length] at hl; omega
    · exact hs.symm.trans ht⟩
  invFun x := ⟨(x.val.1,x.val.2,Sum.inr (Sum.inr (E.placement x.val.1).color)),rfl,x.property,rfl⟩
  left_inv x := by
    apply Subtype.ext
    rcases x with ⟨⟨i,j,p⟩,hs,ht,hl⟩
    dsimp only
    rcases p with p | p | p
    · simp only [Path.length] at hl; omega
    · simp only [Path.length] at hl; omega
    · dsimp only [Path.source] at hs
      subst p
      rfl
  right_inv x := by rfl

noncomputable def arrowCornerEquiv (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) : CornerPath Q E F 1 ≃ ArrowPair Q E F where
  toFun x := by
    rcases x with ⟨⟨i,j,p⟩,hs,ht,hl⟩
    rcases p with p | p | p
    · simp only [Path.length] at hl; omega
    · exact ⟨(i,j,p),hs,ht⟩
    · simp only [Path.length] at hl; omega
  invFun x := ⟨(x.val.1,x.val.2.1,Sum.inr (Sum.inl x.val.2.2)),x.property.1,x.property.2,rfl⟩
  left_inv x := by
    apply Subtype.ext
    rcases x with ⟨⟨i,j,p⟩,hs,ht,hl⟩
    rcases p with p | p | p
    · simp only [Path.length] at hl; omega
    · rfl
    · simp only [Path.length] at hl; omega
  right_inv x := by rfl

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_SumTestEquiv
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
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

def sumTestEquiv (E : (i:I) → BasedComplex Q (K := K) (T i)) (α : V) :
    (Σ i, TestIndex Q (E i).placement α) ≃ TestIndex Q (finiteSum Q E).placement α where
  toFun x := ⟨⟨x.1,x.2.1⟩,x.2.2⟩
  invFun x := ⟨x.1.1,x.1.2,x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

omit [DecidableEq A] [∀ i, DecidableEq (T i)] in
lemma sumTest_differential (E : (i:I) → BasedComplex Q (K := K) (T i)) (α : V) :
    (testMatrix Q (finiteSum Q E).placement (finiteSum Q E).placement α (finiteSum Q E).differential).submatrix
      (sumTestEquiv Q E α) (sumTestEquiv Q E α) =
      Matrix.blockDiagonal' (fun i => testMatrix Q (E i).placement (E i).placement α (E i).differential) := by
  apply Matrix.ext
  rintro ⟨i,x,p⟩ ⟨j,y,q⟩
  by_cases h : i=j
  · subst j
    change pathCoordinates Q (pathBasis Q p.val * Matrix.blockDiagonal' (fun i => (E i).differential) ⟨i,x⟩ ⟨i,y⟩) q.val = _
    rw [Matrix.blockDiagonal'_apply_eq,Matrix.blockDiagonal'_apply_eq]
    rfl
  · change pathCoordinates Q (pathBasis Q p.val * Matrix.blockDiagonal' (fun i => (E i).differential) ⟨i,x⟩ ⟨j,y⟩) q.val = _
    rw [Matrix.blockDiagonal'_apply_ne _ _ _ h,Matrix.blockDiagonal'_apply_ne _ _ _ h,
      MulZeroClass.mul_zero,coordinates_zero]

noncomputable def finiteSumTopTestEquiv (E : (i:I) → BasedComplex Q (K := K) (T i))
    (α : V) (c : ℤ) :
    topTestCycles Q (finiteSum Q E) α c ≃ₗ[K] ((i:I) → topTestCycles Q (E i) α c) := by
  let e := ScalarCycles.reindexEquiv
    (testMatrix Q (finiteSum Q E).placement (finiteSum Q E).placement α (finiteSum Q E).differential).transpose
    (fun x => ((finiteSum Q E).placement x.1).cochain=c ∧ Path.length x.2.val=2)
    (sumTestEquiv Q E α)
  have ht : (Matrix.blockDiagonal' (fun i =>
      testMatrix Q (E i).placement (E i).placement α (E i).differential)).transpose =
      Matrix.blockDiagonal' (fun i => (testMatrix Q (E i).placement (E i).placement α (E i).differential).transpose) := by
    apply Matrix.ext
    rintro ⟨i,x⟩ ⟨j,y⟩
    by_cases h : i=j
    · subst j; simp only [Matrix.transpose_apply,Matrix.blockDiagonal'_apply_eq]
    · simp only [Matrix.transpose_apply,Matrix.blockDiagonal'_apply_ne _ _ _ h,
        Matrix.blockDiagonal'_apply_ne _ _ _ (Ne.symm h)]
  rw [← Matrix.transpose_submatrix,sumTest_differential,ht] at e
  exact e.trans (ScalarCycles.blockEquiv
    (fun i => (testMatrix Q (E i).placement (E i).placement α (E i).differential).transpose)
    (fun i x => ((E i).placement x.1).cochain=c ∧ Path.length x.2.val=2))

noncomputable def coefficientTopSumEquiv (E : (i:I) → BasedComplex Q (K := K) (T i))
    {l:ℤ} (hE : ∀ i x, ((E i).placement x).level=l) (α : V) (c : ℤ) :
    coefficientTopDual Q (finiteSum Q E) α c ≃ₗ[K] ((i:I) → coefficientTopDual Q (E i) α c) :=
  ((coefficientTopTestEquiv Q (finiteSum Q E) (fun x => hE x.1 x.2) α c).trans
    (finiteSumTopTestEquiv Q E α c)).trans
    (LinearEquiv.piCongrRight (fun i => (coefficientTopTestEquiv Q (E i) (hE i) α c).symm))

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_LevelArrayMinimalApply
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_FiniteFamilyLevelSupport
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_GeneratorVector
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
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
lemma generatorVector_sum (E : BasedComplex Q (K := K) I) (α : V) :
    generatorVector Q E α = ∑ i, if (E.placement i).color = α then (1 : ℝ) else 0 := by
  classical
  simp only [generatorVector, Nat.card_eq_fintype_card, Fintype.card_subtype,
    ← Finset.sum_boole]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_HighConeIndex
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
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

noncomputable def highConeNormalized (E:BasedComplex Q (K:=K) I) (T:Set I)
    (h:DownClosed Q E T) :=
  ((highProjection Q E T h).cone Q).reindex Q (highConeIndex T)

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

noncomputable def highPureIndex (E:BasedComplex Q (K:=K) I) (q:ℤ)
    (hE:∀ i,(E.placement i).level≤q) :
    {i:I // (E.placement i).level=q} ≃ ((lowerLevelSet Q E (q-1))ᶜ:Set I) where
  toFun i:=⟨i.val,by change ¬(E.placement i.val).level≤q-1; have hi:=i.property; omega⟩
  invFun i:=⟨i.val,by
    have hi:=i.property
    have hu:=hE i.val
    change ¬(E.placement i.val).level≤q-1 at hi
    omega⟩
  left_inv _:=rfl
  right_inv _:=rfl

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_InverseMatrix
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
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

omit [Fintype V] [DecidableEq A] [DecidableEq I] [DecidableEq J] in
lemma through_absent_level_zero {C:BasedComplex Q (K:=K) I}
    (D:BasedComplex Q (K:=K) J) (f:Map Q C D) (g:Map Q D C)
    (q:ℤ) (hD:∀ j,(D.placement j).level≠q)
    (i k:I) (hi:(C.placement i).level=q) (hk:(C.placement k).level=q) :
    (f.matrix*g.matrix) i k=0 := by
  apply Finset.sum_eq_zero
  intro j _
  change f.matrix i j*g.matrix j k=0
  by_cases hf:f.matrix i j=0
  · rw [hf,zero_mul]
  by_cases hg:g.matrix j k=0
  · rw [hg,mul_zero]
  have hl:=map_level_bound Q f i j hf
  have hu:=map_level_bound Q g j k hg
  exact (hD j (by omega)).elim

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_PositiveConeIndex
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_HighConeRetainedPure
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

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_HomDimensionZeroCycles
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_TargetLow
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

noncomputable def targetLow (_E:BasedComplex Q (K:=K) I) (F:BasedComplex Q (K:=K) J) (d:ℤ) :
    Matrix I J (Q.Zigzag K)→ₗ[K] Matrix I (lowerLevelSet Q F d) (Q.Zigzag K) where
  toFun M i j:=M i j
  map_add' _ _:=rfl
  map_smul' _ _:=rfl

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_HomMono
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

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Quivers_ProbeVertex
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.linearMap_pathBasis _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_base _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_left _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_right _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.corner_val _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_reverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver
variable {V A:Type*} (Q:ReversibleQuiver V A)
attribute [local instance] Classical.decEq Classical.propDecidable

lemma probe_source_iff (v:V) (b:Bool) (a:ProbeArrow V A) :
    (probeQuiver Q).source a=.inr (v,b) ↔ a=.inr (v,b,true) := by
  cases a with
  | inl a => simp [probeQuiver]
  | inr a => rcases a with ⟨w,c,dir⟩; cases dir <;> simp [probeQuiver]

lemma probe_target_iff (v:V) (b:Bool) (a:ProbeArrow V A) :
    (probeQuiver Q).target a=.inr (v,b) ↔ a=.inr (v,b,false) := by
  cases a with
  | inl a => simp [probeQuiver]
  | inr a => rcases a with ⟨w,c,dir⟩; cases dir <;> simp [probeQuiver]

namespace Zigzag.BasedComplex
variable {K I:Type*} [Field K] [Fintype V] [Fintype A] [Fintype I]
local notation "R" => probeQuiver Q

abbrev probeCoefficient (E:BasedComplex R (K:=K) I) (α:V) (n v:ℤ) :=
  {j:I // (E.placement j).color=.inl α ∧ (E.placement j).cochain=n ∧
    (E.placement j).internal=v-1}

lemma probeHomPath_arrow (E:BasedComplex R (K:=K) I) (α:V) (b:Bool)
    (ha:∀i,(E.placement i).color≠.inr (α,b)) (n v:ℤ)
    (t:HomPath R ((initialProjective R (.inr (α,b)) : BasedComplex R (K:=K) PUnit.{1})) E n v) :
    t.val.2.2=.inr (.inl (.inr (α,b,true))) := by
  rcases t with ⟨⟨i,j,p⟩,hs,ht,hc,hd⟩
  cases p with
  | inl w => exact False.elim (ha j (ht.symm.trans hs))
  | inr p => cases p with
    | inl a =>
      exact congrArg (fun a:ProbeArrow V A=>Sum.inr (Sum.inl a))
        ((probe_source_iff Q α b a).mp hs)
    | inr w => exact False.elim (ha j (ht.symm.trans hs))

noncomputable def probeHomPathEquiv (E:BasedComplex R (K:=K) I) (α:V) (b:Bool)
    (ha:∀i,(E.placement i).color≠.inr (α,b)) (n v:ℤ) :
    HomPath R ((initialProjective R (.inr (α,b)) : BasedComplex R (K:=K) PUnit.{1})) E n v ≃ probeCoefficient Q E α n v where
  toFun t := ⟨t.val.2.1,by
    have hp:=probeHomPath_arrow Q E α b ha n v t
    have ht:=t.property.2.1
    have hc:=t.property.2.2.1
    have hd:=t.property.2.2.2
    rw [hp] at ht hd
    change Sum.inl α=(E.placement t.val.2.1).color at ht
    change (E.placement t.val.2.1).cochain=0+n at hc
    change (1:ℤ)=v+0-(E.placement t.val.2.1).internal at hd
    exact ⟨ht.symm,by omega,by omega⟩⟩
  invFun j := ⟨(PUnit.unit,j.val,.inr (.inl (.inr (α,b,true)))),by
    refine ⟨rfl,j.property.1.symm,?_,?_⟩
    · change (E.placement j.val).cochain=0+n
      rw [j.property.2.1,zero_add]
    · change (1:ℤ)=v+0-(E.placement j.val).internal
      rw [j.property.2.2]; omega⟩
  left_inv t := by
    apply Subtype.ext
    apply Prod.ext
    · exact Subsingleton.elim _ _
    · exact Prod.ext rfl (probeHomPath_arrow Q E α b ha n v t).symm
  right_inv _ := rfl

end Zigzag.BasedComplex
end HarmonicArtin.ReversibleQuiver

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_InitialProbeTestUpper
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

omit [Fintype V] [Fintype A] [DecidableEq (ProbeVertex V)]
  [DecidableEq (ProbeArrow V A)] in
lemma probe_core_leaf_orthogonal {α β:V} (h:α≠β) (b:Bool) :
    OrthogonalVertices R (.inl α) (.inr (β,b)) := by
  refine ⟨Sum.inl_ne_inr,?_⟩
  intro a hs ht
  have ha: a=.inr (β,b,false):=(probe_target_iff Q β b a).mp ht
  rw [ha] at hs
  exact h (Sum.inl.inj hs).symm

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_IsolatedIndexCycle
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.linearMap_pathBasis _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_base _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_left _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_right _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.corner_val _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_reverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K I:Type*} (Q:ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A] [Fintype I] [DecidableEq I]

lemma isolated_index_cycle (E:BasedComplex Q (K:=K) I) (i:I)
    (hr:∀j,E.differential i j=0) (hc:∀j,E.differential j i=0) :
    Matrix.single i i (vertexId Q (K:=K) (E.placement i).color)∈homCycles Q E E 0 0 := by
  let f:=Matrix.single i i (vertexId Q (K:=K) (E.placement i).color)
  have h₁:E.differential*f=0 := by
    apply Matrix.ext; intro j k
    change (∑l,E.differential j l*f l k)=0
    apply Finset.sum_eq_zero
    intro l hl
    by_cases hli:i=l
    · subst l
      rw [hc,zero_mul]
    · simp [f,hli]
  have h₂:f*E.differential=0 := by
    apply Matrix.ext; intro j k
    change (∑l,f j l*E.differential l k)=0
    apply Finset.sum_eq_zero
    intro l hl
    by_cases hli:i=l
    · subst l
      rw [hr,mul_zero]
    · simp [f,hli]
  refine ⟨⟨?_,?_⟩,?_⟩
  · apply projectiveEntries_single Q
    · exact vertexId_mul_self Q _
    · exact vertexId_mul_self Q _
  · apply mapDegree_single Q _ _ _ _ _ 0 0 (by omega)
    simpa only [zero_add,sub_self,Path.length,pathBasis_vertex] using pathBasis_homogeneous Q (K:=K) (Sum.inl (E.placement i).color)
  · change E.differential*f-cochainSign (K:=K) 0 • (f*E.differential)=0
    rw [h₁,h₂,smul_zero,sub_zero]

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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_LayerTotalHomDimension
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_NegativeConeIndex
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_PacketPermExterior
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.linearMap_pathBasis _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_base _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_left _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
attribute [local instance] Classical.decEq
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  (hn:∀ a,Q.source a≠Q.target a)

omit [Fintype V] [DecidableEq A] in
lemma classLevelArray_initial (α β:V) (q:ℤ) :
    classLevelArray Q (initialClass Q (K:=K) α) (β,q)=if α=β ∧ q=0 then 1 else 0 := by
  classical
  rw [initialClass,classLevelArray_of_minimal Q _ (show (initialProjective Q α).IsMinimal Q from
    fun i j=>rfl)]
  change (initialProjective Q α).levelArray Q (β,q)=_
  rw [levelArray_eq_sum]
  simp only [initialProjective,GeneratorPlacement.level,Finset.univ_unique,
    Finset.sum_singleton,Finsupp.single_apply,Prod.mk.injEq]
  simp [eq_comm]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_PlacementSignedWeight
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

omit [Fintype V] [DecidableEq A] in
lemma signedGeneratorVector_minimal_eq {I J : Type u} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (E : BasedComplex Q (K:=K) I) (F : BasedComplex Q (K:=K) J)
    (hE : E.IsMinimal Q) (hF : F.IsMinimal Q) (e : HomotopyEquivalence Q E F) :
    signedGeneratorVector Q E=signedGeneratorVector Q F := by
  funext v
  rw [signedGeneratorVector_array,signedGeneratorVector_array,
    generatorArray_eq_of_minimal_homotopyEquivalence Q E F hE hF e]

namespace FiniteModel

omit [Fintype V] [DecidableEq A] in
lemma signedGeneratorVector_homotopy (E F : FiniteModel.{u} Q (K:=K))
    (e : HomotopyEquivalence Q E.complex F.complex) :
    signedGeneratorVector Q E.complex=signedGeneratorVector Q F.complex := by
  obtain ⟨E',hE',⟨eE⟩,hsE⟩ := E.exists_minimal_signed Q
  obtain ⟨F',hF',⟨eF⟩,hsF⟩ := F.exists_minimal_signed Q
  rw [hsE,hsF]
  exact signedGeneratorVector_minimal_eq Q _ _ hE' hF'
    ((eE.symm Q).trans Q (e.trans Q eF))

end FiniteModel

noncomputable def classSignedVector : FiniteHomotopyClass Q (K:=K) → (V → ℝ) :=
  Quotient.lift (fun E => signedGeneratorVector Q E.complex)
    (fun E F h => by obtain ⟨e⟩:=h; exact FiniteModel.signedGeneratorVector_homotopy Q E F e)

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_PositiveTwistModern
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
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

noncomputable def lowPureIndex (E:BasedComplex Q (K:=K) I) (q:ℤ)
    (hE:∀ i,q≤(E.placement i).level) :
    {i:I // (E.placement i).level=q} ≃ lowerLevelSet Q E q where
  toFun i:=⟨i.val,le_of_eq i.property⟩
  invFun i:=⟨i.val,le_antisymm i.property (hE i.val)⟩
  left_inv _:=rfl
  right_inv _:=rfl

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_PositiveWord
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_PositiveWordActionTest
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
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

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Quivers_ProbeLeaf
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver
variable {V A:Type} (Q:ReversibleQuiver V A)

lemma probe_source_leaf {a:ProbeArrow V A} {α:V} {b:Bool}
    (h:(probeQuiver Q).source a=.inr (α,b)) : (probeQuiver Q).target a=.inl α := by
  rcases a with a|⟨v,c,d⟩
  · exact (Sum.inl_ne_inr h).elim
  · cases d
    · exact (Sum.inl_ne_inr h).elim
    · have he:(v,c)=(α,b):=Sum.inr.inj h
      cases he
      rfl

lemma probe_target_leaf {a:ProbeArrow V A} {α:V} {b:Bool}
    (h:(probeQuiver Q).target a=.inr (α,b)) : (probeQuiver Q).source a=.inl α := by
  have hh:=probe_source_leaf Q (a:=(probeQuiver Q).reverse a) (by rw [source_reverse]; exact h)
  rwa [target_reverse] at hh

namespace Zigzag.BasedComplex
variable {K I:Type*} [Field K] [Fintype V] [Fintype A] [Fintype I]
attribute [local instance] Classical.decEq Classical.propDecidable
local notation "R" => probeQuiver Q

lemma probe_differential_row_zero (E:BasedComplex R (K:=K) I) (α:V) (b:Bool)
    (hc:∀j,(E.placement j).color≠.inl α)
    (hf:∀j,(E.placement j).color=.inr (α,b)→(E.placement j).cochain=0)
    (i:I) (hi:(E.placement i).color=.inr (α,b)) (j:I) : E.differential i j=0 := by
  apply (pathCoordinates R).injective
  funext p
  rw [coordinates_zero]
  by_contra hp
  have hs:=coordinates_corner R (E.entries.1 i j) (E.entries.2 i j) hp
  have hdeg:(E.placement j).cochain=(E.placement i).cochain+1 := by
    by_contra h
    exact hp (by rw [(E.degree i j).1 h,coordinates_zero])
  rcases p with v|a|v
  · have hj:(E.placement j).color=.inr (α,b):=hs.2.symm.trans (hs.1.trans hi)
    have hh:=hf j hj
    have hh':=hf i hi
    omega
  · have hh:=probe_source_leaf Q (hs.1.trans hi)
    exact hc j (hs.2.symm.trans hh)
  · have hj:(E.placement j).color=.inr (α,b):=hs.2.symm.trans (hs.1.trans hi)
    have hh:=hf j hj
    have hh':=hf i hi
    omega

lemma probe_differential_col_zero (E:BasedComplex R (K:=K) I) (α:V) (b:Bool)
    (hc:∀j,(E.placement j).color≠.inl α)
    (hf:∀j,(E.placement j).color=.inr (α,b)→(E.placement j).cochain=0)
    (i:I) (hi:(E.placement i).color=.inr (α,b)) (j:I) : E.differential j i=0 := by
  apply (pathCoordinates R).injective
  funext p
  rw [coordinates_zero]
  by_contra hp
  have hs:=coordinates_corner R (E.entries.1 j i) (E.entries.2 j i) hp
  have hdeg:(E.placement i).cochain=(E.placement j).cochain+1 := by
    by_contra h
    exact hp (by rw [(E.degree j i).1 h,coordinates_zero])
  rcases p with v|a|v
  · have hj:(E.placement j).color=.inr (α,b):=hs.1.symm.trans (hs.2.trans hi)
    have hh:=hf j hj
    have hh':=hf i hi
    omega
  · have hh:=probe_target_leaf Q (hs.2.trans hi)
    exact hc j (hs.1.symm.trans hh)
  · have hj:(E.placement j).color=.inr (α,b):=hs.1.symm.trans (hs.2.trans hi)
    have hh:=hf j hj
    have hh':=hf i hi
    omega

lemma generatorArray_placement_pos (E:BasedComplex R (K:=K) I) (i:I) :
    0<E.generatorArray R (E.placement i) := by
  rw [generatorArray_apply]
  change 0<Nat.card {j:I // E.placement j=E.placement i}
  have : Nonempty {j:I // E.placement j=E.placement i}:=⟨⟨i,rfl⟩⟩
  exact Nat.card_pos

end Zigzag.BasedComplex
end HarmonicArtin.ReversibleQuiver

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_ProbeFixedNoDiagonal
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_TermwiseSplitInjection
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_Shift
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_ScalarKernel
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
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
  {I J:Type u} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

omit [Fintype V] [DecidableEq A] [DecidableEq I] [DecidableEq J] in
lemma scalarKernel_has_socle {E:BasedComplex Q (K:=K) I} {F:BasedComplex Q (K:=K) J}
    {f:Map Q E F} (hf:CoefficientMatrix Q f.matrix) {x:I→K}
    (hx:ScalarKernel Q f x) (hx0:x≠0) :
    ∃ α c y,y∈coefficientSocle Q E α c ∧ y≠0 ∧ ScalarKernel Q f y := by
  let S:Finset I:=Finset.univ.filter fun i=>∃ y:I→K,
    PlacementSupported Q E (E.placement i).color (E.placement i).cochain y ∧
      y≠0 ∧ ScalarKernel Q f y
  have hs:S.Nonempty := by
    obtain ⟨i,hi⟩:∃ i,x i≠0 := by
      by_contra h
      push Not at h
      exact hx0 (funext h)
    let y:I→K:=fun j=>if E.placement j=E.placement i then x j else 0
    refine ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,y,?_,?_,hx.project Q _⟩⟩
    · intro j hj
      have he:E.placement j≠E.placement i := by intro he; simp only [he,ne_self_iff_false,or_self] at hj
      exact ite_eq_right he
    · intro hz
      have hh:=congrFun hz i
      apply hi
      simpa only [y,ite_eq_left rfl,Pi.zero_apply] using hh
  obtain ⟨i,hi,hmax⟩:=Finset.exists_max_image S (fun i=>(E.placement i).cochain) hs
  obtain ⟨y,hy,hy0,hyker⟩:=(Finset.mem_filter.mp hi).2
  refine ⟨(E.placement i).color,(E.placement i).cochain,y,⟨hy,?_⟩,hy0,hyker⟩
  intro j a _
  have hz:coefficientOutgoing Q E y a=0 := by
    by_contra hz
    obtain ⟨t,ht⟩:∃ t,coefficientOutgoing Q E y a t≠0 := by
      by_contra h
      push Not at h
      exact hz (funext h)
    have hsupp:=coefficientOutgoing_support Q E _ _ hy a
    have hc:(E.placement t).color=Q.target a :=
      Classical.not_not.mp (fun hn=>ht (hsupp t (Or.inl hn)))
    have hd:(E.placement t).cochain=(E.placement i).cochain+1 :=
      Classical.not_not.mp (fun hn=>ht (hsupp t (Or.inr hn)))
    have htS:t∈S := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,coefficientOutgoing Q E y a,?_,hz,hyker.outgoing Q hf a⟩
      simpa only [hc,hd] using hsupp
    have hh:=hmax t htS
    omega
  exact congrFun hz j

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_PureLayerSelf
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

noncomputable def TermwiseSplitInjection.trans
    {E:BasedComplex Q (K:=K) I} {F:BasedComplex Q (K:=K) J} {G:BasedComplex Q (K:=K) T}
    (a:TermwiseSplitInjection Q E F) (b:TermwiseSplitInjection Q F G) :
    TermwiseSplitInjection Q E G where
  inclusion:=Map.comp Q a.inclusion b.inclusion
  retraction:=b.retraction*a.retraction
  split:=by
    change (a.inclusion.matrix*b.inclusion.matrix)*(b.retraction*a.retraction)=_
    rw [Matrix.mul_assoc,← Matrix.mul_assoc b.inclusion.matrix,b.split,← Matrix.mul_assoc]
    exact (congrArg (fun X=>X*a.retraction) (mul_projectiveIdentity Q a.inclusion.entries)).trans a.split

noncomputable def ChainIsomorphism.termwiseSplit
    {E:BasedComplex Q (K:=K) I} {F:BasedComplex Q (K:=K) J}
    (e:ChainIsomorphism Q E F) : TermwiseSplitInjection Q E F :=
  ⟨e.forward,e.backward.matrix,e.sourceEquation⟩

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

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_TotalVector
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.linearMap_pathBasis _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_base _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_left _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
open _root_.Matrix
open scoped BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

omit [Fintype V] [DecidableEq A] in
lemma classSignedVector_minimal (x : FiniteHomotopyClass Q (K:=K)) :
    classSignedVector Q x=signedGeneratorVector Q (minimalClassModel Q x).complex := by
  exact (congrArg (classSignedVector Q) (minimalClassModel_class Q x)).symm

omit [Fintype V] [DecidableEq A] in
lemma signedGeneratorVector_pure {I : Type u} [Fintype I]
    (E : BasedComplex Q (K:=K) I) (q : ℤ) (hE : ∀ i,(E.placement i).level=q) :
    signedGeneratorVector Q E=cochainSign (K:=ℝ) q • generatorVector Q E := by
  funext v
  simp only [signedGeneratorVector,placementSignedWeight,hE,generatorVector_sum,
    Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

omit [Fintype V] [DecidableEq A] in
lemma classSignedVector_pure (x : FiniteHomotopyClass Q (K:=K)) (q : ℤ)
    (hlo : ClassLowerBound Q q x) (hhi : ClassUpperBound Q q x) :
    classSignedVector Q x=cochainSign (K:=ℝ) q • classTotalVector Q x := by
  rw [classSignedVector_minimal]
  exact signedGeneratorVector_pure Q _ q (fun i=>le_antisymm (hhi i) (hlo i))

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_WordInverseModel
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

lemma canonicalLowTarget_class (hn:∀ a,Q.source a≠Q.target a)
    (w:List V) (x:FiniteHomotopyClass Q (K:=K)) :
    classOfComplex Q (canonicalLowTarget Q w x).complex=x := by
  rw [canonicalLowTarget,FiniteModel.positiveWord_class]
  change positiveWordAction Q w (classOfComplex Q (minimalClassModel Q (inverseWordAction Q w x)).complex)=x
  have he:classOfComplex Q (minimalClassModel Q (inverseWordAction Q w x)).complex=
      inverseWordAction Q w x:=minimalClassModel_class Q _
  rw [he,positive_inverseWord Q hn]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Functors_LeftSocleIndexEquiv
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Functors_HomDualSupportedCycles
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Functors_TruncationIndexEquiv
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_CanonicalFusionLow
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

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_FusionQuiverSimpleEdge
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.instDecidableRelStringLabelStringAdjacent
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.labelSplit_apply _root_.OAI.HarmonicArtin.labelSplit_symm_at _root_.OAI.HarmonicArtin.labelSplit_symm_rest _root_.OAI.HarmonicArtin.unfoldedHom_simple _root_.OAI.HarmonicArtin.unfoldedMatrix_apply
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_UnfoldedInclusion
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.instDecidableRelStringLabelStringAdjacent _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open CoxeterExchange

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S]

variable (M : CoxeterMatrix S)
local notation "Q" => fusionQuiver (fusionLabelSize M) (coxeterFusionEdge M) (coxeterFusionEdge_symm M)

lemma unfolded_full_simply_laced (J : Set S) (hJ : IsSpherical M J) :
    ∀ α∈Set.range (unfoldedInclusion M J),∀ β∈Set.range (unfoldedInclusion M J),
      α=β ∨ OrthogonalVertices Q α β ∨ Nonempty (SimpleEdge Q α β) := by
  rintro _ ⟨α,rfl⟩ _ ⟨β,rfl⟩
  by_cases he : α=β
  · exact Or.inl (congrArg _ he)
  have hi := fun hh => he (unfoldedInclusion_injective M J hh)
  have hn := spherical_fusion_multiplicity_le_one M J hJ α.1 β.1 α.2 β.2
  have hp : (coxeterFusionEdge M (.inl α.1) (.inl β.1)).multiplicity
      (fusionLabelSize M) α.2 β.2=0 ∨
    (coxeterFusionEdge M (.inl α.1) (.inl β.1)).multiplicity
      (fusionLabelSize M) α.2 β.2=1 := by omega
  rcases hp with hz|ho
  · exact Or.inr (Or.inl (fusionQuiver_orthogonal _ _ _ _ _ hi hz))
  · exact Or.inr (Or.inr ⟨fusionQuiver_simpleEdge _ _ _ _ _ hi ho⟩)

theorem unfolded_full_reduced (J : Set S) (hJ : IsSpherical M J)
    (u : List J) (hu : (restrictedMatrix M J).toCoxeterSystem.IsReduced u) :
    (ordinaryCoxeterMatrix Q).toCoxeterSystem.IsReduced
      (fusionExpandedWord (fusionLabelSize M) (u.map fun j : J => (Sum.inl (j:S) : S⊕Unit))) := by
  rw [fusionExpandedWord_map]
  exact embedding_reduced (unfoldedInclusion M J) (unfoldedInclusion_injective M J)
    (unfolded_ordinaryMatrix M J hJ) _ (unfolded_reducedWord M J hJ u hu)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Quivers_ProbeSimpleEdge
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.linearMap_pathBasis _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_base _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_left _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver
open Zigzag Zigzag.BasedComplex CoxeterExchange

variable {V A:Type} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
attribute [local instance] Classical.decEq Classical.propDecidable
local notation "R" => probeQuiver Q
variable [DecidableEq (ProbeVertex V)] [DecidableEq (ProbeArrow V A)]

omit [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [DecidableEq (ProbeVertex V)] [DecidableEq (ProbeArrow V A)] in
lemma probe_orthogonal {α β:V} (h:OrthogonalVertices Q α β) :
    OrthogonalVertices R (.inl α) (.inl β) := by
  refine ⟨fun hh=>h.1 (Sum.inl.inj hh),?_⟩
  rintro (a|⟨v,b,dir⟩) hs ht
  · exact h.2 a (Sum.inl.inj hs) (Sum.inl.inj ht)
  · cases dir <;> simp [probeQuiver] at hs ht

def probe_simpleEdge {α β:V} (e:SimpleEdge Q α β) :
    SimpleEdge R (.inl α) (.inl β) where
  arrow:=.inl e.arrow
  source:=congrArg Sum.inl e.source
  target:=congrArg Sum.inl e.target
  distinct:=fun h=>e.distinct (Sum.inl.inj h)
  unique:=by
    rintro (a|⟨v,b,dir⟩) hs ht
    · exact congrArg Sum.inl (e.unique a (Sum.inl.inj hs) (Sum.inl.inj ht))
    · cases dir <;> simp [probeQuiver] at hs ht

end HarmonicArtin.ReversibleQuiver

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_ProbePacket
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex CoxeterExchange

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] {K:Type*} [Field K]
  (M:CoxeterMatrix S)
local notation "Q" => fusionQuiver (fusionLabelSize M) (coxeterFusionEdge M) (coxeterFusionEdge_symm M)
local notation "hn" => fusionQuiver_no_loops (fusionLabelSize M) (coxeterFusionEdge M)
  (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M)
local notation "R" => probeQuiver Q
local notation "f" => fun v=>classTwistPerm R (K:=K) (probeQuiver_no_loops Q hn) (Sum.inl v)

noncomputable def sourceProbePacket (s:S) : Equiv.Perm (FiniteHomotopyClass R (K:=K)) :=
  ((fusionExpandedWord (fusionLabelSize M) [Sum.inl s]).map f).prod

lemma sourceProbeWord_expand (u:List S) :
    (u.map (sourceProbePacket M (K:=K))).prod=
      ((fusionExpandedWord (fusionLabelSize M) (u.map Sum.inl)).map f).prod := by
  induction u with
  | nil=>rfl
  | cons s u ih=>
    simp only [List.map_cons,List.prod_cons,ih,sourceProbePacket,fusionExpandedWord,
      List.flatMap_cons,List.flatMap_nil,List.append_nil,List.map_append,List.prod_append]

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_ProbeCoreInclusion
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open CoxeterExchange

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] {K:Type*} [Field K]
  (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "Q" => fusionQuiver m (coxeterFusionEdge M) (coxeterFusionEdge_symm M)
local notation "R" => probeQuiver Q

lemma probeCore_matrix (J:Set S) (hJ:IsSpherical M J) (α β:J × FusionLabel m) :
    ordinaryCoxeterMatrix R (probeCoreInclusion M J α) (probeCoreInclusion M J β)=
      unfoldedMatrix M J α β := by
  rcases unfolded_full_simply_laced M J hJ (unfoldedInclusion M J α) ⟨α,rfl⟩
    (unfoldedInclusion M J β) ⟨β,rfl⟩ with he | hrest
  · have h:=unfoldedInclusion_injective M J he
    subst β
    simp
  · rcases hrest with ho | hedge
    · rw [← unfolded_ordinaryMatrix M J hJ,ordinaryCoxeterMatrix_orthogonal Q ho]
      exact ordinaryCoxeterMatrix_orthogonal R (probe_orthogonal Q ho)
    · obtain ⟨e⟩:=hedge
      rw [← unfolded_ordinaryMatrix M J hJ,ordinaryCoxeterMatrix_adjacent Q e]
      exact ordinaryCoxeterMatrix_adjacent R (probe_simpleEdge Q e)

lemma probeCore_simply_laced (J:Set S) (hJ:IsSpherical M J) :
    ∀ α∈Set.range (probeCoreInclusion M J),∀ β∈Set.range (probeCoreInclusion M J),
      α=β ∨ OrthogonalVertices R α β ∨ Nonempty (SimpleEdge R α β) := by
  rintro _ ⟨α,rfl⟩ _ ⟨β,rfl⟩
  rcases unfolded_full_simply_laced M J hJ _ ⟨α,rfl⟩ _ ⟨β,rfl⟩ with he | hrest
  · exact Or.inl (congrArg Sum.inl he)
  · rcases hrest with ho | hedge
    · exact Or.inr (Or.inl (probe_orthogonal Q ho))
    · obtain ⟨e⟩:=hedge
      exact Or.inr (Or.inr ⟨probe_simpleEdge Q e⟩)

lemma probeCore_cons_reduced (J:Set S) (hJ:IsSpherical M J) (w:List J) (j:J)
    (hw:(restrictedMatrix M J).toCoxeterSystem.IsReduced w)
    (hj:(restrictedMatrix M J).toCoxeterSystem.IsReduced (j::w)) (L:FusionLabel m) :
    (ordinaryCoxeterMatrix R).toCoxeterSystem.IsReduced
      (probeCoreInclusion M J (j,L)::(fusionExpandedWord m w).map (probeCoreInclusion M J)) := by
  apply embedding_reduced (probeCoreInclusion M J) (probeCoreInclusion_injective M J)
    (probeCore_matrix M J hJ) ((j,L)::fusionExpandedWord m w)
  have hr:=unfolded_reducedWord M J hJ w hw
  change (unfoldedMatrix M J).toCoxeterSystem.length
    ((unfoldedMatrix M J).toCoxeterSystem.simple (j,L)*
      (unfoldedMatrix M J).toCoxeterSystem.wordProd (fusionExpandedWord m w))=
    (fusionExpandedWord m w).length+1
  rw [← unfoldedHom_wordProd M J hJ]
  have ha: (restrictedMatrix M J).toCoxeterSystem.length
      ((restrictedMatrix M J).toCoxeterSystem.simple j*
        (restrictedMatrix M J).toCoxeterSystem.wordProd w)=
      (restrictedMatrix M J).toCoxeterSystem.length
        ((restrictedMatrix M J).toCoxeterSystem.wordProd w)+1 := by
    rw [hw.eq]
    exact hj.eq
  rw [(unfoldedHom_left_ascent M J hJ _ (j,L)).mpr ha,unfoldedHom_wordProd,hr.eq]

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_InitialProbe
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open CoxeterExchange

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] {K:Type*} [Field K] (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "Q" => fusionQuiver m (coxeterFusionEdge M) (coxeterFusionEdge_symm M)
local notation "R" => probeQuiver Q

noncomputable abbrev sourceInitialProbe (s:S) (L:FusionLabel m) (b:Bool) : FiniteHomotopyClass R (K:=K) :=
  initialClass R (.inr ((.inl s,L),b))

lemma sourceInitialProbe_cap (T:Set S) (s:S) (L:FusionLabel m) (b:Bool) :
    ClassTestUpper R (sourceInitialProbe M (K:=K) s L b) (Set.range (probeCoreInclusion M T)) 1 :=
  initialProbe_test_upper Q _ b _ (by rintro _ ⟨α,rfl⟩; exact ⟨_,rfl⟩)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_FusionWeightedHom
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
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

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_ProbePacketExterior
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open ReversibleQuiver.ProbeEmbedding

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] {K:Type*} [Field K] (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "Q" => fusionQuiver m d (coxeterFusionEdge_symm M)
local notation "R" => probeQuiver Q

lemma sourceProbeInitial_array (α:ProbeVertex (FusionVertex (V:=S⊕Unit) m))
    (p:GeneratorPlacement (ProbeVertex (FusionVertex (V:=S⊕Unit) m))) :
    classGeneratorArray R (initialClass R (K:=K) α) p=if p=⟨α,0,0⟩ then 1 else 0 := by
  rw [initialClass,classGeneratorArray_of_minimal R _ (show (initialProjective R α).IsMinimal R from
    fun i j=>rfl)]
  change (initialProjective R α).generatorArray R p=_
  rw [generatorArray]
  simp only [initialProjective,Finset.univ_unique,Finset.sum_singleton,Finsupp.single_apply,eq_comm]

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_CosetBelow
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.positiveToArtin_generator _root_.OAI.HarmonicArtin.positiveToArtin_word
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

omit [Fintype S] [LinearOrder S] in
lemma sourceCoset_representative_le_iff {P R:Deligne M} (x y:Artin M) (hx:x∈P.val.2) (hy:y∈R.val.2) :
    P ≤ R ↔ P.val.1⊆R.val.1 ∧ x*y⁻¹∈artinParabolic M R.val.1 := by
  conv_lhs => rw [←sourceCoset_eq M P x hx,←sourceCoset_eq M R y hy]
  exact sourceCoset_le_iff M x y

noncomputable def sourceBelowOffset (B:Set S) (hB:IsSpherical M B) (x:Artin M)
    (P:SourceCosetBelow M B hB x) : artinParabolic M B :=
  ⟨sourceCosetRepresentative M P.val*x⁻¹,P.property.2 (sourceCosetRepresentative_mem M P.val)⟩

omit [Fintype S] [LinearOrder S] in
lemma sourceBelowOffset_rep (B:Set S) (hB:IsSpherical M B) (x:Artin M)
    (P:SourceCosetBelow M B hB x) : (sourceBelowOffset M B hB x P:Artin M)*x=sourceCosetRepresentative M P.val := by
  simp [sourceBelowOffset,mul_assoc]

noncomputable def sourceCosetProductFun (B C:Set S) (hT:IsSpherical M (B∪C)) (x:Artin M)
    (P:SourceCosetBelow M B (source_spherical_mono M Set.subset_union_left hT) x ×
      SourceCosetBelow M C (source_spherical_mono M Set.subset_union_right hT) x) :
    SourceCosetBelow M (B∪C) hT x := by
  let b:=sourceBelowOffset M B _ x P.1
  let c:=sourceBelowOffset M C _ x P.2
  let R:=P.1.val.val.1∪P.2.val.val.1
  have hR:R⊆B∪C:=Set.union_subset_union P.1.property.1 P.2.property.1
  refine ⟨sourceCoset M R (source_spherical_mono M hR hT) ((b:Artin M)*c*x),?_⟩
  apply (sourceCoset_le_iff M _ _).mpr
  refine ⟨hR,?_⟩
  simpa only [mul_assoc,mul_inv_cancel,mul_one] using
    Subgroup.mul_mem (artinParabolic M (B∪C))
      (artinParabolic_mono M Set.subset_union_left b.property)
      (artinParabolic_mono M Set.subset_union_right c.property)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_RestrictionHomRange
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type*} [Fintype S] (M:CoxeterMatrix S)

theorem spherical_of_left_descents (J:Set S) (w:M.Group)
    (hJ:∀s∈J,M.toCoxeterSystem.length (M.toCoxeterSystem.simple s*w)<M.toCoxeterSystem.length w) :
    IsSpherical M J := by
  obtain ⟨q,v,hq,hv,he,hl⟩:=exists_longest_descent_factor M J w hJ
  let : Finite (restrictedMatrix M J).Group:=finite_of_all_descents
    (restrictedMatrix M J).toCoxeterSystem q
      (all_descents_of_longest (restrictedMatrix M J).toCoxeterSystem q hq)
  apply Finite.of_surjective
    (fun r=>(⟨restrictionHom M J r,Geometric.restrictionHom_mem_parabolic M J r⟩:coxeterParabolic M J))
  intro a
  have ha:a.val∈(restrictionHom M J).range:=by rw [restrictionHom_range_eq];exact a.property
  obtain ⟨r,hr⟩:=ha
  exact ⟨r,Subtype.ext hr⟩

theorem positive_longest_descent_prefix (J:Set S) (w:M.Group)
    (hJ:∀s∈J,M.toCoxeterSystem.length (M.toCoxeterSystem.simple s*w)<M.toCoxeterSystem.length w) :
    ∃q:(restrictedMatrix M J).Group,
      (∀r:(restrictedMatrix M J).Group,(restrictedMatrix M J).toCoxeterSystem.length r≤
        (restrictedMatrix M J).toCoxeterSystem.length q) ∧
      PositivePrefix M (positiveSimpleLift M (restrictionHom M J q)) (positiveSimpleLift M w) := by
  obtain ⟨q,v,hq,hv,he,hl⟩:=exists_longest_descent_factor M J w hJ
  refine ⟨q,hq,v |> positiveSimpleLift M,?_⟩
  rw [he]
  apply positiveSimpleLift_mul
  simpa only [he,restriction_length] using hl

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_PositiveHead
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.positiveReverse_generator _root_.OAI.HarmonicArtin.positiveReverse_involutive _root_.OAI.HarmonicArtin.positiveReverse_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CoxeterExchange

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type*} [Fintype S] (M:CoxeterMatrix S)

lemma exists_front_head
    (cancel:∀a b c:PositiveArtin M,a*b=a*c→b=c)
    (z:M.Group) (hz:∀w,M.toCoxeterSystem.length w≤M.toCoxeterSystem.length z)
    (a:PositiveArtin M)
    (ih:∀b:PositiveArtin M,positiveDegree M b<positiveDegree M a→HasPositiveHead M b)
    (s:S) (hs:PositivePrefix M (positiveGenerator M s) a) :
    ∃h:M.Group,IsFrontHead M a s h := by
  obtain ⟨b,hb⟩:=hs
  have hdeg:positiveDegree M b<positiveDegree M a:=by rw [hb,positiveDegree_mul,positiveDegree_generator];omega
  obtain ⟨g,hgb,hgreat⟩:=ih b hdeg
  let c: M.Group:=(M.toCoxeterSystem.simple s)⁻¹*z
  have hsc:positiveGenerator M s*positiveSimpleLift M c=positiveSimpleLift M z:=by
    simpa only [positiveSimpleLift_simple] using positiveSimpleLift_left_complement M z hz (M.toCoxeterSystem.simple s)
  obtain ⟨k,hkg,hkc,hmeet⟩:=exists_greatest_common_simplePrefix M g c
  let x:PositiveArtin M:=positiveGenerator M s*positiveSimpleLift M k
  have hxb:PositivePrefix M x a:=by
    obtain ⟨r,hr⟩:=positivePrefix_trans M hkg hgb
    refine ⟨r,?_⟩
    rw [hb,hr,mul_assoc]
  have hxΔ:PositivePrefix M x (positiveSimpleLift M z):=by
    obtain ⟨r,hr⟩:=hkc
    refine ⟨r,?_⟩
    rw [←hsc,hr,mul_assoc]
  have hx:x=positiveSimpleLift M (positiveToCoxeter M x):=positivePrefix_of_simple_eq M hxΔ rfl
  refine ⟨positiveToCoxeter M x,?_,?_,?_⟩
  · exact hx ▸ hxb
  · rw [←hx]
    exact ⟨positiveSimpleLift M k,rfl⟩
  · intro w hwa hsw
    obtain ⟨e,he⟩:=hsw
    have hes:e=positiveSimpleLift M (positiveToCoxeter M e):=
      (positive_simple_factors M (positiveGenerator M s) e w he.symm).2
    have heb:PositivePrefix M e b:=by
      obtain ⟨f,hf⟩:=hwa
      refine ⟨f,cancel (positiveGenerator M s) b (e*f) ?_⟩
      rw [←hb,hf,he,mul_assoc]
    have hec:PositivePrefix M e (positiveSimpleLift M c):=by
      have hwΔ:PositivePrefix M (positiveSimpleLift M w) (positiveSimpleLift M z):=
        ⟨positiveSimpleLift M (w⁻¹*z),(positiveSimpleLift_left_complement M z hz w).symm⟩
      obtain ⟨f,hf⟩:=hwΔ
      refine ⟨f,cancel (positiveGenerator M s) (positiveSimpleLift M c) (e*f) ?_⟩
      rw [hsc,hf,he,mul_assoc]
    have heg:PositivePrefix M e (positiveSimpleLift M g):=by
      rw [hes] at heb ⊢
      exact hgreat _ heb
    obtain ⟨r,hr⟩:=hmeet e heg hec
    rw [←hx]
    refine ⟨r,?_⟩
    dsimp [x]
    rw [he,hr,mul_assoc]

theorem positive_greedy_head
    (cancel:∀a b c:PositiveArtin M,a*b=a*c→b=c)
    (z:M.Group) (hz:∀w,M.toCoxeterSystem.length w≤M.toCoxeterSystem.length z)
    (a:PositiveArtin M) : HasPositiveHead M a := by
  induction a using (measure (positiveDegree M)).wf.induction with
  | h a ih=>
    by_cases ha:a=1
    · subst a
      refine ⟨1,by rw [positiveSimpleLift_one];exact positivePrefix_refl M 1,?_⟩
      intro w hw
      rw [positiveSimpleLift_one]
      exact hw
    obtain ⟨l,hl⟩:=positive_word_surjective M a
    cases l with
    | nil=>exact (ha hl.symm).elim
    | cons s ls=>
      have hs:PositivePrefix M (positiveGenerator M s) a:=by rw [←hl];exact positivePrefix_first M s ls
      obtain ⟨h,hh⟩:=exists_front_head M cancel z hz a (fun b hb=>ih b hb) s hs
      refine ⟨h,hh.1,?_⟩
      intro w hwa
      by_cases hw:w=1
      · subst w
        rw [positiveSimpleLift_one]
        exact positivePrefix_one M _
      obtain ⟨t,ht⟩:=exists_simple_prefix M.toCoxeterSystem hw
      have htw:PositivePrefix M (positiveGenerator M t) (positiveSimpleLift M w):=by
        simpa only [positiveSimpleLift_simple] using (positivePrefix_simple_iff M _ _).mpr ht
      have hta:=positivePrefix_trans M htw hwa
      have hlink:=positive_first_letters_connected M z hz a s t hs hta
      have hfront:IsFrontHead M a t h:=by
        clear ht htw hta
        induction hlink with
        | refl=>exact hh
        | @tail t u chain link hi=>
          obtain ⟨d,hda,htd,hud⟩:=link
          obtain ⟨k,hk⟩:=exists_front_head M cancel z hz a (fun b hb=>ih b hb) u
            (positivePrefix_trans M hud hda)
          have hdk:=hk.2.2 d hda hud
          have htk:=positivePrefix_trans M htd hdk
          have hkh:=hi.2.2 k hk.1 htk
          refine ⟨hi.1,positivePrefix_trans M hk.2.1 hkh,?_⟩
          intro v hva huv
          exact positivePrefix_trans M (hk.2.2 v hva huv) hkh
      exact hfront.2.2 w hwa htw

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_PositiveDescentSet
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type*} [Fintype S] (M:CoxeterMatrix S)
variable (z:M.Group) (hz:∀w,M.toCoxeterSystem.length w≤M.toCoxeterSystem.length z)

include z hz in

theorem positive_descent_fundamental
    (cancel:∀a b c:PositiveArtin M,a*b=a*c→b=c) (a:PositiveArtin M) :
    IsSpherical M (PositiveDescentSet M a) ∧
      ∃q:M.Group,IsParabolicLongest M (PositiveDescentSet M a) q ∧
        PositiveSuffix M (positiveSimpleLift M q) a := by
  obtain ⟨h,hha,hh⟩:=positive_greedy_head M cancel z hz (positiveReverse M z hz a)
  have hD:∀s∈PositiveDescentSet M a,
      M.toCoxeterSystem.length (M.toCoxeterSystem.simple s*h)<M.toCoxeterSystem.length h:=by
    intro s hs
    have hs':PositivePrefix M (positiveSimpleLift M (M.toCoxeterSystem.simple s)) (positiveReverse M z hz a):=by
      have ht:=(positiveReverse_prefix_iff M z hz (positiveGenerator M s) a).mpr hs
      simpa only [positiveReverse_generator,positiveSimpleLift_simple] using ht
    have hp:=(positivePrefix_simple_iff M _ _).mp (hh _ hs')
    have hl:=(weakPrefix_simple_iff M.toCoxeterSystem s h).mp hp
    omega
  refine ⟨spherical_of_left_descents M _ h hD,?_⟩
  obtain ⟨q,hq,hpref⟩:=positive_longest_descent_prefix M _ h hD
  let Q:=restrictionHom M (PositiveDescentSet M a) q
  have hQ:IsParabolicLongest M (PositiveDescentSet M a) Q:=by
    refine ⟨Geometric.restrictionHom_mem_parabolic M _ q,?_⟩
    intro r hr
    have hm:r∈(restrictionHom M (PositiveDescentSet M a)).range:=by rw [restrictionHom_range_eq];exact hr
    obtain ⟨w,rfl⟩:=hm
    simpa only [Q,restriction_length] using hq w
  refine ⟨Q,hQ,?_⟩
  apply (positiveReverse_prefix_iff M z hz _ _).mp
  rw [positiveReverse_simpleLift,parabolic_longest_inverse M _ Q hQ]
  exact positivePrefix_trans M hpref hha

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_NoncriticalPositiveCell
attribute [-instance] _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type*} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)
variable (z:M.Group) (hz:∀w,M.toCoxeterSystem.length w≤M.toCoxeterSystem.length z)
variable (inj:Function.Injective (positiveToArtin M))

include z hz inj in
omit [LinearOrder S] in
theorem positiveCell_realize_top (b:PositiveArtin M) (T:SphericalType M)
    (hT:T.val⊆PositiveDescentSet M b) :
    ∃a:PositiveLiftedCell M,a.2=T ∧ positiveCellTop M a=b := by
  have cancel:∀a d e:PositiveArtin M,a*d=a*e→d=e:=by
    intro a d e h
    apply inj
    exact mul_left_cancel (by simpa only [map_mul] using congrArg (positiveToArtin M) h)
  obtain ⟨hD,q,hq,p,hp⟩:=positive_descent_fundamental M z hz cancel b
  let r:=q*(sphericalLongest M T)⁻¹
  have hm:(sphericalLongest M T)⁻¹∈coxeterParabolic M (PositiveDescentSet M b):=
    coxeterParabolic_mono M hT ((coxeterParabolic M T.val).inv_mem (sphericalLongest_spec M T).1)
  have hl:=parabolic_longest_length_mul M _ q hq (sphericalLongest M T)⁻¹ hm
  rw [M.toCoxeterSystem.length_inv] at hl
  have he:r*sphericalLongest M T=q:=by dsimp [r];group
  have hl':M.toCoxeterSystem.length (r*sphericalLongest M T)=
      M.toCoxeterSystem.length r+M.toCoxeterSystem.length (sphericalLongest M T):=by rw [he];exact hl.symm
  have hprod:=positiveSimpleLift_mul M r (sphericalLongest M T) hl'
  rw [he] at hprod
  refine ⟨(p*positiveSimpleLift M r,T),rfl,?_⟩
  change (p*positiveSimpleLift M r)*positiveSimpleLift M (sphericalLongest M T)=b
  rw [hp,hprod,mul_assoc]

lemma matchingOtherType_subset (a:NoncriticalPositiveCell M) :
    matchingOtherType M z hz a⊆PositiveDescentSet M (positiveCellTop M a.val) := by
  have hT:a.val.2.val⊆PositiveDescentSet M (positiveCellTop M a.val):=
    type_subset_positiveDescentSet M _ _ (sphericalLongest_spec M a.val.2) a.val.1
  have hs:matchingLetter M z hz a∈PositiveDescentSet M (positiveCellTop M a.val):=
    firstPositiveDescent_mem M z hz _ _
  unfold matchingOtherType
  split_ifs
  · exact Set.Subset.trans Set.sdiff_subset hT
  · exact Set.insert_subset hs hT

include inj in
lemma matchingOtherType_spherical (a:NoncriticalPositiveCell M) :
    IsSpherical M (matchingOtherType M z hz a) := by
  have cancel:∀a d e:PositiveArtin M,a*d=a*e→d=e:=by
    intro a d e h
    apply inj
    exact mul_left_cancel (by simpa only [map_mul] using congrArg (positiveToArtin M) h)
  exact spherical_type_mono M (matchingOtherType_subset M z hz a)
    (positive_descent_fundamental M z hz cancel (positiveCellTop M a.val)).1

noncomputable def positiveMatch (a:NoncriticalPositiveCell M) : NoncriticalPositiveCell M :=
  let T:SphericalType M:=⟨matchingOtherType M z hz a,matchingOtherType_spherical M z hz inj a⟩
  let h:=positiveCell_realize_top M z hz inj (positiveCellTop M a.val) T (matchingOtherType_subset M z hz a)
  ⟨h.choose,fun he=>a.property (h.choose_spec.2.symm.trans he)⟩

lemma positiveMatch_top (a:NoncriticalPositiveCell M) :
    positiveCellTop M (positiveMatch M z hz inj a).val=positiveCellTop M a.val := by
  exact (positiveCell_realize_top M z hz inj (positiveCellTop M a.val)
    ⟨matchingOtherType M z hz a,matchingOtherType_spherical M z hz inj a⟩
    (matchingOtherType_subset M z hz a)).choose_spec.2

lemma positiveMatch_type (a:NoncriticalPositiveCell M) :
    (positiveMatch M z hz inj a).val.2.val=matchingOtherType M z hz a := by
  exact congrArg Subtype.val (positiveCell_realize_top M z hz inj (positiveCellTop M a.val)
    ⟨matchingOtherType M z hz a,matchingOtherType_spherical M z hz inj a⟩
    (matchingOtherType_subset M z hz a)).choose_spec.1

lemma positiveMatch_letter (a:NoncriticalPositiveCell M) :
    matchingLetter M z hz (positiveMatch M z hz inj a)=matchingLetter M z hz a := by
  simp only [matchingLetter,positiveMatch_top]

theorem positiveMatch_involutive : Function.Involutive (positiveMatch M z hz inj) := by
  intro a
  apply Subtype.ext
  apply positiveCell_same_top_type_unique M inj
  · apply Subtype.ext
    rw [positiveMatch_type]
    simp only [matchingOtherType,positiveMatch_letter,positiveMatch_type]
    by_cases hs:matchingLetter M z hz a∈a.val.2.val
    · simp only [hs,ite_eq_left,Set.mem_sdiff,Set.mem_singleton_iff,not_true_eq_false,and_false,ite_false, if_false]
      rw [Set.insert_sdiff_singleton, Set.insert_eq_of_mem hs]
    · simp only [hs,ite_false, if_false,Set.mem_insert_iff,true_or,ite_eq_left]
      ext x
      by_cases he : x = matchingLetter M z hz a
      · subst x
        simp [hs]
      · simp [he]
  · exact (positiveMatch_top M z hz inj (positiveMatch M z hz inj a)).trans (positiveMatch_top M z hz inj a)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_PositiveCellPoset2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type*} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S)
variable (z : M.Group) (hz : ∀ w, M.toCoxeterSystem.length w ≤ M.toCoxeterSystem.length z)
variable (inj : Function.Injective (positiveToArtin M))

lemma positive_lt_orientation (a b : PositiveCellPoset M inj) (hab : a < b) :
    PositiveEarlier M z hz inj a b ∨
      ∃ ha : positiveCellTop M a ≠ 1,
        matchingLetter M z hz ⟨a,ha⟩ ∉ a.2.val ∧
        (positiveMatch M z hz inj ⟨a,ha⟩).val = b ∧
        PositiveEarlier M z hz inj b a := by
  by_cases he : positiveCellTop M a = positiveCellTop M b
  · have ha : positiveCellTop M a ≠ 1 := by
      intro h
      have ha' := (positiveCellTop_eq_one_iff M a).mp h
      have hb' := (positiveCellTop_eq_one_iff M b).mp (he.symm.trans h)
      exact hab.ne (ha'.trans hb'.symm)
    have hb : positiveCellTop M b ≠ 1 := fun h => ha (he.trans h)
    let s := matchingLetter M z hz ⟨a,ha⟩
    have ht : a.2.val.toFinset ⊂ b.2.val.toFinset := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨?_,?_⟩
      · intro t ht
        exact Set.mem_toFinset.mpr ((lifted_lt_type M hab).subset (Set.mem_toFinset.mp ht))
      · intro heq
        have htype : a.2.val = b.2.val := by
          ext t
          simpa only [Set.mem_toFinset] using (congrArg (fun F : Finset S => t ∈ F) heq).to_iff
        exact hab.ne (positiveCellToLifted_injective M inj
          (lifted_eq_of_le_type_eq M hab.le htype))
    have hkA : positiveMatchingTypeKey M z hz a = topBlockMatchingKey s a.2.val.toFinset := by
      simp only [positiveMatchingTypeKey,dite_eq_right ha,s,matchingLetter]
    have hkB : positiveMatchingTypeKey M z hz b = topBlockMatchingKey s b.2.val.toFinset := by
      simp only [positiveMatchingTypeKey,dite_eq_right hb,s,matchingLetter,he]
    rcases topBlockMatchingKey_cases (s:=s) ht with hkey | ⟨hs,hT,hkey⟩
    · exact Or.inl (positiveEarlier_of_key_lt M z hz inj a b he (by rwa [hkA,hkB]))
    · have hs' : s ∉ a.2.val := fun h => hs (Set.mem_toFinset.mpr h)
      have hmatch : (positiveMatch M z hz inj ⟨a,ha⟩).val = b := by
        apply positiveCell_same_top_type_unique M inj
        · apply Subtype.ext
          rw [positiveMatch_type,matchingOtherType,ite_eq_right hs']
          ext t
          have hh := congrArg (fun F : Finset S => t ∈ F) hT
          simpa only [Finset.mem_insert,Set.mem_toFinset,Set.mem_insert_iff] using hh.symm.to_iff
        · exact (positiveMatch_top M z hz inj ⟨a,ha⟩).trans he
      exact Or.inr ⟨ha,hs',hmatch,
        positiveEarlier_of_key_lt M z hz inj b a he.symm (by rwa [hkA,hkB])⟩
  · exact Or.inl (positiveEarlier_of_top_lt M z hz inj a b
      (positiveCellTop_degree_strict M inj a b hab.le he))

lemma positiveMatch_before (a : NoncriticalPositiveCell M)
    (hs : matchingLetter M z hz a ∉ a.val.2.val) :
    PositiveEarlier M z hz inj (positiveMatch M z hz inj a).val a.val := by
  apply positiveEarlier_of_key_lt M z hz inj _ _ (positiveMatch_top M z hz inj a)
  simp only [positiveMatchingTypeKey,dite_eq_right a.property,positiveMatch_top]
  apply topBlockStep_key (Or.inl ⟨?_,?_⟩)
  · exact fun h => hs (Set.mem_toFinset.mp h)
  · ext t
    simp only [Set.mem_toFinset,Finset.mem_insert]
    rw [positiveMatch_type,matchingOtherType,ite_eq_right hs]
    rfl

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_PositiveEarlierLinkUpper
attribute [-instance] _root_.OAI.HarmonicArtin.instPartialOrderLiftedPuncturedBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type*} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S)
variable (z : M.Group) (hz : ∀ w, M.toCoxeterSystem.length w ≤ M.toCoxeterSystem.length z)
variable (inj : Function.Injective (positiveToArtin M))

lemma positiveMatch_lower_before (a : NoncriticalPositiveCell M)
    (hs : matchingLetter M z hz a ∈ a.val.2.val) :
    PositiveEarlier M z hz inj a.val (positiveMatch M z hz inj a).val := by
  have hs' : matchingLetter M z hz (positiveMatch M z hz inj a) ∉
      (positiveMatch M z hz inj a).val.2.val := by
    rw [positiveMatch_letter,positiveMatch_type,matchingOtherType,ite_eq_left hs]
    simp only [Set.mem_sdiff,Set.mem_singleton_iff,not_true_eq_false,and_false,not_false_eq_true]
  have h := positiveMatch_before M z hz inj (positiveMatch M z hz inj a) hs'
  rw [positiveMatch_involutive M z hz inj a] at h
  exact h

lemma positiveMatch_symm_value (a b : NoncriticalPositiveCell M)
    (h : (positiveMatch M z hz inj a).val = b.val) :
    (positiveMatch M z hz inj b).val = a.val := by
  have he : positiveMatch M z hz inj a = b := Subtype.ext h
  have he' := congrArg (positiveMatch M z hz inj) he
  rw [positiveMatch_involutive] at he'
  exact (congrArg Subtype.val he').symm

lemma positiveEarlier_upper_eq (a b : PositiveCellPoset M inj) (hab : a < b)
    (hba : PositiveEarlier M z hz inj b a) :
    ∃ ha : positiveCellTop M a ≠ 1,
      matchingLetter M z hz ⟨a,ha⟩ ∉ a.2.val ∧
      (positiveMatch M z hz inj ⟨a,ha⟩).val = b := by
  rcases positive_lt_orientation M z hz inj a b hab with h|⟨ha,hs,hm,_⟩
  · exact (positiveEarlier_asymm M z hz inj h hba).elim
  · exact ⟨ha,hs,hm⟩

lemma positiveEarlierLink_upper_iff (a : NoncriticalPositiveCell M)
    (hs : matchingLetter M z hz a ∈ a.val.2.val) (x : PositiveCellPoset M inj) :
    (PositiveEarlier M z hz inj x a.val ∧ (positiveCellToLifted M x ≤ positiveCellToLifted M a.val ∨
      positiveCellToLifted M a.val ≤ positiveCellToLifted M x)) ↔
      positiveCellToLifted M x < positiveCellToLifted M a.val ∧ x ≠ (positiveMatch M z hz inj a).val := by
  constructor
  · rintro ⟨hr,hcomp⟩
    have hne : x ≠ a.val := by
      intro he
      rw [he] at hr
      exact (positiveEarlier_wf M z hz inj).irrefl.irrefl _ hr
    have hlt : positiveCellToLifted M x < positiveCellToLifted M a.val := by
      rcases hcomp with h|h
      · exact lt_of_le_of_ne h (fun he => hne (positiveCellToLifted_injective M inj he))
      · obtain ⟨_,hh,_⟩ := positiveEarlier_upper_eq M z hz inj a.val x
          (lt_of_le_of_ne h hne.symm) hr
        exact (hh hs).elim
    refine ⟨hlt,?_⟩
    intro he
    rw [he] at hr
    exact positiveEarlier_asymm M z hz inj (positiveMatch_lower_before M z hz inj a hs) hr
  · rintro ⟨hlt,hne⟩
    refine ⟨?_,Or.inl hlt.le⟩
    rcases positive_lt_orientation M z hz inj x a.val hlt with h|⟨hx,_,hm,_⟩
    · exact h
    · have he := positiveMatch_symm_value M z hz inj ⟨x,hx⟩ a hm
      exact (hne he.symm).elim

noncomputable def positiveEarlierLink_upper_iso (a : NoncriticalPositiveCell M)
    (hs : matchingLetter M z hz a ∈ a.val.2.val) :
    WeightEarlierLink (PositiveEarlier M z hz inj) a.val ≃o
      {x : PositiveCellPoset M inj // positiveCellToLifted M x < positiveCellToLifted M a.val ∧
        x ≠ (positiveMatch M z hz inj a).val} where
  toFun x := ⟨x.val,(positiveEarlierLink_upper_iff M z hz inj a hs x.val).mp x.property⟩
  invFun x := ⟨x.val,(positiveEarlierLink_upper_iff M z hz inj a hs x.val).mpr x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := by intros; rfl

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_PositiveFullCell
attribute [-instance] _root_.OAI.HarmonicArtin.instPartialOrderLiftedPuncturedBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type*} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S)
variable (z : M.Group) (hz : ∀ w, M.toCoxeterSystem.length w ≤ M.toCoxeterSystem.length z)
variable (inj : Function.Injective (positiveToArtin M))

variable [Finite M.Group]

noncomputable def positiveFullCell : PositiveLiftedCell M := (1,(fullSphericalCell M).2)

omit [Fintype S] [LinearOrder S] in
lemma positiveFullCell_lifted : positiveCellToLifted M (positiveFullCell M) = fullSphericalCell M := by
  exact Prod.ext (map_one (positiveToArtin M)) rfl

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_PositiveUpperBoundaryRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S)
variable (z : M.Group) (hz : ∀ w, M.toCoxeterSystem.length w ≤ M.toCoxeterSystem.length z)
variable (inj : Function.Injective (positiveToArtin M))

lemma matchingLetter_le_type (a : NoncriticalPositiveCell M) (t : S) (ht : t ∈ a.val.2.val) :
    matchingLetter M z hz a ≤ t :=
  firstPositiveDescent_le M z hz _ _
    (type_subset_positiveDescentSet M _ _ (sphericalLongest_spec M a.val.2) a.val.1 ht)

variable (a : NoncriticalPositiveCell M) (hs : matchingLetter M z hz a ∈ a.val.2.val)
variable [Finite (restrictedMatrix M a.val.2.val).Group]
variable (q : (restrictedMatrix M a.val.2.val).Group)
variable (hq : ∀ w, (restrictedMatrix M a.val.2.val).toCoxeterSystem.length w ≤
  (restrictedMatrix M a.val.2.val).toCoxeterSystem.length q)
variable (inj' : Function.Injective (positiveToArtin (restrictedMatrix M a.val.2.val)))
variable (hc : positiveCellTop (restrictedMatrix M a.val.2.val)
  (positiveFullCell (restrictedMatrix M a.val.2.val)) ≠ 1)

include hs in
lemma restrictedFullMatchingLetter :
    (matchingLetter (restrictedMatrix M a.val.2.val) q hq
      ⟨positiveFullCell (restrictedMatrix M a.val.2.val),hc⟩).val = matchingLetter M z hz a := by
  let t := matchingLetter (restrictedMatrix M a.val.2.val) q hq
      ⟨positiveFullCell (restrictedMatrix M a.val.2.val),hc⟩
  apply le_antisymm
  · exact matchingLetter_le_type (restrictedMatrix M a.val.2.val) q hq
      ⟨positiveFullCell (restrictedMatrix M a.val.2.val),hc⟩ ⟨matchingLetter M z hz a,hs⟩ (Set.mem_univ _)
  · exact matchingLetter_le_type M z hz a t.val t.property

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_SphericalTypeReindex
attribute [-instance] _root_.OAI.HarmonicArtin.instPartialOrderLiftedPuncturedBoundary _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
attribute [-simp] _root_.OAI.HarmonicArtin.positiveToArtin_generator _root_.OAI.HarmonicArtin.positiveToArtin_word _root_.OAI.HarmonicArtin.positiveToCoxeter_word
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CoxeterExchange

attribute [local instance] Classical.decEq Classical.propDecidable
universe u v
variable {S : Type u} {T : Type v} (M : CoxeterMatrix S) (e : S ≃ T)

lemma wordArtin_reindex (w : List S) :
    wordArtin (M.reindex e) (w.map e) = artinReindex M e (wordArtin M w) := by
  induction w with
  | nil => simp [wordArtin]
  | cons s w ih =>
    simpa only [wordArtin,List.map_cons,List.prod_cons,map_mul,artinReindex_generator]
      using congrArg (generator (M.reindex e) (e s) * ·) ih

noncomputable def sphericalTypeReindex : SphericalType M ≃ SphericalType (M.reindex e) where
  toFun A := ⟨e '' A.val,(spherical_reindex M e A.val).mpr A.property⟩
  invFun B := ⟨e ⁻¹' B.val,(spherical_reindex M e (e ⁻¹' B.val)).mp (by
    simpa only [Set.image_preimage_eq _ e.surjective] using B.property)⟩
  left_inv A := by apply Subtype.ext; exact Set.preimage_image_eq _ e.injective
  right_inv B := by apply Subtype.ext; exact Set.image_preimage_eq _ e.surjective

noncomputable def liftedReindexEquiv : LiftedCell M ≃ LiftedCell (M.reindex e) :=
  (artinReindex M e).toEquiv.prodCongr (sphericalTypeReindex M e)

lemma liftedFace_reindex_iff (a b : LiftedCell M) :
    LiftedFace (M.reindex e) (liftedReindexEquiv M e a) (liftedReindexEquiv M e b) ↔
      LiftedFace M a b := by
  change ((e '' a.2.val ⊆ e '' b.2.val) ∧ ∃ w : List T,
    (∀ s ∈ w, s ∈ e '' b.2.val) ∧
    (M.reindex e).toCoxeterSystem.length (wordCoxeter (M.reindex e) w) = w.length ∧
    (∀ v : coxeterParabolic (M.reindex e) (e '' a.2.val),
      (M.reindex e).toCoxeterSystem.length (wordCoxeter (M.reindex e) w) ≤
      (M.reindex e).toCoxeterSystem.length (wordCoxeter (M.reindex e) w * v.val)) ∧
    artinReindex M e a.1 = artinReindex M e b.1 * wordArtin (M.reindex e) w) ↔ _
  rw [Set.image_subset_image_iff e.injective]
  constructor
  · rintro ⟨ht,w,hw,hr,hm,he⟩
    let q := w.map e.symm
    have hq : q.map e = w := by simp [q,List.map_map]
    rw [←hq,reindex_letters] at hw
    rw [←hq,wordCoxeter_reindex,coxeter_length_reindex,List.length_map] at hr
    rw [←hq,wordCoxeter_reindex,minimal_reindex] at hm
    rw [←hq,wordArtin_reindex,←map_mul] at he
    exact ⟨ht,q,hw,hr,hm,(artinReindex M e).injective he⟩
  · rintro ⟨ht,w,hw,hr,hm,he⟩
    refine ⟨ht,w.map e,(reindex_letters e b.2.val w).mpr hw,?_,?_,?_⟩
    · simpa only [wordCoxeter_reindex,coxeter_length_reindex,List.length_map] using hr
    · rw [wordCoxeter_reindex,minimal_reindex]
      exact hm
    · simpa only [wordArtin_reindex,←map_mul] using congrArg (artinReindex M e) he

noncomputable def liftedReindex : LiftedCell M ≃o LiftedCell (M.reindex e) where
  toEquiv := liftedReindexEquiv M e
  map_rel_iff' := by
    intro a b
    rw [lifted_le_iff_face,lifted_le_iff_face]
    exact liftedFace_reindex_iff M e a b

end HarmonicArtin

end OAI
end


