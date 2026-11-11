-- Prove2me | Definitions.Def_OAIQ225Ag009
-- name    : OAIQ225Ag009
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T17:29:53.766229+00:00
-- url     : https://prove2.me/theorems/0fc61277-fa4b-457d-8f4c-7ecbd496e3a3
-- title:
--   Definitions bundle OAIQ225Ag009 of the split of OpenAI, Harmonic heights and the Artin K(pi,1) conjecture
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.HarmonicArtin.salvetti_cover_contractible`, carved from OpenAI's openai/math development (OpenAI, *Harmonic heights and the Artin K(pi,1) conjecture*, OpenAI Math Release, September 23, 2026, result family 254, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 135 declarations of OpenAI's Lean: 40 definitions, 1 inductive type or structure, 1 instance and 93 theorems. The definitions and types are `OAI.HarmonicArtin.IsolatedIterationData`, `OAI.HarmonicArtin.IsolatedIterationData.capped`, `OAI.HarmonicArtin.IsolatedIterationData.fullRegion`, `OAI.HarmonicArtin.IsolatedIterationData.openSocle`, `OAI.HarmonicArtin.IsolatedIterationData.operated`, `OAI.HarmonicArtin.IsolatedIterationData.region`, `OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.layerComparison`, `OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.layerIndexEquiv`, `OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.levelGeneratorEquiv`, `OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.packetTwistComparison`, `OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.signedPacketPerm`, `OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.wordPacketPerm`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.ChainIsomorphism.cone`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.ClassBottomSocleZero`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.HomotopyEquivalence.lowerTruncation`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.HomotopyEquivalence.pureLayer`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.Map.lowerTruncation`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.Map.pureLayer`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.Map.reindexConeIsomorphism`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.adjacent_positiveTwists`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidSecondPivot`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistReduction`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.classLayerSocleDimension`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.classLowerTruncation`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.colorRestriction`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.lowerTruncation`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.minimalClassModelEquivalence`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.reducedBraidTwist`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.sumLayerEquiv`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.sumTruncationEquiv`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.sumTwistEquiv`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.tokenTest`, `OAI.HarmonicArtin.ReversibleQuiver.fixedOrientation`, `OAI.HarmonicArtin.fusionArrowJoin`, `OAI.HarmonicArtin.fusionArrowSplit`, `OAI.HarmonicArtin.fusionOrbitColorLayer`, `OAI.HarmonicArtin.fusionOrbitLayer`, `OAI.HarmonicArtin.fusionOrbitMultiplicity`, `OAI.HarmonicArtin.fusionOrbitWeightedVector`, `OAI.HarmonicArtin.fusionQuiverSplit` and 1 more.
--
--   **Sources.** They come from these modules of lean/OAI/Topology, in whole or in part: `ArtinGroups_Complexes_ActedIndex`, `ArtinGroups_Complexes_BottomSocleZero`, `ArtinGroups_Complexes_ColorBoundary`, `ArtinGroups_Complexes_DownClosed`, `ArtinGroups_Complexes_FiniteHomotopySetoid`, `ArtinGroups_Complexes_FiniteSum2`, `ArtinGroups_Complexes_GeneratorArray2`, `ArtinGroups_Complexes_GeneratorVectorPureLayer`, `ArtinGroups_Complexes_HomDimension`, `ArtinGroups_Complexes_HomDimension2`, `ArtinGroups_Complexes_InverseHomMatrix`, `ArtinGroups_Complexes_LevelArrayComplexMinimal`, `ArtinGroups_Complexes_LowMatrix`, `ArtinGroups_Complexes_LowerTruncation`, `ArtinGroups_Complexes_MinimalModelEquivalence`, `ArtinGroups_Complexes_NegativeAmplitudeCoreIndex`, `ArtinGroups_Complexes_NegativeHomTransformReflect`, `ArtinGroups_Complexes_OptionSumEquiv`, `ArtinGroups_Complexes_PacketPermEnumeration`, `ArtinGroups_Complexes_PacketPermReindex`, `ArtinGroups_Complexes_Refl`, `ArtinGroups_Complexes_ReindexConeIsomorphism`, `ArtinGroups_Complexes_Sum`, `ArtinGroups_Complexes_SumTestEquiv`, `ArtinGroups_Complexes_SumTruncationEquiv`, `ArtinGroups_Complexes_UnfoldedCartanSymm`, `ArtinGroups_Coxeter_AlternatingLiftProd`, `ArtinGroups_Coxeter_BraidCoreFirstTarget`, `ArtinGroups_Coxeter_BraidCorePlacement`, `ArtinGroups_Coxeter_BraidSecondPivot`, `ArtinGroups_Coxeter_OrdinaryTwistBraid`, `ArtinGroups_Functors_ColorPacketPerm`, `ArtinGroups_Functors_ComplexLowerTruncation`, `ArtinGroups_Functors_ComplexPureLayer`, `ArtinGroups_Functors_HomDimensionFlexible`, `ArtinGroups_Functors_Index`, `ArtinGroups_Functors_LayerIndexEquiv`, `ArtinGroups_Functors_LevelGeneratorEquiv`, `ArtinGroups_Functors_PacketSwitchMatrix`, `ArtinGroups_Functors_PacketTwistComparison`, `ArtinGroups_Functors_ReversibleQuiverMap`, `ArtinGroups_Functors_SignedPacketPerm`, `ArtinGroups_Functors_TwistProdGeneratorExterior`, `ArtinGroups_Functors_WordOrbitCountAdjacency`, `ArtinGroups_Functors_WordPacketPermAppend`, `ArtinGroups_Harmonic_ArtinAction`, `ArtinGroups_Harmonic_DimensionPosMultiplicityPos`, `ArtinGroups_Harmonic_FusionColorRegion`, `ArtinGroups_Harmonic_FusionExpandedWordAction`, `ArtinGroups_Harmonic_FusionExpandedWordPerm`, `ArtinGroups_Harmonic_FusionFactorStep`, `ArtinGroups_Harmonic_FusionOrbitModel`, `ArtinGroups_Harmonic_FusionOrbitMultiplicity`, `ArtinGroups_Harmonic_FusionPacketOrbit`, `ArtinGroups_Harmonic_FusionPacketPerm`, `ArtinGroups_Harmonic_IsolatedBoundaryAbsent`, `ArtinGroups_Harmonic_IsolatedIterationData`, `ArtinGroups_Harmonic_SphericalPacketWordProperty`, `ArtinGroups_Harmonic_StringAdjacent`, `ArtinGroups_Quivers_Level`, `ArtinGroups_Quivers_VertexLinear`.
--
--   **Imports.** It imports the published bundle `Def_HarmonicArtin`; the bundles `OAIQ225Ag005` and `OAIQ225Ag006` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ225Ag011` and `OAIQ225Ag012`; the statements `OAI.HarmonicArtin.IsolatedIterationData.separation` and `OAI.HarmonicArtin.IsolatedIterationData.stage_move`.
-- source:
--   OpenAI, Harmonic heights and the Artin K(pi,1) conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 254; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Harmonic-heights-and-the-Artin-K-pi-1-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Topology at commit adc7f12

import Mathlib
import Definitions.Def_HarmonicArtin
import Definitions.Def_OAIQ225Ag005
import Definitions.Def_OAIQ225Ag006

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_ActedIndex
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

variable {V A K I : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I]

noncomputable instance amplitudeCoreDecidable (E : BasedComplex Q (K := K) I) (α : V) :
    DecidableEq (AmplitudeCoreIndex Q E α) := fun a b => instDecidableEqSum a b

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Quivers_Level
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.instAlgebra
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_InverseHomMatrix
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_NegativeHomTransformReflect
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

variable {V A K I J : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_HomDimension
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Quivers_VertexLinear
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype A] [DecidableEq V]
variable {I J L : Type*}

lemma vertex_sum {T : Type*} (s : Finset T) (f : T → Q.Zigzag K) :
    (∑ t ∈ s, f t).vertex = ∑ t ∈ s, (f t).vertex :=
  map_sum (vertexLinear Q) f s

end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Coxeter_BraidCoreFirstTarget
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

variable {V A K I : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
lemma braidSecondSource_to_secondTarget (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) {α β : V} (e : SimpleEdge Q α β)
    (u v : TestIndex Q E.placement α) :
    (normalizedBraidTwist Q hn E e).differential
      (.inr (.inr (.inl u))) (.inr (.inr (.inr (.inl v)))) =
      -projectiveIdentity Q (testPlacement Q E.placement α) u v := by
  simp only [normalizedBraidTwist, reindex, Matrix.submatrix_apply,
    braidTwistIndexEquiv, Equiv.coe_fn_mk, positiveTwist_differential,
    Matrix.fromBlocks, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr,
    Matrix.neg_apply, testTransform, scalarCornerMatrix, testMatrix,
    evaluationMatrix, SimpleEdge.corner_val, pathBasis_arrow,
    selfCornerEquiv_true, Sum.inl.injEq, projectiveIdentity, Matrix.diagonal_apply,
    testPlacement, SimpleEdge.reverse_arrow]
  by_cases h : u = v
  · simp only [ite_eq_left h, arrowBasis_reverse, e.source]
    rw [← pathBasis_token, pathBasis_coordinates, ite_eq_left rfl, one_smul]
  · simp only [ite_eq_right h, MulZeroClass.mul_zero, coordinates_zero, zero_smul, neg_zero]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Coxeter_BraidSecondPivot
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

variable {V A K I : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I]

noncomputable def braidSecondPivot (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) {α β : V} (e : SimpleEdge Q α β) :
    BlockPivot Q ((braidFirstPivot Q hn E e).reduced Q) where
  coefficient := -1
  nonzero := neg_ne_zero.mpr one_ne_zero
  color _ := rfl
  cochain u := by
    change (E.placement u.1).cochain - 1 - 1 =
      (E.placement u.1).cochain - 1 - 1 - 1 + 1
    omega
  internal u := by
    change (E.placement u.1).internal + Path.length u.2.val + 2 =
      (E.placement u.1).internal + Path.length u.2.val + 1 + 1
    omega
  entry u v := by
    rw [BlockPivot.reduced_differential]
    simp only [braidSecondSource_to_secondTarget, braidSecondSource_to_firstTarget,
      smul_zero, MulZeroClass.zero_mul, Finset.sum_const_zero, sub_zero, neg_one_smul]
    rfl

noncomputable def reducedBraidTwist (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) {α β : V} (e : SimpleEdge Q α β) :
    BasedComplex Q (K := K) (BraidCoreIndex Q E α β) :=
  (braidSecondPivot Q hn E e).reduced Q

lemma reducedBraidTwist_differential (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) {α β : V} (e : SimpleEdge Q α β) :
    (reducedBraidTwist Q hn E e).differential = braidCoreDifferential Q E e := by
  apply Matrix.ext
  intro i j
  change ((braidSecondPivot Q hn E e).reduced Q).differential i j = _
  rw [BlockPivot.reduced_differential, braidFirstReduction_core]
  simp only [braidFirstReduction_core_to_secondTarget, smul_zero,
    MulZeroClass.zero_mul, Finset.sum_const_zero, sub_zero]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Coxeter_BraidCorePlacement
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

variable {V A K I : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
lemma reducedBraidTwist_placement (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) {α β : V} (e : SimpleEdge Q α β) :
    (reducedBraidTwist Q hn E e).placement = braidCorePlacement Q E α β := by
  funext i
  rcases i with u | u | u | u | i
  · change (⟨α, (E.placement u.1).cochain - 1 - 1,
      (E.placement u.1).internal + Path.length u.2.val + 1⟩ : GeneratorPlacement V) = _
    congr 1
    omega
  · change (⟨β, (E.placement u.1).cochain - 1 - 1,
      (E.placement u.1).internal + Path.length u.2.val + 1⟩ : GeneratorPlacement V) = _
    congr 1
    omega
  · rfl
  · rfl
  · rfl

lemma reducedBraidTwist_swap (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) {α β : V} (e : SimpleEdge Q α β) :
    (reducedBraidTwist Q hn E (e.reverse Q)).reindex Q (braidCoreSwap Q E α β) =
      reducedBraidTwist Q hn E e := by
  apply ext_placement_differential Q
  · change (reducedBraidTwist Q hn E (e.reverse Q)).placement ∘ _ = _
    rw [reducedBraidTwist_placement, reducedBraidTwist_placement]
    funext i
    rcases i with u | u | u | u | i <;> rfl
  · change (reducedBraidTwist Q hn E (e.reverse Q)).differential.submatrix _ _ = _
    rw [reducedBraidTwist_differential, reducedBraidTwist_differential]
    apply Matrix.ext
    intro i j
    rcases i with u | u | u | u | i <;> rcases j with v | v | v | v | j
    all_goals simp only [Matrix.submatrix_apply, braidCoreSwap, Equiv.coe_fn_mk,
      braidCoreDifferential, SimpleEdge.reverse_reverse]

noncomputable def braidTwistReduction (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) {α β : V} (e : SimpleEdge Q α β) :
    HomotopyEquivalence Q (((E.positiveTwist Q α).positiveTwist Q β).positiveTwist Q α)
      (reducedBraidTwist Q hn E e) := by
  classical
  letI : DecidableEq (TestIndex Q E.placement α ⊕ TestIndex Q E.placement α ⊕
      BraidCoreIndex Q E α β) := braidFirstReducedDecidable Q E α β
  let f := (((E.positiveTwist Q α).positiveTwist Q β).positiveTwist Q α).reindexHomotopyEquivalence Q
    (braidTwistIndexEquiv Q hn E e)
  let g := (braidFirstPivot Q hn E e).reductionEquivalence Q
  let h := (braidSecondPivot Q hn E e).reductionEquivalence Q
  exact (f.trans Q g).trans Q h

noncomputable def adjacent_positiveTwists (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) {α β : V} (e : SimpleEdge Q α β) :
    HomotopyEquivalence Q (((E.positiveTwist Q α).positiveTwist Q β).positiveTwist Q α)
      (((E.positiveTwist Q β).positiveTwist Q α).positiveTwist Q β) := by
  classical
  let f := braidTwistReduction Q hn E e
  let g := braidTwistReduction Q hn E (e.reverse Q)
  let k := (reducedBraidTwist Q hn E (e.reverse Q)).reindexHomotopyEquivalence Q
    (braidCoreSwap Q E α β)
  have k' : HomotopyEquivalence Q (reducedBraidTwist Q hn E (e.reverse Q))
      (reducedBraidTwist Q hn E e) := by
    rw [← reducedBraidTwist_swap Q hn E e]
    exact k
  exact (f.trans Q (k'.symm Q)).trans Q (g.symm Q)

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_FiniteHomotopySetoid
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

universe u

variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

lemma classTwistPerm_orthogonal (hn : ∀ a, Q.source a ≠ Q.target a)
    {α β : V} (h : OrthogonalVertices Q α β) :
    classTwistPerm Q (K := K) hn α * classTwistPerm Q hn β =
      classTwistPerm Q hn β * classTwistPerm Q hn α := by
  apply Equiv.ext
  intro x
  induction x using Quotient.inductionOn with | _ E =>
    apply Quotient.sound
    exact ⟨orthogonal_positiveTwists Q E.complex h⟩

lemma classTwistPerm_adjacent (hn : ∀ a, Q.source a ≠ Q.target a)
    {α β : V} (e : SimpleEdge Q α β) :
    classTwistPerm Q (K := K) hn α * classTwistPerm Q hn β * classTwistPerm Q hn α =
      classTwistPerm Q hn β * classTwistPerm Q hn α * classTwistPerm Q hn β := by
  apply Equiv.ext
  intro x
  induction x using Quotient.inductionOn with | _ E =>
    apply Quotient.sound
    exact ⟨adjacent_positiveTwists Q hn E.complex e⟩

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_HomDimension2
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_Refl
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K I J L N : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V]
  [Fintype I] [Fintype J] [Fintype L] [Fintype N]
  [DecidableEq I] [DecidableEq J] [DecidableEq L] [DecidableEq N]

noncomputable def ChainIsomorphism.cone
    {E : BasedComplex Q (K := K) I} {F : BasedComplex Q (K := K) J}
    {G : BasedComplex Q (K := K) L} {H : BasedComplex Q (K := K) N}
    (f : Map Q E F) (g : Map Q G H)
    (a : ChainIsomorphism Q E G) (b : ChainIsomorphism Q F H)
    (comm : a.forward.matrix * g.matrix = f.matrix * b.forward.matrix) :
    ChainIsomorphism Q (f.cone Q) (g.cone Q) := by
  have hc : a.backward.matrix * f.matrix = g.matrix * b.backward.matrix := by
    calc
      _ = a.backward.matrix * (f.matrix * (b.forward.matrix*b.backward.matrix)) := by
        rw [b.sourceEquation]
        exact congrArg (fun z => a.backward.matrix*z) (mul_projectiveIdentity Q f.entries).symm
      _ = a.backward.matrix * ((a.forward.matrix*g.matrix)*b.backward.matrix) := by
        rw [← Matrix.mul_assoc f.matrix,← comm]
      _ = (a.backward.matrix*a.forward.matrix)*g.matrix*b.backward.matrix := by
        simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [a.targetEquation]
        exact congrArg (fun z => z*b.backward.matrix) (projectiveIdentity_mul Q g.entries)
  exact {
    forward := f.coneMap Q g a.forward b.forward comm
    backward := g.coneMap Q f a.backward b.backward hc
    sourceEquation := by
      change Matrix.fromBlocks a.forward.matrix 0 0 b.forward.matrix *
        Matrix.fromBlocks a.backward.matrix 0 0 b.backward.matrix = _
      rw [Matrix.fromBlocks_multiply]
      simp only [Matrix.mul_zero,Matrix.zero_mul,add_zero,zero_add,a.sourceEquation,b.sourceEquation]
      exact f.coneIdentity Q
    targetEquation := by
      change Matrix.fromBlocks a.backward.matrix 0 0 b.backward.matrix *
        Matrix.fromBlocks a.forward.matrix 0 0 b.forward.matrix = _
      rw [Matrix.fromBlocks_multiply]
      simp only [Matrix.mul_zero,Matrix.zero_mul,add_zero,zero_add,a.targetEquation,b.targetEquation]
      exact g.coneIdentity Q }

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_MinimalModelEquivalence
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable
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

noncomputable def minimalClassModelEquivalence (E : BasedComplex Q (K := K) I) :
    HomotopyEquivalence Q (minimalClassModel Q (classOfComplex Q E)).complex E :=
  Classical.choice (Quotient.exact (minimalClassModel_class Q (classOfComplex Q E)))

omit [Fintype V] [DecidableEq A] in
lemma classLayer_minimal (E : BasedComplex Q (K := K) I) (hE : E.IsMinimal Q) (d : ℤ) :
    classLayer Q d (classOfComplex Q E) = classOfComplex Q (E.pureLayer Q hE d) :=
  classOfComplex_eq Q (((minimalClassModelEquivalence Q E).pureLayer Q
    (minimalClassModel_minimal Q _) hE d).toHomotopyEquivalence Q)

noncomputable def classLayerSocleDimension (d : ℤ) (α : V) (c : ℤ)
    (x : FiniteHomotopyClass Q (K := K)) : ℕ :=
  Module.finrank K (coefficientSocle Q
    ((minimalClassModel Q x).complex.pureLayer Q (minimalClassModel_minimal Q x) d) α c)

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_NegativeAmplitudeCoreIndex
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

variable {V A K I : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I]

def tokenTest (E : BasedComplex Q (K := K) I) (α : V) (i : ActedIndex Q E α) :
    TestIndex Q E.placement α :=
  ⟨i.val, ⟨.inr (.inr α), rfl, i.property.symm⟩⟩

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_BottomSocleZero
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

def ClassBottomSocleZero (d:ℤ) (J:Set V) (x:FiniteHomotopyClass Q (K:=K)) : Prop :=
  ∀ α∈J,∀ c,classLayerSocleDimension Q d α c x=0

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_ColorBoundary
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K:Type*} (Q:ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I:Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma pure_color_block (E:BasedComplex Q (K:=K) I) {q:ℤ} (U:Set V)
    (hp:∀ i,(E.placement i).level=q)
    (hb:∀ i,(E.placement i).color∉colorBoundary Q U) :
    BlockClosed Q E {i | (E.placement i).color∈U} := by
  intro i j hn
  obtain ⟨a,hs,ht⟩:=pure_differential_arrow Q E hp hn
  change ((E.placement i).color∈U ↔ (E.placement j).color∈U)
  constructor
  · intro hi
    by_contra hj
    exact hb j ⟨hj,a,hs ▸ hi,ht⟩
  · intro hj
    by_contra hi
    apply hb i
    exact ⟨hi,Q.reverse a,by simpa only [Q.source_reverse,ht] using hj,
      by simpa only [Q.target_reverse] using hs⟩

noncomputable def colorRestriction (E:BasedComplex Q (K:=K) I) {q:ℤ} (U:Set V)
    (hp:∀ i,(E.placement i).level=q)
    (hb:∀ i,(E.placement i).color∉colorBoundary Q U) :
    BasedComplex Q (K:=K) {i // (E.placement i).color∈U} :=
  blockRestriction Q E _ (pure_color_block Q E U hp hb)

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_DownClosed
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
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

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_FiniteSum2
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K I : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I]
  {T R : I → Type*} [∀ i, Fintype (T i)] [∀ i, Fintype (R i)]
  [∀ i, DecidableEq (T i)] [∀ i, DecidableEq (R i)]

def sumTwistEquiv (E : (i:I) → BasedComplex Q (K := K) (T i)) (α:V) :
    (Σ i, TestIndex Q (E i).placement α ⊕ T i) ≃
      (TestIndex Q (finiteSum Q E).placement α ⊕ Sigma T) where
  toFun
    | ⟨i,.inl ⟨x,p⟩⟩ => .inl ⟨⟨i,x⟩,p⟩
    | ⟨i,.inr x⟩ => .inr ⟨i,x⟩
  invFun
    | .inl ⟨⟨i,x⟩,p⟩ => ⟨i,.inl ⟨x,p⟩⟩
    | .inr ⟨i,x⟩ => ⟨i,.inr x⟩
  left_inv z := by rcases z with ⟨i,⟨x,p⟩|x⟩ <;> rfl
  right_inv z := by rcases z with ⟨⟨i,x⟩,p⟩|⟨i,x⟩ <;> rfl

lemma sumTwist_eq (E : (i:I) → BasedComplex Q (K := K) (T i)) (α:V) :
    ((finiteSum Q E).positiveTwist Q α).reindex Q (sumTwistEquiv Q E α) =
      finiteSum Q (fun i => (E i).positiveTwist Q α) := by
  classical
  apply ext_placement_differential Q
  · funext z
    rcases z with ⟨i,⟨x,p⟩|x⟩ <;> rfl
  · apply Matrix.ext
    rintro ⟨i,x⟩ ⟨j,y⟩
    by_cases hij : i=j
    · subst j
      rcases x with ⟨x,p⟩|x <;> rcases y with ⟨y,q⟩|y
      all_goals dsimp only [reindex,Matrix.submatrix_apply,sumTwistEquiv,Equiv.coe_fn_mk]
      all_goals simp only [finiteSum,positiveTwist_differential,Matrix.blockDiagonal'_apply_eq,
        Matrix.fromBlocks,Matrix.of_apply,Sum.elim_inl,Sum.elim_inr,testTransform,scalarCornerMatrix,testMatrix,
        evaluationMatrix,Matrix.neg_apply,Matrix.zero_apply,Sigma.mk.inj_iff,heq_eq_eq,true_and]
    · have hs (x:T i) (y:T j) : (⟨i,x⟩ : Sigma T) ≠ ⟨j,y⟩ := fun h => hij (congrArg Sigma.fst h)
      rcases x with ⟨x,p⟩|x <;> rcases y with ⟨y,q⟩|y
      all_goals dsimp only [reindex,Matrix.submatrix_apply,sumTwistEquiv,Equiv.coe_fn_mk]
      all_goals simp only [finiteSum,positiveTwist_differential,Matrix.blockDiagonal'_apply_ne _ _ _ hij,
        Matrix.fromBlocks,Matrix.of_apply,Sum.elim_inl,Sum.elim_inr,testTransform,scalarCornerMatrix,testMatrix,
        evaluationMatrix,Matrix.neg_apply,Matrix.zero_apply,ite_eq_right (hs _ _),MulZeroClass.mul_zero,
        coordinates_zero,zero_smul,neg_zero]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_GeneratorArray2
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_GeneratorVectorPureLayer
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A:Type u} {K I:Type*} [Fintype I] [Field K]
  (Q:ReversibleQuiver V A) [Fintype A] [DecidableEq V]

lemma generatorVector_pureLayer (E:BasedComplex Q (K:=K) I) (hE:E.IsMinimal Q)
    (q:ℤ) (α:V) : generatorVector Q (E.pureLayer Q hE q) α = (E.levelArray Q (α,q):ℝ) := by
  classical
  rw [levelArray_apply]
  unfold generatorVector
  congr 1
  apply Nat.card_congr
  exact
    { toFun := fun i=>⟨i.val.val,i.property,i.val.property⟩
      invFun := fun i=>⟨⟨i.val,i.property.2⟩,i.property.1⟩
      left_inv := fun _=>rfl
      right_inv := fun _=>rfl }

lemma generatorVector_minimalLayer (x:FiniteHomotopyClass Q (K:=K)) (q:ℤ) (α:V) :
    generatorVector Q ((minimalClassModel Q x).complex.pureLayer Q (minimalClassModel_minimal Q x) q) α =
      (classLevelArray Q x (α,q):ℝ) := by
  rw [generatorVector_pureLayer,← classLevelArray_of_minimal Q _ (minimalClassModel_minimal Q x),
    minimalClassModel_class]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_Sum
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
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

lemma classPositiveTwist_sum (α : V) (x : I → FiniteHomotopyClass Q (K := K)) :
    classPositiveTwist Q α (classSum Q x) =
      classSum Q (fun i => classPositiveTwist Q α (x i)) := by
  classical
  have hx : x = fun i => Quotient.mk (finiteHomotopySetoid Q) (x i).out := by
    funext i; exact (Quotient.out_eq (x i)).symm
  conv_rhs => rw [hx]
  change _ = classSum Q (fun i => classOfComplex Q ((x i).out.complex.positiveTwist Q α))
  rw [classSum_complex]
  change classOfComplex Q ((finiteSum Q (fun i => (x i).out.complex)).positiveTwist Q α) = _
  exact (classOfComplex_reindex Q _ (sumTwistEquiv Q (fun i => (x i).out.complex) α)).trans
    (congrArg (classOfComplex Q) (sumTwist_eq Q (fun i => (x i).out.complex) α))

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_SumTestEquiv
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype
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

omit [Fintype V] [DecidableEq A] [∀ i, DecidableEq (T i)] in
lemma finiteSum_minimal (E : (i:I) → BasedComplex Q (K := K) (T i))
    (hE : ∀ i, (E i).IsMinimal Q) : (finiteSum Q E).IsMinimal Q := by
  rintro ⟨i,x⟩ ⟨j,y⟩
  change (Matrix.blockDiagonal' (fun i => (E i).differential) ⟨i,x⟩ ⟨j,y⟩).vertex=0
  by_cases h : i=j
  · subst j; rw [Matrix.blockDiagonal'_apply_eq]; exact hE i x y
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ h]; rfl

def sumLayerEquiv (E : (i:I) → BasedComplex Q (K := K) (T i)) (d : ℤ) :
    (Σ i, {x // ((E i).placement x).level=d}) ≃
      {x : Sigma T // ((finiteSum Q E).placement x).level=d} where
  toFun x := ⟨⟨x.1,x.2.val⟩,x.2.property⟩
  invFun x := ⟨x.1.1,x.1.2,x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_LevelArrayComplexMinimal
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V]
  {I : Type u} [Fintype I] [DecidableEq I]

lemma finiteSum_levelArray {T : I → Type u} [∀ i, Fintype (T i)] [∀ i, DecidableEq (T i)]
    (E : (i:I) → BasedComplex Q (K := K) (T i)) :
    (finiteSum Q E).levelArray Q = ∑ i, (E i).levelArray Q := by
  classical
  simp only [levelArray_eq_sum,Fintype.sum_sigma]
  rfl

lemma classLevelArray_sum (x : I → FiniteHomotopyClass Q (K := K)) :
    classLevelArray Q (classSum Q x) = ∑ i, classLevelArray Q (x i) := by
  classical
  let E (i:I) := (minimalClassModel Q (x i)).complex
  have hE (i:I) : (E i).IsMinimal Q := minimalClassModel_minimal Q (x i)
  have hx : x = fun i => classOfComplex Q (E i) := by
    funext i; exact (minimalClassModel_class Q (x i)).symm
  rw [hx,classSum_complex,classLevelArray_complex_minimal Q _ (finiteSum_minimal Q E hE)]
  simp_rw [classLevelArray_complex_minimal Q _ (hE _)]
  exact finiteSum_levelArray Q E

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_LowMatrix
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_LowerTruncation
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

omit [Fintype V] [DecidableEq A] in
lemma classLowerTruncation_minimal (E:BasedComplex Q (K:=K) I) (hE:E.IsMinimal Q) (d:ℤ) :
    classLowerTruncation Q d (classOfComplex Q E)=classOfComplex Q (lowerTruncation Q E hE d) :=
  classOfComplex_eq Q ((minimalClassModelEquivalence Q E).lowerTruncation Q
    (minimalClassModel_minimal Q _) hE d)

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_PacketPermReindex
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.linearMap_pathBasis _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_base _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_left _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
attribute [local instance] Classical.decEq
variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  (hn : ∀ a, Q.source a ≠ Q.target a)
  {J L : Type u} [Fintype J] [Fintype L]

lemma classPacketPerm_reindex (v:J → V)
    (hv : Pairwise fun a b => OrthogonalVertices Q (v a) (v b)) (e:L ≃ J) :
    classPacketPerm Q (K := K) hn v hv = classPacketPerm Q hn (v ∘ e)
      (fun _ _ hab => hv (fun he => hab (e.injective he))) := by
  classical
  apply Equiv.ext
  intro x
  induction x using Quotient.inductionOn with | _ E =>
    erw [classPacketPerm_apply,classPacketPerm_apply]
    exact classOfComplex_packet_reindex Q E.complex v e

lemma classPacketPerm_empty [IsEmpty J] (v:J → V)
    (hv : Pairwise fun a b => OrthogonalVertices Q (v a) (v b)) :
    classPacketPerm Q (K := K) hn v hv = Equiv.refl _ := by
  classical
  apply Equiv.ext
  intro x
  induction x using Quotient.inductionOn with | _ E =>
    rw [classPacketPerm_apply]
    exact (classOfComplex_reindex Q _ (packetEmptyEquiv Q E.complex v)).trans
      (congrArg (classOfComplex Q) (packetEmpty_eq Q E.complex v))

lemma classPacketPerm_cons (v:Option J → V)
    (hv : Pairwise fun a b => OrthogonalVertices Q (v a) (v b)) :
    classPacketPerm Q (K := K) hn v hv =
      classTwistPerm Q hn (v none) * classPacketPerm Q hn (v ∘ some)
        (fun _ _ hab => hv (fun he => hab (Option.some.inj he))) := by
  classical
  apply Equiv.ext
  intro x
  induction x using Quotient.inductionOn with | _ E =>
    change _ = classPositiveTwist Q (v none) (classPacketPerm Q hn (v ∘ some) _ ⟦E⟧)
    erw [classPacketPerm_apply,classPacketPerm_apply]
    have he : v = fun z : Option J => z.elim (v none) (v ∘ some) := by
      funext z; cases z <;> rfl
    conv_lhs => rw [he]
    convert classOfComplex_packet_cons Q E.complex (v none) (v ∘ some)
      (fun a => hv (by simp)) using 1
    all_goals try with_reducible_and_instances rfl

variable {I : Type u} [Fintype I] [DecidableEq I]
lemma classPacketPerm_sum (v:J → V)
    (hv : Pairwise fun a b => OrthogonalVertices Q (v a) (v b))
    (x : I → FiniteHomotopyClass Q (K := K)) :
    classPacketPerm Q hn v hv (classSum Q x) =
      classSum Q (fun i => classPacketPerm Q hn v hv (x i)) := by
  classical
  suffices hh : ∀ (J : Type u) [Fintype J] (v:J → V)
      (hv : Pairwise fun a b => OrthogonalVertices Q (v a) (v b)),
      classPacketPerm Q hn v hv (classSum Q x) =
        classSum Q (fun i => classPacketPerm Q hn v hv (x i)) from hh J v hv
  intro J inst
  apply Fintype.induction_empty_option (P := fun J _ => ∀ (v:J → V)
    (hv : Pairwise fun a b => OrthogonalVertices Q (v a) (v b)),
    classPacketPerm Q hn v hv (classSum Q x) =
      classSum Q (fun i => classPacketPerm Q hn v hv (x i))) _ _ _ J
  · intro J L instL e ih
    let := Fintype.ofEquiv L e.symm
    intro v hv
    rw [classPacketPerm_reindex Q hn v hv e]
    exact ih _ _
  · intro v hv
    rw [classPacketPerm_empty Q hn v hv]
    rfl
  · intro J instJ ih v hv
    rw [classPacketPerm_cons Q hn v hv]
    change classPositiveTwist Q (v none) (classPacketPerm Q hn (v ∘ some) _ (classSum Q x)) =
      classSum Q (fun i => classPositiveTwist Q (v none) (classPacketPerm Q hn (v ∘ some) _ (x i)))
    erw [ih,classPositiveTwist_sum]

lemma classPacketPerm_inverse_sum (v:J → V)
    (hv : Pairwise fun a b => OrthogonalVertices Q (v a) (v b))
    (x : I → FiniteHomotopyClass Q (K := K)) :
    (classPacketPerm Q hn v hv).symm (classSum Q x) =
      classSum Q (fun i => (classPacketPerm Q hn v hv).symm (x i)) := by
  apply (classPacketPerm Q hn v hv).injective
  rw [Equiv.apply_symm_apply,classPacketPerm_sum]
  simp only [Equiv.apply_symm_apply]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_OptionSumEquiv
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
open Zigzag

universe u
attribute [local instance] Classical.decEq
variable {V A : Type u} {K : Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  (hn:∀ a,Q.source a≠Q.target a)

lemma classPacketPerm_sumIndex {J L:Type u} [Fintype J] [Fintype L] (v:J ⊕ L → V)
    (hv:Pairwise fun a b => OrthogonalVertices Q (v a) (v b)) :
    classPacketPerm Q (K:=K) hn v hv =
      classPacketPerm Q hn (v ∘ Sum.inl) (packet_orthogonal_inl Q v hv) *
      classPacketPerm Q hn (v ∘ Sum.inr) (packet_orthogonal_inr Q v hv) := by
  suffices hh : ∀ (J:Type u) [Fintype J] (v:J ⊕ L → V)
    (hv:Pairwise fun a b => OrthogonalVertices Q (v a) (v b)),
    classPacketPerm Q (K:=K) hn v hv =
      classPacketPerm Q hn (v ∘ Sum.inl) (packet_orthogonal_inl Q v hv) *
      classPacketPerm Q hn (v ∘ Sum.inr) (packet_orthogonal_inr Q v hv) from hh J v hv
  intro J inst
  apply Fintype.induction_empty_option (P:=fun J _ => ∀ (v:J ⊕ L → V)
    (hv:Pairwise fun a b => OrthogonalVertices Q (v a) (v b)),
    classPacketPerm Q (K:=K) hn v hv =
      classPacketPerm Q hn (v ∘ Sum.inl) (packet_orthogonal_inl Q v hv) *
      classPacketPerm Q hn (v ∘ Sum.inr) (packet_orthogonal_inr Q v hv)) _ _ _ J
  · intro J J' instJ' e ih
    let := Fintype.ofEquiv J' e.symm
    intro v hv
    erw [classPacketPerm_reindex Q hn v hv (Equiv.sumCongr e (Equiv.refl L)),
      classPacketPerm_reindex Q hn (v ∘ Sum.inl) _ e]
    exact ih _ _
  · intro v hv
    erw [classPacketPerm_empty Q hn (v ∘ Sum.inl),show (Equiv.refl _ : Equiv.Perm (FiniteHomotopyClass Q (K:=K))) = 1 from rfl,_root_.one_mul]
    let e : L ≃ PEmpty ⊕ L :=
      { toFun:=Sum.inr
        invFun:=fun x=>x.elim PEmpty.elim id
        left_inv:=fun _=>rfl
        right_inv:=by intro x; cases x with | inl x=>exact x.elim | inr x=>rfl }
    exact classPacketPerm_reindex Q hn v hv e
  · intro J instJ ih v hv
    erw [classPacketPerm_reindex Q hn v hv (optionSumEquiv J L),classPacketPerm_cons Q hn (v ∘ (optionSumEquiv J L)),
      classPacketPerm_cons Q hn (v ∘ Sum.inl),_root_.mul_assoc]
    apply congrArg (fun p => classTwistPerm Q (K:=K) hn (v (.inl none)) * p)
    exact ih _ _

lemma exists_packetGroupWord {J L:Type u} [Fintype J] [Fintype L] (v:J × L → V)
    (hv:Pairwise fun a b => OrthogonalVertices Q (v a) (v b)) :
    ∃ w:List J, classPacketPerm Q (K:=K) hn v hv =
      (w.map fun j=>classPacketPerm Q hn (fun l=>v (j,l))
        (packet_orthogonal_fiber Q v hv j)).prod := by
  suffices hh : ∀ (J:Type u) [Fintype J] (v:J × L → V)
    (hv:Pairwise fun a b => OrthogonalVertices Q (v a) (v b)),
    ∃ w:List J, classPacketPerm Q (K:=K) hn v hv =
      (w.map fun j=>classPacketPerm Q hn (fun l=>v (j,l))
        (packet_orthogonal_fiber Q v hv j)).prod from hh J v hv
  intro J inst
  apply Fintype.induction_empty_option (P:=fun J _ => ∀ (v:J × L → V)
    (hv:Pairwise fun a b => OrthogonalVertices Q (v a) (v b)),
    ∃ w:List J, classPacketPerm Q (K:=K) hn v hv =
      (w.map fun j=>classPacketPerm Q hn (fun l=>v (j,l))
        (packet_orthogonal_fiber Q v hv j)).prod) _ _ _ J
  · intro J J' instJ' e ih
    let := Fintype.ofEquiv J' e.symm
    intro v hv
    erw [classPacketPerm_reindex Q hn v hv (Equiv.prodCongr e (Equiv.refl L))]
    obtain ⟨w,hw⟩ := ih _ _
    refine ⟨w.map e,hw.trans ?_⟩
    simp only [List.map_map]
    apply congrArg List.prod
    apply List.map_congr_left
    intro j hj
    rfl
  · intro v hv
    refine ⟨[],?_⟩
    erw [classPacketPerm_empty Q hn v hv]
    rfl
  · intro J instJ ih v hv
    erw [classPacketPerm_reindex Q hn v hv (optionProdEquiv J L),classPacketPerm_sumIndex Q hn (v ∘ (optionProdEquiv J L))]
    obtain ⟨w,hw⟩ := ih (fun p=>v (some p.1,p.2))
      (by
        intro a b hab
        apply hv
        intro hh
        simp only [Prod.mk.injEq,Option.some.injEq] at hh
        exact hab (Prod.ext hh.1 hh.2))
    refine ⟨none::w.map some,?_⟩
    simp only [List.map_cons,List.prod_cons,List.map_map]
    exact congrArg (fun p=>classPacketPerm Q hn (fun l=>v (none,l)) _ * p) hw

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_PacketPermEnumeration
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.linearMap_pathBasis _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_base _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_left _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_right
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
  (hn : ∀ a,Q.source a≠Q.target a)

lemma classPacketPerm_enumeration {J : Type u} [Fintype J] (v : J → V)
    (hv : Pairwise fun a b => OrthogonalVertices Q (v a) (v b)) :
    ∃ l : List J, l.Nodup ∧ (∀ j,j∈l) ∧
      (l.map fun j => classTwistPerm Q (K:=K) hn (v j)).prod=classPacketPerm Q hn v hv := by
  suffices hh : ∀ (J : Type u) [Fintype J] (v : J → V)
    (hv : Pairwise fun a b => OrthogonalVertices Q (v a) (v b)),
    ∃ l : List J, l.Nodup ∧ (∀ j,j∈l) ∧
      (l.map fun j => classTwistPerm Q (K:=K) hn (v j)).prod=classPacketPerm Q hn v hv from hh J v hv
  intro J inst
  apply Fintype.induction_empty_option (P:=fun J _ => ∀ (v : J → V)
    (hv : Pairwise fun a b => OrthogonalVertices Q (v a) (v b)),
    ∃ l : List J, l.Nodup ∧ (∀ j,j∈l) ∧
      (l.map fun j => classTwistPerm Q (K:=K) hn (v j)).prod=classPacketPerm Q hn v hv) _ _ _ J
  · intro J L instL e ih
    let := Fintype.ofEquiv L e.symm
    intro v hv
    obtain ⟨l,hl,ha,he⟩ := ih (v∘e) (fun a b hab => hv (fun h => hab (e.injective h)))
    refine ⟨l.map e,hl.map e.injective,?_,?_⟩
    · intro j
      exact List.mem_map.mpr ⟨e.symm j,ha _,e.apply_symm_apply j⟩
    · rw [classPacketPerm_reindex Q hn v hv e]
      simpa only [List.map_map,Function.comp_def] using he
  · intro v hv
    refine ⟨[],List.nodup_nil,fun j => isEmptyElim j,?_⟩
    rw [List.map_nil,List.prod_nil,classPacketPerm_empty]
    rfl
  · intro J inst ih v hv
    obtain ⟨l,hl,ha,he⟩ := ih (v∘some) (fun a b hab => hv (fun h => hab (Option.some.inj h)))
    refine ⟨none::l.map some,?_,?_,?_⟩
    · simp only [List.nodup_cons,List.mem_map,Option.some_ne_none,and_false,exists_false,not_false_eq_true,
        true_and]
      exact hl.map (Option.some_injective _)
    · intro j
      cases j with
      | none => exact List.mem_cons_self
      | some j => exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨j,ha j,rfl⟩)
    · rw [List.map_cons,List.prod_cons,List.map_map,classPacketPerm_cons,← he]
      rfl

lemma classPacketPerm_toList {J : Type u} [Fintype J] (v : J → V)
    (hv : Pairwise fun a b => OrthogonalVertices Q (v a) (v b)) :
    ((Finset.univ : Finset J).toList.map fun j => classTwistPerm Q (K:=K) hn (v j)).prod=
      classPacketPerm Q hn v hv := by
  obtain ⟨l,hl,ha,he⟩ := classPacketPerm_enumeration Q (K:=K) hn v hv
  have hp : (Finset.univ : Finset J).toList.Perm l :=
    (List.perm_ext_iff_of_nodup (Finset.nodup_toList _) hl).mpr (fun j => by simp [ha])
  rw [← he]
  apply (hp.map _).prod_eq'
  rw [List.pairwise_map]
  apply (Finset.nodup_toList (Finset.univ : Finset J)).imp
  intro a b hab
  exact classTwistPerm_orthogonal Q hn (hv hab)

lemma positiveWordAction_eq_prod (w : List V) (x : FiniteHomotopyClass Q (K:=K)) :
    positiveWordAction Q w x=(w.map (classTwistPerm Q hn)).prod x := by
  induction w with
  | nil => rfl
  | cons a w ih => exact congrArg (classPositiveTwist Q a) ih

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_ReindexConeIsomorphism
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K I J L N : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V]
  [Fintype I] [Fintype J] [Fintype L] [Fintype N]
  [DecidableEq I] [DecidableEq J] [DecidableEq L] [DecidableEq N]
  {E : BasedComplex Q (K := K) I} {F : BasedComplex Q (K := K) J}

noncomputable def Map.reindexConeIsomorphism (f : Map Q E F) (e : L ≃ I) (d : N ≃ J) :
    ChainIsomorphism Q (f.cone Q) ((f.reindex Q e d).cone Q) := by
  rw [← f.reindexCone_eq Q e d]
  exact reindexChainIsomorphism Q (f.cone Q) (Equiv.sumCongr e d)

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_SumTruncationEquiv
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype
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

def sumTruncationEquiv (E : (i:I) → BasedComplex Q (K:=K) (T i)) (d:ℤ) :
    (Σ i,lowerLevelSet Q (E i) d) ≃ lowerLevelSet Q (finiteSum Q E) d where
  toFun x:=⟨⟨x.1,x.2.val⟩,x.2.property⟩
  invFun x:=⟨x.1.1,x.1.2,x.2⟩
  left_inv _:=rfl
  right_inv _:=rfl

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_UnfoldedCartanSymm
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
open scoped _root_.Matrix

variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

variable {I : Type*} [Fintype I]

omit [Fintype V] [DecidableEq A] in
lemma generatorVector_nonneg (E : BasedComplex Q (K := K) I) (α : V) :
    0 ≤ generatorVector Q E α := Nat.cast_nonneg _

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Functors_ReversibleQuiverMap
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Iso
open Zigzag Zigzag.BasedComplex

universe u
variable {V A W B : Type u} {K : Type*} {Q : ReversibleQuiver V A} {R : ReversibleQuiver W B}
  (e : Iso Q R) [Field K] [Fintype V] [Fintype W] [Fintype A] [Fintype B]
  [DecidableEq V] [DecidableEq W] [DecidableEq A] [DecidableEq B]
  {I : Type u} [Fintype I] [DecidableEq I]

lemma classMap_packet (hn:∀ a,Q.source a ≠ Q.target a)
    {J:Type u} [Fintype J] (v:J → V)
    (hv:Pairwise fun a b => OrthogonalVertices Q (v a) (v b))
    (x:FiniteHomotopyClass Q (K := K)) :
    e.classMap (classPacketPerm Q hn v hv x) =
      classPacketPerm R (e.loopless hn) (e.vertex ∘ v) (e.orthogonal_pairwise v hv) (e.classMap x) := by
  classical
  suffices hh : ∀ (J:Type u) [Fintype J] (v:J → V)
    (hv:Pairwise fun a b => OrthogonalVertices Q (v a) (v b)), ∀ x,
    e.classMap (classPacketPerm Q hn v hv x) =
      classPacketPerm R (e.loopless hn) (e.vertex ∘ v) (e.orthogonal_pairwise v hv) (e.classMap x) from hh J v hv x
  intro J inst
  apply Fintype.induction_empty_option (P := fun J _ => ∀ (v:J → V)
    (hv:Pairwise fun a b => OrthogonalVertices Q (v a) (v b)), ∀ x,
    e.classMap (classPacketPerm Q hn v hv x) =
      classPacketPerm R (e.loopless hn) (e.vertex ∘ v) (e.orthogonal_pairwise v hv) (e.classMap x)) _ _ _ J
  · intro J L instL f ih
    let := Fintype.ofEquiv L f.symm
    intro v hv x
    rw [classPacketPerm_reindex Q hn v hv f,
      classPacketPerm_reindex R (e.loopless hn) (e.vertex ∘ v) _ f]
    exact ih _ _ x
  · intro v hv x
    rw [classPacketPerm_empty Q hn v hv,classPacketPerm_empty R (e.loopless hn)]
    rfl
  · intro J instJ ih v hv x
    rw [classPacketPerm_cons Q hn v hv,classPacketPerm_cons R (e.loopless hn)]
    change e.classMap (classPositiveTwist Q (v none) (classPacketPerm Q hn (v ∘ some) _ x)) =
      classPositiveTwist R (e.vertex (v none)) (classPacketPerm R _ ((e.vertex ∘ v) ∘ some) _ (e.classMap x))
    rw [e.classMap_positiveTwist]
    exact congrArg (classPositiveTwist R (e.vertex (v none)))
      (ih (v ∘ some) (fun a b hab => hv (fun h => hab (Option.some.inj h))) x)

end HarmonicArtin.ReversibleQuiver.Iso

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Functors_Index
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_reverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.StringFunctor

variable {V B J K : Type*} (Q : ReversibleQuiver V B)
  (step : B → Bool) (hstep : ∀ b, step (Q.reverse b) = step b)
  (N : J → J → Prop) (hN : ∀ ⦃first second⦄, N first second → N second first)
  [Fintype V] [Fintype B] [Fintype J]
  [DecidableEq V] [DecidableEq B] [DecidableEq J] [DecidableRel N] [Field K]
  (orient : B → Bool) (μ : J → K) (A : K)

local notation "U" => Q.stringQuiver step hstep N hN
local notation "I" => StringIndex (V := V) N
local notation "F" => linearMap Q step hstep N hN orient μ A

lemma linearMap_positive {x : Zigzag U K} (hx : x.vertex = 0) (i j : I) :
    (F x i j).vertex = 0 := by
  rw [linearMap_apply,Zigzag.vertex_sum]
  apply Finset.sum_eq_zero
  intro p hp
  rw [Zigzag.vertex_smul]
  by_cases hn : Path.length p ≠ 0
  · rw [pathImage_positive Q step hstep N hN orient μ A p hn i j,smul_zero]
  · have hc : Zigzag.pathCoordinates U x p = 0 := by
      rcases p with a|p|a
      · exact congrFun hx a
      · exact (hn (by norm_num [Path.length])).elim
      · exact (hn (by norm_num [Path.length])).elim
    rw [hc,zero_smul]

lemma complex_minimal {T : Type*} [Fintype T]
    (ho : ∀ b, orient (Q.reverse b) = !(orient b))
    (hμ : ∀ a, μ a ≠ 0) (δ : K)
    (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
    (hPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, μ b = δ * μ a)
    (E : Zigzag.BasedComplex U (K := K) T) (hE : E.IsMinimal U) :
    (complex Q step hstep N hN orient μ A ho hμ δ hA hroot hPF E).IsMinimal U := by
  intro i j
  exact linearMap_positive Q step hstep N hN orient μ A (hE i.1 j.1)
    (indexEmbed N E.placement i) (indexEmbed N E.placement j)

end HarmonicArtin.ReversibleQuiver.StringFunctor

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Functors_PacketSwitchMatrix
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_reverse
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
local notation "F" => linearMap Q step hstep N hN orient μ A

lemma switch_evaluation (u t : V) (b c : J)
    (x : LeftPaths Q step hstep N hN u t b c) (d : {d:J // N b d}) :
    (∑ y : RightPaths Q step hstep N hN u t b c,
      (evaluationMatrix Q step hstep N hN orient μ A u t b c x y • Zigzag.vertexId U (u,c)) *
        (if y.1=d then Zigzag.pathBasis U y.2.val else 0)) =
      F (Zigzag.pathBasis U x.2.val) (evaluationSource N u c x.1) (evaluationTarget N t b d) := by
  rw [Fintype.sum_sigma,Finset.sum_eq_single d]
  · simp only [ite_true, if_true,smul_mul_assoc,Zigzag.cornerPath_left]
    exact Zigzag.sum_cornerPath U
      (F (Zigzag.pathBasis U x.2.val) (evaluationSource N u c x.1) (evaluationTarget N t b d))
      (linearMap_left Q step hstep N hN orient μ A (Zigzag.pathBasis U x.2.val)
        (evaluationSource N u c x.1) (evaluationTarget N t b d))
      (linearMap_right Q step hstep N hN orient μ A (Zigzag.pathBasis U x.2.val)
        (evaluationSource N u c x.1) (evaluationTarget N t b d))
  · intro e he hed
    apply Finset.sum_eq_zero
    intro z hz
    simp only [ite_eq_right hed,mul_zero]
  · simp

section Comparison
variable [Fintype T] [DecidableEq T]
    (ho : ∀ b, orient (Q.reverse b) = !(orient b))
    (hμ : ∀ a, μ a ≠ 0) (δ : K)
    (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
    (hPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, μ b = δ * μ a)
local notation "C" => complex Q step hstep N hN orient μ A ho hμ δ hA hroot hPF

lemma packetEvaluation_right_entry (E : Zigzag.BasedComplex U (K := K) T) (u:V)
    (c:J) (i:T) (y : RightPaths Q step hstep N hN u (E.placement i).color.1 (E.placement i).color.2 c)
    (j:T) (d : {d:J // N (E.placement j).color.2 d}) :
    ((C E).packetEvaluationMatrix U (fun a:J => (u,a))).submatrix
      (rightPacketEquiv Q step hstep N hN E.placement u) id ⟨c,⟨i,y⟩⟩ ⟨j,d⟩ =
      if (⟨i,y.1⟩ : Index N E.placement) = ⟨j,d⟩ then Zigzag.pathBasis U y.2.val else 0 := by
  dsimp only [Matrix.submatrix,rightPacketEquiv,rightHomEquiv,Equiv.coe_fn_mk,
    Zigzag.BasedComplex.packetEvaluationMatrix,Zigzag.evaluationMatrix]
  simp only [Matrix.of_apply]
  split_ifs <;> first | rfl | contradiction

lemma packetEvaluation_left_entry (E : Zigzag.BasedComplex U (K := K) T) (u:V)
    (c:J) (i:T) (x : LeftPaths Q step hstep N hN u (E.placement i).color.1 (E.placement i).color.2 c)
    (j:T) (d : {d:J // N (E.placement j).color.2 d}) :
    (matrix Q step hstep N hN orient μ A
      (E.packetTest U (fun a:J => (u,a))).placement E.placement
      (E.packetEvaluationMatrix U (fun a:J => (u,a)))).submatrix
      (leftPacketEquiv Q step hstep N hN E.placement u) id ⟨c,⟨i,x⟩⟩ ⟨j,d⟩ =
      F (if i=j then Zigzag.pathBasis U x.2.val else 0)
        (evaluationSource N u c x.1) (evaluationTarget N (E.placement j).color.1 (E.placement j).color.2 d) := by
  dsimp only [Matrix.submatrix,leftPacketEquiv,Equiv.coe_fn_mk,matrix,indexEmbed,
    Zigzag.BasedComplex.packetEvaluationMatrix, Zigzag.evaluationMatrix,
    Zigzag.BasedComplex.packetTest,Zigzag.packetPlacement,Zigzag.testPlacement,
    evaluationSource,evaluationTarget]
  simp only [Matrix.of_apply]
  split_ifs <;> first | rfl | contradiction

lemma packetEvaluation_comparison (E : Zigzag.BasedComplex U (K := K) T) (u:V) :
    packetSwitchMatrix Q step hstep N hN orient μ A E.placement u *
      ((C E).packetEvaluationMatrix U (fun a:J => (u,a))).submatrix
        (rightPacketEquiv Q step hstep N hN E.placement u) id =
    (matrix Q step hstep N hN orient μ A
      (E.packetTest U (fun a:J => (u,a))).placement E.placement
      (E.packetEvaluationMatrix U (fun a:J => (u,a)))).submatrix
        (leftPacketEquiv Q step hstep N hN E.placement u) id := by
  apply Matrix.ext
  rintro ⟨c,i,a,x⟩ ⟨j,d⟩
  rw [packetSwitchMatrix,Matrix.blockDiagonal'_mul_entry,Fintype.sum_sigma,Finset.sum_eq_single i]
  · simp only [Zigzag.scalarCornerMatrix,homSwitch,Matrix.blockDiagonal'_apply_eq]
    simp only [packetEvaluation_right_entry,packetEvaluation_left_entry]
    by_cases hij : i=j
    · subst j
      simp only [Sigma.mk.inj_iff,heq_eq_eq,true_and,ite_true, if_true]
      exact switch_evaluation Q step hstep N hN orient μ A _ _ _ _ _ _
    · simp only [ite_eq_right hij,map_zero,Matrix.zero_apply]
      apply Finset.sum_eq_zero
      intro y hy
      have he : (⟨i,y.1⟩ : Index N E.placement) ≠ ⟨j,d⟩ := fun h => hij (congrArg Sigma.fst h)
      rw [ite_eq_right he,mul_zero]
  · intro k hk hki
    apply Finset.sum_eq_zero
    intro y hy
    simp only [Zigzag.scalarCornerMatrix,homSwitch,Matrix.blockDiagonal'_apply_ne _ _ _ (Ne.symm hki),
      zero_smul,zero_mul]
  · simp

end Comparison
end HarmonicArtin.ReversibleQuiver.StringFunctor

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Functors_PacketTwistComparison
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable
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
local notation "C" => complex Q step hstep N hN orient μ A ho hμ δ hA hroot hPF
local notation "M" => map Q step hstep N hN orient μ A ho hμ δ hA hroot hPF

noncomputable def packetTwistComparison (E : Zigzag.BasedComplex U (K := K) T) (u:V) :
    Zigzag.BasedComplex.ChainIsomorphism U
      (C (E.packetTwist U (fun a:J => (u,a))))
      ((C E).packetTwist U (fun a:J => (u,a))) := by
  let f := M (E.packetEvaluation U (fun a:J => (u,a)))
  let g := (C E).packetEvaluation U (fun a:J => (u,a))
  let e := leftPacketEquiv Q step hstep N hN E.placement u
  let d := rightPacketEquiv Q step hstep N hN E.placement u
  let a := packetComparison Q step hstep N hN orient μ A ho hμ δ hA hroot hPF E u
  let b := Zigzag.BasedComplex.ChainIsomorphism.refl U ((C E).reindex U (Equiv.refl _))
  have comm : a.forward.matrix * (g.reindex U d (Equiv.refl _)).matrix =
      (f.reindex U e (Equiv.refl _)).matrix * b.forward.matrix := by
    have h := packetEvaluation_comparison Q step hstep N hN orient μ A ho hμ δ hA hroot hPF E u
    rw [show a.forward.matrix = packetSwitchMatrix Q step hstep N hN orient μ A E.placement u from
      packetComparison_matrix Q step hstep N hN orient μ A ho hμ δ hA hroot hPF E u]
    exact h.trans (Zigzag.mul_projectiveIdentity U (f.reindex U e (Equiv.refl _)).entries).symm
  let middle := Zigzag.BasedComplex.ChainIsomorphism.cone U
    (f.reindex U e (Equiv.refl _)) (g.reindex U d (Equiv.refl _)) a b comm
  exact (((coneComparison Q step hstep N hN orient μ A ho hμ δ hA hroot hPF
      (E.packetEvaluation U (fun a:J => (u,a)))).trans U
    (f.reindexConeIsomorphism U e (Equiv.refl _))).trans U middle).trans U
      (g.reindexConeIsomorphism U d (Equiv.refl _)).symm

end HarmonicArtin.ReversibleQuiver.StringFunctor

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Functors_ColorPacketPerm
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable
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

local notation "F" => classLabelFunctor Q step hstep N hN orient μ A ho hμ δ hA hroot hPF

lemma classLabel_packet (hn : ∀ b, Q.source b ≠ Q.target b) (v:V)
    (x : FiniteHomotopyClass U (K := K)) :
    F (colorPacketPerm Q step hstep N hN hn v x) =
      colorPacketPerm Q step hstep N hN hn v (F x) := by
  induction x using Quotient.inductionOn with | _ E =>
    rw [colorPacketPerm_apply]
    change classOfComplex U (C (E.complex.packetTwist U (fun a:J => (v,a)))) =
      colorPacketPerm Q step hstep N hN hn v
        (Quotient.mk (finiteHomotopySetoid U) (FiniteModel.ofComplex U (C E.complex)))
    rw [colorPacketPerm_apply]
    exact classOfComplex_eq U
      ((packetTwistComparison Q step hstep N hN orient μ A ho hμ δ hA hroot hPF E.complex v).toHomotopyEquivalence U)

lemma classLabel_packet_inverse (hn : ∀ b, Q.source b ≠ Q.target b) (v:V)
    (x : FiniteHomotopyClass U (K := K)) :
    F ((colorPacketPerm Q step hstep N hN hn v).symm x) =
      (colorPacketPerm Q step hstep N hN hn v).symm (F x) := by
  let π := colorPacketPerm Q step hstep N hN (K := K) hn v
  apply π.injective
  change π (F (π.symm x)) = π (π.symm (F x))
  rw [π.apply_symm_apply,← classLabel_packet Q step hstep N hN orient μ A ho hμ δ hA hroot hPF hn v,
    π.apply_symm_apply]

end HarmonicArtin.ReversibleQuiver.StringFunctor

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Functors_SignedPacketPerm
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable
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
local notation "U" => Q.stringQuiver step hstep N hN
open Zigzag.BasedComplex

variable (hn : ∀ b, Q.source b ≠ Q.target b)

noncomputable def signedPacketPerm (a : V × Bool) :
    Equiv.Perm (FiniteHomotopyClass U (K := K)) :=
  if a.2 then colorPacketPerm Q step hstep N hN hn a.1
  else (colorPacketPerm Q step hstep N hN hn a.1).symm

noncomputable def wordPacketPerm : List (V × Bool) →
    Equiv.Perm (FiniteHomotopyClass U (K := K))
  | [] => 1
  | a :: w => signedPacketPerm Q step hstep N hN hn a * wordPacketPerm w

variable {I : Type u} [Fintype I] [DecidableEq I]
lemma signedPacketPerm_sum (a : V × Bool) (x : I → FiniteHomotopyClass U (K := K)) :
    signedPacketPerm Q step hstep N hN hn a (classSum U x) =
      classSum U (fun i => signedPacketPerm Q step hstep N hN hn a (x i)) := by
  unfold signedPacketPerm colorPacketPerm
  cases a.2 <;> simp only [Bool.false_eq_true,ite_false, if_false,ite_true, if_true]
  · exact classPacketPerm_inverse_sum U _ _ _ x
  · exact classPacketPerm_sum U _ _ _ x

lemma wordPacketPerm_sum (w : List (V × Bool)) (x : I → FiniteHomotopyClass U (K := K)) :
    wordPacketPerm Q step hstep N hN hn w (classSum U x) =
      classSum U (fun i => wordPacketPerm Q step hstep N hN hn w (x i)) := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    change signedPacketPerm Q step hstep N hN hn a
      (wordPacketPerm Q step hstep N hN hn w (classSum U x)) = _
    rw [ih,signedPacketPerm_sum]
    rfl

variable (orient : B → Bool) (μ : J → K) (A : K)
  (ho : ∀ b, orient (Q.reverse b) = !(orient b))
  (hμ : ∀ a, μ a ≠ 0) (δ : K)
  (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
  (hPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, μ b = δ * μ a)
local notation "F" => classLabelFunctor Q step hstep N hN orient μ A ho hμ δ hA hroot hPF

lemma classLabel_signedPacket (a : V × Bool) (x : FiniteHomotopyClass U (K := K)) :
    F (signedPacketPerm Q step hstep N hN hn a x) =
      signedPacketPerm Q step hstep N hN hn a (F x) := by
  unfold signedPacketPerm
  cases a.2 <;> simp only [Bool.false_eq_true,ite_false, if_false,ite_true, if_true]
  · exact classLabel_packet_inverse Q step hstep N hN orient μ A ho hμ δ hA hroot hPF hn a.1 x
  · exact classLabel_packet Q step hstep N hN orient μ A ho hμ δ hA hroot hPF hn a.1 x

lemma classLabel_wordPacket (w : List (V × Bool)) (x : FiniteHomotopyClass U (K := K)) :
    F (wordPacketPerm Q step hstep N hN hn w x) =
      wordPacketPerm Q step hstep N hN hn w (F x) := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    change F (signedPacketPerm Q step hstep N hN hn a (wordPacketPerm Q step hstep N hN hn w x)) = _
    rw [classLabel_signedPacket,ih]
    rfl

lemma classLabel_wordOrbit (w : List (V × Bool)) (v : V) (c : J) :
    F (wordPacketPerm Q step hstep N hN hn w (initialClass U (v,c))) =
      classSum U (fun a : {a : J // N c a} =>
        wordPacketPerm Q step hstep N hN hn w (initialClass U (v,a))) := by
  rw [classLabel_wordPacket,classLabel_initial,wordPacketPerm_sum]

end HarmonicArtin.ReversibleQuiver.StringFunctor

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Functors_WordPacketPermAppend
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.StringFunctor
open Zigzag.BasedComplex

universe u
attribute [local instance] Classical.propDecidable
variable {V B J : Type u} {K : Type*} (Q : ReversibleQuiver V B)
  (step : B → Bool) (hstep : ∀ b, step (Q.reverse b) = step b)
  (N : J → J → Prop) (hN : ∀ ⦃first second⦄, N first second → N second first)
  [Fintype V] [Fintype B] [Fintype J]
  [DecidableEq V] [DecidableEq B] [DecidableEq J] [DecidableRel N] [Field K]
  (hn : ∀ b, Q.source b ≠ Q.target b)
local notation "W" => wordPacketPerm Q step hstep N hN (K:=K) hn

lemma wordPacketPerm_append (w z:List (V × Bool)) : W (w++z)=W w * W z := by
  induction w with
  | nil => exact (_root_.one_mul _).symm
  | cons a w ih => simp only [List.cons_append,wordPacketPerm,ih,_root_.mul_assoc]

lemma wordPacketPerm_positive (w:List V) :
    W (w.map fun v=>(v,true)) = (w.map (colorPacketPerm Q step hstep N hN hn)).prod := by
  induction w with
  | nil => rfl
  | cons v w ih => simp only [List.map_cons,List.prod_cons,wordPacketPerm,ih,signedPacketPerm,↓reduceIte]

lemma signedPacketPerm_inverse (a:V × Bool) :
    signedPacketPerm Q step hstep N hN (K:=K) hn (a.1,!a.2) =
      (signedPacketPerm Q step hstep N hN hn a)⁻¹ := by
  cases a with | mk v b => cases b <;> rfl

lemma wordPacketPerm_inverse (w:List (V × Bool)) :
    W (w.reverse.map fun a=>(a.1,!a.2))=(W w)⁻¹ := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    simp only [List.reverse_cons,List.map_append,List.map_cons,List.map_nil,
      wordPacketPerm_append,wordPacketPerm,_root_.mul_one,ih,
      signedPacketPerm_inverse,mul_inv_rev]

end HarmonicArtin.ReversibleQuiver.StringFunctor

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Functors_LayerIndexEquiv
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable
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
local notation "F" => classLabelFunctor Q step hstep N hN orient μ A ho hμ δ hA hroot hPF

variable {T : Type u} [Fintype T] [DecidableEq T]
def layerIndexEquiv (p : T → GeneratorPlacement (V × J)) (d : ℤ) :
    Index N (fun i : {i // (p i).level=d} => p i) ≃
      {i : Index N p // (placement N p i).level=d} where
  toFun x := ⟨⟨x.1.val,x.2⟩,x.1.property⟩
  invFun x := ⟨⟨x.1.1,x.2⟩,x.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

omit [DecidableEq T] in
lemma layer_eq (E : Zigzag.BasedComplex U (K := K) T) (hE : E.IsMinimal U) (d : ℤ) :
    ((C E).pureLayer U (complex_minimal Q step hstep N hN orient μ A ho hμ δ hA hroot hPF E hE) d).reindex U
      (layerIndexEquiv N E.placement d) = C (E.pureLayer U hE d) := by
  apply ext_placement_differential U
  · rfl
  · rfl

noncomputable def layerComparison (E : Zigzag.BasedComplex U (K := K) T)
    (hE : E.IsMinimal U) (d : ℤ) :
    ChainIsomorphism U
      ((C E).pureLayer U (complex_minimal Q step hstep N hN orient μ A ho hμ δ hA hroot hPF E hE) d)
      (C (E.pureLayer U hE d)) := by
  have e := reindexChainIsomorphism U
    ((C E).pureLayer U (complex_minimal Q step hstep N hN orient μ A ho hμ δ hA hroot hPF E hE) d)
    (layerIndexEquiv N E.placement d)
  rw [layer_eq] at e
  exact e

lemma classLabel_complex (E : Zigzag.BasedComplex U (K := K) T) :
    F (classOfComplex U E) = classOfComplex U (C E) := rfl

end HarmonicArtin.ReversibleQuiver.StringFunctor

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Functors_LevelGeneratorEquiv
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable
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
  (N : J → J → Prop) (hN : ∀ ⦃first second : J⦄, N first second → N second first)
  [Fintype V] [Fintype B] [Fintype J]
  [DecidableEq V] [DecidableEq B] [DecidableEq J] [DecidableRel N] [Field K]
local notation "U" => Q.stringQuiver step hstep N hN
open Zigzag.BasedComplex

variable (orient : B → Bool) (μ : J → K) (A : K)
  (ho : ∀ b, orient (Q.reverse b) = !(orient b))
  (hμ : ∀ a, μ a ≠ 0) (δ : K)
  (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
  (hPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, μ b = δ * μ a)
local notation "C" => complex Q step hstep N hN orient μ A ho hμ δ hA hroot hPF
local notation "F" => classLabelFunctor Q step hstep N hN orient μ A ho hμ δ hA hroot hPF

variable {T : Type u} [Fintype T] [DecidableEq T]
def levelGeneratorEquiv (p : T → GeneratorPlacement (V × J)) (v:V) (j:J) (d:ℤ) :
    {i : Index N p // (placement N p i).color=(v,j) ∧ (placement N p i).level=d} ≃
      (Σ a : {a:J // N a j}, {i:T // (p i).color=(v,(a:J)) ∧ (p i).level=d}) where
  toFun x := ⟨⟨(p x.val.1).color.2,by
      have hj := congrArg Prod.snd x.property.1
      change x.val.2.val=j at hj
      simpa only [← hj] using x.val.2.property⟩,
    x.val.1,⟨Prod.ext (by have h := congrArg Prod.fst x.property.1; exact h) rfl,x.property.2⟩⟩
  invFun x := ⟨⟨x.2.val,⟨j,by simpa only [x.2.property.1] using x.1.property⟩⟩,
    ⟨Prod.ext (by have h := congrArg Prod.fst x.2.property.1; exact h) rfl,x.2.property.2⟩⟩
  left_inv x := by
    apply Subtype.ext
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      apply Subtype.ext
      exact (congrArg Prod.snd x.property.1).symm
  right_inv x := by
    apply Sigma.ext
    · apply Subtype.ext
      exact congrArg Prod.snd x.2.property.1
    · have ha := congrArg Prod.snd x.2.property.1
      dsimp only at ha
      apply (Subtype.heq_iff_coe_eq (fun i => by simp only [ha])).mpr
      rfl

omit [DecidableEq T] in
lemma levelArray_label (E : Zigzag.BasedComplex U (K := K) T) (v:V) (j:J) (d:ℤ) :
    (C E).levelArray U ((v,j),d) = ∑ a : {a:J // N a j}, E.levelArray U ((v,a),d) := by
  simp_rw [levelArray_apply]
  erw [Nat.card_congr (levelGeneratorEquiv N E.placement v j d)]
  simp only [Nat.card_eq_fintype_card,Fintype.card_sigma]

lemma classLevelArray_label (x : FiniteHomotopyClass U (K := K)) (v:V) (j:J) (d:ℤ) :
    classLevelArray U (F x) ((v,j),d) =
      ∑ a : {a:J // N a j}, classLevelArray U x ((v,a),d) := by
  let E := (minimalClassModel U x).complex
  have hE := minimalClassModel_minimal U x
  have hx : classOfComplex U E = x := minimalClassModel_class U x
  conv_lhs => rw [← hx,classLabel_complex]
  rw [classLevelArray_complex_minimal U _
    (complex_minimal Q step hstep N hN orient μ A ho hμ δ hA hroot hPF E hE)]
  conv_rhs => rw [← hx,classLevelArray_complex_minimal U E hE]
  exact levelArray_label Q step hstep N hN orient μ A ho hμ δ hA hroot hPF E v j d

end HarmonicArtin.ReversibleQuiver.StringFunctor

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Functors_WordOrbitCountAdjacency
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf
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
local notation "U" => Q.stringQuiver step hstep N hN
open Zigzag.BasedComplex

variable (hn : ∀ b, Q.source b ≠ Q.target b)
  (orient : B → Bool) (μ : J → K) (A : K)
  (ho : ∀ b, orient (Q.reverse b) = !(orient b))
  (hμ : ∀ a, μ a ≠ 0) (δ : K)
  (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
  (hPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, μ b = δ * μ a)
local notation "O" => (fun (w : List (V × Bool)) (s : V) (a : J) =>
  wordPacketPerm Q step hstep N hN hn w (initialClass U (K := K) (s,a)))

include ho hμ hA hroot hPF

lemma wordOrbit_count_adjacency (w : List (V × Bool)) (s v : V) (d : ℤ) (i j : J) :
    (∑ a : {a // N a j}, classLevelArray U (O w s i) ((v,a),d)) =
      ∑ a : {a // N i a}, classLevelArray U (O w s a) ((v,j),d) := by
  rw [← classLevelArray_label Q step hstep N hN orient μ A ho hμ δ hA hroot hPF]
  rw [classLabel_wordOrbit Q step hstep N hN hn orient μ A ho hμ δ hA hroot hPF,
    classLevelArray_sum]
  simp

variable [Nonempty J]
  (hconn : ∀ a b, Relation.ReflTransGen N a b)
  (ρ : J → ℝ) (hρ : ∀ a, 0 < ρ a) (θ : ℝ)
  (hρPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, ρ b = θ * ρ a)

include hconn hρ hρPF

theorem wordOrbit_count_proportional (w : List (V × Bool)) (s v : V) (d : ℤ) :
    ∃ r : ℝ, 0 ≤ r ∧ ∀ j,
      (∑ i, ρ i * (classLevelArray U (O w s i) ((v,j),d) : ℝ)) = r * ρ j := by
  apply GraphConnection.nonnegative_eigenvector_proportional N hconn ρ hρ θ hρPF
  · exact GraphConnection.weighted_intertwiner N hN ρ θ hρPF _
      (wordOrbit_count_adjacency Q step hstep N hN hn orient μ A ho hμ δ hA hroot hPF w s v d)
  · intro j
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (le_of_lt (hρ i)) (Nat.cast_nonneg _)

end HarmonicArtin.ReversibleQuiver.StringFunctor

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_StringAdjacent
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin

namespace ReversibleQuiver
variable {V B : Type} (Q : ReversibleQuiver V B)
  [Fintype V] [Fintype B] [DecidableEq V] [DecidableEq B]

noncomputable def fixedOrientation (b : B) : Bool :=
  decide (Fintype.equivFin B b < Fintype.equivFin B (Q.reverse b))

omit [Fintype V] [DecidableEq V] [DecidableEq B] in
lemma fixedOrientation_reverse (hn : ∀ b, Q.source b ≠ Q.target b) (b:B) :
    Q.fixedOrientation (Q.reverse b) = !(Q.fixedOrientation b) := by
  have hne : Q.reverse b ≠ b := by
    intro h
    have hs := Q.source_reverse b
    rw [h] at hs
    exact hn b hs
  have hc : Fintype.equivFin B b ≠ Fintype.equivFin B (Q.reverse b) :=
    fun h => hne ((Fintype.equivFin B).injective h).symm
  by_cases h : Fintype.equivFin B b < Fintype.equivFin B (Q.reverse b)
  · have h' := not_lt_of_ge (le_of_lt h)
    simp [fixedOrientation,Q.reverse_reverse,h,h']
  · have h' : Fintype.equivFin B (Q.reverse b) < Fintype.equivFin B b :=
      lt_of_le_of_ne (le_of_not_gt h) hc.symm
    simp [fixedOrientation,Q.reverse_reverse,h,h']

namespace StringFunctor
open Zigzag.BasedComplex

variable (step : B → Bool) (hstep : ∀ b, step (Q.reverse b) = step b)
  (hn : ∀ b, Q.source b ≠ Q.target b) (m : ℕ) (hm : 2 ≤ m)
local notation "N" => stringAdjacent m
local notation "hN" => stringAdjacent_symm m
local notation "U" => Q.stringQuiver step hstep N hN
local notation "O" => (fun (w : List (V × Bool)) (s : V) (a : StringLabel m) =>
  wordPacketPerm Q step hstep N hN hn w (initialClass U (K := ℂ) (s,a)))

include hm

include hn hm

theorem string_wordOrbit_count_proportional (w : List (V × Bool)) (s v : V) (d : ℤ) :
    ∃ r : ℝ, 0 ≤ r ∧ ∀ j,
      (∑ i, stringWeight m i * (classLevelArray U (O w s i) ((v,j),d) : ℝ)) =
        r * stringWeight m j := by
  have : NeZero (m-1) := ⟨by omega⟩
  obtain ⟨A,hA,hr,hμ,hPF⟩ := string_connection_exists m hm
  exact wordOrbit_count_proportional Q step hstep N hN hn Q.fixedOrientation
    (fun a => (stringWeight m a : ℂ)) A (Q.fixedOrientation_reverse hn) hμ
    (2 * Real.cos (Real.pi/m) : ℝ) hA hr hPF (stringAdjacent_connected m)
    (stringWeight m) (stringWeight_pos hm) _ (stringAdjacent_weight m hm) w s v d

end StringFunctor
end ReversibleQuiver
end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_FusionFactorStep
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.unfoldedHom_simple _root_.OAI.HarmonicArtin.unfoldedMatrix_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq
variable {E V : Type} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m:E → ℕ) (e:E) (d:V → V → FusionEdge E) (hd:∀ s t,d s t=d t s)

local notation "mr" => (fun f:FusionRest e => m f)
local notation "dr" => (fun s t => FusionEdge.removeFactor e (d s t))
local notation "Qr" => fusionQuiver mr dr (restEdge_symm e d hd)
local notation "Q" => fusionQuiver m d hd

omit [Fintype V] [DecidableEq V] in
lemma fusionFactorStep_reverse (a:FusionQuiverArrow mr dr) :
    fusionFactorStep m e d ((Qr).reverse a) = fusionFactorStep m e d a := by
  change (d a.1.2.1 a.1.1.1).usesFactor e = (d a.1.1.1 a.1.2.1).usesFactor e
  rw [hd]

local notation "step" => fusionFactorStep m e d
local notation "N" => stringAdjacent (m e)
local notation "U" => ReversibleQuiver.stringQuiver Qr step (fusionFactorStep_reverse m e d hd) N (stringAdjacent_symm (m e))

noncomputable def fusionArrowSplit (a:FusionQuiverArrow m d) : StringArrow step N := by
  have hM := (d a.1.1.1 a.1.2.1).multiplicity_split m e a.1.1.2 a.1.2.2
  have hP : if (d a.1.1.1 a.1.2.1).usesFactor e then N (a.1.1.2 e) (a.1.2.2 e)
      else a.1.1.2 e=a.1.2.2 e := by
    by_contra h
    have hk : 0 < (d a.1.1.1 a.1.2.1).multiplicity m a.1.1.2 a.1.2.2 := Nat.zero_lt_of_lt a.2.isLt
    rw [hM,ite_eq_right h] at hk
    exact Nat.lt_irrefl 0 hk
  have hk : a.2.val < ((d a.1.1.1 a.1.2.1).removeFactor e).multiplicity mr
      (restLabel m e a.1.1.2) (restLabel m e a.1.2.2) := by
    exact lt_of_lt_of_le a.2.isLt (le_of_eq (hM.trans (ite_eq_left hP)))
  exact ⟨(⟨((a.1.1.1,restLabel m e a.1.1.2),(a.1.2.1,restLabel m e a.1.2.2)),⟨a.2.val,hk⟩⟩,
    a.1.1.2 e,a.1.2.2 e),hP⟩

noncomputable def fusionArrowJoin (a:StringArrow step N) : FusionQuiverArrow m d := by
  let α := (fusionVertexSplit (V:=V) m e).symm ((Qr).source a.base,a.left)
  let β := (fusionVertexSplit (V:=V) m e).symm ((Qr).target a.base,a.right)
  refine ⟨(α,β),⟨a.base.2.val,?_⟩⟩
  have hM := (d α.1 β.1).multiplicity_split m e α.2 β.2
  dsimp [α,β,fusionVertexSplit] at hM ⊢
  simp only [labelSplit_symm_at,labelSplit_symm_rest] at hM
  rw [hM]
  change a.base.2.val < (if (if step a.base then N a.left a.right else a.left=a.right) then
    ((d a.base.1.1.1 a.base.1.2.1).removeFactor e).multiplicity mr a.base.1.1.2 a.base.1.2.2 else 0)
  have hp : if step a.base then N a.left a.right else a.left=a.right := a.property
  exact lt_of_lt_of_le a.base.2.isLt (le_of_eq (ite_eq_left hp).symm)

omit [Fintype V] [DecidableEq V] in
lemma fusionArrowJoin_split (a:FusionQuiverArrow m d) :
    fusionArrowJoin m e d hd (fusionArrowSplit m e d a) = a := by
  apply fusionArrow_ext
  · exact Prod.ext rfl ((labelSplit m e).symm_apply_apply a.1.1.2)
  · exact Prod.ext rfl ((labelSplit m e).symm_apply_apply a.1.2.2)
  · rfl

omit [Fintype V] [DecidableEq V] in
lemma fusionArrowSplit_join (a:StringArrow step N) :
    fusionArrowSplit m e d (fusionArrowJoin m e d hd a) = a := by
  apply StringArrow.ext
  · apply fusionArrow_ext
    · exact Prod.ext rfl (labelSplit_symm_rest m e _ _)
    · exact Prod.ext rfl (labelSplit_symm_rest m e _ _)
    · rfl
  · exact labelSplit_symm_at m e _ _
  · exact labelSplit_symm_at m e _ _

noncomputable def fusionQuiverSplit : Iso Q U where
  vertex := fusionVertexSplit m e
  arrow :=
    { toFun := fusionArrowSplit m e d
      invFun := fusionArrowJoin m e d hd
      left_inv := fusionArrowJoin_split m e d hd
      right_inv := fusionArrowSplit_join m e d hd }
  source _ := rfl
  target _ := rfl
  reverse a := by
    apply StringArrow.ext
    · apply fusionArrow_ext <;> rfl
    · rfl
    · rfl

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_FusionPacketPerm
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable
variable {E V : Type} {K:Type*} [Field K]
  [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m:E → ℕ) (d:V → V → FusionEdge E) (hd:∀ s t,d s t=d t s)
  (hdiag:∀ s,d s s=.units 0)
local notation "hn" => fusionQuiver_no_loops m d hd hdiag

variable (e:E)
local notation "mr" => (fun f:FusionRest e => m f)
local notation "dr" => (fun s t=>FusionEdge.removeFactor e (d s t))

local notation "Qr" => fusionQuiver mr dr (restFusion_symmetric d hd e)
local notation "hnr" => fusionQuiver_no_loops mr dr (restFusion_symmetric d hd e) (restFusion_diagonal d hdiag e)
local notation "step" => fusionFactorStep m e d
local notation "hstep" => fusionFactorStep_reverse m e d hd
local notation "N" => stringAdjacent (m e)
local notation "hN" => stringAdjacent_symm (m e)
local notation "U" => ReversibleQuiver.stringQuiver Qr step hstep N hN
local notation "F" => ReversibleQuiver.Iso.classMap (fusionQuiverSplit m e d hd) (K:=K)
local notation "W" => StringFunctor.wordPacketPerm Qr step hstep N hN (K:=K) hnr

lemma fusionPacket_split (s:V) : ∃ w:List (FusionVertex (V:=V) mr × Bool),
    ∀ x, F (fusionPacketPerm m d hd hdiag s x) = W w (F x) := by
  let v : (FusionLabel mr × StringLabel (m e)) → FusionVertex (V:=V) mr × StringLabel (m e) :=
    fun p=>((s,p.1),p.2)
  have hv : Pairwise fun a b=>OrthogonalVertices U (v a) (v b) := by
    rintro ⟨a,i⟩ ⟨b,j⟩ hab
    have h := (fusionQuiverSplit m e d hd).orthogonal
      (fusionQuiver_same_color m d hd hdiag s ((labelSplit m e).symm (a,i))
        ((labelSplit m e).symm (b,j)) (fun h=>hab ((labelSplit m e).symm.injective h)))
    simpa only [fusionQuiverSplit,fusionVertexSplit,Equiv.coe_fn_mk,
      labelSplit_symm_at,labelSplit_symm_rest,v] using h
  obtain ⟨l,hl⟩ := exists_packetGroupWord U
    ((fusionQuiverSplit m e d hd).loopless hn) (K:=K) v hv
  refine ⟨l.map fun r=>((s,r),true),?_⟩
  intro x
  rw [fusionPacketPerm,(fusionQuiverSplit m e d hd).classMap_packet]
  erw [classPacketPerm_reindex U _ _ _ (labelSplit m e).symm]
  have he : (fun a=> (fusionQuiverSplit m e d hd).vertex (s,(labelSplit m e).symm a)) = v := by
    funext a
    exact Prod.ext (Prod.ext rfl (labelSplit_symm_rest m e a.1 a.2))
      (labelSplit_symm_at m e a.1 a.2)
  have hp : classPacketPerm U (K:=K) ((fusionQuiverSplit m e d hd).loopless hn)
      (((fusionQuiverSplit m e d hd).vertex ∘ fun L=>(s,L)) ∘ (labelSplit m e).symm)
      (fun a b hab=>(fusionQuiverSplit m e d hd).orthogonal
        (fusionColor_orthogonal m d hd hdiag s
          (fun hh=>hab ((labelSplit m e).symm.injective hh)))) =
      classPacketPerm U ((fusionQuiverSplit m e d hd).loopless hn) v hv := by
    congr 1
  erw [hp]
  rw [hl]
  have hw := StringFunctor.wordPacketPerm_positive Qr step hstep N hN (K:=K) hnr
    (l.map (fun r=>(s,r)))
  simp only [List.map_map] at hw
  erw [hw]
  rfl

lemma fusionSignedPacket_split (a:V × Bool) : ∃ w:List (FusionVertex (V:=V) mr × Bool),
    ∀ x, F (fusionSignedPacketPerm m d hd hdiag a x) = W w (F x) := by
  obtain ⟨w,hw⟩ := fusionPacket_split m d hd hdiag e (K:=K) a.1
  cases hb:a.2
  · refine ⟨w.reverse.map (fun z=>(z.1,!z.2)),?_⟩
    intro x
    rw [StringFunctor.wordPacketPerm_inverse]
    apply (W w).injective
    change W w (F (fusionSignedPacketPerm m d hd hdiag a x)) = W w ((W w).symm (F x))
    rw [Equiv.apply_symm_apply]
    erw [← hw]
    simp only [fusionSignedPacketPerm,hb]
    change F (fusionPacketPerm m d hd hdiag a.1
      ((fusionPacketPerm m d hd hdiag a.1).symm x)) = F x
    rw [Equiv.apply_symm_apply]
  · refine ⟨w,?_⟩
    simpa only [fusionSignedPacketPerm,hb,↓reduceIte] using hw

lemma fusionWord_split (w:List (V × Bool)) : ∃ z:List (FusionVertex (V:=V) mr × Bool),
    ∀ x, F (fusionWordPacketPerm m d hd hdiag w x) = W z (F x) := by
  induction w with
  | nil => exact ⟨[],fun _=>rfl⟩
  | cons a w ih =>
    obtain ⟨z,hz⟩ := ih
    obtain ⟨t,ht⟩ := fusionSignedPacket_split m d hd hdiag e (K:=K) a
    refine ⟨t++z,?_⟩
    intro x
    change F (fusionSignedPacketPerm m d hd hdiag a (fusionWordPacketPerm m d hd hdiag w x)) = _
    rw [ht,hz,StringFunctor.wordPacketPerm_append]
    rfl

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Coxeter_AlternatingLiftProd
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex CoxeterExchange

attribute [local instance] Classical.decEq Classical.propDecidable

variable {E V : Type} {K : Type*} [Field K]
  [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m : E → ℕ) (d : V → V → FusionEdge E) (hd : ∀ s t,d s t=d t s)
  (hdiag : ∀ s,d s s=.units 0)

lemma fusionWordPacketPerm_positive (w : List V) :
    fusionWordPacketPerm m d hd hdiag (K:=K) (w.map fun s => (s,true))=
      (w.map (fusionPacketPerm m d hd hdiag)).prod := by
  induction w with
  | nil => rfl
  | cons i w ih => simp only [List.map_cons,List.prod_cons,fusionWordPacketPerm,
      fusionSignedPacketPerm,ite_true, if_true,ih]

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Coxeter_OrdinaryTwistBraid
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.linearMap_pathBasis _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_base _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_left _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
open CoxeterExchange

universe u
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  (hn : ∀ a,Q.source a≠Q.target a)

lemma ordinaryTwist_braid (α β : V) :
    ((altList α β (ordinaryCoxeterMatrix Q α β)).map (classTwistPerm Q (K:=K) hn)).prod=
      ((altList β α (ordinaryCoxeterMatrix Q α β)).map (classTwistPerm Q hn)).prod := by
  by_cases he : α=β
  · subst β; rfl
  by_cases ho : OrthogonalVertices Q α β
  · rw [ordinaryCoxeterMatrix_orthogonal Q ho]
    simpa only [altList_succ,altList_zero,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,
      _root_.mul_one] using classTwistPerm_orthogonal Q hn ho
  by_cases ha : Nonempty (SimpleEdge Q α β)
  · obtain ⟨edge⟩ := ha
    rw [ordinaryCoxeterMatrix_adjacent Q edge]
    simpa only [altList_succ,altList_zero,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,
      _root_.mul_one,_root_.mul_assoc] using classTwistPerm_adjacent Q hn edge
  · have hzero : ordinaryCoxeterMatrix Q α β=0 := by simp [ordinaryCoxeterMatrix,he,ho,ha]
    rw [hzero]
    rfl

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Functors_ComplexLowerTruncation
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

omit [Fintype V] [Fintype W] [DecidableEq A] [DecidableEq B] in
lemma classMap_lowerTruncation (x:FiniteHomotopyClass Q (K:=K)) (d:ℤ) :
    e.classMap (classLowerTruncation Q d x)=classLowerTruncation R d (e.classMap x) := by
  let E:=(minimalClassModel Q x).complex
  have hE:=minimalClassModel_minimal Q x
  have hx:classOfComplex Q E=x:=minimalClassModel_class Q x
  rw [← hx,classMap_complex,classLowerTruncation_minimal Q E hE d,
    classLowerTruncation_minimal R (e.complex E) (e.complex_minimal hE) d,
    classMap_complex,e.complex_lowerTruncation]
  rfl

end HarmonicArtin.ReversibleQuiver.Iso

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Functors_ComplexPureLayer
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable
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

omit [Fintype V] [Fintype W] [DecidableEq A] [DecidableEq B] in
lemma classMap_layer (x:FiniteHomotopyClass Q (K := K)) (d:ℤ) :
    e.classMap (classLayer Q d x) = classLayer R d (e.classMap x) := by
  let E := (minimalClassModel Q x).complex
  have hE := minimalClassModel_minimal Q x
  have hx : classOfComplex Q E = x := minimalClassModel_class Q x
  rw [← hx,classMap_complex,classLayer_minimal Q E hE d,
    classLayer_minimal R (e.complex E) (e.complex_minimal hE) d,classMap_complex,e.complex_pureLayer]
  rfl

end HarmonicArtin.ReversibleQuiver.Iso

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Functors_HomDimensionFlexible
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Functors_TwistProdGeneratorExterior
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_FusionExpandedWordAction
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {E V : Type} {K : Type*} [Field K]
  [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m : E → ℕ) (d : V → V → FusionEdge E) (hd : ∀ s t,d s t=d t s)
  (hdiag : ∀ s,d s s=.units 0)
local notation "Q" => fusionQuiver m d hd
local notation "hn" => fusionQuiver_no_loops m d hd hdiag

lemma fusionExpandedWord_action (w : List V) (x : FiniteHomotopyClass Q (K:=K)) :
    positiveWordAction Q (fusionExpandedWord m w) x=
      fusionWordPacketPerm m d hd hdiag (w.map fun s => (s,true)) x := by
  induction w generalizing x with
  | nil => rfl
  | cons s w ih =>
    change positiveWordAction Q (((Finset.univ : Finset (FusionLabel m)).toList.map (fun L => (s,L)))++
      fusionExpandedWord m w) x=_
    rw [positiveWordAction_append,ih,positiveWordAction_eq_prod Q hn,List.map_map,Function.comp_def,
      classPacketPerm_toList Q hn (fun L => (s,L)) (fusionColor_orthogonal m d hd hdiag s)]
    rfl

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_FusionExpandedWordPerm
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {E V : Type} {K : Type*} [Field K]
  [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m : E → ℕ) (d : V → V → FusionEdge E) (hd : ∀ s t,d s t=d t s)
  (hdiag : ∀ s,d s s=.units 0)
local notation "Q" => fusionQuiver m d hd
local notation "hn" => fusionQuiver_no_loops m d hd hdiag

lemma fusionExpandedWord_perm (w : List V) :
    ((fusionExpandedWord m w).map (classTwistPerm Q (K:=K) hn)).prod=
      fusionWordPacketPerm m d hd hdiag (w.map fun s => (s,true)) := by
  apply Equiv.ext
  intro x
  rw [← positiveWordAction_eq_prod Q hn,fusionExpandedWord_action]

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_SphericalPacketWordProperty
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex CoxeterExchange

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] {K : Type*} [Field K]
  (M : CoxeterMatrix S)
local notation "Q" => fusionQuiver (fusionLabelSize M) (coxeterFusionEdge M) (coxeterFusionEdge_symm M)
local notation "hn" => fusionQuiver_no_loops (fusionLabelSize M) (coxeterFusionEdge M)
  (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M)
local notation "P" => fusionWordPacketPerm (fusionLabelSize M) (coxeterFusionEdge M)
  (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M) (K:=K)

theorem spherical_packet_word_property (J : Set S) (hJ : IsSpherical M J)
    (u v : List J) (hu : (restrictedMatrix M J).toCoxeterSystem.IsReduced u)
    (hv : (restrictedMatrix M J).toCoxeterSystem.IsReduced v)
    (he : (restrictedMatrix M J).toCoxeterSystem.wordProd u=
      (restrictedMatrix M J).toCoxeterSystem.wordProd v) :
    P ((u.map fun j : J => (Sum.inl (j:S) : S⊕Unit)).map fun s => (s,true))=
      P ((v.map fun j : J => (Sum.inl (j:S) : S⊕Unit)).map fun s => (s,true)) := by
  let f := fun α : J × FusionLabel (fusionLabelSize M) => classTwistPerm Q (K:=K) hn
    (unfoldedInclusion M J α)
  have hb : ∀ α β,((altList α β (unfoldedMatrix M J α β)).map f).prod=
      ((altList β α (unfoldedMatrix M J α β)).map f).prod := by
    intro α β
    have hh := ordinaryTwist_braid Q (K:=K) hn (unfoldedInclusion M J α) (unfoldedInclusion M J β)
    rw [unfolded_ordinaryMatrix M J hJ] at hh
    simpa only [← altList_map,List.map_map,Function.comp_def,f] using hh
  have hh := reduced_word_property (unfoldedMatrix M J).toCoxeterSystem f hb
    (fusionExpandedWord (fusionLabelSize M) u) (fusionExpandedWord (fusionLabelSize M) v)
    (unfolded_reducedWord M J hJ u hu) (unfolded_reducedWord M J hJ v hv)
    (unfolded_word_eq M J hJ u v he)
  rw [← fusionExpandedWord_perm,← fusionExpandedWord_perm]
  simp only [fusionExpandedWord_map,List.map_map,Function.comp_def,unfoldedInclusion,f] at hh ⊢
  convert hh using 1 <;> first | (with_reducible_and_instances rfl) | (congr 3)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_ArtinAction
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.restrictedArtinHom_generator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex CoxeterExchange

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] {K : Type*} [Field K]
  (M : CoxeterMatrix S)
local notation "Q" => fusionQuiver (fusionLabelSize M) (coxeterFusionEdge M) (coxeterFusionEdge_symm M)
local notation "T" => fusionPacketPerm (fusionLabelSize M) (coxeterFusionEdge M)
  (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M) (K:=K)

theorem sourcePacket_braid (i j : S) :
    ((altList i j (M i j)).map fun s => T (Sum.inl s)).prod=
      ((altList j i (M i j)).map fun s => T (Sum.inl s)).prod := by
  by_cases hij : i=j
  · subst j; rfl
  by_cases hz : M i j=0
  · rw [hz]; rfl
  have hm : 2≤M i j := by have hh:=M.off_diagonal i j hij; omega
  let J : Set S := {i,j}
  let a : J := ⟨i,by simp [J]⟩
  let b : J := ⟨j,by simp [J]⟩
  have hab : a≠b := fun h => hij (congrArg Subtype.val h)
  have hJ : IsSpherical M J := spherical_pair M i j hm
  have hu := altList_reduced (restrictedMatrix M J).toCoxeterSystem a b hab (M i j)
    (Or.inr (le_refl (M i j)))
  have hv := altList_reduced (restrictedMatrix M J).toCoxeterSystem b a hab.symm (M i j)
    (Or.inr (le_of_eq (M.symmetric i j)))
  have he := altList_braid (restrictedMatrix M J).toCoxeterSystem a b
  have hh := spherical_packet_word_property M (K:=K) J hJ
    (altList a b (M i j)) (altList b a (M i j)) hu hv he
  rw [fusionWordPacketPerm_positive,fusionWordPacketPerm_positive] at hh
  simp only [altList_map,a,b] at hh
  simpa only [← altList_map,List.map_map,Function.comp_def] using hh

lemma sourcePacket_relators : ∀ r∈braidRelators M,
    FreeGroup.lift (fun s => T (Sum.inl s)) r=1 := by
  rintro r ⟨⟨i,j⟩,rfl⟩
  rw [map_mul,map_inv]
  apply mul_inv_eq_one.mpr
  rw [alternating_lift_prod,alternating_lift_prod]
  exact sourcePacket_braid M (K:=K) i j

noncomputable def sourceArtinAction :
    Artin M →* Equiv.Perm (FiniteHomotopyClass Q (K:=K)) :=
  PresentedGroup.toGroup (sourcePacket_relators M (K:=K))

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_FusionPacketOrbit
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable
variable {E V : Type} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m:E → ℕ) (d:V → V → FusionEdge E) (hd:∀ s t,d s t=d t s)
  (hdiag:∀ s,d s s=.units 0)
local notation "Q" => fusionQuiver m d hd

variable (e:E)
local notation "mr" => (fun f:FusionRest e => m f)
local notation "dr" => (fun s t=>FusionEdge.removeFactor e (d s t))
local notation "Qr" => fusionQuiver mr dr (restFusion_symmetric d hd e)
local notation "hnr" => fusionQuiver_no_loops mr dr (restFusion_symmetric d hd e) (restFusion_diagonal d hdiag e)
local notation "step" => fusionFactorStep m e d
local notation "hstep" => fusionFactorStep_reverse m e d hd
local notation "N" => stringAdjacent (m e)
local notation "hN" => stringAdjacent_symm (m e)
local notation "U" => ReversibleQuiver.stringQuiver Qr step hstep N hN
local notation "F" => ReversibleQuiver.Iso.classMap (fusionQuiverSplit m e d hd) (K:=ℂ)
local notation "W" => StringFunctor.wordPacketPerm Qr step hstep N hN (K:=ℂ) hnr
local notation "O" => fusionPacketOrbit m d hd hdiag

lemma fusionOrbit_split (w:List (V × Bool)) : ∃ z:List (FusionVertex (V:=V) mr × Bool),
    ∀ s L,F (O w s L)=W z (initialClass U ((s,restLabel m e L),L e)) := by
  obtain ⟨z,hz⟩ := fusionWord_split m d hd hdiag e (K:=ℂ) w
  refine ⟨z,fun s L=>?_⟩
  rw [fusionPacketOrbit,hz,(fusionQuiverSplit m e d hd).classMap_initial]
  rfl

variable (hm:∀ e,2 ≤ m e)

include hm in
lemma fusionOrbit_count_slice (w:List (V × Bool)) (s v:V) (q:ℤ)
    (r t:FusionLabel mr) : ∃ c:ℝ, ∀ j,
    (∑ i,stringWeight (m e) i *
      (classLevelArray Q (O w s ((labelSplit m e).symm (t,i))) ((v,(labelSplit m e).symm (r,j)),q):ℝ)) =
        c*stringWeight (m e) j := by
  obtain ⟨z,hz⟩ := fusionOrbit_split m d hd hdiag e w
  obtain ⟨c,hc,h⟩ := StringFunctor.string_wordOrbit_count_proportional Qr step hstep hnr (m e) (hm e)
    z (s,t) (v,r) q
  refine ⟨c,fun j=>?_⟩
  calc
    _ = ∑ i,stringWeight (m e) i * (classLevelArray U (W z (initialClass U ((s,t),i))) (((v,r),j),q):ℝ) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← (fusionQuiverSplit m e d hd).classMap_levelArray,hz]
      simp only [fusionQuiverSplit,fusionVertexSplit,Equiv.coe_fn_mk,
        labelSplit_symm_at,labelSplit_symm_rest]
    _ = _ := h j

include hm

theorem fusionPacketOrbit_count_proportional (w:List (V × Bool)) (s v:V) (q:ℤ) :
    ∃ c:ℝ,0 ≤ c ∧ ∀ L,
      (∑ H,fusionWeight m H*(classLevelArray Q (O w s H) ((v,L),q):ℝ)) =
        c*fusionWeight m L :=
  fusion_weighted_matrix_proportional m hm _
    (fun e=>fusionOrbit_count_slice m d hd hdiag e hm w s v q)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_FusionOrbitModel
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable
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

lemma fusionOrbitModel_minimal (w:List (V × Bool)) (s:V) (L:FusionLabel m) :
    (fusionOrbitModel m d hd hdiag w s L).complex.IsMinimal Q :=
  minimalClassModel_minimal Q _

noncomputable def fusionOrbitLayer (w:List (V × Bool)) (s:V) (L:FusionLabel m) (q:ℤ) :
    BasedComplex Q (K:=ℂ) (FusionOrbitLayerIndex m d hd hdiag w s L q) :=
  (fusionOrbitModel m d hd hdiag w s L).complex.pureLayer Q
     (fusionOrbitModel_minimal m d hd hdiag w s L) q

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_FusionOrbitMultiplicity
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open _root_.Matrix _root_.OAI.Matrix
open scoped _root_.Matrix _root_.OAI.Matrix BigOperators

attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable

variable {E V:Type} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m:E → ℕ) (d:V → V → FusionEdge E) (hd:∀ s t,d s t=d t s)
  (hdiag:∀ s,d s s=.units 0) (hm:∀ e,2 ≤ m e)
local notation "Q" => fusionQuiver m d hd
local notation "Y" => fusionOrbitLayer m d hd hdiag

noncomputable def fusionOrbitMultiplicity (w:List (V × Bool)) (s:V) (q:ℤ) (v:V) : ℝ :=
  Classical.choose (fusionPacketOrbit_count_proportional m d hd hdiag hm w s v q)

noncomputable def fusionOrbitWeightedVector (w:List (V × Bool)) (s:V) (q:ℤ) :
    FusionVertex (V:=V) m → ℝ := ∑ L,fusionWeight m L • generatorVector Q (Y w s L q)

lemma fusionOrbitLayer_generator (w:List (V × Bool)) (s:V) (q:ℤ) (H:FusionLabel m)
    (α:FusionVertex (V:=V) m) : generatorVector Q (Y w s H q) α =
      (classLevelArray Q (fusionPacketOrbit m d hd hdiag w s H) (α,q):ℝ) :=
  generatorVector_minimalLayer Q _ _ _

lemma fusionOrbitWeightedVector_eq (w:List (V × Bool)) (s:V) (q:ℤ) :
    fusionOrbitWeightedVector m d hd hdiag w s q =
      fusionFold m (fusionOrbitMultiplicity m d hd hdiag hm w s q) := by
  ext ⟨v,L⟩
  simp only [fusionOrbitWeightedVector,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  have hc:= (Classical.choose_spec (fusionPacketOrbit_count_proportional m d hd hdiag hm w s v q)).2 L
  simpa only [fusionOrbitLayer_generator,fusionFold,
    fusionOrbitMultiplicity,mul_comm] using hc

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_FusionColorRegion
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open _root_.Matrix _root_.OAI.Matrix
open scoped _root_.Matrix _root_.OAI.Matrix BigOperators

attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable
variable {E V:Type} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m:E → ℕ) (d:V → V → FusionEdge E) (hd:∀ s t,d s t=d t s)
  (hdiag:∀ s,d s s=.units 0)
local notation "Q" => fusionQuiver m d hd
local notation "Y" => fusionOrbitLayer m d hd hdiag

noncomputable def fusionOrbitColorLayer (w:List (V × Bool)) (s:V) (q:ℤ) (U:Set V)
    (hb:∀ L i,((Y w s L q).placement i).color∉colorBoundary Q (fusionColorRegion m U))
    (L:FusionLabel m) :=
  colorRestriction Q (Y w s L q) (fusionColorRegion m U) (fun i=>i.property) (hb L)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_DimensionPosMultiplicityPos
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open _root_.Matrix _root_.OAI.Matrix
open scoped _root_.Matrix _root_.OAI.Matrix BigOperators

attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable
variable {E V:Type} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m:E → ℕ) (d:V → V → FusionEdge E) (hd:∀ s t,d s t=d t s)
  (hdiag:∀ s,d s s=.units 0) (hm:∀ e,2 ≤ m e)
local notation "Q" => fusionQuiver m d hd
local notation "Y" => fusionOrbitLayer m d hd hdiag
local notation "C" => fusionFoldedCartan m d
local notation "a" => fusionOrbitMultiplicity m d hd hdiag hm

lemma fusionOrbitMultiplicity_pos_at_generator (w:List (V × Bool)) (s:V) (q:ℤ)
    (H:FusionLabel m) (i:FusionOrbitLayerIndex m d hd hdiag w s H q) :
    0<a w s q ((Y w s H q).placement i).color.1 := by
  let α:=((Y w s H q).placement i).color
  have hg:0<generatorVector Q (Y w s H q) α := by
    unfold generatorVector
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast Fintype.card_pos_iff.mpr (show Nonempty {j | ((Y w s H q).placement j).color=α} from ⟨i,rfl⟩)
  have hs:0<fusionOrbitWeightedVector m d hd hdiag w s q α := by
    apply lt_of_lt_of_le (mul_pos (fusionWeight_pos m hm H) hg)
    change fusionWeight m H * generatorVector Q (Y w s H q) α ≤
      (∑ T,fusionWeight m T • generatorVector Q (Y w s T q)) α
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    apply Finset.single_le_sum _ (Finset.mem_univ H)
    intro T _
    exact mul_nonneg (fusionWeight_pos m hm T).le (generatorVector_nonneg Q _ _)
  rw [fusionOrbitWeightedVector_eq m d hd hdiag hm] at hs
  exact (mul_pos_iff_of_pos_left (fusionWeight_pos m hm α.2)).mp hs

lemma fusionOrbit_boundary_absent (w:List (V × Bool)) (s:V) (q:ℤ) (U:Set V)
    (hz:∀ b,b∉U → (∃ v∈U,C b v<0) → a w s q b=0) :
    ∀ L i,((Y w s L q).placement i).color∉colorBoundary Q (fusionColorRegion m U) := by
  intro L i hi
  rcases hi with ⟨hi,r,hr,he⟩
  have hb:((Y w s L q).placement i).color.1∉U:=hi
  have hu:r.1.1.1∈U:=hr
  have he':r.1.2=((Y w s L q).placement i).color:=he
  have hn:r.1.1.1≠r.1.2.1 := by
    intro hh
    rw [hh,he'] at hu
    exact hb hu
  have hneg:=fusion_arrow_color_cartan_neg m d hm r hn
  rw [fusionFoldedCartan_symm m d hd] at hneg
  rw [he'] at hneg
  have hc:=hz _ hb ⟨r.1.1.1,hu,hneg⟩
  have hp:=fusionOrbitMultiplicity_pos_at_generator m d hd hdiag hm w s q L i
  exact hp.ne' hc

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_IsolatedBoundaryAbsent
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open _root_.Matrix _root_.OAI.Matrix CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "hd" => coxeterFusionEdge_symm M
local notation "hdiag" => coxeterFusionEdge_diag M
local notation "hm" => (fun e=>le_trans (by norm_num) (fusionLabelSize_ge_four M e))
local notation "Q" => fusionQuiver m d hd
local notation "Y" => fusionOrbitLayer m d hd hdiag
local notation "μ" => fusionOrbitMultiplicity m d hd hdiag hm
local notation "C" => fusionFoldedCartan m d

lemma source_isolated_boundary_absent (I J:Set S) (z:List ((S⊕Unit)×Bool))
    (s:S⊕Unit) (q:ℤ) (c:S⊕Unit→ℝ)
    (hcSupp:∀ v,v∉Sum.inl '' I→c v=0)
    (hdata:∀ v,(v∈Sum.inl '' I ∧ v∉Sum.inl '' J) ∨
      (v∉Sum.inl '' I ∧ ∃ u∈Sum.inl '' I,C v u<0)→μ z s q v=c v) :
    ∀ L i,((Y z s L q).placement i).color∉colorBoundary Q (fusionColorRegion m (Sum.inl '' I)) := by
  apply fusionOrbit_boundary_absent m d hd hdiag hm z s q (Sum.inl '' I)
  intro v hv ha
  exact (hdata v (Or.inr ⟨hv,ha⟩)).trans (hcSupp v hv)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_IsolatedIterationData
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open _root_.Matrix _root_.OAI.Matrix

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "hd" => coxeterFusionEdge_symm M
local notation "hdiag" => coxeterFusionEdge_diag M
local notation "hm" => (fun e=>le_trans (by norm_num) (fusionLabelSize_ge_four M e))
local notation "Q" => fusionQuiver m d hd
local notation "O" => fusionPacketOrbit m d hd hdiag
local notation "Y" => fusionOrbitLayer m d hd hdiag
local notation "μ" => fusionOrbitMultiplicity m d hd hdiag hm
local notation "C" => fusionFoldedCartan m d

structure IsolatedIterationData where
  I : Set S
  J : Set S
  hJI : J⊆I
  hJ : IsSpherical M J
  s : S⊕Unit
  q : ℤ
  c : S⊕Unit→ℝ
  hc : ∀ v,0 ≤ c v
  hcSupp : ∀ v,v∉Sum.inl '' I→c v=0
  hcPos : ∀ v,v∈Sum.inl '' I→0 < c v
  hcNull : ∀ v,v∈Sum.inl '' I→(C *ᵥ c) v=0
  valid : List ((S⊕Unit)×Bool)→Prop
  move : ∀ z,valid z→∀ j:J,valid ((.inl j,true)::z)
  data : ∀ z,valid z→∀ v,(v∈Sum.inl '' I ∧ v∉Sum.inl '' J) ∨
    (v∉Sum.inl '' I ∧ ∃ u∈Sum.inl '' I,C v u<0)→μ z s q v=c v
  strict : ∀ z,valid z→∀ g∈artinParabolic M J,
    (∀ L,ClassCapOn Q (sourceArtinAction M g (O z s L))
      (closedNeighborhood Q (Set.range (unfoldedInclusion M J))) q)→
    ∀ j:J,c (.inl (j:S))<fusionFamilyMultiplicity m d hd hm
      (fun L=>sourceArtinAction M g (O z s L)) q (.inl (j:S))

namespace IsolatedIterationData
variable {M} (D:IsolatedIterationData M)

abbrev region : Set (FusionVertex (V:=S⊕Unit) m) := fusionColorRegion m (Sum.inl '' D.I)
abbrev operated : Set (FusionVertex (V:=S⊕Unit) m) := fusionColorRegion m (Sum.inl '' D.J)
def capped (z:List ((S⊕Unit)×Bool)) : Prop :=
  ∀ L,ClassCapOn Q (O z D.s L) (closedNeighborhood Q D.region) D.q
def openSocle (z:List ((S⊕Unit)×Bool)) (k:ℤ) : Prop :=
  ∀ H,ClassBottomSocleZero Q k D.operated (O z D.s H)

lemma boundary (z:List ((S⊕Unit)×Bool)) (hz:D.valid z) :
    ∀ L i,((Y z D.s L D.q).placement i).color∉colorBoundary Q D.region :=
  source_isolated_boundary_absent M D.I D.J z D.s D.q D.c D.hcSupp (D.data z hz)

noncomputable abbrev fullRegion (z:List ((S⊕Unit)×Bool)) (hz:D.valid z) (L:FusionLabel m) :=
  fusionOrbitColorLayer m d hd hdiag z D.s D.q (Sum.inl '' D.I) (D.boundary z hz) L

end IsolatedIterationData
end HarmonicArtin

end OAI
end


