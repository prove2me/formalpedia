-- Prove2me | Definitions.Def_OAIQ225Ag011
-- name    : OAIQ225Ag011
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T17:33:57.968408+00:00
-- url     : https://prove2.me/theorems/3568c802-0448-43bd-bdf3-020f09e604b8
-- title:
--   Definitions bundle OAIQ225Ag011 of the split of OpenAI, Harmonic heights and the Artin K(pi,1) conjecture
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.HarmonicArtin.salvetti_cover_contractible`, carved from OpenAI's openai/math development (OpenAI, *Harmonic heights and the Artin K(pi,1) conjecture*, OpenAI Math Release, September 23, 2026, result family 254, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 182 declarations of OpenAI's Lean: 65 definitions, 2 inductive types or structures and 115 theorems. The definitions and types are `OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.expressionAction`, `OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.truncationComparison`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.HomotopyEquivalence.ofPure`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.TermwiseSplitInjection.colorTarget`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeTwistReduction`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.canonicalLowMap`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.canonicalLowSource`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.canonicalWordLow`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.cappedSummandInjection`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.coneLayerIsomorphism`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.frameModel`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.highConeRetainedPureIndex`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeIndexEquiv`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeIndexMap`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudePivot`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeTwistReduction`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.normalizedNegativeAmplitudeTwist`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.reducedAmplitudeTwist`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.reducedNegativeAmplitudeTwist`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.sumLayerComparison`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.summandSecondaryClass`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.summandSecondaryOnCycles`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.unfoldedArtinAction`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.unfoldedFrame`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.upperTruncation`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.wordLowModel`, `OAI.HarmonicArtin.SourceAllEligibleLower`, `OAI.HarmonicArtin.SourceBlockOccurs`, `OAI.HarmonicArtin.SourceCandidate`, `OAI.HarmonicArtin.SourceCappedCandidate`, `OAI.HarmonicArtin.SourceCosetOrbit`, `OAI.HarmonicArtin.SourceEarlier`, `OAI.HarmonicArtin.SourceEarlierLower`, `OAI.HarmonicArtin.SourceEarlierUpper`, `OAI.HarmonicArtin.SourceEligible`, `OAI.HarmonicArtin.SourceEligibleWithin`, `OAI.HarmonicArtin.SourceResidue`, `OAI.HarmonicArtin.SourceResidueAllowed`, `OAI.HarmonicArtin.SourceResidueEarlier`, `OAI.HarmonicArtin.SourceResidueEarlierLower` and 27 more.
--
--   **Sources.** They come from these modules of lean/OAI/Topology, in whole or in part: `ArtinGroups_Complexes_ActedIndex`, `ArtinGroups_Complexes_CanonicalWordLow`, `ArtinGroups_Complexes_CoefficientTopDual`, `ArtinGroups_Complexes_ColorSupport`, `ArtinGroups_Complexes_DownClosed`, `ArtinGroups_Complexes_HighConeRetainedPure`, `ArtinGroups_Complexes_HomMono`, `ArtinGroups_Complexes_Initial`, `ArtinGroups_Complexes_InverseMatrix`, `ArtinGroups_Complexes_InverseWordAction`, `ArtinGroups_Complexes_LowerTruncation`, `ArtinGroups_Complexes_LowerTruncationSum`, `ArtinGroups_Complexes_MinimalGeneratorDualCycle`, `ArtinGroups_Complexes_MinimalModel`, `ArtinGroups_Complexes_NegativeAmplitudeCoreIndex`, `ArtinGroups_Complexes_NegativeTwistModern`, `ArtinGroups_Complexes_OutsideCap`, `ArtinGroups_Complexes_PacketPermExterior`, `ArtinGroups_Complexes_PositiveTopDivisor`, `ArtinGroups_Complexes_PositiveTwistLowerBound`, `ArtinGroups_Complexes_PositiveWord`, `ArtinGroups_Complexes_PositiveWordActionOrthogonal`, `ArtinGroups_Complexes_PositiveWordLowerBound`, `ArtinGroups_Complexes_PureCoefficientCohomology`, `ArtinGroups_Complexes_PureLayerSelf`, `ArtinGroups_Complexes_ReducedAmplitudeTwistLevel`, `ArtinGroups_Complexes_ReducedNegativeAmplitudeTwist`, `ArtinGroups_Complexes_ReducedNoTopDivisor`, `ArtinGroups_Complexes_ScalarKernel`, `ArtinGroups_Complexes_SecondaryLayer`, `ArtinGroups_Complexes_Shift`, `ArtinGroups_Complexes_SumTestEquiv`, `ArtinGroups_Complexes_SumTruncationEquiv`, `ArtinGroups_Complexes_SummandSecondary`, `ArtinGroups_Complexes_TargetLow`, `ArtinGroups_Complexes_TotalVectorLayer`, `ArtinGroups_Complexes_UnfoldedPresentation`, `ArtinGroups_Complexes_UpperBound`, `ArtinGroups_Complexes_WordInverseModel`, `ArtinGroups_Coxeter_CanonicalReducedWordLow`, `ArtinGroups_Coxeter_PositiveBraidRel`, `ArtinGroups_Functors_LayerIndexEquiv`, `ArtinGroups_Functors_TruncationIndexEquiv`, `ArtinGroups_Harmonic_AllEligibleLower`, `ArtinGroups_Harmonic_ArtinReindex`, `ArtinGroups_Harmonic_Block`, `ArtinGroups_Harmonic_Candidate`, `ArtinGroups_Harmonic_CanonicalFusionLow`, `ArtinGroups_Harmonic_CanonicalFusionLowCount`, `ArtinGroups_Harmonic_CanonicalFusionLowExpansion`, `ArtinGroups_Harmonic_CanonicalFusionMultiplicity`, `ArtinGroups_Harmonic_CappedCandidate`, `ArtinGroups_Harmonic_CosetOrbit`, `ArtinGroups_Harmonic_CosetProfile`, `ArtinGroups_Harmonic_CosetSum`, `ArtinGroups_Harmonic_EarlierLower`, `ArtinGroups_Harmonic_EarlierUpper`, `ArtinGroups_Harmonic_Eligible`, `ArtinGroups_Harmonic_EligibleWithin`, `ArtinGroups_Harmonic_FrameFamily`, `ArtinGroups_Harmonic_FusionColorRegion`, `ArtinGroups_Harmonic_FusionExpressionAction`, `ArtinGroups_Harmonic_FusionExpressionOrbit`, `ArtinGroups_Harmonic_FusionZeroLabel`, `ArtinGroups_Harmonic_Harmonic`, `ArtinGroups_Harmonic_LayerExpression`, `ArtinGroups_Harmonic_MultiplicitySum`, `ArtinGroups_Harmonic_PeakSupport`, `ArtinGroups_Harmonic_PositiveComponent`, `ArtinGroups_Harmonic_ResidueActive`, `ArtinGroups_Harmonic_ResidueAllowed`, `ArtinGroups_Harmonic_ResidueEarlierLower`, `ArtinGroups_Harmonic_ResidueRank`, `ArtinGroups_Harmonic_TieCode`, `ArtinGroups_Harmonic_TypedRightCoset`, `ArtinGroups_Quivers_ProbeSimpleEdge`, `ArtinGroups_Quivers_VertexLinear`.
--
--   **Imports.** It imports the published bundle `Def_HarmonicArtin`; the bundles `OAIQ225Ag009` and `OAIQ225Ag010` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ225Ag013` and `OAIQ225Ag014`; the statements `OAI.HarmonicArtin.sourceClosedResidue_nonempty`, `OAI.HarmonicArtin.sourceEarlierLower_contractible`, `OAI.HarmonicArtin.sourcePositiveBlock_contractible`, `OAI.HarmonicArtin.sourceResidue_lower_weights_contractible` and `OAI.HarmonicArtin.sourceResidue_zero_ne_lower`.
-- source:
--   OpenAI, Harmonic heights and the Artin K(pi,1) conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 254; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Harmonic-heights-and-the-Artin-K-pi-1-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Topology at commit adc7f12

import Mathlib
import Definitions.Def_HarmonicArtin
import Definitions.Def_OAIQ225Ag009
import Definitions.Def_OAIQ225Ag010

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_ActedIndex
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

variable {V A K I : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I]

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
-- module Solutions.OAIQ225_AG.ArtinGroups_Quivers_VertexLinear
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

lemma tokenMatrix_matrixTwo_mul [Fintype J]
    (f : Matrix I J (Q.Zigzag K)) (g : Matrix J L (Q.Zigzag K)) :
    TokenMatrix Q (matrixTwo Q f * g) := by
  intro i k
  constructor
  · rw [Matrix.mul_apply, vertex_sum]
    apply Finset.sum_eq_zero
    intro j _
    rw [vertex_mul]
    exact MulZeroClass.zero_mul _
  · rw [Matrix.mul_apply, arrow_sum]
    apply Finset.sum_eq_zero
    intro j _
    rw [arrow_mul]
    ext a
    change (0 : K) * (g j k).arrow a + 0 * (g j k).vertex (Q.target a) = 0
    simp only [MulZeroClass.zero_mul, add_zero]

lemma tokenMatrix_mul_matrixTwo [Fintype J]
    (f : Matrix I J (Q.Zigzag K)) (g : Matrix J L (Q.Zigzag K)) :
    TokenMatrix Q (f * matrixTwo Q g) := by
  intro i k
  constructor
  · rw [Matrix.mul_apply, vertex_sum]
    apply Finset.sum_eq_zero
    intro j _
    rw [vertex_mul]
    exact MulZeroClass.mul_zero _
  · rw [Matrix.mul_apply, arrow_sum]
    apply Finset.sum_eq_zero
    intro j _
    rw [arrow_mul]
    ext a
    change (f i j).vertex (Q.source a) * (0 : K) + (f i j).arrow a * 0 = 0
    simp only [MulZeroClass.mul_zero, add_zero]

namespace BasedComplex
variable [Fintype I] [Fintype J]

lemma tokenHomDifferential_tokenMatrix (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (hE : E.IsMinimal Q) (hF : F.IsMinimal Q)
    (n : ℤ) (f : Matrix I J (Q.Zigzag K)) :
    TokenMatrix Q (tokenHomDifferential Q E F n f) := by
  rw [tokenHomDifferential_apply Q E F hE hF]
  exact tokenMatrix_sub Q (tokenMatrix_matrixTwo_mul Q _ _)
    (tokenMatrix_smul Q _ (tokenMatrix_mul_matrixTwo Q _ _))

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_SecondaryLayer
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

lemma secondaryLayer_token (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (hE : E.IsMinimal Q) (hF : F.IsMinimal Q)
    (q d n : ℤ)
    (f : Matrix {i // (E.placement i).level = q} {j // (F.placement j).level = d} (Q.Zigzag K)) :
    TokenMatrix Q (secondaryLayer Q E F q d n f) := by
  intro i j
  exact tokenHomDifferential_tokenMatrix Q E F hE hF n (extendLayer Q E F q d f) i.val j.val

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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_SummandSecondary
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_PureCoefficientCohomology
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.instPreorderLiftedCell _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype A] [DecidableEq V]
variable {I J T : Type*} [Fintype I] [Fintype J] [Fintype T]

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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_CoefficientTopDual
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_UnfoldedPresentation
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

universe u

variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

lemma unfoldedTwist_relators (hn : ∀ a, Q.source a ≠ Q.target a)
    (M : CoxeterMatrix V) (hM : UnfoldedPresentation Q M) :
    ∀ r ∈ braidRelators M,
      FreeGroup.lift (classTwistPerm Q (K := K) hn) r = 1 := by
  rintro r ⟨⟨α, β⟩, rfl⟩
  rw [map_mul, map_inv]
  apply mul_inv_eq_one.mpr
  rcases hM.relation α β with hab | hzero | ⟨htwo, ho⟩ | ⟨hthree, ⟨he⟩⟩
  · subst β
    rfl
  · simp only [hzero, alternating]
  · simp only [htwo, alternating, map_mul, FreeGroup.lift_apply_of, _root_.mul_one]
    exact classTwistPerm_orthogonal Q hn ho
  · simp only [hthree, alternating, map_mul, FreeGroup.lift_apply_of, _root_.mul_one]
    simpa only [_root_.mul_assoc] using classTwistPerm_adjacent Q (K := K) hn he

noncomputable def unfoldedArtinAction (hn : ∀ a, Q.source a ≠ Q.target a)
    (M : CoxeterMatrix V) (hM : UnfoldedPresentation Q M) :
    Artin M →* Equiv.Perm (FiniteHomotopyClass Q (K := K)) :=
  PresentedGroup.toGroup (unfoldedTwist_relators Q hn M hM)

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_Initial
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

noncomputable def unfoldedFrame (hn : ∀ a, Q.source a ≠ Q.target a)
    (M : CoxeterMatrix V) (hM : UnfoldedPresentation Q M) (x : Artin M) (α : V) :
    FiniteHomotopyClass Q (K := K) :=
  unfoldedArtinAction Q hn M hM x (initialClass Q α)

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_MinimalModel
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

noncomputable def frameModel (hn : ∀ a, Q.source a ≠ Q.target a)
    (M : CoxeterMatrix V) (hM : UnfoldedPresentation Q M) (x : Artin M) (α : V) :
    FiniteModel.{u} Q (K := K) := minimalClassModel Q (unfoldedFrame Q hn M hM x α)

lemma frameModel_minimal (hn : ∀ a, Q.source a ≠ Q.target a)
    (M : CoxeterMatrix V) (hM : UnfoldedPresentation Q M) (x : Artin M) (α : V) :
    (frameModel Q (K := K) hn M hM x α).complex.IsMinimal Q := minimalClassModel_minimal Q _

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_MinimalGeneratorDualCycle
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.linearMap_pathBasis _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_base _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_left _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_right _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.corner_val _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_reverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K I J : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V]
  [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

theorem minimal_generator_dual_cycle
    (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J)
    (hF : F.IsMinimal Q) (e : HomotopyEquivalence Q E F) (j : J) :
    ∃ x : I → K, x ≠ 0 ∧
      (∀ i, E.placement i ≠ F.placement j → x i = 0) ∧
      ∀ k, ∑ i, (E.differential k i).vertex (F.placement j).color * x i = 0 := by
  have hf0 i k w : (F.differential i k).vertex w = 0 := congrFun (hF i k) w
  let x : I → K := fun i => (e.forward.matrix i j).vertex (F.placement j).color
  refine ⟨x, ?_, ?_, ?_⟩
  · intro hx
    have he := congrArg (fun M : Matrix J J (Q.Zigzag K) =>
      (M j j).vertex (F.placement j).color) e.targetEquation
    have hz i : (e.forward.matrix i j).vertex (F.placement j).color = 0 :=
      congrFun hx i
    simp only [Matrix.mul_apply, Matrix.add_apply, vertex_add, Pi.add_apply, vertex_sum,
      Finset.sum_apply, vertex_mul, Pi.mul_apply, hf0, hz,
      MulZeroClass.zero_mul, MulZeroClass.mul_zero, Finset.sum_const_zero,
      add_zero] at he
    simp [projectiveIdentity] at he
  · intro i hi
    by_contra hn
    exact hi ((reduction_support Q e.forward.entries e.forward.degree i j
      (F.placement j).color hn).1)
  · intro k
    have he := congrArg (fun M : Matrix I J (Q.Zigzag K) =>
      (M k j).vertex (F.placement j).color) e.forward.commute
    simpa only [Matrix.mul_apply, vertex_sum, Finset.sum_apply, vertex_mul,
      Pi.mul_apply, hf0, Pi.zero_apply, MulZeroClass.mul_zero,
      Finset.sum_const_zero] using he

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_NegativeAmplitudeCoreIndex
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
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
lemma tokenTest_injective (E : BasedComplex Q (K := K) I) (α : V) :
    Function.Injective (tokenTest Q E α) := by
  intro i j h
  exact Subtype.ext (congrArg Sigma.fst h)

def negativeAmplitudeIndexMap (E : BasedComplex Q (K := K) I) (α : V) :
    ActedIndex Q E α ⊕ ActedIndex Q E α ⊕ NegativeAmplitudeCoreIndex Q E α →
      I ⊕ TestIndex Q E.placement α
  | .inl i => .inl i.val
  | .inr (.inl i) => .inr (tokenTest Q E α i)
  | .inr (.inr (.inl u)) => .inr u.val
  | .inr (.inr (.inr i)) => .inl i.val

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma negativeAmplitudeIndexMap_injective (E : BasedComplex Q (K := K) I) (α : V) :
    Function.Injective (negativeAmplitudeIndexMap Q E α) := by
  intro i j h
  rcases i with i | i | u | i <;> rcases j with j | j | v | j
  all_goals dsimp only [negativeAmplitudeIndexMap] at h
  all_goals try cases h
  · exact congrArg Sum.inl (Subtype.ext (Sum.inl.inj h))
  · exact (j.property ((Sum.inl.inj h) ▸ i.property)).elim
  · exact congrArg (fun x => Sum.inr (Sum.inl x)) (tokenTest_injective Q E α (Sum.inr.inj h))
  · have hv := v.property
    rw [← Sum.inr.inj h] at hv
    exact (hv rfl).elim
  · have hu := u.property
    rw [Sum.inr.inj h] at hu
    exact (hu rfl).elim
  · exact congrArg (fun x => Sum.inr (Sum.inr (Sum.inl x))) (Subtype.ext (Sum.inr.inj h))
  · exact (i.property ((Sum.inl.inj h).symm ▸ j.property)).elim
  · exact congrArg (fun x => Sum.inr (Sum.inr (Sum.inr x))) (Subtype.ext (Sum.inl.inj h))

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma negativeAmplitudeIndexMap_surjective (E : BasedComplex Q (K := K) I) (α : V) :
    Function.Surjective (negativeAmplitudeIndexMap Q E α) := by
  intro u
  rcases u with i | ⟨i, ⟨v | a | v, hs, ht⟩⟩
  · by_cases hi : (E.placement i).color = α
    · exact ⟨.inl ⟨i, hi⟩, rfl⟩
    · exact ⟨.inr (.inr (.inr ⟨i, hi⟩)), rfl⟩
  · exact ⟨.inr (.inr (.inl ⟨⟨i, ⟨.inl v, hs, ht⟩⟩, by norm_num [Path.length]⟩)), rfl⟩
  · exact ⟨.inr (.inr (.inl ⟨⟨i, ⟨.inr (.inl a), hs, ht⟩⟩, by norm_num [Path.length]⟩)), rfl⟩
  · dsimp only [Path.source, Path.target] at hs ht
    subst v
    exact ⟨.inr (.inl ⟨i, ht.symm⟩), rfl⟩

noncomputable def negativeAmplitudeIndexEquiv (E : BasedComplex Q (K := K) I) (α : V) :
    ActedIndex Q E α ⊕ ActedIndex Q E α ⊕ NegativeAmplitudeCoreIndex Q E α ≃
      I ⊕ TestIndex Q E.placement α :=
  Equiv.ofBijective (negativeAmplitudeIndexMap Q E α)
    ⟨negativeAmplitudeIndexMap_injective Q E α, negativeAmplitudeIndexMap_surjective Q E α⟩

noncomputable def normalizedNegativeAmplitudeTwist (E : BasedComplex Q (K := K) I) (α : V) :
    BasedComplex Q (K := K)
      (ActedIndex Q E α ⊕ ActedIndex Q E α ⊕ NegativeAmplitudeCoreIndex Q E α) :=
  (E.negativeTwist Q α).reindex Q (negativeAmplitudeIndexEquiv Q E α)

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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_ReducedNegativeAmplitudeTwist
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_UpperBound
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I J : Type u} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

omit [Fintype V] [DecidableEq A] in
lemma minimal_bound_transport (E:BasedComplex Q (K:=K) I)
    (F:BasedComplex Q (K:=K) J) (hF:F.IsMinimal Q)
    (e:HomotopyEquivalence Q E F) (P:GeneratorPlacement V→Prop)
    (h:∀ i,P (E.placement i)) : ∀ j,P (F.placement j) := by
  intro j
  obtain ⟨x,hx,hs,_⟩ := minimal_generator_dual_cycle Q E F hF e j
  have hex : ∃ i,x i≠0 := not_forall.mp (fun hh=>hx (funext hh))
  obtain ⟨i,hi⟩:=hex
  have hp:E.placement i=F.placement j := Classical.not_not.mp (fun hn=>hi (hs i hn))
  rw [← hp]
  exact h i

omit [Fintype V] [DecidableEq A] in
lemma classUpperBound_of_representative (E:BasedComplex Q (K:=K) I) {l:ℤ}
    (h:∀ i,(E.placement i).level≤l) : ClassUpperBound Q l (classOfComplex Q E) :=
  minimal_bound_transport Q E _ (minimalClassModel_minimal Q _)
    (minimalClassModelEquivalence Q E).symm (fun p=>p.level≤l) h

omit [Fintype V] [DecidableEq A] in
lemma classLowerBound_of_representative (E:BasedComplex Q (K:=K) I) {l:ℤ}
    (h:∀ i,l≤(E.placement i).level) : ClassLowerBound Q l (classOfComplex Q E) :=
  minimal_bound_transport Q E _ (minimalClassModel_minimal Q _)
    (minimalClassModelEquivalence Q E).symm (fun p=>l≤p.level) h

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

lemma classPositiveTwist_outside_cap (x:FiniteHomotopyClass Q (K:=K))
    (U:Set V) (d:ℤ) (α:V) (hα:α∈U) (h:ClassOutsideCap Q x U d) :
    ClassOutsideCap Q (classPositiveTwist Q α x) U d := by
  let E:=minimalClassModel Q x
  let F:=E.complex.positiveTwist Q α
  have hx:classOfComplex Q F=classPositiveTwist Q α x := by
    change classPositiveTwist Q α (classOfComplex Q E.complex)=_
    exact congrArg (classPositiveTwist Q α) (minimalClassModel_class Q x)
  rw [← hx]
  apply minimal_bound_transport Q F _ (minimalClassModel_minimal Q _)
    (minimalClassModelEquivalence Q F).symm (fun p=>p.color∉U→p.level≤d)
  intro i hi
  rcases i with j|j
  · exact (hi hα).elim
  · exact h j hi

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_ReducedAmplitudeTwistLevel
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_PositiveTwistLowerBound
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Coxeter_PositiveBraidRel
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A:Type u} (Q:ReversibleQuiver V A)

variable {K:Type*} [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

lemma PositiveBraidRel.action_eq (hn:∀ a,Q.source a≠Q.target a)
    {v w:List V} (h:PositiveBraidRel Q v w) (x:FiniteHomotopyClass Q (K:=K)) :
    positiveWordAction Q v x=positiveWordAction Q w x := by
  induction h with
  | refl => rfl
  | symm h ih => exact ih.symm
  | trans h k ih ik => exact ih.trans ik
  | cons α h ih => exact congrArg (classPositiveTwist Q α) ih
  | orthogonal h w =>
    exact congrArg (fun f:Equiv.Perm (FiniteHomotopyClass Q (K:=K))=>f (positiveWordAction Q w x))
      (classTwistPerm_orthogonal Q hn h)
  | adjacent e w =>
    exact congrArg (fun f:Equiv.Perm (FiniteHomotopyClass Q (K:=K))=>f (positiveWordAction Q w x))
      (classTwistPerm_adjacent Q hn e)

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_PositiveTopDivisor
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.instPreorderLiftedCell _root_.OAI.HarmonicArtin.liftedPartialOrder
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

theorem positive_top_divisor (hn:∀ a,Q.source a≠Q.target a)
    (U:Set V)
    (hU:∀ α∈U,∀ β∈U,α=β ∨ OrthogonalVertices Q α β ∨ Nonempty (SimpleEdge Q α β))
    (x:FiniteHomotopyClass Q (K:=K)) (t:ℤ) (hx:ClassTestUpper Q x U t)
    (w:List V) :
    (∀ s∈w,s∈U)→∀ β∈U,∀ l:ℤ,t<l→
      ClassTestUpper Q (positiveWordAction Q w x) U l→
      ∀ c:ℤ,¬ClassTestExact Q β l c (positiveWordAction Q w x)→
        ∃ v,PositiveBraidRel Q w (β::v) := by
  refine (measure (fun w:List V=>w.length)).wf.induction
    (C := fun w => (∀ s∈w,s∈U)→∀ β∈U,∀ l:ℤ,t<l→
      ClassTestUpper Q (positiveWordAction Q w x) U l→
      ∀ c:ℤ,¬ClassTestExact Q β l c (positiveWordAction Q w x)→
        ∃ v,PositiveBraidRel Q w (β::v)) w (fun w ih=>?_)
  intro hw β hβ l hl hout c htop
  cases w with
  | nil => exact (htop (hx β hβ l hl c)).elim
  | cons α w =>
    have hα:α∈U:=hw α (by simp)
    have hw':∀ s∈w,s∈U:=fun s hs=>hw s (List.mem_cons_of_mem _ hs)
    by_cases he:β=α
    · subst β
      exact ⟨w,PositiveBraidRel.refl _⟩
    have htail:ClassTestUpper Q (positiveWordAction Q w x) U l :=
      classPositiveTwist_testUpper_reflect Q hn _ U α hα hout
    have ha:∀ c,ClassTestExact Q α l c (positiveWordAction Q w x) :=
      (classPositiveTwist_testUpper_iff Q hn _ U α hα htail).mp hout
    have hb:¬ClassTestExact Q β l c (positiveWordAction Q w x) := by
      intro hz
      exact htop (classTestExact_positive_other Q _ α β he l c (ha (c+1)) hz)
    obtain ⟨v,hv⟩:=ih w (by change w.length<(α::w).length; simp) hw' β hβ l hl htail c hb
    rcases hU α hα β hβ with heq | hrest
    · exact (he heq.symm).elim
    rcases hrest with ho | hedge
    · exact ⟨α::v,PositiveBraidRel.trans (PositiveBraidRel.cons α hv)
        (PositiveBraidRel.orthogonal ho v)⟩
    obtain ⟨edge⟩ := hedge
    have hvU:∀ s∈v,s∈U := by
      have hh:=PositiveBraidRel.mem_set Q hv U hw'
      exact fun s hs=>hh s (List.mem_cons_of_mem _ hs)
    have hvlen:v.length<(α::w).length := by
      have hh:=PositiveBraidRel.length_eq Q hv
      simp only [List.length_cons] at *
      omega
    have htail':ClassTestUpper Q (classPositiveTwist Q β (positiveWordAction Q v x)) U l := by
      change ClassTestUpper Q (positiveWordAction Q (β::v) x) U l
      rw [← PositiveBraidRel.action_eq Q hn hv x]
      exact htail
    have hvbound:ClassTestUpper Q (positiveWordAction Q v x) U l :=
      classPositiveTwist_testUpper_reflect Q hn _ U β hβ htail'
    have htop':¬ClassTestExact Q β l c
        (classPositiveTwist Q α (classPositiveTwist Q β (positiveWordAction Q v x))) := by
      intro hz
      apply htop
      change ClassTestExact Q β l c (classPositiveTwist Q α (positiveWordAction Q w x))
      rw [PositiveBraidRel.action_eq Q hn hv x]
      exact hz
    have hαtop:¬ClassTestExact Q α l (c+1) (positiveWordAction Q v x) :=
      fun hz=>htop' ((classTestExact_positive_adjacent Q hn _ edge l c).mpr hz)
    obtain ⟨z,hz⟩:=ih v hvlen hvU α hα l hl hvbound (c+1) hαtop
    exact ⟨α::β::z,PositiveBraidRel.trans (PositiveBraidRel.cons α hv)
      (PositiveBraidRel.trans (PositiveBraidRel.cons α (PositiveBraidRel.cons β hz))
        (PositiveBraidRel.adjacent edge z))⟩

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_ReducedNoTopDivisor
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
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

theorem reducedWord_testUpper (hn:∀ a,Q.source a≠Q.target a)
    (U:Set V)
    (hU:∀ α∈U,∀ β∈U,α=β ∨ OrthogonalVertices Q α β ∨ Nonempty (SimpleEdge Q α β))
    (x:FiniteHomotopyClass Q (K:=K)) (t:ℤ) (hx:ClassTestUpper Q x U t)
    (w:List V) (hw:∀ s∈w,s∈U)
    (hr:(ordinaryCoxeterMatrix Q).toCoxeterSystem.IsReduced w) :
    ClassTestUpper Q (positiveWordAction Q w x) U (t+1) := by
  induction w with
  | nil => exact fun α hα l hl c=>hx α hα l (by omega) c
  | cons α w ih =>
    have hα:α∈U:=hw α (by simp)
    have hw':∀ s∈w,s∈U:=fun s hs=>hw s (List.mem_cons_of_mem _ hs)
    have hr':(ordinaryCoxeterMatrix Q).toCoxeterSystem.IsReduced w:=by
      simpa only [List.drop_succ_cons,List.drop_zero] using hr.drop 1
    have ht:=ih hw' hr'
    apply (classPositiveTwist_testUpper_iff Q hn _ U α hα ht).mpr
    intro c
    by_contra htop
    obtain ⟨v,hv⟩:=positive_top_divisor Q hn U hU x t hx w hw' α hα (t+1)
      (by omega) ht c htop
    exact reduced_no_top_divisor Q hr hv

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_PositiveWordLowerBound
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

lemma positiveWord_lower_bound (w:List V) (x:FiniteHomotopyClass Q (K:=K))
    {d:ℤ} (hx:ClassLowerBound Q d x) : ClassLowerBound Q d (positiveWordAction Q w x) := by
  induction w with
  | nil => exact hx
  | cons α w ih => exact classPositiveTwist_lower_bound Q α _ ih

lemma positiveWord_outside_cap (w:List V) (x:FiniteHomotopyClass Q (K:=K))
    (U:Set V) (d:ℤ) (hw:∀ s∈w,s∈U) (hx:ClassOutsideCap Q x U d) :
    ClassOutsideCap Q (positiveWordAction Q w x) U d := by
  induction w with
  | nil => exact hx
  | cons α w ih =>
    exact classPositiveTwist_outside_cap Q _ U d α (hw α (by simp))
      (ih (fun s hs=>hw s (List.mem_cons_of_mem _ hs)))

theorem reducedWord_layer_bounds (hn:∀ a,Q.source a≠Q.target a)
    (U:Set V)
    (hU:∀ α∈U,∀ β∈U,α=β ∨ OrthogonalVertices Q α β ∨ Nonempty (SimpleEdge Q α β))
    (x:FiniteHomotopyClass Q (K:=K)) (a b:ℤ)
    (hlo:ClassLowerBound Q a x) (hhi:ClassUpperBound Q b x)
    (w:List V) (hw:∀ s∈w,s∈U)
    (hr:(ordinaryCoxeterMatrix Q).toCoxeterSystem.IsReduced w) :
    ClassLowerBound Q a (positiveWordAction Q w x) ∧
      ClassUpperBound Q (b+1) (positiveWordAction Q w x) := by
  refine ⟨positiveWord_lower_bound Q w x hlo,?_⟩
  apply classUpperBound_of_test_and_outside Q _ U (b+1)
  · have he : b+2+1=(b+1)+2 := by omega
    rw [← he]
    exact reducedWord_testUpper Q hn U hU x (b+2)
      (classTestUpper_of_generator_cap Q x b hhi U) w hw hr
  · have hh:=positiveWord_outside_cap Q w x U b hw (classOutsideCap_of_upper Q x U b hhi)
    intro i hi
    have hb:=hh i hi
    omega

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_InverseWordAction
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
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

theorem inverseReducedWord_layer_bounds (hn:∀ a,Q.source a≠Q.target a)
    (U:Set V)
    (hU:∀ α∈U,∀ β∈U,α=β ∨ OrthogonalVertices Q α β ∨ Nonempty (SimpleEdge Q α β))
    (x:FiniteHomotopyClass Q (K:=K)) (a b:ℤ)
    (hlo:ClassLowerBound Q a x) (hhi:ClassUpperBound Q b x)
    (w:List V) (hw:∀ s∈w,s∈U)
    (hr:(ordinaryCoxeterMatrix Q).toCoxeterSystem.IsReduced w) :
    ClassLowerBound Q (a-1) (inverseWordAction Q w x) ∧
      ClassUpperBound Q b (inverseWordAction Q w x) := by
  refine ⟨?_,inverseWord_upper_bound Q w x hhi⟩
  apply classLowerBound_of_placed_vanishing Q _ (a-1)
  intro p hp
  let P:=classOfComplex Q (placedProjective Q (K:=K) p)
  have hPlo:ClassLowerBound Q p.level P :=
    classLowerBound_of_representative Q _ (fun _=>le_rfl)
  have hPhi:ClassUpperBound Q p.level P :=
    classUpperBound_of_representative Q _ (fun _=>le_rfl)
  have hcap:ClassUpperBound Q (p.level+1) (positiveWordAction Q w P) :=
    (reducedWord_layer_bounds Q hn U hU P p.level p.level hPlo hPhi w hw hr).2
  rw [← positiveWord_homDimension Q hn w P (inverseWordAction Q w x) 0 0,
    positive_inverseWord Q hn]
  exact classHomDimension_zero_of_layer_gap Q _ x (p.level+1) a hcap hlo (by omega)

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_DownClosed
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

noncomputable def upperTruncation (E:BasedComplex Q (K:=K) I) (hE:E.IsMinimal Q) (d:ℤ) :=
  highRestriction Q E (lowerLevelSet Q E d) (levelDownClosed Q E hE d)

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

omit [Fintype V] [DecidableEq A] in
lemma classLowerTruncation_cap (d:ℤ) (x:FiniteHomotopyClass Q (K:=K)) :
    ClassUpperBound Q d (classLowerTruncation Q d x) :=
  classUpperBound_of_representative Q _ (fun i=>i.property)

omit [Fintype V] [DecidableEq A] in
lemma classLowerTruncation_floor (d a:ℤ) (x:FiniteHomotopyClass Q (K:=K))
    (hx:ClassLowerBound Q a x) : ClassLowerBound Q a (classLowerTruncation Q d x) :=
  classLowerBound_of_representative Q _ (fun i=>hx i)

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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_CanonicalWordLow
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
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

lemma canonicalWordLow_floor (hn:∀ a,Q.source a≠Q.target a)
    (w:List V) (q:ℤ) (x:FiniteHomotopyClass Q (K:=K))
    (hx:ClassLowerBound Q q x) : ClassLowerBound Q q (canonicalWordLow Q w q x) := by
  apply classLowerBound_of_placed_vanishing Q _ q
  intro p hp
  let P:=classOfComplex Q (placedProjective Q (K:=K) p)
  let R:=inverseWordAction Q w P
  let N:=inverseWordAction Q w x
  have hP:ClassUpperBound Q p.level P:=
    classUpperBound_of_representative Q _ (fun _=>le_rfl)
  have hR:ClassUpperBound Q ((q-1)+1) R := by
    have hb:=inverseWord_upper_bound Q w P hP
    intro i
    exact le_trans (hb i) (by omega)
  have hz:classHomDimension Q 0 0 R N=0 := by
    rw [← positiveWord_homDimension Q hn w R N 0 0]
    change classHomDimension Q 0 0
      (positiveWordAction Q w (inverseWordAction Q w P))
      (positiveWordAction Q w (inverseWordAction Q w x))=0
    rw [positive_inverseWord Q hn,positive_inverseWord Q hn]
    exact classHomDimension_zero_of_layer_gap Q P x p.level q hP hx hp
  have ht:=classLowerTruncation_homDimension_zero Q R N (q-1) hR hz
  have ht':classHomDimension Q 0 0 (positiveWordAction Q w R)
      (positiveWordAction Q w (classLowerTruncation Q (q-1) N))=0 := by
    rw [positiveWord_homDimension Q hn]
    exact ht
  change classHomDimension Q 0 0 P (canonicalWordLow Q w q x)=0
  simpa only [R,N,positive_inverseWord Q hn,canonicalWordLow] using ht'

theorem canonicalReducedWordLow_pure (hn:∀ a,Q.source a≠Q.target a)
    (U:Set V)
    (hU:∀ α∈U,∀ β∈U,α=β ∨ OrthogonalVertices Q α β ∨ Nonempty (SimpleEdge Q α β))
    (x:FiniteHomotopyClass Q (K:=K)) (q:ℤ)
    (hlo:ClassLowerBound Q q x) (hhi:ClassUpperBound Q q x)
    (w:List V) (hw:∀ s∈w,s∈U)
    (hr:(ordinaryCoxeterMatrix Q).toCoxeterSystem.IsReduced w) :
    ClassLowerBound Q q (canonicalWordLow Q w q x) ∧
      ClassUpperBound Q q (canonicalWordLow Q w q x) := by
  refine ⟨canonicalWordLow_floor Q hn w q x hlo,?_⟩
  have hN:ClassLowerBound Q (q-1) (inverseWordAction Q w x):=
    (inverseReducedWord_layer_bounds Q hn U hU x q q hlo hhi w hw hr).1
  have hlow:=classLowerTruncation_floor Q (q-1) (q-1) (inverseWordAction Q w x) hN
  have hcap:=classLowerTruncation_cap Q (q-1) (inverseWordAction Q w x)
  have h:= (reducedWord_layer_bounds Q hn U hU
    (classLowerTruncation Q (q-1) (inverseWordAction Q w x)) (q-1) (q-1)
      hlow hcap w hw hr).2
  have he:q-1+1=q:=by omega
  rw [he] at h
  exact h

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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_Shift
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
  {I J L:Type u} [Fintype I] [Fintype J] [Fintype L]
  [DecidableEq I] [DecidableEq J] [DecidableEq L]

omit [Fintype V] [DecidableEq A] [DecidableEq J] [DecidableEq L] in
lemma derivedMono_postcompose_injective (E:BasedComplex Q (K:=K) I)
    (F:BasedComplex Q (K:=K) J) (G:BasedComplex Q (K:=K) L)
    {d q n v:ℤ} (hE:∀ i,(E.placement i).level=d)
    (hF:∀ j,(F.placement j).level=q) (h:n+v=q-d) (f:Map Q F G)
    (hm:∀ T:FiniteModel.{u} Q (K:=K),ClassUpperBound Q q (classOfComplex Q T.complex)→
      HomMonoFrom Q T.complex f) :
    Function.Injective (postcomposeOnCycles Q E F G f n v) := by
  apply (postcomposeOnCycles Q E F G f n v).ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro g hg
  have he:∀ i,((sourceShift Q E n v).placement i).level=q := by
    intro i
    have hh:=sourceShift_pure Q E n v hE i
    omega
  have hb:=hm (FiniteModel.ofComplex Q (sourceShift Q E n v))
    (classUpperBound_of_representative Q _ (fun i=>(he i).le)) g.val
    (sourceShift_cycle Q E F n v g.property)
  change g.val*f.matrix∈homBoundaries Q (sourceShift Q E n v) G 0 0 →
    g.val∈homBoundaries Q (sourceShift Q E n v) F 0 0 at hb
  have hp:g.val*f.matrix=0 := by
    have hh:=congrArg Subtype.val hg
    exact hh
  have hz:=hb (by rw [hp]; exact Submodule.zero_mem _)
  rw [pure_coefficient_boundaries_zero Q (sourceShift Q E n v) F he hF (by omega)] at hz
  apply Subtype.ext
  exact hz

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

lemma positiveWord_homMono (hn:∀ a,Q.source a≠Q.target a) (w:List V)
    (T E F:FiniteModel.{u} Q (K:=K)) (f:Map Q E.complex F.complex)
    (h:HomMonoFrom Q T.complex f) :
    HomMonoFrom Q (positiveWord Q w T).complex (positiveWordMap Q w f) := by
  induction w with
  | nil => exact h
  | cons α w ih => exact ih.positiveTwist Q hn α
end FiniteModel

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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_ColorSupport
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

lemma classNegativeTwist_outside_floor (x:FiniteHomotopyClass Q (K:=K))
    (U:Set V) (q:ℤ) (α:V) (hα:α∈U) (h:ClassOutsideFloor Q U q x) :
    ClassOutsideFloor Q U q (classNegativeTwist Q α x) := by
  let E:=minimalClassModel Q x
  let F:=E.complex.negativeTwist Q α
  have hx:classOfComplex Q F=classNegativeTwist Q α x := by
    change classNegativeTwist Q α (classOfComplex Q E.complex)=_
    exact congrArg (classNegativeTwist Q α) (minimalClassModel_class Q x)
  rw [← hx]
  apply minimal_bound_transport Q F _ (minimalClassModel_minimal Q _)
    ((minimalClassModelEquivalence Q F).symm Q) (fun p=>p.color∉U→q≤p.level)
  intro i hi
  rcases i with j|j
  · exact h j hi
  · exact (hi hα).elim

lemma inverseWord_outside_floor (w:List V) (x:FiniteHomotopyClass Q (K:=K))
    (U:Set V) (q:ℤ) (hw:∀ s∈w,s∈U) (h:ClassOutsideFloor Q U q x) :
    ClassOutsideFloor Q U q (inverseWordAction Q w x) := by
  induction w generalizing x with
  | nil => exact h
  | cons α w ih =>
    exact ih _ (fun s hs=>hw s (List.mem_cons_of_mem _ hs))
      (classNegativeTwist_outside_floor Q x U q α (hw α (by simp)) h)

lemma classPositiveTwist_colorSupport (x:FiniteHomotopyClass Q (K:=K))
    (U:Set V) (α:V) (hα:α∈U) (h:ClassColorSupport Q U x) :
    ClassColorSupport Q U (classPositiveTwist Q α x) := by
  let E:=minimalClassModel Q x
  let F:=E.complex.positiveTwist Q α
  have hx:classOfComplex Q F=classPositiveTwist Q α x := by
    change classPositiveTwist Q α (classOfComplex Q E.complex)=_
    exact congrArg (classPositiveTwist Q α) (minimalClassModel_class Q x)
  rw [← hx]
  apply minimal_bound_transport Q F _ (minimalClassModel_minimal Q _)
    ((minimalClassModelEquivalence Q F).symm Q) (fun p=>p.color∈U)
  intro i
  rcases i with j|j
  · exact hα
  · exact h j

lemma positiveWord_colorSupport (w:List V) (x:FiniteHomotopyClass Q (K:=K))
    (U:Set V) (hw:∀ s∈w,s∈U) (h:ClassColorSupport Q U x) :
    ClassColorSupport Q U (positiveWordAction Q w x) := by
  induction w with
  | nil => exact h
  | cons α w ih =>
    exact classPositiveTwist_colorSupport Q _ U α (hw α (by simp))
      (ih (fun s hs=>hw s (List.mem_cons_of_mem _ hs)))

lemma canonicalWordLow_colorSupport (w:List V) (x:FiniteHomotopyClass Q (K:=K))
    (U:Set V) (q:ℤ) (hw:∀ s∈w,s∈U) (hx:ClassLowerBound Q q x) :
    ClassColorSupport Q U (canonicalWordLow Q w q x) := by
  apply positiveWord_colorSupport Q w _ U hw
  have hf:=inverseWord_outside_floor Q w x U q hw (fun i _=>hx i)
  apply minimal_bound_transport Q _ _ (minimalClassModel_minimal Q _)
    ((minimalClassModelEquivalence Q
      (lowerTruncation Q (minimalClassModel Q (inverseWordAction Q w x)).complex
        (minimalClassModel_minimal Q _) (q-1))).symm Q) (fun p=>p.color∈U)
  intro i
  by_contra hi
  have hh:=hf i hi
  have hl:=i.property
  change ((minimalClassModel Q (inverseWordAction Q w x)).complex.placement i).level≤q-1 at hl
  omega

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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_InverseMatrix
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_HighConeRetainedPure
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_SumTestEquiv
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_SumTruncationEquiv
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_LowerTruncationSum
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

omit [Fintype V] [DecidableEq A] in
lemma classLowerTruncation_sum (d:ℤ) (x:I→FiniteHomotopyClass Q (K:=K)) :
    classLowerTruncation Q d (classSum Q x)=classSum Q (fun i=>classLowerTruncation Q d (x i)) := by
  classical
  let E (i:I):=(minimalClassModel Q (x i)).complex
  have hE (i:I):(E i).IsMinimal Q:=minimalClassModel_minimal Q (x i)
  have hx:x=fun i=>classOfComplex Q (E i):=funext fun i=>(minimalClassModel_class Q (x i)).symm
  rw [hx,classSum_complex,classLowerTruncation_minimal Q _ (finiteSum_minimal Q E hE)]
  simp_rw [classLowerTruncation_minimal Q _ (hE _)]
  rw [classSum_complex,← sumTruncation_eq]
  exact classOfComplex_reindex Q _ _

omit [Fintype V] [DecidableEq A] in
lemma classLayer_sum (d:ℤ) (x:I→FiniteHomotopyClass Q (K:=K)) :
    classLayer Q d (classSum Q x)=classSum Q (fun i=>classLayer Q d (x i)) := by
  classical
  let E (i:I):=(minimalClassModel Q (x i)).complex
  have hE (i:I):(E i).IsMinimal Q:=minimalClassModel_minimal Q (x i)
  have hx:x=fun i=>classOfComplex Q (E i):=funext fun i=>(minimalClassModel_class Q (x i)).symm
  rw [hx,classSum_complex,classLayer_minimal Q _ (finiteSum_minimal Q E hE)]
  simp_rw [classLayer_minimal Q _ (hE _)]
  rw [classSum_complex,← sumLayer_eq]
  exact classOfComplex_reindex Q _ _

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_NegativeTwistModern
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

omit [Fintype V] [DecidableEq A] in
lemma classLayer_upperBound (x:FiniteHomotopyClass Q (K:=K)) (q:ℤ) :
    ClassUpperBound Q q (classLayer Q q x) :=
  classUpperBound_of_representative Q _ (fun i=>le_of_eq i.property)

omit [Fintype V] [DecidableEq A] in
lemma classLayer_lowerBound (x:FiniteHomotopyClass Q (K:=K)) (q:ℤ) :
    ClassLowerBound Q q (classLayer Q q x) :=
  classLowerBound_of_representative Q _ (fun i=>le_of_eq i.property.symm)

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_PacketPermExterior
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
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

lemma classPacketPerm_exterior {J:Type u} [Fintype J] (v:J → V)
    (hv:Pairwise fun a b=>OrthogonalVertices Q (v a) (v b))
    (x:FiniteHomotopyClass Q (K:=K)) (a:GeneratorPlacement V)
    (ha:∀ j,v j≠a.color) :
    classGeneratorArray Q (classPacketPerm Q hn v hv x) a=classGeneratorArray Q x a := by
  suffices hh:∀ (J:Type u) [Fintype J] (v:J → V)
    (hv:Pairwise fun a b=>OrthogonalVertices Q (v a) (v b)),
    (∀ j,v j≠a.color) →
      classGeneratorArray Q (classPacketPerm Q hn v hv x) a=classGeneratorArray Q x a from
    hh J v hv ha
  intro J inst
  apply Fintype.induction_empty_option (P:=fun J _=>∀ (v:J → V)
    (hv:Pairwise fun a b=>OrthogonalVertices Q (v a) (v b)),
    (∀ j,v j≠a.color) →
      classGeneratorArray Q (classPacketPerm Q hn v hv x) a=classGeneratorArray Q x a) _ _ _ J
  · intro J L instL e ih
    let :=Fintype.ofEquiv L e.symm
    intro v hv ha
    rw [classPacketPerm_reindex Q hn v hv e]
    exact ih _ _ (fun j=>ha (e j))
  · intro v hv ha
    rw [classPacketPerm_empty Q hn v hv]
    rfl
  · intro J instJ ih v hv ha
    rw [classPacketPerm_cons Q hn v hv]
    change classGeneratorArray Q
      (classPositiveTwist Q (v none) (classPacketPerm Q hn (v ∘ some) _ x)) a=_
    rw [classPositiveTwist_exterior Q _ _ _ (ha none)]
    exact ih _ _ (fun j=>ha (some j))

lemma classPacketPerm_inverse_exterior {J:Type u} [Fintype J] (v:J → V)
    (hv:Pairwise fun a b=>OrthogonalVertices Q (v a) (v b))
    (x:FiniteHomotopyClass Q (K:=K)) (a:GeneratorPlacement V)
    (ha:∀ j,v j≠a.color) :
    classGeneratorArray Q ((classPacketPerm Q hn v hv).symm x) a=classGeneratorArray Q x a := by
  have h:=classPacketPerm_exterior Q hn v hv ((classPacketPerm Q hn v hv).symm x) a ha
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_PositiveWordActionOrthogonal
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
  (hn:∀a,Q.source a≠Q.target a)

include hn in
lemma positiveWordAction_orthogonal_comm (α:V) (w:List V)
    (hw:∀β∈w,OrthogonalVertices Q α β) (x:FiniteHomotopyClass Q (K:=K)) :
    classPositiveTwist Q α (positiveWordAction Q w x)=
      positiveWordAction Q w (classPositiveTwist Q α x) := by
  induction w with
  | nil=>rfl
  | cons β w ih=>
    change classPositiveTwist Q α (classPositiveTwist Q β (positiveWordAction Q w x))=_
    have he:=congrArg (fun p:Equiv.Perm (FiniteHomotopyClass Q (K:=K))=>p (positiveWordAction Q w x))
      (classTwistPerm_orthogonal Q hn (hw β (by simp)))
    change classPositiveTwist Q α (classPositiveTwist Q β (positiveWordAction Q w x))=
      classPositiveTwist Q β (classPositiveTwist Q α (positiveWordAction Q w x)) at he
    rw [he,ih (fun γ hγ=>hw γ (List.mem_cons_of_mem _ hγ))]
    rfl

lemma classPacketPerm_testUpper_reflect {J:Type u} [Fintype J]
    (v:J→V) (hv:Pairwise fun a b=>OrthogonalVertices Q (v a) (v b))
    (U:Set V) (hU:∀a,v a∈U) (x:FiniteHomotopyClass Q (K:=K)) {t:ℤ}
    (h:ClassTestUpper Q (classPacketPerm Q hn v hv x) U t) : ClassTestUpper Q x U t := by
  rw [← classPacketPerm_toList Q hn v hv] at h
  have he: ((Finset.univ:Finset J).toList.map (fun a=>classTwistPerm Q hn (v a))).prod x=
      positiveWordAction Q ((Finset.univ:Finset J).toList.map v) x := by
    rw [positiveWordAction_eq_prod Q hn,List.map_map]
    rfl
  rw [he] at h
  apply positiveWordAction_testUpper_reflect Q hn _ x U _ h
  intro α hα
  obtain ⟨a,_,rfl⟩:=List.mem_map.mp hα
  exact hU a

lemma classPacketPerm_testExact_of_cap {J:Type u} [Fintype J]
    (v:J→V) (hv:Pairwise fun a b=>OrthogonalVertices Q (v a) (v b))
    (U:Set V) (hU:∀a,v a∈U) (x:FiniteHomotopyClass Q (K:=K)) {t:ℤ}
    (h:ClassTestUpper Q (classPacketPerm Q hn v hv x) U t) (a:J) (c:ℤ) :
    ClassTestExact Q (v a) t c x := by
  let vr:{b:J // b≠a}→V:=fun b=>v b.val
  have hvr:Pairwise fun b b'=>OrthogonalVertices Q (vr b) (vr b') := by
    intro b b' hbb
    exact hv (fun he=>hbb (Subtype.ext he))
  have he:classPacketPerm Q (K:=K) hn v hv=classTwistPerm Q hn (v a)*classPacketPerm Q hn vr hvr := by
    let vo:Option {b:J // b≠a}→V:=v ∘ Equiv.optionSubtypeNe a
    have hvo:Pairwise fun b b'=>OrthogonalVertices Q (vo b) (vo b') :=
      fun b b' hbb=>hv (fun hh=>hbb ((Equiv.optionSubtypeNe a).injective hh))
    calc
      classPacketPerm Q hn v hv = classPacketPerm Q hn vo hvo :=
        classPacketPerm_reindex Q hn v hv (Equiv.optionSubtypeNe a)
      _ = classTwistPerm Q hn (vo none)*classPacketPerm Q hn (vo ∘ some)
          (fun b b' hbb=>hvo (fun hh=>hbb (Option.some.inj hh))) :=
        classPacketPerm_cons Q hn vo hvo
      _ = _ := rfl
  have hc:classPositiveTwist Q (v a) (classPacketPerm Q hn vr hvr x)=
      classPacketPerm Q hn vr hvr (classPositiveTwist Q (v a) x) := by
    rw [← classPacketPerm_toList Q hn vr hvr]
    have hword (y:FiniteHomotopyClass Q (K:=K)):
        ((Finset.univ:Finset {b:J // b≠a}).toList.map (fun b=>classTwistPerm Q hn (vr b))).prod y=
        positiveWordAction Q ((Finset.univ:Finset {b:J // b≠a}).toList.map vr) y := by
      rw [positiveWordAction_eq_prod Q hn,List.map_map]
      rfl
    rw [hword,hword]
    apply positiveWordAction_orthogonal_comm Q hn
    intro β hβ
    obtain ⟨b,_,rfl⟩:=List.mem_map.mp hβ
    exact hv (Ne.symm b.property)
  rw [he] at h
  change ClassTestUpper Q (classPositiveTwist Q (v a) (classPacketPerm Q hn vr hvr x)) U t at h
  rw [hc] at h
  have hs:=classPacketPerm_testUpper_reflect Q hn vr hvr U (fun b=>hU b.val) _ h
  exact (classPositiveTwist_testUpper_iff Q hn x U (v a) (hU a)
    (classPositiveTwist_testUpper_reflect Q hn x U (v a) (hU a) hs)).mp hs c

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_ScalarKernel
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
  {I J:Type u} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

omit [Fintype V] [DecidableEq A] [DecidableEq I] [DecidableEq J] in
theorem pureMap_scalarKernel_zero (E:BasedComplex Q (K:=K) I) (F:BasedComplex Q (K:=K) J)
    {q:ℤ} (hE:∀ i,(E.placement i).level=q) (hF:∀ j,(F.placement j).level=q)
    (f:Map Q E F)
    (hm:∀ T:FiniteModel.{u} Q (K:=K),ClassUpperBound Q q (classOfComplex Q T.complex)→
      HomMonoFrom Q T.complex f)
    {x:I→K} (hx:ScalarKernel Q f x) : x=0 := by
  by_contra hx0
  obtain ⟨α,c,y,hy,hy0,hyk⟩:=scalarKernel_has_socle Q (pureMap_coefficient Q f q hE hF) hx hx0
  let p:GeneratorPlacement V:=⟨α,c,q-c⟩
  let P:=placedProjective Q (K:=K) p
  have hP:∀ i,(P.placement i).level=q := by intro i; change c+(q-c)=q; omega
  let z:PUnit.{u+1}→K:=fun _=>1
  have hz:z∈coefficientTopDual Q P α c := by
    constructor
    · intro i hi
      exact (hi.elim (fun h=>h rfl) (fun h=>h rfl)).elim
    · intro i a
      change ∑ j:PUnit.{u+1},(0:K)*z j=0
      simp only [MulZeroClass.zero_mul,Finset.sum_const_zero]
  let g:=topSocleMatrix Q α z y
  have hg:g∈homCycles Q P E 0 0 := by
    simpa only [sub_self] using topSocleMatrix_mem_homCycles Q P E hP hE α c c hz hy
  have hg':g*f.matrix∈homCycles Q P F 0 0 := by
    simpa only [zero_add] using homCycles_mul Q hg (map_mem_homCycles Q f)
  have hco:CoefficientMatrix Q (g*f.matrix):=
    pure_homSpace_coefficient Q P F hP hF (by omega) hg'.1
  have hzero:g*f.matrix=0 := by
    apply Matrix.ext
    intro i j
    apply coefficient_row_zero Q hg'.1.1 hco i _ j
    intro j
    change (∑ k,g i k*f.matrix k j).vertex α=0
    simp only [vertex_sum,Finset.sum_apply,g,topSocleMatrix,vertex_mul,vertex_smul,
      Pi.mul_apply,Pi.smul_apply,smul_eq_mul,vertexId_eval,_root_.mul_one,z,_root_.one_mul,ite_true, if_true,eq_self]
    exact hyk j α
  have hmono:=derivedMono_postcompose_injective Q P E F hP hE (n:=0) (v:=0) (by omega) f hm
  have hgzero:(⟨g,hg⟩:homCycles Q P E 0 0)=0 := by
    apply hmono
    apply Subtype.ext
    change g*f.matrix=(0:Matrix PUnit.{u+1} I (Q.Zigzag K))*f.matrix
    rw [Matrix.zero_mul]
    exact hzero
  exact topSocleMatrix_ne_zero Q α (by intro h; have hh:=congrFun h PUnit.unit; exact one_ne_zero hh) hy0
    (congrArg Subtype.val hgzero)

omit [Fintype V] [DecidableEq A] in
theorem pureMap_termwiseSplit (E:BasedComplex Q (K:=K) I) (F:BasedComplex Q (K:=K) J)
    {q:ℤ} (hE:∀ i,(E.placement i).level=q) (hF:∀ j,(F.placement j).level=q)
    (f:Map Q E F)
    (hm:∀ T:FiniteModel.{u} Q (K:=K),ClassUpperBound Q q (classOfComplex Q T.complex)→
      HomMonoFrom Q T.complex f) :
    ∃ g:TermwiseSplitInjection Q E F,g.inclusion=f := by
  let R:=f.scalarMatrix Q
  have hk:LinearMap.ker R.toLinearMapRight'=⊥ := by
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    exact pureMap_scalarKernel_zero Q E F hE hF f hm (scalarKernel_of_vecMul_zero Q f hx)
  obtain ⟨s,hs⟩:=LinearMap.exists_leftInverse_of_injective R.toLinearMapRight' hk
  let S:=s.toMatrixRight'
  have hRS:R*S=1 := by
    have hh:=congrArg LinearMap.toMatrixRight' hs
    simpa only [LinearMap.toMatrixRight'_comp,LinearMap.toMatrixRight'_id,
      LinearEquiv.apply_symm_apply] using hh
  let g:Matrix J I (Q.Zigzag K):=fun j i=>S j i •(1:Q.Zigzag K)
  refine ⟨⟨f,g,?_⟩,rfl⟩
  apply Matrix.ext
  intro i j
  change ∑ k,f.matrix i k*g k j=projectiveIdentity Q E.placement i j
  simp_rw [map_coefficient_entry Q f (pureMap_coefficient Q f q hE hF)]
  simp only [g,smul_mul_smul_comm,_root_.mul_one,← Finset.sum_smul]
  have hij:=congrArg (fun N:Matrix I I K=>N i j) hRS
  change (∑ k,f.scalarMatrix Q i k*S k j)=(1:Matrix I I K) i j at hij
  rw [hij]
  by_cases he:i=j
  · subst j
    simp only [Matrix.one_apply_eq,one_smul,projectiveIdentity,Matrix.diagonal_apply_eq]
  · simp only [Matrix.one_apply_ne he,zero_smul,projectiveIdentity,Matrix.diagonal_apply_ne _ he]

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

noncomputable def HomotopyEquivalence.ofPure
    {E:BasedComplex Q (K:=K) I} {F:BasedComplex Q (K:=K) J}
    (e:HomotopyEquivalence Q E F) {q:ℤ}
    (hE:∀ i,(E.placement i).level=q) (hF:∀ j,(F.placement j).level=q) :
    ChainIsomorphism Q E F :=
  ((pureLayerSelf Q E hE).trans Q
    (e.pureLayer Q (pure_minimal Q E hE) (pure_minimal Q F hF) q)).trans Q
      ((pureLayerSelf Q F hF).symm Q)

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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_TotalVectorLayer
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

omit [Fintype V] [DecidableEq A] in
lemma classTotalVector_layer (x:FiniteHomotopyClass Q (K:=K)) (q:ℤ) :
    classTotalVector Q (classLayer Q q x)=
      generatorVector Q ((minimalClassModel Q x).complex.pureLayer Q
        (minimalClassModel_minimal Q x) q) := by
  have h:=classSignedVector_pure Q (classLayer Q q x) q
    (classLayer_lowerBound Q x q) (classLayer_upperBound Q x q)
  have h':classSignedVector Q (classLayer Q q x)=
      cochainSign (K:=ℝ) q • generatorVector Q
        ((minimalClassModel Q x).complex.pureLayer Q (minimalClassModel_minimal Q x) q) :=
    signedGeneratorVector_pure Q _ q (fun i=>i.property)
  have hq:=congrArg (fun z:V→ℝ=>cochainSign (K:=ℝ) q • z) (h.symm.trans h')
  simpa only [smul_smul,cochainSign_mul_self,one_smul] using hq

omit [Fintype V] [DecidableEq A] in
lemma classTotalVector_layer_apply (x:FiniteHomotopyClass Q (K:=K)) (q:ℤ) (α:V) :
    classTotalVector Q (classLayer Q q x) α=(classLevelArray Q x (α,q):ℝ) := by
  rw [classTotalVector_layer]
  exact generatorVector_minimalLayer Q x q α

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Coxeter_CanonicalReducedWordLow
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

theorem canonicalReducedWordLow_termwiseSplit (hn:∀ a,Q.source a≠Q.target a)
    (U:Set V)
    (hU:∀ α∈U,∀ β∈U,α=β ∨ OrthogonalVertices Q α β ∨ Nonempty (SimpleEdge Q α β))
    (x:FiniteHomotopyClass Q (K:=K)) (q:ℤ)
    (hlo:ClassLowerBound Q q x) (hhi:ClassUpperBound Q q x)
    (w:List V) (hw:∀ s∈w,s∈U)
    (hr:(ordinaryCoxeterMatrix Q).toCoxeterSystem.IsReduced w) :
    Nonempty (TermwiseSplitInjection Q (minimalClassModel Q (canonicalWordLow Q w q x)).complex
      (minimalClassModel Q x).complex) := by
  obtain ⟨f,hm⟩:=canonicalReducedWordLow_monic Q hn U hU x q hlo hhi w hw hr
  have hp:=canonicalReducedWordLow_pure Q hn U hU x q hlo hhi w hw hr
  obtain ⟨g,_⟩:=pureMap_termwiseSplit Q _ _
    (fun i=>le_antisymm (hp.2 i) (hp.1 i)) (fun i=>le_antisymm (hhi i) (hlo i)) f hm
  exact ⟨g⟩

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Functors_LayerIndexEquiv
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
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

lemma classLabel_layer (d : ℤ) (x : FiniteHomotopyClass U (K := K)) :
    classLayer U d (F x) = F (classLayer U d x) := by
  let E := (minimalClassModel U x).complex
  have hE := minimalClassModel_minimal U x
  have hx : classOfComplex U E = x := minimalClassModel_class U x
  conv_lhs => rw [← hx,classLabel_complex]
  rw [classLayer_minimal U (C E) (complex_minimal Q step hstep N hN orient μ A ho hμ δ hA hroot hPF E hE)]
  change _ = classOfComplex U (C (E.pureLayer U hE d))
  exact classOfComplex_eq U
    ((layerComparison Q step hstep N hN orient μ A ho hμ δ hA hroot hPF E hE d).toHomotopyEquivalence U)

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
local notation "F" => classLabelFunctor Q step hstep N hN orient μ A ho hμ δ hA hroot hPF

variable {T : Type u} [Fintype T] [DecidableEq T]

omit [DecidableEq T] in
lemma truncation_eq (E : Zigzag.BasedComplex U (K := K) T) (hE : E.IsMinimal U) (d : ℤ) :
    (lowerTruncation U (C E) (complex_minimal Q step hstep N hN orient μ A ho hμ δ hA hroot hPF E hE) d).reindex U
      (truncationIndexEquiv Q step hstep N hN orient μ A ho hμ δ hA hroot hPF E d) = C (lowerTruncation U E hE d) := by
  apply ext_placement_differential U
  · rfl
  · rfl

noncomputable def truncationComparison (E : Zigzag.BasedComplex U (K := K) T)
    (hE : E.IsMinimal U) (d : ℤ) :
    ChainIsomorphism U
      (lowerTruncation U (C E) (complex_minimal Q step hstep N hN orient μ A ho hμ δ hA hroot hPF E hE) d)
      (C (lowerTruncation U E hE d)) := by
  have e := reindexChainIsomorphism U
    (lowerTruncation U (C E) (complex_minimal Q step hstep N hN orient μ A ho hμ δ hA hroot hPF E hE) d)
    (truncationIndexEquiv Q step hstep N hN orient μ A ho hμ δ hA hroot hPF E d)
  rw [truncation_eq] at e
  exact e

lemma classLabel_truncation (d : ℤ) (x : FiniteHomotopyClass U (K := K)) :
    classLowerTruncation U d (F x) = F (classLowerTruncation U d x) := by
  let E := (minimalClassModel U x).complex
  have hE := minimalClassModel_minimal U x
  have hx : classOfComplex U E = x := minimalClassModel_class U x
  conv_lhs => rw [← hx,classLabel_complex]
  rw [classLowerTruncation_minimal U (C E) (complex_minimal Q step hstep N hN orient μ A ho hμ δ hA hroot hPF E hE)]
  change _ = classOfComplex U (C (lowerTruncation U E hE d))
  exact classOfComplex_eq U
    ((truncationComparison Q step hstep N hN orient μ A ho hμ δ hA hroot hPF E hE d).toHomotopyEquivalence U)

end HarmonicArtin.ReversibleQuiver.StringFunctor

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_LayerExpression
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin

namespace ReversibleQuiver.StringFunctor
universe u
attribute [local instance] Classical.propDecidable Classical.decEq
variable {V B J:Type u} {K:Type*} (Q:ReversibleQuiver V B)
  (step:B→Bool) (hstep:∀ b,step (Q.reverse b)=step b)
  (N:J→J→Prop) (hN:∀ ⦃first second : J⦄, N first second → N second first)
  [Fintype V] [Fintype B] [Fintype J]
  [DecidableEq V] [DecidableEq B] [DecidableEq J] [DecidableRel N] [Field K]
  (hn:∀ b,Q.source b≠Q.target b)
local notation "U" => Q.stringQuiver step hstep N hN
open Zigzag.BasedComplex

local notation "W" => wordPacketPerm Q step hstep N hN (K:=K) hn

noncomputable def expressionAction : LayerExpression V →
    FiniteHomotopyClass U (K:=K) → FiniteHomotopyClass U (K:=K)
  | .input,x=>x
  | .word w t,x=>W w (expressionAction t x)
  | .low d t,x=>classLowerTruncation U d (expressionAction t x)
  | .layer d t,x=>classLayer U d (expressionAction t x)

lemma expressionAction_sum {I:Type u} [Fintype I] [DecidableEq I]
    (t:LayerExpression V) (x:I→FiniteHomotopyClass U (K:=K)) :
    expressionAction Q step hstep N hN hn t (classSum U x)=
      classSum U (fun i=>expressionAction Q step hstep N hN hn t (x i)) := by
  induction t with
  | input => rfl
  | word w t ih => exact (congrArg (W w) ih).trans (wordPacketPerm_sum Q step hstep N hN hn w _)
  | low d t ih => exact (congrArg (classLowerTruncation U d) ih).trans (classLowerTruncation_sum U d _)
  | layer d t ih => exact (congrArg (classLayer U d) ih).trans (classLayer_sum U d _)

variable (orient:B→Bool) (μ:J→K) (A:K)
  (ho:∀ b,orient (Q.reverse b)=!(orient b))
  (hμ:∀ a,μ a≠0) (δ:K) (hA:A≠0) (hroot:A^2+A⁻¹^2+δ=0)
  (hPF:∀ a,∑ b∈GraphConnection.neighbors N a,μ b=δ*μ a)
local notation "F" => classLabelFunctor Q step hstep N hN orient μ A ho hμ δ hA hroot hPF
local notation "T" => expressionAction Q step hstep N hN (K:=K) hn

lemma classLabel_expression (t:LayerExpression V) (x:FiniteHomotopyClass U (K:=K)) :
    F (T t x)=T t (F x) := by
  induction t with
  | input => rfl
  | word w t ih =>
    change F (W w (T t x))=W w (T t (F x))
    rw [classLabel_wordPacket,ih]
  | low d t ih =>
    change F (classLowerTruncation U d (T t x))=classLowerTruncation U d (T t (F x))
    rw [← classLabel_truncation,ih]
  | layer d t ih =>
    change F (classLayer U d (T t x))=classLayer U d (T t (F x))
    rw [← classLabel_layer,ih]

lemma classLabel_expressionOrbit (t:LayerExpression V) (s:V) (i:J) :
    F (T t (initialClass U (s,i)))=
      classSum U (fun a:{a:J // N i a}=>T t (initialClass U (s,a))) := by
  rw [classLabel_expression,classLabel_initial,expressionAction_sum]

include ho hμ hA hroot hPF
lemma expressionOrbit_count_adjacency (t:LayerExpression V) (s v:V) (d:ℤ) (i j:J) :
    (∑ a:{a // N a j},classLevelArray U (T t (initialClass U (s,i))) ((v,a),d))=
      ∑ a:{a // N i a},classLevelArray U (T t (initialClass U (s,a))) ((v,j),d) := by
  rw [← classLevelArray_label Q step hstep N hN orient μ A ho hμ δ hA hroot hPF]
  rw [classLabel_expressionOrbit Q step hstep N hN hn orient μ A ho hμ δ hA hroot hPF,
    classLevelArray_sum]
  simp

variable [Nonempty J] (hconn:∀ a b,Relation.ReflTransGen N a b)
  (ρ:J→ℝ) (hρ:∀ a,0<ρ a) (θ:ℝ)
  (hρPF:∀ a,∑ b∈GraphConnection.neighbors N a,ρ b=θ*ρ a)
include hconn hρ hρPF

theorem expressionOrbit_count_proportional (t:LayerExpression V) (s v:V) (d:ℤ) :
    ∃ r:ℝ,0 ≤ r ∧ ∀ j,
      (∑ i,ρ i*(classLevelArray U (T t (initialClass U (s,i))) ((v,j),d):ℝ))=r*ρ j := by
  apply GraphConnection.nonnegative_eigenvector_proportional N hconn ρ hρ θ hρPF
  · exact GraphConnection.weighted_intertwiner N hN ρ θ hρPF _
      (expressionOrbit_count_adjacency Q step hstep N hN hn orient μ A ho hμ δ hA hroot hPF t s v d)
  · intro j
    exact Finset.sum_nonneg fun i _=>mul_nonneg (le_of_lt (hρ i)) (Nat.cast_nonneg _)

end ReversibleQuiver.StringFunctor

namespace ReversibleQuiver.StringFunctor
open Zigzag.BasedComplex

variable {V B:Type} (Q:ReversibleQuiver V B)
  [Fintype V] [Fintype B] [DecidableEq V] [DecidableEq B]
  (step:B→Bool) (hstep:∀ b,step (Q.reverse b)=step b)
  (hn:∀ b,Q.source b≠Q.target b) (m:ℕ) (hm : 2 ≤ m)
local notation "N" => stringAdjacent m
local notation "hN" => stringAdjacent_symm m
local notation "U" => Q.stringQuiver step hstep N hN
local notation "T" => expressionAction Q step hstep N hN (K:=ℂ) hn

include hm

theorem string_expressionOrbit_count_proportional (t:LayerExpression V) (s v:V) (d:ℤ) :
    ∃ r:ℝ,0 ≤ r ∧ ∀ j,
      (∑ i,stringWeight m i*(classLevelArray U (T t (initialClass U (s,i))) ((v,j),d):ℝ))=
        r*stringWeight m j := by
  have : NeZero (m-1):=⟨by omega⟩
  obtain ⟨A,hA,hr,hμ,hPF⟩:=string_connection_exists m hm
  exact expressionOrbit_count_proportional Q step hstep N hN hn Q.fixedOrientation
    (fun a=>(stringWeight m a:ℂ)) A (Q.fixedOrientation_reverse hn) hμ
    (2*Real.cos (Real.pi/m):ℝ) hA hr hPF (stringAdjacent_connected m)
    (stringWeight m) (stringWeight_pos hm) _ (stringAdjacent_weight m hm) t s v d

end ReversibleQuiver.StringFunctor
end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_FusionExpressionAction
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

variable (e:E)
local notation "mr" => (fun f:FusionRest e=>m f)
local notation "dr" => (fun s t=>FusionEdge.removeFactor e (d s t))
local notation "Qr" => fusionQuiver mr dr (restFusion_symmetric d hd e)
local notation "hnr" => fusionQuiver_no_loops mr dr (restFusion_symmetric d hd e) (restFusion_diagonal d hdiag e)
local notation "step" => fusionFactorStep m e d
local notation "hstep" => fusionFactorStep_reverse m e d hd
local notation "N" => stringAdjacent (m e)
local notation "hN" => stringAdjacent_symm (m e)
local notation "U" => ReversibleQuiver.stringQuiver Qr step hstep N hN
local notation "F" => ReversibleQuiver.Iso.classMap (fusionQuiverSplit m e d hd) (K:=K)
local notation "T" => StringFunctor.expressionAction Qr step hstep N hN (K:=K) hnr
local notation "P" => fusionExpressionAction m d hd hdiag (K:=K)

lemma fusionExpression_split (t:LayerExpression V) :
    ∃ z:LayerExpression (FusionVertex (V:=V) mr),∀ x,F (P t x)=T z (F x) := by
  induction t with
  | input => exact ⟨.input,fun _=>rfl⟩
  | word w t ih =>
    obtain ⟨z,hz⟩:=ih
    obtain ⟨w',hw⟩:=fusionWord_split m d hd hdiag e (K:=K) w
    refine ⟨.word w' z,fun x=>?_⟩
    change F (fusionWordPacketPerm m d hd hdiag w (P t x))=
      StringFunctor.wordPacketPerm Qr step hstep N hN hnr w' (T z (F x))
    rw [hw,hz]
  | low k t ih =>
    obtain ⟨z,hz⟩:=ih
    refine ⟨.low k z,fun x=>?_⟩
    change F (classLowerTruncation Q k (P t x))=classLowerTruncation U k (T z (F x))
    rw [(fusionQuiverSplit m e d hd).classMap_lowerTruncation,hz]
  | layer k t ih =>
    obtain ⟨z,hz⟩:=ih
    refine ⟨.layer k z,fun x=>?_⟩
    change F (classLayer Q k (P t x))=classLayer U k (T z (F x))
    rw [(fusionQuiverSplit m e d hd).classMap_layer,hz]

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_CanonicalFusionLow
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.unfoldedHom_simple _root_.OAI.HarmonicArtin.unfoldedMatrix_apply
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
local notation "hn" => fusionQuiver_no_loops m d hd hdiag
local notation "P" => fusionWordPacketPerm m d hd hdiag (K:=K)

noncomputable def canonicalFusionLow (w:List V) (q:ℤ) (x:FiniteHomotopyClass Q (K:=K)) :
    FiniteHomotopyClass Q (K:=K) :=
  let p:=P (w.map fun s=>(s,true))
  p (classLowerTruncation Q (q-1) (p.symm x))

lemma canonicalFusionLow_eq_ordinary (w:List V) (z:List (FusionVertex (V:=V) m))
    (hz:∀ x:FiniteHomotopyClass Q (K:=K),positiveWordAction Q z x=P (w.map fun s=>(s,true)) x)
    (q:ℤ) (x:FiniteHomotopyClass Q (K:=K)) :
    canonicalFusionLow m d hd hdiag w q x=canonicalWordLow Q z q x := by
  have hinv:(P (w.map fun s=>(s,true))).symm x=inverseWordAction Q z x := by
    apply (P (w.map fun s=>(s,true))).injective
    rw [Equiv.apply_symm_apply,← hz,positive_inverseWord Q hn]
  dsimp [canonicalFusionLow,canonicalWordLow]
  rw [hinv,hz]

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
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_FusionExpressionOrbit
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

variable (e:E)
local notation "mr" => (fun f:FusionRest e=>m f)
local notation "dr" => (fun s t=>FusionEdge.removeFactor e (d s t))
local notation "Qr" => fusionQuiver mr dr (restFusion_symmetric d hd e)
local notation "hnr" => fusionQuiver_no_loops mr dr (restFusion_symmetric d hd e) (restFusion_diagonal d hdiag e)
local notation "step" => fusionFactorStep m e d
local notation "hstep" => fusionFactorStep_reverse m e d hd
local notation "N" => stringAdjacent (m e)
local notation "hN" => stringAdjacent_symm (m e)
local notation "U" => ReversibleQuiver.stringQuiver Qr step hstep N hN
local notation "F" => ReversibleQuiver.Iso.classMap (fusionQuiverSplit m e d hd) (K:=ℂ)
local notation "T" => StringFunctor.expressionAction Qr step hstep N hN (K:=ℂ) hnr
local notation "O" => fusionExpressionOrbit m d hd hdiag

lemma fusionExpressionOrbit_split (t:LayerExpression V) :
    ∃ z:LayerExpression (FusionVertex (V:=V) mr),∀ s L,
      F (O t s L)=T z (initialClass U ((s,restLabel m e L),L e)) := by
  obtain ⟨z,hz⟩:=fusionExpression_split m d hd hdiag e (K:=ℂ) t
  refine ⟨z,fun s L=>?_⟩
  rw [fusionExpressionOrbit,hz,(fusionQuiverSplit m e d hd).classMap_initial]
  rfl

variable (hm : ∀ e, 2 ≤ m e)
include hm in
lemma fusionExpressionOrbit_count_slice (t:LayerExpression V) (s v:V) (q:ℤ)
    (r a:FusionLabel mr) : ∃ c:ℝ,∀ j,
    (∑ i,stringWeight (m e) i*
      (classLevelArray Q (O t s ((labelSplit m e).symm (a,i))) ((v,(labelSplit m e).symm (r,j)),q):ℝ))=
        c*stringWeight (m e) j := by
  obtain ⟨z,hz⟩:=fusionExpressionOrbit_split m d hd hdiag e t
  obtain ⟨c,_,h⟩:=StringFunctor.string_expressionOrbit_count_proportional Qr step hstep hnr (m e) (hm e)
    z (s,a) (v,r) q
  refine ⟨c,fun j=>?_⟩
  calc
    _ = ∑ i,stringWeight (m e) i * (classLevelArray U (T z (initialClass U ((s,a),i))) (((v,r),j),q):ℝ) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← (fusionQuiverSplit m e d hd).classMap_levelArray,hz]
      simp only [fusionQuiverSplit,fusionVertexSplit,Equiv.coe_fn_mk,
        labelSplit_symm_at,labelSplit_symm_rest]
    _ = _ := h j

include hm

theorem fusionExpressionOrbit_count_proportional (t:LayerExpression V) (s v:V) (q:ℤ) :
    ∃ c:ℝ,0 ≤ c ∧ ∀ L,
      (∑ H,fusionWeight m H*(classLevelArray Q (O t s H) ((v,L),q):ℝ))=c*fusionWeight m L :=
  fusion_weighted_matrix_proportional m hm _
    (fun e=>fusionExpressionOrbit_count_slice m d hd hdiag e hm t s v q)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_CanonicalFusionLowCount
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
  (hdiag:∀ s,d s s=.units 0) (hm:∀ e,2 ≤ m e)
local notation "Q" => fusionQuiver m d hd

include hm

theorem canonicalFusionLow_count_proportional (w:List V) (z:List (V×Bool))
    (s v:V) (q k:ℤ) : ∃ c:ℝ,0 ≤ c ∧ ∀ L,
    (∑ H,fusionWeight m H*(classLevelArray Q
      (canonicalFusionLow m d hd hdiag w q (classLayer Q q (fusionPacketOrbit m d hd hdiag z s H)))
       ((v,L),k):ℝ))=c*fusionWeight m L := by
  simpa only [fusionExpressionOrbit,canonicalFusionExpression_action,fusionPacketOrbit] using
    fusionExpressionOrbit_count_proportional m d hd hdiag hm
      (canonicalFusionExpression w z q) s v k

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_CanonicalFusionMultiplicity
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
  (hdiag:∀ s,d s s=.units 0) (hm:∀ e,2 ≤ m e)

noncomputable def canonicalFusionMultiplicity (w:List V) (z:List (V×Bool))
    (s:V) (q:ℤ) (v:V) : ℝ :=
  Classical.choose (canonicalFusionLow_count_proportional m d hd hdiag hm w z s v q q)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_FusionZeroLabel
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_FusionColorRegion
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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

noncomputable def fusionOrbitColorMultiplicity (hm:∀ e,2 ≤ m e)
    (w:List (V × Bool)) (s:V) (q:ℤ) (U:Set V) : V → ℝ :=
  fun v=>if v∈U then fusionOrbitMultiplicity m d hd hdiag hm w s q v else 0

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_FrameFamily
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "hd" => coxeterFusionEdge_symm M
local notation "hdiag" => coxeterFusionEdge_diag M
local notation "hm" => fusionLabelSize_ge_two M
local notation "Q" => fusionQuiver m d hd
local notation "O" => fusionPacketOrbit m d hd hdiag
local notation "aw" => sourceArtinAction M (K:=ℂ)

noncomputable def sourceFrameFamily (x:Artin M) (L:FusionLabel m) :
    FiniteHomotopyClass Q (K:=ℂ) := aw x (O [] (.inr ()) L)

noncomputable def sourceMultiplicity (x:Artin M) (k:ℤ) (v:S⊕Unit) : ℝ :=
  fusionFamilyMultiplicity m d hd hm (sourceFrameFamily M x) k v

lemma sourceMultiplicity_nonneg (x:Artin M) (k:ℤ) (v:S⊕Unit) :
    0 ≤ sourceMultiplicity M x k v := fusionFamilyMultiplicity_nonneg m d hd hm _ k v

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_Harmonic
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open _root_.Matrix _root_.OAI.Matrix

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

noncomputable def sourceHarmonicAt (T:Set S) (x:Artin M) (k:ℤ) : S⊕Unit→ℝ :=
  harmonicExtension (framedCartan M) ((Sum.inl : S→S⊕Unit) '' T) (sourceMultiplicity M x k)

lemma sourceHarmonicAt_nonneg (T:Set S) (hT:IsSpherical M T) (x:Artin M) (k:ℤ) :
    ∀ i,0 ≤ sourceHarmonicAt M T x k i :=
  harmonicExtension_nonneg _ _ (framed_spherical_posDef M T hT)
    (framedCartan_off M) _ (sourceMultiplicity_nonneg M x k)

noncomputable def sourceCosetVector (P:Deligne M) (k:ℤ) : S⊕Unit→ℝ :=
  sourceHarmonicAt M P.val.1 (sourceCosetRepresentative M P) k

lemma sourceCosetVector_nonneg (P:Deligne M) (k:ℤ) :
    ∀ i,0 ≤ sourceCosetVector M P k i :=
  sourceHarmonicAt_nonneg M P.val.1 P.property.1 _ k

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_MultiplicitySum
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "hd" => coxeterFusionEdge_symm M
local notation "hm" => fusionLabelSize_ge_two M
local notation "Q" => fusionQuiver m d hd

lemma sourceMultiplicity_sum (x:Artin M) (k:ℤ) (v:S⊕Unit) :
    sourceMultiplicity M x k v=(∑ L,fusionWeight m L *
      (classLevelArray Q (sourceFrameFamily M x L) ((v,fusionZeroLabel m hm),k):ℝ)) /
      fusionWeight m (fusionZeroLabel m hm) := by
  unfold sourceMultiplicity fusionFamilyMultiplicity
  simp only [classTotalVector_layer_apply]

lemma sourceMultiplicity_support_finite (x:Artin M) :
    {k:ℤ | sourceMultiplicity M x k≠0}.Finite := by
  have h:=finiteFamily_level_support Q (sourceFrameFamily M x)
  apply h.subset
  intro k hk
  by_contra hn
  apply hk
  funext v
  have hz:∀ L,classLevelArray Q (sourceFrameFamily M x L)
      ((v,fusionZeroLabel m hm),k)=0 := by
    intro L
    by_contra hne
    exact hn ⟨L,_,hne⟩
  rw [sourceMultiplicity_sum]
  simp only [hz,Nat.cast_zero,MulZeroClass.mul_zero,Finset.sum_const_zero,zero_div,Pi.zero_apply]

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_CosetSum
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.decEq Classical.propDecidable

variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

lemma sourceCosetVector_support_finite (P:Deligne M) :
    {k:ℤ | sourceCosetVector M P k≠0}.Finite := by
  apply (sourceMultiplicity_support_finite M (sourceCosetRepresentative M P)).subset
  intro k hk
  by_contra hn
  apply hk
  have hz:sourceMultiplicity M (sourceCosetRepresentative M P) k=0:=not_not.mp hn
  change harmonicExtension _ _ _=0
  rw [hz,harmonicExtension_zero]

noncomputable def sourceCosetSum (P:Deligne M) (k:ℤ) : ℝ :=
  ∑ i,sourceCosetVector M P k i

lemma sourceCosetVector_le_sum (P:Deligne M) (k:ℤ) (i:S⊕Unit) :
    sourceCosetVector M P k i ≤ sourceCosetSum M P k :=
  Finset.single_le_sum (fun j _=>sourceCosetVector_nonneg M P k j) (Finset.mem_univ i)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_PositiveComponent
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open _root_.Matrix _root_.OAI.Matrix
open scoped BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

noncomputable def sourceCosetSign (P:Deligne M) (k:ℕ) (i:S⊕Unit) : ℤ :=
  sourceSignAt M (fun d=>sourceCosetVector M P (d:ℤ)) k i

noncomputable def sourceSecondary (P:Deligne M) (k:ℕ) : ℤ :=
  ∑i:P.val.1,sourceCosetSign M P k (.inl (i:S))

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_Block
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.decEq Classical.propDecidable
open scoped BigOperators

variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

noncomputable def sourceBlock (P:Deligne M) (k:ℕ) : SourceBlock S :=
  toLex (sourceCosetSum M P k,toLex (toLex (sourceCosetVector M P k),sourceSecondary M P k))

def SourceBlockOccurs (b:SourceBlock S) : Prop :=
  b=sourceZeroBlock (S:=S) ∨ ∃ P:Deligne M,∃ k:ℕ,b=sourceBlock M P k

lemma sourceBlock_of_vector_zero (P:Deligne M) (k:ℕ) (h:sourceCosetVector M P k=0) :
    sourceBlock M P k=sourceZeroBlock (S:=S) := by
  have hh:sourceSecondary M P k=0 := by
    apply Finset.sum_eq_zero
    intro i _
    apply sourceSignAt_zero
    exact congrFun h _
  simp only [sourceBlock,sourceZeroBlock,sourceCosetSum,h,Pi.zero_apply,Finset.sum_const_zero,hh]
  rfl

lemma sourceCosetSum_pos_of_ne_zero (P:Deligne M) (k:ℕ)
    (h:sourceCosetVector M P k≠0) : 0 < sourceCosetSum M P k := by
  have hx:∃i,sourceCosetVector M P k i≠0 := by
    by_contra hn
    apply h
    funext i
    exact not_not.mp (fun hi=>hn ⟨i,hi⟩)
  obtain ⟨i,hi⟩:=hx
  exact (lt_of_le_of_ne (sourceCosetVector_nonneg M P k i) (Ne.symm hi)).trans_le
    (sourceCosetVector_le_sum M P k i)

lemma sourceZeroBlock_le (b:SourceBlock S) (h:SourceBlockOccurs M b) :
    sourceZeroBlock (S:=S)≤b := by
  rcases h with rfl|⟨P,k,rfl⟩
  · exact le_rfl
  by_cases hz:sourceCosetVector M P k=0
  · rw [sourceBlock_of_vector_zero M P k hz]
  · exact (Prod.Lex.lt_iff.mpr (Or.inl (sourceCosetSum_pos_of_ne_zero M P k hz))).le

noncomputable def sourceBlockRank (b:SourceBlock S) : ℕ :=
  {a:SourceBlock S | SourceBlockOccurs M a ∧ a<b}.ncard

@[simp] lemma sourceBlockRank_zero : sourceBlockRank M (sourceZeroBlock (S:=S))=0 := by
  have he:{a:SourceBlock S | SourceBlockOccurs M a ∧ a < sourceZeroBlock (S:=S)}=∅ := by
    ext a
    simp only [Set.mem_ofPred_eq,Set.mem_empty_iff_false,iff_false,not_and]
    intro ha
    exact not_lt_of_ge (sourceZeroBlock_le M a ha)
  simp only [sourceBlockRank,he,Set.ncard_empty]

lemma sourceBlockRank_support_finite (P:Deligne M) :
    {k:ℕ | sourceBlockRank M (sourceBlock M P k)≠0}.Finite := by
  have h:{k:ℕ | sourceCosetVector M P (k:ℤ)≠0}.Finite :=
    (sourceCosetVector_support_finite M P).preimage (by intro a ha b hb he; exact Int.ofNat_inj.mp he)
  apply h.subset
  intro k hk
  change sourceCosetVector M P (k:ℤ)≠0
  intro hz
  apply hk
  rw [sourceBlock_of_vector_zero M P k hz,sourceBlockRank_zero]

noncomputable def sourceHeight (P:Deligne M) : Colex (ℕ→₀ℕ) :=
  toColex (Finsupp.ofSupportFinite (fun k=>sourceBlockRank M (sourceBlock M P k))
    (sourceBlockRank_support_finite M P))

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Quivers_ProbeSimpleEdge
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
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

variable (hn:∀a,Q.source a≠Q.target a)
omit [DecidableEq A] in
lemma probe_core_braid (α β:V) :
    ((altList α β (ordinaryCoxeterMatrix Q α β)).map
      (fun v=>classTwistPerm R (K:=K) (probeQuiver_no_loops Q hn) (.inl v))).prod=
    ((altList β α (ordinaryCoxeterMatrix Q α β)).map
      (fun v=>classTwistPerm R (K:=K) (probeQuiver_no_loops Q hn) (.inl v))).prod := by
  by_cases he:α=β
  · subst β; rfl
  by_cases ho:OrthogonalVertices Q α β
  · rw [ordinaryCoxeterMatrix_orthogonal Q ho]
    simpa only [altList_succ,altList_zero,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,
      _root_.mul_one] using classTwistPerm_orthogonal R (K:=K)
        (probeQuiver_no_loops Q hn) (probe_orthogonal Q ho)
  by_cases ha:Nonempty (SimpleEdge Q α β)
  · obtain ⟨e⟩:=ha
    rw [ordinaryCoxeterMatrix_adjacent Q e]
    simpa only [altList_succ,altList_zero,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,
      _root_.mul_one,_root_.mul_assoc] using classTwistPerm_adjacent R (K:=K)
        (probeQuiver_no_loops Q hn) (probe_simpleEdge Q e)
  · have hz:ordinaryCoxeterMatrix Q α β=0:=by simp [ordinaryCoxeterMatrix,he,ho,ha]
    rw [hz]; rfl
end HarmonicArtin.ReversibleQuiver

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_CanonicalFusionLowExpansion
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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

lemma canonicalFusionLow_eq_expansion (w : List V) (q : ℤ)
    (x : FiniteHomotopyClass Q (K:=K)) :
    canonicalFusionLow m d hd hdiag w q x=canonicalWordLow Q (fusionExpandedWord m w) q x := by
  apply canonicalFusionLow_eq_ordinary m d hd hdiag w (fusionExpandedWord m w)
  intro y
  exact fusionExpandedWord_action m d hd hdiag w y

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_CappedCandidate
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex _root_.Matrix _root_.OAI.Matrix

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "Q" => fusionQuiver m d (coxeterFusionEdge_symm M)
local notation "C" => fusionFoldedCartan m d

structure SourceCappedCandidate (T J:Set S) (z:Artin M) (q:ℤ) (p:S⊕Unit→ℝ) : Prop where
  subset : J⊆T
  spherical : IsSpherical M J
  cap : ∀H,ClassCapOn Q (sourceFrameFamily M z H)
    (closedNeighborhood Q (Set.range (unfoldedInclusion M T))) q
  harmonic : ∀j:J,(C *ᵥ p) (.inl (j:S))=0
  exterior : ∀v,v∉Sum.inl '' J→sourceMultiplicity M z q v=p v
  negative : ∀s∈T,s∉J→(C *ᵥ p) (.inl s)<0
  representatives : ∀a∈artinParabolic M J,
    (∀H,ClassCapOn Q (sourceFrameFamily M (a*z) H)
      (Set.range (unfoldedInclusion M T)) q)→
    ∀j:J,p (.inl (j:S))≤ sourceMultiplicity M (a*z) q (.inl (j:S))

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_Candidate
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag.BasedComplex _root_.Matrix _root_.OAI.Matrix

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "Q" => fusionQuiver m (coxeterFusionEdge M) (coxeterFusionEdge_symm M)
local notation "U" => fun J:Set S=>Set.range (unfoldedInclusion M J)

structure SourceCandidate (T J:Set S) (z:Artin M) (q:ℤ) : Prop where
  proper : J⊂T
  cap : ∀H,ClassCapOn Q (sourceFrameFamily M z H) (closedNeighborhood Q (U T) \ U J) q
  negative : ∀s∈T,s∉J→(framedCartan M *ᵥ sourceHarmonicAt M J z q) (.inl s)<0
  representatives : ∀y∈rightCoset M J z,
    (∀H,ClassCapOn Q (sourceFrameFamily M y H) (U T) q)→
      ∀j:J,sourceHarmonicAt M J z q (.inl (j:S))≤ sourceMultiplicity M y q (.inl (j:S))

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_CosetProfile
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

noncomputable def sourceCosetProfile (P:Deligne M) : ℕ→₀(S⊕Unit→ℝ) :=
  Finsupp.ofSupportFinite (fun k=>sourceCosetVector M P (k:ℤ))
    ((sourceCosetVector_support_finite M P).preimage
      (by intro a ha b hb he; exact Int.ofNat_inj.mp he))

@[simp] lemma sourceCosetProfile_apply (P:Deligne M) (k:ℕ) :
    sourceCosetProfile M P k=sourceCosetVector M P (k:ℤ) := rfl

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_PeakSupport
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open _root_.Matrix _root_.OAI.Matrix

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

noncomputable def sourcePeakSupport (P:Deligne M) (i:S) : Finset ℕ :=
  (sourceCosetProfile M P).support.filter (fun k=>sourceCosetVector M P k (.inl i)≠0)

noncomputable def sourcePeak (P:Deligne M) (i:S) : ℕ :=
  (sourcePeakSupport M P i).sup id

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_Eligible
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open _root_.Matrix _root_.OAI.Matrix

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

def SourceEligible (P Q:Deligne M) (i:S) : Prop :=
  i∈P.val.1 ∧ i∉Q.val.1 ∧
  (∀d:ℕ,sourcePeak M P i<d→sourceCosetVector M Q d (.inl i)=0) ∧
  (sourceCosetVector M Q (sourcePeak M P i) (.inl i) < sourceCosetVector M P (sourcePeak M P i) (.inl i) ∨
   sourceCosetVector M Q (sourcePeak M P i) (.inl i)=sourceCosetVector M P (sourcePeak M P i) (.inl i) ∧
     sourceCosetSign M P (sourcePeak M P i) (.inl i)=1)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_TieCode
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

noncomputable def sourceVertexKey (P:Deligne M) : Lex (Colex (ℕ→₀ℕ) × ℕ) :=
  toLex (sourceHeight M P,sourceTieCode M P)

def SourceEarlier (P R:Deligne M) : Prop := sourceVertexKey M P < sourceVertexKey M R

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_EarlierLower
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

abbrev SourceEarlierLower (P:Deligne M) := {Q:Deligne M // Q<P ∧ SourceEarlier M Q P}

def sourceEligibleSet (P Q:Deligne M) : Set S := {i | SourceEligible M P Q i}

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_AllEligibleLower
attribute [-instance] _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open Simplicial CategoryTheory

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

abbrev SourceAllEligibleLower (P:Deligne M) :=
  {Q:Deligne M // Q<P ∧ ∀i∈P.val.1,i∉Q.val.1→SourceEligible M P Q i}

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_EarlierUpper
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

abbrev SourceEarlierUpper (P:Deligne M) := {R:Deligne M // P<R ∧ SourceEarlier M R P}

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_ResidueAllowed
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open _root_.Matrix _root_.OAI.Matrix

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

def SourceResidueAllowed (strict:Bool) (P Q:Deligne M) (q:ℤ) : Prop :=
  Q<P ∧ ∀i∈P.val.1,i∉Q.val.1→
    (∀d:ℤ,q<d→sourceCosetVector M Q d (.inl i)=0) ∧
    (if strict then sourceCosetVector M Q q (.inl i) < sourceCosetVector M P q (.inl i)
      else sourceCosetVector M Q q (.inl i)≤ sourceCosetVector M P q (.inl i))

abbrev SourceResidue (strict:Bool) (P:Deligne M) (q:ℤ) :=
  {Q:Deligne M // SourceResidueAllowed M strict P Q q}

noncomputable def sourceResidueHeight (P Q:Deligne M) (q:ℤ) : ℝ :=
  ∑i∈P.val.1.toFinset,(sourceCosetVector M Q q (.inl i)-sourceCosetVector M P q (.inl i))

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_EligibleWithin
attribute [-instance] _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

abbrev SourceEligibleWithin (P R:Deligne M) :=
  {Q:Deligne M // Q≤R ∧ ∀i∈R.val.1,i∉Q.val.1→SourceEligible M P Q i}

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_ResidueActive
attribute [-instance] _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open _root_.Matrix _root_.OAI.Matrix Simplicial CategoryTheory

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

abbrev SourceResidueEarlierUpper (P X:Deligne M) (q:ℤ) :=
  {R:Deligne M // X<R ∧ R<P ∧ sourceResidueHeight M P R q≤ sourceResidueHeight M P X q}

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_ResidueEarlierLower
attribute [-instance] _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open Simplicial CategoryTheory

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

abbrev SourceResidueEarlierLower (strict:Bool) (P X:Deligne M) (q:ℤ) :=
  {Y:Deligne M // SourceResidueAllowed M strict P Y q ∧ Y<X ∧
    sourceResidueHeight M P Y q < sourceResidueHeight M P X q}

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_CosetOrbit
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
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
local notation "O" => fusionPacketOrbit m d hd hdiag
local notation "aw" => sourceArtinAction M (K:=ℂ)

def SourceCosetOrbit (J:Set S) (z₀:List ((S⊕Unit)×Bool)) (s:S⊕Unit)
    (z:List ((S⊕Unit)×Bool)) : Prop :=
  ∃ g∈artinParabolic M J,∀ L,O z s L=aw g (O z₀ s L)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_ResidueRank
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

noncomputable def sourceResidueRank (strict:Bool) (P:Deligne M) (q:ℤ) (h:ℝ) : ℕ :=
  {a:ℝ | a∈Set.range (fun X:SourceResidue M strict P q=>sourceResidueHeight M P X q) ∧ a<h}.ncard

noncomputable def sourceResidueSecondary (P X:Deligne M) (q:ℤ) : ℕ :=
  if sourceResidueHeight M P X q<0 then Fintype.card S-X.val.1.ncard else X.val.1.ncard

noncomputable def sourceResidueKey (strict:Bool) (P:Deligne M) (q:ℤ)
    (X:SourceResidue M strict P q) : Lex (ℕ × Lex (ℕ×ℕ)) :=
  toLex (sourceResidueRank M strict P q (sourceResidueHeight M P X q),
    toLex (sourceResidueSecondary M P X q,sourceTieCode M X))

def SourceResidueEarlier (strict:Bool) (P:Deligne M) (q:ℤ)
    (X Y:SourceResidue M strict P q) : Prop := sourceResidueKey M strict P q X < sourceResidueKey M strict P q Y

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_ArtinReindex
attribute [-instance] _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.decEq Classical.propDecidable
universe u v
variable {S:Type u} {T:Type v} (M:CoxeterMatrix S) (e:S≃T)

noncomputable def deligneReindexMap : Deligne M →o Deligne (M.reindex e) where
  toFun P:=⟨(e '' P.val.1,artinReindex M e '' P.val.2),(spherical_reindex M e P.val.1).mpr P.property.1,by
    obtain ⟨x,hx⟩:=P.property.2
    exact ⟨artinReindex M e x,by rw [hx,rightCoset_reindex]⟩⟩
  monotone':=fun _ _ h=>⟨Set.image_mono h.1,Set.image_mono h.2⟩

lemma deligneReindex_le_iff (P Q:Deligne M) :
    deligneReindexMap M e P≤deligneReindexMap M e Q ↔ P≤Q := by
  change (e '' P.val.1⊆e '' Q.val.1 ∧ artinReindex M e '' P.val.2⊆artinReindex M e '' Q.val.2) ↔ _
  rw [Set.image_subset_image_iff e.injective,Set.image_subset_image_iff (artinReindex M e).injective]
  rfl

lemma deligneReindex_surjective : Function.Surjective (deligneReindexMap M e) := by
  intro Q
  let A:=e ⁻¹' Q.val.1
  have hA:e '' A=Q.val.1:=Set.image_preimage_eq _ e.surjective
  have hsp:IsSpherical M A:=(spherical_reindex M e A).mp (by rw [hA];exact Q.property.1)
  obtain ⟨y,hy⟩:=Q.property.2
  obtain ⟨x,rfl⟩:=(artinReindex M e).surjective y
  refine ⟨⟨(A,rightCoset M A x),hsp,x,rfl⟩,?_⟩
  apply Subtype.ext
  change (e '' A,artinReindex M e '' rightCoset M A x)=Q.val
  rw [rightCoset_reindex,hA,← hy]

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_TypedRightCoset
attribute [-instance] _root_.OAI.HarmonicArtin.instPartialOrderLiftedPuncturedBoundary _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset
attribute [-simp] _root_.OAI.HarmonicArtin.positiveToArtin_generator _root_.OAI.HarmonicArtin.positiveToArtin_word
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
universe u
variable {S:Type u} (M:CoxeterMatrix S)

def typedRightCoset (T:Set S) (hT:IsSpherical M T) (x:Artin M) : Deligne M :=
  ⟨(T,rightCoset M T x),hT,x,rfl⟩

lemma cellToDeligne_le_typedRightCoset (a:LiftedCell M) (T:Set S)
    (hT:IsSpherical M T) (x:Artin M) :
    cellToDeligne M a≤typedRightCoset M T hT x ↔
      a.2.val⊆T ∧ x*a.1∈artinParabolic M T := by
  change (a.2.val⊆T ∧ rightCoset M a.2.val a.1⁻¹⊆rightCoset M T x) ↔ _
  constructor
  · rintro ⟨ht,hc⟩
    refine ⟨ht,?_⟩
    have ha:a.1⁻¹∈rightCoset M a.2.val a.1⁻¹:=by
      change a.1⁻¹*(a.1⁻¹)⁻¹∈artinParabolic M a.2.val
      simp
    have hi: a.1⁻¹*x⁻¹∈artinParabolic M T:=hc ha
    simpa using (artinParabolic M T).inv_mem hi
  · rintro ⟨ht,hx⟩
    refine ⟨ht,?_⟩
    intro g hg
    change g*(a.1⁻¹)⁻¹∈artinParabolic M a.2.val at hg
    change g*x⁻¹∈artinParabolic M T
    have hga: g*a.1∈artinParabolic M T:=artinParabolic_mono M ht (by simpa using hg)
    have hh:=(artinParabolic M T).mul_mem hga ((artinParabolic M T).inv_mem hx)
    simpa only [mul_inv_rev,mul_assoc,mul_inv_cancel_left] using hh

end HarmonicArtin

end OAI
end


