-- Prove2me | Definitions.Def_OAIQ236Ap007
-- name    : OAIQ236Ap007
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T19:52:29.749094+00:00
-- url     : https://prove2.me/theorems/d5524b1f-0dca-4d2a-aa70-302b19ad9061
-- title:
--   Definitions bundle OAIQ236Ap007 of the split of OpenAI, Parabolic intersections in Artin groups
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.HarmonicArtin.ParabolicIntersections.unconditional_arbitrary_intersections`, `OAI.HarmonicArtin.ParabolicIntersections.unconditional_nonclique_dynamics`, `OAI.HarmonicArtin.ParabolicIntersections.unconditional_parabolic_closure` and `OAI.HarmonicArtin.ParabolicIntersections.unconditional_parabolic_intersections`, carved from OpenAI's openai/math development (OpenAI, *Parabolic intersections in Artin groups*, OpenAI Math Release, September 23, 2026, result family 254, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 212 declarations of OpenAI's Lean: 84 definitions, 1 inductive type or structure, 4 instances and 123 theorems. The definitions and types are `OAI.HarmonicArtin.ParabolicIntersections.visualEdgeTransitiveAction`, `OAI.HarmonicArtin.ParabolicIntersections.visualGraph`, `OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.cornerPath`, `OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.testIndex`, `OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.layerIndexEquiv`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.AdjacentTestIndex`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.AmplitudeCoreIndex`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.ChainIsomorphism.termwiseSplit`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.ClassColorSupport`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.ClassCone`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.ClassOutsideCap`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.ClassOutsideFloor`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.FiniteModel.positiveWord`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.FiniteModel.positiveWordMap`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.HomotopyEquivalence.coneSource`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.HomotopyEquivalence.coneTarget`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.HomotopyEquivalence.negativeTwistModern`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.HomotopyEquivalence.positiveTwistModern`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.Map.homotopyConeMap`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.Map.inverseMatrix`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.Map.scalarMatrix`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.NegativeAmplitudeCoreIndex`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.PlacementSupported`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.ScalarKernel`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.TermwiseSplitInjection.trans`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.TestUpperBound`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.UnfoldedPresentation`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.allPureIndex`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.blockInclusionMap`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.blockProjectionMap`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.canonicalLowTarget`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.coefficientOutgoing`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.emptyTestIndex`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.extendLayer`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.finiteSumTopTestEquiv`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.generatorTokenTest`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.highConeNormalized`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.highProjection`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.highPureIndex`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.highRestriction` and 45 more.
--
--   **Sources.** They come from these modules of lean/OAI/Topology, in whole or in part: `ArtinGroups_Complexes_ActedIndex`, `ArtinGroups_Complexes_ArrowShift`, `ArtinGroups_Complexes_BlockClosed`, `ArtinGroups_Complexes_Capped`, `ArtinGroups_Complexes_CoefficientTopDual`, `ArtinGroups_Complexes_ColorSupport`, `ArtinGroups_Complexes_Cone`, `ArtinGroups_Complexes_Cone2`, `ArtinGroups_Complexes_DownClosed`, `ArtinGroups_Complexes_EmptyTestIndex`, `ArtinGroups_Complexes_ExtendLayer`, `ArtinGroups_Complexes_GeneratorTokenTest`, `ArtinGroups_Complexes_HighConeIndex`, `ArtinGroups_Complexes_HomSpaceDuality`, `ArtinGroups_Complexes_HomSpacePairing`, `ArtinGroups_Complexes_HomotopyConeMap`, `ArtinGroups_Complexes_InitialProbeTestUpper`, `ArtinGroups_Complexes_InverseMatrix`, `ArtinGroups_Complexes_InverseWordAction`, `ArtinGroups_Complexes_LeftMatrix`, `ArtinGroups_Complexes_LowMatrix`, `ArtinGroups_Complexes_NegativeAmplitudeCoreIndex`, `ArtinGroups_Complexes_NegativeConeIndex`, `ArtinGroups_Complexes_NegativeTwistModern`, `ArtinGroups_Complexes_OutsideCap`, `ArtinGroups_Complexes_PlacedProjective`, `ArtinGroups_Complexes_PositiveConeIndex`, `ArtinGroups_Complexes_PositiveTwistModern`, `ArtinGroups_Complexes_PositiveWord`, `ArtinGroups_Complexes_PureLayerSelf`, `ArtinGroups_Complexes_PureSupportedCycles`, `ArtinGroups_Complexes_RestrictExtendLayerMul`, `ArtinGroups_Complexes_RestrictLayer`, `ArtinGroups_Complexes_ScalarExactNotZero`, `ArtinGroups_Complexes_ScalarKernel`, `ArtinGroups_Complexes_ScalarSupported`, `ArtinGroups_Complexes_ScalarSupportedCochainShift`, `ArtinGroups_Complexes_ScalarSupportedTokenShift`, `ArtinGroups_Complexes_SumTestEquiv`, `ArtinGroups_Complexes_SumTruncationEquiv`, `ArtinGroups_Complexes_TargetLow`, `ArtinGroups_Complexes_TestComplexVertexDifferential`, `ArtinGroups_Complexes_TestUpperBound`, `ArtinGroups_Complexes_TokenShift`, `ArtinGroups_Complexes_TwistNewTestIndex`, `ArtinGroups_Complexes_UnfoldedPresentation`, `ArtinGroups_Complexes_WordInverseModel`, `ArtinGroups_Coxeter_ParabolicProductMap`, `ArtinGroups_Functors_LayerIndexEquiv`, `ArtinGroups_Functors_Path2`, `ArtinGroups_Functors_TestIndex2`, `ArtinGroups_Functors_ZigzagLinear`, `ArtinGroups_Harmonic_CosetBelow`, `ArtinGroups_Harmonic_FusionVertex`, `ArtinGroups_Harmonic_MaximalReducedMonoidPrefix`, `ArtinGroups_Harmonic_MaximalReducedPositivePrefix`, `ArtinGroups_Harmonic_PositiveLiftSimple`, `ArtinGroups_Harmonic_RestrictedArtinHom`, `ArtinGroups_ParabolicIntersections_VisualEdgeTransitive`, `ArtinGroups_ParabolicIntersections_VisualTree`, `ArtinGroups_Quivers_CoefficientMatrix`, `ArtinGroups_Quivers_Level`, `ArtinGroups_Quivers_PathTwo`, `ArtinGroups_Quivers_PathTwoSelf`, `ArtinGroups_Quivers_PathZero`, `ArtinGroups_Quivers_ProbeVertex`, `ArtinGroups_Quivers_SignDiagonal`, `ArtinGroups_Quivers_TokenTestVector`, `ArtinGroups_Quivers_TraceLinear`, `ArtinGroups_Quivers_UnitTestVector`, `ArtinGroups_Quivers_VertexLinear`, `ArtinGroups_Realizations_NerveChain`, `ArtinGroups_Realizations_NerveOrderMap`, `ArtinGroups_Realizations_RealizeSimplex`.
--
--   **Imports.** It imports the published bundle `Def_ArtinParabolicIntersections`; the bundles `OAIQ236Ap002`, `OAIQ236Ap003` and `OAIQ236Ap004` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ236Ap009` and `OAIQ236Ap010`.
-- source:
--   OpenAI, Parabolic intersections in Artin groups, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 254; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Parabolic-intersections-in-Artin-groups-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Topology at commit adc7f12

import Mathlib
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.List.ChainOfFn
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.PushoutI
import Mathlib.Topology.MetricSpace.Isometry
import Definitions.Def_ArtinParabolicIntersections
import Definitions.Def_OAIQ236Ap002
import Definitions.Def_OAIQ236Ap003
import Definitions.Def_OAIQ236Ap004

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_ActedIndex
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

variable {V A K I : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I]

abbrev AmplitudeCoreIndex (E : BasedComplex Q (K := K) I) (α : V) :=
  {u : TestIndex Q E.placement α // Path.length u.2.val ≠ 0} ⊕
    {i : I // (E.placement i).color ≠ α}

noncomputable instance amplitudeCoreFintype (E : BasedComplex Q (K := K) I) (α : V) :
    Fintype (AmplitudeCoreIndex Q E α) := by
  classical
  unfold AmplitudeCoreIndex
  infer_instance

noncomputable instance amplitudeCoreDecidable (E : BasedComplex Q (K := K) I) (α : V) :
    DecidableEq (AmplitudeCoreIndex Q E α) := fun a b => instDecidableEqSum a b

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_TokenShift
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

variable {V A K I : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I]

noncomputable def tokenShift (E : BasedComplex Q (K := K) I) :
    BasedComplex Q (K := K) I where
  placement i := ⟨(E.placement i).color, (E.placement i).cochain - 1,
    (E.placement i).internal + 2⟩
  differential := -E.differential
  entries := projectiveEntries_neg Q E.entries
  degree i j := by
    constructor
    · intro h
      change -E.differential i j = 0
      rw [(E.degree i j).1 (by dsimp only at h; omega), neg_zero]
    · change Homogeneous Q (0 + ((E.placement i).internal + 2) -
        ((E.placement j).internal + 2)) (-E.differential i j)
      convert homogeneous_neg Q (E.degree i j).2 using 1 <;> first | (with_reducible_and_instances rfl) | (omega)
  square_zero := by rw [Matrix.neg_mul, Matrix.mul_neg, neg_neg, E.square_zero]

def testShiftIndexEquiv (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) (α : V) :
    (TestIndex Q E.placement α ⊕ TestIndex Q E.placement α ⊕ TestIndex Q E.placement α) ≃
      TestIndex Q (E.positiveTwist Q α).placement α where
  toFun
    | .inl u => ⟨.inl u, selfCornerEquiv Q hn α false⟩
    | .inr (.inl u) => ⟨.inr u.1, u.2⟩
    | .inr (.inr u) => ⟨.inl u, selfCornerEquiv Q hn α true⟩
  invFun
    | ⟨.inl u, p⟩ => if (selfCornerEquiv Q hn α).symm p then .inr (.inr u) else .inl u
    | ⟨.inr i, p⟩ => .inr (.inl ⟨i, p⟩)
  left_inv u := by rcases u with u | u | u <;> rfl
  right_inv u := by
    rcases u with ⟨u | i, p⟩
    · have he := (selfCornerEquiv Q hn α).apply_symm_apply p
      cases h : (selfCornerEquiv Q hn α).symm p
      · simp only [h, Bool.false_eq_true, ↓reduceIte]
        congr 1
        change (selfCornerEquiv Q hn α false : _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.CornerPath Q α α) = p
        simpa only [h] using he
      · simp only [h, ↓reduceIte]
        congr 1
        change (selfCornerEquiv Q hn α true : _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.CornerPath Q α α) = p
        simpa only [h] using he
    · rfl

noncomputable def normalizedTestTwist (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) (α : V) :=
  ((E.positiveTwist Q α).testComplex Q α).reindex Q (testShiftIndexEquiv Q hn E α)

lemma normalizedTestTwist_pivot_entry (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) (α : V) (u v : TestIndex Q E.placement α) :
    (normalizedTestTwist Q hn E α).differential (.inl u) (.inr (.inl v)) =
      projectiveIdentity Q (testPlacement Q E.placement α) u v := by
  classical
  change (pathCoordinates Q (K := K) (pathBasis Q (K := K) (.inl α) *
    evaluationMatrix Q E.placement α u v.1) v.2.val) • vertexId Q (K := K) α = _
  rw [pathBasis_vertex]
  simp only [evaluationMatrix]
  by_cases h : u.1 = v.1
  · rcases u with ⟨i, p⟩
    rcases v with ⟨j, q⟩
    dsimp only at h
    subst j
    simp only [ite_true, if_true, cornerPath_left, pathBasis_coordinates, projectiveIdentity,
      Matrix.diagonal_apply, testPlacement, Sigma.mk.inj_iff, heq_eq_eq, true_and]
    simp only [Subtype.val_inj, ite_smul, one_smul, zero_smul]
  · have huv : u ≠ v := fun he => h (congrArg Sigma.fst he)
    simp only [ite_eq_right h, MulZeroClass.mul_zero, coordinates_zero, zero_smul,
      projectiveIdentity, Matrix.diagonal_apply, ite_eq_right huv]

omit [DecidableEq I] in
lemma normalizedTestTwist_unit_token (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) (α : V) (u v : TestIndex Q E.placement α) :
    (normalizedTestTwist Q hn E α).differential (.inl u) (.inr (.inr v)) = 0 := by
  change (pathCoordinates Q (K := K) (pathBasis Q (K := K) (.inl α) *
    (-((testMatrix Q E.placement E.placement α E.differential) u v • vertexId Q (K := K) α)))
      (.inr (.inr α))) • vertexId Q (K := K) α = 0
  rw [pathBasis_vertex, _root_.mul_neg, mul_smul, vertexId_mul_self]
  rw [map_neg, Pi.neg_apply, coordinates_smul, pathCoordinates_token, token_vertexId]
  simp only [Pi.zero_apply, MulZeroClass.mul_zero, neg_zero, zero_smul]

omit [DecidableEq I] in
lemma normalizedTestTwist_token_token (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) (α : V) (u v : TestIndex Q E.placement α) :
    (normalizedTestTwist Q hn E α).differential (.inr (.inr u)) (.inr (.inr v)) =
      -(E.testComplex Q α).differential u v := by
  have ht : tokenBasis Q (K := K) α * vertexId Q α = tokenBasis Q α := by
    simpa only [Path.target, pathBasis_token] using
      (pathBasis_right Q (K := K) (.inr (.inr α)))
  change (pathCoordinates Q (K := K) (pathBasis Q (K := K) (.inr (.inr α)) *
    (-((testMatrix Q E.placement E.placement α E.differential) u v • vertexId Q (K := K) α)))
      (.inr (.inr α))) • vertexId Q (K := K) α =
    -((testMatrix Q E.placement E.placement α E.differential) u v • vertexId Q (K := K) α)
  rw [pathBasis_token, _root_.mul_neg, mul_smul, ht]
  simp only [map_neg, Pi.neg_apply, coordinates_smul, ← pathBasis_token,
    pathBasis_coordinates, ite_true, if_true, _root_.mul_one, neg_smul]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_ArrowShift
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K I : Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I]

abbrev AdjacentTestIndex (E:BasedComplex Q (K:=K) I) (α β:V) :=
  TestIndex Q E.placement β ⊕ TestIndex Q E.placement β ⊕
    TestIndex Q E.placement β ⊕ TestIndex Q E.placement β ⊕ TestIndex Q E.placement α

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_BlockClosed
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
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

omit [Fintype V] [DecidableEq A] in
lemma blockInclusion_entries (E:BasedComplex Q (K:=K) I) (T:Set I) :
    ProjectiveEntries Q (fun i:T=>E.placement i) E.placement (blockInclusion Q E T) :=
  ⟨fun i j=>(projectiveEntries_identity Q).1 (i:I) j,
   fun i j=>(projectiveEntries_identity Q).2 (i:I) j⟩
omit [Fintype V] [DecidableEq A] in
lemma blockProjection_entries (E:BasedComplex Q (K:=K) I) (T:Set I) :
    ProjectiveEntries Q E.placement (fun i:T=>E.placement i) (blockProjection Q E T) :=
  ⟨fun i j=>(projectiveEntries_identity Q).1 i (j:I),
   fun i j=>(projectiveEntries_identity Q).2 i (j:I)⟩

omit [Fintype V] [DecidableEq A] in
lemma blockInclusion_commute (E:BasedComplex Q (K:=K) I) (T:Set I) (h:BlockClosed Q E T) :
    (blockRestriction Q E T h).differential*blockInclusion Q E T=
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
  · have hz:E.differential i j=0 := by
      by_contra hh
      exact hj ((h i j hh).mp i.property)
    rw [hz]
    apply Finset.sum_eq_zero
    intro k _
    have hne:(k:I)≠j := by intro he; exact hj (he ▸ k.property)
    rw [ite_eq_right hne,MulZeroClass.mul_zero]

omit [Fintype V] [DecidableEq A] in
lemma blockProjection_commute (E:BasedComplex Q (K:=K) I) (T:Set I) (h:BlockClosed Q E T) :
    E.differential*blockProjection Q E T=
      blockProjection Q E T*(blockRestriction Q E T h).differential := by
  rw [mul_blockProjection Q E T _ _ E.entries]
  apply Matrix.ext
  intro i j
  change E.differential i j=(∑ k:T,(if i=(k:I) then vertexId Q (K:=K) (E.placement i).color else 0)*E.differential k j)
  by_cases hi:i∈T
  · let i':T:=⟨i,hi⟩
    have he (k:T) : (i=(k:I)) ↔ i'=k := by simp only [i',Subtype.ext_iff]
    simp only [he,ite_mul,zero_mul,Fintype.sum_ite_eq]
    exact (E.entries.1 i j).symm
  · have hz:E.differential i j=0 := by
      by_contra hh
      exact hi ((h i j hh).mpr j.property)
    rw [hz]
    symm
    apply Finset.sum_eq_zero
    intro k _
    have hne:i≠(k:I) := by intro he; exact hi (he.symm ▸ k.property)
    rw [ite_eq_right hne,zero_mul]

noncomputable def blockInclusionMap (E:BasedComplex Q (K:=K) I) (T:Set I) (h:BlockClosed Q E T) :
    Map Q (blockRestriction Q E T h) E where
  matrix:=blockInclusion Q E T
  entries:=blockInclusion_entries Q E T
  degree:=fun i j=>mapDegree_identity Q (i:I) j
  commute:=blockInclusion_commute Q E T h

noncomputable def blockProjectionMap (E:BasedComplex Q (K:=K) I) (T:Set I) (h:BlockClosed Q E T) :
    Map Q E (blockRestriction Q E T h) where
  matrix:=blockProjection Q E T
  entries:=blockProjection_entries Q E T
  degree:=fun i j=>mapDegree_identity Q i (j:I)
  commute:=blockProjection_commute Q E T h

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Quivers_Level
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.instAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag

variable {V A K I J L : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V]

lemma mapDegree_level_bound {p : I → GeneratorPlacement V} {q : J → GeneratorPlacement V}
    {M : Matrix I J (Q.Zigzag K)} {n v : ℤ} (h : MapDegree Q p q n v M)
    {i : I} {j : J} (hne : M i j ≠ 0) :
    (q j).level ≤ (p i).level + n + v := by
  have hc : (q j).cochain = (p i).cochain + n := by
    by_contra hc
    exact hne ((h i j).1 hc)
  have ha := homogeneous_nonzero_degree Q (h i j).2 hne
  dsimp only [GeneratorPlacement.level]
  omega

lemma atLevel_degree_neg (p : I → GeneratorPlacement V) (q : J → GeneratorPlacement V)
    (M : Matrix I J (Q.Zigzag K)) (d : ℤ) (hM : MapDegree Q p q (-1) 0 M) :
    atLevel Q p q M d = 0 := by
  apply Matrix.ext
  intro i j
  change M i.val j.val = 0
  by_contra hne
  have h := mapDegree_level_bound Q hM hne
  rw [i.property, j.property] at h
  omega

namespace BasedComplex

variable [Fintype I] [Fintype J] [Fintype L]

lemma map_level_bound {E : BasedComplex Q (K := K) I} {F : BasedComplex Q (K := K) J}
    (f : Map Q E F) (i : I) (j : J) (h : f.matrix i j ≠ 0) :
    (F.placement j).level ≤ (E.placement i).level := by
  simpa only [add_zero] using mapDegree_level_bound Q f.degree h

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Quivers_TraceLinear
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag

variable {V A K I J : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V]

lemma trace_smul (r : K) (x : Q.Zigzag K) : trace Q (r • x) = r * trace Q x := by
  simp only [trace, token_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]

def traceLinear : Q.Zigzag K →ₗ[K] K where
  toFun := trace Q
  map_add' := trace_add Q
  map_smul' := by intro r x; exact trace_smul Q r x

namespace BasedComplex
variable [Fintype I] [Fintype J]

noncomputable def supertrace (E : BasedComplex Q (K := K) I) :
    Matrix I I (Q.Zigzag K) →ₗ[K] K where
  toFun f := ∑ i, cochainSign (K := K) (E.placement i).cochain * trace Q (f i i)
  map_add' f g := by
    simp only [Matrix.add_apply, trace_add, _root_.mul_add, Finset.sum_add_distrib]
  map_smul' r f := by
    simp only [Matrix.smul_apply, smul_eq_mul, RingHom.id_apply, trace_smul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

lemma supertrace_mul (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) {n v : ℤ}
    {f : Matrix I J (Q.Zigzag K)} (hf : MapDegree Q E.placement F.placement n v f)
    (g : Matrix J I (Q.Zigzag K)) :
    supertrace Q F (g * f) = cochainSign (K := K) n * supertrace Q E (f * g) := by
  change (∑ j, cochainSign (K := K) _ * traceLinear Q (∑ i, g j i * f i j)) =
    cochainSign (K := K) n * ∑ i, cochainSign (K := K) _ * traceLinear Q (∑ j, f i j * g j i)
  simp only [map_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hc : (F.placement j).cochain = (E.placement i).cochain + n
  · change cochainSign (K := K) _ * trace Q (g j i * f i j) =
      cochainSign (K := K) n * (cochainSign (K := K) _ * trace Q (f i j * g j i))
    rw [hc, cochainSign_add, trace_mul_comm Q (g j i)]
    ring
  · rw [(hf i j).1 hc, MulZeroClass.mul_zero, MulZeroClass.zero_mul,
      map_zero, MulZeroClass.mul_zero, MulZeroClass.mul_zero]
    exact (MulZeroClass.mul_zero _).symm

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_ExtendLayer
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype
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

def extendLayer (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J)
    (l k : ℤ) :
    Matrix {i // (E.placement i).level = l} {j // (F.placement j).level = k} (Q.Zigzag K) →ₗ[K]
      Matrix I J (Q.Zigzag K) where
  toFun f i j := if hi : (E.placement i).level = l then
      if hj : (F.placement j).level = k then f ⟨i, hi⟩ ⟨j, hj⟩ else 0 else 0
  map_add' f g := by
    apply Matrix.ext
    intro i j
    change (if hi : (E.placement i).level = l then
      if hj : (F.placement j).level = k then f ⟨i, hi⟩ ⟨j, hj⟩ + g ⟨i, hi⟩ ⟨j, hj⟩ else 0 else 0) =
      (if hi : (E.placement i).level = l then
      if hj : (F.placement j).level = k then f ⟨i, hi⟩ ⟨j, hj⟩ else 0 else 0) +
      (if hi : (E.placement i).level = l then
      if hj : (F.placement j).level = k then g ⟨i, hi⟩ ⟨j, hj⟩ else 0 else 0)
    split_ifs <;> simp only [add_zero]
  map_smul' r f := by
    apply Matrix.ext
    intro i j
    change (if hi : (E.placement i).level = l then
      if hj : (F.placement j).level = k then r • f ⟨i, hi⟩ ⟨j, hj⟩ else 0 else 0) =
      r • (if hi : (E.placement i).level = l then
      if hj : (F.placement j).level = k then f ⟨i, hi⟩ ⟨j, hj⟩ else 0 else 0)
    split_ifs <;> simp only [smul_zero]

lemma extendLayer_entry (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (l k : ℤ)
    (f : Matrix {i // (E.placement i).level = l} {j // (F.placement j).level = k} (Q.Zigzag K))
    (i : I) (j : J) :
    extendLayer Q E F l k f i j = if hi : (E.placement i).level = l then
      if hj : (F.placement j).level = k then f ⟨i, hi⟩ ⟨j, hj⟩ else 0 else 0 := rfl

lemma extendLayer_apply (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (l k : ℤ)
    (f : Matrix {i // (E.placement i).level = l} {j // (F.placement j).level = k} (Q.Zigzag K))
    (i : {i // (E.placement i).level = l}) (j : {j // (F.placement j).level = k}) :
    extendLayer Q E F l k f i j = f i j := by
  change (if hi : (E.placement i.val).level = l then
      if hj : (F.placement j.val).level = k then f ⟨i.val, hi⟩ ⟨j.val, hj⟩ else 0 else 0) = f i j
  rw [dite_eq_left i.property, dite_eq_left j.property]

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

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Quivers_PathZero
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype A] [DecidableEq V]

variable {I J L : Type*}

lemma matrixZero_eq_zero {f : Matrix I J (Q.Zigzag K)} (hf : PositiveMatrix Q f) :
    matrixZero Q f = 0 := by
  apply Matrix.ext
  intro i j
  exact pathZero_eq_zero Q (hf i j)

end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_RestrictLayer
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype
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

lemma restrictLayer_extend (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (l k : ℤ)
    (f : Matrix {i // (E.placement i).level = l} {j // (F.placement j).level = k} (Q.Zigzag K)) :
    restrictLayer Q E F l k (extendLayer Q E F l k f) = f := by
  apply Matrix.ext
  intro i j
  exact extendLayer_apply Q E F l k f i j

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Quivers_CoefficientMatrix
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype
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

end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Quivers_PathTwo
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype A] [DecidableEq V]

variable {I J L : Type*}

lemma positive_matrix_decomposition {f : Matrix I J (Q.Zigzag K)} (hf : PositiveMatrix Q f) :
    matrixOne Q f + matrixTwo Q f = f := by
  have h := matrix_decomposition Q f
  rw [matrixZero_eq_zero Q hf, zero_add] at h
  exact h

lemma matrixTwo_mul_positive [Fintype J]
    (f : Matrix I J (Q.Zigzag K)) {g : Matrix J L (Q.Zigzag K)}
    (hg : PositiveMatrix Q g) : matrixTwo Q f * g = 0 := by
  apply Matrix.ext
  intro i j
  rw [Matrix.mul_apply]
  exact Finset.sum_eq_zero fun t _ => pathTwo_mul_positive Q _ (hg t j)

lemma positive_mul_matrixTwo [Fintype J]
    {f : Matrix I J (Q.Zigzag K)} (hf : PositiveMatrix Q f)
    (g : Matrix J L (Q.Zigzag K)) : f * matrixTwo Q g = 0 := by
  apply Matrix.ext
  intro i j
  rw [Matrix.mul_apply]
  exact Finset.sum_eq_zero fun t _ => positive_mul_pathTwo Q (hf i t) _

namespace BasedComplex
variable [Fintype I] [Fintype J]

noncomputable def linearHomDifferential (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (n : ℤ) :
    Matrix I J (Q.Zigzag K) →ₗ[K] Matrix I J (Q.Zigzag K) where
  toFun f := matrixOne Q E.differential * f -
    cochainSign (K := K) n • (f * matrixOne Q F.differential)
  map_add' f g := by
    simp only [Matrix.mul_add, Matrix.add_mul, smul_add]
    abel
  map_smul' r f := by
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_sub, RingHom.id_apply]
    rw [smul_comm]

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Quivers_PathTwoSelf
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype
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

end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_Capped
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype
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

lemma extendLayer_coefficient (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (l k : ℤ)
    {f : Matrix {i // (E.placement i).level = l} {j // (F.placement j).level = k} (Q.Zigzag K)}
    (hf : CoefficientMatrix Q f) : CoefficientMatrix Q (extendLayer Q E F l k f) := by
  intro i j
  simp only [extendLayer_entry]
  split_ifs with hi hj
  · exact hf ⟨i, hi⟩ ⟨j, hj⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

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

lemma extend_restrictLayer (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (l k : ℤ) {f : Matrix I J (Q.Zigzag K)}
    (hs : ∀ i j, (E.placement i).level ≠ l ∨ (F.placement j).level ≠ k → f i j = 0) :
    extendLayer Q E F l k (restrictLayer Q E F l k f) = f := by
  apply Matrix.ext
  intro i j
  rw [extendLayer_entry]
  split_ifs with hi hj
  · rfl
  · exact (hs i j (Or.inr hj)).symm
  · exact (hs i j (Or.inl hi)).symm

lemma extend_mul_matrixTwo_support (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (q d : ℤ)
    (f : Matrix {i // (E.placement i).level = q} {j // (F.placement j).level = d} (Q.Zigzag K))
    (i : I) (j : J) (h : (E.placement i).level ≠ q ∨ (F.placement j).level ≠ d-1) :
    (extendLayer Q E F q d f * matrixTwo Q F.differential) i j = 0 := by
  classical
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro t _
  rw [extendLayer_entry]
  split_ifs with hi ht
  · have hj : (F.placement j).level ≠ (F.placement t).level - 1 := by
      rcases h with hh | hh
      · exact (hh hi).elim
      · simpa only [ht] using hh
    change f ⟨i, hi⟩ ⟨t, ht⟩ * pathTwo Q (F.differential t j) = 0
    rw [pathTwo_eq_zero Q (differential_token_level Q F hj), MulZeroClass.mul_zero]
  · exact MulZeroClass.zero_mul _
  · exact MulZeroClass.zero_mul _

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_HomSpacePairing
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
variable {I J : Type*} [Fintype I] [Fintype J]

omit [DecidableEq A] in
lemma supertrace_mul_single [DecidableEq I] [DecidableEq J]
    (E : BasedComplex Q (K := K) I) (f : Matrix I J (Q.Zigzag K)) (i : I) (j : J)
    (z : Q.Zigzag K) :
    supertrace Q E (f * Matrix.single j i z) =
      cochainSign (K := K) (E.placement i).cochain * trace Q (f i j * z) := by
  unfold supertrace
  change (∑ k, cochainSign (K := K) (E.placement k).cochain *
    trace Q ((f * Matrix.single j i z) k k)) = _
  rw [Finset.sum_eq_single i]
  · rw [Matrix.mul_single_apply_same]
  · intro k _ hk
    rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hk, trace_zero, MulZeroClass.mul_zero]
  · intro h
    exact (h (Finset.mem_univ i)).elim

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_HomSpaceDuality
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
variable {I J : Type*} [Fintype I] [Fintype J]

local instance zigzagFiniteDimensional : FiniteDimensional K (Q.Zigzag K) :=
  (pathBasis Q (K := K)).finiteDimensional_of_finite

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Quivers_VertexLinear
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype A] [DecidableEq V]
variable {I J L : Type*}

lemma tokenMatrix_smul (r : K) {f : Matrix I J (Q.Zigzag K)}
    (hf : TokenMatrix Q f) : TokenMatrix Q (r • f) := by
  intro i j
  constructor
  · change r • (f i j).vertex = 0
    rw [(hf i j).1, smul_zero]
  · change r • (f i j).arrow = 0
    rw [(hf i j).2, smul_zero]

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

end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_LeftMatrix
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype A] [DecidableEq V]
variable {I J L : Type*} [Fintype I] [Fintype J] [Fintype L]

lemma coefficientMap_row_support {E : BasedComplex Q (K := K) I}
    {F : BasedComplex Q (K := K) J} (f : Map Q E F)
    (hf : CoefficientMatrix Q f.matrix) (U : Set V)
    (hF : ∀ j, (F.placement j).color ∈ U) (i : I) (j : J)
    (hi : (E.placement i).color ∉ U) : f.matrix i j = 0 := by
  apply Zigzag.ext
  · funext w
    change (f.matrix i j).vertex w = 0
    by_contra hw
    have he := (reduction_support Q f.entries f.degree i j w hw).1
    exact hi (he ▸ hF j)
  · exact (hf i j).1
  · exact (hf i j).2

noncomputable def leftMatrix (a : Matrix I J (Q.Zigzag K)) :
    Matrix J L (Q.Zigzag K) →ₗ[K] Matrix I L (Q.Zigzag K) where
  toFun f := a * f
  map_add' _ _ := Matrix.mul_add _ _ _
  map_smul' _ _ := Matrix.mul_smul _ _ _

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_RestrictExtendLayerMul
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype A] [DecidableEq V]
variable {I J : Type*} [Fintype I] [Fintype J]

lemma restrict_extendLayer_mul (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (q d k : ℤ)
    (f : Matrix {i // (E.placement i).level = q} {j // (F.placement j).level = d} (Q.Zigzag K))
    (g : Matrix J J (Q.Zigzag K)) :
    restrictLayer Q E F q k (extendLayer Q E F q d f * g) =
      f * restrictLayer Q F F d k g := by
  classical
  apply Matrix.ext
  intro i j
  change (∑ t, extendLayer Q E F q d f i.val t * g t j.val) =
    ∑ t : {j // (F.placement j).level = d}, f i t * g t.val j.val
  symm
  apply Fintype.sum_of_injective Subtype.val Subtype.val_injective
  · intro t ht
    have hh : (F.placement t).level ≠ d := fun h => ht ⟨⟨t, h⟩, rfl⟩
    rw [extendLayer_entry, dite_eq_left i.property, dite_eq_right hh, MulZeroClass.zero_mul]
  · intro t
    rw [extendLayer_apply Q E F q d f i t]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_CoefficientTopDual
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.corner_val _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_reverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def topSocleMatrix (α : V) (x : I → K) (y : J → K) :
    Matrix I J (Q.Zigzag K) := fun i j => (x i * y j) • vertexId Q α

omit [Fintype V] [DecidableEq A] [Fintype I] [Fintype J] in
lemma topSocleMatrix_ne_zero (α : V) {x : I → K} {y : J → K}
    (hx : x ≠ 0) (hy : y ≠ 0) : topSocleMatrix Q α x y ≠ 0 := by
  obtain ⟨i,hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hx (funext hn)
  obtain ⟨j,hj⟩ : ∃ j, y j ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hy (funext hn)
  intro hz
  have he := congrArg (fun f : Matrix I J (Q.Zigzag K) => (f i j).vertex α) hz
  have h : x i * y j = 0 := by
    simpa [topSocleMatrix, vertexId_eval] using he
  exact (mul_ne_zero hi hj) h

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_UnfoldedPresentation
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

universe u

variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

structure UnfoldedPresentation (M : CoxeterMatrix V) : Prop where
  relation (α β : V) : α = β ∨ M α β = 0 ∨
    (M α β = 2 ∧ OrthogonalVertices Q α β) ∨
    (M α β = 3 ∧ Nonempty (SimpleEdge Q α β))

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_DownClosed
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype
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

noncomputable def lowRestriction (E:BasedComplex Q (K:=K) I) (T:Set I) (h:DownClosed Q E T) :
    BasedComplex Q (K:=K) T := E.restrict Q T h.low_condition
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

omit [Fintype V] [DecidableEq A] in
lemma lowCone_source_retained (E:BasedComplex Q (K:=K) I) (T:Set I) (h:DownClosed Q E T)
    (i:T) (j:(Tᶜ:Set I)) : (lowConeNormalized Q E T h).differential (.inl i) (.inr (.inr j))=0 := by
  change (if (i:I)=(j:I) then vertexId Q (K:=K) (E.placement i).color else 0)=0
  have hn:(i:I)≠(j:I):=fun he=>j.property (he ▸ i.property)
  rw [ite_eq_right hn]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_LowMatrix
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype
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

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma homotopy_level_bound (E:BasedComplex Q (K:=K) I)
    (H:Matrix I I (Q.Zigzag K)) (hH:MapDegree Q E.placement E.placement (-1) 0 H)
    (i j:I) (h:H i j≠0) : (E.placement j).level≤(E.placement i).level := by
  have hh:=mapDegree_level_bound Q hH h
  omega

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Quivers_TokenTestVector
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.corner_val _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_reverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag
variable {V A K I : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A] [Fintype I]

lemma token_coordinates (α : V) (p : Path V A) :
    pathCoordinates Q (tokenBasis Q (K := K) α) p = if Sum.inr (Sum.inr α)=p then 1 else 0 := by
  rw [← pathBasis_token,pathBasis_coordinates]

noncomputable def tokenTestVector (p : I → GeneratorPlacement V) (α : V) :
    (I → K) →ₗ[K] (TestIndex Q p α → K) where
  toFun x i := x i.1 * pathCoordinates Q (tokenBasis Q α) i.2.val
  map_add' x y := by funext i; exact _root_.add_mul _ _ _
  map_smul' r x := by funext i; exact _root_.mul_assoc _ _ _

noncomputable def sumTokenTest (p : I → GeneratorPlacement V) (α : V) :
    (TestIndex Q p α → K) →ₗ[K] (I → K) where
  toFun x i := ∑ z : CornerPath Q α (p i).color, x ⟨i,z⟩
  map_add' x y := by funext i; exact Finset.sum_add_distrib
  map_smul' r x := by funext i; exact (Finset.mul_sum _ _ _).symm

omit [Fintype I] [DecidableEq A] in
lemma sumTokenTest_support (p : I → GeneratorPlacement V) (α : V) (c : ℤ)
    (x : TestIndex Q p α → K)
    (hx : ∀ i, ¬ ((p i.1).cochain=c ∧ Path.length i.2.val=2) → x i=0) :
    ∀ i, (p i).color ≠ α ∨ (p i).cochain ≠ c → sumTokenTest Q p α x i=0 := by
  intro i hi
  apply Finset.sum_eq_zero
  intro z hz
  apply hx
  rintro ⟨hc,hl⟩
  rcases hi with hi|hi
  · apply hi
    have he := corner_length_two Q z hl
    have ht := z.property.2
    rw [he] at ht
    exact ht.symm
  · exact hi hc

omit [Fintype I] in
lemma tokenTestVector_sum (p : I → GeneratorPlacement V) (α : V) (c : ℤ)
    (x : TestIndex Q p α → K)
    (hx : ∀ i, ¬ ((p i.1).cochain=c ∧ Path.length i.2.val=2) → x i=0) :
    tokenTestVector Q p α (sumTokenTest Q p α x) = x := by
  funext i
  change (∑ z : CornerPath Q α (p i.1).color, x ⟨i.1,z⟩) *
    pathCoordinates Q (tokenBasis Q α) i.2.val = x i
  by_cases hl : Path.length i.2.val=2
  · have he := corner_length_two Q i.2 hl
    rw [token_coordinates,ite_eq_left he.symm,_root_.mul_one]
    apply Finset.sum_eq_single i.2
    · intro z hz hzi
      apply hx
      rintro ⟨hc,hzlen⟩
      apply hzi
      apply Subtype.ext
      exact (corner_length_two Q z hzlen).trans he.symm
    · simp
  · rw [hx i (fun h => hl h.2)]
    rw [token_coordinates,ite_eq_right (fun he => hl (by rw [← he]; rfl)),MulZeroClass.mul_zero]

omit [Fintype I] in
lemma sumTokenTest_unit (p : I → GeneratorPlacement V) (α : V)
    (x : I → K) (hx : ∀ i, (p i).color≠α → x i=0) :
    sumTokenTest Q p α (tokenTestVector Q p α x)=x := by
  funext i
  by_cases hi : (p i).color=α
  · let z : CornerPath Q α (p i).color := ⟨Sum.inr (Sum.inr α),rfl,hi.symm⟩
    change (∑ w : CornerPath Q α (p i).color, x i * pathCoordinates Q (tokenBasis Q α) w.val)=x i
    rw [Finset.sum_eq_single z]
    · rw [token_coordinates,ite_eq_left rfl,_root_.mul_one]
    · intro w hw hwz
      rw [token_coordinates,ite_eq_right (fun he => hwz (Subtype.ext he.symm)),MulZeroClass.mul_zero]
    · simp
  · change (∑ w : CornerPath Q α (p i).color, x i * pathCoordinates Q (tokenBasis Q α) w.val)=x i
    rw [hx i hi]
    simp

omit [DecidableEq A] in
lemma trace_left_corner {α : V} (x : Zigzag Q K) (hx : vertexId Q α * x=x) :
    trace Q x=x.token α := by
  unfold trace
  apply Finset.sum_eq_single α
  · intro β hβ hβα
    have hh := coordinates_vertexId_left Q α x (Sum.inr (Sum.inr β))
    rw [hx] at hh
    simpa [Path.source,pathCoordinates_token,hβα,Ne.symm hβα] using hh
  · simp

lemma token_path_mul {α β : V} (p : CornerPath Q α β) (x : Zigzag Q K) :
    (pathBasis Q p.val*x).token α=pathCoordinates Q x (Path.dual Q p.val) := by
  rw [coordinates_trace,Path.dual_dual,trace_mul_comm]
  symm
  apply trace_left_corner
  rw [← _root_.mul_assoc,cornerPath_left]

lemma tokenTestVector_differential (E : BasedComplex Q (K := K) I) (α:V)
    (x : I → K) (hx : ∀ i, (E.placement i).color≠α → x i=0)
    (i : TestIndex Q E.placement α) :
    Matrix.vecMul (tokenTestVector Q E.placement α x)
      (testMatrix Q E.placement E.placement α E.differential).transpose i =
      ∑ j, x j * pathCoordinates Q (E.differential i.1 j) (Path.dual Q i.2.val) := by
  change (∑ z : TestIndex Q E.placement α, x z.1 * pathCoordinates Q (tokenBasis Q α) z.2.val *
    pathCoordinates Q (pathBasis Q i.2.val * E.differential i.1 z.1) z.2.val)=_
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hc : (E.placement j).color=α
  · let z : CornerPath Q α (E.placement j).color := ⟨Sum.inr (Sum.inr α),rfl,hc.symm⟩
    rw [Finset.sum_eq_single z]
    · rw [token_coordinates,ite_eq_left rfl,_root_.mul_one]
      change x j * (pathBasis Q i.2.val * E.differential i.1 j).token α = _
      rw [token_path_mul]
    · intro w hw hwz
      rw [token_coordinates,ite_eq_right (fun he => hwz (Subtype.ext he.symm)),
        MulZeroClass.mul_zero,MulZeroClass.zero_mul]
    · simp
  · simp only [hx j hc,MulZeroClass.zero_mul,Finset.sum_const_zero]

namespace BasedComplex

noncomputable def topTestCycles (E : BasedComplex Q (K := K) I) (α:V) (c:ℤ) :=
  ScalarCycles.supportedKernel (testMatrix Q E.placement E.placement α E.differential).transpose
    (fun i => (E.placement i.1).cochain=c ∧ Path.length i.2.val=2)

lemma sumTokenTest_top (E : BasedComplex Q (K := K) I) (α:V) (c:ℤ)
    {x : TestIndex Q E.placement α → K} (hx : x ∈ topTestCycles Q E α c) :
    sumTokenTest Q E.placement α x ∈ coefficientTopDual Q E α c := by
  have hs := sumTokenTest_support Q E.placement α c x hx.1
  constructor
  · exact hs
  · intro i a
    by_cases ha : Q.target a=α
    · by_cases ht : Q.source a=(E.placement i).color
      · let z : TestIndex Q E.placement α := ⟨i,Sum.inr (Sum.inl (Q.reverse a)),
          (Q.source_reverse a).trans ha,(Q.target_reverse a).trans ht⟩
        have hh := tokenTestVector_differential Q E α (sumTokenTest Q E.placement α x)
          (fun j h => hs j (Or.inl h)) z
        rw [tokenTestVector_sum Q E.placement α c x hx.1,hx.2] at hh
        simpa only [z,Path.dual,Q.reverse_reverse,pathCoordinates_arrow,mul_comm,Pi.zero_apply] using hh.symm
      · apply Finset.sum_eq_zero
        intro j hj
        have hz : (E.differential i j).arrow a=0 := by
          by_contra hn
          exact ht (coordinates_corner Q (p := Sum.inr (Sum.inl a))
            (E.entries.1 i j) (E.entries.2 i j) hn).1
        rw [hz,MulZeroClass.zero_mul]
    · apply Finset.sum_eq_zero
      intro j hj
      by_cases hjc : (E.placement j).color=α
      · have hz : (E.differential i j).arrow a=0 := by
          by_contra hn
          exact ha ((coordinates_corner Q (p := Sum.inr (Sum.inl a))
            (E.entries.1 i j) (E.entries.2 i j) hn).2.trans hjc)
        rw [hz,MulZeroClass.zero_mul]
      · rw [hs j (Or.inl hjc),MulZeroClass.mul_zero]

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Quivers_UnitTestVector
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.corner_val _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_reverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag
variable {V A K I : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A] [Fintype I]

lemma vertex_coordinates (α : V) (p : Path V A) :
    pathCoordinates Q (vertexId Q (K := K) α) p = if Sum.inl α=p then 1 else 0 := by
  rw [← pathBasis_vertex,pathBasis_coordinates]

noncomputable def unitTestVector (p : I → GeneratorPlacement V) (α : V) :
    (I → K) →ₗ[K] (TestIndex Q p α → K) where
  toFun x i := x i.1 * pathCoordinates Q (vertexId Q α) i.2.val
  map_add' x y := by funext i; exact _root_.add_mul _ _ _
  map_smul' r x := by funext i; exact _root_.mul_assoc _ _ _

noncomputable def sumUnitTest (p : I → GeneratorPlacement V) (α : V) :
    (TestIndex Q p α → K) →ₗ[K] (I → K) where
  toFun x i := ∑ z : CornerPath Q α (p i).color, x ⟨i,z⟩
  map_add' x y := by funext i; exact Finset.sum_add_distrib
  map_smul' r x := by funext i; exact (Finset.mul_sum _ _ _).symm

omit [Fintype I] [DecidableEq A] in
lemma sumUnitTest_support (p : I → GeneratorPlacement V) (α : V) (c : ℤ)
    (x : TestIndex Q p α → K)
    (hx : ∀ i, ¬ ((p i.1).cochain=c ∧ Path.length i.2.val=0) → x i=0) :
    ∀ i, (p i).color ≠ α ∨ (p i).cochain ≠ c → sumUnitTest Q p α x i=0 := by
  intro i hi
  apply Finset.sum_eq_zero
  intro z hz
  apply hx
  rintro ⟨hc,hl⟩
  rcases hi with hi|hi
  · apply hi
    have he := corner_length_zero Q z hl
    have ht := z.property.2
    rw [he] at ht
    exact ht.symm
  · exact hi hc

omit [Fintype I] in
lemma unitTestVector_sum (p : I → GeneratorPlacement V) (α : V) (c : ℤ)
    (x : TestIndex Q p α → K)
    (hx : ∀ i, ¬ ((p i.1).cochain=c ∧ Path.length i.2.val=0) → x i=0) :
    unitTestVector Q p α (sumUnitTest Q p α x) = x := by
  funext i
  change (∑ z : CornerPath Q α (p i.1).color, x ⟨i.1,z⟩) *
    pathCoordinates Q (vertexId Q α) i.2.val = x i
  by_cases hl : Path.length i.2.val=0
  · have he := corner_length_zero Q i.2 hl
    rw [vertex_coordinates,ite_eq_left he.symm,_root_.mul_one]
    apply Finset.sum_eq_single i.2
    · intro z hz hzi
      apply hx
      rintro ⟨hc,hzlen⟩
      apply hzi
      apply Subtype.ext
      exact (corner_length_zero Q z hzlen).trans he.symm
    · simp
  · rw [hx i (fun h => hl h.2)]
    rw [vertex_coordinates,ite_eq_right (fun he => hl (by rw [← he]; rfl)),MulZeroClass.mul_zero]

omit [Fintype I] in
lemma sumUnitTest_unit (p : I → GeneratorPlacement V) (α : V)
    (x : I → K) (hx : ∀ i, (p i).color≠α → x i=0) :
    sumUnitTest Q p α (unitTestVector Q p α x)=x := by
  funext i
  by_cases hi : (p i).color=α
  · let z : CornerPath Q α (p i).color := ⟨Sum.inl α,rfl,hi.symm⟩
    change (∑ w : CornerPath Q α (p i).color, x i * pathCoordinates Q (vertexId Q α) w.val)=x i
    rw [Finset.sum_eq_single z]
    · rw [vertex_coordinates,ite_eq_left rfl,_root_.mul_one]
    · intro w hw hwz
      rw [vertex_coordinates,ite_eq_right (fun he => hwz (Subtype.ext he.symm)),MulZeroClass.mul_zero]
    · simp
  · change (∑ w : CornerPath Q α (p i).color, x i * pathCoordinates Q (vertexId Q α) w.val)=x i
    rw [hx i hi]
    simp

omit [DecidableEq A] in
lemma unitTestVector_differential (E : BasedComplex Q (K := K) I) (α:V)
    (x : I → K) (hx : ∀ i, (E.placement i).color≠α → x i=0)
    (j : TestIndex Q E.placement α) :
    Matrix.vecMul (unitTestVector Q E.placement α x)
      (testMatrix Q E.placement E.placement α E.differential) j =
      ∑ i, x i * pathCoordinates Q (E.differential i j.1) j.2.val := by
  change (∑ z : TestIndex Q E.placement α, x z.1 * pathCoordinates Q (vertexId Q α) z.2.val *
    pathCoordinates Q (pathBasis Q z.2.val * E.differential z.1 j.1) j.2.val)=_
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hc : (E.placement i).color=α
  · simp only [_root_.mul_assoc,← Finset.mul_sum]
    rw [coordinates_mul_expansion Q (vertexId Q α) (E.differential i j.1)
      (vertexId_mul_self Q α) (by rw [hc]; exact vertexId_mul_self Q α)]
    have heq := E.entries.1 i j.1
    rw [hc] at heq
    rw [heq]
  · simp only [hx i hc,MulZeroClass.zero_mul,Finset.sum_const_zero]

namespace BasedComplex

noncomputable def socleTestCycles (E : BasedComplex Q (K := K) I) (α:V) (c:ℤ) :=
  ScalarCycles.supportedKernel (testMatrix Q E.placement E.placement α E.differential)
    (fun i => (E.placement i.1).cochain=c ∧ Path.length i.2.val=0)

lemma sumUnitTest_socle (E : BasedComplex Q (K := K) I) (α:V) (c:ℤ)
    {x : TestIndex Q E.placement α → K} (hx : x ∈ socleTestCycles Q E α c) :
    sumUnitTest Q E.placement α x ∈ coefficientSocle Q E α c := by
  have hs := sumUnitTest_support Q E.placement α c x hx.1
  constructor
  · exact hs
  · intro j a ha
    by_cases ht : Q.target a=(E.placement j).color
    · let z : TestIndex Q E.placement α := ⟨j,Sum.inr (Sum.inl a),ha,ht⟩
      have hh := unitTestVector_differential Q E α (sumUnitTest Q E.placement α x)
        (fun i h => hs i (Or.inl h)) z
      rw [unitTestVector_sum Q E.placement α c x hx.1,hx.2] at hh
      exact hh.symm
    · apply Finset.sum_eq_zero
      intro i hi
      have hz : (E.differential i j).arrow a=0 := by
        by_contra hn
        exact ht (coordinates_corner Q (p := Sum.inr (Sum.inl a)) (E.entries.1 i j) (E.entries.2 i j) hn).2
      rw [hz,MulZeroClass.mul_zero]

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_PureSupportedCycles
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.corner_val _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_reverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag
variable {V A K I J : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

omit [Fintype I] in
lemma testMatrix_identity (p : I → GeneratorPlacement V) (α : V) :
    testMatrix Q p p α (projectiveIdentity Q p (K := K)) = 1 := by
  apply Matrix.ext
  intro u v
  change pathCoordinates Q (pathBasis Q u.2.val *
    (if u.1 = v.1 then vertexId Q (p u.1).color else 0)) v.2.val = _
  by_cases hi : u.1 = v.1
  · rcases u with ⟨i,u⟩
    rcases v with ⟨j,v⟩
    dsimp only at hi
    subst j
    simp only [ite_true, if_true,cornerPath_right,pathBasis_coordinates]
    by_cases hp : u=v
    · subst v; simp
    · have hv : u.val ≠ v.val := fun h => hp (Subtype.ext h)
      simp [hp,hv]
  · rw [ite_eq_right hi,MulZeroClass.mul_zero,coordinates_zero]
    exact (Matrix.one_apply_ne (fun h => hi (congrArg Sigma.fst h))).symm

end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_NegativeAmplitudeCoreIndex
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.corner_val _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_reverse _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.selfCornerEquiv_false _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.selfCornerEquiv_true
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

variable {V A K I : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I]

abbrev NegativeAmplitudeCoreIndex (E : BasedComplex Q (K := K) I) (α : V) :=
  {u : TestIndex Q E.placement α // Path.length u.2.val ≠ 2} ⊕
    {i : I // (E.placement i).color ≠ α}

noncomputable instance negativeAmplitudeCoreFintype (E : BasedComplex Q (K := K) I) (α : V) :
    Fintype (NegativeAmplitudeCoreIndex Q E α) := by
  classical
  unfold NegativeAmplitudeCoreIndex
  infer_instance

noncomputable instance negativeAmplitudeCoreDecidable (E : BasedComplex Q (K := K) I) (α : V) :
    DecidableEq (NegativeAmplitudeCoreIndex Q E α) := fun a b => instDecidableEqSum a b

def tokenTest (E : BasedComplex Q (K := K) I) (α : V) (i : ActedIndex Q E α) :
    TestIndex Q E.placement α :=
  ⟨i.val, ⟨.inr (.inr α), rfl, i.property.symm⟩⟩

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

noncomputable def targetLow (_E:BasedComplex Q (K:=K) I) (F:BasedComplex Q (K:=K) J) (d:ℤ) :
    Matrix I J (Q.Zigzag K)→ₗ[K] Matrix I (lowerLevelSet Q F d) (Q.Zigzag K) where
  toFun M i j:=M i j
  map_add' _ _:=rfl
  map_smul' _ _:=rfl

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_PlacedProjective
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

noncomputable def placedProjective (p:GeneratorPlacement V) : BasedComplex Q (K:=K) PUnit.{u+1} where
  placement _:=p
  differential:=0
  entries:=projectiveEntries_zero Q
  degree:=mapDegree_zero Q 1 0
  square_zero:=Matrix.zero_mul _

noncomputable def placedGeneratorMap (E:BasedComplex Q (K:=K) I) (i:I)
    (hi:∀ j,E.differential i j=0) : Map Q (placedProjective Q (E.placement i)) E where
  matrix _ j:=projectiveIdentity Q (K:=K) E.placement i j
  entries:=⟨fun _ j=>(projectiveEntries_identity Q).1 i j,
    fun _ j=>(projectiveEntries_identity Q).2 i j⟩
  degree:=fun _ j=>mapDegree_identity Q i j
  commute:=by
    apply Matrix.ext
    intro z j
    change (∑ _k:PUnit.{u+1}, (0:Q.Zigzag K) * projectiveIdentity Q (K:=K) E.placement i j)=
      (projectiveIdentity Q (K:=K) E.placement*E.differential) i j
    simp only [zero_mul,Finset.sum_const_zero]
    exact ((congrArg (fun M:Matrix I I (Q.Zigzag K)=>M i j)
      (projectiveIdentity_mul Q E.entries)).trans (hi j)).symm

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_ScalarSupported
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.instAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K I J : Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V]
  [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

omit [DecidableEq I] in
lemma scalarDifferential_square (E:BasedComplex Q (K:=K) I) (α:V) :
    E.differential.map (vertexHom Q α) * E.differential.map (vertexHom Q α)=0 := by
  rw [← Matrix.map_mul,E.square_zero]
  apply Matrix.ext
  intro i j
  change (vertexHom Q α) (0:Q.Zigzag K)=0
  exact map_zero _

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_TestComplexVertexDifferential
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.corner_val _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_reverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K I : Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I]

lemma testComplex_vertex_differential (E:BasedComplex Q (K:=K) I) (α:V) :
    (E.testComplex Q α).differential.map (vertexHom Q α)=
      testMatrix Q E.placement E.placement α E.differential := by
  apply Matrix.ext
  intro i j
  change ((testMatrix Q E.placement E.placement α E.differential i j) • vertexId Q α).vertex α = _
  simp

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_ScalarSupportedCochainShift
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K I : Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I]

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma scalarSupported_cochainShift (E F:BasedComplex Q (K:=K) I)
    (hl:∀ i,(F.placement i).level=(E.placement i).level)
    (hc:∀ i,(F.placement i).cochain=(E.placement i).cochain-1)
    (l c:ℤ) (x:I→K) : ScalarSupported Q F l c x ↔ ScalarSupported Q E l (c+1) x := by
  constructor <;> intro h i hi <;> apply h i <;> intro hh <;> apply hi
  · rw [hl,hc] at hh
    exact ⟨hh.1,by omega⟩
  · rw [hl,hc]
    exact ⟨hh.1,by omega⟩

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma scalarExact_cochainShift_iff (E F:BasedComplex Q (K:=K) I) (α β:V)
    (hl:∀ i,(F.placement i).level=(E.placement i).level)
    (hc:∀ i,(F.placement i).cochain=(E.placement i).cochain-1)
    (hd:F.differential.map (vertexHom Q β) = -E.differential.map (vertexHom Q α))
    (l c:ℤ) : ScalarExactAt Q F β l c ↔ ScalarExactAt Q E α l (c+1) := by
  constructor
  · intro h x hx hd0
    have hxs:ScalarSupported Q F l c x :=
      (scalarSupported_cochainShift Q E F hl hc l c x).mpr hx
    have hdx:Matrix.vecMul x (F.differential.map (vertexHom Q β))=0 := by
      rw [hd,Matrix.vecMul_neg,hd0,neg_zero]
    obtain ⟨y,hy,hyb⟩:=h x hxs hdx
    refine ⟨-y,?_,?_⟩
    · have hh:ScalarSupported Q E (l-1) (c-1+1) y :=
        (scalarSupported_cochainShift Q E F hl hc (l-1) (c-1) y).mp hy
      intro i hi
      change -y i=0
      rw [hh i,neg_zero]
      simpa only [sub_add_cancel,add_sub_cancel_right] using hi
    · rw [hd,Matrix.vecMul_neg] at hyb
      simpa only [Matrix.neg_vecMul] using hyb
  · intro h x hx hd0
    have hxs:ScalarSupported Q E l (c+1) x :=
      (scalarSupported_cochainShift Q E F hl hc l c x).mp hx
    have hdx:Matrix.vecMul x (E.differential.map (vertexHom Q α))=0 := by
      rw [hd,Matrix.vecMul_neg] at hd0
      exact neg_eq_zero.mp hd0
    obtain ⟨y,hy,hyb⟩:=h x hxs hdx
    refine ⟨-y,?_,?_⟩
    · apply (scalarSupported_cochainShift Q E F hl hc (l-1) (c-1) (-y)).mpr
      intro i hi
      change -y i=0
      rw [hy i,neg_zero]
      simpa only [sub_add_cancel,add_sub_cancel_right] using hi
    · rw [hd,Matrix.vecMul_neg,Matrix.neg_vecMul,neg_neg,hyb]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_GeneratorTokenTest
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.corner_val _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_reverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K I : Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I]

def generatorTokenTest (E:BasedComplex Q (K:=K) I) (i:I) :
    TestIndex Q E.placement (E.placement i).color :=
  ⟨i,Sum.inr (Sum.inr (E.placement i).color),rfl,rfl⟩

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
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_TwistNewTestIndex
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.corner_val _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_reverse _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.selfCornerEquiv_false _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.selfCornerEquiv_true
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K I : Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I]

def twistNewTestIndex (E:BasedComplex Q (K:=K) I) (α β:V)
    (p:Zigzag.CornerPath Q β α) (u:TestIndex Q E.placement α) :
    TestIndex Q (E.positiveTwist Q α).placement β := ⟨Sum.inl u,p⟩

def twistOldTestIndex (E:BasedComplex Q (K:=K) I) (α β:V)
    (u:TestIndex Q E.placement β) :
    TestIndex Q (E.positiveTwist Q α).placement β := ⟨Sum.inr u.1,u.2⟩

lemma twistTest_new_differential
    (E:BasedComplex Q (K:=K) I) (α β:V)
    (y:TestIndex Q (E.positiveTwist Q α).placement β→K)
    (p:Zigzag.CornerPath Q β α) (v:TestIndex Q E.placement α) :
    Matrix.vecMul y (testMatrix Q (E.positiveTwist Q α).placement
      (E.positiveTwist Q α).placement β (E.positiveTwist Q α).differential)
      (twistNewTestIndex Q E α β p v) =
    -Matrix.vecMul (fun u=>y (twistNewTestIndex Q E α β p u))
      (testMatrix Q E.placement E.placement α E.differential) v := by
  classical
  change (∑ z:TestIndex Q (E.positiveTwist Q α).placement β,
    y z * pathCoordinates Q (pathBasis Q z.2.val *
      (E.positiveTwist Q α).differential z.1 (Sum.inl v)) p.val)=_
  rw [Fintype.sum_sigma,Fintype.sum_sum_type]
  dsimp only
  have ho:(∑ i:I,∑ z:Zigzag.CornerPath Q β (E.placement i).color,
      y ⟨Sum.inr i,z⟩ * pathCoordinates Q
      (pathBasis Q z.val * (E.positiveTwist Q α).differential (Sum.inr i) (Sum.inl v)) p.val)=0 := by
    apply Finset.sum_eq_zero
    intro i hi
    apply Finset.sum_eq_zero
    intro z hz
    change _ * pathCoordinates Q (_ * 0) _=0
    rw [MulZeroClass.mul_zero,coordinates_zero,MulZeroClass.mul_zero]
  have he := congrArg (fun a:K =>
    (∑ u:TestIndex Q E.placement α,∑ z:Zigzag.CornerPath Q β α,
      y ⟨Sum.inl u,z⟩ * pathCoordinates Q (pathBasis Q z.val *
      (E.positiveTwist Q α).differential (Sum.inl u) (Sum.inl v)) p.val) + a) ho
  apply he.trans
  rw [add_zero]
  rw [show -Matrix.vecMul (fun u=>y (twistNewTestIndex Q E α β p u))
      (testMatrix Q E.placement E.placement α E.differential) v =
      ∑ u, -(y (twistNewTestIndex Q E α β p u) *
      testMatrix Q E.placement E.placement α E.differential u v) by
        exact (Finset.sum_neg_distrib _).symm]
  apply Finset.sum_congr rfl
  intro u hu
  change (∑ z:Zigzag.CornerPath Q β α,y ⟨Sum.inl u,z⟩ *
    pathCoordinates Q (pathBasis Q z.val *
      (-(testMatrix Q E.placement E.placement α E.differential u v • vertexId Q (K:=K) α))) p.val)=_
  simp only [_root_.mul_neg,mul_smul,cornerPath_right,map_neg,map_smul,
    pathBasis_coordinates,Pi.neg_apply,Pi.smul_apply,smul_eq_mul]
  rw [Finset.sum_eq_single p]
  · simp [twistNewTestIndex]
  · intro z hz hzp
    rw [ite_eq_right (fun equality=>hzp (Subtype.ext equality))]
    simp
  · simp

lemma twistTest_old_differential
    (E:BasedComplex Q (K:=K) I) (α β:V)
    (y:TestIndex Q (E.positiveTwist Q α).placement β→K)
    (hy:∀ p:Zigzag.CornerPath Q β α,∀ u:TestIndex Q E.placement α,
      y (twistNewTestIndex Q E α β p u)=0)
    (v:TestIndex Q E.placement β) :
    Matrix.vecMul y (testMatrix Q (E.positiveTwist Q α).placement
      (E.positiveTwist Q α).placement β (E.positiveTwist Q α).differential)
      (twistOldTestIndex Q E α β v) =
    Matrix.vecMul (fun u=>y (twistOldTestIndex Q E α β u))
      (testMatrix Q E.placement E.placement β E.differential) v := by
  classical
  change (∑ z:TestIndex Q (E.positiveTwist Q α).placement β,
    y z * pathCoordinates Q (pathBasis Q z.2.val *
      (E.positiveTwist Q α).differential z.1 (Sum.inr v.1)) v.2.val)=_
  rw [Fintype.sum_sigma,Fintype.sum_sum_type]
  dsimp only
  have hn:(∑ u:TestIndex Q E.placement α,∑ z:Zigzag.CornerPath Q β α,
      y ⟨Sum.inl u,z⟩ * pathCoordinates Q
      (pathBasis Q z.val * (E.positiveTwist Q α).differential (Sum.inl u) (Sum.inr v.1)) v.2.val)=0 := by
    apply Finset.sum_eq_zero
    intro u hu
    apply Finset.sum_eq_zero
    intro z hz
    have hh:=hy z u
    change y ⟨Sum.inl u,z⟩=0 at hh
    rw [hh,MulZeroClass.zero_mul]
  have he := congrArg (fun a:K => a+
    (∑ i:I,∑ z:Zigzag.CornerPath Q β (E.placement i).color,
      y ⟨Sum.inr i,z⟩ * pathCoordinates Q (pathBasis Q z.val *
      (E.positiveTwist Q α).differential (Sum.inr i) (Sum.inr v.1)) v.2.val)) hn
  apply he.trans
  rw [zero_add]
  change _ = ∑ z:TestIndex Q E.placement β,
    y (twistOldTestIndex Q E α β z) *
    pathCoordinates Q (pathBasis Q z.2.val * E.differential z.1 v.1) v.2.val
  rw [Fintype.sum_sigma]
  rfl

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_ScalarSupportedTokenShift
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K I : Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I]

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma scalarSupported_tokenShift (E:BasedComplex Q (K:=K) I) (l c:ℤ) (x:I→K) :
    ScalarSupported Q (E.tokenShift Q) l c x ↔ ScalarSupported Q E (l-1) (c+1) x := by
  constructor <;> intro h i hi <;> apply h i <;> intro hh <;> apply hi
  · change (E.placement i).cochain-1+((E.placement i).internal+2)=l ∧
      (E.placement i).cochain-1=c at hh
    dsimp only [GeneratorPlacement.level]
    omega
  · change (E.placement i).cochain-1+((E.placement i).internal+2)=l ∧
      (E.placement i).cochain-1=c
    dsimp only [GeneratorPlacement.level] at hh
    omega

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma scalarDifferential_tokenShift (E:BasedComplex Q (K:=K) I) (α:V) :
    (E.tokenShift Q).differential.map (vertexHom Q α)=
      -E.differential.map (vertexHom Q α) := by
  apply Matrix.ext
  intro i j
  exact map_neg (vertexHom Q α) _

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
theorem scalarExact_tokenShift_iff (E:BasedComplex Q (K:=K) I) (α:V) (l c:ℤ) :
    ScalarExactAt Q (E.tokenShift Q) α l c ↔ ScalarExactAt Q E α (l-1) (c+1) := by
  constructor
  · intro h x hx hd
    have hxs:ScalarSupported Q (E.tokenShift Q) l c x :=
      (scalarSupported_tokenShift Q E l c x).mpr hx
    have hdx:Matrix.vecMul x ((E.tokenShift Q).differential.map (vertexHom Q α))=0 := by
      rw [scalarDifferential_tokenShift,Matrix.vecMul_neg,hd,neg_zero]
    obtain ⟨y,hy,hyb⟩:=h x hxs hdx
    refine ⟨-y,?_,?_⟩
    · have hh:ScalarSupported Q E (l-1-1) (c-1+1) y :=
        (scalarSupported_tokenShift Q E (l-1) (c-1) y).mp hy
      intro i hi
      change -y i=0
      rw [hh i,neg_zero]
      simpa only [sub_add_cancel,add_sub_cancel_right] using hi
    · rw [scalarDifferential_tokenShift,Matrix.vecMul_neg] at hyb
      simpa only [Matrix.neg_vecMul] using hyb
  · intro h x hx hd
    have hxs:ScalarSupported Q E (l-1) (c+1) x :=
      (scalarSupported_tokenShift Q E l c x).mp hx
    have hdx:Matrix.vecMul x (E.differential.map (vertexHom Q α))=0 := by
      rw [scalarDifferential_tokenShift,Matrix.vecMul_neg] at hd
      exact neg_eq_zero.mp hd
    obtain ⟨y,hy,hyb⟩:=h x hxs hdx
    refine ⟨-y,?_,?_⟩
    · apply (scalarSupported_tokenShift Q E (l-1) (c-1) (-y)).mpr
      intro i hi
      change -y i=0
      rw [hy i,neg_zero]
      simpa only [sub_add_cancel,add_sub_cancel_right] using hi
    · rw [scalarDifferential_tokenShift,Matrix.vecMul_neg,Matrix.neg_vecMul,neg_neg,hyb]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_TestUpperBound
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.corner_val _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_reverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K I J : Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

def TestUpperBound (E:BasedComplex Q (K:=K) I) (U:Set V) (t:ℤ) : Prop :=
  ∀ α∈U,∀ l:ℤ,t<l→∀ c:ℤ,ScalarExactAt Q (E.testComplex Q α) α l c

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
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_OutsideCap
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf
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

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma scalarExact_of_absent_degree (E:BasedComplex Q (K:=K) I) (α:V) (l c:ℤ)
    (h:∀ i,(E.placement i).level≠l) : ScalarExactAt Q E α l c := by
  intro x hx _
  have hz:x=0 := by funext i; exact hx i (fun hh=>h i hh.1)
  refine ⟨0,?_,?_⟩
  · intro index _; rfl
  · rw [Matrix.zero_vecMul,hz]

omit [DecidableEq I] in
lemma testUpperBound_of_generator_cap (E:BasedComplex Q (K:=K) I) (d:ℤ)
    (h:∀ i,(E.placement i).level≤d) (U:Set V) : TestUpperBound Q E U (d+2) := by
  intro α _ l hl c
  apply scalarExact_of_absent_degree Q _ α l c
  intro j he
  have hp:Path.length j.2.val≤2 := by rcases j.2.val with v|a|v <;> norm_num [Path.length]
  have hi:=h j.1
  dsimp only [testComplex,testPlacement,GeneratorPlacement.level] at he hi
  omega

def ClassOutsideCap (x:FiniteHomotopyClass Q (K:=K)) (U:Set V) (d:ℤ) : Prop :=
  ∀ i,((minimalClassModel Q x).complex.placement i).color∉U→
    ((minimalClassModel Q x).complex.placement i).level≤d

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

noncomputable def inverseWordAction : List V→FiniteHomotopyClass Q (K:=K)→FiniteHomotopyClass Q (K:=K)
  | [],x=>x
  | α::w,x=>inverseWordAction w (classNegativeTwist Q α x)

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
noncomputable def positiveWord : List V → FiniteModel.{u} Q (K:=K) → FiniteModel.{u} Q (K:=K)
  | [],E=>E
  | α::w,E=>ofComplex Q ((positiveWord w E).complex.positiveTwist Q α)

noncomputable def positiveWordMap : (w:List V) → {E F:FiniteModel.{u} Q (K:=K)} →
    Map Q E.complex F.complex → Map Q (positiveWord Q w E).complex (positiveWord Q w F).complex
  | [],_,_,f=>f
  | α::w,_,_,f=>(positiveWordMap w f).positiveTwist Q α

end FiniteModel

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

noncomputable def wordInverseModel (w:List V) (x:FiniteHomotopyClass Q (K:=K)) :=
  minimalClassModel Q (inverseWordAction Q w x)

noncomputable def canonicalLowTarget (w:List V) (x:FiniteHomotopyClass Q (K:=K)) :=
  FiniteModel.positiveWord Q w (wordInverseModel Q w x)

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

def ClassColorSupport (U:Set V) (x:FiniteHomotopyClass Q (K:=K)) : Prop :=
  ∀ i,((minimalClassModel Q x).complex.placement i).color∈U

def ClassOutsideFloor (U:Set V) (q:ℤ) (x:FiniteHomotopyClass Q (K:=K)) : Prop :=
  ∀ i,((minimalClassModel Q x).complex.placement i).color∉U→
    q≤((minimalClassModel Q x).complex.placement i).level

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_InverseMatrix
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf
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
lemma cone_homotopy_degree11 (f:Map Q E F)
    (H:Matrix (I⊕J) (I⊕J) (Q.Zigzag K))
    (hH:MapDegree Q (f.cone Q).placement (f.cone Q).placement (-1) 0 H) :
    MapDegree Q E.placement E.placement (-1) 0 H.toBlocks₁₁ := by
  intro i j
  refine ⟨?_,(hH (.inl i) (.inl j)).2⟩
  intro h
  apply (hH (.inl i) (.inl j)).1
  change (E.placement j).cochain-1≠(E.placement i).cochain-1+(-1)
  omega

omit [Fintype V] [DecidableEq A] [DecidableEq I] [DecidableEq J] in
lemma cone_homotopy_degree22 (f:Map Q E F)
    (H:Matrix (I⊕J) (I⊕J) (Q.Zigzag K))
    (hH:MapDegree Q (f.cone Q).placement (f.cone Q).placement (-1) 0 H) :
    MapDegree Q F.placement F.placement (-1) 0 H.toBlocks₂₂ :=
  fun i j=>hH (.inr i) (.inr j)

omit [Fintype V] [DecidableEq A] [DecidableEq I] [DecidableEq J] in
lemma cone_homotopy_degree21 (f:Map Q E F)
    (H:Matrix (I⊕J) (I⊕J) (Q.Zigzag K))
    (hH:MapDegree Q (f.cone Q).placement (f.cone Q).placement (-1) 0 H) :
    MapDegree Q F.placement E.placement 0 0 H.toBlocks₂₁ := by
  intro i j
  refine ⟨?_,(hH (.inr i) (.inl j)).2⟩
  intro h
  apply (hH (.inr i) (.inl j)).1
  change (E.placement j).cochain-1≠(F.placement i).cochain+(-1)
  omega

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

omit [Fintype V] [DecidableEq A] in
lemma cone_identity_blocks (f:Map Q E F) :
    projectiveIdentity Q (K:=K) (f.cone Q).placement=
      Matrix.fromBlocks (projectiveIdentity Q E.placement) 0 0
        (projectiveIdentity Q F.placement) := by
  apply Matrix.ext
  intro i j
  rcases i with i|i <;> rcases j with j|j <;> simp [projectiveIdentity,Matrix.diagonal,Map.cone,Map.conePlacement]

omit [Fintype V] [DecidableEq A] [DecidableEq I] [DecidableEq J] in
lemma cone_homotopy_source_block (f:Map Q E F)
    (H:Matrix (I⊕J) (I⊕J) (Q.Zigzag K)) :
    ((f.cone Q).differential*H+H*(f.cone Q).differential).toBlocks₁₁=
      -(E.differential*H.toBlocks₁₁+H.toBlocks₁₁*E.differential)+f.matrix*H.toBlocks₂₁ := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks H]
  change ((Matrix.fromBlocks (-E.differential) f.matrix 0 F.differential)*
      Matrix.fromBlocks H.toBlocks₁₁ H.toBlocks₁₂ H.toBlocks₂₁ H.toBlocks₂₂+
    Matrix.fromBlocks H.toBlocks₁₁ H.toBlocks₁₂ H.toBlocks₂₁ H.toBlocks₂₂*
      Matrix.fromBlocks (-E.differential) f.matrix 0 F.differential).toBlocks₁₁=_
  rw [Matrix.fromBlocks_multiply,Matrix.fromBlocks_multiply]
  change (-E.differential*H.toBlocks₁₁+f.matrix*H.toBlocks₂₁)+
    (H.toBlocks₁₁*(-E.differential)+H.toBlocks₁₂*(0 : Matrix J I (Q.Zigzag K)))=_
  simp only [Matrix.mul_zero,add_zero,Matrix.neg_mul,Matrix.mul_neg]
  abel

omit [Fintype V] [DecidableEq A] [DecidableEq I] [DecidableEq J] in
lemma cone_homotopy_target_block (f:Map Q E F)
    (H:Matrix (I⊕J) (I⊕J) (Q.Zigzag K)) :
    ((f.cone Q).differential*H+H*(f.cone Q).differential).toBlocks₂₂=
      (F.differential*H.toBlocks₂₂+H.toBlocks₂₂*F.differential)+H.toBlocks₂₁*f.matrix := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks H]
  change ((Matrix.fromBlocks (-E.differential) f.matrix 0 F.differential)*
      Matrix.fromBlocks H.toBlocks₁₁ H.toBlocks₁₂ H.toBlocks₂₁ H.toBlocks₂₂+
    Matrix.fromBlocks H.toBlocks₁₁ H.toBlocks₁₂ H.toBlocks₂₁ H.toBlocks₂₂*
      Matrix.fromBlocks (-E.differential) f.matrix 0 F.differential).toBlocks₂₂=_
  rw [Matrix.fromBlocks_multiply,Matrix.fromBlocks_multiply]
  change ((0 : Matrix J I (Q.Zigzag K))*H.toBlocks₁₂+F.differential*H.toBlocks₂₂)+
    (H.toBlocks₂₁*f.matrix+H.toBlocks₂₂*F.differential)=_
  simp only [Matrix.zero_mul,zero_add]
  abel

noncomputable def Map.inverseMatrix (f:Map Q E F) (g:Matrix J I (Q.Zigzag K))
    (hg:ProjectiveEntries Q F.placement E.placement g)
    (hd:MapDegree Q F.placement E.placement 0 0 g)
    (hfg:f.matrix*g=projectiveIdentity Q E.placement)
    (hgf:g*f.matrix=projectiveIdentity Q F.placement) : Map Q F E where
  matrix:=g
  entries:=hg
  degree:=hd
  commute:=by
    calc
      F.differential*g=(projectiveIdentity Q F.placement*F.differential)*g := by
        exact congrArg (fun m=>m*g) (projectiveIdentity_mul Q F.entries).symm
      _=((g*f.matrix)*F.differential)*g := by rw [hgf]
      _=(g*(f.matrix*F.differential))*g := by simp only [Matrix.mul_assoc]
      _=(g*(E.differential*f.matrix))*g := by rw [f.commute]
      _=(g*E.differential)*(f.matrix*g) := by simp only [Matrix.mul_assoc]
      _=(g*E.differential)*projectiveIdentity Q E.placement :=
        congrArg (fun m=>(g*E.differential)*m) hfg
      _=g*E.differential := mul_projectiveIdentity Q (projectiveEntries_mul Q hg E.entries)

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_HomotopyConeMap
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
open _root_.Matrix

attribute [local instance] Classical.propDecidable
attribute [local instance 2000] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I J L N:Type u} [Fintype I] [Fintype J] [Fintype L] [Fintype N]
  [DecidableEq I] [DecidableEq J] [DecidableEq L] [DecidableEq N]
  {E:BasedComplex Q (K:=K) I} {F:BasedComplex Q (K:=K) J}
  {G:BasedComplex Q (K:=K) L} {D:BasedComplex Q (K:=K) N}

omit [Fintype V] [DecidableEq A] [DecidableEq I] [DecidableEq J]
  [DecidableEq L] [DecidableEq N] in
lemma cone_block_entries (f:Map Q E F) (g:Map Q G D)
    (a:Matrix I L (Q.Zigzag K)) (b:Matrix I N (Q.Zigzag K))
    (c:Matrix J L (Q.Zigzag K)) (d:Matrix J N (Q.Zigzag K))
    (ha:ProjectiveEntries Q E.placement G.placement a)
    (hb:ProjectiveEntries Q E.placement D.placement b)
    (hc:ProjectiveEntries Q F.placement G.placement c)
    (hd:ProjectiveEntries Q F.placement D.placement d) :
    ProjectiveEntries Q (f.cone Q).placement (g.cone Q).placement
      (Matrix.fromBlocks a b c d) := by
  constructor <;> intro i j <;> rcases i with i|i <;> rcases j with j|j
  · exact ha.1 i j
  · exact hb.1 i j
  · exact hc.1 i j
  · exact hd.1 i j
  · exact ha.2 i j
  · exact hb.2 i j
  · exact hc.2 i j
  · exact hd.2 i j

omit [Fintype V] [DecidableEq A] [DecidableEq I] [DecidableEq J]
  [DecidableEq L] [DecidableEq N] in
lemma cone_block_degree (f:Map Q E F) (g:Map Q G D)
    (a:Matrix I L (Q.Zigzag K)) (b:Matrix I N (Q.Zigzag K))
    (c:Matrix J L (Q.Zigzag K)) (d:Matrix J N (Q.Zigzag K)) (n v:ℤ)
    (ha:MapDegree Q E.placement G.placement n v a)
    (hb:MapDegree Q E.placement D.placement (n-1) v b)
    (hc:MapDegree Q F.placement G.placement (n+1) v c)
    (hd:MapDegree Q F.placement D.placement n v d) :
    MapDegree Q (f.cone Q).placement (g.cone Q).placement n v
      (Matrix.fromBlocks a b c d) := by
  intro i j
  rcases i with i|i <;> rcases j with j|j
  · refine ⟨?_,(ha i j).2⟩
    intro h
    apply (ha i j).1
    change (G.placement j).cochain-1≠(E.placement i).cochain-1+n at h
    omega
  · refine ⟨?_,(hb i j).2⟩
    intro h
    apply (hb i j).1
    change (D.placement j).cochain≠(E.placement i).cochain-1+n at h
    omega
  · refine ⟨?_,(hc i j).2⟩
    intro h
    apply (hc i j).1
    change (G.placement j).cochain-1≠(F.placement i).cochain+n at h
    omega
  · exact hd i j

noncomputable def Map.homotopyConeMap (f:Map Q E F) (g:Map Q G D)
    (a:Map Q E G) (b:Map Q F D) (h:Matrix I N (Q.Zigzag K))
    (he:ProjectiveEntries Q E.placement D.placement h)
    (hd:MapDegree Q E.placement D.placement (-1) 0 h)
    (hc:f.matrix*b.matrix=a.matrix*g.matrix+(E.differential*h+h*D.differential)) :
    Map Q (f.cone Q) (g.cone Q) where
  matrix:=Matrix.fromBlocks a.matrix h 0 b.matrix
  entries:=cone_block_entries Q f g _ _ _ _ a.entries he (projectiveEntries_zero Q) b.entries
  degree:=cone_block_degree Q f g _ _ _ _ 0 0 a.degree hd (mapDegree_zero Q _ _) b.degree
  commute:=by
    change Matrix.fromBlocks (-E.differential) f.matrix 0 F.differential *
      Matrix.fromBlocks a.matrix h 0 b.matrix =
      Matrix.fromBlocks a.matrix h 0 b.matrix *
      Matrix.fromBlocks (-G.differential) g.matrix 0 D.differential
    rw [Matrix.fromBlocks_multiply,Matrix.fromBlocks_multiply]
    simp only [Matrix.neg_mul,Matrix.mul_neg,Matrix.mul_zero,Matrix.zero_mul,
      add_zero,zero_add,neg_zero,a.commute,b.commute]
    congr 1
    rw [hc]
    abel

omit [Fintype V] [DecidableEq A] in
lemma homotopy_coherence_closed (e:HomotopyEquivalence Q F G) :
    F.differential*(e.sourceHomotopy*e.forward.matrix-e.forward.matrix*e.targetHomotopy)+
      (e.sourceHomotopy*e.forward.matrix-e.forward.matrix*e.targetHomotopy)*G.differential=0 := by
  have hs:=congrArg (fun m=>m*e.forward.matrix) e.sourceEquation
  have ht:=congrArg (fun m=>e.forward.matrix*m) e.targetEquation
  have hid₁ : projectiveIdentity Q F.placement*e.forward.matrix=e.forward.matrix :=
    projectiveIdentity_mul Q e.forward.entries
  have hid₂ : e.forward.matrix*projectiveIdentity Q G.placement=e.forward.matrix :=
    mul_projectiveIdentity Q e.forward.entries
  erw [Matrix.add_mul,hid₁] at hs
  erw [Matrix.mul_add,hid₂] at ht
  have hh:(F.differential*e.sourceHomotopy+e.sourceHomotopy*F.differential)*e.forward.matrix=
      e.forward.matrix*(G.differential*e.targetHomotopy+e.targetHomotopy*G.differential) := by
    apply add_left_cancel (a:=e.forward.matrix)
    rw [← hs,← ht,Matrix.mul_assoc]
  have hc₁ : (e.sourceHomotopy*e.forward.matrix)*G.differential=
      (e.sourceHomotopy*F.differential)*e.forward.matrix := by
    rw [Matrix.mul_assoc,← e.forward.commute,← Matrix.mul_assoc]
  have hc₂ : F.differential*(e.forward.matrix*e.targetHomotopy)=
      (e.forward.matrix*G.differential)*e.targetHomotopy := by
    rw [← Matrix.mul_assoc,e.forward.commute]
  have hr : F.differential*(e.sourceHomotopy*e.forward.matrix-e.forward.matrix*e.targetHomotopy)+
      (e.sourceHomotopy*e.forward.matrix-e.forward.matrix*e.targetHomotopy)*G.differential =
      (F.differential*e.sourceHomotopy+e.sourceHomotopy*F.differential)*e.forward.matrix-
      e.forward.matrix*(G.differential*e.targetHomotopy+e.targetHomotopy*G.differential) := by
    simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.add_mul,Matrix.mul_add]
    rw [hc₁,hc₂]
    simp only [← Matrix.mul_assoc]
    abel
  rw [hr,hh,sub_self]

omit [Fintype V] [DecidableEq A] in
lemma cone_target_replace_backward_square (f:Map Q E F) (e:HomotopyEquivalence Q F G) :
    (f.matrix*e.forward.matrix)*e.backward.matrix =
      projectiveIdentity Q E.placement*f.matrix+
        (E.differential*(f.matrix*e.sourceHomotopy)+(f.matrix*e.sourceHomotopy)*F.differential) := by
  have hid : projectiveIdentity Q E.placement*f.matrix=f.matrix :=
    projectiveIdentity_mul Q f.entries
  have hid' : f.matrix*projectiveIdentity Q F.placement=f.matrix :=
    mul_projectiveIdentity Q f.entries
  erw [hid,Matrix.mul_assoc,e.sourceEquation,Matrix.mul_add,hid',Matrix.mul_add]
  simp only [← Matrix.mul_assoc]
  rw [f.commute]

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma cone_target_replace_correction (f:Map Q E F) (e:HomotopyEquivalence Q F G)
    (k:Matrix J L (Q.Zigzag K))
    (hk:k=e.sourceHomotopy*e.forward.matrix-e.forward.matrix*e.targetHomotopy)
    (hkc:F.differential*k+k*G.differential=0) :
    -(E.differential*(f.matrix*e.sourceHomotopy*k))+
      (f.matrix*e.forward.matrix)*(e.targetHomotopy+e.backward.matrix*k)+
      (f.matrix*e.sourceHomotopy*k)*G.differential =
      (f.matrix*e.sourceHomotopy)*e.forward.matrix := by
  have hb : -(E.differential*(f.matrix*e.sourceHomotopy*k))+
      (f.matrix*e.sourceHomotopy*k)*G.differential =
      f.matrix*k-(f.matrix*e.forward.matrix)*(e.backward.matrix*k) := by
    have hkc' : k*G.differential=-(F.differential*k) :=
      eq_neg_of_add_eq_zero_right hkc
    have hs : F.differential*e.sourceHomotopy+e.sourceHomotopy*F.differential =
        e.forward.matrix*e.backward.matrix-projectiveIdentity Q F.placement := by
      rw [e.sourceEquation]
      abel
    calc
      _ = -(f.matrix*((F.differential*e.sourceHomotopy+e.sourceHomotopy*F.differential)*k)) := by
        simp only [Matrix.mul_add,Matrix.add_mul,Matrix.mul_assoc]
        rw [hkc']
        simp only [Matrix.mul_neg,← Matrix.mul_assoc,neg_add_rev]
        rw [f.commute]
        abel
      _ = f.matrix*k-(f.matrix*e.forward.matrix)*(e.backward.matrix*k) := by
        rw [hs,Matrix.sub_mul,Matrix.mul_sub]
        have hid : projectiveIdentity Q F.placement*k=k := by
          rw [hk]
          apply projectiveIdentity_mul Q
          simpa only [sub_eq_add_neg] using projectiveEntries_add Q
            (projectiveEntries_mul Q e.sourceEntries e.forward.entries)
            (projectiveEntries_neg Q (projectiveEntries_mul Q e.forward.entries e.targetEntries))
        erw [hid]
        simp only [Matrix.mul_assoc]
        abel
  have hsum : (f.matrix*e.forward.matrix)*(e.targetHomotopy+e.backward.matrix*k) =
      (f.matrix*e.forward.matrix)*e.targetHomotopy+
        (f.matrix*e.forward.matrix)*(e.backward.matrix*k) := Matrix.mul_add _ _ _
  rw [hsum]
  calc
    _ = (-(E.differential*(f.matrix*e.sourceHomotopy*k))+
          (f.matrix*e.sourceHomotopy*k)*G.differential)+
        ((f.matrix*e.forward.matrix)*e.targetHomotopy+
          (f.matrix*e.forward.matrix)*(e.backward.matrix*k)) := by abel
    _ = (f.matrix*e.sourceHomotopy)*e.forward.matrix := by
      rw [hb,hk,Matrix.mul_sub]
      simp only [Matrix.mul_assoc]
      abel

noncomputable def HomotopyEquivalence.coneTarget (e:HomotopyEquivalence Q F G) (f:Map Q E F) :
    HomotopyEquivalence Q (f.cone Q) ((f.comp Q e.forward).cone Q) := by
  let g:=f.comp Q e.forward
  let k:=e.sourceHomotopy*e.forward.matrix-e.forward.matrix*e.targetHomotopy
  have ke:ProjectiveEntries Q F.placement G.placement k := by
    simpa only [k,sub_eq_add_neg] using projectiveEntries_add Q
      (projectiveEntries_mul Q e.sourceEntries e.forward.entries)
      (projectiveEntries_neg Q (projectiveEntries_mul Q e.forward.entries e.targetEntries))
  have kd:MapDegree Q F.placement G.placement (-1) 0 k := by
    have h₁:=mapDegree_mul Q e.sourceDegree e.forward.degree
    have h₂:=mapDegree_mul Q e.forward.degree e.targetDegree
    simp only [add_zero,zero_add] at h₁ h₂
    simpa only [k,sub_eq_add_neg] using mapDegree_add Q h₁ (mapDegree_neg Q h₂)
  have kc:F.differential*k+k*G.differential=0 := homotopy_coherence_closed Q e
  let j:=e.targetHomotopy+e.backward.matrix*k
  have je:ProjectiveEntries Q G.placement G.placement j :=
    projectiveEntries_add Q e.targetEntries (projectiveEntries_mul Q e.backward.entries ke)
  have jd:MapDegree Q G.placement G.placement (-1) 0 j :=
    mapDegree_add Q e.targetDegree (mapDegree_mul Q e.backward.degree kd)
  have jc:G.differential*j+j*G.differential=
      G.differential*e.targetHomotopy+e.targetHomotopy*G.differential := by
    have hz:G.differential*(e.backward.matrix*k)+(e.backward.matrix*k)*G.differential=0 := by
      rw [← Matrix.mul_assoc,e.backward.commute]
      simpa only [Matrix.mul_add,Matrix.mul_assoc,Matrix.mul_zero] using
        congrArg (fun m=>e.backward.matrix*m) kc
    dsimp only [j]
    simp only [Matrix.mul_add,Matrix.add_mul]
    calc
      _ = (G.differential*e.targetHomotopy+e.targetHomotopy*G.differential)+
          (G.differential*(e.backward.matrix*k)+(e.backward.matrix*k)*G.differential) := by abel
      _ = _ := by rw [hz,add_zero]
  have pe:ProjectiveEntries Q E.placement F.placement (f.matrix*e.sourceHomotopy) :=
    projectiveEntries_mul Q f.entries e.sourceEntries
  have pd:MapDegree Q E.placement F.placement (-1) 0 (f.matrix*e.sourceHomotopy) :=
    mapDegree_mul Q f.degree e.sourceDegree
  let a:Map Q (f.cone Q) (g.cone Q):=f.coneMap Q g (Map.identity Q E) e.forward (by
    change projectiveIdentity Q E.placement*(f.matrix*e.forward.matrix)=_
    exact projectiveIdentity_mul Q (projectiveEntries_mul Q f.entries e.forward.entries))
  let b:Map Q (g.cone Q) (f.cone Q):=g.homotopyConeMap Q f (Map.identity Q E) e.backward
    (f.matrix*e.sourceHomotopy) pe pd (cone_target_replace_backward_square Q f e)
  let h:=Matrix.fromBlocks (0:Matrix I I (Q.Zigzag K)) (0:Matrix I J (Q.Zigzag K))
      (0:Matrix J I (Q.Zigzag K)) e.sourceHomotopy
  let t:=Matrix.fromBlocks (0:Matrix I I (Q.Zigzag K)) (f.matrix*e.sourceHomotopy*k)
      (0:Matrix L I (Q.Zigzag K)) j
  refine ⟨a,b,h,t,?_,?_,?_,?_,?_,?_⟩
  · exact cone_block_entries Q f f _ _ _ _ (projectiveEntries_zero Q)
      (projectiveEntries_zero Q) (projectiveEntries_zero Q) e.sourceEntries
  · exact cone_block_entries Q g g _ _ _ _ (projectiveEntries_zero Q)
      (projectiveEntries_mul Q pe ke) (projectiveEntries_zero Q) je
  · exact cone_block_degree Q f f _ _ _ _ (-1) 0 (mapDegree_zero Q _ _)
      (mapDegree_zero Q _ _) (mapDegree_zero Q _ _) e.sourceDegree
  · exact cone_block_degree Q g g _ _ _ _ (-1) 0 (mapDegree_zero Q _ _)
      (mapDegree_mul Q pd kd) (mapDegree_zero Q _ _) jd
  · change Matrix.fromBlocks (projectiveIdentity Q E.placement) 0 0 e.forward.matrix *
      Matrix.fromBlocks (projectiveIdentity Q E.placement) (f.matrix*e.sourceHomotopy) 0 e.backward.matrix =
      projectiveIdentity Q (f.cone Q).placement+
        (Matrix.fromBlocks (-E.differential) f.matrix 0 F.differential*h+
          h*Matrix.fromBlocks (-E.differential) f.matrix 0 F.differential)
    dsimp only [h]
    rw [cone_identity_blocks,Matrix.fromBlocks_multiply,Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_multiply,Matrix.fromBlocks_add,Matrix.fromBlocks_add]
    simp only [Matrix.zero_mul,Matrix.mul_zero,add_zero,zero_add]
    have hi:projectiveIdentity Q E.placement*projectiveIdentity Q E.placement=
        projectiveIdentity Q E.placement :=projectiveIdentity_mul Q (projectiveEntries_identity Q (K:=K) (p:=E.placement))
    have hp:projectiveIdentity Q E.placement*(f.matrix*e.sourceHomotopy)=
        f.matrix*e.sourceHomotopy := projectiveIdentity_mul Q pe
    erw [hi,hp,e.sourceEquation]
  · change Matrix.fromBlocks (projectiveIdentity Q E.placement) (f.matrix*e.sourceHomotopy) 0 e.backward.matrix *
      Matrix.fromBlocks (projectiveIdentity Q E.placement) 0 0 e.forward.matrix =
      projectiveIdentity Q (g.cone Q).placement+
        (Matrix.fromBlocks (-E.differential) g.matrix 0 G.differential*t+
          t*Matrix.fromBlocks (-E.differential) g.matrix 0 G.differential)
    dsimp only [t]
    rw [cone_identity_blocks,Matrix.fromBlocks_multiply,Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_multiply,Matrix.fromBlocks_add,Matrix.fromBlocks_add]
    simp only [Matrix.zero_mul,Matrix.mul_zero,add_zero,zero_add,Matrix.neg_mul]
    have hi:projectiveIdentity Q E.placement*projectiveIdentity Q E.placement=
        projectiveIdentity Q E.placement :=projectiveIdentity_mul Q (projectiveEntries_identity Q (K:=K) (p:=E.placement))
    erw [hi,jc,← e.targetEquation]
    congr 1
    exact (cone_target_replace_correction Q f e k rfl kc).symm

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_Cone
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
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
  {G:BasedComplex Q (K:=K) L}

omit [Fintype V] [DecidableEq A] in
lemma cone_source_replace_backward_square (e:HomotopyEquivalence Q E G) (f:Map Q G F) :
    f.matrix*projectiveIdentity Q F.placement =
      e.backward.matrix*(e.forward.matrix*f.matrix)+
        (G.differential*(-(e.targetHomotopy*f.matrix))+
          (-(e.targetHomotopy*f.matrix))*F.differential) := by
  have hid : f.matrix*projectiveIdentity Q F.placement=f.matrix :=
    mul_projectiveIdentity Q f.entries
  have hid' : projectiveIdentity Q G.placement*f.matrix=f.matrix :=
    projectiveIdentity_mul Q f.entries
  rw [hid]
  simp only [Matrix.mul_neg,Matrix.neg_mul,← Matrix.mul_assoc]
  rw [e.targetEquation,Matrix.add_mul]
  erw [hid']
  simp only [Matrix.add_mul,Matrix.mul_assoc]
  rw [← f.commute]
  abel

omit [Fintype V] [DecidableEq A] [DecidableEq J] in
lemma cone_source_replace_correction (e:HomotopyEquivalence Q E G) (f:Map Q G F)
    (k:Matrix I L (Q.Zigzag K))
    (hk:k=e.sourceHomotopy*e.forward.matrix-e.forward.matrix*e.targetHomotopy)
    (hkc:E.differential*k+k*G.differential=0) :
    -(E.differential*(-(k*e.targetHomotopy*f.matrix)))+
      (-(e.sourceHomotopy-k*e.backward.matrix))*(e.forward.matrix*f.matrix)+
      (-(k*e.targetHomotopy*f.matrix))*F.differential =
      e.forward.matrix*(-(e.targetHomotopy*f.matrix)) := by
  have kc:E.differential*k=-(k*G.differential) := eq_neg_of_add_eq_zero_left hkc
  have hs:G.differential*e.targetHomotopy+e.targetHomotopy*G.differential =
      e.backward.matrix*e.forward.matrix-projectiveIdentity Q G.placement := by
    rw [e.targetEquation]
    abel
  have ke:ProjectiveEntries Q E.placement G.placement k := by
    rw [hk]
    simpa only [sub_eq_add_neg] using projectiveEntries_add Q
      (projectiveEntries_mul Q e.sourceEntries e.forward.entries)
      (projectiveEntries_neg Q (projectiveEntries_mul Q e.forward.entries e.targetEntries))
  have hid:k*projectiveIdentity Q G.placement=k := mul_projectiveIdentity Q ke
  have hb : -(E.differential*(-(k*e.targetHomotopy*f.matrix)))+
      (-(k*e.targetHomotopy*f.matrix))*F.differential =
      k*f.matrix-(k*e.backward.matrix)*(e.forward.matrix*f.matrix) := by
    calc
      _ = -(k*(G.differential*e.targetHomotopy+e.targetHomotopy*G.differential)*f.matrix) := by
        simp only [Matrix.mul_neg,Matrix.neg_mul,neg_neg,← Matrix.mul_assoc]
        rw [kc]
        simp only [Matrix.neg_mul,Matrix.mul_add,Matrix.add_mul,Matrix.mul_assoc]
        rw [← f.commute]
        abel
      _ = _ := by
        rw [hs,Matrix.mul_sub,Matrix.sub_mul]
        erw [hid]
        simp only [Matrix.mul_assoc]
        abel
  calc
    _ = (-(E.differential*(-(k*e.targetHomotopy*f.matrix)))+
          (-(k*e.targetHomotopy*f.matrix))*F.differential)+
          (-(e.sourceHomotopy-k*e.backward.matrix))*(e.forward.matrix*f.matrix) := by abel
    _ = _ := by
      rw [hb]
      simp only [Matrix.neg_mul,Matrix.sub_mul,Matrix.mul_assoc]
      calc
        _ = (k-e.sourceHomotopy*e.forward.matrix)*f.matrix := by
          simp only [Matrix.sub_mul,Matrix.mul_assoc]
          abel
        _ = _ := by
          rw [hk]
          simp only [Matrix.sub_mul,Matrix.mul_neg,Matrix.mul_assoc]
          abel

noncomputable def HomotopyEquivalence.coneSource (e:HomotopyEquivalence Q E G) (f:Map Q G F) :
    HomotopyEquivalence Q ((e.forward.comp Q f).cone Q) (f.cone Q) := by
  let g:=e.forward.comp Q f
  let k:=e.sourceHomotopy*e.forward.matrix-e.forward.matrix*e.targetHomotopy
  have ke:ProjectiveEntries Q E.placement G.placement k := by
    simpa only [k,sub_eq_add_neg] using projectiveEntries_add Q
      (projectiveEntries_mul Q e.sourceEntries e.forward.entries)
      (projectiveEntries_neg Q (projectiveEntries_mul Q e.forward.entries e.targetEntries))
  have kd:MapDegree Q E.placement G.placement (-1) 0 k := by
    have h₁:=mapDegree_mul Q e.sourceDegree e.forward.degree
    have h₂:=mapDegree_mul Q e.forward.degree e.targetDegree
    simp only [add_zero,zero_add] at h₁ h₂
    simpa only [k,sub_eq_add_neg] using mapDegree_add Q h₁ (mapDegree_neg Q h₂)
  have kc:E.differential*k+k*G.differential=0 := homotopy_coherence_closed Q e
  let h:=e.sourceHomotopy-k*e.backward.matrix
  have he:ProjectiveEntries Q E.placement E.placement h := by
    simpa only [h,sub_eq_add_neg] using projectiveEntries_add Q e.sourceEntries
      (projectiveEntries_neg Q (projectiveEntries_mul Q ke e.backward.entries))
  have hd:MapDegree Q E.placement E.placement (-1) 0 h := by
    simpa only [h,sub_eq_add_neg] using mapDegree_add Q e.sourceDegree
      (mapDegree_neg Q (mapDegree_mul Q kd e.backward.degree))
  have hc:E.differential*h+h*E.differential=
      E.differential*e.sourceHomotopy+e.sourceHomotopy*E.differential := by
    have hz:E.differential*(k*e.backward.matrix)+(k*e.backward.matrix)*E.differential=0 := by
      simp only [Matrix.mul_assoc]
      rw [← e.backward.commute]
      simpa only [Matrix.add_mul,Matrix.mul_assoc,Matrix.zero_mul] using
        congrArg (fun m=>m*e.backward.matrix) kc
    dsimp only [h]
    simp only [Matrix.mul_sub,Matrix.sub_mul]
    calc
      _ = (E.differential*e.sourceHomotopy+e.sourceHomotopy*E.differential)-
          (E.differential*(k*e.backward.matrix)+(k*e.backward.matrix)*E.differential) := by abel
      _ = _ := by rw [hz,sub_zero]
  have pe:ProjectiveEntries Q G.placement F.placement (-(e.targetHomotopy*f.matrix)) :=
    projectiveEntries_neg Q (projectiveEntries_mul Q e.targetEntries f.entries)
  have pd:MapDegree Q G.placement F.placement (-1) 0 (-(e.targetHomotopy*f.matrix)) :=
    mapDegree_neg Q (mapDegree_mul Q e.targetDegree f.degree)
  let a:Map Q (g.cone Q) (f.cone Q):=g.coneMap Q f e.forward (Map.identity Q F) (by
    change _=(e.forward.matrix*f.matrix)*projectiveIdentity Q F.placement
    exact (mul_projectiveIdentity Q (projectiveEntries_mul Q e.forward.entries f.entries)).symm)
  let b:Map Q (f.cone Q) (g.cone Q):=f.homotopyConeMap Q g e.backward (Map.identity Q F)
    (-(e.targetHomotopy*f.matrix)) pe pd (cone_source_replace_backward_square Q e f)
  let s:=Matrix.fromBlocks (-h) (-(k*e.targetHomotopy*f.matrix))
      (0:Matrix J I (Q.Zigzag K)) (0:Matrix J J (Q.Zigzag K))
  let t:=Matrix.fromBlocks (-e.targetHomotopy) (0:Matrix L J (Q.Zigzag K))
      (0:Matrix J L (Q.Zigzag K)) (0:Matrix J J (Q.Zigzag K))
  refine ⟨a,b,s,t,?_,?_,?_,?_,?_,?_⟩
  · exact cone_block_entries Q g g _ _ _ _ (projectiveEntries_neg Q he)
      (projectiveEntries_neg Q (projectiveEntries_mul Q (projectiveEntries_mul Q ke e.targetEntries) f.entries))
      (projectiveEntries_zero Q) (projectiveEntries_zero Q)
  · exact cone_block_entries Q f f _ _ _ _ (projectiveEntries_neg Q e.targetEntries)
      (projectiveEntries_zero Q) (projectiveEntries_zero Q) (projectiveEntries_zero Q)
  · exact cone_block_degree Q g g _ _ _ _ (-1) 0 (mapDegree_neg Q hd)
      (mapDegree_neg Q (mapDegree_mul Q (mapDegree_mul Q kd e.targetDegree) f.degree))
      (mapDegree_zero Q _ _) (mapDegree_zero Q _ _)
  · exact cone_block_degree Q f f _ _ _ _ (-1) 0 (mapDegree_neg Q e.targetDegree)
      (mapDegree_zero Q _ _) (mapDegree_zero Q _ _) (mapDegree_zero Q _ _)
  · change Matrix.fromBlocks e.forward.matrix 0 0 (projectiveIdentity Q F.placement) *
      Matrix.fromBlocks e.backward.matrix (-(e.targetHomotopy*f.matrix)) 0 (projectiveIdentity Q F.placement) =
      projectiveIdentity Q (g.cone Q).placement+
        (Matrix.fromBlocks (-E.differential) g.matrix 0 F.differential*s+
          s*Matrix.fromBlocks (-E.differential) g.matrix 0 F.differential)
    dsimp only [s]
    rw [cone_identity_blocks,Matrix.fromBlocks_multiply,Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_multiply,Matrix.fromBlocks_add,Matrix.fromBlocks_add]
    simp only [Matrix.zero_mul,Matrix.mul_zero,add_zero,zero_add,Matrix.neg_mul,Matrix.mul_neg,neg_neg]
    have hi:projectiveIdentity Q F.placement*projectiveIdentity Q F.placement=
        projectiveIdentity Q F.placement :=
      projectiveIdentity_mul Q (projectiveEntries_identity Q (K:=K) (p:=F.placement))
    erw [hi,hc,← e.sourceEquation]
    simp only [neg_zero,zero_add,add_zero]
    congr 1
    simpa only [h,g,Map.comp,Matrix.neg_mul,Matrix.mul_neg,neg_neg,add_assoc] using
      (cone_source_replace_correction Q e f k rfl kc).symm
  · change Matrix.fromBlocks e.backward.matrix (-(e.targetHomotopy*f.matrix)) 0 (projectiveIdentity Q F.placement) *
      Matrix.fromBlocks e.forward.matrix 0 0 (projectiveIdentity Q F.placement) =
      projectiveIdentity Q (f.cone Q).placement+
        (Matrix.fromBlocks (-G.differential) f.matrix 0 F.differential*t+
          t*Matrix.fromBlocks (-G.differential) f.matrix 0 F.differential)
    dsimp only [t]
    rw [cone_identity_blocks,Matrix.fromBlocks_multiply,Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_multiply,Matrix.fromBlocks_add,Matrix.fromBlocks_add]
    simp only [Matrix.zero_mul,Matrix.mul_zero,add_zero,zero_add,Matrix.neg_mul,Matrix.mul_neg,neg_neg]
    have hi:projectiveIdentity Q F.placement*projectiveIdentity Q F.placement=
        projectiveIdentity Q F.placement :=
      projectiveIdentity_mul Q (projectiveEntries_identity Q (K:=K) (p:=F.placement))
    have hp:(e.targetHomotopy*f.matrix)*projectiveIdentity Q F.placement=
        e.targetHomotopy*f.matrix :=
      mul_projectiveIdentity Q (projectiveEntries_mul Q e.targetEntries f.entries)
    erw [hi,hp,e.targetEquation]
    simp only [neg_zero,zero_add]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Quivers_SignDiagonal
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag
universe u
open _root_.Matrix

variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V]
  {I J:Type u} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

omit [Fintype I] in
lemma signDiagonal_degree (p:I→GeneratorPlacement V) (ε:I→Bool) :
    MapDegree Q p p 0 0 (signDiagonal Q (K:=K) p ε) := by
  intro i j
  by_cases h:i=j
  · subst j
    simp only [signDiagonal,Matrix.diagonal_apply_eq]
    split_ifs
    · simpa only [Matrix.neg_apply,projectiveIdentity,Matrix.diagonal_apply_eq] using
        (mapDegree_neg Q (mapDegree_identity Q (K:=K) (p:=p)) i i)
    · simpa only [projectiveIdentity,Matrix.diagonal_apply_eq] using
        (mapDegree_identity Q (K:=K) (p:=p) i i)
  · simp only [signDiagonal,Matrix.diagonal_apply_ne _ h]
    constructor
    · intro; trivial
    · exact homogeneous_zero Q _

namespace BasedComplex
noncomputable def signChainIsomorphism (E F:BasedComplex Q (K:=K) I) (ε:I→Bool)
    (hp:F.placement=E.placement)
    (hd:∀ i j,(if ε j then -E.differential i j else E.differential i j)=
      (if ε i then -F.differential i j else F.differential i j)) :
    ChainIsomorphism Q E F := by
  let s:=signDiagonal Q (K:=K) E.placement ε
  have he:ProjectiveEntries Q E.placement F.placement s := by
    rw [hp]; exact signDiagonal_entries Q _ _
  have hdeg:MapDegree Q E.placement F.placement 0 0 s := by
    rw [hp]; exact signDiagonal_degree Q _ _
  let f:Map Q E F:=⟨s,he,hdeg,by
    apply Matrix.ext
    intro i j
    have hF:ProjectiveEntries Q E.placement F.placement F.differential := by
      rw [← hp]; exact F.entries
    exact (mul_signDiagonal Q ε E.differential E.entries i j).trans
      ((hd i j).trans (signDiagonal_mul Q ε F.differential hF i j).symm)⟩
  have hg:ProjectiveEntries Q F.placement E.placement s := by
    rw [hp]; exact signDiagonal_entries Q _ _
  have hgd:MapDegree Q F.placement E.placement 0 0 s := by
    rw [hp]; exact signDiagonal_degree Q _ _
  have hs:f.matrix*s=projectiveIdentity Q E.placement := signDiagonal_square Q _ _
  have ht:s*f.matrix=projectiveIdentity Q F.placement := by
    rw [hp]; exact signDiagonal_square Q _ _
  refine ⟨f,⟨s,hg,hgd,?_⟩,hs,ht⟩
  calc
    F.differential*s=(projectiveIdentity Q F.placement*F.differential)*s := by
      exact congrArg (fun matrix=>matrix*s) (projectiveIdentity_mul Q F.entries).symm
    _=((s*f.matrix)*F.differential)*s := by rw [ht]
    _=(s*(f.matrix*F.differential))*s := by simp only [Matrix.mul_assoc]
    _=(s*(E.differential*f.matrix))*s := by rw [f.commute]
    _=(s*E.differential)*(f.matrix*s) := by simp only [Matrix.mul_assoc]
    _=(s*E.differential)*projectiveIdentity Q E.placement := by rw [hs]
    _=s*E.differential := mul_projectiveIdentity Q (projectiveEntries_mul Q hg E.entries)

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_PositiveConeIndex
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
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

def positiveConeIndex (f:Map Q E F) (α:V) :
    ((TestIndex Q E.placement α ⊕ I) ⊕ (TestIndex Q F.placement α ⊕ J)) ≃
      (TestIndex Q (f.cone Q).placement α ⊕ (I ⊕ J)) where
  toFun
    | .inl (.inl p) => .inl ⟨.inl p.1,p.2⟩
    | .inl (.inr i) => .inr (.inl i)
    | .inr (.inl p) => .inl ⟨.inr p.1,p.2⟩
    | .inr (.inr j) => .inr (.inr j)
  invFun
    | .inl ⟨.inl i,p⟩ => .inl (.inl ⟨i,p⟩)
    | .inl ⟨.inr j,p⟩ => .inr (.inl ⟨j,p⟩)
    | .inr (.inl i) => .inl (.inr i)
    | .inr (.inr j) => .inr (.inr j)
  left_inv := by intro k;rcases k with (p|i)|(p|j) <;> rfl
  right_inv := by intro k;rcases k with ⟨i|j,p⟩|(i|j) <;> rfl

def positiveConeSign (α:V) :
    ((TestIndex Q E.placement α ⊕ I) ⊕ (TestIndex Q F.placement α ⊕ J)) → Bool
  | .inl (.inl _) => true
  | _ => false

omit [DecidableEq I] [DecidableEq J] in
lemma positiveCone_placement (f:Map Q E F) (α:V) :
    ((f.positiveTwist Q α).cone Q).placement =
      (((f.cone Q).positiveTwist Q α).reindex Q (positiveConeIndex Q f α)).placement := by
  funext k
  rcases k with (p|i)|(p|j) <;> rfl

lemma positiveCone_differential (f:Map Q E F) (α:V)
    (i j:(TestIndex Q E.placement α ⊕ I) ⊕ (TestIndex Q F.placement α ⊕ J)) :
    (if positiveConeSign Q (E:=E) (F:=F) α j then
      -((((f.cone Q).positiveTwist Q α).reindex Q (positiveConeIndex Q f α)).differential i j)
     else (((f.cone Q).positiveTwist Q α).reindex Q (positiveConeIndex Q f α)).differential i j) =
    (if positiveConeSign Q (E:=E) (F:=F) α i then
      -(((f.positiveTwist Q α).cone Q).differential i j)
     else ((f.positiveTwist Q α).cone Q).differential i j) := by
  rcases i with (p|i)|(p|i) <;> rcases j with (r|j)|(r|j)
  · change -(-((pathCoordinates Q (pathBasis Q (K:=K) p.2.val * (-E.differential p.1 r.1)) r.2.val) • vertexId Q α)) =
      -(-(-((pathCoordinates Q (pathBasis Q (K:=K) p.2.val * E.differential p.1 r.1) r.2.val) • vertexId Q α)))
    simp only [neg_neg,mul_neg,map_neg,Pi.neg_apply,neg_smul]
  · change evaluationMatrix Q (f.cone Q).placement α ⟨.inl p.1,p.2⟩ (.inl j) =
      -(-evaluationMatrix Q E.placement α p j)
    simp only [evaluationMatrix,Sum.inl.injEq,neg_neg]
    split_ifs <;> rfl
  · rfl
  · change evaluationMatrix Q (f.cone Q).placement α ⟨.inl p.1,p.2⟩ (.inr j) = -(0:Q.Zigzag K)
    simp only [evaluationMatrix,Sum.inl_ne_inr,ite_false, if_false,neg_zero]
  · change -(0:Q.Zigzag K)= -0
    simp only [neg_zero]
  · rfl
  · rfl
  · rfl
  · change -(-((pathCoordinates Q (pathBasis Q (K:=K) p.2.val * 0) r.2.val) • vertexId Q α))=0
    simp only [mul_zero,map_zero,Pi.zero_apply,zero_smul,neg_zero]
  · change evaluationMatrix Q (f.cone Q).placement α ⟨.inr p.1,p.2⟩ (.inl j)=0
    simp only [evaluationMatrix,Sum.inr_ne_inl,ite_false, if_false]
  · rfl
  · change evaluationMatrix Q (f.cone Q).placement α ⟨.inr p.1,p.2⟩ (.inr j)=
      evaluationMatrix Q F.placement α p j
    simp only [evaluationMatrix,Sum.inr.injEq]
    split_ifs <;> rfl
  · change -(0:Q.Zigzag K)=0
    simp only [neg_zero]
  · rfl
  · rfl
  · rfl

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_Cone2
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

def ClassCone (x y z:FiniteHomotopyClass Q (K:=K)) : Prop :=
  ∃ E F:FiniteModel Q (K:=K), ∃ f:Map Q E.complex F.complex,
    classOfComplex Q E.complex=x ∧ classOfComplex Q F.complex=y ∧
    classOfComplex Q (f.cone Q)=z

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

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

def emptyTestIndex (E:BasedComplex Q (K:=K) I) (α:V)
    (h:IsEmpty (TestIndex Q E.placement α)) : I ≃ I ⊕ TestIndex Q E.placement α where
  toFun:=Sum.inl
  invFun
    | .inl i=>i
    | .inr p=>h.false p |>.elim
  left_inv _:=rfl
  right_inv k:=by cases k with
    | inl i=>rfl
    | inr p=>exact (h.false p).elim

omit [DecidableEq I] in
lemma negativeTwist_empty_reindex (E:BasedComplex Q (K:=K) I) (α:V)
    (h:IsEmpty (TestIndex Q E.placement α)) :
    (E.negativeTwist Q α).reindex Q (emptyTestIndex Q E α h)=E := by
  apply ext_placement_differential Q <;> rfl

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

noncomputable def highConeNormalized (E:BasedComplex Q (K:=K) I) (T:Set I)
    (h:DownClosed Q E T) :=
  ((highProjection Q E T h).cone Q).reindex Q (highConeIndex T)

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
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_ScalarExactNotZero
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf
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

omit [Fintype V] [DecidableEq A] in
lemma scalarExact_not_of_zero_differential {I:Type u} [Fintype I]
    (E:BasedComplex Q (K:=K) I) (α:V) (hd:E.differential=0) (i:I) :
    ¬ScalarExactAt Q E α (E.placement i).level (E.placement i).cochain := by
  intro h
  have hdm:E.differential.map (vertexHom Q α)=0 := by rw [hd]; ext a b; exact map_zero (vertexHom Q (K:=K) α)
  let x:I→K:=Pi.single i 1
  have hx:ScalarSupported Q E (E.placement i).level (E.placement i).cochain x := by
    intro j hj
    have hji:j≠i:=by rintro rfl; exact hj ⟨rfl,rfl⟩
    exact Pi.single_eq_of_ne hji _
  obtain ⟨y,_,hy⟩:=h x hx (by rw [hdm,Matrix.vecMul_zero])
  rw [hdm,Matrix.vecMul_zero] at hy
  have hh:=congrFun hy i
  simp [x] at hh

lemma classPositiveTwist_initial_orthogonal {α β:V} (h:OrthogonalVertices Q α β) :
    classPositiveTwist Q α (initialClass Q (K:=K) β)=initialClass Q β := by
  let E:=initialProjective Q (K:=K) β
  let :IsEmpty (TestIndex Q E.placement α):=⟨fun i=>by
    rcases i with ⟨i,⟨p,hs,ht⟩⟩
    change Path.source Q p=α at hs
    change Path.target Q p=β at ht
    rcases p with a|a|a
    · exact h.1 (hs.symm.trans ht)
    · exact h.2 a hs ht
    · exact h.1 (hs.symm.trans ht)⟩
  change classOfComplex Q (E.positiveTwist Q α)=classOfComplex Q E
  rw [classOfComplex_reindex Q _ (Equiv.emptySum (TestIndex Q E.placement α) PUnit).symm]
  congr 1

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Quivers_ProbeVertex
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.corner_val _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_reverse
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_InitialProbeTestUpper
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_NegativeConeIndex
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
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

def negativeConeIndex (f:Map Q E F) (α:V) :
    ((I ⊕ TestIndex Q E.placement α) ⊕ (J ⊕ TestIndex Q F.placement α)) ≃
      ((I ⊕ J) ⊕ TestIndex Q (f.cone Q).placement α) where
  toFun
    | .inl (.inl i) => .inl (.inl i)
    | .inl (.inr p) => .inr ⟨.inl p.1,p.2⟩
    | .inr (.inl j) => .inl (.inr j)
    | .inr (.inr p) => .inr ⟨.inr p.1,p.2⟩
  invFun
    | .inl (.inl i) => .inl (.inl i)
    | .inl (.inr j) => .inr (.inl j)
    | .inr ⟨.inl i,p⟩ => .inl (.inr ⟨i,p⟩)
    | .inr ⟨.inr j,p⟩ => .inr (.inr ⟨j,p⟩)
  left_inv := by
    intro k; rcases k with (i|p)|(j|p) <;> rfl
  right_inv := by
    intro k; rcases k with (i|j)|⟨i|j,p⟩ <;> rfl

def negativeConeSign (α:V) :
    ((I ⊕ TestIndex Q E.placement α) ⊕ (J ⊕ TestIndex Q F.placement α)) → Bool
  | .inl (.inr _) => true
  | _ => false

omit [DecidableEq I] [DecidableEq J] in
lemma negativeCone_placement (f:Map Q E F) (α:V) :
    ((f.negativeTwist Q α).cone Q).placement =
      (((f.cone Q).negativeTwist Q α).reindex Q (negativeConeIndex Q f α)).placement := by
  funext k
  rcases k with (i|p)|(j|p)
  · rfl
  · change GeneratorPlacement.mk α ((E.placement p.1).cochain+1-1)
        ((E.placement p.1).internal+Path.length p.2.val-2) =
      GeneratorPlacement.mk α ((E.placement p.1).cochain-1+1)
        ((E.placement p.1).internal+Path.length p.2.val-2)
    congr 1
    omega
  · rfl
  · rfl

lemma negativeCone_differential (f:Map Q E F) (α:V)
    (i j:(I ⊕ TestIndex Q E.placement α) ⊕ (J ⊕ TestIndex Q F.placement α)) :
    (if negativeConeSign Q (E:=E) (F:=F) α j then
      -((((f.cone Q).negativeTwist Q α).reindex Q (negativeConeIndex Q f α)).differential i j)
     else (((f.cone Q).negativeTwist Q α).reindex Q (negativeConeIndex Q f α)).differential i j) =
    (if negativeConeSign Q (E:=E) (F:=F) α i then
      -(((f.negativeTwist Q α).cone Q).differential i j)
     else ((f.negativeTwist Q α).cone Q).differential i j) := by
  rcases i with (i|p)|(i|p) <;> rcases j with (j|r)|(j|r)
  · rfl
  · change -coevaluationMatrix Q (f.cone Q).placement α (.inl i) ⟨.inl r.1,r.2⟩ =
      -coevaluationMatrix Q E.placement α i r
    simp only [coevaluationMatrix, Sum.inl.injEq]
    split_ifs <;> rfl
  · rfl
  · change coevaluationMatrix Q (f.cone Q).placement α (.inl i) ⟨.inr r.1,r.2⟩ = 0
    simp only [coevaluationMatrix, Sum.inl_ne_inr,ite_false, if_false]
  · change (0:Q.Zigzag K)= -(-0)
    simp only [neg_zero]
  · change -(-((pathCoordinates Q (pathBasis Q (K:=K) p.2.val * (-E.differential p.1 r.1)) r.2.val) • vertexId Q α)) =
      -(-(-((pathCoordinates Q (pathBasis Q (K:=K) p.2.val * E.differential p.1 r.1) r.2.val) • vertexId Q α)))
    simp only [neg_neg,mul_neg,map_neg,Pi.neg_apply,neg_smul]
  · change (0:Q.Zigzag K)= -0
    simp only [neg_zero]
  · rfl
  · rfl
  · change -coevaluationMatrix Q (f.cone Q).placement α (.inr i) ⟨.inl r.1,r.2⟩ = 0
    simp only [coevaluationMatrix, Sum.inr_ne_inl,ite_false, if_false,neg_zero]
  · rfl
  · change coevaluationMatrix Q (f.cone Q).placement α (.inr i) ⟨.inr r.1,r.2⟩ =
      coevaluationMatrix Q F.placement α i r
    simp only [coevaluationMatrix, Sum.inr.injEq]
    split_ifs <;> rfl
  · rfl
  · change -(-((pathCoordinates Q (pathBasis Q (K:=K) p.2.val * 0) r.2.val) • vertexId Q α))=0
    simp only [mul_zero,map_zero,Pi.zero_apply,zero_smul,neg_zero]
  · rfl
  · rfl

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_NegativeTwistModern
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

noncomputable def HomotopyEquivalence.negativeTwistModern
    {J:Type u} [Fintype J] [DecidableEq J]
    {E:BasedComplex Q (K:=K) I} {F:BasedComplex Q (K:=K) J}
    (e:HomotopyEquivalence Q E F) (α:V) :
    HomotopyEquivalence Q (E.negativeTwist Q α) (F.negativeTwist Q α) := by
  convert e.negativeTwist Q α using 1
  all_goals try with_reducible_and_instances rfl

noncomputable def allPureIndex (E:BasedComplex Q (K:=K) I) (q:ℤ)
    (h:∀ i,(E.placement i).level=q) : I ≃ {i:I // (E.placement i).level=q} where
  toFun i:=⟨i,h i⟩
  invFun i:=i.val
  left_inv _:=rfl
  right_inv _:=rfl

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_PositiveTwistModern
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

noncomputable def HomotopyEquivalence.positiveTwistModern
    {J:Type u} [Fintype J] [DecidableEq J]
    {E:BasedComplex Q (K:=K) I} {F:BasedComplex Q (K:=K) J}
    (e:HomotopyEquivalence Q E F) (α:V) :
    HomotopyEquivalence Q (E.positiveTwist Q α) (F.positiveTwist Q α) := by
  convert e.positiveTwist Q α using 1
  all_goals try with_reducible_and_instances rfl

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
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_ScalarKernel
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

def ScalarKernel {E:BasedComplex Q (K:=K) I} {F:BasedComplex Q (K:=K) J}
    (f:Map Q E F) (x:I→K) : Prop := ∀ j β,∑ i,x i*(f.matrix i j).vertex β=0

def PlacementSupported (E:BasedComplex Q (K:=K) I) (α:V) (c:ℤ) (x:I→K) : Prop :=
  ∀ i,(E.placement i).color≠α ∨ (E.placement i).cochain≠c→x i=0

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma differential_arrow_right_support (E:BasedComplex Q (K:=K) I) (i j:I) (a:A)
    (h:(E.placement j).color≠Q.target a) : (E.differential i j).arrow a=0 := by
  have hh:=congrArg (fun z:Q.Zigzag K=>z.arrow a) (E.entries.2 i j)
  simpa only [arrow_mul,Pi.add_apply,leftScale,rightScale,arrow_vertexId,Pi.zero_apply,
    MulZeroClass.mul_zero,zero_add,vertexId_eval,ite_eq_right h.symm,MulZeroClass.mul_zero] using hh.symm

noncomputable def coefficientOutgoing (E:BasedComplex Q (K:=K) I) (x:I→K) (a:A) : I→K :=
  fun j=>∑ i,x i*(E.differential i j).arrow a

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma coefficientOutgoing_support (E:BasedComplex Q (K:=K) I) (α:V) (c:ℤ)
    {x:I→K} (hx:PlacementSupported Q E α c x) (a:A) :
    PlacementSupported Q E (Q.target a) (c+1) (coefficientOutgoing Q E x a) := by
  intro j hj
  apply Finset.sum_eq_zero
  intro i _
  rcases hj with hj|hj
  · rw [differential_arrow_right_support Q E i j a hj,MulZeroClass.mul_zero]
  · by_cases hi:(E.placement i).cochain=c
    · rw [(E.degree i j).1 (by omega)]
      exact MulZeroClass.mul_zero _
    · rw [hx i (Or.inr hi),MulZeroClass.zero_mul]

omit [Fintype V] [DecidableEq A] [DecidableEq I] [DecidableEq J] in
lemma ScalarKernel.outgoing {E:BasedComplex Q (K:=K) I} {F:BasedComplex Q (K:=K) J}
    {f:Map Q E F} (hf:CoefficientMatrix Q f.matrix) {x:I→K} (hx:ScalarKernel Q f x)
    (a:A) : ScalarKernel Q f (coefficientOutgoing Q E x a) := by
  intro j β
  by_cases hb:β=(F.placement j).color
  · subst β
    by_cases hja:(F.placement j).color=Q.target a
    · rw [hja]
      have hh (i:I) := congrArg (fun M:Matrix I J (Q.Zigzag K)=>(M i j).arrow a) f.commute
      simp only [Matrix.mul_apply,arrow_sum,Finset.sum_apply,arrow_mul,Pi.add_apply,
        leftScale,rightScale,(hf _ _).1,Pi.zero_apply,MulZeroClass.mul_zero,
        MulZeroClass.zero_mul,zero_add,add_zero] at hh
      change ∑ k,(∑ i,x i*(E.differential i k).arrow a)*(f.matrix k j).vertex (Q.target a)=0
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      simp_rw [_root_.mul_assoc,← Finset.mul_sum,hh,Finset.mul_sum,← _root_.mul_assoc]
      rw [Finset.sum_comm]
      simp only [← Finset.sum_mul]
      apply Finset.sum_eq_zero
      intro k _
      rw [hx k (Q.source a),MulZeroClass.zero_mul]
    · apply Finset.sum_eq_zero
      intro i _
      by_cases hc:(E.placement i).color=Q.target a
      · have he:(f.matrix i j).vertex (F.placement j).color=0 := by
          by_contra he
          have hs:=reduction_support Q f.entries f.degree i j _ he
          exact hja (hs.1 ▸ hc)
        rw [he,MulZeroClass.mul_zero]
      · have hz:coefficientOutgoing Q E x a i=0 := by
          apply Finset.sum_eq_zero
          intro k _
          rw [differential_arrow_right_support Q E k i a hc,MulZeroClass.mul_zero]
        rw [hz,MulZeroClass.zero_mul]
  · apply Finset.sum_eq_zero
    intro i _
    rw [entry_vertex_right_support Q f.entries i j β hb,MulZeroClass.mul_zero]

omit [Fintype V] [DecidableEq A] [DecidableEq I] [DecidableEq J] in
lemma ScalarKernel.project {E:BasedComplex Q (K:=K) I} {F:BasedComplex Q (K:=K) J}
    {f:Map Q E F} {x:I→K} (hx:ScalarKernel Q f x) (p:GeneratorPlacement V) :
    ScalarKernel Q f (fun i=>if E.placement i=p then x i else 0) := by
  intro j β
  by_cases hj:F.placement j=p
  · convert hx j β using 1
    all_goals try with_reducible_and_instances rfl
    apply Finset.sum_congr rfl
    intro i _
    dsimp only
    by_cases hi:E.placement i=p
    · rw [ite_eq_left hi]
    · rw [ite_eq_right hi,MulZeroClass.zero_mul]
      have hz:(f.matrix i j).vertex β=0 := by
        by_contra hz
        exact hi ((reduction_support Q f.entries f.degree i j β hz).1.trans hj)
      rw [hz,MulZeroClass.mul_zero]
  · apply Finset.sum_eq_zero
    intro i _
    dsimp only
    by_cases hi:E.placement i=p
    · rw [ite_eq_left hi]
      have hz:(f.matrix i j).vertex β=0 := by
        by_contra hz
        exact hj ((reduction_support Q f.entries f.degree i j β hz).1.symm.trans hi)
      rw [hz,MulZeroClass.mul_zero]
    · rw [ite_eq_right hi,MulZeroClass.zero_mul]

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

noncomputable def Map.scalarMatrix {E:BasedComplex Q (K:=K) I} {F:BasedComplex Q (K:=K) J}
    (f:Map Q E F) : Matrix I J K := fun i j=>(f.matrix i j).vertex (F.placement j).color

omit [Fintype V] [DecidableEq A] [DecidableEq I] [DecidableEq J] in
lemma map_vertex_source_eq_target {E:BasedComplex Q (K:=K) I} {F:BasedComplex Q (K:=K) J}
    (f:Map Q E F) (i:I) (j:J) :
    (f.matrix i j).vertex (E.placement i).color=f.scalarMatrix Q i j := by
  by_cases h:(E.placement i).color=(F.placement j).color
  · exact congrArg _ h
  · rw [entry_vertex_right_support Q f.entries i j _ h]
    exact (entry_vertex_left_support Q f.entries i j _ (Ne.symm h)).symm

omit [Fintype V] [DecidableEq A] [DecidableEq I] [DecidableEq J] in
lemma map_coefficient_entry {E:BasedComplex Q (K:=K) I} {F:BasedComplex Q (K:=K) J}
    (f:Map Q E F) (hf:CoefficientMatrix Q f.matrix) (i:I) (j:J) :
    f.matrix i j=f.scalarMatrix Q i j •vertexId Q (E.placement i).color := by
  apply ext
  · funext β
    simp only [vertex_smul,Pi.smul_apply,smul_eq_mul,vertexId_eval]
    by_cases hb:β=(E.placement i).color
    · subst β
      rw [ite_eq_left rfl,_root_.mul_one]
      exact map_vertex_source_eq_target Q f i j
    · rw [ite_eq_right hb,MulZeroClass.mul_zero]
      exact entry_vertex_left_support Q f.entries i j _ hb
  · simpa only [arrow_smul,arrow_vertexId,smul_zero] using (hf i j).1
  · simpa only [token_smul,token_vertexId,smul_zero] using (hf i j).2

omit [Fintype V] [DecidableEq A] [DecidableEq I] [DecidableEq J] in
lemma scalarKernel_of_vecMul_zero {E:BasedComplex Q (K:=K) I} {F:BasedComplex Q (K:=K) J}
    (f:Map Q E F) {x:I→K} (hx:Matrix.vecMul x (f.scalarMatrix Q)=0) : ScalarKernel Q f x := by
  intro j β
  by_cases hb:β=(F.placement j).color
  · subst β
    exact congrFun hx j
  · apply Finset.sum_eq_zero
    intro i _
    rw [entry_vertex_right_support Q f.entries i j _ hb,MulZeroClass.mul_zero]

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

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_SumTestEquiv
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_SumTruncationEquiv
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_PositiveLiftSimple
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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

omit [Fintype S] in
lemma wordArtin_positive_power (v:List S) (n:ℕ) :
    ∃ u:List S,wordArtin M u=wordArtin M v^n := by
  induction n with
  | zero => exact ⟨[],by simp [wordArtin]⟩
  | succ n ih =>
    obtain ⟨u,hu⟩:=ih
    exact ⟨u++v,by rw [wordArtin_append,hu,pow_succ]⟩

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_FusionVertex
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin

variable {E V : Type*} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m : E → ℕ) (d : V → V → FusionEdge E)

noncomputable def fusionArrowAtEquiv (hd : ∀ s t, d s t = d t s)
    (α β : FusionVertex (V := V) m) :
    {a : FusionQuiverArrow m d // (fusionQuiver m d hd).source a = α ∧
      (fusionQuiver m d hd).target a = β} ≃
      Fin ((d α.1 β.1).multiplicity m α.2 β.2) where
  toFun a := Fin.cast (congrArg₂ (fun (i j : FusionVertex (V := V) m) =>
    (d i.1 j.1).multiplicity m i.2 j.2) a.property.1 a.property.2) a.val.2
  invFun k := ⟨⟨(α,β),k⟩,rfl,rfl⟩
  left_inv := by
    rintro ⟨⟨⟨α',β'⟩,k⟩,hα,hβ⟩
    change α'=α at hα
    change β'=β at hβ
    subst α'; subst β'; rfl
  right_inv _ := rfl

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Functors_LayerIndexEquiv
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
open Zigzag.BasedComplex

variable (ho : ∀ b, orient (Q.reverse b) = !(orient b))
    (hμ : ∀ a, μ a ≠ 0) (δ : K)
    (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
    (hPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, μ b = δ * μ a)

variable {T : Type u} [Fintype T] [DecidableEq T]
def layerIndexEquiv (p : T → GeneratorPlacement (V × J)) (d : ℤ) :
    Index N (fun i : {i // (p i).level=d} => p i) ≃
      {i : Index N p // (placement N p i).level=d} where
  toFun x := ⟨⟨x.1.val,x.2⟩,x.1.property⟩
  invFun x := ⟨⟨x.1.1,x.2⟩,x.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end HarmonicArtin.ReversibleQuiver.StringFunctor

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_MaximalReducedPositivePrefix
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CoxeterExchange

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type*} [Fintype S] (M:CoxeterMatrix S)

lemma reduced_right_factor (w:List S) (s:S) (hw:M.toCoxeterSystem.IsReduced w)
    (h:¬M.toCoxeterSystem.IsReduced (w++[s])) :
    ∃v:List S,M.toCoxeterSystem.IsReduced v ∧
      wordArtin M w=wordArtin M v*generator M s ∧ v.length+1=w.length := by
  let cs:=M.toCoxeterSystem
  have hd:cs.IsRightDescent (cs.wordProd w) s := by
    by_contra hn
    apply h
    change cs.length (cs.wordProd (w++[s]))=(w++[s]).length
    simp only [cs.wordProd_append,cs.wordProd_cons,cs.wordProd_nil,mul_one,List.length_append,List.length_singleton]
    rw [cs.not_isRightDescent_iff.mp hn,hw.eq]
  obtain ⟨v,hv,he⟩:=cs.exists_isReduced (cs.wordProd w*cs.simple s)
  have hp:cs.wordProd (v++[s])=cs.wordProd w := by
    simp only [cs.wordProd_append,cs.wordProd_cons,cs.wordProd_nil,mul_one]
    rw [←he,mul_assoc,cs.simple_mul_simple_self,mul_one]
  have hl:v.length+1=w.length := by
    rw [←hv.eq,←he,←hw.eq]
    exact cs.isRightDescent_iff.mp hd
  have hr:cs.IsReduced (v++[s]) := by
    change cs.length (cs.wordProd (v++[s]))=(v++[s]).length
    rw [hp,hw.eq,List.length_append,List.length_singleton,hl]
  refine ⟨v,hv,?_,hl⟩
  have heq:=wordArtin_eq_of_reduced M w (v++[s]) hw hr hp.symm
  rw [wordArtin_append] at heq
  simpa only [wordArtin,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one] using heq

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_RestrictedArtinHom
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ParabolicIntersections.artinExponent_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.artinMap_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.mem_relativeStabilizer _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeArtinHom_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visualFromArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visualToArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visual_smul_vertex _root_.OAI.HarmonicArtin.artinCoxeter_generator _root_.OAI.HarmonicArtin.positiveToArtin_generator _root_.OAI.HarmonicArtin.positiveToArtin_word
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type*} (M:CoxeterMatrix S) (J:Set S)

lemma restrictedArtinHom_word (w:List J) :
    restrictedArtinHom M J (wordArtin (restrictedMatrix M J) w)=wordArtin M (w.map Subtype.val) := by
  induction w with
  | nil => simp [wordArtin]
  | cons s w ih =>
    change restrictedArtinHom M J (generator (restrictedMatrix M J) s * wordArtin _ w)=
      generator M s * wordArtin M (w.map Subtype.val)
    rw [map_mul,restrictedArtinHom_generator,ih]

lemma restrictedArtinHom_range : (restrictedArtinHom M J).range=artinParabolic M J := by
  apply le_antisymm
  · rintro _ ⟨g,rfl⟩
    have hg:g∈Subgroup.closure (Set.range (generator (restrictedMatrix M J))) := by
      have hh:Subgroup.closure (Set.range (generator (restrictedMatrix M J)))=⊤:=
        PresentedGroup.closure_range_of (braidRelators (restrictedMatrix M J))
      rw [hh]; trivial
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨s,rfl⟩:=hx
      rw [restrictedArtinHom_generator]
      exact Subgroup.subset_closure ⟨s,s.property,rfl⟩
    | one => rw [map_one]; exact Subgroup.one_mem _
    | mul x y hx hy hix hiy => rw [map_mul]; exact Subgroup.mul_mem _ hix hiy
    | inv x hx hix => rw [map_inv]; exact Subgroup.inv_mem _ hix
  · apply (Subgroup.closure_le _).2
    rintro _ ⟨s,hs,rfl⟩
    exact ⟨generator (restrictedMatrix M J) ⟨s,hs⟩,restrictedArtinHom_generator M J _⟩

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Functors_ZigzagLinear
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.corner_val _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_reverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.ProbeEmbedding
open Zigzag Zigzag.BasedComplex

variable {V A K : Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V]
  [DecidableEq (ProbeVertex V)]

variable {I J L:Type*}

lemma complex_minimal [Fintype I] {E : BasedComplex Q (K := K) I} (h:E.IsMinimal Q) :
    (complex Q E).IsMinimal (probeQuiver Q) := by
  intro i j
  ext v
  change (zigzagLinear Q (E.differential i j)).vertex v=0
  cases v <;> simp [h i j]

end HarmonicArtin.ReversibleQuiver.ProbeEmbedding

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Functors_Path2
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.ProbeEmbedding
open Zigzag Zigzag.BasedComplex

variable {V A K:Type*} (Q:ReversibleQuiver V A)
local notation "R" => probeQuiver Q

lemma path_injective : Function.Injective (path (V:=V) (A:=A)) := by
  exact Sum.map_injective.mpr ⟨Sum.inl_injective,Sum.map_injective.mpr ⟨Sum.inl_injective,Sum.inl_injective⟩⟩

lemma cornerPath_surjective (s t:V)
    (p:CornerPath R (.inl s) (.inl t)) :
    ∃q:CornerPath Q s t,path q.val=p.val := by
  rcases p with ⟨p,hs,ht⟩
  rcases p with (v|v)|(a|⟨v,b,d⟩)|(v|v)
  · exact ⟨⟨.inl v,Sum.inl.inj hs,Sum.inl.inj ht⟩,rfl⟩
  · cases hs
  · exact ⟨⟨.inr (.inl a),Sum.inl.inj hs,Sum.inl.inj ht⟩,rfl⟩
  · cases d
    · cases ht
    · cases hs
  · exact ⟨⟨.inr (.inr v),Sum.inl.inj hs,Sum.inl.inj ht⟩,rfl⟩
  · cases hs

noncomputable def cornerPath (s t:V) : CornerPath Q s t ≃ CornerPath R (.inl s) (.inl t) :=
  Equiv.ofBijective (fun p=>⟨path p.val,by
    rw [path_source,path_target,p.property.1,p.property.2]; exact ⟨rfl,rfl⟩⟩)
    ⟨fun _ _ h=>Subtype.ext (path_injective (congrArg Subtype.val h)),by
      intro p; obtain ⟨q,hq⟩:=cornerPath_surjective Q s t p
      exact ⟨q,Subtype.ext hq⟩⟩

end HarmonicArtin.ReversibleQuiver.ProbeEmbedding

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Functors_TestIndex2
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.ProbeEmbedding
open Zigzag Zigzag.BasedComplex

variable {V A K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [DecidableEq (ProbeVertex V)] [DecidableEq (ProbeArrow V A)]
  {I J:Type*}
local notation "R" => probeQuiver Q

noncomputable def testIndex (p : I → GeneratorPlacement V) (α:V) :
    TestIndex Q p α ≃ TestIndex R (placement ∘ p) (Sum.inl α) :=
  Equiv.sigmaCongrRight fun i => cornerPath Q α (p i).color

end HarmonicArtin.ReversibleQuiver.ProbeEmbedding

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Coxeter_ParabolicProductMap
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ParabolicIntersections.artinExponent_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.artinMap_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.mem_relativeStabilizer _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeArtinHom_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visualFromArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visualToArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visual_smul_vertex _root_.OAI.HarmonicArtin.artinCoxeter_generator _root_.OAI.HarmonicArtin.positiveToArtin_generator _root_.OAI.HarmonicArtin.positiveToArtin_word
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

omit [Fintype S] [LinearOrder S] in
lemma sourceParabolic_union (B C:Set S) :
    artinParabolic M (B∪C)=artinParabolic M B⊔artinParabolic M C := by
  simp only [artinParabolic,Set.image_union,Subgroup.closure_union]

omit [Fintype S] [LinearOrder S] in
lemma sourceParabolicProductMap_apply (B C:Set S) (hc:∀s∈B,∀t∈C,M s t=2)
    (x:artinParabolic M B × artinParabolic M C) :
    sourceParabolicProductMap M B C hc x=(x.1:Artin M)*x.2 :=rfl

omit [Fintype S] [LinearOrder S] in
lemma sourceParabolicProductMap_range (B C:Set S) (hc:∀s∈B,∀t∈C,M s t=2) :
    (sourceParabolicProductMap M B C hc).range=artinParabolic M (B∪C) := by
  rw [sourceParabolic_union]
  apply le_antisymm
  · rintro g ⟨⟨b,c⟩,rfl⟩
    exact Subgroup.mul_mem _
      ((show artinParabolic M B ≤ artinParabolic M B ⊔ artinParabolic M C from le_sup_left) b.property)
      ((show artinParabolic M C ≤ artinParabolic M B ⊔ artinParabolic M C from le_sup_right) c.property)
  · apply sup_le
    · intro b hb
      exact ⟨(⟨b,hb⟩,1),by simp [sourceParabolicProductMap_apply]⟩
    · intro c hc'
      exact ⟨(1,⟨c,hc'⟩),by simp [sourceParabolicProductMap_apply]⟩

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_CosetBelow
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

omit [Fintype S] [LinearOrder S] in
lemma sourceSplit_difference (B C:Set S) (hc:∀s∈B,∀t∈C,M s t=2)
    (b b':artinParabolic M B) (c c':artinParabolic M C) (x:Artin M) :
    ((b:Artin M)*c*x)*((b':Artin M)*c'*x)⁻¹=
      ((b:Artin M)*(b':Artin M)⁻¹)*((c:Artin M)*(c':Artin M)⁻¹) := by
  have he:=sourceParabolics_commute M B C hc ((b':Artin M)⁻¹) ((c:Artin M)*(c':Artin M)⁻¹)
    (Subgroup.inv_mem _ b'.property) (Subgroup.mul_mem _ c.property (Subgroup.inv_mem _ c'.property))
  calc
    _=(b:Artin M)*(((c:Artin M)*(c':Artin M)⁻¹)*(b':Artin M)⁻¹):=by group
    _=(b:Artin M)*((b':Artin M)⁻¹*((c:Artin M)*(c':Artin M)⁻¹)):=by rw [he.eq]
    _=_:=by group

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_MaximalReducedMonoidPrefix
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CoxeterExchange

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type*} [Fintype S] (M:CoxeterMatrix S)

lemma reduced_monoid_right_factor (w:List S) (s:S) (hw:M.toCoxeterSystem.IsReduced w)
    (h:¬M.toCoxeterSystem.IsReduced (w++[s])) :
    ∃v:List S,M.toCoxeterSystem.IsReduced v ∧
      wordPositive M w=wordPositive M v*positiveGenerator M s ∧ v.length+1=w.length := by
  let cs:=M.toCoxeterSystem
  have hd:cs.IsRightDescent (cs.wordProd w) s := by
    by_contra hn
    apply h
    change cs.length (cs.wordProd (w++[s]))=(w++[s]).length
    simp only [cs.wordProd_append,cs.wordProd_cons,cs.wordProd_nil,mul_one,List.length_append,List.length_singleton]
    rw [cs.not_isRightDescent_iff.mp hn,hw.eq]
  obtain ⟨v,hv,he⟩:=cs.exists_isReduced (cs.wordProd w*cs.simple s)
  have hp:cs.wordProd (v++[s])=cs.wordProd w := by
    simp only [cs.wordProd_append,cs.wordProd_cons,cs.wordProd_nil,mul_one]
    rw [←he,mul_assoc,cs.simple_mul_simple_self,mul_one]
  have hl:v.length+1=w.length := by
    rw [←hv.eq,←he,←hw.eq]
    exact cs.isRightDescent_iff.mp hd
  have hr:cs.IsReduced (v++[s]) := by
    change cs.length (cs.wordProd (v++[s]))=(v++[s]).length
    rw [hp,hw.eq,List.length_append,List.length_singleton,hl]
  refine ⟨v,hv,?_,hl⟩
  have heq:=wordPositive_eq_of_reduced M w (v++[s]) hw hr hp.symm
  rw [wordPositive_append] at heq
  simpa only [wordPositive,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one] using heq

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_VisualTree
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Bass--Serre tree and stabilizers of an actual visual Artin splitting. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} (M : CoxeterMatrix S) (Y Z : Set S)
local notation "φ" => visualEdgeInclusion M Y Z

noncomputable abbrev visualGraph := AmalgamTree.graph φ

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_VisualEdgeTransitive
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transitivity on oriented edges of the visual Bass--Serre tree. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} (M : CoxeterMatrix S) (Y Z : Set S)
variable [hSplit : Fact (IsVisualSplit M Y Z)]
noncomputable local instance visualEdgeTransitiveAction : MulAction (Artin M) (VisualVertex M Y Z) :=
  visualAction M Y Z hSplit.out

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Realizations_RealizeSimplex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section TopologyDependencies
open CategoryTheory Opposite Simplicial
open scoped unitInterval

namespace HarmonicArtin
universe u

lemma toSimp_map_symm (Y : TopCat.{u}) {n m : SimplexCategoryᵒᵖ} (a : n ⟶ m)
    (g : C(Convexity.StdSimplex ℝ (Fin (n.unop.len + 1)), Y))
    (z : Convexity.StdSimplex ℝ (Fin (m.unop.len + 1))) :
    toSimp Y m ((TopCat.toSSet.obj Y).map a ((toSimp Y n).symm g)) z =
      g (Convexity.StdSimplex.map a.unop.toOrderHom z) := by
  have key := toSimp_naturality_apply (Y := Y) a.unop ((toSimp Y n).symm g) z
  rw [Equiv.apply_symm_apply] at key
  exact key

end HarmonicArtin

end TopologyDependencies

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Realizations_NerveChain
attribute [-instance] _root_.OAI.HarmonicArtin.finiteLinearWeightsCompact _root_.OAI.HarmonicArtin.instT2SpaceOrderWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open scoped BigOperators
open Simplicial CategoryTheory Opposite Convexity

attribute [local instance] Classical.decEq Classical.propDecidable
universe u
variable {P:Type u} [PartialOrder P]

noncomputable def nerveWeightsMap : nerve P⟶TopCat.toSSet.obj (TopCat.of (OrderWeights P)) where
  app n:=↾fun x=>(toSimp _ n).symm (nerveWeightsSimplex x)
  naturality {n m} a:=by
    apply ConcreteCategory.hom_ext
    intro x
    apply (toSimp _ m).injective
    ext z : 1
    apply OrderWeights.ext
    change (toSimp (TopCat.of (OrderWeights P)) m ((toSimp (TopCat.of (OrderWeights P)) m).symm
        (nerveWeightsSimplex ((nerve P).map a x))) z).weights =
      (toSimp (TopCat.of (OrderWeights P)) m ((TopCat.toSSet.obj (TopCat.of (OrderWeights P))).map a
        ((toSimp (TopCat.of (OrderWeights P)) n).symm (nerveWeightsSimplex x))) z).weights
    rw [toSimp_map_symm, Equiv.apply_symm_apply]
    exact chainWeights_natural (nerveChain x) a.unop.toOrderHom z

noncomputable def nerveToWeights : C(|nerve P|,OrderWeights P) :=
  ((sSetTopAdj.homEquiv _ _).symm nerveWeightsMap).hom

lemma nerveToWeights_simplex {n:SimplexCategory} (x:(nerve P).obj (op n))
    (z:StdSimplex ℝ (Fin (n.len+1))) :
    nerveToWeights (realizeSimplex (nerve P) x z)=orderWeightsOfChain (nerveChain x) z := by
  have he:(sSetTopAdj.homEquiv _ _) (TopCat.ofHom (nerveToWeights (P:=P)))=nerveWeightsMap:=
    (sSetTopAdj.homEquiv _ _).apply_symm_apply _
  rw [Adjunction.homEquiv_unit] at he
  have hh:=ConcreteCategory.congr_hom (congrArg (fun f:nerve P ⟶ TopCat.toSSet.obj (TopCat.of (OrderWeights P))=>f.app (op n)) he) x
  have ht:=congrArg (fun f=>(toSimp _ (op n)) f z) hh
  exact ht

noncomputable def weightsToNerve (w:OrderWeights P) : |nerve P| :=
  realizeSimplex (nerve P) (n:=⦋weightDim w⦌) (nerveOfChain (weightChain w)) (weightSimplex w)

lemma nerveToWeights_weightsToNerve (w:OrderWeights P) :
    nerveToWeights (weightsToNerve w)=w := by
  unfold weightsToNerve
  rw [nerveToWeights_simplex (n:=⦋weightDim w⦌)]
  exact orderWeightsOfChain_canonical w

lemma weightsToNerve_simplex {n:SimplexCategory} (x:(nerve P).obj (op n))
    (z:StdSimplex ℝ (Fin (n.len+1))) :
    weightsToNerve (orderWeightsOfChain (nerveChain x) z)=realizeSimplex (nerve P) x z := by
  let a:⦋simplexSupportDim z⦌⟶n:=SimplexCategory.mkHom (simplexSupportInclusion z)
  let b:⦋simplexSupportDim z⦌⟶⦋weightDim (orderWeightsOfChain (nerveChain x) z)⦌:=
    SimplexCategory.mkHom (supportedWeightMap (nerveChain x) z)
  have he:(nerve P).map b.op (nerveOfChain (weightChain (orderWeightsOfChain (nerveChain x) z)))=
      (nerve P).map a.op x:=by
    apply nerve.ext_of_isThin
    funext i
    exact DFunLike.congr_fun (supportedWeightMap_chain (nerveChain x) z) i
  have h₁:=realizeSimplex_natural (nerve P) b
    (nerveOfChain (weightChain (orderWeightsOfChain (nerveChain x) z))) (simplexSupported z)
  have h₂:=realizeSimplex_natural (nerve P) a x (simplexSupported z)
  change _=realizeSimplex (nerve P) x (StdSimplex.map (simplexSupportInclusion z) (simplexSupported z)) at h₂
  rw [simplexSupported_map] at h₂
  have hb:StdSimplex.map b.toOrderHom (simplexSupported z)=weightSimplex (orderWeightsOfChain (nerveChain x) z):=
    supportedWeightMap_simplex (nerveChain x) z
  rw [he,hb] at h₁
  exact h₁.symm.trans h₂

lemma weightsToNerve_continuous : Continuous (weightsToNerve (P:=P)) := by
  rw [orderWeights_continuous_iff]
  intro n x
  simp_rw [weightsToNerve_simplex]
  exact (realizeSimplex (nerve P) x).continuous

noncomputable def nerveWeightsHomeomorph : |nerve P| ≃ₜ OrderWeights P := by
  have he:ContinuousMap.comp ⟨weightsToNerve,weightsToNerve_continuous⟩ nerveToWeights=ContinuousMap.id |nerve P|:=by
    have ht:TopCat.ofHom (ContinuousMap.comp ⟨weightsToNerve,weightsToNerve_continuous⟩ nerveToWeights)=𝟙 |nerve P|:=by
      apply (sSetTopAdj.homEquiv _ _).injective
      rw [Adjunction.homEquiv_unit,Adjunction.homEquiv_unit]
      ext n x
      apply (toSimp _ n).injective
      ext z
      change weightsToNerve (nerveToWeights (realizeSimplex (nerve P) x z))=realizeSimplex (nerve P) x z
      rw [nerveToWeights_simplex,weightsToNerve_simplex]
    exact congrArg TopCat.Hom.hom ht
  exact {
    toFun:=nerveToWeights
    invFun:=weightsToNerve
    left_inv:=fun x=>ContinuousMap.congr_fun he x
    right_inv:=nerveToWeights_weightsToNerve
    continuous_toFun:=nerveToWeights.continuous
    continuous_invFun:=weightsToNerve_continuous }

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Realizations_NerveOrderMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
universe u
open scoped unitInterval
open Simplicial CategoryTheory Opposite

attribute [local instance] Classical.decEq Classical.propDecidable

noncomputable def nerveVertex (Q:Type u) [Preorder Q] (c:Q) : |nerve Q| :=
  realizeSimplex (nerve Q) (ComposableArrows.mk₀ c) (Convexity.StdSimplex.single 0)

end HarmonicArtin

end OAI
end


