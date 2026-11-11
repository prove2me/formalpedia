-- Prove2me | Definitions.Def_OAIQ236Ap008
-- name    : OAIQ236Ap008
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T19:58:16.72439+00:00
-- url     : https://prove2.me/theorems/353133b7-fb15-4e25-8bf5-ac34efdca7fe
-- title:
--   Definitions bundle OAIQ236Ap008 of the split of OpenAI, Parabolic intersections in Artin groups
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.HarmonicArtin.ParabolicIntersections.unconditional_arbitrary_intersections`, `OAI.HarmonicArtin.ParabolicIntersections.unconditional_nonclique_dynamics`, `OAI.HarmonicArtin.ParabolicIntersections.unconditional_parabolic_closure` and `OAI.HarmonicArtin.ParabolicIntersections.unconditional_parabolic_intersections`, carved from OpenAI's openai/math development (OpenAI, *Parabolic intersections in Artin groups*, OpenAI Math Release, September 23, 2026, result family 254, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 142 declarations of OpenAI's Lean: 42 definitions, 1 inductive type or structure and 99 theorems. The definitions and types are `OAI.HarmonicArtin.IsolatedIterationData`, `OAI.HarmonicArtin.IsolatedIterationData.capped`, `OAI.HarmonicArtin.IsolatedIterationData.fullRegion`, `OAI.HarmonicArtin.IsolatedIterationData.openSocle`, `OAI.HarmonicArtin.IsolatedIterationData.operated`, `OAI.HarmonicArtin.IsolatedIterationData.region`, `OAI.HarmonicArtin.ParabolicIntersections.ClassTestCochainUpper`, `OAI.HarmonicArtin.ParabolicIntersections.PointedClass`, `OAI.HarmonicArtin.ParabolicIntersections.PointedFamilySpace`, `OAI.HarmonicArtin.ParabolicIntersections.PointedLabel`, `OAI.HarmonicArtin.ParabolicIntersections.pointedAction`, `OAI.HarmonicArtin.ParabolicIntersections.pointedCosetVector`, `OAI.HarmonicArtin.ParabolicIntersections.pointedFamily`, `OAI.HarmonicArtin.ParabolicIntersections.pointedHarmonicAt`, `OAI.HarmonicArtin.ParabolicIntersections.pointedInitial`, `OAI.HarmonicArtin.ParabolicIntersections.pointedMultiplicity`, `OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.packetComparison`, `OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.packetTwistComparison`, `OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.signedPacketPerm`, `OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.wordPacketPerm`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.ChainIsomorphism.cone`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.ClassBottomSocleZero`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.Map.reindexConeIsomorphism`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.adjacent_positiveTwists`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidSecondPivot`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistReduction`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.classLayerSocleDimension`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.classSignedVector`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.minimalClassModelEquivalence`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.reducedBraidTwist`, `OAI.HarmonicArtin.ReversibleQuiver.fixedOrientation`, `OAI.HarmonicArtin.fusionArrowJoin`, `OAI.HarmonicArtin.fusionArrowSplit`, `OAI.HarmonicArtin.fusionOrbitColorLayer`, `OAI.HarmonicArtin.fusionOrbitLayer`, `OAI.HarmonicArtin.fusionOrbitMultiplicity`, `OAI.HarmonicArtin.fusionOrbitWeightedVector`, `OAI.HarmonicArtin.fusionQuiverSplit`, `OAI.HarmonicArtin.sourceArtinAction`, `OAI.HarmonicArtin.sourceCoset` and 3 more.
--
--   **Sources.** They come from these modules of lean/OAI/Topology, in whole or in part: `ArtinGroups_Complexes_BottomSocleZero`, `ArtinGroups_Complexes_FiniteHomotopySetoid`, `ArtinGroups_Complexes_GeneratorVectorPureLayer`, `ArtinGroups_Complexes_LevelArrayComplexMinimal`, `ArtinGroups_Complexes_MinimalModelEquivalence`, `ArtinGroups_Complexes_NegativeTwistModern`, `ArtinGroups_Complexes_OptionSumEquiv`, `ArtinGroups_Complexes_PacketPermEnumeration`, `ArtinGroups_Complexes_PacketPermReindex`, `ArtinGroups_Complexes_PlacementSignedWeight`, `ArtinGroups_Complexes_Refl`, `ArtinGroups_Complexes_ReindexConeIsomorphism`, `ArtinGroups_Complexes_Sum`, `ArtinGroups_Complexes_TotalVector`, `ArtinGroups_Complexes_TotalVectorLayer`, `ArtinGroups_Complexes_UpperBound`, `ArtinGroups_Coxeter_AlternatingLiftProd`, `ArtinGroups_Coxeter_BraidCoreFirstTarget`, `ArtinGroups_Coxeter_BraidCorePlacement`, `ArtinGroups_Coxeter_BraidSecondPivot`, `ArtinGroups_Coxeter_OrdinaryTwistBraid`, `ArtinGroups_Functors_ColorPacketPerm`, `ArtinGroups_Functors_Index`, `ArtinGroups_Functors_LayerIndexEquiv`, `ArtinGroups_Functors_LevelGeneratorEquiv`, `ArtinGroups_Functors_PacketSwitchMatrix`, `ArtinGroups_Functors_PacketTwistComparison`, `ArtinGroups_Functors_ReversibleQuiverMap`, `ArtinGroups_Functors_SignedPacketPerm`, `ArtinGroups_Functors_WordOrbitCountAdjacency`, `ArtinGroups_Functors_WordPacketPermAppend`, `ArtinGroups_Harmonic_ArtinAction`, `ArtinGroups_Harmonic_Coset`, `ArtinGroups_Harmonic_DimensionPosMultiplicityPos`, `ArtinGroups_Harmonic_FusionColorRegion`, `ArtinGroups_Harmonic_FusionExpandedWordAction`, `ArtinGroups_Harmonic_FusionExpandedWordPerm`, `ArtinGroups_Harmonic_FusionFactorStep`, `ArtinGroups_Harmonic_FusionOrbitModel`, `ArtinGroups_Harmonic_FusionOrbitMultiplicity`, `ArtinGroups_Harmonic_FusionPacketOrbit`, `ArtinGroups_Harmonic_FusionPacketPerm`, `ArtinGroups_Harmonic_Harmonic`, `ArtinGroups_Harmonic_IsolatedBoundaryAbsent`, `ArtinGroups_Harmonic_IsolatedIterationData`, `ArtinGroups_Harmonic_SphericalFoldedMatrix`, `ArtinGroups_Harmonic_SphericalPacketWordProperty`, `ArtinGroups_Harmonic_StringAdjacent`, `ArtinGroups_Harmonic_UnfoldedColorOrthogonal`, `ArtinGroups_Harmonic_UnfoldedHom`, `ArtinGroups_Harmonic_UnfoldedInclusion`, `ArtinGroups_Harmonic_UnfoldedMatrix`, `ArtinGroups_ParabolicIntersections_PointedFamily`, `ArtinGroups_ParabolicIntersections_PointedMultiplicity`, `ArtinGroups_ParabolicIntersections_PointedProfile`, `ArtinGroups_ParabolicIntersections_SphericalCochain`.
--
--   **Imports.** It imports the published bundle `Def_ArtinParabolicIntersections`; the bundles `OAIQ236Ap005` and `OAIQ236Ap006` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ236Ap011` and `OAIQ236Ap012`; the statements `OAI_HarmonicArtin_IsolatedIterationData_cap_move`, `OAI.HarmonicArtin.IsolatedIterationData.cap_move_s236`, `OAI_HarmonicArtin_IsolatedIterationData_stage_move`, `OAI.HarmonicArtin.IsolatedIterationData.stage_move_s236`, `OAI_HarmonicArtin_ParabolicIntersections_null_boundary_contradiction` and `OAI.HarmonicArtin.ParabolicIntersections.null_boundary_contradiction_s236`.
-- source:
--   OpenAI, Parabolic intersections in Artin groups, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 254; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Parabolic-intersections-in-Artin-groups-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Topology at commit adc7f12

import Mathlib
import Definitions.Def_ArtinParabolicIntersections
import Definitions.Def_OAIQ236Ap005
import Definitions.Def_OAIQ236Ap006

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Coxeter_BraidCoreFirstTarget
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Coxeter_BraidSecondPivot
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Coxeter_BraidCorePlacement
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_FiniteHomotopySetoid
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_Refl
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_MinimalModelEquivalence
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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

noncomputable def classLayerSocleDimension (d : ℤ) (α : V) (c : ℤ)
    (x : FiniteHomotopyClass Q (K := K)) : ℕ :=
  Module.finrank K (coefficientSocle Q
    ((minimalClassModel Q x).complex.pureLayer Q (minimalClassModel_minimal Q x) d) α c)

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_UpperBound
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_BottomSocleZero
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_GeneratorVectorPureLayer
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_Sum
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_LevelArrayComplexMinimal
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_PacketPermReindex
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_OptionSumEquiv
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_PacketPermEnumeration
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_PlacementSignedWeight
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_ReindexConeIsomorphism
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_TotalVector
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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
lemma classSignedVector_pure (x : FiniteHomotopyClass Q (K:=K)) (q : ℤ)
    (hlo : ClassLowerBound Q q x) (hhi : ClassUpperBound Q q x) :
    classSignedVector Q x=cochainSign (K:=ℝ) q • classTotalVector Q x := by
  rw [classSignedVector_minimal]
  exact signedGeneratorVector_pure Q _ q (fun i=>le_antisymm (hhi i) (hlo i))

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_TotalVectorLayer
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Functors_ReversibleQuiverMap
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Functors_Index
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Functors_PacketSwitchMatrix
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable
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

noncomputable def packetComparison (E : Zigzag.BasedComplex U (K := K) T) (u:V) :
    Zigzag.BasedComplex.ChainIsomorphism U
      ((C (E.packetTest U (fun a:J => (u,a)))).reindex U
        (leftPacketEquiv Q step hstep N hN E.placement u))
      (((C E).packetTest U (fun a:J => (u,a))).reindex U
        (rightPacketEquiv Q step hstep N hN E.placement u)) := by
  let s := Zigzag.BasedComplex.ChainIsomorphism.finiteSum U
    (fun c => homComparison Q step hstep N hN orient μ A ho hμ δ hA hroot hPF E u c)
  have hL := congrArg Zigzag.BasedComplex.differential
    (leftPacketComplex_eq Q step hstep N hN orient μ A ho hμ δ hA hroot hPF E u)
  have hR := congrArg Zigzag.BasedComplex.differential
    (rightPacketComplex_eq Q step hstep N hN orient μ A ho hμ δ hA hroot hPF E u)
  exact {
    forward := {
      matrix := s.forward.matrix
      entries := s.forward.entries
      degree := s.forward.degree
      commute := by rw [hL,hR]; exact s.forward.commute }
    backward := {
      matrix := s.backward.matrix
      entries := s.backward.entries
      degree := s.backward.degree
      commute := by rw [hL,hR]; exact s.backward.commute }
    sourceEquation := s.sourceEquation
    targetEquation := s.targetEquation }

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
-- module Solutions.OAIQ236_AP.ArtinGroups_Functors_PacketTwistComparison
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable
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

lemma packetComparison_matrix (E : Zigzag.BasedComplex U (K := K) T) (u:V) :
    (packetComparison Q step hstep N hN orient μ A ho hμ δ hA hroot hPF E u).forward.matrix =
      packetSwitchMatrix Q step hstep N hN orient μ A E.placement u := by
  rfl

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
-- module Solutions.OAIQ236_AP.ArtinGroups_Functors_ColorPacketPerm
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Functors_SignedPacketPerm
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Functors_WordPacketPermAppend
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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
local notation "U" => Q.stringQuiver step hstep N hN
open Zigzag.BasedComplex

variable (ho : ∀ b, orient (Q.reverse b) = !(orient b))
    (hμ : ∀ a, μ a ≠ 0) (δ : K)
    (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
    (hPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, μ b = δ * μ a)
local notation "C" => complex Q step hstep N hN orient μ A ho hμ δ hA hroot hPF
local notation "F" => classLabelFunctor Q step hstep N hN orient μ A ho hμ δ hA hroot hPF

variable {T : Type u} [Fintype T] [DecidableEq T]

lemma classLabel_complex (E : Zigzag.BasedComplex U (K := K) T) :
    F (classOfComplex U E) = classOfComplex U (C E) := rfl

end HarmonicArtin.ReversibleQuiver.StringFunctor

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Functors_LevelGeneratorEquiv
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Functors_WordOrbitCountAdjacency
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_StringAdjacent
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_FusionFactorStep
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.unfoldedMatrix_apply
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_FusionPacketPerm
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Coxeter_AlternatingLiftProd
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Coxeter_OrdinaryTwistBraid
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_FusionExpandedWordAction
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_FusionExpandedWordPerm
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_SphericalFoldedMatrix
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq _root_.OAI.HarmonicArtin.instDecidableRelStringLabelStringAdjacent
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.labelSplit_apply _root_.OAI.HarmonicArtin.labelSplit_symm_at _root_.OAI.HarmonicArtin.labelSplit_symm_rest _root_.OAI.HarmonicArtin.unfoldedMatrix_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open _root_.Matrix
open scoped _root_.Matrix BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type*} [Fintype S] [LinearOrder S]

omit [LinearOrder S] in
theorem spherical_no_infinite_label (M:CoxeterMatrix S) (J:Set S) (hJ:IsSpherical M J)
    (i j:J) (hij:i≠j) : M i j≠0 := by
  intro hzero
  let C:=((Geometric.cartan M).submatrix ((↑):J → S) ((↑):J → S))
  let x:J → ℝ:=Pi.single i 1+Pi.single j 1
  have hne:x≠0 := by
    intro h
    have hi:=congrFun h i
    simp [x,hij] at hi
  have hpos:0 < x ⬝ᵥ (C *ᵥ x) := by
    simpa only [star_trivial] using (Geometric.spherical_cartan_posDef M J hJ).dotProduct_mulVec_pos hne
  have hval : (i:S)≠j := fun h=>hij (Subtype.ext h)
  have hval' : (j:S)≠i := Ne.symm hval
  have hct : x ⬝ᵥ (C *ᵥ x)=0 := by
    simp [x,C,Matrix.mulVec_add,add_dotProduct,dotProduct_add,Matrix.mulVec_single,
      Geometric.cartan,hval,hval',hzero,← M.symmetric i j]
  rw [hct] at hpos
  exact lt_irrefl _ hpos

theorem spherical_fusion_multiplicity_le_one (M:CoxeterMatrix S) (J:Set S)
    (hJ:IsSpherical M J) (i j:J) (L L':FusionLabel (fusionLabelSize M)) :
    (coxeterFusionEdge M (.inl i) (.inl j)).multiplicity (fusionLabelSize M) L L' ≤ 1 := by
  by_cases hij:i=j
  · subst j
    simp [coxeterFusionEdge_diag,FusionEdge.multiplicity]
  have hval : (i:S)≠j := fun h=>hij (Subtype.ext h)
  have hzero := spherical_no_infinite_label M J hJ i j hij
  simp only [coxeterFusionEdge,dite_eq_right hval,dite_eq_right hzero]
  split_ifs with h2 h3
  · simp [FusionEdge.multiplicity]
  · simp only [FusionEdge.multiplicity]
    split_ifs <;> omega
  · exact factorMultiplicity_le_one (fusionLabelSize M) _ L L'

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_UnfoldedMatrix
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq _root_.OAI.HarmonicArtin.instDecidableRelStringLabelStringAdjacent
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.labelSplit_apply _root_.OAI.HarmonicArtin.labelSplit_symm_at _root_.OAI.HarmonicArtin.labelSplit_symm_rest _root_.OAI.HarmonicArtin.restrictedArtinHom_generator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open _root_.Matrix Geometric CoxeterExchange
open scoped BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type*} [Fintype S] [LinearOrder S]

lemma unfoldedMatrix_cartan (M : CoxeterMatrix S) (J : Set S) (hJ : IsSpherical M J) :
    cartan (unfoldedMatrix M J)=fusionUnfoldedCartan (fusionLabelSize M)
      (fun i j : J => coxeterFusionEdge M (.inl i) (.inl j)) := by
  funext α β
  by_cases he : α=β
  · subst β
    simp [cartan,fusionUnfoldedCartan,coxeterFusionEdge_diag,FusionEdge.multiplicity]
  · have hn := spherical_fusion_multiplicity_le_one M J hJ α.1 β.1 α.2 β.2
    have hp : (coxeterFusionEdge M (.inl α.1) (.inl β.1)).multiplicity
        (fusionLabelSize M) α.2 β.2=0 ∨
      (coxeterFusionEdge M (.inl α.1) (.inl β.1)).multiplicity
        (fusionLabelSize M) α.2 β.2=1 := by omega
    rcases hp with hzero | hone
    · have hm : unfoldedMatrix M J α β=2 := by rw [unfoldedMatrix_apply,ite_eq_right he,ite_eq_left hzero]
      have hc : cartan (unfoldedMatrix M J) α β=0 := by
        simp only [cartan,ite_eq_right he,hm]
        norm_num
      rw [hc]
      simp only [fusionUnfoldedCartan,Matrix.sub_apply,Matrix.diagonal_apply,ite_eq_right he,
        Matrix.of_apply,hzero,Nat.cast_zero,sub_zero]
    · have hm : unfoldedMatrix M J α β=3 := by simp only [unfoldedMatrix_apply,ite_eq_right he,hone] <;> norm_num
      have hc : cartan (unfoldedMatrix M J) α β= -1 := by
        simp only [cartan,ite_eq_right he,hm]
        norm_num [Real.cos_pi_div_three]
      rw [hc]
      simp only [fusionUnfoldedCartan,Matrix.sub_apply,Matrix.diagonal_apply,ite_eq_right he,
        Matrix.of_apply,hone,Nat.cast_one,zero_sub]

theorem unfolded_word_representation (M : CoxeterMatrix S) (J : Set S)
    (hJ : IsSpherical M J) (u : List J) (p : J → ℝ) :
    representation (unfoldedMatrix M J).toCoxeterSystem
      ((unfoldedMatrix M J).toCoxeterSystem.wordProd (fusionExpandedWord (fusionLabelSize M) u))
      (fusionFold (fusionLabelSize M) p)=
      fusionFold (fusionLabelSize M)
        (representation (restrictedMatrix M J).toCoxeterSystem
          ((restrictedMatrix M J).toCoxeterSystem.wordProd u) p) := by
  rw [← rowReflectWord_representation,← rowReflectWord_representation,unfoldedMatrix_cartan M J hJ]
  simpa only [foldedMatrix_cartan] using fusion_word_intertwining (fusionLabelSize M)
    (fun e => le_trans (by norm_num) (fusionLabelSize_ge_four M e))
    (fun i j : J => coxeterFusionEdge M (.inl i) (.inl j))
    (fun i => coxeterFusionEdge_diag M (.inl i)) u p

lemma unfolded_rootRow_fold (M : CoxeterMatrix S) (J : Set S) (hJ : IsSpherical M J)
    (p : J → ℝ) (α : J × FusionLabel (fusionLabelSize M)) :
    rootRow (unfoldedMatrix M J) α (fusionFold (fusionLabelSize M) p)=
      fusionWeight (fusionLabelSize M) α.2*rootRow (restrictedMatrix M J) α.1 p := by
  rw [rootRow_apply,unfoldedMatrix_cartan M J hJ,fusion_intertwining (fusionLabelSize M)
    (fun e => le_trans (by norm_num) (fusionLabelSize_ge_four M e)),foldedMatrix_cartan]
  rfl

lemma unfolded_strict_chamber (M : CoxeterMatrix S) (J : Set S) (hJ : IsSpherical M J) :
    ∃ p : J → ℝ,(∀ i,0 < rootRow (restrictedMatrix M J) i p) ∧
      ∀ α,0 < rootRow (unfoldedMatrix M J) α (fusionFold (fusionLabelSize M) p) := by
  let : Finite (restrictedMatrix M J).Group := restricted_finite M J hJ
  let : Fintype (restrictedMatrix M J).Group := Fintype.ofFinite _
  obtain ⟨p,hp⟩ := exists_strict_chamber (restrictedMatrix M J).toCoxeterSystem
  refine ⟨p,?_,?_⟩
  · intro i
    rw [rootRow_apply,hp]
    norm_num
  · intro α
    rw [unfolded_rootRow_fold M J hJ,rootRow_apply,hp,mul_one]
    exact fusionWeight_pos (fusionLabelSize M)
      (fun e => le_trans (by norm_num) (fusionLabelSize_ge_four M e)) α.2

theorem unfolded_left_ascent_iff (M : CoxeterMatrix S) (J : Set S)
    (hJ : IsSpherical M J) (u : List J) (α : J × FusionLabel (fusionLabelSize M)) :
    let c := (restrictedMatrix M J).toCoxeterSystem
    let d := (unfoldedMatrix M J).toCoxeterSystem
    d.length (d.simple α*d.wordProd (fusionExpandedWord (fusionLabelSize M) u))=
        d.length (d.wordProd (fusionExpandedWord (fusionLabelSize M) u))+1 ↔
      c.length (c.simple α.1*c.wordProd u)=c.length (c.wordProd u)+1 := by
  dsimp only
  obtain ⟨p,hp,hq⟩ := unfolded_strict_chamber M J hJ
  rw [← rootRow_pos_iff_left_ascent _ (fusionFold (fusionLabelSize M) p) hq,
    ← rootRow_pos_iff_left_ascent _ p hp,unfolded_word_representation M J hJ,
    unfolded_rootRow_fold M J hJ]
  exact mul_pos_iff_of_pos_left (fusionWeight_pos (fusionLabelSize M)
    (fun e => le_trans (by norm_num) (fusionLabelSize_ge_four M e)) α.2)

theorem unfolded_word_one (M : CoxeterMatrix S) (J : Set S) (hJ : IsSpherical M J)
    (u : List J) (hu : (restrictedMatrix M J).toCoxeterSystem.wordProd u=1) :
    (unfoldedMatrix M J).toCoxeterSystem.wordProd (fusionExpandedWord (fusionLabelSize M) u)=1 := by
  obtain ⟨p,hp,hq⟩ := unfolded_strict_chamber M J hJ
  apply chamber_stabilizer (unfoldedMatrix M J).toCoxeterSystem
    (fusionFold (fusionLabelSize M) p) hq
  rw [unfolded_word_representation M J hJ,hu,map_one]
  rfl

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_UnfoldedHom
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq _root_.OAI.HarmonicArtin.instDecidableRelStringLabelStringAdjacent
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.labelSplit_apply _root_.OAI.HarmonicArtin.labelSplit_symm_at _root_.OAI.HarmonicArtin.labelSplit_symm_rest _root_.OAI.HarmonicArtin.restrictedArtinHom_generator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open Geometric CoxeterExchange
open scoped BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable

variable {S : Type*} [Fintype S] [LinearOrder S]

noncomputable def unfoldedHom (M : CoxeterMatrix S) (J : Set S) (hJ : IsSpherical M J) :
    (restrictedMatrix M J).Group →* (unfoldedMatrix M J).Group :=
  (restrictedMatrix M J).toCoxeterSystem.lift
    ⟨fun i => (unfoldedMatrix M J).toCoxeterSystem.wordProd
      (fusionExpandedWord (fusionLabelSize M) [i]),by
      intro i j
      let c := (restrictedMatrix M J).toCoxeterSystem
      let d := (unfoldedMatrix M J).toCoxeterSystem
      have hword : c.wordProd ((List.replicate ((restrictedMatrix M J) i j) [i,j]).flatten)=1 := by
        rw [wordProd_flatten_replicate]
        simpa only [CoxeterSystem.wordProd_cons,CoxeterSystem.wordProd_nil,mul_one]
          using c.simple_mul_simple_pow i j
      have hu := unfolded_word_one M J hJ _ hword
      rw [fusionExpandedWord_flatten_replicate,wordProd_flatten_replicate] at hu
      have he : fusionExpandedWord (fusionLabelSize M) [i,j]=
          fusionExpandedWord (fusionLabelSize M) [i]++fusionExpandedWord (fusionLabelSize M) [j] :=
        fusionExpandedWord_append _ [i] [j]
      rw [he,d.wordProd_append] at hu
      exact hu⟩

@[simp] lemma unfoldedHom_simple (M : CoxeterMatrix S) (J : Set S) (hJ : IsSpherical M J) (i : J) :
    unfoldedHom M J hJ ((restrictedMatrix M J).toCoxeterSystem.simple i)=
      (unfoldedMatrix M J).toCoxeterSystem.wordProd (fusionExpandedWord (fusionLabelSize M) [i]) :=
  (restrictedMatrix M J).toCoxeterSystem.lift_apply_simple _ i

lemma unfoldedHom_wordProd (M : CoxeterMatrix S) (J : Set S) (hJ : IsSpherical M J) (u : List J) :
    unfoldedHom M J hJ ((restrictedMatrix M J).toCoxeterSystem.wordProd u)=
      (unfoldedMatrix M J).toCoxeterSystem.wordProd (fusionExpandedWord (fusionLabelSize M) u) := by
  induction u with
  | nil => simp [fusionExpandedWord]
  | cons i u ih =>
    rw [CoxeterSystem.wordProd_cons,map_mul,unfoldedHom_simple,ih]
    change _=(unfoldedMatrix M J).toCoxeterSystem.wordProd
      (fusionExpandedWord (fusionLabelSize M) ([i]++u))
    rw [fusionExpandedWord_append,CoxeterSystem.wordProd_append]

theorem unfolded_word_eq (M : CoxeterMatrix S) (J : Set S) (hJ : IsSpherical M J)
    (u v : List J) (h : (restrictedMatrix M J).toCoxeterSystem.wordProd u=
      (restrictedMatrix M J).toCoxeterSystem.wordProd v) :
    (unfoldedMatrix M J).toCoxeterSystem.wordProd (fusionExpandedWord (fusionLabelSize M) u)=
      (unfoldedMatrix M J).toCoxeterSystem.wordProd (fusionExpandedWord (fusionLabelSize M) v) := by
  rw [← unfoldedHom_wordProd M J hJ,← unfoldedHom_wordProd M J hJ,h]

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_UnfoldedColorOrthogonal
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq _root_.OAI.HarmonicArtin.instDecidableRelStringLabelStringAdjacent
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.labelSplit_apply _root_.OAI.HarmonicArtin.labelSplit_symm_at _root_.OAI.HarmonicArtin.labelSplit_symm_rest _root_.OAI.HarmonicArtin.restrictedArtinHom_generator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open _root_.Matrix Geometric CoxeterExchange
open scoped BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type*} [Fintype S] [LinearOrder S]

lemma unfolded_color_orthogonal (M : CoxeterMatrix S) (J : Set S) (hJ : IsSpherical M J)
    (α β : J × FusionLabel (fusionLabelSize M)) (hcolor : α.1=β.1) (hne : α≠β) :
    cartan (unfoldedMatrix M J) α β=0 := by
  rw [unfoldedMatrix_cartan M J hJ]
  simp [fusionUnfoldedCartan,hne,hcolor,coxeterFusionEdge_diag,
    FusionEdge.multiplicity]

theorem unfolded_reducedWord (M : CoxeterMatrix S) (J : Set S) (hJ : IsSpherical M J)
    (u : List J) (hu : (restrictedMatrix M J).toCoxeterSystem.IsReduced u) :
    (unfoldedMatrix M J).toCoxeterSystem.IsReduced (fusionExpandedWord (fusionLabelSize M) u) := by
  let c := (restrictedMatrix M J).toCoxeterSystem
  let d := (unfoldedMatrix M J).toCoxeterSystem
  obtain ⟨p,hp,hq⟩ := unfolded_strict_chamber M J hJ
  induction u with
  | nil => simp [fusionExpandedWord,CoxeterSystem.IsReduced]
  | cons i u ih =>
    have hru : c.IsReduced u := by simpa only [List.drop_succ_cons,List.drop_zero] using hu.drop 1
    have heu := ih hru
    let block := (Finset.univ : Finset (FusionLabel (fusionLabelSize M))).toList.map (fun L => (i,L))
    have hn : block.Nodup := List.Nodup.map (fun a b h => Prod.mk.inj h |>.2) (Finset.nodup_toList _)
    have hcolor : ∀ α∈block,α.1=i := by
      intro α hα
      obtain ⟨L,_,rfl⟩ := List.mem_map.mp hα
      rfl
    have horth : ∀ α∈block,∀ β∈block,α≠β → cartan (unfoldedMatrix M J) α β=0 := by
      intro α hα β hβ hne
      exact unfolded_color_orthogonal M J hJ α β ((hcolor α hα).trans (hcolor β hβ).symm) hne
    have ha : c.length (c.simple i*c.wordProd u)=c.length (c.wordProd u)+1 := by
      simpa only [CoxeterSystem.wordProd_cons,List.length_cons,← hru.eq] using hu.eq
    have has : ∀ α∈block,d.length (d.simple α*d.wordProd (fusionExpandedWord (fusionLabelSize M) u))=
        d.length (d.wordProd (fusionExpandedWord (fusionLabelSize M) u))+1 := by
      intro α hα
      apply (unfolded_left_ascent_iff M J hJ u α).mpr
      rw [hcolor α hα]
      exact ha
    have hb := orthogonal_ascent_block d (fusionFold (fusionLabelSize M) p) hq block hn horth
      (d.wordProd (fusionExpandedWord (fusionLabelSize M) u)) has
    change d.length (d.wordProd (block++fusionExpandedWord (fusionLabelSize M) u))=
      (block++fusionExpandedWord (fusionLabelSize M) u).length
    rw [d.wordProd_append,hb,List.length_append,heu.eq]

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_UnfoldedInclusion
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instDecidableRelStringLabelStringAdjacent
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.labelSplit_apply _root_.OAI.HarmonicArtin.labelSplit_symm_at _root_.OAI.HarmonicArtin.labelSplit_symm_rest
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

abbrev unfoldedInclusion (M : CoxeterMatrix S) (J : Set S)
    (α : J × FusionLabel (fusionLabelSize M)) : FusionVertex (V:=S⊕Unit) (fusionLabelSize M) :=
  (Sum.inl α.1.val,α.2)

omit [Fintype S] in
lemma unfoldedInclusion_injective (M : CoxeterMatrix S) (J : Set S) :
    Function.Injective (unfoldedInclusion M J) := by
  intro α β h
  exact Prod.ext (Subtype.ext (Sum.inl.inj (Prod.mk.inj h).1)) (Prod.mk.inj h).2

variable (M : CoxeterMatrix S)
local notation "Q" => fusionQuiver (fusionLabelSize M) (coxeterFusionEdge M) (coxeterFusionEdge_symm M)

lemma unfolded_ordinaryMatrix (J : Set S) (hJ : IsSpherical M J)
    (α β : J × FusionLabel (fusionLabelSize M)) :
    ordinaryCoxeterMatrix Q (unfoldedInclusion M J α) (unfoldedInclusion M J β)=
      unfoldedMatrix M J α β := by
  by_cases he : α=β
  · subst β
    simp
  · have hi := fun hh => he (unfoldedInclusion_injective M J hh)
    have hn := spherical_fusion_multiplicity_le_one M J hJ α.1 β.1 α.2 β.2
    have hp : (coxeterFusionEdge M (.inl α.1) (.inl β.1)).multiplicity
        (fusionLabelSize M) α.2 β.2=0 ∨
      (coxeterFusionEdge M (.inl α.1) (.inl β.1)).multiplicity
        (fusionLabelSize M) α.2 β.2=1 := by omega
    rcases hp with hz|ho
    · have horth := fusionQuiver_orthogonal (fusionLabelSize M) (coxeterFusionEdge M)
        (coxeterFusionEdge_symm M) (unfoldedInclusion M J α) (unfoldedInclusion M J β) hi hz
      rw [ordinaryCoxeterMatrix_orthogonal Q horth,unfoldedMatrix_apply,ite_eq_right he,ite_eq_left hz]
    · let edge := fusionQuiver_simpleEdge (fusionLabelSize M) (coxeterFusionEdge M)
        (coxeterFusionEdge_symm M) (unfoldedInclusion M J α) (unfoldedInclusion M J β) hi ho
      rw [ordinaryCoxeterMatrix_adjacent Q edge,unfoldedMatrix_apply,ite_eq_right he,ho]
      norm_num

lemma fusionExpandedWord_map {E V T : Type*} [Fintype E] [DecidableEq E]
    (m : E → ℕ) (f : V → T) (u : List V) :
    fusionExpandedWord m (u.map f)=(fusionExpandedWord m u).map (fun α => (f α.1,α.2)) := by
  induction u with
  | nil => rfl
  | cons i u ih =>
    simp only [List.map_cons,fusionExpandedWord,List.flatMap_cons,List.map_append,List.map_map]
    congr 1

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_SphericalPacketWordProperty
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_ArtinAction
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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

lemma sourceArtinAction_generator (s : S) :
    sourceArtinAction M (K:=K) (generator M s)=T (Sum.inl s) :=
  PresentedGroup.toGroup.of _

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_FusionPacketOrbit
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_FusionOrbitModel
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_FusionOrbitMultiplicity
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_FusionColorRegion
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_DimensionPosMultiplicityPos
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_Harmonic
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

noncomputable def sourceCosetRepresentative (P:Deligne M) : Artin M :=
  P.property.2.choose

omit [Fintype S] [LinearOrder S] in
lemma sourceCosetRepresentative_spec (P:Deligne M) :
    P.val.2=rightCoset M P.val.1 (sourceCosetRepresentative M P) :=
  P.property.2.choose_spec

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_Coset
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

noncomputable def sourceCoset (T:Set S) (hT:IsSpherical M T) (x:Artin M) : Deligne M :=
  ⟨(T,rightCoset M T x),hT,⟨x,rfl⟩⟩

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_IsolatedBoundaryAbsent
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_IsolatedIterationData
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

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_PointedFamily
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ParabolicIntersections.artinExponent_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.artinMap_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.mem_relativeStabilizer _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeArtinHom_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visualFromArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visualToArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visual_smul_vertex _root_.OAI.HarmonicArtin.artinCoxeter_generator _root_.OAI.HarmonicArtin.positiveLift_one _root_.OAI.HarmonicArtin.positiveToArtin_generator _root_.OAI.HarmonicArtin.positiveToArtin_word _root_.OAI.HarmonicArtin.restrictedArtinHom_generator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The existing categorical action with an arbitrary original color as frame. -/

namespace HarmonicArtin.ParabolicIntersections

open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
attribute [local instance] Classical.decEq Classical.propDecidable

variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "hd" => coxeterFusionEdge_symm M
local notation "diag" => coxeterFusionEdge_diag M
local notation "Q" => fusionQuiver m d hd

abbrev PointedLabel := FusionLabel m
abbrev PointedClass := FiniteHomotopyClass Q (K := ℂ)
abbrev PointedFamilySpace := PointedLabel M → PointedClass M

noncomputable def pointedAction : Artin M →* Equiv.Perm (PointedClass M) :=
  sourceArtinAction M (K := ℂ)

noncomputable def pointedInitial (f : S) : PointedFamilySpace M :=
  fun L => initialClass Q (.inl f, L)

noncomputable def pointedFamily (f : S) (x : Artin M) : PointedFamilySpace M :=
  fun L => pointedAction M x (pointedInitial M f L)

@[simp] theorem pointedAction_generator (s : S) :
    pointedAction M (generator M s) = fusionPacketPerm m d hd diag (.inl s) :=
  sourceArtinAction_generator M s

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_PointedMultiplicity
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Layer counts of the pointed categorical family, at every integer level. -/

namespace HarmonicArtin.ParabolicIntersections

open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
attribute [local instance] Classical.decEq Classical.propDecidable

variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "hd" => coxeterFusionEdge_symm M
local notation "hm" => fusionLabelSize_ge_two M
local notation "Q" => fusionQuiver m d hd

noncomputable def pointedMultiplicity (f : S) (x : Artin M) (k : ℤ) (v : S ⊕ Unit) : ℝ :=
  fusionFamilyMultiplicity m d hd hm (pointedFamily M f x) k v

lemma pointedMultiplicity_sum (f : S) (x : Artin M) (k : ℤ) (v : S ⊕ Unit) :
    pointedMultiplicity M f x k v =
      (∑ L, fusionWeight m L * (classLevelArray Q (pointedFamily M f x L)
        ((v, fusionZeroLabel m hm), k) : ℝ)) / fusionWeight m (fusionZeroLabel m hm) := by
  unfold pointedMultiplicity fusionFamilyMultiplicity
  simp only [classTotalVector_layer_apply]

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_PointedProfile
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Harmonic profiles on actual parabolic cosets for a relative frame. -/

namespace HarmonicArtin.ParabolicIntersections

open _root_.Matrix _root_.OAI.Matrix
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S) (f : S)

noncomputable def pointedHarmonicAt (T : Set S) (x : Artin M) (k : ℤ) : S ⊕ Unit → ℝ :=
  harmonicExtension (framedCartan M) (Sum.inl '' T) (pointedMultiplicity M f x k)

noncomputable def pointedCosetVector (P : Deligne M) (k : ℤ) : S ⊕ Unit → ℝ :=
  pointedHarmonicAt M f P.val.1 (sourceCosetRepresentative M P) k

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_SphericalCochain
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ordinary cochain bound in Lemma 7.2 of paper 082-03. -/
namespace HarmonicArtin.ParabolicIntersections
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A : Type} {K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

/-- Unlike `ClassTestUpper`, this bounds ordinary cochain degree, uniformly
in total degree. -/
def ClassTestCochainUpper (x : FiniteHomotopyClass Q (K := K)) (U : Set V) (m : ℤ) : Prop :=
  ∀ α ∈ U, ∀ l c : ℤ, m < c → ClassTestExact Q α l c x

end HarmonicArtin.ParabolicIntersections

end OAI
end


