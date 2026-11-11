-- Prove2me | Definitions.Def_OAIQ236Ap012
-- name    : OAIQ236Ap012
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T20:01:21.930917+00:00
-- url     : https://prove2.me/theorems/fdb11253-efc2-424c-91b9-a6ec629fd5b8
-- title:
--   Definitions bundle OAIQ236Ap012 of the split of OpenAI, Parabolic intersections in Artin groups
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.HarmonicArtin.ParabolicIntersections.unconditional_arbitrary_intersections`, `OAI.HarmonicArtin.ParabolicIntersections.unconditional_nonclique_dynamics`, `OAI.HarmonicArtin.ParabolicIntersections.unconditional_parabolic_closure` and `OAI.HarmonicArtin.ParabolicIntersections.unconditional_parabolic_intersections`, carved from OpenAI's openai/math development (OpenAI, *Parabolic intersections in Artin groups*, OpenAI Math Release, September 23, 2026, result family 254, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 34 declarations of OpenAI's Lean: 11 definitions and 23 theorems. The definitions and types are `OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.expressionAction`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.frameModel`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.unfoldedArtinAction`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.unfoldedFrame`, `OAI.HarmonicArtin.SourceCosetOrbit`, `OAI.HarmonicArtin.fusionOrbitColorMultiplicity`, `OAI.HarmonicArtin.fusionOrdinaryAction`, `OAI.HarmonicArtin.sourceBottomWord`, `OAI.HarmonicArtin.sourceConvexModel`, `OAI.HarmonicArtin.sourceConvexWord`, `OAI.HarmonicArtin.sourcePositiveWord`.
--
--   **Sources.** They come from these modules of lean/OAI/Topology, in whole or in part: `ArtinGroups_Complexes_ColorSupport`, `ArtinGroups_Complexes_Initial`, `ArtinGroups_Complexes_LowerTruncation`, `ArtinGroups_Complexes_MinimalModel`, `ArtinGroups_Complexes_OutsideCap`, `ArtinGroups_Complexes_PositiveWordLowerBound`, `ArtinGroups_Complexes_ScalarKernel`, `ArtinGroups_Complexes_Shift`, `ArtinGroups_Complexes_UnfoldedPresentation`, `ArtinGroups_Geometry_ConvexWord`, `ArtinGroups_Harmonic_CanonicalFusionLow`, `ArtinGroups_Harmonic_CanonicalFusionLowExpansion`, `ArtinGroups_Harmonic_CanonicalFusionMultiplicity`, `ArtinGroups_Harmonic_CosetOrbit`, `ArtinGroups_Harmonic_FusionColorRegion`, `ArtinGroups_Harmonic_FusionQuiverSimpleEdge`, `ArtinGroups_Harmonic_FusionZeroLabel`, `ArtinGroups_Harmonic_LayerExpression`, `ArtinGroups_Harmonic_PositiveWord`, `ArtinGroups_Harmonic_UnfoldedFullWordMem`, `ArtinGroups_Harmonic_UnfoldedInclusion`.
--
--   **Imports.** It imports the published bundle `Def_ArtinParabolicIntersections`; the bundles `OAIQ236Ap008` and `OAIQ236Ap009` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ236Ap013`; the statements `OAI_HarmonicArtin_fusionOrbitColor_subobject_separation` and `OAI.HarmonicArtin.fusionOrbitColor_subobject_separation_s236`; the proofs of `OAI_HarmonicArtin_ParabolicIntersections_pointedProbe_raise_lower`, `OAI.HarmonicArtin.ParabolicIntersections.pointedProbe_raise_lower_s236`, `OAI_HarmonicArtin_fusionOrbitColor_subobject_separation` and `OAI.HarmonicArtin.fusionOrbitColor_subobject_separation_s236`.
-- source:
--   OpenAI, Parabolic intersections in Artin groups, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 254; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Parabolic-intersections-in-Artin-groups-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Topology at commit adc7f12

import Mathlib
import Definitions.Def_ArtinParabolicIntersections
import Definitions.Def_OAIQ236Ap008
import Definitions.Def_OAIQ236Ap009

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_UnfoldedPresentation
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_Initial
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

noncomputable def unfoldedFrame (hn : ∀ a, Q.source a ≠ Q.target a)
    (M : CoxeterMatrix V) (hM : UnfoldedPresentation Q M) (x : Artin M) (α : V) :
    FiniteHomotopyClass Q (K := K) :=
  unfoldedArtinAction Q hn M hM x (initialClass Q α)

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
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_Shift
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_PositiveWordLowerBound
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

lemma positiveWord_outside_cap (w:List V) (x:FiniteHomotopyClass Q (K:=K))
    (U:Set V) (d:ℤ) (hw:∀ s∈w,s∈U) (hx:ClassOutsideCap Q x U d) :
    ClassOutsideCap Q (positiveWordAction Q w x) U d := by
  induction w with
  | nil => exact hx
  | cons α w ih =>
    exact classPositiveTwist_outside_cap Q _ U d α (hw α (by simp))
      (ih (fun s hs=>hw s (List.mem_cons_of_mem _ hs)))

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_ColorSupport
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_LayerExpression
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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

end ReversibleQuiver.StringFunctor

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_CanonicalFusionLow
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

lemma canonicalFusionLow_eq_ordinary (w:List V) (z:List (FusionVertex (V:=V) m))
    (hz:∀ x:FiniteHomotopyClass Q (K:=K),positiveWordAction Q z x=P (w.map fun s=>(s,true)) x)
    (q:ℤ) (x:FiniteHomotopyClass Q (K:=K)) :
    canonicalFusionLow m d hd hdiag w q x=canonicalWordLow Q z q x := by
  have hinv:(P (w.map fun s=>(s,true))).symm x=inverseWordAction Q z x := by
    apply (P (w.map fun s=>(s,true))).injective
    rw [Equiv.apply_symm_apply,← hz,positive_inverseWord Q hn]
  dsimp [canonicalFusionLow,canonicalWordLow]
  rw [hinv,hz]

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_FusionQuiverSimpleEdge
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.instDecidableRelStringLabelStringAdjacent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin

variable {E V : Type*} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m : E → ℕ) (d : V → V → FusionEdge E) (hd : ∀ s t, d s t = d t s)

noncomputable def fusionOrdinaryAction {K : Type*} [Field K]
    (hdiag : ∀ s, d s s = .units 0) :
    Artin (fusionOrdinaryMatrix m d hd) →*
      Equiv.Perm (ReversibleQuiver.Zigzag.BasedComplex.FiniteHomotopyClass
        (fusionQuiver m d hd) (K := K)) :=
  ReversibleQuiver.Zigzag.BasedComplex.unfoldedArtinAction (fusionQuiver m d hd)
    (fusionQuiver_no_loops m d hd hdiag) (fusionOrdinaryMatrix m d hd)
    (fusionOrdinaryPresentation m d hd)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_CanonicalFusionMultiplicity
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
local notation "O" => fusionPacketOrbit m d hd hdiag

lemma fusionOrbitWeightedVector_class (z:List (V×Bool)) (s:V) (q:ℤ) :
    fusionOrbitWeightedVector m d hd hdiag z s q=
      ∑ L,fusionWeight m L • classTotalVector Q (classLayer Q q (O z s L)) := by
  simp only [fusionOrbitWeightedVector,classTotalVector_layer]
  rfl

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

lemma fusionFamilyMultiplicity_orbit (hdiag:∀ s,d s s=.units 0)
    (z:List (V×Bool)) (s:V) (q:ℤ) :
    fusionFamilyMultiplicity m d hd hm (fusionPacketOrbit m d hd hdiag z s) q=
      fusionOrbitMultiplicity m d hd hdiag hm z s q := by
  funext v
  have h:=congrFun (fusionOrbitWeightedVector_eq m d hd hdiag hm z s q) (v,fusionZeroLabel m hm)
  rw [fusionOrbitWeightedVector_class] at h
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,fusionFold] at h
  unfold fusionFamilyMultiplicity
  rw [h]
  exact mul_div_cancel_left₀ _ (ne_of_gt (fusionWeight_pos m hm _))

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_UnfoldedInclusion
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.instDecidableRelStringLabelStringAdjacent
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_CanonicalFusionLowExpansion
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_UnfoldedFullWordMem
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex CoxeterExchange

attribute [local instance] Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] {K : Type*} [Field K]
  (M : CoxeterMatrix S)
local notation "Q" => fusionQuiver (fusionLabelSize M) (coxeterFusionEdge M) (coxeterFusionEdge_symm M)
local notation "C" => canonicalFusionLow (fusionLabelSize M) (coxeterFusionEdge M)
  (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M) (K:=K)

lemma sourceCanonicalLow_eq (J : Set S) (u : List J) (q : ℤ)
    (x : FiniteHomotopyClass Q (K:=K)) :
    C (u.map fun j : J => (Sum.inl (j:S) : S⊕Unit)) q x =
      canonicalWordLow Q (fusionExpandedWord (fusionLabelSize M)
        (u.map fun j : J => (Sum.inl (j:S) : S⊕Unit))) q x := by
  convert canonicalFusionLow_eq_expansion (fusionLabelSize M) (coxeterFusionEdge M)
    (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M)
    (u.map fun j : J => (Sum.inl (j:S) : S⊕Unit)) q x using 1
  all_goals try with_reducible_and_instances rfl
  exact congrArg (fun decEq : DecidableEq (FusionQuiverArrow (fusionLabelSize M) (coxeterFusionEdge M)) =>
    @canonicalWordLow _ _ K Q _ _ _ _ decEq (fusionExpandedWord (fusionLabelSize M)
      (u.map fun j : J => (Sum.inl (j:S) : S⊕Unit))) q x) (Subsingleton.elim _ _)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Geometry_ConvexWord
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
local notation "Q" => fusionQuiver m d hd
local notation "O" => fusionPacketOrbit m d hd hdiag

noncomputable def sourceConvexWord (J:Set S) (w:(restrictedMatrix M J).Group) : List J :=
  reducedExpression (restrictedMatrix M J) w⁻¹

omit [Fintype S] [LinearOrder S] in
lemma sourceConvexWord_reduced (J:Set S) (w:(restrictedMatrix M J).Group) :
    (restrictedMatrix M J).toCoxeterSystem.IsReduced (sourceConvexWord M J w) :=
  reducedExpression_reduced _ _

noncomputable def sourceConvexModel (J:Set S) (z:List ((S⊕Unit)×Bool))
    (s:S⊕Unit) (q:ℤ) (w:(restrictedMatrix M J).Group) (L:FusionLabel m) : FiniteModel Q (K:=ℂ) :=
  minimalClassModel Q (canonicalFusionLow m d hd hdiag
    ((sourceConvexWord M J w).map (sourceRootInclusion J)) q (classLayer Q q (O z s L)))

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

noncomputable def fusionOrbitColorMultiplicity (hm:∀ e,2 ≤ m e)
    (w:List (V × Bool)) (s:V) (q:ℤ) (U:Set V) : V → ℝ :=
  fun v=>if v∈U then fusionOrbitMultiplicity m d hd hdiag hm w s q v else 0

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_CosetOrbit
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
local notation "aw" => sourceArtinAction M (K:=ℂ)

def SourceCosetOrbit (J:Set S) (z₀:List ((S⊕Unit)×Bool)) (s:S⊕Unit)
    (z:List ((S⊕Unit)×Bool)) : Prop :=
  ∃ g∈artinParabolic M J,∀ L,O z s L=aw g (O z₀ s L)

lemma sourceCosetOrbit_move (J:Set S) (z₀:List ((S⊕Unit)×Bool)) (s:S⊕Unit)
    (z:List ((S⊕Unit)×Bool)) (hz:SourceCosetOrbit M J z₀ s z) (j:J) :
    SourceCosetOrbit M J z₀ s ((.inl j,true)::z) := by
  obtain ⟨g,hg,he⟩:=hz
  refine ⟨generator M j*g,(artinParabolic M J).mul_mem
    (Subgroup.subset_closure ⟨j,j.property,rfl⟩) hg,fun L=>?_⟩
  change fusionPacketPerm m d hd hdiag (.inl j) (O z s L)=_
  rw [he,map_mul,sourceArtinAction_generator]
  rfl

lemma sourceCosetOrbit_strict (J:Set S) (z₀:List ((S⊕Unit)×Bool)) (s:S⊕Unit)
    (q:ℤ) (c:S⊕Unit→ℝ)
    (huniv:∀ g∈artinParabolic M J,
      (∀ L,ClassCapOn Q (aw g (O z₀ s L))
        (closedNeighborhood Q (Set.range (unfoldedInclusion M J))) q)→
      ∀ j:J,c (.inl (j:S))<fusionFamilyMultiplicity m d hd hm
        (fun L=>aw g (O z₀ s L)) q (.inl (j:S)))
    (z:List ((S⊕Unit)×Bool)) (hz:SourceCosetOrbit M J z₀ s z) :
    ∀ g∈artinParabolic M J,
      (∀ L,ClassCapOn Q (aw g (O z s L))
        (closedNeighborhood Q (Set.range (unfoldedInclusion M J))) q)→
      ∀ j:J,c (.inl (j:S))<fusionFamilyMultiplicity m d hd hm
        (fun L=>aw g (O z s L)) q (.inl (j:S)) := by
  obtain ⟨a,ha,he⟩:=hz
  intro g hg hc j
  have hf:(fun L=>aw g (O z s L))=(fun L=>aw (g*a) (O z₀ s L)) := by
    funext L
    rw [he,map_mul]
    rfl
  rw [hf]
  apply huniv (g*a) ((artinParabolic M J).mul_mem hg ha) _ j
  intro label
  rw [← congrFun hf label]
  exact hc label

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_PositiveWord
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open CoxeterExchange Geometric

attribute [local instance] Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] {K:Type*} [Field K]
  (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "Q" => fusionQuiver m d (coxeterFusionEdge_symm M)
local notation "aw" => sourceArtinAction M (K:=K)

noncomputable def sourcePositiveWord (J:Set S) (w:List J)
    (x:FiniteHomotopyClass Q (K:=K)) : FiniteHomotopyClass Q (K:=K) :=
  aw (wordArtin M (w.map Subtype.val)) x

noncomputable def sourceBottomWord (J:Set S) (q:ℤ) (w:List J)
    (x:FiniteHomotopyClass Q (K:=K)) : FiniteHomotopyClass Q (K:=K) :=
  classLayer Q q (sourcePositiveWord M J w x)

end HarmonicArtin

end OAI
end


