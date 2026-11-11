-- Prove2me | Definitions.Def_OAIQ236Ap011
-- name    : OAIQ236Ap011
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T20:09:40.538339+00:00
-- url     : https://prove2.me/theorems/8af23b30-dc7d-40ad-8bcb-486e7d5ff9e7
-- title:
--   Definitions bundle OAIQ236Ap011 of the split of OpenAI, Parabolic intersections in Artin groups
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.HarmonicArtin.ParabolicIntersections.unconditional_arbitrary_intersections`, `OAI.HarmonicArtin.ParabolicIntersections.unconditional_nonclique_dynamics`, `OAI.HarmonicArtin.ParabolicIntersections.unconditional_parabolic_closure` and `OAI.HarmonicArtin.ParabolicIntersections.unconditional_parabolic_intersections`, carved from OpenAI's openai/math development (OpenAI, *Parabolic intersections in Artin groups*, OpenAI Math Release, September 23, 2026, result family 254, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 311 declarations of OpenAI's Lean: 98 definitions, 6 inductive types or structures, 3 instances and 204 theorems. The definitions and types are `OAI.HarmonicArtin.ParabolicIntersections.ExteriorCutoff`, `OAI.HarmonicArtin.ParabolicIntersections.PointedCandidate`, `OAI.HarmonicArtin.ParabolicIntersections.PointedCappedCandidate`, `OAI.HarmonicArtin.ParabolicIntersections.PointedResidue`, `OAI.HarmonicArtin.ParabolicIntersections.PointedResidueAllowed`, `OAI.HarmonicArtin.ParabolicIntersections.PointedResidueEarlier`, `OAI.HarmonicArtin.ParabolicIntersections.PointedResidueEarlierLower`, `OAI.HarmonicArtin.ParabolicIntersections.PointedResidueEarlierUpper`, `OAI.HarmonicArtin.ParabolicIntersections.PublishedFoldingGcd`, `OAI.HarmonicArtin.ParabolicIntersections.PublishedMeshInput`, `OAI.HarmonicArtin.ParabolicIntersections.PublishedSphericalAlgebraInputs`, `OAI.HarmonicArtin.ParabolicIntersections.PublishedSphericalInputs`, `OAI.HarmonicArtin.ParabolicIntersections.RelativeAllEligibleLower`, `OAI.HarmonicArtin.ParabolicIntersections.RelativeBlockOccurs`, `OAI.HarmonicArtin.ParabolicIntersections.RelativeClass`, `OAI.HarmonicArtin.ParabolicIntersections.RelativeDescendingLower`, `OAI.HarmonicArtin.ParabolicIntersections.RelativeDescendingUpper`, `OAI.HarmonicArtin.ParabolicIntersections.RelativeEligible`, `OAI.HarmonicArtin.ParabolicIntersections.RelativeEligibleWithin`, `OAI.HarmonicArtin.ParabolicIntersections.RelativeFamilySpace`, `OAI.HarmonicArtin.ParabolicIntersections.RelativeLabel`, `OAI.HarmonicArtin.ParabolicIntersections.RelativeMinimum`, `OAI.HarmonicArtin.ParabolicIntersections.RelativePath`, `OAI.HarmonicArtin.ParabolicIntersections.RelativeStrictLower`, `OAI.HarmonicArtin.ParabolicIntersections.RelativeVertex`, `OAI.HarmonicArtin.ParabolicIntersections.VanDerLekRelativeEmbedding`, `OAI.HarmonicArtin.ParabolicIntersections.deligneRightTranslate`, `OAI.HarmonicArtin.ParabolicIntersections.foldedPositiveHom`, `OAI.HarmonicArtin.ParabolicIntersections.instMulActionArtinVisualVertex_2`, `OAI.HarmonicArtin.ParabolicIntersections.instMulActionArtinVisualVertex_4`, `OAI.HarmonicArtin.ParabolicIntersections.instMulActionArtinVisualVertex_5`, `OAI.HarmonicArtin.ParabolicIntersections.parabolicState`, `OAI.HarmonicArtin.ParabolicIntersections.pointedCosetSum`, `OAI.HarmonicArtin.ParabolicIntersections.pointedProfile`, `OAI.HarmonicArtin.ParabolicIntersections.pointedResidueActive`, `OAI.HarmonicArtin.ParabolicIntersections.pointedResidueClose`, `OAI.HarmonicArtin.ParabolicIntersections.pointedResidueEarlierLowerIso`, `OAI.HarmonicArtin.ParabolicIntersections.pointedResidueEarlierUpperIso`, `OAI.HarmonicArtin.ParabolicIntersections.pointedResidueHeight`, `OAI.HarmonicArtin.ParabolicIntersections.pointedResidueKey` and 64 more.
--
--   **Sources.** They come from these modules of lean/OAI/Topology, in whole or in part: `ArtinGroups_Complexes_CanonicalWordLow`, `ArtinGroups_Complexes_LowerTruncation`, `ArtinGroups_Complexes_MinimalModelEquivalence`, `ArtinGroups_Complexes_PacketPermExterior`, `ArtinGroups_Complexes_PositiveTopDivisor`, `ArtinGroups_Complexes_PositiveWordActionOrthogonal`, `ArtinGroups_Coxeter_ParabolicProductMap`, `ArtinGroups_Coxeter_PositiveBraidRel`, `ArtinGroups_Functors_ComplexLowerTruncation`, `ArtinGroups_Functors_ComplexPureLayer`, `ArtinGroups_Functors_LayerIndexEquiv`, `ArtinGroups_Functors_TruncationIndexEquiv`, `ArtinGroups_Harmonic_Candidate`, `ArtinGroups_Harmonic_Coset`, `ArtinGroups_Harmonic_CosetBelow`, `ArtinGroups_Harmonic_CosetProfile`, `ArtinGroups_Harmonic_CosetSum`, `ArtinGroups_Harmonic_FrameFamily`, `ArtinGroups_Harmonic_FusionSignedPacketExterior`, `ArtinGroups_Harmonic_Harmonic`, `ArtinGroups_Harmonic_InitialProbe`, `ArtinGroups_Harmonic_MapPacket`, `ArtinGroups_Harmonic_MultiplicitySum`, `ArtinGroups_Harmonic_ProbeCoreInclusion`, `ArtinGroups_Harmonic_ProbeFixedOutside`, `ArtinGroups_Harmonic_ProbePacket`, `ArtinGroups_Harmonic_ProbePacketExterior`, `ArtinGroups_Harmonic_ProbePositiveWord`, `ArtinGroups_Harmonic_ProbePositiveWordAppend`, `ArtinGroups_Harmonic_ProbePositiveWordInitial`, `ArtinGroups_Harmonic_ProbePositiveWordLeft`, `ArtinGroups_Harmonic_SignedLetter`, `ArtinGroups_Harmonic_TieCode`, `ArtinGroups_Harmonic_UnfoldedHom`, `ArtinGroups_Harmonic_UnfoldedInclusion`, `ArtinGroups_Harmonic_UnfoldedInclusionRange`, `ArtinGroups_ParabolicIntersections_ConditionalMain`, `ArtinGroups_ParabolicIntersections_FoldingGcdInput`, `ArtinGroups_ParabolicIntersections_FoldingPositive`, `ArtinGroups_ParabolicIntersections_MainIntersection`, `ArtinGroups_ParabolicIntersections_PointedCandidate`, `ArtinGroups_ParabolicIntersections_PointedCappedCandidate`, `ArtinGroups_ParabolicIntersections_PointedCosetExteriorCap`, `ArtinGroups_ParabolicIntersections_PointedCosetGeometry`, `ArtinGroups_ParabolicIntersections_PointedCosetProduct`, `ArtinGroups_ParabolicIntersections_PointedFamily`, `ArtinGroups_ParabolicIntersections_PointedInitialCounts`, `ArtinGroups_ParabolicIntersections_PointedMultiplicity`, `ArtinGroups_ParabolicIntersections_PointedProfile`, `ArtinGroups_ParabolicIntersections_PointedResidueActive`, `ArtinGroups_ParabolicIntersections_PointedResidueAllowed`, `ArtinGroups_ParabolicIntersections_PointedResidueEarlierLower`, `ArtinGroups_ParabolicIntersections_PointedResidueEarlierLowerIso`, `ArtinGroups_ParabolicIntersections_PointedResidueHeightZero`, `ArtinGroups_ParabolicIntersections_PointedResidueRank`, `ArtinGroups_ParabolicIntersections_PointedResidueZeroLower`, `ArtinGroups_ParabolicIntersections_PointedWeighted`, `ArtinGroups_ParabolicIntersections_ProperParabolicMalnormal`, `ArtinGroups_ParabolicIntersections_ReducedInputsMain`, `ArtinGroups_ParabolicIntersections_RelativeActive`, `ArtinGroups_ParabolicIntersections_RelativeAllEligible`, `ArtinGroups_ParabolicIntersections_RelativeEligible`, `ArtinGroups_ParabolicIntersections_RelativeEligibleFactor`, `ArtinGroups_ParabolicIntersections_RelativeEligibleWithin`, `ArtinGroups_ParabolicIntersections_RelativeFamily`, `ArtinGroups_ParabolicIntersections_RelativeHeight`, `ArtinGroups_ParabolicIntersections_RelativeInitialStabilizer`, `ArtinGroups_ParabolicIntersections_RelativeInvisibleFactor`, `ArtinGroups_ParabolicIntersections_RelativeLowerBasics`, `ArtinGroups_ParabolicIntersections_RelativeLowerComparison`, `ArtinGroups_ParabolicIntersections_RelativeLowerConnected`, `ArtinGroups_ParabolicIntersections_RelativeLowerRetraction`, `ArtinGroups_ParabolicIntersections_RelativeMinimumContainment`, `ArtinGroups_ParabolicIntersections_RelativeNullBlockData`, `ArtinGroups_ParabolicIntersections_RelativePeaks`, `ArtinGroups_ParabolicIntersections_RelativePoset`, `ArtinGroups_ParabolicIntersections_RelativeTies`, `ArtinGroups_ParabolicIntersections_RelativeTranslation`, `ArtinGroups_ParabolicIntersections_RelativeUpperBasics`, `ArtinGroups_ParabolicIntersections_RelativeUpperComparison`, `ArtinGroups_ParabolicIntersections_RelativeUpperConnected`, `ArtinGroups_ParabolicIntersections_RelativeUpperSigns`, `ArtinGroups_ParabolicIntersections_SphericalCommonExtension`, `ArtinGroups_ParabolicIntersections_SphericalMesh`, `ArtinGroups_ParabolicIntersections_StandardEmbedding`, `ArtinGroups_ParabolicIntersections_VisualFactorMalnormal`, `ArtinGroups_ParabolicIntersections_VisualInfiniteBranching`, `ArtinGroups_ParabolicIntersections_VisualTrivialSegment`, `ArtinGroups_Quivers_ProbeSimpleEdge`.
--
--   **Imports.** It imports the published bundle `Def_ArtinParabolicIntersections`; the bundles `OAIQ236Ap008` and `OAIQ236Ap009` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ236Ap013`; the statements `OAI_HarmonicArtin_ParabolicIntersections_PointedCappedCandidate_probe_euler`, `OAI.HarmonicArtin.ParabolicIntersections.PointedCappedCandidate.probe_euler_s236`, `OAI_HarmonicArtin_ParabolicIntersections_pointedCandidate_comparison_parabolic`, `OAI.HarmonicArtin.ParabolicIntersections.pointedCandidate_comparison_parabolic_s236`, `OAI_HarmonicArtin_ParabolicIntersections_pointedProbe_raise_lower`, `OAI.HarmonicArtin.ParabolicIntersections.pointedProbe_raise_lower_s236`, `OAI_HarmonicArtin_ParabolicIntersections_relative_descending_lower_connected`, `OAI.HarmonicArtin.ParabolicIntersections.relative_descending_lower_connected_s236`, `OAI_HarmonicArtin_ParabolicIntersections_spherical_mesh_input`, `OAI.HarmonicArtin.ParabolicIntersections.spherical_mesh_input_s236`, `OAI_HarmonicArtin_ParabolicIntersections_spherical_reduction` and `OAI.HarmonicArtin.ParabolicIntersections.spherical_reduction_s236`; the proofs of `OAI_HarmonicArtin_ParabolicIntersections_pointedProbe_raise_lower`, `OAI.HarmonicArtin.ParabolicIntersections.pointedProbe_raise_lower_s236`, `OAI_HarmonicArtin_ParabolicIntersections_spherical_mesh_input`, `OAI.HarmonicArtin.ParabolicIntersections.spherical_mesh_input_s236` and `OAI.HarmonicArtin.ParabolicIntersections.unconditional_nonclique_dynamics`.
-- source:
--   OpenAI, Parabolic intersections in Artin groups, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 254; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Parabolic-intersections-in-Artin-groups-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Topology at commit adc7f12

import Mathlib
import Mathlib.Algebra.FreeAlgebra
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.List.ChainOfFn
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.PushoutI
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Kernel
import Mathlib.RingTheory.TwoSidedIdeal.Operations
import Mathlib.Topology.MetricSpace.Isometry
import Definitions.Def_ArtinParabolicIntersections
import Definitions.Def_OAIQ236Ap008
import Definitions.Def_OAIQ236Ap009

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

omit [Fintype V] [DecidableEq A] in
lemma classLayer_minimal (E : BasedComplex Q (K := K) I) (hE : E.IsMinimal Q) (d : ℤ) :
    classLayer Q d (classOfComplex Q E) = classOfComplex Q (E.pureLayer Q hE d) :=
  classOfComplex_eq Q (((minimalClassModelEquivalence Q E).pureLayer Q
    (minimalClassModel_minimal Q _) hE d).toHomotopyEquivalence Q)

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Coxeter_PositiveBraidRel
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_PositiveTopDivisor
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
lemma classLowerTruncation_minimal (E:BasedComplex Q (K:=K) I) (hE:E.IsMinimal Q) (d:ℤ) :
    classLowerTruncation Q d (classOfComplex Q E)=classOfComplex Q (lowerTruncation Q E hE d) :=
  classOfComplex_eq Q ((minimalClassModelEquivalence Q E).lowerTruncation Q
    (minimalClassModel_minimal Q _) hE d)

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

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_PacketPermExterior
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_PositiveWordActionOrthogonal
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Functors_LayerIndexEquiv
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

end HarmonicArtin.ReversibleQuiver.StringFunctor

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_UnfoldedHom
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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

theorem unfoldedHom_left_ascent (M : CoxeterMatrix S) (J : Set S) (hJ : IsSpherical M J)
    (w : (restrictedMatrix M J).Group) (α : J × FusionLabel (fusionLabelSize M)) :
    let c := (restrictedMatrix M J).toCoxeterSystem
    let d := (unfoldedMatrix M J).toCoxeterSystem
    d.length (d.simple α*unfoldedHom M J hJ w)=d.length (unfoldedHom M J hJ w)+1 ↔
      c.length (c.simple α.1*w)=c.length w+1 := by
  dsimp only
  obtain ⟨u,hu,he⟩ := (restrictedMatrix M J).toCoxeterSystem.exists_isReduced w
  rw [he,unfoldedHom_wordProd]
  exact unfolded_left_ascent_iff M J hJ u α

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

lemma fusionExpandedWord_mem {E V : Type*} [Fintype E] [DecidableEq E]
    (m : E → ℕ) (u : List V) (α : V × FusionLabel m)
    (hα : α∈fusionExpandedWord m u) : α.1∈u := by
  obtain ⟨i,hi,hα⟩ := List.mem_flatMap.mp hα
  obtain ⟨L,_,rfl⟩ := List.mem_map.mp hα
  exact hi

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Quivers_ProbeSimpleEdge
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_ProbePacket
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedAction_generator _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.restrictedArtinHom_generator
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

lemma spherical_probe_word_property (J:Set S) (hJ:IsSpherical M J)
    (u v:List J) (hu:(restrictedMatrix M J).toCoxeterSystem.IsReduced u)
    (hv:(restrictedMatrix M J).toCoxeterSystem.IsReduced v)
    (he:(restrictedMatrix M J).toCoxeterSystem.wordProd u=
      (restrictedMatrix M J).toCoxeterSystem.wordProd v) :
    ((u.map Subtype.val).map (sourceProbePacket M (K:=K))).prod=
      ((v.map Subtype.val).map (sourceProbePacket M (K:=K))).prod := by
  let g:=fun α:J×FusionLabel (fusionLabelSize M)=>f (unfoldedInclusion M J α)
  have hb:∀α β,((altList α β (unfoldedMatrix M J α β)).map g).prod=
      ((altList β α (unfoldedMatrix M J α β)).map g).prod:=by
    intro α β
    have hh:=probe_core_braid Q (K:=K) hn (unfoldedInclusion M J α) (unfoldedInclusion M J β)
    rw [unfolded_ordinaryMatrix M J hJ] at hh
    simp only [← altList_map,List.map_map,Function.comp_def] at hh
    simpa only [g] using hh
  have hh:=reduced_word_property (unfoldedMatrix M J).toCoxeterSystem g hb
    (fusionExpandedWord (fusionLabelSize M) u) (fusionExpandedWord (fusionLabelSize M) v)
    (unfolded_reducedWord M J hJ u hu) (unfolded_reducedWord M J hJ v hv)
    (unfolded_word_eq M J hJ u v he)
  rw [sourceProbeWord_expand,sourceProbeWord_expand]
  simp only [fusionExpandedWord_map,List.map_map,Function.comp_def,unfoldedInclusion,g] at hh ⊢
  convert hh using 1
  all_goals try with_reducible_and_instances rfl

lemma sourceProbePacket_braid (i j:S) :
    ((altList i j (M i j)).map (sourceProbePacket M (K:=K))).prod=
      ((altList j i (M i j)).map (sourceProbePacket M (K:=K))).prod := by
  by_cases hij:i=j
  · subst j; rfl
  by_cases hz:M i j=0
  · rw [hz]; rfl
  have hm:2≤M i j:=by have hh:=M.off_diagonal i j hij; omega
  let J:Set S:={i,j}
  let a:J:=⟨i,by simp [J]⟩
  let b:J:=⟨j,by simp [J]⟩
  have hab:a≠b:=fun h=>hij (congrArg Subtype.val h)
  have hJ:IsSpherical M J:=spherical_pair M i j hm
  have hu:=altList_reduced (restrictedMatrix M J).toCoxeterSystem a b hab (M i j)
    (Or.inr (by rfl : M i j ≤ restrictedMatrix M J a b))
  have hv:=altList_reduced (restrictedMatrix M J).toCoxeterSystem b a hab.symm (M i j)
    (Or.inr (by simpa only [restrictedMatrix_apply,a,b,M.symmetric j i] using (le_refl (M i j))))
  have he:=altList_braid (restrictedMatrix M J).toCoxeterSystem a b
  have hh:=spherical_probe_word_property M (K:=K) J hJ
    (altList a b (M i j)) (altList b a (M i j)) hu hv he
  simp only [altList_map,a,b] at hh
  simpa only [← altList_map,List.map_map,Function.comp_def] using hh

lemma sourceProbePacket_relators : ∀r∈braidRelators M,
    FreeGroup.lift (sourceProbePacket M (K:=K)) r=1 := by
  rintro r ⟨⟨i,j⟩,rfl⟩
  rw [map_mul,map_inv]
  apply mul_inv_eq_one.mpr
  rw [alternating_lift_prod,alternating_lift_prod]
  exact sourceProbePacket_braid M i j

noncomputable def sourceProbeAction : Artin M →* Equiv.Perm (FiniteHomotopyClass R (K:=K)) :=
  PresentedGroup.toGroup (sourceProbePacket_relators M)

lemma sourceProbeAction_generator (s:S) :
    sourceProbeAction M (K:=K) (generator M s)=sourceProbePacket M s :=
  PresentedGroup.toGroup.of _

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_ProbePositiveWord
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] {K:Type*} [Field K]
  (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "Q" => fusionQuiver m d (coxeterFusionEdge_symm M)
local notation "hn" => fusionQuiver_no_loops m d (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M)
local notation "R" => probeQuiver Q
local notation "hnR" => probeQuiver_no_loops Q hn

lemma sourceProbePacket_as_packet (s:S) :
    sourceProbePacket M (K:=K) s=classPacketPerm R hnR
      (fun L:FusionLabel m=>Sum.inl (Sum.inl s,L))
      (fun _ _ hab=>probe_orthogonal Q
        (fusionColor_orthogonal m d (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M)
          (.inl s) hab)) := by
  unfold sourceProbePacket fusionExpandedWord
  simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,List.map_map,Function.comp_def]
  convert classPacketPerm_toList R (K:=K) hnR (fun L:FusionLabel m=>Sum.inl (Sum.inl s,L))
    (fun _ _ hab=>probe_orthogonal Q
      (fusionColor_orthogonal m d (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M)
        (.inl s) hab)) using 1
  all_goals try with_reducible_and_instances rfl

noncomputable def probePositiveWord (J:Set S) (w:List J)
    (x:FiniteHomotopyClass R (K:=K)) : FiniteHomotopyClass R (K:=K) :=
  sourceProbeAction M (wordArtin M (w.map Subtype.val)) x

lemma probePositiveWord_cons (J:Set S) (j:J) (w:List J) (x:FiniteHomotopyClass R (K:=K)) :
    probePositiveWord M J (j::w) x=sourceProbePacket M j (probePositiveWord M J w x) := by
  simp only [probePositiveWord,List.map_cons,wordArtin,List.prod_cons,map_mul,
    sourceProbeAction_generator,Equiv.Perm.mul_apply]

lemma probePositiveWord_expanded (J:Set S) (w:List J) (x:FiniteHomotopyClass R (K:=K)) :
    probePositiveWord M J w x=positiveWordAction R
      ((fusionExpandedWord m ((w.map Subtype.val).map Sum.inl)).map Sum.inl) x := by
  rw [positiveWordAction_eq_prod R hnR]
  unfold probePositiveWord wordArtin
  simp only [map_list_prod,List.map_map,sourceProbeAction_generator,Function.comp_def]
  have h:=sourceProbeWord_expand M (K:=K) (w.map Subtype.val)
  apply congrArg (fun p:Equiv.Perm (FiniteHomotopyClass R (K:=K))=>p x)
  simpa only [List.map_map, Function.comp_def] using h

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_ProbeCoreInclusion
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedAction_generator _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf
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
local notation "hn" => fusionQuiver_no_loops m (coxeterFusionEdge M)
  (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M)
local notation "R" => probeQuiver Q
local notation "hnR" => probeQuiver_no_loops Q hn

abbrev probeCoreInclusion (J:Set S) (α:J × FusionLabel m) : ProbeVertex (FusionVertex (V:=S⊕Unit) m) :=
  Sum.inl (unfoldedInclusion M J α)

omit [Fintype S] in
lemma probeCoreInclusion_injective (J:Set S) : Function.Injective (probeCoreInclusion M J) :=
  fun _ _ he=>unfoldedInclusion_injective M J (Sum.inl.inj he)

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

lemma probePositiveWord_core_expanded (J:Set S) (w:List J) (x:FiniteHomotopyClass R (K:=K)) :
    probePositiveWord M J w x=positiveWordAction R
      ((fusionExpandedWord m w).map (probeCoreInclusion M J)) x := by
  simpa only [fusionExpandedWord_map,List.map_map,Function.comp_def,
    probeCoreInclusion,unfoldedInclusion] using probePositiveWord_expanded M J w x

lemma probeCore_word_support (J:Set S) (w:List J) :
    ∀ α∈(fusionExpandedWord m w).map (probeCoreInclusion M J),
      α∈Set.range (probeCoreInclusion M J) := by
  intro α hα
  obtain ⟨β,_,rfl⟩:=List.mem_map.mp hα
  exact ⟨β,rfl⟩

lemma probePositiveWord_testUpper_reflect (J:Set S) (w:List J)
    (x:FiniteHomotopyClass R (K:=K)) {t:ℤ}
    (h:ClassTestUpper R (probePositiveWord M J w x) (Set.range (probeCoreInclusion M J)) t) :
    ClassTestUpper R x (Set.range (probeCoreInclusion M J)) t := by
  rw [probePositiveWord_core_expanded] at h
  exact positiveWordAction_testUpper_reflect R hnR _ x _ (probeCore_word_support M J w) h

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

theorem probe_reduced_ascent_top_exact (J:Set S) (hJ:IsSpherical M J)
    (w:List J) (j:J) (hw:(restrictedMatrix M J).toCoxeterSystem.IsReduced w)
    (hj:(restrictedMatrix M J).toCoxeterSystem.IsReduced (j::w))
    (x:FiniteHomotopyClass R (K:=K)) (t ℓ:ℤ) (hlt:t<ℓ)
    (hx:ClassTestUpper R x (Set.range (probeCoreInclusion M J)) t)
    (hy:ClassTestUpper R (probePositiveWord M J w x) (Set.range (probeCoreInclusion M J)) ℓ)
    (L:FusionLabel m) (c:ℤ) :
    ClassTestExact R (probeCoreInclusion M J (j,L)) ℓ c (probePositiveWord M J w x) := by
  rw [probePositiveWord_core_expanded] at hy ⊢
  by_contra hc
  obtain ⟨v,hv⟩:=positive_top_divisor R hnR _ (probeCore_simply_laced M J hJ)
    x t hx _ (probeCore_word_support M J w) _ ⟨(j,L),rfl⟩ ℓ hlt hy c hc
  exact reduced_no_top_divisor R (probeCore_cons_reduced M J hJ w j hw hj L) hv

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_ProbePositiveWordAppend
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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
local notation "hn" => fusionQuiver_no_loops m (coxeterFusionEdge M)
  (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M)
local notation "R" => probeQuiver Q
local notation "hnR" => probeQuiver_no_loops Q hn

lemma probePositiveWord_append (J:Set S) (u v:List J) (x:FiniteHomotopyClass R (K:=K)) :
    probePositiveWord M J (u++v) x=probePositiveWord M J u (probePositiveWord M J v x) := by
  simp only [probePositiveWord,List.map_append,wordArtin_append,map_mul,Equiv.Perm.mul_apply]

lemma probePositiveWord_eq_of_restricted (J:Set S) (u v:List J)
    (h:wordArtin (restrictedMatrix M J) u=wordArtin (restrictedMatrix M J) v)
    (x:FiniteHomotopyClass R (K:=K)) : probePositiveWord M J u x=probePositiveWord M J v x := by
  have he:=congrArg (restrictedArtinHom M J) h
  rw [restrictedArtinHom_word,restrictedArtinHom_word] at he
  unfold probePositiveWord
  rw [he]

lemma sourceProbePacket_top_exact_of_cap (J:Set S) (j:J)
    (x:FiniteHomotopyClass R (K:=K)) {t:ℤ}
    (h:ClassTestUpper R (sourceProbePacket M j x) (Set.range (probeCoreInclusion M J)) t)
    (L:FusionLabel m) (c:ℤ) : ClassTestExact R (probeCoreInclusion M J (j,L)) t c x := by
  rw [sourceProbePacket_as_packet] at h
  exact classPacketPerm_testExact_of_cap R hnR _ _ (Set.range (probeCoreInclusion M J)) (fun L=>⟨(j,L),rfl⟩) x h L c

theorem probe_positive_top_factor (J:Set S) (hJ:IsSpherical M J)
    (x:FiniteHomotopyClass R (K:=K)) (t:ℤ)
    (hx:ClassTestUpper R x (Set.range (probeCoreInclusion M J)) t)
    (w:List J) (j:J) (ℓ:ℤ) (hlt:t<ℓ)
    (hy:ClassTestUpper R (probePositiveWord M J w x) (Set.range (probeCoreInclusion M J)) ℓ)
    (L:FusionLabel m) (c:ℤ)
    (htop:¬ClassTestExact R (probeCoreInclusion M J (j,L)) ℓ c (probePositiveWord M J w x)) :
    ∃v:List J,wordArtin (restrictedMatrix M J) w=
      generator (restrictedMatrix M J) j*wordArtin (restrictedMatrix M J) v ∧ v.length+1=w.length := by
  let N:=restrictedMatrix M J
  let U:=Set.range (probeCoreInclusion M J)
  induction w using (measure (fun w:List J=>w.length)).wf.induction generalizing j ℓ L c with
  | h w ih=>
    cases w with
    | nil=>exact (htop (hx _ ⟨(j,L),rfl⟩ ℓ hlt c)).elim
    | cons s w=>
      obtain ⟨u,v,hu,he,hlen,hpos,hmax⟩:=maximal_reduced_positive_prefix N s w
      have heword:wordArtin N (s::w)=wordArtin N (u++v) := by
        rw [wordArtin_append]; exact he
      have heact:probePositiveWord M J (s::w) x=
          probePositiveWord M J u (probePositiveWord M J v x) := by
        rw [probePositiveWord_eq_of_restricted M J _ _ heword,probePositiveWord_append]
      have hvsmall:v.length<(s::w).length:=by omega
      let y:=probePositiveWord M J v x
      have hcap:ClassTestUpper R y U ℓ := by
        apply probePositiveWord_testUpper_reflect M J u
        rw [←heact]
        exact hy
      by_cases hj:N.toCoxeterSystem.IsReduced (j::u)
      · have hncap:¬ClassTestUpper R y U (ℓ-1) := by
          intro hc
          apply htop
          rw [heact]
          exact probe_reduced_ascent_top_exact M J hJ u j hu hj y (ℓ-1) ℓ (by omega) hc
            (by rw [←heact]; exact hy) L c
        have htopv:∃γ:J,∃L' c',¬ClassTestExact R (probeCoreInclusion M J (γ,L')) ℓ c' y := by
          by_contra hh
          apply hncap
          intro α hα l hl c'
          obtain ⟨⟨γ,L'⟩,rfl⟩:=hα
          by_cases heq:l=ℓ
          · subst l
            by_contra hnot
            exact hh ⟨γ,L',c',hnot⟩
          · exact hcap _ ⟨(γ,L'),rfl⟩ l (by omega) c'
        obtain ⟨γ,L',c',hγ⟩:=htopv
        obtain ⟨v',hv',hvlen⟩:=ih v hvsmall γ ℓ hlt hcap L' c' hγ
        have huγ:N.toCoxeterSystem.IsReduced (u++[γ]) := by
          by_contra hnot
          obtain ⟨u',hu',he',hlen'⟩:=reduced_right_factor N u γ hu hnot
          have hea:probePositiveWord M J u y=
              probePositiveWord M J u' (sourceProbePacket M γ y) := by
            have hw:wordArtin N u=wordArtin N (u'++[γ]):=by
              rw [wordArtin_append]; exact he'
            rw [probePositiveWord_eq_of_restricted M J _ _ hw,probePositiveWord_append]
            rfl
          have hγcap:ClassTestUpper R (sourceProbePacket M γ y) U ℓ := by
            apply probePositiveWord_testUpper_reflect M J u'
            rw [←hea,←heact]
            exact hy
          exact hγ (sourceProbePacket_top_exact_of_cap M J γ y hγcap L' c')
        have hext:wordArtin N (s::w)=wordArtin N (u++[γ])*wordArtin N v' := by
          rw [he,hv',wordArtin_append]
          exact (_root_.mul_assoc _ _ _).symm
        have hlxt:(u++[γ]).length+v'.length=(s::w).length := by
          simp only [List.length_append,List.length_singleton]
          omega
        have hh:=hmax (u++[γ]) v' huγ hext hlxt
        simp only [List.length_append,List.length_singleton] at hh
        omega
      · obtain ⟨u',hu',he',hlen'⟩:=reduced_left_factor N u j hu hj
        refine ⟨u'++v,?_,?_⟩
        · rw [he,he',wordArtin_append,_root_.mul_assoc]
        · simp only [List.length_append]
          omega

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_ProbePositiveWordInitial
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedAction_generator _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] {K:Type*} [Field K] (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "Q" => fusionQuiver m (coxeterFusionEdge M) (coxeterFusionEdge_symm M)
local notation "R" => probeQuiver Q

lemma probePositiveWord_initial_avoiding (T:Set S) (w:List T) (s:S)
    (hw:∀t∈w,(t:S)≠s) (L:FusionLabel m) (b:Bool) :
    probePositiveWord M T w (initialClass R (K:=K) (.inr ((.inl s,L),b)))=
      initialClass R (.inr ((.inl s,L),b)) := by
  rw [probePositiveWord_core_expanded]
  have ho:∀α∈(fusionExpandedWord m w).map (probeCoreInclusion M T),
      OrthogonalVertices R α (.inr ((.inl s,L),b)) := by
    intro α hα
    obtain ⟨⟨t,H⟩,ht,rfl⟩:=List.mem_map.mp hα
    apply probe_core_leaf_orthogonal Q _ b
    intro he
    apply hw t _ (Sum.inl.inj (congrArg Prod.fst he))
    exact fusionExpandedWord_mem m w (t,H) ht
  generalize (fusionExpandedWord m w).map (probeCoreInclusion M T)=v at *
  induction v with
  | nil=>rfl
  | cons α v ih=>
    change classPositiveTwist R α (positiveWordAction R v _)=_
    rw [ih (fun β hβ=>ho β (List.mem_cons_of_mem _ hβ))]
    exact classPositiveTwist_initial_orthogonal R (ho α (by simp))

lemma probePositiveWord_initial_avoiding_subtype (T:Set S) (w:List T) (s:T)
    (hw:s∉w) (L:FusionLabel m) (b:Bool) :
    probePositiveWord M T w (initialClass R (K:=K) (.inr ((.inl s,L),b)))=
      initialClass R (.inr ((.inl s,L),b)) := by
  apply probePositiveWord_initial_avoiding M T w s _ L b
  intro t ht he
  exact hw ((Subtype.ext he : t=s) ▸ ht)

lemma sourceProbePacket_testUpper_reflect (T:Set S) (t:T)
    (x:FiniteHomotopyClass R (K:=K)) (q:ℤ)
    (h:ClassTestUpper R (sourceProbePacket M t x) (Set.range (probeCoreInclusion M T)) q) :
    ClassTestUpper R x (Set.range (probeCoreInclusion M T)) q := by
  rw [sourceProbePacket_as_packet] at h
  exact classPacketPerm_testUpper_reflect R
    (probeQuiver_no_loops Q (fusionQuiver_no_loops m (coxeterFusionEdge M)
      (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M))) _ _
    (Set.range (probeCoreInclusion M T)) (fun H=>⟨(t,H),rfl⟩) x h

lemma probePositiveWord_initial_cap_not_mem (T:Set S) (w:List T) (s:T)
    (L:FusionLabel m) (b:Bool)
    (hc:ClassTestUpper R (probePositiveWord M T w (initialClass R (K:=K) (.inr ((.inl s,L),b))))
      (Set.range (probeCoreInclusion M T)) 1) : s∉w := by
  induction w with
  | nil=>simp
  | cons t w ih=>
    rw [probePositiveWord_cons] at hc
    have hw:s∉w:=ih (sourceProbePacket_testUpper_reflect M T t _ 1 hc)
    have hst:s≠t:=by
      rintro rfl
      rw [probePositiveWord_initial_avoiding_subtype M T w s hw] at hc
      exact initialProbe_top_not_exact Q (K:=K) (.inl s,L) b
        (sourceProbePacket_top_exact_of_cap M T s _ hc L 0)
    simpa only [List.mem_cons,not_or] using And.intro hst hw

lemma probePositiveWord_initial_cap_iff (T:Set S) (w:List T) (s:T)
    (L:FusionLabel m) (b:Bool) :
    ClassTestUpper R (probePositiveWord M T w (initialClass R (K:=K) (.inr ((.inl s,L),b))))
      (Set.range (probeCoreInclusion M T)) 1 ↔ s∉w := by
  constructor
  · exact probePositiveWord_initial_cap_not_mem M T w s L b
  · intro hw
    rw [probePositiveWord_initial_avoiding_subtype M T w s hw]
    exact initialProbe_test_upper Q (K:=K) _ b _ (by rintro _ ⟨α,rfl⟩; exact ⟨_,rfl⟩)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_InitialProbe
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ParabolicIntersections.artinExponent_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.artinMap_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.mem_relativeStabilizer _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedAction_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeArtinHom_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visualFromArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visualToArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visual_smul_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.artinCoxeter_generator _root_.OAI.HarmonicArtin.positiveToArtin_generator _root_.OAI.HarmonicArtin.positiveToArtin_word
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
local notation "hnR" => probeQuiver_no_loops Q (fusionQuiver_no_loops m (coxeterFusionEdge M)
  (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M))

noncomputable abbrev sourceInitialProbe (s:S) (L:FusionLabel m) (b:Bool) : FiniteHomotopyClass R (K:=K) :=
  initialClass R (.inr ((.inl s,L),b))

lemma sourceInitialProbe_cap (T:Set S) (s:S) (L:FusionLabel m) (b:Bool) :
    ClassTestUpper R (sourceInitialProbe M (K:=K) s L b) (Set.range (probeCoreInclusion M T)) 1 :=
  initialProbe_test_upper Q _ b _ (by rintro _ ⟨α,rfl⟩; exact ⟨_,rfl⟩)

lemma probePositiveWord_initial_top (T:Set S) (w:List T) (s:T) (hs:s∈w)
    (L:FusionLabel m) (b:Bool) :
    ∃l:ℤ,1<l ∧ ClassTestUpper R (probePositiveWord M T w (sourceInitialProbe M (K:=K) s L b))
      (Set.range (probeCoreInclusion M T)) l ∧
      ∃j:T,∃H c,¬ClassTestExact R (probeCoreInclusion M T (j,H)) l c
        (probePositiveWord M T w (sourceInitialProbe M (K:=K) s L b)) := by
  have he:∃n:ℕ,ClassTestUpper R (probePositiveWord M T w (sourceInitialProbe M (K:=K) s L b))
      (Set.range (probeCoreInclusion M T)) (1+n) := by
    rw [probePositiveWord_core_expanded]
    exact ⟨_,positiveWordAction_testUpper R hnR _ _ _ (probeCore_word_support M T w)
      1 (sourceInitialProbe_cap M T s L b)⟩
  have hn:¬ClassTestUpper R (probePositiveWord M T w (sourceInitialProbe M (K:=K) s L b))
      (Set.range (probeCoreInclusion M T)) 1 := by
    intro h
    exact probePositiveWord_initial_cap_not_mem M T w s L b h hs
  obtain ⟨l,hl,hcap,α,⟨⟨j,H⟩,rfl⟩,c,hc⟩:=exists_top_test R _ _ 1 he hn
  exact ⟨l,hl,hcap,j,H,c,hc⟩

lemma probePositiveWord_factor (T:Set S) (w v:List T) (j:T)
    (he:wordArtin (restrictedMatrix M T) w=
      generator (restrictedMatrix M T) j*wordArtin (restrictedMatrix M T) v)
    (x:FiniteHomotopyClass R (K:=K)) :
    probePositiveWord M T w x=sourceProbePacket M j (probePositiveWord M T v x) := by
  have hw:wordArtin (restrictedMatrix M T) w=wordArtin (restrictedMatrix M T) (j::v):=he
  rw [probePositiveWord_eq_of_restricted M T w (j::v) hw,probePositiveWord_cons]

theorem positive_equal_probe_fraction (T:Set S) (hT:IsSpherical M T) (V:Set S)
    (a b:List T)
    (he:∀s:T,(s:S)∈V→∀L d,
      probePositiveWord M T a (sourceInitialProbe M (K:=K) s L d)=
        probePositiveWord M T b (sourceInitialProbe M (K:=K) s L d)) :
    ∃u v:List T,(∀s∈u,(s:S)∉V) ∧ (∀s∈v,(s:S)∉V) ∧
      (wordArtin (restrictedMatrix M T) a)⁻¹*wordArtin (restrictedMatrix M T) b=
        (wordArtin (restrictedMatrix M T) u)⁻¹*wordArtin (restrictedMatrix M T) v := by
  let N:=restrictedMatrix M T
  induction a using (measure (fun a:List T=>a.length)).wf.induction generalizing b with
  | h a ih=>
    by_cases ha:∀s∈a,(s:S)∉V
    · refine ⟨a,b,ha,?_,rfl⟩
      intro s hs hsV
      let L:FusionLabel m:=fusionZeroLabel m
        (fun edge=>le_trans (by norm_num) (fusionLabelSize_ge_four M edge))
      have has:s∉a:=fun hs=>ha s hs hsV
      have hc:ClassTestUpper R (probePositiveWord M T a (sourceInitialProbe M (K:=K) s L false))
          (Set.range (probeCoreInclusion M T)) 1 := (probePositiveWord_initial_cap_iff M T a s L false).mpr has
      rw [he s hsV L false] at hc
      exact probePositiveWord_initial_cap_not_mem M T b s L false hc hs
    · simp only [not_forall,Classical.not_not] at ha
      obtain ⟨s,hs,hsV⟩:=ha
      let L:FusionLabel m:=fusionZeroLabel m
        (fun edge=>le_trans (by norm_num) (fusionLabelSize_ge_four M edge))
      let x:FiniteHomotopyClass R (K:=K):=sourceInitialProbe M (K:=K) s L false
      obtain ⟨l,hl,hcap,j,H,c,htop⟩:=probePositiveWord_initial_top M T a s hs L false (K:=K)
      have hx:ClassTestUpper R x (Set.range (probeCoreInclusion M T)) 1:=sourceInitialProbe_cap M T s L false
      obtain ⟨a',ha',hlen⟩:=probe_positive_top_factor M T hT x 1 hx a j l hl hcap H c htop
      have heab:probePositiveWord M T a x=probePositiveWord M T b x:=he s hsV L false
      rw [heab] at hcap htop
      obtain ⟨b',hb',hblen⟩:=probe_positive_top_factor M T hT x 1 hx b j l hl hcap H c htop
      have he':∀s:T,(s:S)∈V→∀L d,
          probePositiveWord M T a' (sourceInitialProbe M (K:=K) s L d)=
            probePositiveWord M T b' (sourceInitialProbe M (K:=K) s L d) := by
        intro s hs L d
        apply (sourceProbePacket M j).injective
        rw [←probePositiveWord_factor M T a a' j ha',←probePositiveWord_factor M T b b' j hb']
        exact he s hs L d
      obtain ⟨u,v,hu,hv,hfrac⟩:=ih a' (show a'.length<a.length by omega) b' he'
      refine ⟨u,v,hu,hv,?_⟩
      rw [←hfrac,ha',hb']
      group

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_MapPacket
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ParabolicIntersections.artinExponent_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.artinMap_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.mem_relativeStabilizer _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedAction_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeArtinHom_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visualFromArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visualToArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visual_smul_vertex _root_.OAI.HarmonicArtin.artinCoxeter_generator _root_.OAI.HarmonicArtin.positiveLift_one _root_.OAI.HarmonicArtin.positiveToArtin_generator _root_.OAI.HarmonicArtin.positiveToArtin_word _root_.OAI.HarmonicArtin.restrictedArtinHom_generator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open ReversibleQuiver.ProbeEmbedding

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] {K:Type*} [Field K]
  (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "Q" => fusionQuiver m d (coxeterFusionEdge_symm M)
local notation "hn" => fusionQuiver_no_loops m d (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M)
local notation "R" => probeQuiver Q
local notation "bw" => sourceProbeAction M (K:=K)

lemma sourceProbeAction_homDimension (g:Artin M) (x y:FiniteHomotopyClass R (K:=K)) (n v:ℤ) :
    classHomDimension R n v (bw g x) (bw g y)=classHomDimension R n v x y := by
  let H:Subgroup (Artin M):=
    { carrier:={g|∀x y,classHomDimension R n v (bw g x) (bw g y)=classHomDimension R n v x y}
      one_mem':=by intro x y; simp
      mul_mem':=by
        intro a b ha hb x y
        simp only [map_mul,Equiv.Perm.mul_apply]
        exact (ha (bw b x) (bw b y)).trans (hb x y)
      inv_mem':=by
        intro a ha x y
        have h:=ha (bw a⁻¹ x) (bw a⁻¹ y)
        simpa only [map_inv,Equiv.Perm.inv_def,Equiv.apply_symm_apply] using h.symm }
  have hg:g∈H:=PresentedGroup.generated_by (braidRelators M) H (by
    intro s
    change ∀x y,classHomDimension R n v (bw (generator M s) x) (bw (generator M s) y)=_
    intro x y
    rw [sourceProbeAction_generator]
    exact twistProd_homDimension Q hn (fusionExpandedWord m [Sum.inl s]) x y n v) g
  exact hg x y

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_ProbePacketExterior
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ParabolicIntersections.artinExponent_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.artinMap_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.mem_relativeStabilizer _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedAction_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeArtinHom_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visualFromArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visualToArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visual_smul_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.artinCoxeter_generator _root_.OAI.HarmonicArtin.positiveLift_one _root_.OAI.HarmonicArtin.positiveToArtin_generator _root_.OAI.HarmonicArtin.positiveToArtin_word _root_.OAI.HarmonicArtin.restrictedArtinHom_generator
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
local notation "hn" => fusionQuiver_no_loops m d (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M)
local notation "R" => probeQuiver Q
local notation "bw" => sourceProbeAction M (K:=K)

lemma sourceProbePacket_exterior (s:S) (x:FiniteHomotopyClass R (K:=K))
    (p:GeneratorPlacement (ProbeVertex (FusionVertex (V:=S⊕Unit) m)))
    (hp:∀L,Sum.inl (Sum.inl s,L)≠p.color) :
    classGeneratorArray R (sourceProbePacket M s x) p=classGeneratorArray R x p := by
  apply twistProd_generator_exterior Q hn
  intro a ha
  unfold fusionExpandedWord at ha
  simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,List.mem_map] at ha
  obtain ⟨L,_,rfl⟩:=ha
  exact hp L

lemma sourceProbeAction_exterior (J:Set S) (g:Artin M) (hg:g∈artinParabolic M J)
    (x:FiniteHomotopyClass R (K:=K))
    (p:GeneratorPlacement (ProbeVertex (FusionVertex (V:=S⊕Unit) m)))
    (hp:∀s∈J,∀L,Sum.inl (Sum.inl s,L)≠p.color) :
    classGeneratorArray R (bw g x) p=classGeneratorArray R x p := by
  let H:Subgroup (Artin M):=
    { carrier:={g|∀x,classGeneratorArray R (bw g x) p=classGeneratorArray R x p}
      one_mem':=by intro x; simp
      mul_mem':=by
        intro a b ha hb x
        simp only [map_mul,Equiv.Perm.mul_apply]
        exact (ha (bw b x)).trans (hb x)
      inv_mem':=by
        intro a ha x
        have h:=ha (bw a⁻¹ x)
        simpa only [map_inv,Equiv.Perm.inv_def,Equiv.apply_symm_apply] using h.symm }
  have hH:artinParabolic M J≤H:=(Subgroup.closure_le H).mpr (by
    rintro g ⟨s,hs,rfl⟩
    change ∀x,classGeneratorArray R (bw (generator M s) x) p=_
    intro x
    rw [sourceProbeAction_generator]
    exact sourceProbePacket_exterior M s x p (hp s hs))
  exact hH hg x

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
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_FusionSignedPacketExterior
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedAction_generator _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.unfoldedHom_simple _root_.OAI.HarmonicArtin.unfoldedMatrix_apply
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
local notation "hn" => fusionQuiver_no_loops m d hd hdiag

lemma fusionSignedPacket_exterior (b:V × Bool) (x:FiniteHomotopyClass Q (K:=ℂ))
    (a:GeneratorPlacement (FusionVertex (V:=V) m)) (ha:b.1≠a.color.1) :
    classGeneratorArray Q (fusionSignedPacketPerm m d hd hdiag b x) a=classGeneratorArray Q x a := by
  have he:∀ L:FusionLabel m,(b.1,L)≠a.color :=
    fun L h=>ha (congrArg Prod.fst h)
  cases hb:b.2
  · simpa [fusionSignedPacketPerm,hb,fusionPacketPerm] using
      classPacketPerm_inverse_exterior Q hn _ (fusionColor_orthogonal m d hd hdiag b.1) x a he
  · simpa [fusionSignedPacketPerm,hb,fusionPacketPerm] using
      classPacketPerm_exterior Q hn _ (fusionColor_orthogonal m d hd hdiag b.1) x a he

lemma fusionWord_exterior (w:List (V × Bool)) (x:FiniteHomotopyClass Q (K:=ℂ))
    (a:GeneratorPlacement (FusionVertex (V:=V) m))
    (ha:∀ b∈w,b.1≠a.color.1) :
    classGeneratorArray Q (fusionWordPacketPerm m d hd hdiag w x) a=classGeneratorArray Q x a := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    change classGeneratorArray Q (fusionSignedPacketPerm m d hd hdiag b
      (fusionWordPacketPerm m d hd hdiag w x)) a=_
    rw [fusionSignedPacket_exterior m d hd hdiag b _ a (ha b (by simp))]
    exact ih (fun b hb=>ha b (by simp [hb]))

lemma fusionWord_level_exterior (w:List (V × Bool)) (x:FiniteHomotopyClass Q (K:=ℂ))
    (v:V) (L:FusionLabel m) (q:ℤ) (hv:∀ b∈w,b.1≠v) :
    classLevelArray Q (fusionWordPacketPerm m d hd hdiag w x) ((v,L),q)=
      classLevelArray Q x ((v,L),q) := by
  apply finsupp_mapDomain_fiber
  intro a ha
  apply fusionWord_exterior m d hd hdiag
  have he:a.color.1=v:=congrArg (fun z=>(z.1:FusionVertex (V:=V) m).1) ha
  simpa only [he] using hv

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_SignedLetter
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ParabolicIntersections.artinExponent_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.artinMap_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.mem_relativeStabilizer _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedAction_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeArtinHom_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visualFromArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visualToArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visual_smul_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.artinCoxeter_generator _root_.OAI.HarmonicArtin.positiveLift_one _root_.OAI.HarmonicArtin.positiveToArtin_generator _root_.OAI.HarmonicArtin.positiveToArtin_word _root_.OAI.HarmonicArtin.restrictedArtinHom_generator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] {K:Type*} [Field K]
  (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "P" => fusionWordPacketPerm m d (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M) (K:=K)

lemma sourceArtinAction_signedWord (w:List (S×Bool)) :
    sourceArtinAction M (K:=K) (sourceSignedWord M w)=P (sourcePacketWord w) := by
  induction w with
  | nil=>simp [sourceSignedWord,sourcePacketWord,fusionWordPacketPerm]
  | cons a w ih=>
    rw [sourceSignedWord_cons,map_mul,ih]
    change _=_*P (sourcePacketWord w)
    congr 1
    rcases a with ⟨s,b⟩
    cases b <;> simp [sourceSignedLetter,fusionSignedPacketPerm,sourceArtinAction_generator,map_inv]

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_UnfoldedInclusionRange
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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
local notation "hm" => (fun e=>le_trans (by norm_num) (fusionLabelSize_ge_four M e))
local notation "Q" => fusionQuiver m d hd
local notation "aw" => sourceArtinAction M (K:=ℂ)

omit [Fintype S] in
lemma unfoldedInclusion_range (J:Set S) :
    Set.range (unfoldedInclusion M J)=fusionColorRegion m (Sum.inl '' J) := by
  ext α
  rcases α with ⟨v,L⟩
  constructor
  · rintro ⟨⟨j,H⟩,he⟩
    change (Sum.inl (j:S),H)=(v,L) at he
    obtain ⟨rfl,rfl⟩:=Prod.mk.inj he
    exact ⟨j,j.property,rfl⟩
  · rintro ⟨j,hj,rfl⟩
    exact ⟨(⟨j,hj⟩,L),rfl⟩

lemma sourceArtinAction_level_exterior (J:Set S) (g:Artin M) (hg:g∈artinParabolic M J)
    (x:FiniteHomotopyClass Q (K:=ℂ)) (v:S⊕Unit) (hv:v∉Sum.inl '' J)
    (L:FusionLabel m) (k:ℤ) :
    classLevelArray Q (aw g x) ((v,L),k)=classLevelArray Q x ((v,L),k) := by
  obtain ⟨w,hw,rfl⟩:=artinParabolic_signed_word M J g hg
  rw [sourceArtinAction_signedWord]
  apply fusionWord_level_exterior m d hd hdiag
  intro b hb he
  obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hb
  exact hv ⟨a.1,hw a ha,he⟩

lemma sourceArtinAction_multiplicity_exterior (J:Set S) (g:Artin M) (hg:g∈artinParabolic M J)
    (x:FusionLabel m→FiniteHomotopyClass Q (K:=ℂ)) (v:S⊕Unit) (hv:v∉Sum.inl '' J) (k:ℤ) :
    fusionFamilyMultiplicity m d hd hm (fun L=>aw g (x L)) k v=
      fusionFamilyMultiplicity m d hd hm x k v := by
  unfold fusionFamilyMultiplicity
  congr 1
  apply Finset.sum_congr rfl
  intro L hL
  congr 1
  simp only [classTotalVector_layer_apply]
  congr 1
  exact sourceArtinAction_level_exterior M J g hg (x L) v hv _ k

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_FrameFamily
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_ProbePositiveWordLeft
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] {K:Type*} [Field K] (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "Q" => fusionQuiver m (coxeterFusionEdge M) (coxeterFusionEdge_symm M)
local notation "R" => probeQuiver Q

lemma probePositiveWord_left_fraction_fixed (T:Set S) (g:Artin M) (a b:List T)
    (he:g=(wordArtin M (a.map Subtype.val))⁻¹*wordArtin M (b.map Subtype.val))
    (x:FiniteHomotopyClass R (K:=K)) (hx:sourceProbeAction M g x=x) :
    probePositiveWord M T a x=probePositiveWord M T b x := by
  have hw:wordArtin M (b.map Subtype.val)=wordArtin M (a.map Subtype.val)*g := by
    rw [he]; group
  unfold probePositiveWord
  rw [hw,map_mul,Equiv.Perm.mul_apply,hx]

theorem sourceProbe_parabolic_detector (T J:Set S) (hT:IsSpherical M T)
    (g:Artin M) (hg:g∈artinParabolic M T)
    (hfix:∀s∈T,s∉J→∀L b,
      sourceProbeAction M (K:=K) g (sourceInitialProbe M s L b)=sourceInitialProbe M s L b) :
    g∈artinParabolic M J := by
  rw [←restrictedArtinHom_range M T] at hg
  obtain ⟨z,hz⟩:=hg
  let :Finite (restrictedMatrix M T).Group:=restricted_finite M T hT
  obtain ⟨a,b,hfrac⟩:=finiteArtin_positive_left_fraction (restrictedMatrix M T) z
  have hgf:g=(wordArtin M (a.map Subtype.val))⁻¹*wordArtin M (b.map Subtype.val) := by
    rw [←hz,hfrac,map_mul,map_inv,restrictedArtinHom_word,restrictedArtinHom_word]
  have he:∀s:T,(s:S)∈T\J→∀L d,
      probePositiveWord M T a (sourceInitialProbe M (K:=K) s L d)=
        probePositiveWord M T b (sourceInitialProbe M s L d) := by
    intro s hs L d
    exact probePositiveWord_left_fraction_fixed M T g a b hgf _ (hfix s s.property hs.2 L d)
  obtain ⟨u,v,hu,hv,heq⟩:=positive_equal_probe_fraction M T hT (T\J) a b he
  have hword (w:List T) (hw:∀s∈w,(s:S)∉T\J) :
      restrictedArtinHom M T (wordArtin (restrictedMatrix M T) w)∈artinParabolic M J := by
    rw [restrictedArtinHom_word]
    apply wordArtin_mem_parabolic M J
    intro s hs
    obtain ⟨t,ht,rfl⟩:=List.mem_map.mp hs
    by_contra hn
    exact hw t ht ⟨t.property,hn⟩
  rw [←hz,hfrac,heq,map_mul,map_inv]
  exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hword u hu)) (hword v hv)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_ProbeFixedOutside
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ParabolicIntersections.artinExponent_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.artinMap_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.mem_relativeStabilizer _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedAction_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeArtinHom_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visualFromArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visualToArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visual_smul_vertex _root_.OAI.HarmonicArtin.artinCoxeter_generator _root_.OAI.HarmonicArtin.positiveToArtin_generator _root_.OAI.HarmonicArtin.positiveToArtin_word
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
local notation "Q" => fusionQuiver m (coxeterFusionEdge M) (coxeterFusionEdge_symm M)
local notation "R" => probeQuiver Q

lemma sourceProbe_fixed_outside (B:Set S) (g:Artin M) (hg:g∈artinParabolic M B)
    (s:S) (hs:s∉B) (L:FusionLabel m) (b:Bool) :
    sourceProbeAction M (K:=ℂ) g (sourceInitialProbe M s L b)=sourceInitialProbe M s L b := by
  apply probeClass_fixed_of_no_diagonal Q
  · intro n u
    rw [sourceProbeAction_exterior M B g hg _ _ (by
      intro t ht H he
      have hh:t=s:=Sum.inl.inj (congrArg (fun x:FusionVertex (V:=S⊕Unit) m=>x.1) (Sum.inl.inj he))
      exact hs (hh ▸ ht)),sourceProbeInitial_array]
    simp
  · intro n u
    rw [sourceProbeAction_exterior M B g hg _ _ (by intros;exact Sum.inl_ne_inr),sourceProbeInitial_array]
    simp only [GeneratorPlacement.mk.injEq,true_and]
  · rw [sourceProbeAction_homDimension]
    exact initial_homDimension_le_one R
      (probeQuiver_no_loops Q (fusionQuiver_no_loops m (coxeterFusionEdge M)
        (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M))) _ 0 0

theorem sourceParabolic_inter (T B C:Set S) (hT:IsSpherical M T)
    (hB:B⊆T) (_hC:C⊆T) :
    artinParabolic M B ⊓ artinParabolic M C=artinParabolic M (B∩C) := by
  apply le_antisymm
  · intro g hg
    apply sourceProbe_parabolic_detector M (K:=ℂ) T (B∩C) hT g
      (artinParabolic_mono M hB hg.1)
    intro s _ hs L b
    by_cases hb:s∈B
    · exact sourceProbe_fixed_outside M C g hg.2 s (fun hc=>hs ⟨hb,hc⟩) L b
    · exact sourceProbe_fixed_outside M B g hg.1 s hb L b
  · exact le_inf (artinParabolic_mono M Set.inter_subset_left)
      (artinParabolic_mono M Set.inter_subset_right)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Coxeter_ParabolicProductMap
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

lemma sourceParabolicProductMap_injective (B C:Set S) (hT:IsSpherical M (B∪C))
    (hd:Disjoint B C) (hc:∀s∈B,∀t∈C,M s t=2) :
    Function.Injective (sourceParabolicProductMap M B C hc) := by
  intro a b he
  change (a.1:Artin M)*a.2=(b.1:Artin M)*b.2 at he
  have hx:((b.1:Artin M)⁻¹*a.1)=(b.2:Artin M)*(a.2:Artin M)⁻¹ := by
    calc
      _=(b.1:Artin M)⁻¹*((a.1:Artin M)*a.2)*(a.2:Artin M)⁻¹:=by group
      _=(b.2:Artin M)*(a.2:Artin M)⁻¹:=by rw [he];group
  have hm:((b.1:Artin M)⁻¹*a.1)∈artinParabolic M B⊓artinParabolic M C:=
    ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ b.1.property) a.1.property,
      hx ▸ Subgroup.mul_mem _ b.2.property (Subgroup.inv_mem _ a.2.property)⟩
  rw [sourceParabolic_inter M (B∪C) B C hT Set.subset_union_left Set.subset_union_right,
    Set.disjoint_iff_inter_eq_empty.mp hd,sourceParabolic_empty] at hm
  have hab:(a.1:Artin M)=(b.1:Artin M):=(inv_mul_eq_one.mp (Subgroup.mem_bot.mp hm)).symm
  have hcd:(a.2:Artin M)=(b.2:Artin M):=by rw [hab] at he;exact mul_left_cancel he
  exact Prod.ext (Subtype.ext hab) (Subtype.ext hcd)

lemma sourceParabolicProduct_mem (B C:Set S) (hT:IsSpherical M (B∪C))
    (hd:Disjoint B C) (hc:∀s∈B,∀t∈C,M s t=2)
    (R:Set S) (hR:R⊆B∪C) (b:artinParabolic M B) (c:artinParabolic M C) :
    (b:Artin M)*c∈artinParabolic M R ↔
      (b:Artin M)∈artinParabolic M (R∩B) ∧ (c:Artin M)∈artinParabolic M (R∩C) := by
  have hc':∀s∈R∩B,∀t∈R∩C,M s t=2:=fun s hs t ht=>hc s hs.2 t ht.2
  have he:(R∩B)∪(R∩C)=R:=by
    ext s
    constructor
    · rintro (⟨hs,_⟩|⟨hs,_⟩) <;> exact hs
    · intro hs
      rcases hR hs with h|h
      · exact Or.inl ⟨hs,h⟩
      · exact Or.inr ⟨hs,h⟩
  constructor
  · intro hh
    rw [←he,←sourceParabolicProductMap_range M (R∩B) (R∩C) hc'] at hh
    obtain ⟨⟨p,q⟩,hpq⟩:=hh
    let p':artinParabolic M B:=⟨p.val,artinParabolic_mono M Set.inter_subset_right p.property⟩
    let q':artinParabolic M C:=⟨q.val,artinParabolic_mono M Set.inter_subset_right q.property⟩
    have hh:(p',q')=(b,c):=sourceParabolicProductMap_injective M B C hT hd hc hpq
    have hpb:(p:Artin M)=(b:Artin M):=congrArg (fun z:artinParabolic M B × artinParabolic M C=>(z.1:Artin M)) hh
    have hqc:(q:Artin M)=(c:Artin M):=congrArg (fun z:artinParabolic M B × artinParabolic M C=>(z.2:Artin M)) hh
    exact ⟨hpb ▸ p.property,hqc ▸ q.property⟩
  · rintro ⟨hb,hc⟩
    exact Subgroup.mul_mem _ (artinParabolic_mono M Set.inter_subset_left hb)
      (artinParabolic_mono M Set.inter_subset_left hc)

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

omit [LinearOrder S] in
lemma framed_spherical_posDef (T:Set S) (hT:IsSpherical M T) :
    ((framedCartan M).submatrix ((↑):((Sum.inl : S→S⊕Unit) '' T)→S⊕Unit) Subtype.val).PosDef := by
  let e:((Sum.inl : S→S⊕Unit) '' T)→T:=fun i=>⟨(Classical.choose i.property),
    (Classical.choose_spec i.property).1⟩
  have he:∀ i:((Sum.inl : S→S⊕Unit) '' T),Sum.inl (e i:S)=(i:S⊕Unit):=
    fun i=>(Classical.choose_spec i.property).2
  have hi:Function.Injective e:=by
    intro i j hij
    apply Subtype.ext
    rw [←he i,←he j,hij]
  have h:((Geometric.cartan M).submatrix ((↑):T→S) Subtype.val).PosDef:=
    Geometric.spherical_cartan_posDef M T hT
  convert h.submatrix hi using 1
  all_goals try with_reducible_and_instances rfl
  ext i j
  change framedCartan M (i:S⊕Unit) (j:S⊕Unit)=Geometric.cartan M (e i) (e j)
  rw [←he i,←he j]
  rfl

noncomputable def sourceHarmonicAt (T:Set S) (x:Artin M) (k:ℤ) : S⊕Unit→ℝ :=
  harmonicExtension (framedCartan M) ((Sum.inl : S→S⊕Unit) '' T) (sourceMultiplicity M x k)

noncomputable def sourceCosetVector (P:Deligne M) (k:ℤ) : S⊕Unit→ℝ :=
  sourceHarmonicAt M P.val.1 (sourceCosetRepresentative M P) k

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_Candidate
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag.BasedComplex _root_.Matrix _root_.OAI.Matrix

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

omit [Fintype S] [LinearOrder S] in
lemma source_spherical_mono {J T:Set S} (h:J⊆T) (hT:IsSpherical M T) : IsSpherical M J := by
  let :Finite (coxeterParabolic M T):=hT
  have hm:coxeterParabolic M J ≤ coxeterParabolic M T:=Subgroup.closure_mono (Set.image_mono h)
  exact Finite.of_injective (fun z:coxeterParabolic M J=>(⟨z,hm z.property⟩:coxeterParabolic M T))
    (fun a b h=>Subtype.ext (congrArg (fun z:coxeterParabolic M T => (z:M.Group)) h))

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

omit [Fintype S] [LinearOrder S] in
lemma sourceCoset_le {T U:Set S} {hT:IsSpherical M T} {hU:IsSpherical M U}
    (h:T⊆U) (x:Artin M) : sourceCoset M T hT x ≤ sourceCoset M U hU x :=
  ⟨h,rightCoset_mono M h x⟩

omit [Fintype S] [LinearOrder S] in
lemma sourceCosetRepresentative_mem (P:Deligne M) : sourceCosetRepresentative M P∈P.val.2 := by
  rw [sourceCosetRepresentative_spec]
  exact rightCoset_self M _ _

omit [Fintype S] [LinearOrder S] in
lemma sourceCoset_eq (P:Deligne M) (x:Artin M) (hx:x∈P.val.2) :
    sourceCoset M P.val.1 P.property.1 x=P := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change rightCoset M P.val.1 x=P.val.2
    rw [sourceCosetRepresentative_spec] at hx ⊢
    exact rightCoset_eq_of_mem M _ _ _ hx

omit [Fintype S] [LinearOrder S] in
lemma deligne_eq_of_le_type_eq {P R:Deligne M} (h:P≤R) (ht:P.val.1=R.val.1) : P=R := by
  let x:=sourceCosetRepresentative M P
  have hx:=sourceCosetRepresentative_mem M P
  have hr:=sourceCoset_eq M R x (h.2 hx)
  have hp:=sourceCoset_eq M P x hx
  rw [←hr,←hp]
  apply Subtype.ext
  simp only [sourceCoset,ht]

omit [Fintype S] [LinearOrder S] in
lemma deligne_lt_type {P R:Deligne M} (h:P<R) : P.val.1⊂R.val.1 := by
  exact lt_of_le_of_ne h.le.1 (fun he=>h.ne (deligne_eq_of_le_type_eq M h.le he))

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_CosetBelow
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ParabolicIntersections.artinExponent_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.artinMap_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.mem_relativeStabilizer _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedAction_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeArtinHom_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visualFromArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visualToArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visual_smul_vertex _root_.OAI.HarmonicArtin.artinCoxeter_generator _root_.OAI.HarmonicArtin.positiveToArtin_generator _root_.OAI.HarmonicArtin.positiveToArtin_word
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

omit [Fintype S] [LinearOrder S] in
lemma sourceCoset_le_iff {T U:Set S} {hT:IsSpherical M T} {hU:IsSpherical M U} (x y:Artin M) :
    sourceCoset M T hT x ≤ sourceCoset M U hU y ↔ T⊆U ∧ x*y⁻¹∈artinParabolic M U := by
  constructor
  · intro h
    exact ⟨h.1,h.2 (rightCoset_self M T x)⟩
  · rintro ⟨hT,hxy⟩
    refine ⟨hT,?_⟩
    intro z hz
    change z*y⁻¹∈artinParabolic M U
    have he:z*y⁻¹=(z*x⁻¹)*(x*y⁻¹):=by group
    rw [he]
    exact Subgroup.mul_mem _ (artinParabolic_mono M hT hz) hxy

omit [Fintype S] [LinearOrder S] in
lemma sourceCoset_representative_le_iff {P R:Deligne M} (x y:Artin M) (hx:x∈P.val.2) (hy:y∈R.val.2) :
    P ≤ R ↔ P.val.1⊆R.val.1 ∧ x*y⁻¹∈artinParabolic M R.val.1 := by
  conv_lhs => rw [←sourceCoset_eq M P x hx,←sourceCoset_eq M R y hy]
  exact sourceCoset_le_iff M x y

lemma sourceSplit_coset_le (B C:Set S) (hT:IsSpherical M (B∪C))
    (hd:Disjoint B C) (hc:∀s∈B,∀t∈C,M s t=2) (x:Artin M)
    (R V R' V':Set S) (hR:R⊆B) (hV:V⊆C) (hR':R'⊆B) (hV':V'⊆C)
    (b b':artinParabolic M B) (c c':artinParabolic M C) :
    sourceCoset M (R∪V) (source_spherical_mono M (Set.union_subset_union hR hV) hT) ((b:Artin M)*c*x) ≤
      sourceCoset M (R'∪V') (source_spherical_mono M (Set.union_subset_union hR' hV') hT) ((b':Artin M)*c'*x) ↔
    (sourceCoset M R (source_spherical_mono M (hR.trans Set.subset_union_left) hT) ((b:Artin M)*x) ≤
      sourceCoset M R' (source_spherical_mono M (hR'.trans Set.subset_union_left) hT) ((b':Artin M)*x)) ∧
    (sourceCoset M V (source_spherical_mono M (hV.trans Set.subset_union_right) hT) ((c:Artin M)*x) ≤
      sourceCoset M V' (source_spherical_mono M (hV'.trans Set.subset_union_right) hT) ((c':Artin M)*x)) := by
  rw [sourceCoset_le_iff,sourceCoset_le_iff,sourceCoset_le_iff,
    sourceSplit_types hd hR hV hR' hV',sourceSplit_difference M B C hc b b' c c' x]
  have hf:=sourceParabolicProduct_mem M B C hT hd hc (R'∪V')
    (Set.union_subset_union hR' hV') (b*b'⁻¹) (c*c'⁻¹)
  have hi:=sourceSplit_inter hd hR' hV'
  rw [hi.1,hi.2] at hf
  simp only [Subgroup.coe_mul,Subgroup.coe_inv] at hf
  have hb:((b:Artin M)*x)*((b':Artin M)*x)⁻¹=(b:Artin M)*(b':Artin M)⁻¹:=by group
  have hh:((c:Artin M)*x)*((c':Artin M)*x)⁻¹=(c:Artin M)*(c':Artin M)⁻¹:=by group
  rw [hb,hh]
  rw [hf]
  tauto

abbrev SourceCosetBelow (B:Set S) (hB:IsSpherical M B) (x:Artin M) :=
  Set.Iic (sourceCoset M B hB x)

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

lemma sourceCosetProductFun_le_iff (B C:Set S) (hT:IsSpherical M (B∪C))
    (hd:Disjoint B C) (hc:∀s∈B,∀t∈C,M s t=2) (x:Artin M)
    (P R:SourceCosetBelow M B (source_spherical_mono M Set.subset_union_left hT) x ×
      SourceCosetBelow M C (source_spherical_mono M Set.subset_union_right hT) x) :
    sourceCosetProductFun M B C hT x P ≤ sourceCosetProductFun M B C hT x R ↔ P≤R := by
  let b:=sourceBelowOffset M B _ x P.1
  let c:=sourceBelowOffset M C _ x P.2
  let b':=sourceBelowOffset M B _ x R.1
  let c':=sourceBelowOffset M C _ x R.2
  change sourceCoset M _ (source_spherical_mono M (Set.union_subset_union P.1.property.1 P.2.property.1) hT) ((b:Artin M)*c*x) ≤ sourceCoset M _ (source_spherical_mono M (Set.union_subset_union R.1.property.1 R.2.property.1) hT) ((b':Artin M)*c'*x) ↔ _
  rw [sourceCoset_le_iff,sourceSplit_types hd P.1.property.1 P.2.property.1 R.1.property.1 R.2.property.1,
    sourceSplit_difference M B C hc b b' c c' x]
  have hf:=sourceParabolicProduct_mem M B C hT hd hc (R.1.val.val.1∪R.2.val.val.1)
    (Set.union_subset_union R.1.property.1 R.2.property.1)
    (b*b'⁻¹) (c*c'⁻¹)
  have hi:=sourceSplit_inter hd R.1.property.1 R.2.property.1
  rw [hi.1,hi.2] at hf
  simp only [Subgroup.coe_mul,Subgroup.coe_inv] at hf
  change ((P.1.val.val.1⊆R.1.val.val.1 ∧ P.2.val.val.1⊆R.2.val.val.1) ∧ _) ↔ _
  rw [hf]
  have hb:((b:Artin M)*(b':Artin M)⁻¹)=sourceCosetRepresentative M P.1.val*(sourceCosetRepresentative M R.1.val)⁻¹:=by
    dsimp [b,b',sourceBelowOffset];group
  have hc':((c:Artin M)*(c':Artin M)⁻¹)=sourceCosetRepresentative M P.2.val*(sourceCosetRepresentative M R.2.val)⁻¹:=by
    dsimp [c,c',sourceBelowOffset];group
  rw [hb,hc']
  change _ ↔ P.1.val ≤ R.1.val ∧ P.2.val ≤ R.2.val
  rw [sourceCoset_representative_le_iff M _ _ (sourceCosetRepresentative_mem M _) (sourceCosetRepresentative_mem M _),
    sourceCoset_representative_le_iff M _ _ (sourceCosetRepresentative_mem M _) (sourceCosetRepresentative_mem M _)]
  tauto

lemma sourceCosetProductFun_eq_of_reps (B C:Set S) (hT:IsSpherical M (B∪C))
    (hd:Disjoint B C) (hc:∀s∈B,∀t∈C,M s t=2) (x:Artin M)
    (P:SourceCosetBelow M B (source_spherical_mono M Set.subset_union_left hT) x ×
      SourceCosetBelow M C (source_spherical_mono M Set.subset_union_right hT) x)
    (b:artinParabolic M B) (c:artinParabolic M C)
    (hb:(b:Artin M)*x∈P.1.val.val.2) (hcc:(c:Artin M)*x∈P.2.val.val.2) :
    (sourceCosetProductFun M B C hT x P).val=
      sourceCoset M (P.1.val.val.1∪P.2.val.val.1)
        (source_spherical_mono M (Set.union_subset_union P.1.property.1 P.2.property.1) hT) ((b:Artin M)*c*x) := by
  let a:=sourceBelowOffset M B _ x P.1
  let d:=sourceBelowOffset M C _ x P.2
  have h₁:sourceCoset M P.1.val.val.1 P.1.val.property.1 ((a:Artin M)*x)=
      sourceCoset M P.1.val.val.1 P.1.val.property.1 ((b:Artin M)*x):=by
    rw [sourceBelowOffset_rep M B _ x P.1,
      sourceCoset_eq M P.1.val _ (sourceCosetRepresentative_mem M P.1.val),sourceCoset_eq M P.1.val _ hb]
  have h₂:sourceCoset M P.2.val.val.1 P.2.val.property.1 ((d:Artin M)*x)=
      sourceCoset M P.2.val.val.1 P.2.val.property.1 ((c:Artin M)*x):=by
    rw [sourceBelowOffset_rep M C _ x P.2,
      sourceCoset_eq M P.2.val _ (sourceCosetRepresentative_mem M P.2.val),sourceCoset_eq M P.2.val _ hcc]
  apply le_antisymm
  · exact (sourceSplit_coset_le M B C hT hd hc x _ _ _ _ P.1.property.1 P.2.property.1
      P.1.property.1 P.2.property.1 a b d c).mpr ⟨h₁.le,h₂.le⟩
  · exact (sourceSplit_coset_le M B C hT hd hc x _ _ _ _ P.1.property.1 P.2.property.1
      P.1.property.1 P.2.property.1 b a c d).mpr ⟨h₁.ge,h₂.ge⟩

lemma sourceCosetProductFun_surjective (B C:Set S) (hT:IsSpherical M (B∪C))
    (hd:Disjoint B C) (hc:∀s∈B,∀t∈C,M s t=2) (x:Artin M) :
    Function.Surjective (sourceCosetProductFun M B C hT x) := by
  intro P
  let z:=sourceCosetRepresentative M P.val
  have hz:=sourceCosetRepresentative_mem M P.val
  have hg:z*x⁻¹∈artinParabolic M (B∪C):=P.property.2 hz
  rw [←sourceParabolicProductMap_range M B C hc] at hg
  obtain ⟨⟨b,c⟩,he⟩:=hg
  change (b:Artin M)*c=z*x⁻¹ at he
  have he':(b:Artin M)*c*x=z:=by rw [he];group
  let R:=P.val.val.1∩B
  let V:=P.val.val.1∩C
  have hR:R⊆B:=Set.inter_subset_right
  have hV:V⊆C:=Set.inter_subset_right
  have hRV:R∪V=P.val.val.1:=by
    ext s
    constructor
    · rintro (⟨hs,_⟩|⟨hs,_⟩) <;> exact hs
    · intro hs
      rcases P.property.1 hs with hb|hc
      · exact Or.inl ⟨hs,hb⟩
      · exact Or.inr ⟨hs,hc⟩
  let PB:SourceCosetBelow M B (source_spherical_mono M Set.subset_union_left hT) x:=
    ⟨sourceCoset M R (source_spherical_mono M (hR.trans Set.subset_union_left) hT) ((b:Artin M)*x),
      (sourceCoset_le_iff M _ _).mpr ⟨hR,by simpa only [mul_assoc,mul_inv_cancel,mul_one] using b.property⟩⟩
  let PC:SourceCosetBelow M C (source_spherical_mono M Set.subset_union_right hT) x:=
    ⟨sourceCoset M V (source_spherical_mono M (hV.trans Set.subset_union_right) hT) ((c:Artin M)*x),
      (sourceCoset_le_iff M _ _).mpr ⟨hV,by simpa only [mul_assoc,mul_inv_cancel,mul_one] using c.property⟩⟩
  refine ⟨(PB,PC),Subtype.ext ?_⟩
  rw [sourceCosetProductFun_eq_of_reps M B C hT hd hc x (PB,PC) b c
    (rightCoset_self M R _) (rightCoset_self M V _)]
  change sourceCoset M (R∪V) _ ((b:Artin M)*c*x)=P.val
  simp only [hRV,he']
  exact sourceCoset_eq M P.val z hz

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_MultiplicitySum
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_CosetSum
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_CosetProfile
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_TieCode
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

lemma sourceDeligne_countable : Countable (Deligne M) := by
  let :Countable (Artin M):=Function.Surjective.countable (PresentedGroup.mk_surjective (braidRelators M))
  apply Function.Injective.countable (f:=fun P:Deligne M=>(P.val.1,sourceCosetRepresentative M P))
  intro P R h
  have ht:P.val.1=R.val.1:=congrArg (fun z:Set S × Artin M=>z.1) h
  have hx:sourceCosetRepresentative M P=sourceCosetRepresentative M R:=congrArg (fun z:Set S × Artin M=>z.2) h
  apply Subtype.ext
  apply Prod.ext
  · exact ht
  · rw [sourceCosetRepresentative_spec,sourceCosetRepresentative_spec,ht,hx]

noncomputable def sourceTieCode (P:Deligne M) : ℕ :=
  letI:=sourceDeligne_countable M
  letI:=Encodable.ofCountable (Deligne M)
  Encodable.encode P

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_PointedFamily
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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

noncomputable instance pointedFamilyMulAction : MulAction (Artin M) (PointedFamilySpace M) where
  smul g F := fun L => pointedAction M g (F L)
  one_smul F := by
    funext L
    exact congrArg (fun p => p (F L)) (map_one (pointedAction M))
  mul_smul g h F := by
    funext L
    exact congrArg (fun p => p (F L)) (map_mul (pointedAction M) g h)

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

lemma pointedMultiplicity_nonneg (f : S) (x : Artin M) (k : ℤ) (v : S ⊕ Unit) :
    0 ≤ pointedMultiplicity M f x k v := fusionFamilyMultiplicity_nonneg m d hd hm _ k v

/-- Bounded count intervals contain only finitely many actual count values. -/
lemma pointedMultiplicity_values_finite (f : S) (B : ℝ) :
    {r : ℝ | r ≤ B ∧ ∃ x k v, r = pointedMultiplicity M f x k v}.Finite := by
  have hh := finite_normalized_weighted_nat_sums (fusionWeight m) (fusionWeight_pos m hm)
    (fusionWeight m (fusionZeroLabel m hm)) (fusionWeight_pos m hm _) B
  apply hh.subset
  rintro r ⟨hr, x, k, v, rfl⟩
  exact ⟨hr, ⟨fun L => classLevelArray Q (pointedFamily M f x L)
    ((v, fusionZeroLabel m hm), k), pointedMultiplicity_sum M f x k v⟩⟩

lemma pointedMultiplicity_support_finite (f : S) (x : Artin M) :
    {k : ℤ | pointedMultiplicity M f x k ≠ 0}.Finite := by
  have hh := finiteFamily_level_support Q (pointedFamily M f x)
  apply hh.subset
  intro k hk
  by_contra hn
  apply hk
  funext v
  have hz (L : FusionLabel m) : classLevelArray Q (pointedFamily M f x L)
      ((v, fusionZeroLabel m hm), k) = 0 := by
    by_contra hne
    exact hn ⟨L, _, hne⟩
  rw [pointedMultiplicity_sum]
  simp only [hz, Nat.cast_zero, MulZeroClass.mul_zero, Finset.sum_const_zero, zero_div, Pi.zero_apply]

/-- The relative family changes no count outside the operated standard subgroup. -/
lemma pointedMultiplicity_exterior (J : Set S) (g : Artin M)
    (hg : g ∈ artinParabolic M J) (f : S) (x : Artin M)
    (v : S ⊕ Unit) (hv : v ∉ Sum.inl '' J) (k : ℤ) :
    pointedMultiplicity M f (g * x) k v = pointedMultiplicity M f x k v := by
  unfold pointedMultiplicity
  have he : pointedFamily M f (g * x) =
      fun L => sourceArtinAction M g (pointedFamily M f x L) := by
    funext L
    simp only [pointedFamily, pointedAction, map_mul, Equiv.Perm.mul_apply]
  rw [he]
  exact sourceArtinAction_multiplicity_exterior M J g hg _ v hv k

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_PointedProfile
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.sourceCosetProfile_apply
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

lemma pointedHarmonicAt_outside (T : Set S) (x : Artin M) (k : ℤ) (i : S ⊕ Unit)
    (hi : i ∉ Sum.inl '' T) :
    pointedHarmonicAt M f T x k i = pointedMultiplicity M f x k i :=
  harmonicExtension_outside _ _ _ hi

lemma pointedHarmonicAt_nonneg (T : Set S) (hT : IsSpherical M T) (x : Artin M) (k : ℤ) :
    ∀ i, 0 ≤ pointedHarmonicAt M f T x k i :=
  harmonicExtension_nonneg _ _ (framed_spherical_posDef M T hT)
    (framedCartan_off M) _ (pointedMultiplicity_nonneg M f x k)

lemma pointedHarmonicAt_harmonic (T : Set S) (hT : IsSpherical M T)
    (x : Artin M) (k : ℤ) (i : (Sum.inl : S → S ⊕ Unit) '' T) :
    (framedCartan M *ᵥ pointedHarmonicAt M f T x k) i = 0 :=
  harmonicExtension_harmonic _ _ (framed_spherical_posDef M T hT) _ i

lemma pointedHarmonicAt_invariant (T : Set S) (g x : Artin M)
    (hg : g ∈ artinParabolic M T) (k : ℤ) :
    pointedHarmonicAt M f T (g * x) k = pointedHarmonicAt M f T x k := by
  apply harmonicExtension_congr_exterior
  intro i hi
  exact pointedMultiplicity_exterior M T g hg f x i hi k

lemma pointedHarmonicAt_of_mem (T : Set S) (x y : Artin M)
    (hy : y ∈ rightCoset M T x) (k : ℤ) :
    pointedHarmonicAt M f T y k = pointedHarmonicAt M f T x k := by
  have hh := pointedHarmonicAt_invariant M f T (y * x⁻¹) x hy k
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using hh

lemma pointedCosetVector_eq (P : Deligne M) (x : Artin M) (hx : x ∈ P.val.2) (k : ℤ) :
    pointedCosetVector M f P k = pointedHarmonicAt M f P.val.1 x k := by
  rw [sourceCosetRepresentative_spec] at hx
  exact (pointedHarmonicAt_of_mem M f P.val.1 _ x hx k).symm

lemma pointedCosetVector_nonneg (P : Deligne M) (k : ℤ) :
    ∀ i, 0 ≤ pointedCosetVector M f P k i :=
  pointedHarmonicAt_nonneg M f P.val.1 P.property.1 _ k

lemma pointedCosetVector_harmonic (P : Deligne M) (k : ℤ) (i : (Sum.inl : S → S ⊕ Unit) '' P.val.1) :
    (framedCartan M *ᵥ pointedCosetVector M f P k) i = 0 :=
  pointedHarmonicAt_harmonic M f P.val.1 P.property.1 _ k i

lemma pointedCosetVector_support_finite (P : Deligne M) :
    {k : ℤ | pointedCosetVector M f P k ≠ 0}.Finite := by
  apply (pointedMultiplicity_support_finite M f (sourceCosetRepresentative M P)).subset
  intro k hk
  by_contra hn
  apply hk
  have hz : pointedMultiplicity M f (sourceCosetRepresentative M P) k = 0 := not_not.mp hn
  change harmonicExtension _ _ _ = 0
  rw [hz, harmonicExtension_zero]

noncomputable def pointedCosetSum (P : Deligne M) (k : ℤ) : ℝ :=
  ∑ i, pointedCosetVector M f P k i

lemma pointedCosetVector_le_sum (P : Deligne M) (k : ℤ) (i : S ⊕ Unit) :
    pointedCosetVector M f P k i ≤ pointedCosetSum M f P k :=
  Finset.single_le_sum (fun j _ => pointedCosetVector_nonneg M f P k j) (Finset.mem_univ i)

lemma pointedCosetVector_bounded_finite (B : ℝ) :
    {p : S ⊕ Unit → ℝ | ∃ P : Deligne M, ∃ k : ℤ,
      pointedCosetSum M f P k ≤ B ∧ p = pointedCosetVector M f P k}.Finite := by
  let A : Set ℝ := {0} ∪ {r : ℝ | r ≤ B ∧ ∃ x k v, r = pointedMultiplicity M f x k v}
  have hA : A.Finite := (Set.finite_singleton 0).union (pointedMultiplicity_values_finite M f B)
  apply (finite_harmonic_images (framedCartan M) A hA).subset
  rintro p ⟨P, k, hB, rfl⟩
  let T : Set (S ⊕ Unit) := Sum.inl '' P.val.1
  let v : S ⊕ Unit → ℝ := fun i => if i ∈ T then 0 else pointedCosetVector M f P k i
  refine ⟨T, v, ?_, ?_⟩
  · intro i
    by_cases hi : i ∈ T
    · exact Or.inl (by simp only [v, hi, ↓reduceIte, Set.mem_singleton_iff])
    · right
      dsimp only [v]
      simp only [hi, ↓reduceIte]
      refine ⟨(pointedCosetVector_le_sum M f P k i).trans hB, ?_⟩
      exact ⟨sourceCosetRepresentative M P, k, i,
        pointedHarmonicAt_outside M f P.val.1 _ k i hi⟩
  · change harmonicExtension (framedCartan M) T _ = harmonicExtension (framedCartan M) T v
    apply harmonicExtension_congr_exterior
    intro i hi
    simp only [v, hi, ↓reduceIte]
    exact (pointedHarmonicAt_outside M f P.val.1 _ k i hi).symm

/-- Shift the fixed integer cutoff to zero while retaining every recorded level. -/
noncomputable def pointedProfile (P : Deligne M) (cutoff : ℤ) : ℕ →₀ (S ⊕ Unit → ℝ) :=
  Finsupp.ofSupportFinite (fun k => pointedCosetVector M f P (cutoff + k))
    ((pointedCosetVector_support_finite M f P).preimage (by
      intro a _ b _ he
      exact Int.ofNat_inj.mp (add_left_cancel he)))

@[simp] lemma pointedProfile_apply (P : Deligne M) (cutoff : ℤ) (k : ℕ) :
    pointedProfile M f P cutoff k = pointedCosetVector M f P (cutoff + k) := rfl

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_PointedWeighted
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted multiplicities for the family based at any original color. -/
namespace HarmonicArtin.ParabolicIntersections
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S) (f : S)

lemma pointedMultiplicity_exterior_ordered (J : Set S) (g : Artin M)
    (hg : g ∈ artinParabolic M J) (x : Artin M) (v : S ⊕ Unit)
    (hv : v ∉ Sum.inl '' J) (k : ℤ) :
    pointedMultiplicity M f (g*x) k v = pointedMultiplicity M f x k v :=
  pointedMultiplicity_exterior M J g hg f x v hv k

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_PointedInitialCounts
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ParabolicIntersections.artinExponent_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.artinMap_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.mem_relativeStabilizer _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeArtinHom_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visualFromArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visualToArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visual_smul_vertex _root_.OAI.HarmonicArtin.artinCoxeter_generator _root_.OAI.HarmonicArtin.positiveToArtin_generator _root_.OAI.HarmonicArtin.positiveToArtin_word
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact counts and harmonic vectors at the initial pointed family. -/
namespace HarmonicArtin.ParabolicIntersections
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S) (f : S)
local notation "m" => fusionLabelSize M
local notation "Q" => fusionQuiver m (coxeterFusionEdge M) (coxeterFusionEdge_symm M)

@[simp] lemma pointedFamily_one (L : FusionLabel m) :
    pointedFamily M f 1 L = initialClass Q (.inl f,L) := by
  simp only [pointedFamily, pointedAction, map_one, Equiv.Perm.one_apply, pointedInitial]

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_RelativePoset
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamilyMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The connected poset of actual spherical cosets inside a fixed standard coset. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} (M : CoxeterMatrix S)

abbrev RelativeVertex (Y : Set S) (x : Artin M) :=
  {P : Deligne M // P.val.1 ⊆ Y ∧ P.val.2 ⊆ rightCoset M Y x}

def relativeAdjacent {Y : Set S} {x : Artin M} (P R : RelativeVertex M Y x) : Prop :=
  P ≤ R ∨ R ≤ P

abbrev RelativePath {Y : Set S} {x : Artin M} (P R : RelativeVertex M Y x) :=
  Relation.ReflTransGen (relativeAdjacent M) P R

noncomputable def relativeVertex (Y T : Set S) (hT : IsSpherical M T) (hTY : T ⊆ Y)
    (x z : Artin M) (hz : z ∈ rightCoset M Y x) : RelativeVertex M Y x :=
  ⟨sourceCoset M T hT z, hTY, rightCoset_subset_of_point M hTY hz⟩

noncomputable def relativeElement (Y : Set S) (x z : Artin M)
    (hz : z ∈ rightCoset M Y x) : RelativeVertex M Y x :=
  relativeVertex M Y ∅ (spherical_empty M) (Set.empty_subset _) x z hz

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_RelativeHeight
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ParabolicIntersections.artinExponent_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.artinMap_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.mem_relativeStabilizer _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamily_one _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeArtinHom_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visualFromArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visualToArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visual_smul_vertex _root_.OAI.HarmonicArtin.artinCoxeter_generator _root_.OAI.HarmonicArtin.positiveLift_one _root_.OAI.HarmonicArtin.positiveToArtin_generator _root_.OAI.HarmonicArtin.positiveToArtin_word _root_.OAI.HarmonicArtin.restrictedArtinHom_generator _root_.OAI.HarmonicArtin.sourceCosetProfile_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The relative harmonic height

The finite-support, highest-level-first height of §6.2 of paper 082-03.
The last coordinate is the full closed-type sign mask. The cutoff is an
arbitrary integer; null signs can occur at the cutoff itself.
-/

namespace HarmonicArtin.ParabolicIntersections

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S) (f : S)
  (U : Set (S ⊕ Unit)) (cutoff : ℤ)

noncomputable def relativeSignMask (P : Deligne M) (k : ℕ) (i : Lex (S ⊕ Unit)) : ℤ :=
  if ofLex i ∈ Sum.inl '' P.val.1 then
    relativeSign M U (pointedProfile M f P cutoff) k (ofLex i) else 0

noncomputable def relativeBlock (P : Deligne M) (k : ℕ) : RelativeBlock S :=
  toLex (pointedCosetSum M f P (cutoff + k),
    toLex (toLex (pointedProfile M f P cutoff k), toLex (relativeSignMask M f U cutoff P k)))

def RelativeBlockOccurs (b : RelativeBlock S) : Prop :=
  b = relativeZeroBlock (S := S) ∨ ∃ P : Deligne M, ∃ k : ℕ, b = relativeBlock M f U cutoff P k

lemma relativeSignMask_bounds (P : Deligne M) (k : ℕ) (i : Lex (S ⊕ Unit)) :
    relativeSignMask M f U cutoff P k i ∈ Set.Icc (-1 : ℤ) 1 := by
  unfold relativeSignMask relativeSign
  split_ifs <;> norm_num

lemma relativeBlock_of_vector_zero (P : Deligne M) (k : ℕ)
    (hz : pointedProfile M f P cutoff k = 0) :
    relativeBlock M f U cutoff P k = relativeZeroBlock (S := S) := by
  have hmask : relativeSignMask M f U cutoff P k = 0 := by
    funext i
    simp only [relativeSignMask, relativeSign, hz, Pi.zero_apply, ↓reduceIte, ite_self]
  have hsum : pointedCosetSum M f P (cutoff + k) = 0 := by
    change (∑ i, pointedProfile M f P cutoff k i) = 0
    simp only [hz, Pi.zero_apply, Finset.sum_const_zero]
  simp only [relativeBlock, relativeZeroBlock, hz, hmask, hsum]
  rfl

lemma relativeZeroBlock_le (b : RelativeBlock S) (hb : RelativeBlockOccurs M f U cutoff b) :
    relativeZeroBlock (S := S) ≤ b := by
  rcases hb with rfl | ⟨P, k, rfl⟩
  · exact le_rfl
  by_cases hz : pointedProfile M f P cutoff k = 0
  · rw [relativeBlock_of_vector_zero M f U cutoff P k hz]
  · have hex : ∃ i, pointedProfile M f P cutoff k i ≠ 0 := by
      by_contra hn
      apply hz
      funext i
      exact not_not.mp (fun hi => hn ⟨i, hi⟩)
    obtain ⟨i, hi⟩ := hex
    have hp : 0 < pointedCosetSum M f P (cutoff + k) :=
      (lt_of_le_of_ne (pointedCosetVector_nonneg M f P (cutoff + k) i) (Ne.symm hi)).trans_le
        (pointedCosetVector_le_sum M f P (cutoff + k) i)
    exact (Prod.Lex.lt_iff.mpr (Or.inl hp)).le

lemma relativeBlock_bounded_finite (B : ℝ) :
    {b : RelativeBlock S | RelativeBlockOccurs M f U cutoff b ∧ (ofLex b).1 ≤ B}.Finite := by
  let A := {p : S ⊕ Unit → ℝ | ∃ P : Deligne M, ∃ k : ℤ,
    pointedCosetSum M f P k ≤ B ∧ p = pointedCosetVector M f P k}
  let Z := {z : Lex (S ⊕ Unit) → ℤ | ∀ i, z i ∈ Set.Icc (-1 : ℤ) 1}
  have hA : A.Finite := pointedCosetVector_bounded_finite M f B
  have hZ : Z.Finite := Set.Finite.pi' (fun _ => Set.finite_Icc _ _)
  let bfun : (S ⊕ Unit → ℝ) × (Lex (S ⊕ Unit) → ℤ) → RelativeBlock S :=
    fun v => toLex (∑ i, v.1 i, toLex (toLex v.1, toLex v.2))
  apply ((hA.prod hZ).image bfun |>.insert (relativeZeroBlock (S := S))).subset
  rintro b ⟨(rfl | ⟨P, k, rfl⟩), hb⟩
  · exact Set.mem_insert _ _
  · apply Set.mem_insert_of_mem
    refine ⟨(pointedCosetVector M f P (cutoff + k), relativeSignMask M f U cutoff P k),
      ⟨⟨P, cutoff + k, hb, rfl⟩, fun i => relativeSignMask_bounds M f U cutoff P k i⟩, rfl⟩

lemma relativeBlock_predecessors_finite (b : RelativeBlock S) :
    {a : RelativeBlock S | RelativeBlockOccurs M f U cutoff a ∧ a < b}.Finite := by
  apply (relativeBlock_bounded_finite M f U cutoff (ofLex b).1).subset
  intro a ha
  exact ⟨ha.1, Prod.Lex.monotone_fst_ofLex ha.2.le⟩

noncomputable def relativeBlockRank (b : RelativeBlock S) : ℕ :=
  {a : RelativeBlock S | RelativeBlockOccurs M f U cutoff a ∧ a < b}.ncard

lemma relativeBlockRank_strictMono {b c : RelativeBlock S}
    (hb : RelativeBlockOccurs M f U cutoff b) (hbc : b < c) :
    relativeBlockRank M f U cutoff b < relativeBlockRank M f U cutoff c := by
  apply Set.ncard_lt_ncard _ (relativeBlock_predecessors_finite M f U cutoff c)
  refine ⟨fun a ha => ⟨ha.1, ha.2.trans hbc⟩, ?_⟩
  intro h
  exact (h ⟨hb, hbc⟩).2.false

lemma relativeBlockRank_eq_iff {b c : RelativeBlock S}
    (hb : RelativeBlockOccurs M f U cutoff b) (hc : RelativeBlockOccurs M f U cutoff c) :
    relativeBlockRank M f U cutoff b = relativeBlockRank M f U cutoff c ↔ b = c := by
  constructor
  · intro he
    rcases lt_trichotomy b c with h | h | h
    · have := relativeBlockRank_strictMono M f U cutoff hb h
      omega
    · exact h
    · have := relativeBlockRank_strictMono M f U cutoff hc h
      omega
  · exact congrArg _

lemma relativeBlockRank_lt_iff {b c : RelativeBlock S}
    (hb : RelativeBlockOccurs M f U cutoff b) (hc : RelativeBlockOccurs M f U cutoff c) :
    relativeBlockRank M f U cutoff b < relativeBlockRank M f U cutoff c ↔ b < c := by
  constructor
  · intro h
    by_contra hn
    rcases lt_or_eq_of_le (le_of_not_gt hn) with he | rfl
    · exact Nat.lt_asymm h (relativeBlockRank_strictMono M f U cutoff hc he)
    · exact h.false
  · exact relativeBlockRank_strictMono M f U cutoff hb

@[simp] lemma relativeBlockRank_zero :
    relativeBlockRank M f U cutoff (relativeZeroBlock (S := S)) = 0 := by
  have he : {a : RelativeBlock S | RelativeBlockOccurs M f U cutoff a ∧
      a < relativeZeroBlock (S := S)} = ∅ := by
    ext a
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro ha
    exact not_lt_of_ge (relativeZeroBlock_le M f U cutoff a ha)
  simp only [relativeBlockRank, he, Set.ncard_empty]

lemma relativeBlockRank_support_finite (P : Deligne M) :
    {k : ℕ | relativeBlockRank M f U cutoff (relativeBlock M f U cutoff P k) ≠ 0}.Finite := by
  apply (pointedProfile M f P cutoff).hasFiniteSupport.subset
  intro k hk
  change pointedProfile M f P cutoff k ≠ 0
  intro hz
  apply hk
  rw [relativeBlock_of_vector_zero M f U cutoff P k hz, relativeBlockRank_zero]

noncomputable def relativeHeight (P : Deligne M) : Colex (ℕ →₀ ℕ) :=
  toColex (Finsupp.ofSupportFinite
    (fun k => relativeBlockRank M f U cutoff (relativeBlock M f U cutoff P k))
    (relativeBlockRank_support_finite M f U cutoff P))

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_RelativeTies
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Visible and invisible sets along tied comparable vertices, §6.5 of paper 082-03. -/

namespace HarmonicArtin.ParabolicIntersections

open _root_.Matrix _root_.OAI.Matrix
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S) (f : S)
  (U : Set (S ⊕ Unit)) (cutoff : ℤ)

/-- Absence of recorded incidence, restricted to the group currently acting. -/
def relativeInvisible (Y : Set S) (P : Deligne M) : Set S :=
  {i | i ∈ Y ∧ ∀ k, ¬levelIncident (framedCartan M) (pointedProfile M f P cutoff) k (.inl i)}

def relativeVisible (Y : Set S) (P : Deligne M) : Set S :=
  P.val.1 \ relativeInvisible M f cutoff Y P

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_RelativeTranslation
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ParabolicIntersections.artinExponent_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.artinMap_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.mem_relativeStabilizer _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamily_one _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeArtinHom_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visualFromArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visualToArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visual_smul_vertex _root_.OAI.HarmonicArtin.artinCoxeter_generator _root_.OAI.HarmonicArtin.positiveToArtin_generator _root_.OAI.HarmonicArtin.positiveToArtin_word _root_.OAI.HarmonicArtin.sourceCosetProfile_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Right translation of the relative coset poset by a transported stabilizer. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S)

noncomputable def deligneRightTranslate (P : Deligne M) (r : Artin M) : Deligne M :=
  sourceCoset M P.val.1 P.property.1 (sourceCosetRepresentative M P*r)

omit [Fintype S] [LinearOrder S] in
@[simp] lemma deligneRightTranslate_type (P : Deligne M) (r : Artin M) :
    (deligneRightTranslate M P r).val.1 = P.val.1 := rfl

omit [Fintype S] [LinearOrder S] in
lemma deligneRightTranslate_relative (Y : Set S) (x a : Artin M)
    (ha : a ∈ artinParabolic M Y) (P : RelativeVertex M Y x) :
    (deligneRightTranslate M P.val (x⁻¹*a*x)).val.1 ⊆ Y ∧
      (deligneRightTranslate M P.val (x⁻¹*a*x)).val.2 ⊆ rightCoset M Y x := by
  refine ⟨P.property.1, ?_⟩
  apply rightCoset_subset_of_point M P.property.1
  let z := sourceCosetRepresentative M P.val
  have hz : z*x⁻¹ ∈ artinParabolic M Y :=
    P.property.2 (sourceCosetRepresentative_mem M P.val)
  have he : (z*(x⁻¹*a*x))*x⁻¹ = (z*x⁻¹)*a := by group
  change (z*(x⁻¹*a*x))*x⁻¹ ∈ artinParabolic M Y
  rw [he]
  exact (artinParabolic M Y).mul_mem hz ha

noncomputable def relativeTranslate (Y : Set S) (x a : Artin M)
    (ha : a ∈ artinParabolic M Y) (P : RelativeVertex M Y x) : RelativeVertex M Y x :=
  ⟨deligneRightTranslate M P.val (x⁻¹*a*x), deligneRightTranslate_relative M Y x a ha P⟩

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_PointedCosetGeometry
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ParabolicIntersections
open _root_.Matrix _root_.OAI.Matrix

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)

lemma pointedCosetVector_upper_outside {P R:Deligne M} (h:P≤R) (k:ℤ) (i:S⊕Unit)
    (hi:i∉(Sum.inl:S→S⊕Unit) '' R.val.1) :
    pointedCosetVector M f R k i=pointedCosetVector M f P k i := by
  let x:=sourceCosetRepresentative M P
  have hx:=sourceCosetRepresentative_mem M P
  rw [pointedCosetVector_eq M f R x (h.2 hx),pointedCosetVector_eq M f P x hx,
    pointedHarmonicAt_outside M f R.val.1 x k i hi,
    pointedHarmonicAt_outside M f P.val.1 x k i (fun he=>hi (Set.image_mono h.1 he))]

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_PointedResidueAllowed
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ParabolicIntersections
open _root_.Matrix _root_.OAI.Matrix

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)

def PointedResidueAllowed (strict:Bool) (P Q:Deligne M) (q:ℤ) : Prop :=
  Q<P ∧ ∀i∈P.val.1,i∉Q.val.1→
    (∀d:ℤ,q<d→pointedCosetVector M f Q d (.inl i)=0) ∧
    (if strict then pointedCosetVector M f Q q (.inl i)<pointedCosetVector M f P q (.inl i)
      else pointedCosetVector M f Q q (.inl i)≤ pointedCosetVector M f P q (.inl i))

abbrev PointedResidue (strict:Bool) (P:Deligne M) (q:ℤ) :=
  {Q:Deligne M // PointedResidueAllowed M f strict P Q q}

noncomputable def pointedResidueHeight (P Q:Deligne M) (q:ℤ) : ℝ :=
  ∑i∈P.val.1.toFinset,(pointedCosetVector M f Q q (.inl i)-pointedCosetVector M f P q (.inl i))

lemma pointedCosetVector_lower_compare_int {P Q:Deligne M} (h:Q≤P) (k:ℤ)
    (ho:∀i∈P.val.1,i∉Q.val.1→pointedCosetVector M f Q k (.inl i)≤ pointedCosetVector M f P k (.inl i)) :
    pointedCosetVector M f Q k≤ pointedCosetVector M f P k := by
  apply harmonic_boundary_comparison (framedCartan M) ((Sum.inl:S→S⊕Unit) '' Q.val.1)
    (framed_spherical_posDef M Q.val.1 Q.property.1) (framedCartan_off M)
    (pointedCosetVector M f Q k) (pointedCosetVector M f P k)
    (pointedCosetVector_harmonic M f Q k)
    (fun i=>pointedCosetVector_harmonic M f P k ⟨i,Set.image_mono h.1 i.property⟩)
  intro i hi
  by_cases hp:i∈(Sum.inl:S→S⊕Unit) '' P.val.1
  · obtain ⟨j,hj,rfl⟩:=hp
    exact ho j hj (fun hq=>hi ⟨j,hq,rfl⟩)
  · exact (pointedCosetVector_upper_outside M f h k i hp).symm.le

lemma pointedCosetVector_lower_compare_int_rev {P Q:Deligne M} (h:Q≤P) (k:ℤ)
    (ho:∀i∈P.val.1,i∉Q.val.1→pointedCosetVector M f P k (.inl i)≤ pointedCosetVector M f Q k (.inl i)) :
    pointedCosetVector M f P k≤ pointedCosetVector M f Q k := by
  apply harmonic_boundary_comparison (framedCartan M) ((Sum.inl:S→S⊕Unit) '' Q.val.1)
    (framed_spherical_posDef M Q.val.1 Q.property.1) (framedCartan_off M)
    (pointedCosetVector M f P k) (pointedCosetVector M f Q k)
    (fun i=>pointedCosetVector_harmonic M f P k ⟨i,Set.image_mono h.1 i.property⟩)
    (pointedCosetVector_harmonic M f Q k)
  intro i hi
  by_cases hp:i∈(Sum.inl:S→S⊕Unit) '' P.val.1
  · obtain ⟨j,hj,rfl⟩:=hp
    exact ho j hj (fun hq=>hi ⟨j,hq,rfl⟩)
  · exact (pointedCosetVector_upper_outside M f h k i hp).le

lemma pointedResidueAllowed_le {strict:Bool} {P Q:Deligne M} {q:ℤ}
    (h:PointedResidueAllowed M f strict P Q q) : pointedCosetVector M f Q q≤ pointedCosetVector M f P q := by
  apply pointedCosetVector_lower_compare_int M f h.1.le q
  intro i hi hn
  have hh:=(h.2 i hi hn).2
  cases strict with
  | false => exact hh
  | true => exact hh.le

lemma pointedResidueHeight_nonpos {strict:Bool} {P Q:Deligne M} {q:ℤ}
    (h:PointedResidueAllowed M f strict P Q q) : pointedResidueHeight M f P Q q≤0 := by
  exact Finset.sum_nonpos (fun i _=>sub_nonpos.mpr (pointedResidueAllowed_le M f h (.inl i)))

lemma pointedResidueHeight_mono {P Q R:Deligne M} {q:ℤ}
    (h:pointedCosetVector M f Q q≤ pointedCosetVector M f R q) :
    pointedResidueHeight M f P Q q≤ pointedResidueHeight M f P R q :=
  Finset.sum_le_sum (fun i _=>sub_le_sub_right (h (.inl i)) _)

lemma pointedResidueHeight_lt {P Q R:Deligne M} {q:ℤ}
    (h:pointedCosetVector M f Q q≤ pointedCosetVector M f R q)
    (hn:∃i∈P.val.1,pointedCosetVector M f Q q (.inl i)<pointedCosetVector M f R q (.inl i)) :
    pointedResidueHeight M f P Q q<pointedResidueHeight M f P R q := by
  apply Finset.sum_lt_sum (fun i _=>sub_le_sub_right (h (.inl i)) _)
  obtain ⟨i,hi,hl⟩:=hn
  exact ⟨i,Set.mem_toFinset.mpr hi,sub_lt_sub_right hl _⟩

lemma pointedResidueAllowed_upper {strict:Bool} {P Q R:Deligne M} {q:ℤ}
    (h:PointedResidueAllowed M f strict P Q q) (hr:Q≤R) (hp:R<P) :
    PointedResidueAllowed M f strict P R q := by
  refine ⟨hp,?_⟩
  intro i hi hn
  have hq:i∉Q.val.1:=fun hh=>hn (hr.1 hh)
  have he(d:ℤ):pointedCosetVector M f R d (.inl i)=pointedCosetVector M f Q d (.inl i):=
    pointedCosetVector_upper_outside M f hr d _ (by
      rintro ⟨j,hj,hh⟩;exact hn ((Sum.inl_injective hh) ▸ hj))
  simp only [he]
  exact h.2 i hi hq

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_PointedCosetExteriorCap
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ParabolicIntersections
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)

lemma pointedCosetVector_open_at (P:Deligne M) (z:Artin M) (hz:z∈P.val.2)
    (v:S⊕Unit) (hv:v∉Sum.inl '' P.val.1) (q:ℤ) :
    pointedCosetVector M f P q v=pointedMultiplicity M f z q v := by
  rw [pointedCosetVector_eq M f P z hz q]
  exact pointedHarmonicAt_outside M f P.val.1 z q v hv

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_PointedResidueHeightZero
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ParabolicIntersections
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex _root_.Matrix _root_.OAI.Matrix

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)

lemma pointedResidueHeight_zero_vector {strict:Bool} {P X:Deligne M} {q:ℤ}
    (hx:PointedResidueAllowed M f strict P X q) (hh:pointedResidueHeight M f P X q=0) :
    pointedCosetVector M f X q=pointedCosetVector M f P q := by
  have hn:=pointedResidueAllowed_le M f hx
  funext v
  by_cases hp:v∈Sum.inl '' P.val.1
  · obtain ⟨i,hi,rfl⟩:=hp
    have hz:pointedCosetVector M f X q (.inl i)-pointedCosetVector M f P q (.inl i)=0 :=
      (Finset.sum_eq_zero_iff_of_nonpos (fun j _=>sub_nonpos.mpr (hn (.inl j)))).mp hh i (Set.mem_toFinset.mpr hi)
    exact sub_eq_zero.mp hz
  · exact (pointedCosetVector_upper_outside M f hx.1.le q v hp).symm

lemma pointedResidueAllowed_closed_trans {P X Y:Deligne M} {q:ℤ}
    (hX:PointedResidueAllowed M f false P X q) (hY:PointedResidueAllowed M f false X Y q) :
    PointedResidueAllowed M f false P Y q := by
  refine ⟨hY.1.trans hX.1,?_⟩
  intro i hi hni
  by_cases hxi:i∈X.val.1
  · have hv:=pointedResidueAllowed_le M f hX (.inl i)
    exact ⟨(hY.2 i hxi hni).1,(hY.2 i hxi hni).2.trans hv⟩
  · have he(k:ℤ):pointedCosetVector M f Y k (.inl i)=pointedCosetVector M f X k (.inl i):=
      (pointedCosetVector_upper_outside M f hY.1.le k _ (by
        rintro ⟨j,hj,hh⟩;exact hxi ((Sum.inl_injective hh) ▸ hj))).symm
    simpa only [he] using hX.2 i hi hxi

lemma pointedResidue_zero_lower_iff {P X Y:Deligne M} {q:ℤ}
    (hx:PointedResidueAllowed M f false P X q) (hh:pointedResidueHeight M f P X q=0) (hy:Y<X) :
    PointedResidueAllowed M f false P Y q ↔ PointedResidueAllowed M f false X Y q := by
  constructor
  · intro hY
    refine ⟨hy,?_⟩
    intro i hi hni
    rw [pointedResidueHeight_zero_vector M f hx hh]
    exact hY.2 i (hx.1.le.1 hi) hni
  · exact pointedResidueAllowed_closed_trans M f hx

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_PointedCappedCandidate
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ParabolicIntersections
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex _root_.Matrix _root_.OAI.Matrix

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "Q" => fusionQuiver m d (coxeterFusionEdge_symm M)
local notation "C" => fusionFoldedCartan m d

structure PointedCappedCandidate (T J:Set S) (z:Artin M) (q:ℤ) (p:S⊕Unit→ℝ) : Prop where
  subset : J⊆T
  spherical : IsSpherical M J
  cap : ∀H,ClassCapOn Q (pointedFamily M f z H)
    (closedNeighborhood Q (Set.range (unfoldedInclusion M T))) q
  harmonic : ∀j:J,(C *ᵥ p) (.inl (j:S))=0
  exterior : ∀v,v∉Sum.inl '' J→pointedMultiplicity M f z q v=p v
  negative : ∀s∈T,s∉J→(C *ᵥ p) (.inl s)<0
  representatives : ∀a∈artinParabolic M J,
    (∀H,ClassCapOn Q (pointedFamily M f (a*z) H)
      (Set.range (unfoldedInclusion M T)) q)→
    ∀j:J,p (.inl (j:S))≤ pointedMultiplicity M f (a*z) q (.inl (j:S))

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_PointedCandidate
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ParabolicIntersections
open ReversibleQuiver ReversibleQuiver.Zigzag.BasedComplex _root_.Matrix _root_.OAI.Matrix

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)
local notation "m" => fusionLabelSize M
local notation "Q" => fusionQuiver m (coxeterFusionEdge M) (coxeterFusionEdge_symm M)
local notation "U" => fun J:Set S=>Set.range (unfoldedInclusion M J)

structure PointedCandidate (T J:Set S) (z:Artin M) (q:ℤ) : Prop where
  proper : J⊂T
  cap : ∀H,ClassCapOn Q (pointedFamily M f z H) (closedNeighborhood Q (U T) \ U J) q
  negative : ∀s∈T,s∉J→(framedCartan M *ᵥ pointedHarmonicAt M f J z q) (.inl s)<0
  representatives : ∀y∈rightCoset M J z,
    (∀H,ClassCapOn Q (pointedFamily M f y H) (U T) q)→
      ∀j:J,pointedHarmonicAt M f J z q (.inl (j:S))≤ pointedMultiplicity M f y q (.inl (j:S))

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_PointedResidueActive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ParabolicIntersections
open _root_.Matrix _root_.OAI.Matrix Simplicial CategoryTheory

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)

lemma pointedCosetVector_upper_antitone_int {X R:Deligne M} (h:X≤R) (q:ℤ)
    (hr:∀i∈R.val.1,i∉X.val.1→0≤(framedCartan M *ᵥ pointedCosetVector M f X q) (.inl i)) :
    pointedCosetVector M f R q≤ pointedCosetVector M f X q := by
  apply harmonic_upper_antitone (framedCartan M) (framedCartan_off M)
    ((Sum.inl:S→S⊕Unit) '' R.val.1) (framed_spherical_posDef M R.val.1 R.property.1)
    (pointedCosetVector M f X q) (pointedCosetVector M f R q)
    (pointedCosetVector_upper_outside M f h q) (pointedCosetVector_harmonic M f R q)
  rintro ⟨_,⟨i,hi,rfl⟩⟩
  by_cases ht:i∈X.val.1
  · rw [pointedCosetVector_harmonic M f X q ⟨.inl i,⟨i,ht,rfl⟩⟩]
  · exact hr i hi ht

lemma pointedCosetVector_upper_monotone_int {X R:Deligne M} (h:X≤R) (q:ℤ)
    (hr:∀i∈R.val.1,i∉X.val.1→(framedCartan M *ᵥ pointedCosetVector M f X q) (.inl i)≤0) :
    pointedCosetVector M f X q≤ pointedCosetVector M f R q := by
  apply harmonic_upper_monotone (framedCartan M) (framedCartan_off M)
    ((Sum.inl:S→S⊕Unit) '' R.val.1) (framed_spherical_posDef M R.val.1 R.property.1)
    (pointedCosetVector M f X q) (pointedCosetVector M f R q)
    (pointedCosetVector_upper_outside M f h q) (pointedCosetVector_harmonic M f R q)
  rintro ⟨_,⟨i,hi,rfl⟩⟩
  by_cases ht:i∈X.val.1
  · rw [pointedCosetVector_harmonic M f X q ⟨.inl i,⟨i,ht,rfl⟩⟩]
  · exact hr i hi ht

lemma pointedResidueHeight_lt_of_ne {P Q R:Deligne M} {q:ℤ} (hQ:Q≤P) (hR:R≤P)
    (h:pointedCosetVector M f Q q≤ pointedCosetVector M f R q)
    (hn:pointedCosetVector M f Q q≠pointedCosetVector M f R q) :
    pointedResidueHeight M f P Q q<pointedResidueHeight M f P R q := by
  apply pointedResidueHeight_lt M f h
  by_contra he
  apply hn
  funext v
  by_cases hv:v∈(Sum.inl:S→S⊕Unit) '' P.val.1
  · obtain ⟨i,hi,rfl⟩:=hv
    exact le_antisymm (h _) (le_of_not_gt (fun hl=>he ⟨i,hi,hl⟩))
  · exact (pointedCosetVector_upper_outside M f hQ q v hv).symm.trans
      (pointedCosetVector_upper_outside M f hR q v hv)

def pointedResidueActive (P X:Deligne M) (q:ℤ) : Set S :=
  {i | i∈P.val.1 ∧ i∉X.val.1 ∧ 0≤(framedCartan M *ᵥ pointedCosetVector M f X q) (.inl i)}

abbrev PointedResidueEarlierUpper (P X:Deligne M) (q:ℤ) :=
  {R:Deligne M // X<R ∧ R<P ∧ pointedResidueHeight M f P R q≤ pointedResidueHeight M f P X q}

lemma pointedResidueUpper_meets {P X R:Deligne M} {q:ℤ} (hr:X<R) (hp:R≤P)
    (hh:pointedResidueHeight M f P R q≤ pointedResidueHeight M f P X q) :
    ∃i∈R.val.1,i∈pointedResidueActive M f P X q := by
  by_contra hn
  have hnrow:∀i∈R.val.1,i∉X.val.1→(framedCartan M *ᵥ pointedCosetVector M f X q) (.inl i)<0:=by
    intro i hi hxi
    exact lt_of_not_ge (fun hh=>hn ⟨i,hi,hp.1 hi,hxi,hh⟩)
  have hv:=pointedCosetVector_upper_monotone_int M f hr.le q (fun i hi hx=>(hnrow i hi hx).le)
  have hne:pointedCosetVector M f X q≠pointedCosetVector M f R q:=by
    intro he
    obtain ⟨i,hi,hxi⟩:=Set.exists_of_ssubset (deligne_lt_type M hr)
    have hh:=hnrow i hi hxi
    rw [he,pointedCosetVector_harmonic M f R q ⟨.inl i,⟨i,hi,rfl⟩⟩] at hh
    exact lt_irrefl _ hh
  exact (not_lt_of_ge hh) (pointedResidueHeight_lt_of_ne M f (hr.le.trans hp) hp hv hne)

lemma pointedResidueUpper_active {P X R:Deligne M} {q:ℤ} (hr:X≤R)
    (ha:∀i∈R.val.1,i∉X.val.1→i∈pointedResidueActive M f P X q) :
    pointedResidueHeight M f P R q≤ pointedResidueHeight M f P X q :=
  pointedResidueHeight_mono M f (pointedCosetVector_upper_antitone_int M f hr q (fun i hi hn=>(ha i hi hn).2.2))

noncomputable def pointedResidueUpperTop (P X:Deligne M) (q:ℤ) (hx:X≤P) : Deligne M :=
  sourceCoset M (X.val.1 ∪ pointedResidueActive M f P X q)
    (source_spherical_mono M (show X.val.1 ∪ pointedResidueActive M f P X q⊆P.val.1 from
      fun _ hi=>hi.elim (fun h=>hx.1 h) (fun h=>h.1)) P.property.1)
    (sourceCosetRepresentative M X)

noncomputable def pointedResidueUpperClip (P X R:Deligne M) (q:ℤ) : Deligne M :=
  sourceCoset M (R.val.1 ∩ (X.val.1 ∪ pointedResidueActive M f P X q))
    (source_spherical_mono M Set.inter_subset_left R.property.1) (sourceCosetRepresentative M X)

lemma pointedResidueUpperClip_le {P X R:Deligne M} {q:ℤ} (h:X≤R) :
    pointedResidueUpperClip M f P X R q≤R := by
  calc
    pointedResidueUpperClip M f P X R q≤ sourceCoset M R.val.1 R.property.1 (sourceCosetRepresentative M X):=
      sourceCoset_le M Set.inter_subset_left _
    _=R:=sourceCoset_eq M R _ (h.2 (sourceCosetRepresentative_mem M X))

lemma le_pointedResidueUpperClip {P X R:Deligne M} {q:ℤ} (h:X≤R) :
    X≤ pointedResidueUpperClip M f P X R q := by
  calc
    X=sourceCoset M X.val.1 X.property.1 (sourceCosetRepresentative M X):=
      (sourceCoset_eq M X _ (sourceCosetRepresentative_mem M X)).symm
    _≤ pointedResidueUpperClip M f P X R q:=sourceCoset_le M (show X.val.1⊆R.val.1 ∩ (X.val.1 ∪ pointedResidueActive M f P X q) from
      fun i hi=>⟨h.1 hi,Or.inl hi⟩) _

lemma pointedResidueUpperClip_mem {P X R:Deligne M} {q:ℤ}
    (h: X<R ∧ R<P ∧ pointedResidueHeight M f P R q≤ pointedResidueHeight M f P X q) :
    X<pointedResidueUpperClip M f P X R q ∧ pointedResidueUpperClip M f P X R q<P ∧
      pointedResidueHeight M f P (pointedResidueUpperClip M f P X R q) q≤ pointedResidueHeight M f P X q := by
  have hl:=le_pointedResidueUpperClip M f (P:=P) (q:=q) h.1.le
  refine ⟨lt_of_le_of_ne hl ?_,(pointedResidueUpperClip_le M f h.1.le).trans_lt h.2.1,
    pointedResidueUpper_active M f hl (fun _ hi hn=>hi.2.resolve_left hn)⟩
  intro he
  obtain ⟨i,hi,hd⟩:=pointedResidueUpper_meets M f h.1 h.2.1.le h.2.2
  have ht:=congrArg (fun K:Deligne M=>K.val.1) he
  have hm:i∈(pointedResidueUpperClip M f P X R q).val.1:=⟨hi,Or.inr hd⟩
  rw [←ht] at hm
  exact hd.2.1 hm

noncomputable def pointedResidueUpperRetraction (P X:Deligne M) (q:ℤ) :
    PointedResidueEarlierUpper M f P X q →o PointedResidueEarlierUpper M f P X q where
  toFun R:=⟨pointedResidueUpperClip M f P X R q,pointedResidueUpperClip_mem M f R.property⟩
  monotone':=by
    intro Y Z h
    change pointedResidueUpperClip M f P X Y q≤ pointedResidueUpperClip M f P X Z q
    exact sourceCoset_le M (show Y.val.val.1 ∩ (X.val.1 ∪ pointedResidueActive M f P X q)⊆
      Z.val.val.1 ∩ (X.val.1 ∪ pointedResidueActive M f P X q) from fun _ hi=>⟨h.1 hi.1,hi.2⟩) _

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_PointedResidueEarlierLower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ParabolicIntersections
open Simplicial CategoryTheory

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)

lemma pointedResidueAllowed_trans {strict:Bool} {P Q R:Deligne M} {q:ℤ}
    (hQ:PointedResidueAllowed M f strict P Q q) (hR:PointedResidueAllowed M f true Q R q) :
    PointedResidueAllowed M f strict P R q := by
  refine ⟨hR.1.trans hQ.1,?_⟩
  intro i hi hn
  by_cases hq:i∈Q.val.1
  · have hr:=hR.2 i hq hn
    have hl:pointedCosetVector M f R q (.inl i)<pointedCosetVector M f P q (.inl i):=
      lt_of_lt_of_le (by simpa only [↓reduceIte] using hr.2) (pointedResidueAllowed_le M f hQ (.inl i))
    refine ⟨hr.1,?_⟩
    cases strict with
    | false => exact hl.le
    | true => exact hl
  · have he(d:ℤ):pointedCosetVector M f Q d (.inl i)=pointedCosetVector M f R d (.inl i):=
      pointedCosetVector_upper_outside M f hR.1.le d _ (by
        rintro ⟨j,hj,hh⟩;exact hq ((Sum.inl_injective hh) ▸ hj))
    simpa only [he] using hQ.2 i hi hq

lemma pointedResidue_strict_height_drop {P Q R:Deligne M} {q:ℤ}
    (hQ:Q≤P) (hR:PointedResidueAllowed M f true Q R q) :
    pointedResidueHeight M f P R q<pointedResidueHeight M f P Q q := by
  apply pointedResidueHeight_lt M f (pointedResidueAllowed_le M f hR)
  obtain ⟨i,hi,hn⟩:=Set.exists_of_ssubset (deligne_lt_type M hR.1)
  exact ⟨i,hQ.1 hi,by simpa only [↓reduceIte] using (hR.2 i hi hn).2⟩

abbrev PointedResidueEarlierLower (strict:Bool) (P X:Deligne M) (q:ℤ) :=
  {Y:Deligne M // PointedResidueAllowed M f strict P Y q ∧ Y<X ∧
    pointedResidueHeight M f P Y q<pointedResidueHeight M f P X q}

def pointedResidueNegative (X Y:Deligne M) (q:ℤ) : Set S :=
  {i | i∈X.val.1 ∧ i∉Y.val.1 ∧ pointedCosetVector M f Y q (.inl i)<pointedCosetVector M f X q (.inl i)}

lemma pointedResidueNegative_nonempty {P X Y:Deligne M} {q:ℤ} (hy:Y≤X)
    (hh:pointedResidueHeight M f P Y q<pointedResidueHeight M f P X q) :
    (pointedResidueNegative M f X Y q).Nonempty := by
  by_contra hn
  have hc:pointedCosetVector M f X q≤ pointedCosetVector M f Y q:=by
    apply pointedCosetVector_lower_compare_int_rev M f hy q
    intro i hi hnY
    exact le_of_not_gt (fun hl=>hn ⟨i,hi,hnY,hl⟩)
  exact (not_lt_of_ge (pointedResidueHeight_mono M f hc)) hh

lemma pointedResidueNegative_shared {X Y Z:Deligne M} {q:ℤ} (h:Y≤Z) (i:S) (hi:i∉Z.val.1) :
    i∈pointedResidueNegative M f X Y q ↔ i∈pointedResidueNegative M f X Z q := by
  have hy:i∉Y.val.1:=fun hh=>hi (h.1 hh)
  have he:=pointedCosetVector_upper_outside M f h q (.inl i) (by
    rintro ⟨j,hj,hh⟩;exact hi ((Sum.inl_injective hh) ▸ hj))
  simp only [pointedResidueNegative,Set.mem_ofPred_eq,hy,hi,not_false_eq_true,true_and,he]

noncomputable def pointedResidueClose (X Y:Deligne M) (q:ℤ) : Deligne M :=
  sourceCoset M (X.val.1 \ pointedResidueNegative M f X Y q)
    (source_spherical_mono M Set.sdiff_subset X.property.1) (sourceCosetRepresentative M Y)

lemma le_pointedResidueClose {X Y:Deligne M} {q:ℤ} (h:Y≤X) : Y≤ pointedResidueClose M f X Y q := by
  calc
    Y=sourceCoset M Y.val.1 Y.property.1 (sourceCosetRepresentative M Y):=
      (sourceCoset_eq M Y _ (sourceCosetRepresentative_mem M Y)).symm
    _≤ pointedResidueClose M f X Y q:=sourceCoset_le M (show Y.val.1⊆X.val.1 \ pointedResidueNegative M f X Y q from
      fun i hi=>⟨h.1 hi,fun hn=>hn.2.1 hi⟩) _

lemma pointedResidueClose_le {X Y:Deligne M} {q:ℤ} (h:Y≤X) : pointedResidueClose M f X Y q≤X := by
  calc
    pointedResidueClose M f X Y q≤ sourceCoset M X.val.1 X.property.1 (sourceCosetRepresentative M Y):=
      sourceCoset_le M Set.sdiff_subset _
    _=X:=sourceCoset_eq M X _ (h.2 (sourceCosetRepresentative_mem M Y))

lemma pointedResidueClose_strict {strict:Bool} {P X Y:Deligne M} {q:ℤ}
    (hy:PointedResidueAllowed M f strict P Y q) (hx:X≤P) (hyx:Y≤X)
    (hh:pointedResidueHeight M f P Y q<pointedResidueHeight M f P X q) :
    PointedResidueAllowed M f true X (pointedResidueClose M f X Y q) q := by
  refine ⟨lt_of_le_of_ne (pointedResidueClose_le M f hyx) ?_,?_⟩
  · intro he
    obtain ⟨i,hi⟩:=pointedResidueNegative_nonempty M f hyx hh
    have ht:=congrArg (fun K:Deligne M=>K.val.1) he
    have hm:i∈(pointedResidueClose M f X Y q).val.1:=by rw [ht]; exact hi.1
    exact hm.2 hi
  · intro i hi hn
    have hc: i∈pointedResidueNegative M f X Y q:=by
      by_contra hnot
      exact hn ⟨hi,hnot⟩
    have he(d:ℤ):pointedCosetVector M f (pointedResidueClose M f X Y q) d (.inl i)=pointedCosetVector M f Y d (.inl i):=
      pointedCosetVector_upper_outside M f (le_pointedResidueClose M f hyx) d _ (by
        rintro ⟨j,hj,hh⟩;exact hn ((Sum.inl_injective hh) ▸ hj))
    simp only [↓reduceIte,he]
    exact ⟨(hy.2 i (hx.1 hi) hc.2.1).1,hc.2.2⟩

lemma pointedResidueClose_monotone {X Y Z:Deligne M} {q:ℤ} (h:Y≤Z) (hz:Z≤X) :
    pointedResidueClose M f X Y q≤ pointedResidueClose M f X Z q := by
  have ht:X.val.1 \ pointedResidueNegative M f X Y q⊆X.val.1 \ pointedResidueNegative M f X Z q:=by
    intro i hi
    refine ⟨hi.1,?_⟩
    intro hh
    exact hi.2 ((pointedResidueNegative_shared M f h i hh.2.1).mpr hh)
  calc
    pointedResidueClose M f X Y q≤ sourceCoset M (pointedResidueClose M f X Z q).val.1
      (pointedResidueClose M f X Z q).property.1 (sourceCosetRepresentative M Y):=sourceCoset_le M ht _
    _=pointedResidueClose M f X Z q:=sourceCoset_eq M _ _
      ((le_pointedResidueClose M f hz).2 (h.2 (sourceCosetRepresentative_mem M Y)))

lemma pointedResidueClose_eq {X Y:Deligne M} {q:ℤ}
    (h:PointedResidueAllowed M f true X Y q) : pointedResidueClose M f X Y q=Y := by
  symm
  apply deligne_eq_of_le_type_eq M (le_pointedResidueClose M f h.1.le)
  ext i
  change i∈Y.val.1 ↔ i∈X.val.1 ∧ ¬i∈pointedResidueNegative M f X Y q
  constructor
  · intro hi
    exact ⟨h.1.le.1 hi,fun hn=>hn.2.1 hi⟩
  · rintro ⟨hi,hn⟩
    by_contra hy
    exact hn ⟨hi,hy,by simpa only [↓reduceIte] using (h.2 i hi hy).2⟩

noncomputable def pointedResidueLowerInclusion {strict:Bool} {P X:Deligne M} {q:ℤ}
    (hX:PointedResidueAllowed M f strict P X q) :
    PointedResidue M f true X q →o PointedResidueEarlierLower M f strict P X q where
  toFun Y:=⟨Y.val,pointedResidueAllowed_trans M f hX Y.property,Y.property.1,
    pointedResidue_strict_height_drop M f hX.1.le Y.property⟩
  monotone':=fun _ _ h=>h

noncomputable def pointedResidueLowerProjection {strict:Bool} {P X:Deligne M} {q:ℤ}
    (hX:PointedResidueAllowed M f strict P X q) :
    PointedResidueEarlierLower M f strict P X q →o PointedResidue M f true X q where
  toFun Y:=⟨pointedResidueClose M f X Y q,pointedResidueClose_strict M f Y.property.1 hX.1.le
    Y.property.2.1.le Y.property.2.2⟩
  monotone':=fun _ Z h=>pointedResidueClose_monotone M f h Z.property.2.1.le

noncomputable def pointedResidueLowerEquiv {strict:Bool} {P X:Deligne M} {q:ℤ}
    (hX:PointedResidueAllowed M f strict P X q) :
    ContinuousMap.HomotopyEquiv |CategoryTheory.nerve (PointedResidueEarlierLower M f strict P X q)|
      |CategoryTheory.nerve (PointedResidue M f true X q)| :=
  nerveOrderRetractionEquiv (pointedResidueLowerProjection M f hX) (pointedResidueLowerInclusion M f hX)
    (by apply OrderHom.ext; funext Y; apply Subtype.ext; exact pointedResidueClose_eq M f Y.property)
    (fun Y=>le_pointedResidueClose M f Y.property.2.1.le)

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_PointedResidueRank
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)

lemma pointedResidueHeight_range_finite (strict:Bool) (P:Deligne M) (q:ℤ) :
    (Set.range (fun X:PointedResidue M f strict P q=>pointedResidueHeight M f P X q)).Finite := by
  let A: Set (S⊕Unit→ℝ):={v | ∃X:Deligne M,∃k:ℤ,pointedCosetSum M f X k≤ pointedCosetSum M f P q ∧ v=pointedCosetVector M f X k}
  have hA:A.Finite:=pointedCosetVector_bounded_finite M f _
  apply (hA.image (fun v:S⊕Unit→ℝ=>∑i∈P.val.1.toFinset,(v (.inl i)-pointedCosetVector M f P q (.inl i)))).subset
  rintro h ⟨X,rfl⟩
  refine ⟨pointedCosetVector M f X q,⟨X,q,?_,rfl⟩,rfl⟩
  exact Finset.sum_le_sum (fun i _=>pointedResidueAllowed_le M f X.property i)

noncomputable def pointedResidueRank (strict:Bool) (P:Deligne M) (q:ℤ) (h:ℝ) : ℕ :=
  {a:ℝ | a∈Set.range (fun X:PointedResidue M f strict P q=>pointedResidueHeight M f P X q) ∧ a<h}.ncard

lemma pointedResidueRank_strictMono (strict:Bool) (P:Deligne M) (q:ℤ) {a b:ℝ}
    (ha:a∈Set.range (fun X:PointedResidue M f strict P q=>pointedResidueHeight M f P X q)) (hab:a<b) :
    pointedResidueRank M f strict P q a<pointedResidueRank M f strict P q b := by
  apply Set.ncard_lt_ncard _ ((pointedResidueHeight_range_finite M f strict P q).subset (fun _ h=>h.1))
  refine ⟨fun _ h=>⟨h.1,h.2.trans hab⟩,?_⟩
  intro h
  exact (h ⟨ha,hab⟩).2.false

lemma pointedResidueRank_lt_iff (strict:Bool) (P:Deligne M) (q:ℤ)
    (X Y:PointedResidue M f strict P q) :
    pointedResidueRank M f strict P q (pointedResidueHeight M f P X q)<
      pointedResidueRank M f strict P q (pointedResidueHeight M f P Y q) ↔
      pointedResidueHeight M f P X q<pointedResidueHeight M f P Y q := by
  constructor
  · intro h
    by_contra hn
    rcases lt_or_eq_of_le (le_of_not_gt hn) with hh|hh
    · have ht:=pointedResidueRank_strictMono M f strict P q ⟨Y,rfl⟩ hh
      exact (not_lt_of_ge h.le) ht
    · rw [hh] at h
      exact h.false
  · exact pointedResidueRank_strictMono M f strict P q ⟨X,rfl⟩

lemma pointedResidueRank_eq_iff (strict:Bool) (P:Deligne M) (q:ℤ)
    (X Y:PointedResidue M f strict P q) :
    pointedResidueRank M f strict P q (pointedResidueHeight M f P X q)=
      pointedResidueRank M f strict P q (pointedResidueHeight M f P Y q) ↔
      pointedResidueHeight M f P X q=pointedResidueHeight M f P Y q := by
  constructor
  · intro he
    rcases lt_trichotomy (pointedResidueHeight M f P X q) (pointedResidueHeight M f P Y q) with h|h|h
    · have :=(pointedResidueRank_lt_iff M f strict P q X Y).mpr h;omega
    · exact h
    · have :=(pointedResidueRank_lt_iff M f strict P q Y X).mpr h;omega
  · intro h;rw[h]

noncomputable def pointedResidueSecondary (P X:Deligne M) (q:ℤ) : ℕ :=
  if pointedResidueHeight M f P X q<0 then Fintype.card S-X.val.1.ncard else X.val.1.ncard

noncomputable def pointedResidueKey (strict:Bool) (P:Deligne M) (q:ℤ)
    (X:PointedResidue M f strict P q) : Lex (ℕ × Lex (ℕ×ℕ)) :=
  toLex (pointedResidueRank M f strict P q (pointedResidueHeight M f P X q),
    toLex (pointedResidueSecondary M f P X q,sourceTieCode M X))

def PointedResidueEarlier (strict:Bool) (P:Deligne M) (q:ℤ)
    (X Y:PointedResidue M f strict P q) : Prop := pointedResidueKey M f strict P q X<pointedResidueKey M f strict P q Y

lemma pointedResidueEarlier_iff (strict:Bool) (P:Deligne M) (q:ℤ)
    (X Y:PointedResidue M f strict P q) :
    PointedResidueEarlier M f strict P q X Y ↔
      pointedResidueHeight M f P X q<pointedResidueHeight M f P Y q ∨
      pointedResidueHeight M f P X q=pointedResidueHeight M f P Y q ∧
        (pointedResidueSecondary M f P X q<pointedResidueSecondary M f P Y q ∨
          pointedResidueSecondary M f P X q=pointedResidueSecondary M f P Y q ∧ sourceTieCode M X < sourceTieCode M Y) := by
  change _< _ ↔ _
  rw [Prod.Lex.lt_iff]
  simp only [pointedResidueKey,ofLex_toLex,pointedResidueRank_lt_iff,pointedResidueRank_eq_iff,Prod.Lex.lt_iff]

lemma pointedResidueEarlier_lower_negative {strict:Bool} {P:Deligne M} {q:ℤ}
    (X Y:PointedResidue M f strict P q) (h:Y.val<X.val) (hh:pointedResidueHeight M f P X q<0) :
    PointedResidueEarlier M f strict P q Y X ↔ pointedResidueHeight M f P Y q<pointedResidueHeight M f P X q := by
  rw [pointedResidueEarlier_iff]
  have hn:Y.val.val.1.ncard<X.val.val.1.ncard:=Set.ncard_lt_ncard (deligne_lt_type M h) (Set.toFinite _)
  have hb:X.val.val.1.ncard≤Fintype.card S:=by simpa only [Nat.card_eq_fintype_card] using Set.ncard_le_card X.val.val.1
  constructor
  · rintro (h|⟨he,h⟩)
    · exact h
    · have hy:pointedResidueHeight M f P Y q<0:=he ▸ hh
      simp only [pointedResidueSecondary,hy,hh,ite_eq_left] at h
      omega
  · exact Or.inl

lemma pointedResidueEarlier_upper_negative {strict:Bool} {P:Deligne M} {q:ℤ}
    (X Y:PointedResidue M f strict P q) (h:X.val<Y.val) (hh:pointedResidueHeight M f P X q<0) :
    PointedResidueEarlier M f strict P q Y X ↔ pointedResidueHeight M f P Y q≤ pointedResidueHeight M f P X q := by
  rw [pointedResidueEarlier_iff]
  have hn:X.val.val.1.ncard<Y.val.val.1.ncard:=Set.ncard_lt_ncard (deligne_lt_type M h) (Set.toFinite _)
  have hb:Y.val.val.1.ncard≤Fintype.card S:=by simpa only [Nat.card_eq_fintype_card] using Set.ncard_le_card Y.val.val.1
  constructor
  · rintro (h|⟨he,_⟩)
    · exact h.le
    · exact he.le
  · intro h
    rcases lt_or_eq_of_le h with h|he
    · exact Or.inl h
    · refine Or.inr ⟨he,Or.inl ?_⟩
      have hy:pointedResidueHeight M f P Y q<0:=he ▸ hh
      simp only [pointedResidueSecondary,hy,hh,ite_eq_left]
      omega

lemma pointedResidueEarlier_lower_zero {P:Deligne M} {q:ℤ}
    (X Y:PointedResidue M f false P q) (h:Y.val<X.val) (hh:pointedResidueHeight M f P X q=0) :
    PointedResidueEarlier M f false P q Y X := by
  rw [pointedResidueEarlier_iff]
  have hn:Y.val.val.1.ncard<X.val.val.1.ncard:=Set.ncard_lt_ncard (deligne_lt_type M h) (Set.toFinite _)
  rcases lt_or_eq_of_le (pointedResidueHeight_nonpos M f Y.property) with h|he
  · exact Or.inl (hh ▸ h)
  · refine Or.inr ⟨he.trans hh.symm,Or.inl ?_⟩
    simpa only [pointedResidueSecondary,he,hh,lt_self_iff_false,ite_false, if_false] using hn

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_PointedResidueEarlierLowerIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ParabolicIntersections
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)

noncomputable def pointedResidueEarlierLowerIso {strict:Bool} {P:Deligne M} {q:ℤ}
    (X:PointedResidue M f strict P q) (hh:pointedResidueHeight M f P X q<0) :
    WeightEarlierLower (PointedResidueEarlier M f strict P q) X ≃o
      PointedResidueEarlierLower M f strict P X q where
  toFun Y:=⟨Y.val.val,Y.val.property,Y.property.2,
    (pointedResidueEarlier_lower_negative M f X Y.val Y.property.2 hh).mp Y.property.1⟩
  invFun Y:=⟨⟨Y.val,Y.property.1⟩,
    (pointedResidueEarlier_lower_negative M f X ⟨Y.val,Y.property.1⟩ Y.property.2.1 hh).mpr Y.property.2.2,
    Y.property.2.1⟩
  left_inv _:=rfl
  right_inv _:=rfl
  map_rel_iff':=by intros;rfl

noncomputable def pointedResidueEarlierUpperIso {strict:Bool} {P:Deligne M} {q:ℤ}
    (X:PointedResidue M f strict P q) (hh:pointedResidueHeight M f P X q<0) :
    WeightEarlierUpper (PointedResidueEarlier M f strict P q) X ≃o
      PointedResidueEarlierUpper M f P X q where
  toFun Y:=⟨Y.val.val,Y.property.2,Y.val.property.1,
    (pointedResidueEarlier_upper_negative M f X Y.val Y.property.2 hh).mp Y.property.1⟩
  invFun Y:=⟨⟨Y.val,pointedResidueAllowed_upper M f X.property Y.property.1.le Y.property.2.1⟩,
    (pointedResidueEarlier_upper_negative M f X _ Y.property.1 hh).mpr Y.property.2.2,Y.property.1⟩
  left_inv _:=rfl
  right_inv _:=rfl
  map_rel_iff':=by intros;rfl

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_PointedResidueZeroLower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ParabolicIntersections
open Simplicial CategoryTheory
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)

noncomputable def pointedResidueZeroLowerIso {P:Deligne M} {q:ℤ}
    (X:PointedResidue M f false P q) (hh:pointedResidueHeight M f P X q=0) :
    WeightEarlierLower (PointedResidueEarlier M f false P q) X ≃o PointedResidue M f false X q where
  toFun Y:=⟨Y.val.val,(pointedResidue_zero_lower_iff M f X.property hh Y.property.2).mp Y.val.property⟩
  invFun Y:=⟨⟨Y.val,pointedResidueAllowed_closed_trans M f X.property Y.property⟩,
    pointedResidueEarlier_lower_zero M f X _ Y.property.1 hh,Y.property.1⟩
  left_inv _:=rfl
  right_inv _:=rfl
  map_rel_iff':=by intros;rfl

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_PointedCosetProduct
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pointed multiplicities on products of commuting standard cosets. -/
namespace HarmonicArtin.ParabolicIntersections
open _root_.Matrix _root_.OAI.Matrix
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)

lemma pointedCosetVector_open (P:Deligne M) (i:S) (hi:i∉P.val.1)
    (x:Artin M) (hx:x∈P.val.2) (k:ℤ) :
    pointedCosetVector M f P k (.inl i) = pointedMultiplicity M f x k (.inl i) :=
  pointedCosetVector_open_at M f P x hx (.inl i) (by
    rintro ⟨j,hj,he⟩; exact hi (Sum.inl.inj he ▸ hj)) k

lemma pointedCosetProduct_open_left (B C:Set S) (hT:IsSpherical M (B∪C))
    (hd:Disjoint B C) (hc:∀s∈B,∀t∈C,M s t=2) (x:Artin M)
    (P:SourceCosetBelow M B (source_spherical_mono M Set.subset_union_left hT) x ×
      SourceCosetBelow M C (source_spherical_mono M Set.subset_union_right hT) x)
    (i:S) (hi:i∈B) (ho:i∉P.1.val.val.1) (k:ℤ) :
    pointedCosetVector M f (sourceCosetProductFun M B C hT x P).val k (.inl i)=
      pointedCosetVector M f P.1.val k (.inl i) := by
  let b:=sourceBelowOffset M B _ x P.1
  let c:=sourceBelowOffset M C _ x P.2
  have hnot:i∉(sourceCosetProductFun M B C hT x P).val.val.1:=by
    rintro (h|h)
    · exact ho h
    · exact Set.disjoint_left.mp hd hi (P.2.property.1 h)
  have hrep:(b:Artin M)*c*x∈(sourceCosetProductFun M B C hT x P).val.val.2:=
    rightCoset_self M _ _
  have hr:(b:Artin M)*x∈P.1.val.val.2:=by
    rw [show (b:Artin M)*x=sourceCosetRepresentative M P.1.val from sourceBelowOffset_rep M B _ x P.1]
    exact sourceCosetRepresentative_mem M P.1.val
  rw [pointedCosetVector_open M f _ i hnot _ hrep,
    pointedCosetVector_open M f P.1.val i ho _ hr]
  have he:((b:Artin M)*c)*x=(c:Artin M)*((b:Artin M)*x):=by
    rw [(sourceParabolics_commute M B C hc b c b.property c.property).eq,_root_.mul_assoc]
  rw [he]
  apply pointedMultiplicity_exterior_ordered M f C c c.property
  rintro ⟨s,hs,he⟩
  cases Sum.inl_injective he
  exact Set.disjoint_left.mp hd hi hs

lemma pointedCosetProduct_open_right (B C:Set S) (hT:IsSpherical M (B∪C))
    (hd:Disjoint B C) (x:Artin M)
    (P:SourceCosetBelow M B (source_spherical_mono M Set.subset_union_left hT) x ×
      SourceCosetBelow M C (source_spherical_mono M Set.subset_union_right hT) x)
    (i:S) (hi:i∈C) (ho:i∉P.2.val.val.1) (k:ℤ) :
    pointedCosetVector M f (sourceCosetProductFun M B C hT x P).val k (.inl i)=
      pointedCosetVector M f P.2.val k (.inl i) := by
  let b:=sourceBelowOffset M B _ x P.1
  let c:=sourceBelowOffset M C _ x P.2
  have hnot:i∉(sourceCosetProductFun M B C hT x P).val.val.1:=by
    rintro (h|h)
    · exact Set.disjoint_left.mp hd (P.1.property.1 h) hi
    · exact ho h
  have hrep:(b:Artin M)*c*x∈(sourceCosetProductFun M B C hT x P).val.val.2:=
    rightCoset_self M _ _
  have hr:(c:Artin M)*x∈P.2.val.val.2:=by
    rw [show (c:Artin M)*x=sourceCosetRepresentative M P.2.val from sourceBelowOffset_rep M C _ x P.2]
    exact sourceCosetRepresentative_mem M P.2.val
  rw [pointedCosetVector_open M f _ i hnot _ hrep,
    pointedCosetVector_open M f P.2.val i ho _ hr,_root_.mul_assoc]
  apply pointedMultiplicity_exterior_ordered M f B b b.property
  rintro ⟨s,hs,he⟩
  cases Sum.inl_injective he
  exact Set.disjoint_left.mp hd hs hi


end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_RelativeActive
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ParabolicIntersections.artinExponent_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.artinMap_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.deligneRightTranslate_type _root_.OAI.HarmonicArtin.ParabolicIntersections.mem_relativeStabilizer _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamily_one _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeArtinHom_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visualFromArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visualToArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visual_smul_vertex _root_.OAI.HarmonicArtin.artinCoxeter_generator _root_.OAI.HarmonicArtin.positiveLift_one _root_.OAI.HarmonicArtin.positiveToArtin_generator _root_.OAI.HarmonicArtin.positiveToArtin_word _root_.OAI.HarmonicArtin.restrictedArtinHom_generator _root_.OAI.HarmonicArtin.sourceCosetProfile_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sphericity of all active upper colors in the actual relative filtration. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S) (f : S)
  (U : Set (S ⊕ Unit)) (cutoff : ℤ)

def relativeActiveSet (Y : Set S) (P : Deligne M) : Set S :=
  {i | i ∈ Y ∧ i ∉ P.val.1 ∧ relativeActive (framedCartan M) U (pointedProfile M f P cutoff) (.inl i)}

theorem relativeActiveSet_spherical (Y : Set S) (P : Deligne M)
    (hPY : P.val.1 ⊆ Y) (hYU : ∀ i ∈ Y, (.inl i : S ⊕ Unit) ∈ U) :
    IsSpherical M (P.val.1 ∪ relativeActiveSet M f U cutoff Y P) := by
  let K := P.val.1 ∪ relativeActiveSet M f U cutoff Y P
  let T : Set (S ⊕ Unit) := Sum.inl '' P.val.1
  let L : Set (S ⊕ Unit) := Sum.inl '' K
  have hL : ((framedCartan M).submatrix ((↑) : L → S ⊕ Unit) Subtype.val).PosDef := by
    apply relative_active_posDef (framedCartan M) (framedCartan_symm M)
      (framedCartan_off M) (fun i => by rw [framedCartan_diag]; norm_num) U
      (pointedProfile M f P cutoff)
      (fun k i => pointedCosetVector_nonneg M f P (cutoff+k) i)
      T (framed_spherical_posDef M P.val.1 P.property.1)
    · intro k i hi
      exact pointedCosetVector_harmonic M f P (cutoff+k) ⟨i,hi⟩
    · rintro i ⟨j,hj,rfl⟩
      exact hYU j (hj.elim (fun h => hPY h) (fun h => h.1))
    · rintro i ⟨j,(hj|hj),rfl⟩
      · exact Or.inl ⟨j,hj,rfl⟩
      · exact Or.inr hj.2.2
  let g : K → L := fun i => ⟨.inl (i:S),⟨i,i.property,rfl⟩⟩
  have hg : Function.Injective g := by
    intro i j h
    exact Subtype.ext (Sum.inl.inj (congrArg Subtype.val h))
  apply Geometric.spherical_of_cartan_posDef M K
  convert hL.submatrix hg using 1
  all_goals try with_reducible_and_instances rfl
  ext i j
  rfl

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_RelativeUpperBasics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Highest-incidence comparisons for upper edges of the relative filtration. -/
namespace HarmonicArtin.ParabolicIntersections
open _root_.Matrix _root_.OAI.Matrix
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S) (f : S)
  (U : Set (S ⊕ Unit)) (cutoff : ℤ)

lemma relativeHeight_lt_iff (P R : Deligne M) :
    relativeHeight M f U cutoff P < relativeHeight M f U cutoff R ↔
      ∃ k, (∀ d, k < d → relativeBlock M f U cutoff P d = relativeBlock M f U cutoff R d) ∧
        relativeBlock M f U cutoff P k < relativeBlock M f U cutoff R k := by
  rw [Finsupp.Colex.lt_iff]
  constructor
  · rintro ⟨k, hk, hlt⟩
    refine ⟨k, fun d hd => ?_, (relativeBlockRank_lt_iff M f U cutoff
      (Or.inr ⟨P,k,rfl⟩) (Or.inr ⟨R,k,rfl⟩)).mp hlt⟩
    exact (relativeBlockRank_eq_iff M f U cutoff (Or.inr ⟨P,d,rfl⟩)
      (Or.inr ⟨R,d,rfl⟩)).mp (hk d hd)
  · rintro ⟨k, hk, hlt⟩
    exact ⟨k, fun d hd => congrArg (relativeBlockRank M f U cutoff) (hk d hd),
      (relativeBlockRank_lt_iff M f U cutoff (Or.inr ⟨P,k,rfl⟩)
        (Or.inr ⟨R,k,rfl⟩)).mpr hlt⟩

noncomputable def relativeIncidence (P : Deligne M) (i : S) : ℕ :=
  incidenceLevel (framedCartan M) (pointedProfile M f P cutoff) (.inl i)

noncomputable def relativeUpperLevel (P R : Deligne M) : ℕ :=
  (R.val.1.toFinset \ P.val.1.toFinset).sup (relativeIncidence M f cutoff P)

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_RelativePeaks
attribute [-simp] _root_.OAI.HarmonicArtin.ParabolicIntersections.artinExponent_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.artinMap_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.deligneRightTranslate_type _root_.OAI.HarmonicArtin.ParabolicIntersections.mem_relativeStabilizer _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamily_one _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeArtinHom_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visualFromArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visualToArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visual_smul_vertex _root_.OAI.HarmonicArtin.artinCoxeter_generator _root_.OAI.HarmonicArtin.positiveToArtin_generator _root_.OAI.HarmonicArtin.positiveToArtin_word
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Last occupied levels and lower-edge harmonic comparisons for the pointed family. -/
namespace HarmonicArtin.ParabolicIntersections
open _root_.Matrix _root_.OAI.Matrix
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S) (cutoff:ℤ)

noncomputable def relativePeakSupport (P:Deligne M) (i:S) : Finset ℕ :=
  (pointedProfile M f P cutoff).support.filter (fun k=>pointedProfile M f P cutoff k (.inl i)≠0)

noncomputable def relativePeak (P:Deligne M) (i:S) : ℕ :=
  (relativePeakSupport M f cutoff P i).sup id

lemma relativePeakSupport_mem (P:Deligne M) (i:S) (k:ℕ) :
    k∈relativePeakSupport M f cutoff P i ↔ pointedProfile M f P cutoff k (.inl i)≠0 := by
  unfold relativePeakSupport
  rw [Finset.mem_filter, Finsupp.mem_support_iff]
  constructor
  · exact And.right
  · intro h
    exact ⟨fun he=>h (congrFun he (.inl i)),h⟩

lemma relativePeak_bound (P:Deligne M) (i:S) (k:ℕ)
    (h:pointedProfile M f P cutoff k (.inl i)≠0) : k≤ relativePeak M f cutoff P i :=
  Finset.le_sup (f:=id) ((relativePeakSupport_mem M f cutoff P i k).mpr h)

lemma relativePeak_above (P:Deligne M) (i:S) {k:ℕ} (h:relativePeak M f cutoff P i<k) :
    pointedProfile M f P cutoff k (.inl i)=0 := by
  by_contra hn
  exact Nat.not_lt_of_ge (relativePeak_bound M f cutoff P i k hn) h

lemma relativePeak_nonzero (P:Deligne M) (i:S)
    (h:(relativePeakSupport M f cutoff P i).Nonempty) :
    pointedProfile M f P cutoff (relativePeak M f cutoff P i) (.inl i)≠0 := by
  apply (relativePeakSupport_mem M f cutoff P i _).mp
  obtain ⟨k,hk,he⟩:=Finset.exists_mem_eq_sup _ h id
  change (relativePeakSupport M f cutoff P i).sup id∈relativePeakSupport M f cutoff P i
  rw [he]
  exact hk

lemma relativePeak_nonzero_of_pos (P:Deligne M) (i:S) (h:0 < relativePeak M f cutoff P i) :
    pointedProfile M f P cutoff (relativePeak M f cutoff P i) (.inl i)≠0 := by
  apply relativePeak_nonzero M f cutoff P i
  by_contra hn
  have he:relativePeakSupport M f cutoff P i=∅:=Finset.not_nonempty_iff_eq_empty.mp hn
  simp only [relativePeak,he,Finset.sup_empty] at h
  exact Nat.not_lt_zero _ h

noncomputable def relativeLowerLevel (P Q:Deligne M) : ℕ :=
  (P.val.1.toFinset \ Q.val.1.toFinset).sup (fun i=>max (relativePeak M f cutoff P i) (relativePeak M f cutoff Q i))

lemma relativePeak_le_lowerLevel (P Q:Deligne M) (i:S) (hi:i∈P.val.1) (hq:i∉Q.val.1) :
    relativePeak M f cutoff P i≤ relativeLowerLevel M f cutoff P Q ∧ relativePeak M f cutoff Q i≤ relativeLowerLevel M f cutoff P Q := by
  have hh:=Finset.le_sup (f:=fun i=>max (relativePeak M f cutoff P i) (relativePeak M f cutoff Q i))
    (show i∈P.val.1.toFinset \ Q.val.1.toFinset by simp [hi,hq])
  exact ⟨(le_max_left _ _).trans hh,(le_max_right _ _).trans hh⟩

lemma relativeProfile_eq_of_lower_open {P Q:Deligne M} (h:Q≤P) (k:ℕ)
    (ho:∀i∈P.val.1,i∉Q.val.1→pointedProfile M f Q cutoff k (.inl i)=pointedProfile M f P cutoff k (.inl i)) :
    pointedProfile M f Q cutoff k=pointedProfile M f P cutoff k := by
  have hext(i:S⊕Unit)(hi:i∉(Sum.inl:S→S⊕Unit) '' Q.val.1):
      pointedProfile M f Q cutoff k i=pointedProfile M f P cutoff k i:=by
    by_cases hp:i∈(Sum.inl:S→S⊕Unit) '' P.val.1
    · obtain ⟨j,hj,rfl⟩:=hp
      exact ho j hj (fun hq=>hi ⟨j,hq,rfl⟩)
    · exact (pointedCosetVector_upper_outside M f h (cutoff+k) i hp).symm
  have hq:=harmonicExtension_unique (framedCartan M) ((Sum.inl:S→S⊕Unit) '' Q.val.1)
    (framed_spherical_posDef M Q.val.1 Q.property.1) (pointedProfile M f P cutoff k)
    (pointedProfile M f Q cutoff k) hext (pointedCosetVector_harmonic M f Q (cutoff+k))
  have hp:=harmonicExtension_unique (framedCartan M) ((Sum.inl:S→S⊕Unit) '' Q.val.1)
    (framed_spherical_posDef M Q.val.1 Q.property.1) (pointedProfile M f P cutoff k)
    (pointedProfile M f P cutoff k) (fun _ _=>rfl)
    (fun i=>pointedCosetVector_harmonic M f P (cutoff+k) ⟨i,Set.image_mono h.1 i.property⟩)
  exact hq.trans hp.symm

lemma relativeProfile_lower_comparison {P Q:Deligne M} (h:Q≤P) (k:ℕ)
    (ho:∀i∈P.val.1,i∉Q.val.1→pointedProfile M f P cutoff k (.inl i)≤ pointedProfile M f Q cutoff k (.inl i)) :
    pointedProfile M f P cutoff k≤ pointedProfile M f Q cutoff k := by
  apply harmonic_boundary_comparison (framedCartan M) ((Sum.inl:S→S⊕Unit) '' Q.val.1)
    (framed_spherical_posDef M Q.val.1 Q.property.1) (framedCartan_off M)
    (pointedProfile M f P cutoff k) (pointedProfile M f Q cutoff k)
    (fun i=>pointedCosetVector_harmonic M f P (cutoff+k) ⟨i,Set.image_mono h.1 i.property⟩)
    (pointedCosetVector_harmonic M f Q (cutoff+k))
  intro i hi
  by_cases hp:i∈(Sum.inl:S→S⊕Unit) '' P.val.1
  · obtain ⟨j,hj,rfl⟩:=hp
    exact ho j hj (fun hq=>hi ⟨j,hq,rfl⟩)
  · exact (pointedCosetVector_upper_outside M f h (cutoff+k) i hp).le

lemma relativeProfile_lower_comparison_rev {P Q:Deligne M} (h:Q≤P) (k:ℕ)
    (ho:∀i∈P.val.1,i∉Q.val.1→pointedProfile M f Q cutoff k (.inl i)≤ pointedProfile M f P cutoff k (.inl i)) :
    pointedProfile M f Q cutoff k≤ pointedProfile M f P cutoff k := by
  apply harmonic_boundary_comparison (framedCartan M) ((Sum.inl:S→S⊕Unit) '' Q.val.1)
    (framed_spherical_posDef M Q.val.1 Q.property.1) (framedCartan_off M)
    (pointedProfile M f Q cutoff k) (pointedProfile M f P cutoff k)
    (pointedCosetVector_harmonic M f Q (cutoff+k))
    (fun i=>pointedCosetVector_harmonic M f P (cutoff+k) ⟨i,Set.image_mono h.1 i.property⟩)
  intro i hi
  by_cases hp:i∈(Sum.inl:S→S⊕Unit) '' P.val.1
  · obtain ⟨j,hj,rfl⟩:=hp
    exact ho j hj (fun hq=>hi ⟨j,hq,rfl⟩)
  · exact (pointedCosetVector_upper_outside M f h (cutoff+k) i hp).symm.le

lemma relativeProfile_eq_above_lower {P Q:Deligne M} (h:Q≤P) {k:ℕ}
    (hk:relativeLowerLevel M f cutoff P Q<k) : pointedProfile M f Q cutoff k=pointedProfile M f P cutoff k := by
  apply relativeProfile_eq_of_lower_open M f cutoff h k
  intro i hi hq
  have hb:=relativePeak_le_lowerLevel M f cutoff P Q i hi hq
  rw [relativePeak_above M f cutoff Q i (hb.2.trans_lt hk),relativePeak_above M f cutoff P i (hb.1.trans_lt hk)]


end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_RelativeUpperSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Active-color rows and full sign masks at an upper comparison level. -/
namespace HarmonicArtin.ParabolicIntersections
open _root_.Matrix _root_.OAI.Matrix
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S) (f : S)
  (U : Set (S ⊕ Unit)) (cutoff : ℤ)

def relativeColorActive (P : Deligne M) (i : S) : Prop :=
  relativeActive (framedCartan M) U (pointedProfile M f P cutoff) (.inl i)

lemma relative_mask_upper_nonneg {P R : Deligne M} (h : P ≤ R) (k : ℕ)
    (hs : ∀ i, relativeSign M U (pointedProfile M f R cutoff) k i =
      relativeSign M U (pointedProfile M f P cutoff) k i)
    (hn : ∀ i ∈ R.val.1, i ∉ P.val.1 →
      0 ≤ relativeSign M U (pointedProfile M f P cutoff) k (.inl i)) :
    relativeSignMask M f U cutoff P k ≤ relativeSignMask M f U cutoff R k := by
  intro i
  unfold relativeSignMask
  rw [hs]
  by_cases hp : ofLex i ∈ Sum.inl '' P.val.1
  · simp only [hp, Set.image_mono h.1 hp, ↓reduceIte, le_refl]
  · by_cases hr : ofLex i ∈ Sum.inl '' R.val.1
    · obtain ⟨j,hj,he⟩ := hr
      have hnp : j ∉ P.val.1 := fun hh => hp ⟨j,hh,he⟩
      simp only [hp, show ofLex i ∈ Sum.inl '' R.val.1 from ⟨j,hj,he⟩, ↓reduceIte]
      rw [←he]
      exact hn j hj hnp
    · simp only [hp, hr, ↓reduceIte, le_refl]

lemma relative_mask_upper_nonpos {P R : Deligne M} (h : P ≤ R) (k : ℕ)
    (hs : ∀ i, relativeSign M U (pointedProfile M f R cutoff) k i =
      relativeSign M U (pointedProfile M f P cutoff) k i)
    (hn : ∀ i ∈ R.val.1, i ∉ P.val.1 →
      relativeSign M U (pointedProfile M f P cutoff) k (.inl i) ≤ 0) :
    relativeSignMask M f U cutoff R k ≤ relativeSignMask M f U cutoff P k := by
  intro i
  unfold relativeSignMask
  rw [hs]
  by_cases hp : ofLex i ∈ Sum.inl '' P.val.1
  · simp only [hp, Set.image_mono h.1 hp, ↓reduceIte, le_refl]
  · by_cases hr : ofLex i ∈ Sum.inl '' R.val.1
    · obtain ⟨j,hj,he⟩ := hr
      have hnp : j ∉ P.val.1 := fun hh => hp ⟨j,hh,he⟩
      simp only [hp, show ofLex i ∈ Sum.inl '' R.val.1 from ⟨j,hj,he⟩, ↓reduceIte]
      rw [←he]
      exact hn j hj hnp
    · simp only [hp, hr, ↓reduceIte, le_refl]

lemma relativeBlock_lt_of_mask {P R : Deligne M} {k : ℕ}
    (hv : pointedProfile M f P cutoff k = pointedProfile M f R cutoff k)
    (hm : relativeSignMask M f U cutoff P k < relativeSignMask M f U cutoff R k) :
    relativeBlock M f U cutoff P k < relativeBlock M f U cutoff R k := by
  unfold relativeBlock
  apply Prod.Lex.lt_iff.mpr
  refine Or.inr ⟨congrArg (fun v : S ⊕ Unit → ℝ => ∑ i, v i) hv, ?_⟩
  exact Prod.Lex.lt_iff.mpr (Or.inr ⟨congrArg toLex hv, Pi.toLex_strictMono hm⟩)

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_RelativeUpperComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Strict upper-neighbor comparisons for the relative height. -/
namespace HarmonicArtin.ParabolicIntersections
open _root_.Matrix _root_.OAI.Matrix
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S) (f : S)
  (U : Set (S ⊕ Unit)) (cutoff : ℤ)

lemma relativeHeight_eq_of_blocks {P R : Deligne M}
    (he : ∀ k, relativeBlock M f U cutoff P k = relativeBlock M f U cutoff R k) :
    relativeHeight M f U cutoff P = relativeHeight M f U cutoff R := by
  apply congrArg toColex
  ext k
  change relativeBlockRank M f U cutoff _ = relativeBlockRank M f U cutoff _
  rw [he]

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_RelativeLowerBasics
attribute [-simp] _root_.OAI.HarmonicArtin.ParabolicIntersections.artinExponent_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.artinMap_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.deligneRightTranslate_type _root_.OAI.HarmonicArtin.ParabolicIntersections.mem_relativeStabilizer _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamily_one _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeArtinHom_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visualFromArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visualToArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visual_smul_vertex _root_.OAI.HarmonicArtin.artinCoxeter_generator _root_.OAI.HarmonicArtin.positiveToArtin_generator _root_.OAI.HarmonicArtin.positiveToArtin_word
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The highest changed level on a lower edge, including invisible opened colors. -/
namespace HarmonicArtin.ParabolicIntersections
open _root_.Matrix _root_.OAI.Matrix
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)
  (U:Set (S ⊕ Unit)) (cutoff:ℤ)

lemma relativeLowerLevel_attained (P Q:Deligne M)
    (hsome : ∃ i ∈ P.val.1, i ∉ Q.val.1 ∧ ∃ k,
      0 < pointedProfile M f P cutoff k (.inl i) ∨
      0 < pointedProfile M f Q cutoff k (.inl i)) :
    ∃ i ∈ P.val.1, i ∉ Q.val.1 ∧
      (0 < pointedProfile M f P cutoff (relativeLowerLevel M f cutoff P Q) (.inl i) ∨
       0 < pointedProfile M f Q cutoff (relativeLowerLevel M f cutoff P Q) (.inl i)) := by
  by_cases hz : relativeLowerLevel M f cutoff P Q = 0
  · obtain ⟨i,hi,hq,k,hk⟩ := hsome
    have hb := relativePeak_le_lowerLevel M f cutoff P Q i hi hq
    have hk0 : k = 0 := by
      rcases hk with hk|hk
      · exact Nat.eq_zero_of_le_zero (hz ▸ (relativePeak_bound M f cutoff P i k (ne_of_gt hk)).trans hb.1)
      · exact Nat.eq_zero_of_le_zero (hz ▸ (relativePeak_bound M f cutoff Q i k (ne_of_gt hk)).trans hb.2)
    exact ⟨i,hi,hq,by simpa only [hz,hk0] using hk⟩
  · obtain ⟨j,hj,hq,_⟩ := hsome
    have hn : (P.val.1.toFinset \ Q.val.1.toFinset).Nonempty := ⟨j,by simp [hj,hq]⟩
    obtain ⟨i,hi,he⟩ := Finset.exists_mem_eq_sup _ hn
      (fun i => max (relativePeak M f cutoff P i) (relativePeak M f cutoff Q i))
    have hip : i ∈ P.val.1 := Set.mem_toFinset.mp (Finset.mem_sdiff.mp hi).1
    have hiq : i ∉ Q.val.1 := fun hh => (Finset.mem_sdiff.mp hi).2 (Set.mem_toFinset.mpr hh)
    refine ⟨i,hip,hiq,?_⟩
    change relativeLowerLevel M f cutoff P Q = _ at he
    by_cases hle : relativePeak M f cutoff Q i ≤ relativePeak M f cutoff P i
    · have hh := he.trans (max_eq_left hle)
      have hp : 0 < relativePeak M f cutoff P i := Nat.pos_of_ne_zero (fun hh0 => hz (hh.trans hh0))
      rw [hh]
      exact Or.inl (lt_of_le_of_ne (pointedCosetVector_nonneg M f P _ _)
        (Ne.symm (relativePeak_nonzero_of_pos M f cutoff P i hp)))
    · have hh := he.trans (max_eq_right (lt_of_not_ge hle).le)
      have hp : 0 < relativePeak M f cutoff Q i := Nat.pos_of_ne_zero (fun hh0 => hz (hh.trans hh0))
      rw [hh]
      exact Or.inr (lt_of_le_of_ne (pointedCosetVector_nonneg M f Q _ _)
        (Ne.symm (relativePeak_nonzero_of_pos M f cutoff Q i hp)))

lemma relativeBlock_eq_above_lower {P Q:Deligne M} (h:Q≤P) {k:ℕ}
    (hk:relativeLowerLevel M f cutoff P Q<k) :
    relativeBlock M f U cutoff Q k=relativeBlock M f U cutoff P k := by
  have hv := relativeProfile_eq_above_lower M f cutoff h hk
  have hs (i:S ⊕ Unit) : relativeSign M U (pointedProfile M f Q cutoff) k i =
      relativeSign M U (pointedProfile M f P cutoff) k i :=
    relativeSign_congr_above M U _ _ k
      (fun d hd => relativeProfile_eq_above_lower M f cutoff h (hk.trans_le hd)) i
  have hm : relativeSignMask M f U cutoff Q k = relativeSignMask M f U cutoff P k := by
    funext i
    unfold relativeSignMask
    by_cases hq : ofLex i ∈ Sum.inl '' Q.val.1
    · simp only [hq,Set.image_mono h.1 hq,↓reduceIte,hs]
    · by_cases hp : ofLex i ∈ Sum.inl '' P.val.1
      · obtain ⟨j,hj,he⟩ := hp
        have hjq : j ∉ Q.val.1 := fun hh => hq ⟨j,hh,he⟩
        have hz := relativePeak_above M f cutoff P j
          ((relativePeak_le_lowerLevel M f cutoff P Q j hj hjq).1.trans_lt hk)
        have hsign : relativeSign M U (pointedProfile M f P cutoff) k (.inl j) = 0 := by
          simp only [relativeSign,hz,↓reduceIte]
        simp only [hs,←he,hsign,ite_self]
      · simp only [hq,hp,↓reduceIte]
  unfold relativeBlock
  have hsum : pointedCosetSum M f Q (cutoff+k) = pointedCosetSum M f P (cutoff+k) :=
    congrArg (fun v:S ⊕ Unit → ℝ => ∑ i,v i) hv
  rw [hsum,hv,hm]

lemma relativeHeight_eq_of_opened_zero {P Q:Deligne M} (h:Q≤P)
    (hz : ∀ i ∈ P.val.1, i ∉ Q.val.1 → ∀ k,
      pointedProfile M f P cutoff k (.inl i) = 0 ∧ pointedProfile M f Q cutoff k (.inl i) = 0) :
    relativeHeight M f U cutoff Q = relativeHeight M f U cutoff P := by
  have hv (k:ℕ) : pointedProfile M f Q cutoff k = pointedProfile M f P cutoff k :=
    relativeProfile_eq_of_lower_open M f cutoff h k (fun i hi hq => (hz i hi hq k).2.trans (hz i hi hq k).1.symm)
  apply relativeHeight_eq_of_blocks M f U cutoff
  intro k
  have hs (i:S ⊕ Unit) := relativeSign_congr_above M U _ _ k (fun d _ => hv d) i
  have hm : relativeSignMask M f U cutoff Q k = relativeSignMask M f U cutoff P k := by
    funext i
    unfold relativeSignMask
    rw [hs]
    by_cases hq : ofLex i ∈ Sum.inl '' Q.val.1
    · simp only [hq,Set.image_mono h.1 hq,↓reduceIte]
    · by_cases hp : ofLex i ∈ Sum.inl '' P.val.1
      · obtain ⟨j,hj,he⟩ := hp
        have hjq : j ∉ Q.val.1 := fun hh => hq ⟨j,hh,he⟩
        have hsign : relativeSign M U (pointedProfile M f P cutoff) k (.inl j) = 0 := by
          simp only [relativeSign,(hz j hj hjq k).1,↓reduceIte]
        simp only [←he,hsign,ite_self]
      · simp only [hq,hp,↓reduceIte]
  unfold relativeBlock
  have hsum : pointedCosetSum M f Q (cutoff+k) = pointedCosetSum M f P (cutoff+k) :=
    congrArg (fun v:S ⊕ Unit → ℝ => ∑ i,v i) (hv k)
  rw [hsum,hv,hm]

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_RelativeEligible
attribute [-simp] _root_.OAI.HarmonicArtin.ParabolicIntersections.artinExponent_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.artinMap_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.deligneRightTranslate_type _root_.OAI.HarmonicArtin.ParabolicIntersections.mem_relativeStabilizer _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamily_one _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeArtinHom_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visualFromArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visualToArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visual_smul_vertex _root_.OAI.HarmonicArtin.artinCoxeter_generator _root_.OAI.HarmonicArtin.positiveToArtin_generator _root_.OAI.HarmonicArtin.positiveToArtin_word
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The eligible opened colors in a descending lower face. -/
namespace HarmonicArtin.ParabolicIntersections
open _root_.Matrix _root_.OAI.Matrix
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)
  (U:Set (S ⊕ Unit)) (cutoff:ℤ)

def RelativeEligible (P Q:Deligne M) (i:S) : Prop :=
  i∈P.val.1 ∧ i∉Q.val.1 ∧
  (∀d:ℕ,relativePeak M f cutoff P i<d→pointedProfile M f Q cutoff d (.inl i)=0) ∧
  (pointedProfile M f Q cutoff (relativePeak M f cutoff P i) (.inl i)<pointedProfile M f P cutoff (relativePeak M f cutoff P i) (.inl i) ∨
   pointedProfile M f Q cutoff (relativePeak M f cutoff P i) (.inl i)=pointedProfile M f P cutoff (relativePeak M f cutoff P i) (.inl i) ∧
     relativeSign M U (pointedProfile M f P cutoff) (relativePeak M f cutoff P i) (.inl i)=1)

lemma relative_ineligible_top_ge {P Q:Deligne M}
    (ha:∀i∈P.val.1,i∉Q.val.1→¬RelativeEligible M f U cutoff P Q i) :
    ∀i∈P.val.1,i∉Q.val.1→
      pointedProfile M f P cutoff (relativeLowerLevel M f cutoff P Q) (.inl i)≤
        pointedProfile M f Q cutoff (relativeLowerLevel M f cutoff P Q) (.inl i) := by
  intro i hi hq
  have hb:=relativePeak_le_lowerLevel M f cutoff P Q i hi hq
  rcases eq_or_lt_of_le hb.1 with he|he
  · by_contra hn
    apply ha i hi hq
    refine ⟨hi,hq,?_,Or.inl ?_⟩
    · intro d hd
      exact relativePeak_above M f cutoff Q i (hb.2.trans_lt (he ▸ hd))
    · rw [he]
      exact lt_of_not_ge hn
  · rw [relativePeak_above M f cutoff P i he]
    exact pointedCosetVector_nonneg M f Q _ _

lemma relative_eligible_top_le {P Q:Deligne M}
    (ha:∀i∈P.val.1,i∉Q.val.1→RelativeEligible M f U cutoff P Q i) :
    ∀i∈P.val.1,i∉Q.val.1→
      pointedProfile M f Q cutoff (relativeLowerLevel M f cutoff P Q) (.inl i)≤
        pointedProfile M f P cutoff (relativeLowerLevel M f cutoff P Q) (.inl i) := by
  intro i hi hq
  have hb:=relativePeak_le_lowerLevel M f cutoff P Q i hi hq
  have hh:=ha i hi hq
  rcases eq_or_lt_of_le hb.1 with he|he
  · rcases hh.2.2.2 with hl|⟨hl,_⟩
    · rw [he] at hl; exact hl.le
    · rw [he] at hl; exact hl.le
  · rw [relativePeak_above M f cutoff P i he,hh.2.2.1 _ he]

lemma relativeSign_eq_at_lower_tie {P Q:Deligne M} (h:Q≤P)
    (hv:pointedProfile M f Q cutoff (relativeLowerLevel M f cutoff P Q)=pointedProfile M f P cutoff (relativeLowerLevel M f cutoff P Q))
    (i:S⊕Unit) : relativeSign M U (pointedProfile M f Q cutoff) (relativeLowerLevel M f cutoff P Q) i=
      relativeSign M U (pointedProfile M f P cutoff) (relativeLowerLevel M f cutoff P Q) i := by
  apply relativeSign_congr_above M U
  intro d hd
  rcases eq_or_lt_of_le hd with rfl|hd
  · exact hv
  · exact relativeProfile_eq_above_lower M f cutoff h hd

lemma relative_ineligible_tie_sign {P Q:Deligne M} (i:S) (hi:i∈P.val.1) (hq:i∉Q.val.1)
    (ha:¬RelativeEligible M f U cutoff P Q i)
    (he:relativePeak M f cutoff P i=relativeLowerLevel M f cutoff P Q)
    (hv:pointedProfile M f Q cutoff (relativeLowerLevel M f cutoff P Q)=pointedProfile M f P cutoff (relativeLowerLevel M f cutoff P Q))
    (hp : 0 < pointedProfile M f P cutoff (relativeLowerLevel M f cutoff P Q) (.inl i)) :
    relativeSign M U (pointedProfile M f P cutoff) (relativeLowerLevel M f cutoff P Q) (.inl i)= -1 := by
  have hn:relativeSign M U (pointedProfile M f P cutoff) (relativeLowerLevel M f cutoff P Q) (.inl i)≠1:=by
    intro hs
    apply ha
    refine ⟨hi,hq,?_,Or.inr ⟨?_,?_⟩⟩
    · intro d hd
      exact relativePeak_above M f cutoff Q i ((relativePeak_le_lowerLevel M f cutoff P Q i hi hq).2.trans_lt (he ▸ hd))
    · rw [he,hv]
    · rwa [he]
  dsimp only [relativeSign] at hn ⊢
  rw [ite_eq_right (ne_of_gt hp)] at hn ⊢
  split_ifs with hs
  · rw [ite_eq_left hs] at hn
    exact (hn rfl).elim
  · rfl

lemma relative_eligible_tie_sign {P Q:Deligne M} (i:S)
    (ha:RelativeEligible M f U cutoff P Q i) (he:relativePeak M f cutoff P i=relativeLowerLevel M f cutoff P Q)
    (hv:pointedProfile M f Q cutoff (relativeLowerLevel M f cutoff P Q)=pointedProfile M f P cutoff (relativeLowerLevel M f cutoff P Q)) :
    relativeSign M U (pointedProfile M f P cutoff) (relativeLowerLevel M f cutoff P Q) (.inl i)=1 := by
  rcases ha.2.2.2 with hl|⟨_,hs⟩
  · rw [he,hv] at hl
    exact (lt_irrefl _ hl).elim
  · rwa [he] at hs


lemma relativeEligible_positive {P Q:Deligne M} {i:S}
    (h:RelativeEligible M f U cutoff P Q i) :
    0 < pointedProfile M f P cutoff (relativePeak M f cutoff P i) (.inl i) := by
  rcases h.2.2.2 with hl | ⟨_,hs⟩
  · exact lt_of_le_of_lt (pointedCosetVector_nonneg M f Q _ _) hl
  · by_contra hn
    have hz : pointedProfile M f P cutoff (relativePeak M f cutoff P i) (.inl i) = 0 :=
      le_antisymm (le_of_not_gt hn) (pointedCosetVector_nonneg M f P _ _)
    simp only [relativeSign,hz,↓reduceIte] at hs
    norm_num at hs

lemma relativeLowerLevel_prescribed_at_tie {P Q:Deligne M}
    (hsome : ∃ i ∈ P.val.1, i ∉ Q.val.1 ∧ ∃ k,
      0 < pointedProfile M f P cutoff k (.inl i) ∨
      0 < pointedProfile M f Q cutoff k (.inl i))
    (hv:pointedProfile M f Q cutoff (relativeLowerLevel M f cutoff P Q) =
        pointedProfile M f P cutoff (relativeLowerLevel M f cutoff P Q)) :
    ∃ i ∈ P.val.1, i ∉ Q.val.1 ∧ relativePeak M f cutoff P i = relativeLowerLevel M f cutoff P Q ∧
      0 < pointedProfile M f P cutoff (relativeLowerLevel M f cutoff P Q) (.inl i) := by
  obtain ⟨i,hi,hq,hp⟩ := relativeLowerLevel_attained M f cutoff P Q hsome
  have hn : 0 < pointedProfile M f P cutoff (relativeLowerLevel M f cutoff P Q) (.inl i) := by
    rcases hp with hp|hp
    · exact hp
    · rwa [hv] at hp
  exact ⟨i,hi,hq,le_antisymm (relativePeak_le_lowerLevel M f cutoff P Q i hi hq).1
    (relativePeak_bound M f cutoff P i _ (ne_of_gt hn)),hn⟩

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_RelativeLowerComparison
attribute [-simp] _root_.OAI.HarmonicArtin.ParabolicIntersections.artinExponent_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.artinMap_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.deligneRightTranslate_type _root_.OAI.HarmonicArtin.ParabolicIntersections.mem_relativeStabilizer _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamily_one _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeArtinHom_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visualFromArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visualToArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visual_smul_vertex _root_.OAI.HarmonicArtin.artinCoxeter_generator _root_.OAI.HarmonicArtin.positiveToArtin_generator _root_.OAI.HarmonicArtin.positiveToArtin_word
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Strict lower-neighbor comparisons for the relative height. -/
namespace HarmonicArtin.ParabolicIntersections
open _root_.Matrix _root_.OAI.Matrix
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)
  (U:Set (S ⊕ Unit)) (cutoff:ℤ)

lemma relativeMasks_ne_of_open_sign {P Q:Deligne M} (i:S) (hi:i∈P.val.1) (hq:i∉Q.val.1)
    (k:ℕ) (hs : relativeSign M U (pointedProfile M f P cutoff) k (.inl i) ≠ 0) :
    relativeSignMask M f U cutoff Q k ≠ relativeSignMask M f U cutoff P k := by
  intro heq
  have hP : (.inl i:S ⊕ Unit) ∈ Sum.inl '' P.val.1 := ⟨i,hi,rfl⟩
  have hQ : (.inl i:S ⊕ Unit) ∉ Sum.inl '' Q.val.1 := by
    rintro ⟨j,hj,he⟩
    exact hq (Sum.inl.inj he ▸ hj)
  have hz := congrFun heq (toLex (.inl i))
  simp only [relativeSignMask,ofLex_toLex,hP,hQ,↓reduceIte] at hz
  exact hs hz.symm

lemma relativeLower_ineligible_le {P Q:Deligne M} (h:Q<P)
    (ha:∀i∈P.val.1,i∉Q.val.1→¬RelativeEligible M f U cutoff P Q i) :
    relativeHeight M f U cutoff P ≤ relativeHeight M f U cutoff Q := by
  by_cases hsome : ∃ i ∈ P.val.1, i ∉ Q.val.1 ∧ ∃ k,
      0 < pointedProfile M f P cutoff k (.inl i) ∨
      0 < pointedProfile M f Q cutoff k (.inl i)
  · apply le_of_lt
    apply (relativeHeight_lt_iff M f U cutoff P Q).mpr
    refine ⟨relativeLowerLevel M f cutoff P Q,
      fun d hd => (relativeBlock_eq_above_lower M f U cutoff h.le hd).symm,?_⟩
    let H := relativeLowerLevel M f cutoff P Q
    by_cases hv : pointedProfile M f Q cutoff H = pointedProfile M f P cutoff H
    · have hsEq := relativeSign_eq_at_lower_tie M f U cutoff h.le hv
      have hs (i:S) (hi:i∈P.val.1) (hq:i∉Q.val.1) :
          relativeSign M U (pointedProfile M f P cutoff) H (.inl i) ≤ 0 := by
        by_cases hz : pointedProfile M f P cutoff H (.inl i) = 0
        · simp only [relativeSign,hz,↓reduceIte,le_refl]
        · have hp := lt_of_le_of_ne (pointedCosetVector_nonneg M f P (cutoff+H) (.inl i)) (Ne.symm hz)
          have he : relativePeak M f cutoff P i = H := le_antisymm
            (relativePeak_le_lowerLevel M f cutoff P Q i hi hq).1
            (relativePeak_bound M f cutoff P i H hz)
          rw [relative_ineligible_tie_sign M f U cutoff i hi hq (ha i hi hq) he hv hp]
          norm_num
      have hm := relative_mask_upper_nonpos M f U cutoff h.le H
        (fun i => (hsEq i).symm) (fun i hi hq => by rw [hsEq]; exact hs i hi hq)
      obtain ⟨i,hi,hq,he,hp⟩ := relativeLowerLevel_prescribed_at_tie M f cutoff hsome hv
      have hsign := relative_ineligible_tie_sign M f U cutoff i hi hq (ha i hi hq) he hv hp
      have hn := relativeMasks_ne_of_open_sign M f U cutoff i hi hq H (by rw [hsign]; norm_num)
      exact relativeBlock_lt_of_mask M f U cutoff hv.symm (lt_of_le_of_ne hm (Ne.symm hn))
    · exact Prod.Lex.lt_iff.mpr (Or.inl (harmonic_sum_lt_of_lt _ _
        (relativeProfile_lower_comparison M f cutoff h.le H (relative_ineligible_top_ge M f U cutoff ha))
        (Ne.symm hv)))
  · have hz : ∀ i ∈ P.val.1, i ∉ Q.val.1 → ∀ k,
        pointedProfile M f P cutoff k (.inl i) = 0 ∧ pointedProfile M f Q cutoff k (.inl i) = 0 := by
      intro i hi hq k
      constructor
      · exact le_antisymm (le_of_not_gt (fun hp => hsome ⟨i,hi,hq,k,Or.inl hp⟩))
          (pointedCosetVector_nonneg M f P _ _)
      · exact le_antisymm (le_of_not_gt (fun hp => hsome ⟨i,hi,hq,k,Or.inr hp⟩))
          (pointedCosetVector_nonneg M f Q _ _)
    exact (relativeHeight_eq_of_opened_zero M f U cutoff h.le hz).symm.le

/-- A descending lower face opens at least one eligible color. -/
theorem relativeLower_descending_has_eligible {P Q:Deligne M} (h:Q<P)
    (he:relativeHeight M f U cutoff Q < relativeHeight M f U cutoff P) :
    ∃ i, RelativeEligible M f U cutoff P Q i := by
  by_contra hn
  exact (not_lt_of_ge (relativeLower_ineligible_le M f U cutoff h
    (fun i _ _ hi => hn ⟨i,hi⟩))) he

/-- Opening only eligible colors strictly decreases height. -/
theorem relativeLower_eligible_descending {P Q:Deligne M} (h:Q<P)
    (ha:∀i∈P.val.1,i∉Q.val.1→RelativeEligible M f U cutoff P Q i) :
    relativeHeight M f U cutoff Q < relativeHeight M f U cutoff P := by
  have hsome : ∃ i ∈ P.val.1, i ∉ Q.val.1 ∧ ∃ k,
      0 < pointedProfile M f P cutoff k (.inl i) ∨
      0 < pointedProfile M f Q cutoff k (.inl i) := by
    obtain ⟨i,hi,hq⟩ := Set.exists_of_ssubset (deligne_lt_type M h)
    exact ⟨i,hi,hq,relativePeak M f cutoff P i,Or.inl (relativeEligible_positive M f U cutoff (ha i hi hq))⟩
  apply (relativeHeight_lt_iff M f U cutoff Q P).mpr
  refine ⟨relativeLowerLevel M f cutoff P Q,
    fun d hd => relativeBlock_eq_above_lower M f U cutoff h.le hd,?_⟩
  let H := relativeLowerLevel M f cutoff P Q
  by_cases hv : pointedProfile M f Q cutoff H = pointedProfile M f P cutoff H
  · have hsEq := relativeSign_eq_at_lower_tie M f U cutoff h.le hv
    have hs (i:S) (hi:i∈P.val.1) (hq:i∉Q.val.1) :
        0 ≤ relativeSign M U (pointedProfile M f P cutoff) H (.inl i) := by
      rcases eq_or_lt_of_le (relativePeak_le_lowerLevel M f cutoff P Q i hi hq).1 with he|he
      · rw [relative_eligible_tie_sign M f U cutoff i (ha i hi hq) he hv]
        norm_num
      · have hz : pointedProfile M f P cutoff H (.inl i) = 0 := relativePeak_above M f cutoff P i he
        simp only [relativeSign,hz,↓reduceIte,le_refl]
    have hm := relative_mask_upper_nonneg M f U cutoff h.le H
      (fun i => (hsEq i).symm) (fun i hi hq => by rw [hsEq]; exact hs i hi hq)
    obtain ⟨i,hi,hq,he,_⟩ := relativeLowerLevel_prescribed_at_tie M f cutoff hsome hv
    have hsign := relative_eligible_tie_sign M f U cutoff i (ha i hi hq) he hv
    have hn := relativeMasks_ne_of_open_sign M f U cutoff i hi hq H (by rw [hsign]; norm_num)
    exact relativeBlock_lt_of_mask M f U cutoff hv (lt_of_le_of_ne hm hn)
  · exact Prod.Lex.lt_iff.mpr (Or.inl (harmonic_sum_lt_of_lt _ _
      (relativeProfile_lower_comparison_rev M f cutoff h.le H (relative_eligible_top_le M f U cutoff ha)) hv))

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_RelativeLowerRetraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Closing the ineligible colors retracts descending lower faces onto eligible faces. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)
  (U:Set (S ⊕ Unit)) (cutoff:ℤ)

abbrev RelativeDescendingLower (P:Deligne M) := {Q:Deligne M // Q<P ∧ relativeHeight M f U cutoff Q < relativeHeight M f U cutoff P}

def relativeEligibleSet (P Q:Deligne M) : Set S := {i | RelativeEligible M f U cutoff P Q i}

lemma relativeEligible_shared {P Q R:Deligne M} (h:Q≤R) (i:S) (hi:i∉R.val.1) :
    RelativeEligible M f U cutoff P Q i ↔ RelativeEligible M f U cutoff P R i := by
  have hq:i∉Q.val.1:=fun hh=>hi (h.1 hh)
  have he(k:ℕ):pointedProfile M f Q cutoff k (.inl i)=pointedProfile M f R cutoff k (.inl i):=
    (pointedCosetVector_upper_outside M f h (cutoff+k) (.inl i) (by
      rintro ⟨j,hj,hh⟩; exact hi ((Sum.inl_injective hh) ▸ hj))).symm
  simp only [RelativeEligible,he,hq,hi,not_false_eq_true,true_and]

noncomputable def relativeLowerClose (P Q:Deligne M) : Deligne M :=
  sourceCoset M (P.val.1 \ relativeEligibleSet M f U cutoff P Q)
    (source_spherical_mono M Set.sdiff_subset P.property.1) (sourceCosetRepresentative M Q)

lemma le_relativeLowerClose {P Q:Deligne M} (h:Q≤P) : Q≤ relativeLowerClose M f U cutoff P Q := by
  have he:=sourceCoset_eq M Q _ (sourceCosetRepresentative_mem M Q)
  nth_rw 1 [←he]
  exact sourceCoset_le M (show Q.val.1⊆P.val.1 \ relativeEligibleSet M f U cutoff P Q from
    fun i hi=>⟨h.1 hi,fun he=>he.2.1 hi⟩) _

lemma relativeLowerClose_le {P Q:Deligne M} (h:Q≤P) : relativeLowerClose M f U cutoff P Q≤P := by
  have he:=sourceCoset_eq M P _ (h.2 (sourceCosetRepresentative_mem M Q))
  calc
    relativeLowerClose M f U cutoff P Q≤ sourceCoset M P.val.1 P.property.1 (sourceCosetRepresentative M Q):=
      sourceCoset_le M Set.sdiff_subset _
    _=P:=he

lemma relativeLowerClose_all_eligible {P Q:Deligne M} (h:Q≤P) :
    ∀i∈P.val.1,i∉(relativeLowerClose M f U cutoff P Q).val.1→RelativeEligible M f U cutoff P (relativeLowerClose M f U cutoff P Q) i := by
  intro i hi hn
  have hh:RelativeEligible M f U cutoff P Q i:=by
    by_contra he
    exact hn ⟨hi,he⟩
  exact (relativeEligible_shared M f U cutoff (le_relativeLowerClose M f U cutoff h) i hn).mp hh

lemma relativeLowerClose_mem {P Q:Deligne M} (h:Q<P) (he:relativeHeight M f U cutoff Q < relativeHeight M f U cutoff P) :
    relativeLowerClose M f U cutoff P Q<P ∧ relativeHeight M f U cutoff (relativeLowerClose M f U cutoff P Q) < relativeHeight M f U cutoff P := by
  obtain ⟨i,hi⟩:=relativeLower_descending_has_eligible M f U cutoff h he
  have hl:relativeLowerClose M f U cutoff P Q<P:=by
    apply lt_of_le_of_ne (relativeLowerClose_le M f U cutoff h.le)
    intro hh
    have ht:=congrArg (fun K:Deligne M=>K.val.1) hh
    have hm:i∈(relativeLowerClose M f U cutoff P Q).val.1:=by rw [ht]; exact hi.1
    exact hm.2 hi
  exact ⟨hl,relativeLower_eligible_descending M f U cutoff hl (relativeLowerClose_all_eligible M f U cutoff h.le)⟩

lemma relativeLowerClose_monotone {P Q R:Deligne M} (h:Q≤R) (hr:R≤P) :
    relativeLowerClose M f U cutoff P Q≤ relativeLowerClose M f U cutoff P R := by
  have ht:P.val.1 \ relativeEligibleSet M f U cutoff P Q⊆P.val.1 \ relativeEligibleSet M f U cutoff P R:=by
    intro i hi
    refine ⟨hi.1,?_⟩
    intro hh
    exact hi.2 ((relativeEligible_shared M f U cutoff h i hh.2.1).mpr hh)
  have hx:(sourceCosetRepresentative M Q)∈(relativeLowerClose M f U cutoff P R).val.2:=
    (le_relativeLowerClose M f U cutoff hr).2 (h.2 (sourceCosetRepresentative_mem M Q))
  have he:=sourceCoset_eq M (relativeLowerClose M f U cutoff P R) _ hx
  rw [←he]
  exact sourceCoset_le M ht _

noncomputable def relativeLowerRetraction (P:Deligne M) :
    RelativeDescendingLower M f U cutoff P →o RelativeDescendingLower M f U cutoff P where
  toFun Q:=⟨relativeLowerClose M f U cutoff P Q,relativeLowerClose_mem M f U cutoff Q.property.1 Q.property.2⟩
  monotone':=fun _ R h=>relativeLowerClose_monotone M f U cutoff h R.property.1.le

lemma le_relativeLowerRetraction (P:Deligne M) (Q:RelativeDescendingLower M f U cutoff P) :
    Q≤ relativeLowerRetraction M f U cutoff P Q := le_relativeLowerClose M f U cutoff Q.property.1.le

lemma relativeLowerClose_eq_of_all {P Q:Deligne M}
    (he:∀i∈P.val.1,i∉Q.val.1→RelativeEligible M f U cutoff P Q i) (h:Q≤P) : relativeLowerClose M f U cutoff P Q=Q := by
  symm
  apply deligne_eq_of_le_type_eq M (le_relativeLowerClose M f U cutoff h)
  ext i
  change i∈Q.val.1 ↔ i∈P.val.1 ∧ ¬RelativeEligible M f U cutoff P Q i
  constructor
  · intro hi
    exact ⟨h.1 hi,fun hh=>hh.2.1 hi⟩
  · rintro ⟨hi,hn⟩
    by_contra hq
    exact hn (he i hi hq)


end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_RelativeAllEligible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ParabolicIntersections
open Simplicial CategoryTheory
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)
  (U:Set (S ⊕ Unit)) (cutoff:ℤ)

abbrev RelativeAllEligibleLower (P:Deligne M) :=
  {Q:Deligne M // Q<P ∧ ∀i∈P.val.1,i∉Q.val.1→RelativeEligible M f U cutoff P Q i}

noncomputable def relativeAllEligibleInclusion (P:Deligne M) :
    RelativeAllEligibleLower M f U cutoff P →o RelativeDescendingLower M f U cutoff P where
  toFun Q:=⟨Q.val,Q.property.1,relativeLower_eligible_descending M f U cutoff Q.property.1 Q.property.2⟩
  monotone':=fun _ _ h=>h

noncomputable def relativeAllEligibleProjection (P:Deligne M) :
    RelativeDescendingLower M f U cutoff P →o RelativeAllEligibleLower M f U cutoff P where
  toFun Q:=⟨relativeLowerClose M f U cutoff P Q,(relativeLowerClose_mem M f U cutoff Q.property.1 Q.property.2).1,
    relativeLowerClose_all_eligible M f U cutoff Q.property.1.le⟩
  monotone':=fun _ R h=>relativeLowerClose_monotone M f U cutoff h R.property.1.le

lemma relativeAllEligible_retract (P:Deligne M) :
    (relativeAllEligibleProjection M f U cutoff P).comp (relativeAllEligibleInclusion M f U cutoff P)=OrderHom.id := by
  apply OrderHom.ext
  funext Q
  apply Subtype.ext
  exact relativeLowerClose_eq_of_all M f U cutoff Q.property.2 Q.property.1.le

noncomputable def relativeEarlierLower_equiv_allEligible (P:Deligne M) :
    ContinuousMap.HomotopyEquiv |nerve (RelativeDescendingLower M f U cutoff P)| |nerve (RelativeAllEligibleLower M f U cutoff P)| :=
  nerveOrderRetractionEquiv (relativeAllEligibleProjection M f U cutoff P) (relativeAllEligibleInclusion M f U cutoff P)
    (relativeAllEligible_retract M f U cutoff P) (le_relativeLowerRetraction M f U cutoff P)


end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_RelativeEligibleWithin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ParabolicIntersections
open Simplicial CategoryTheory
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)
  (U:Set (S ⊕ Unit)) (cutoff:ℤ)

abbrev RelativeEligibleWithin (P R:Deligne M) :=
  {Q:Deligne M // Q≤R ∧ ∀i∈R.val.1,i∉Q.val.1→RelativeEligible M f U cutoff P Q i}

instance relativeEligibleWithinTop (P R:Deligne M) : OrderTop (RelativeEligibleWithin M f U cutoff P R) where
  top:=⟨R,le_rfl,fun _ h hn=>(hn h).elim⟩
  le_top:=fun Q=>Q.property.1

lemma relativeEligibleProduct_left (Ref:Deligne M) (B C:Set S) (hT:IsSpherical M (B∪C))
    (hd:Disjoint B C) (hc:∀s∈B,∀t∈C,M s t=2) (x:Artin M)
    (A:SourceCosetBelow M B (source_spherical_mono M Set.subset_union_left hT) x ×
      SourceCosetBelow M C (source_spherical_mono M Set.subset_union_right hT) x)
    (i:S) (hi:i∈B) :
    RelativeEligible M f U cutoff Ref (sourceCosetProductFun M B C hT x A).val i ↔ RelativeEligible M f U cutoff Ref A.1.val i := by
  have hn:i∉(sourceCosetProductFun M B C hT x A).val.val.1 ↔i∉A.1.val.val.1:=by
    constructor
    · exact fun h h'=>h (Or.inl h')
    · intro h
      rintro (h'|h')
      · exact h h'
      · exact Set.disjoint_left.mp hd hi (A.2.property.1 h')
  by_cases ho:i∉A.1.val.val.1
  · have he (k:ℕ) : pointedProfile M f (sourceCosetProductFun M B C hT x A).val cutoff k (.inl i) =
        pointedProfile M f A.1.val cutoff k (.inl i) :=
        pointedCosetProduct_open_left M f B C hT hd hc x A i hi ho (cutoff+k)
    simp only [RelativeEligible,hn,he]
  · constructor
    · intro h;exact (ho (hn.mp h.2.1)).elim
    · intro h;exact (ho h.2.1).elim

lemma relativeEligibleProduct_right (Ref:Deligne M) (B C:Set S) (hT:IsSpherical M (B∪C))
    (hd:Disjoint B C) (x:Artin M)
    (A:SourceCosetBelow M B (source_spherical_mono M Set.subset_union_left hT) x ×
      SourceCosetBelow M C (source_spherical_mono M Set.subset_union_right hT) x)
    (i:S) (hi:i∈C) :
    RelativeEligible M f U cutoff Ref (sourceCosetProductFun M B C hT x A).val i ↔ RelativeEligible M f U cutoff Ref A.2.val i := by
  have hn:i∉(sourceCosetProductFun M B C hT x A).val.val.1 ↔i∉A.2.val.val.1:=by
    constructor
    · exact fun h h'=>h (Or.inr h')
    · intro h
      rintro (h'|h')
      · exact Set.disjoint_left.mp hd (A.1.property.1 h') hi
      · exact h h'
  by_cases ho:i∉A.2.val.val.1
  · have he (k:ℕ) : pointedProfile M f (sourceCosetProductFun M B C hT x A).val cutoff k (.inl i) =
        pointedProfile M f A.2.val cutoff k (.inl i) :=
        pointedCosetProduct_open_right M f B C hT hd x A i hi ho (cutoff+k)
    simp only [RelativeEligible,hn,he]
  · constructor
    · intro h;exact (ho (hn.mp h.2.1)).elim
    · intro h;exact (ho h.2.1).elim

lemma relativeEligibleProduct_condition (Ref:Deligne M) (B C:Set S) (hT:IsSpherical M (B∪C))
    (hd:Disjoint B C) (hc:∀s∈B,∀t∈C,M s t=2) (x:Artin M)
    (A:SourceCosetBelow M B (source_spherical_mono M Set.subset_union_left hT) x ×
      SourceCosetBelow M C (source_spherical_mono M Set.subset_union_right hT) x) :
    (∀i∈B∪C,i∉(sourceCosetProductFun M B C hT x A).val.val.1→
      RelativeEligible M f U cutoff Ref (sourceCosetProductFun M B C hT x A).val i) ↔
    (∀i∈B,i∉A.1.val.val.1→RelativeEligible M f U cutoff Ref A.1.val i) ∧
    (∀i∈C,i∉A.2.val.val.1→RelativeEligible M f U cutoff Ref A.2.val i) := by
  constructor
  · intro h
    constructor
    · intro i hi ho
      apply (relativeEligibleProduct_left M f U cutoff Ref B C hT hd hc x A i hi).mp
      apply h i (Or.inl hi)
      rintro (ha|ha)
      · exact ho ha
      · exact Set.disjoint_left.mp hd hi (A.2.property.1 ha)
    · intro i hi ho
      apply (relativeEligibleProduct_right M f U cutoff Ref B C hT hd x A i hi).mp
      apply h i (Or.inr hi)
      rintro (ha|ha)
      · exact Set.disjoint_left.mp hd (A.1.property.1 ha) hi
      · exact ho ha
  · rintro ⟨h,h'⟩ i (hi|hi) ho
    · exact (relativeEligibleProduct_left M f U cutoff Ref B C hT hd hc x A i hi).mpr
        (h i hi (fun hh=>ho (Or.inl hh)))
    · exact (relativeEligibleProduct_right M f U cutoff Ref B C hT hd x A i hi).mpr
        (h' i hi (fun hh=>ho (Or.inr hh)))

noncomputable def relativeEligibleProductFun (Ref:Deligne M) (B C:Set S) (hT:IsSpherical M (B∪C))
    (hd:Disjoint B C) (hc:∀s∈B,∀t∈C,M s t=2) (x:Artin M)
    (A:RelativeEligibleWithin M f U cutoff Ref (sourceCoset M B (source_spherical_mono M Set.subset_union_left hT) x) ×
      RelativeEligibleWithin M f U cutoff Ref (sourceCoset M C (source_spherical_mono M Set.subset_union_right hT) x)) :
    RelativeEligibleWithin M f U cutoff Ref (sourceCoset M (B∪C) hT x) := by
  let a:SourceCosetBelow M B (source_spherical_mono M Set.subset_union_left hT) x:=⟨A.1.val,A.1.property.1⟩
  let b:SourceCosetBelow M C (source_spherical_mono M Set.subset_union_right hT) x:=⟨A.2.val,A.2.property.1⟩
  let p:=sourceCosetProductFun M B C hT x (a,b)
  exact ⟨p.val,p.property,(relativeEligibleProduct_condition M f U cutoff Ref B C hT hd hc x (a,b)).mpr
    ⟨A.1.property.2,A.2.property.2⟩⟩

lemma relativeEligibleProductFun_le_iff (Ref:Deligne M) (B C:Set S) (hT:IsSpherical M (B∪C))
    (hd:Disjoint B C) (hc:∀s∈B,∀t∈C,M s t=2) (x:Artin M)
    (A D:RelativeEligibleWithin M f U cutoff Ref (sourceCoset M B (source_spherical_mono M Set.subset_union_left hT) x) ×
      RelativeEligibleWithin M f U cutoff Ref (sourceCoset M C (source_spherical_mono M Set.subset_union_right hT) x)) :
    relativeEligibleProductFun M f U cutoff Ref B C hT hd hc x A ≤ relativeEligibleProductFun M f U cutoff Ref B C hT hd hc x D ↔ A≤D :=
  sourceCosetProductFun_le_iff M B C hT hd hc x
    (⟨A.1.val,A.1.property.1⟩,⟨A.2.val,A.2.property.1⟩)
    (⟨D.1.val,D.1.property.1⟩,⟨D.2.val,D.2.property.1⟩)

lemma relativeEligibleProductFun_surjective (Ref:Deligne M) (B C:Set S) (hT:IsSpherical M (B∪C))
    (hd:Disjoint B C) (hc:∀s∈B,∀t∈C,M s t=2) (x:Artin M) :
    Function.Surjective (relativeEligibleProductFun M f U cutoff Ref B C hT hd hc x) := by
  intro D
  obtain ⟨⟨a,b⟩,he⟩:=sourceCosetProductFun_surjective M B C hT hd hc x ⟨D.val,D.property.1⟩
  have hprop:∀i∈B∪C,i∉(sourceCosetProductFun M B C hT x (a,b)).val.val.1→
      RelativeEligible M f U cutoff Ref (sourceCosetProductFun M B C hT x (a,b)).val i:=by
    rw [he]
    exact D.property.2
  have hh:=(relativeEligibleProduct_condition M f U cutoff Ref B C hT hd hc x (a,b)).mp hprop
  refine ⟨(⟨a.val,a.property,hh.1⟩,⟨b.val,b.property,hh.2⟩),?_⟩
  apply Subtype.ext
  change (sourceCosetProductFun M B C hT x (a,b)).val=D.val
  exact congrArg Subtype.val he

noncomputable def relativeEligibleProduct (Ref:Deligne M) (B C:Set S) (hT:IsSpherical M (B∪C))
    (hd:Disjoint B C) (hc:∀s∈B,∀t∈C,M s t=2) (x:Artin M) :
    (RelativeEligibleWithin M f U cutoff Ref (sourceCoset M B (source_spherical_mono M Set.subset_union_left hT) x) ×
      RelativeEligibleWithin M f U cutoff Ref (sourceCoset M C (source_spherical_mono M Set.subset_union_right hT) x)) ≃o
    RelativeEligibleWithin M f U cutoff Ref (sourceCoset M (B∪C) hT x) :=
  OrderIso.ofSurjective
    (OrderEmbedding.ofMapLEIff (relativeEligibleProductFun M f U cutoff Ref B C hT hd hc x)
      (relativeEligibleProductFun_le_iff M f U cutoff Ref B C hT hd hc x))
    (relativeEligibleProductFun_surjective M f U cutoff Ref B C hT hd hc x)

noncomputable def relativeEligiblePuncture (P:Deligne M) :
    {Q:RelativeEligibleWithin M f U cutoff P P //Q≠⊤} ≃o RelativeAllEligibleLower M f U cutoff P where
  toFun Q:=⟨Q.val.val,lt_of_le_of_ne Q.val.property.1 (fun he=>Q.property (Subtype.ext he)),Q.val.property.2⟩
  invFun Q:=⟨⟨Q.val,Q.property.1.le,Q.property.2⟩,by intro he;exact Q.property.1.ne (congrArg Subtype.val he)⟩
  left_inv _:=rfl
  right_inv _:=rfl
  map_rel_iff':=Iff.rfl


end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_RelativeEligibleFactor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)
  (U:Set (S ⊕ Unit)) (cutoff:ℤ)

lemma relativeEligible_factor_iff (P R V:Deligne M) (hRP:R.val.1⊆P.val.1)
    (q:ℕ) (strict:Bool) (hp:∀i∈R.val.1,relativePeak M f cutoff P i=q)
    (hs:∀i∈R.val.1,relativeSign M U (pointedProfile M f P cutoff) q (.inl i)=if strict then -1 else 1)
    (hv:∀i∈R.val.1,pointedProfile M f R cutoff q (.inl i)=pointedProfile M f P cutoff q (.inl i))
    (i:S) (hi:i∈R.val.1) (ho:i∉V.val.1) :
    RelativeEligible M f U cutoff P V i ↔
      (∀d:ℤ,cutoff+(q:ℤ)<d→pointedCosetVector M f V d (.inl i)=0) ∧
      (if strict then pointedProfile M f V cutoff q (.inl i)<pointedProfile M f R cutoff q (.inl i)
        else pointedProfile M f V cutoff q (.inl i) ≤ pointedProfile M f R cutoff q (.inl i)) := by
  have hcap:(∀d:ℕ,q<d→pointedProfile M f V cutoff d (.inl i)=0) ↔
      (∀d:ℤ,cutoff+(q:ℤ)<d→pointedCosetVector M f V d (.inl i)=0):=by
    constructor
    · intro h d hd
      have hn:0≤d-cutoff:=by omega
      have he:cutoff+((d-cutoff).toNat:ℤ)=d:=by rw [Int.toNat_of_nonneg hn];omega
      rw [←he]
      exact h (d-cutoff).toNat (by omega)
    · intro h d hd
      have hh : (q:ℤ) < d := by exact_mod_cast hd
      exact h (cutoff+d) (by omega)
  simp only [RelativeEligible,hRP hi,ho,true_and,hp i hi,hcap,hs i hi,←hv i hi]
  cases strict <;> simp only [Bool.false_eq_true,↓reduceIte,Int.reduceNeg,Int.reduceEq,not_false_eq_true,true_and,and_true,
    and_false,or_false]
  constructor
  · rintro ⟨ha,hb⟩
    exact ⟨ha,hb.elim le_of_lt le_of_eq⟩
  · rintro ⟨ha,hb⟩
    exact ⟨ha,lt_or_eq_of_le hb⟩

noncomputable def relativeEligibleFactor (P R:Deligne M) (hRP:R.val.1⊆P.val.1)
    (q:ℕ) (strict:Bool) (hp:∀i∈R.val.1,relativePeak M f cutoff P i=q)
    (hs:∀i∈R.val.1,relativeSign M U (pointedProfile M f P cutoff) q (.inl i)=if strict then -1 else 1)
    (hv:∀i∈R.val.1,pointedProfile M f R cutoff q (.inl i)=pointedProfile M f P cutoff q (.inl i)) :
    {V:RelativeEligibleWithin M f U cutoff P R // V≠⊤} ≃o PointedResidue M f strict R (cutoff+q) where
  toFun V:=⟨V.val.val,lt_of_le_of_ne V.val.property.1 (fun he=>V.property (Subtype.ext he)),
    fun i hi ho=>(relativeEligible_factor_iff M f U cutoff P R V.val.val hRP q strict hp hs hv i hi ho).mp
      (V.val.property.2 i hi ho)⟩
  invFun V:=⟨⟨V.val,V.property.1.le,fun i hi ho=>
    (relativeEligible_factor_iff M f U cutoff P R V.val hRP q strict hp hs hv i hi ho).mpr (V.property.2 i hi ho)⟩,
    fun he=>V.property.1.ne (congrArg Subtype.val he)⟩
  left_inv _:=rfl
  right_inv _:=rfl
  map_rel_iff':=by intros;rfl

noncomputable def relativeEligibleProductPuncture (Ref:Deligne M) (B C:Set S) (hT:IsSpherical M (B∪C))
    (hd:Disjoint B C) (hc:∀s∈B,∀t∈C,M s t=2) (x:Artin M) :
    BinaryProductBoundary
      (RelativeEligibleWithin M f U cutoff Ref (sourceCoset M B (source_spherical_mono M Set.subset_union_left hT) x))
      (RelativeEligibleWithin M f U cutoff Ref (sourceCoset M C (source_spherical_mono M Set.subset_union_right hT) x)) ≃o
      {V:RelativeEligibleWithin M f U cutoff Ref (sourceCoset M (B∪C) hT x) //V≠⊤} :=
  { toFun:=fun V=>⟨relativeEligibleProduct M f U cutoff Ref B C hT hd hc x V.val,by
      intro he
      exact V.property ((relativeEligibleProduct M f U cutoff Ref B C hT hd hc x).injective
        (he.trans (relativeEligibleProduct M f U cutoff Ref B C hT hd hc x).map_top.symm))⟩
    invFun:=fun V=>⟨(relativeEligibleProduct M f U cutoff Ref B C hT hd hc x).symm V.val,by
      intro he
      apply V.property
      rw [←(relativeEligibleProduct M f U cutoff Ref B C hT hd hc x).apply_symm_apply V.val,he,
        (relativeEligibleProduct M f U cutoff Ref B C hT hd hc x).map_top]⟩
    left_inv:=fun V=>Subtype.ext ((relativeEligibleProduct M f U cutoff Ref B C hT hd hc x).symm_apply_apply V.val)
    right_inv:=fun V=>Subtype.ext ((relativeEligibleProduct M f U cutoff Ref B C hT hd hc x).apply_symm_apply V.val)
    map_rel_iff':=by intros;exact (relativeEligibleProduct M f U cutoff Ref B C hT hd hc x).map_rel_iff }


end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_RelativeNullBlockData
attribute [-instance] _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ParabolicIntersections
open _root_.Matrix _root_.OAI.Matrix ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)
  (U:Set (S ⊕ Unit)) (cutoff:ℤ)

noncomputable def relativeNullPatch (P:Deligne M) (q:ℕ) (i:S⊕Unit) (v:S⊕Unit) : ℝ :=
  if v∈sourcePositiveComponent M (pointedProfile M f P cutoff q) i then pointedProfile M f P cutoff q v else 0


end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_RelativeLowerConnected
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Comparability paths in the descending lower neighborhood. -/
namespace HarmonicArtin.ParabolicIntersections
open CategoryTheory Simplicial
attribute [local instance] Classical.decEq Classical.propDecidable

variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)
  (U:Set (S ⊕ Unit)) (cutoff:ℤ)

def RelativeStrictLower {Y:Set S} {x:Artin M} (P R:RelativeVertex M Y x) : Prop :=
  R<P ∧ relativeHeight M f U cutoff R.val < relativeHeight M f U cutoff P.val

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_RelativeUpperConnected
attribute [-instance] _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Connected descending upper neighborhoods, using their common active-color extension. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S) (f : S)
  (U : Set (S ⊕ Unit)) (cutoff : ℤ) (Y : Set S) (x : Artin M)

noncomputable def relativeUpperTop (P : RelativeVertex M Y x)
    (hYU : ∀ i ∈ Y, (.inl i : S ⊕ Unit) ∈ U) : RelativeVertex M Y x :=
  relativeVertex M Y (P.val.val.1 ∪ relativeActiveSet M f U cutoff Y P.val)
    (relativeActiveSet_spherical M f U cutoff Y P.val P.property.1 hYU)
    (fun _ hi => hi.elim (fun h => P.property.1 h) (fun h => h.1))
    x (sourceCosetRepresentative M P.val) (P.property.2 (sourceCosetRepresentative_mem M P.val))

noncomputable def relativeUpperClip (P R : RelativeVertex M Y x) : RelativeVertex M Y x :=
  relativeVertex M Y (R.val.val.1 ∩ (P.val.val.1 ∪ relativeActiveSet M f U cutoff Y P.val))
    (source_spherical_mono M Set.inter_subset_left R.val.property.1)
    (fun _ hi => R.property.1 hi.1)
    x (sourceCosetRepresentative M P.val) (P.property.2 (sourceCosetRepresentative_mem M P.val))

def RelativeDescendingUpper (P R : RelativeVertex M Y x) : Prop :=
  P < R ∧ relativeHeight M f U cutoff R.val < relativeHeight M f U cutoff P.val

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_RelativeMinimumContainment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Confinement of the actual categorical stabilizer from a harmonic minimum. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)
  (U:Set (S ⊕ Unit)) (cutoff:ℤ) {Y:Set S} {x:Artin M}

def RelativeMinimum (P:RelativeVertex M Y x) : Prop :=
  ∀ V:RelativeVertex M Y x,relativeHeight M f U cutoff P.val ≤ relativeHeight M f U cutoff V.val

noncomputable def relativeContainingType (Y:Set S) (P:Deligne M) : Set S :=
  relativeVisible M f cutoff Y P ∪ relativeInvisible M f cutoff Y P

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_RelativeFamily
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ParabolicIntersections.artinExponent_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.artinMap_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.deligneRightTranslate_type _root_.OAI.HarmonicArtin.ParabolicIntersections.mem_relativeStabilizer _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamily_one _root_.OAI.HarmonicArtin.ParabolicIntersections.visualFromArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visualToArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visual_smul_vertex _root_.OAI.HarmonicArtin.artinCoxeter_generator _root_.OAI.HarmonicArtin.positiveLift_one _root_.OAI.HarmonicArtin.positiveToArtin_generator _root_.OAI.HarmonicArtin.positiveToArtin_word _root_.OAI.HarmonicArtin.restrictedArtinHom_generator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The relative categorical family of paper 082-03

The family consists of actual bounded-projective homotopy classes in the
extended diagram. Its initial color is the new relative color `f`; the
auxiliary universal color is the one already adjoined by the fusion model.
-/

namespace HarmonicArtin.ParabolicIntersections

variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S) (X : Set S)
local notation "N" => relativeMatrix M X

attribute [local instance] OAI.HarmonicArtin.ParabolicIntersections.instLinearOrderSumUnit_solutions
abbrev RelativeLabel := PointedLabel N
abbrev RelativeClass := PointedClass N
abbrev RelativeFamilySpace := PointedFamilySpace N

noncomputable def relativeAction : Artin M →* Equiv.Perm (RelativeClass M X) :=
  (pointedAction N).comp (relativeArtinHom M X)

noncomputable def relativeInitial : RelativeFamilySpace M X := pointedInitial N (.inr ())

noncomputable def relativeFamily (x : Artin M) : RelativeFamilySpace M X :=
  fun L => relativeAction M X x (relativeInitial M X L)

@[simp] theorem relativeFamily_one : relativeFamily M X 1 = relativeInitial M X := by
  funext L
  simp [relativeFamily]

noncomputable instance relativeFamilyMulAction : MulAction (Artin M) (RelativeFamilySpace M X) where
  smul g F := fun L => relativeAction M X g (F L)
  one_smul F := by
    funext L
    exact congrArg (fun p => p (F L)) (map_one (relativeAction M X))
  mul_smul g h F := by
    funext L
    exact congrArg (fun p => p (F L)) (map_mul (relativeAction M X) g h)

@[simp] theorem relativeFamily_eq_smul (x : Artin M) :
    relativeFamily M X x = x • relativeInitial M X := rfl

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_RelativeInitialStabilizer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The initial stabilizer in the relative diagram

The sole input below is the unrestricted standard-parabolic embedding theorem:
van der Lek, *The Homotopy Type of Complex Hyperplane Complements* (1983),
Chapter II, §4, Theorem 4.13(i). See also Charney–Paris, *Convexity of parabolic
subgroups in Artin groups* (2014), §1, p. 2, https://arxiv.org/abs/1401.7634.
The exact case needed is injectivity of the canonical inclusion from the
original Artin presentation into the presentation with one additional color.
The categorical stabilizer identity is proved below, not assumed.
-/
namespace HarmonicArtin.ParabolicIntersections
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (X:Set S)
attribute [local instance] Classical.decEq Classical.propDecidable

structure VanDerLekRelativeEmbedding : Prop where
  injective : Function.Injective (relativeArtinHom M X)

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_RelativeInvisibleFactor
attribute [-instance] _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Removing the all-level invisible factor in the nonspherical case of §8. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S) (f : S)

/-- Every exterior count below the cutoff is zero. The cutoff is chosen
from the actual finite family, independently of the harmonic minimum. -/
def ExteriorCutoff (Y : Set S) (x : Artin M) (cutoff : ℤ) : Prop :=
  ∀ k, k < cutoff → ∀ v, v ∉ Sum.inl '' Y → pointedMultiplicity M f x k v = 0

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_FoldingGcdInput
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Published gcd input for an admissible folding

Castella, *Admissible submonoids of Artin--Tits monoids* (2008),
Proposition 41(2), states that an admissible folding preserves left and
right gcds. Source: https://arxiv.org/pdf/0804.0704, p. 15.
The field below is exactly its common-left-atom consequence: if two
expanded positive words have a common left atom, their original words
have a common left atom. The folding here is the color partition.
Its required Coxeter admissibility is already established by
`unfoldedHom_right_ascent` (constant ascent sign on every color).

The field involves positive words and braid relations only. It contains
no tests, family action, height, stabilizer, or intersection assertion.
-/
namespace HarmonicArtin.ParabolicIntersections
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open CoxeterExchange Geometric
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "Q" => fusionQuiver m (coxeterFusionEdge M) (coxeterFusionEdge_symm M)

/-- The precise part of published gcd preservation needed below. The
sphericity proof is retained in the type to identify the admissible
finite-type folding to which the source theorem is applied. -/
structure PublishedFoldingGcd (Y : Set S) (_hY : IsSpherical M Y) : Prop where
  common_atom : ∀ (u v : List Y) (α : FusionVertex (V := S⊕Unit) m)
    (r s : List (FusionVertex (V := S⊕Unit) m)),
    PositiveBraidRel Q (fusionExpandedWord m (u.map fun j : Y => (Sum.inl (j:S) : S⊕Unit))) (α::r) →
    PositiveBraidRel Q (fusionExpandedWord m (v.map fun j : Y => (Sum.inl (j:S) : S⊕Unit))) (α::s) →
    ∃ i : Y, PositivePrefix (restrictedMatrix M Y) (positiveGenerator _ i) (wordPositive _ u) ∧
      PositivePrefix (restrictedMatrix M Y) (positiveGenerator _ i) (wordPositive _ v)

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_SphericalCommonExtension
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Common positive extensions with the actual total test-height bound. -/
namespace HarmonicArtin.ParabolicIntersections
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open CoxeterExchange Geometric
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S) (f : S)

noncomputable def restrictedPointedFamily (Y : Set S) (x : Artin M)
    (a : Artin (restrictedMatrix M Y)) : PointedFamilySpace M :=
  pointedFamily M f (restrictedArtinHom M Y a*x)

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_MainIntersection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The main intersection theorems of paper 082-03

The hypotheses are exactly the published inputs documented in
`MeshNilpotence`, `FoldingGcdInput`, `AcyclicTwistInput`, and
`RelativeInitialStabilizer`. All relative-height, positive-height,
stabilizer-containment and rank-induction arguments are proved in this
local development; none of those new assertions is a hypothesis here.
-/
namespace HarmonicArtin.ParabolicIntersections
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S)

/-- Only the published general mesh-algebra, admissible-folding and
acyclic-evaluation facts; see the individual definitions for exact sources. -/
structure PublishedSphericalInputs : Prop where
  mesh : ∀ Y : Set S, IsSpherical M Y →
    MeshNilpotent (fusionQuiver (fusionLabelSize M) (coxeterFusionEdge M)
      (coxeterFusionEdge_symm M)) (fusionColorRegion (fusionLabelSize M) (Sum.inl '' Y))
  folding : ∀ (Y : Set S) (hY : IsSpherical M Y), PublishedFoldingGcd M Y hY
  acyclic : PublishedAcyclicTwist (fusionQuiver (fusionLabelSize M)
    (coxeterFusionEdge M) (coxeterFusionEdge_symm M))

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_ConditionalMain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Main statements with the acyclic-evaluation input already discharged. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [fS : Fintype S] [oS : LinearOrder S] (M : CoxeterMatrix S)

/-- The two remaining published finite-type algebra inputs. -/
structure PublishedSphericalAlgebraInputs : Prop where
  mesh : ∀ Y : Set S, IsSpherical M Y →
    MeshNilpotent (fusionQuiver (fusionLabelSize M) (coxeterFusionEdge M)
      (coxeterFusionEdge_symm M)) (fusionColorRegion (fusionLabelSize M) (Sum.inl '' Y))
  folding : ∀ (Y : Set S) (hY : IsSpherical M Y), PublishedFoldingGcd M Y hY

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_FoldingPositive
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ParabolicIntersections.deligneRightTranslate_type _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedAction_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamily_one _root_.OAI.HarmonicArtin.ParabolicIntersections.positiveMap_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.positiveSupport_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.positiveSupport_mul _root_.OAI.HarmonicArtin.ParabolicIntersections.positiveSupport_one _root_.OAI.HarmonicArtin.ParabolicIntersections.positiveSupport_word
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive-monoid folding and its action on simple elements. These are
proved from the Coxeter word theorem and the established folding geometry. -/
namespace HarmonicArtin.ParabolicIntersections
open CoxeterExchange Geometric
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S)
    (Y : Set S) (hY : IsSpherical M Y)
local notation "R" => restrictedMatrix M Y
local notation "N" => unfoldedMatrix M Y
local notation "m" => fusionLabelSize M

lemma folded_word_product (w : List Y) :
    (w.map (fun i => wordPositive N (fusionExpandedWord m [i]))).prod =
      wordPositive N (fusionExpandedWord m w) := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    rw [List.map_cons,List.prod_cons,ih]
    simpa only [fusionExpandedWord, List.flatMap_cons, List.flatMap_nil, List.append_nil] using
      (wordPositive_append N (fusionExpandedWord m [i]) (fusionExpandedWord m w)).symm

include hY in
lemma folded_positive_relations :
    ∀ a b : FreeMonoid Y, positiveBraidRelations R a b →
      FreeMonoid.lift (fun i => wordPositive N (fusionExpandedWord m [i])) a =
      FreeMonoid.lift (fun i => wordPositive N (fusionExpandedWord m [i])) b := by
  rintro a b ⟨i,j,rfl,rfl⟩
  simp only [FreeMonoid.lift_ofList,folded_word_product]
  let : Finite (R).Group := restricted_finite M Y hY
  obtain ⟨z,hz⟩ := exists_longest (R).toCoxeterSystem
  apply wordPositive_eq_of_reduced N
  · exact unfolded_reducedWord M Y hY _ (alternating_isReduced_of_longest R z hz i j)
  · rw [(R).symmetric i j]
    exact unfolded_reducedWord M Y hY _ (alternating_isReduced_of_longest R z hz j i)
  · exact unfolded_word_eq M Y hY _ _ (altList_braid (R).toCoxeterSystem i j)

noncomputable def foldedPositiveHom : PositiveArtin R →* PositiveArtin N :=
  PresentedMonoid.lift (fun i => wordPositive N (fusionExpandedWord m [i]))
    (folded_positive_relations M Y hY)

@[simp] lemma foldedPositiveHom_generator (i : Y) :
    foldedPositiveHom M Y hY (positiveGenerator R i)=
      wordPositive N (fusionExpandedWord m [i]) := rfl

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_ReducedInputsMain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Main results after discharging the acyclic-twist and folding inputs. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S)

/-- The remaining finite-type input is positive-degree mesh nilpotence. -/
def PublishedMeshInput : Prop :=
  ∀ Y : Set S, IsSpherical M Y →
    MeshNilpotent (fusionQuiver (fusionLabelSize M) (coxeterFusionEdge M)
      (coxeterFusionEdge_symm M)) (fusionColorRegion (fusionLabelSize M) (Sum.inl '' Y))

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_StandardEmbedding
attribute [-instance] _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamilyMulAction _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Injectivity of every finite-rank standard Artin parabolic. -/
namespace HarmonicArtin.ParabolicIntersections
open CoxeterExchange Geometric
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] (M : CoxeterMatrix S) (J : Set S)
local notation "R" => restrictedMatrix M J

noncomputable def parabolicState (a : Artin R) : M.Group × Artin R :=
  (restrictionHom M J (artinCoxeter R a),a)

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_SphericalMesh
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Discharging the finite spherical mesh input for the actual fusion quiver. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "U" => (fun Y : Set S => fusionColorRegion (V := S⊕Unit) m (Sum.inl '' Y))

noncomputable def sphericalRegionEquiv (Y : Set S) :
    (Y × FusionLabel m) ≃ U Y :=
  (Equiv.ofInjective (unfoldedInclusion M Y) (unfoldedInclusion_injective M Y)).trans
    (Equiv.setCongr (unfoldedInclusion_range M Y))

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_VisualTrivialSegment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The visual tree has a segment with trivial pointwise stabilizer.
This proves the segment step in CMMW (2026), Theorem 3.2, using the
unconditional parabolic intersection theorem and rank descent. -/
namespace HarmonicArtin.ParabolicIntersections
open TreeAction
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S) (Y Z : Set S)
variable [hSplit : Fact (IsVisualSplit M Y Z)]
noncomputable local instance instMulActionArtinVisualVertex_2 : MulAction (Artin M) (VisualVertex M Y Z) :=
  visualAction M Y Z hSplit.out

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_VisualFactorMalnormal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weak malnormality for the vertex factors, and hence their parabolics. -/
namespace HarmonicArtin.ParabolicIntersections
open TreeAction
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S) (Y Z : Set S)
variable [hSplit : Fact (IsVisualSplit M Y Z)]
noncomputable local instance instMulActionArtinVisualVertex_4 : MulAction (Artin M) (VisualVertex M Y Z) :=
  visualAction M Y Z hSplit.out

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_ProperParabolicMalnormal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Weak malnormality of all proper parabolics

This proves the implication needed from Charney--Martin--Morris-Wright,
*Acylindrical hyperbolicity for Artin groups with a visual splitting*,
Algebraic & Geometric Topology 26 (2026), Proposition 4.2, for the present
Artin groups. A proper parabolic preserves a proper convex subtree. Two
translates can be placed at the ends of a segment with trivial stabilizer.
Their common stabilizer fixes that segment, hence is trivial.
-/
namespace HarmonicArtin.ParabolicIntersections
open TreeAction
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S) (Y Z : Set S)
variable [hSplit : Fact (IsVisualSplit M Y Z)]
noncomputable local instance properParabolicAction : MulAction (Artin M) (VisualVertex M Y Z) :=
  visualAction M Y Z hSplit.out

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_VisualInfiniteBranching
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Infinite branching for the genuine visual tree. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable

variable {S : Type} [Fintype S] (M : CoxeterMatrix S) (Y Z : Set S)
variable [hSplit : Fact (IsVisualSplit M Y Z)]
noncomputable local instance instMulActionArtinVisualVertex_5 : MulAction (Artin M) (VisualVertex M Y Z) :=
  visualAction M Y Z hSplit.out

end HarmonicArtin.ParabolicIntersections

end OAI
end


