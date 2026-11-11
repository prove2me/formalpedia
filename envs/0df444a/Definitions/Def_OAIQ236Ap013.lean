-- Prove2me | Definitions.Def_OAIQ236Ap013
-- name    : OAIQ236Ap013
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T20:14:09.509806+00:00
-- url     : https://prove2.me/theorems/70f37ad6-0878-4b22-a9b9-cf1bc8ed04aa
-- title:
--   Definitions bundle OAIQ236Ap013 of the split of OpenAI, Parabolic intersections in Artin groups
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.HarmonicArtin.ParabolicIntersections.unconditional_arbitrary_intersections`, `OAI.HarmonicArtin.ParabolicIntersections.unconditional_nonclique_dynamics`, `OAI.HarmonicArtin.ParabolicIntersections.unconditional_parabolic_closure` and `OAI.HarmonicArtin.ParabolicIntersections.unconditional_parabolic_intersections`, carved from OpenAI's openai/math development (OpenAI, *Parabolic intersections in Artin groups*, OpenAI Math Release, September 23, 2026, result family 254, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 41 declarations of OpenAI's Lean: 8 definitions and 33 theorems. The definitions and types are `OAI.HarmonicArtin.canonicalFusionMultiplicity`, `OAI.HarmonicArtin.isolatedDataOfCoset`, `OAI.HarmonicArtin.probeBottomWord`, `OAI.HarmonicArtin.sourceConvexActualInclusion`, `OAI.HarmonicArtin.sourceConvexRegionInclusion`, `OAI.HarmonicArtin.sourceConvexVector`, `OAI.HarmonicArtin.sourceTypeComponent`, `OAI.HarmonicArtin.sphericalPositiveCancelMonoid`.
--
--   **Sources.** They come from these modules of lean/OAI/Topology, in whole or in part: `ArtinGroups_Cancellation_SphericalPositiveCancelMonoid`, `ArtinGroups_Complexes_CanonicalWordLow`, `ArtinGroups_Complexes_InverseWordAction`, `ArtinGroups_Complexes_LowerTruncationSum`, `ArtinGroups_Complexes_PositiveWordLowerBound`, `ArtinGroups_Complexes_ReducedNoTopDivisor`, `ArtinGroups_Coxeter_CanonicalReducedWordLow`, `ArtinGroups_Functors_TruncationIndexEquiv`, `ArtinGroups_Geometry_ConvexInclusion`, `ArtinGroups_Geometry_ConvexWord`, `ArtinGroups_Harmonic_CanonicalFusionLowCount`, `ArtinGroups_Harmonic_CanonicalFusionMultiplicity`, `ArtinGroups_Harmonic_CanonicalLowSupport`, `ArtinGroups_Harmonic_CosetOrbit`, `ArtinGroups_Harmonic_FusionExpressionAction`, `ArtinGroups_Harmonic_FusionExpressionOrbit`, `ArtinGroups_Harmonic_LayerExpression`, `ArtinGroups_Harmonic_ProbePositiveWord`, `ArtinGroups_Harmonic_ProbePositiveWordMonoid`, `ArtinGroups_Harmonic_ProbePositiveWordPositive`, `ArtinGroups_Harmonic_TypeComponent`, `ArtinGroups_Harmonic_UnfoldedFullWordMem`.
--
--   **Imports.** It imports the published bundle `Def_ArtinParabolicIntersections`; the bundles `OAIQ236Ap011` and `OAIQ236Ap012` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI_HarmonicArtin_sourceProbe_convex_euler` and `OAI.HarmonicArtin.sourceProbe_convex_euler_s236`; the proofs of `OAI_HarmonicArtin_IsolatedIterationData_cap_move`, `OAI.HarmonicArtin.IsolatedIterationData.cap_move_s236`, `OAI_HarmonicArtin_IsolatedIterationData_stage_move`, `OAI.HarmonicArtin.IsolatedIterationData.stage_move_s236`, `OAI_HarmonicArtin_ParabolicIntersections_PointedCappedCandidate_probe_euler`, `OAI.HarmonicArtin.ParabolicIntersections.PointedCappedCandidate.probe_euler_s236`, `OAI_HarmonicArtin_ParabolicIntersections_exists_minimal_parabolic`, `OAI.HarmonicArtin.ParabolicIntersections.exists_minimal_parabolic_s236`, `OAI_HarmonicArtin_ParabolicIntersections_null_boundary_contradiction`, `OAI.HarmonicArtin.ParabolicIntersections.null_boundary_contradiction_s236`, `OAI_HarmonicArtin_ParabolicIntersections_pointedCandidate_comparison_parabolic`, `OAI.HarmonicArtin.ParabolicIntersections.pointedCandidate_comparison_parabolic_s236`, `OAI_HarmonicArtin_ParabolicIntersections_relative_descending_lower_connected`, `OAI.HarmonicArtin.ParabolicIntersections.relative_descending_lower_connected_s236`, `OAI_HarmonicArtin_ParabolicIntersections_spherical_reduction`, `OAI.HarmonicArtin.ParabolicIntersections.spherical_reduction_s236`, `OAI.HarmonicArtin.ParabolicIntersections.unconditional_arbitrary_intersections`, `OAI.HarmonicArtin.ParabolicIntersections.unconditional_parabolic_closure`, `OAI.HarmonicArtin.ParabolicIntersections.unconditional_parabolic_intersections`, `OAI_HarmonicArtin_sourceProbe_convex_euler` and `OAI.HarmonicArtin.sourceProbe_convex_euler_s236`.
-- source:
--   OpenAI, Parabolic intersections in Artin groups, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 254; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Parabolic-intersections-in-Artin-groups-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Topology at commit adc7f12

import Mathlib
import Definitions.Def_ArtinParabolicIntersections
import Definitions.Def_OAIQ236Ap011
import Definitions.Def_OAIQ236Ap012

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_ReducedNoTopDivisor
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_LowerTruncationSum
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
local notation "F" => classLabelFunctor Q step hstep N hN orient μ A ho hμ δ hA hroot hPF

variable {T : Type u} [Fintype T] [DecidableEq T]

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
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_LayerExpression
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamily_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_CanonicalFusionLowCount
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

noncomputable def canonicalFusionMultiplicity (w:List V) (z:List (V×Bool))
    (s:V) (q:ℤ) (v:V) : ℝ :=
  Classical.choose (canonicalFusionLow_count_proportional m d hd hdiag hm w z s v q q)

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
local notation "R" => probeQuiver Q

noncomputable def probeBottomWord (J:Set S) (q:ℤ) (w:List J)
    (x:FiniteHomotopyClass R (K:=K)) : FiniteHomotopyClass R (K:=K) :=
  classLayer R q (probePositiveWord M J w x)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_ProbePositiveWordPositive
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamilyMulAction _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
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

lemma probePositiveWord_eq_of_positive (J:Set S) (u v:List J)
    (h:wordPositive (restrictedMatrix M J) u=wordPositive (restrictedMatrix M J) v)
    (x:FiniteHomotopyClass R (K:=K)) : probePositiveWord M J u x=probePositiveWord M J v x := by
  apply probePositiveWord_eq_of_restricted M J u v
  have he:=congrArg (positiveToArtin (restrictedMatrix M J)) h
  simpa only [positiveToArtin_word] using he

theorem probe_positive_monoid_top_factor (J:Set S) (hJ:IsSpherical M J)
    (x:FiniteHomotopyClass R (K:=K)) (t:ℤ)
    (hx:ClassTestUpper R x (Set.range (probeCoreInclusion M J)) t)
    (w:List J) (j:J) (ℓ:ℤ) (hlt:t<ℓ)
    (hy:ClassTestUpper R (probePositiveWord M J w x) (Set.range (probeCoreInclusion M J)) ℓ)
    (L:FusionLabel m) (c:ℤ)
    (htop:¬ClassTestExact R (probeCoreInclusion M J (j,L)) ℓ c (probePositiveWord M J w x)) :
    ∃v:List J,wordPositive (restrictedMatrix M J) w=
      positiveGenerator (restrictedMatrix M J) j*wordPositive (restrictedMatrix M J) v ∧ v.length+1=w.length := by
  let N:=restrictedMatrix M J
  let U:=Set.range (probeCoreInclusion M J)
  induction w using (measure (fun w:List J=>w.length)).wf.induction generalizing j ℓ L c with
  | h w ih=>
    cases w with
    | nil=>exact (htop (hx _ ⟨(j,L),rfl⟩ ℓ hlt c)).elim
    | cons s w=>
      obtain ⟨u,v,hu,he,hlen,hpos,hmax⟩:=maximal_reduced_monoid_prefix N s w
      have heword:wordPositive N (s::w)=wordPositive N (u++v) := by
        rw [wordPositive_append]; exact he
      have heact:probePositiveWord M J (s::w) x=
          probePositiveWord M J u (probePositiveWord M J v x) := by
        rw [probePositiveWord_eq_of_positive M J _ _ heword,probePositiveWord_append]
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
          obtain ⟨u',_,he',_⟩:=reduced_monoid_right_factor N u γ hu hnot
          have hea:probePositiveWord M J u y=
              probePositiveWord M J u' (sourceProbePacket M γ y) := by
            have hw:wordPositive N u=wordPositive N (u'++[γ]):=by
              rw [wordPositive_append]; exact he'
            rw [probePositiveWord_eq_of_positive M J _ _ hw,probePositiveWord_append]
            rfl
          have hγcap:ClassTestUpper R (sourceProbePacket M γ y) U ℓ := by
            apply probePositiveWord_testUpper_reflect M J u'
            rw [←hea,←heact]
            exact hy
          exact hγ (sourceProbePacket_top_exact_of_cap M J γ y hγcap L' c')
        have hext:wordPositive N (s::w)=wordPositive N (u++[γ])*wordPositive N v' := by
          rw [he,hv',wordPositive_append]
          exact (_root_.mul_assoc _ _ _).symm
        have hlxt:(u++[γ]).length+v'.length=(s::w).length := by
          simp only [List.length_append,List.length_singleton]
          omega
        have hh:=hmax (u++[γ]) v' huγ hext hlxt
        simp only [List.length_append,List.length_singleton] at hh
        omega
      · obtain ⟨u',_,he',hlen'⟩:=reduced_monoid_left_factor N u j hu hj
        refine ⟨u'++v,?_,?_⟩
        · rw [he,he',wordPositive_append,_root_.mul_assoc]
        · simp only [List.length_append]
          omega

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_ProbePositiveWordMonoid
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamilyMulAction _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ParabolicIntersections.deligneRightTranslate_type _root_.OAI.HarmonicArtin.ParabolicIntersections.foldedPositiveHom_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedAction_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamily_one _root_.OAI.HarmonicArtin.ParabolicIntersections.positiveMap_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.positiveSupport_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.positiveSupport_mul _root_.OAI.HarmonicArtin.ParabolicIntersections.positiveSupport_one _root_.OAI.HarmonicArtin.ParabolicIntersections.positiveSupport_word _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.positiveDegree_generator _root_.OAI.HarmonicArtin.positiveDegree_mul _root_.OAI.HarmonicArtin.positiveDegree_one _root_.OAI.HarmonicArtin.positiveDegree_word _root_.OAI.HarmonicArtin.positiveReverse_generator _root_.OAI.HarmonicArtin.positiveReverse_one _root_.OAI.HarmonicArtin.positiveSimpleLift_one _root_.OAI.HarmonicArtin.positiveSimpleLift_simple _root_.OAI.HarmonicArtin.positiveToCoxeter_generator _root_.OAI.HarmonicArtin.positiveToCoxeter_simpleLift _root_.OAI.HarmonicArtin.positiveToCoxeter_word
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

lemma probePositiveWord_monoid_factor (T:Set S) (w v:List T) (j:T)
    (he:wordPositive (restrictedMatrix M T) w=
      positiveGenerator (restrictedMatrix M T) j*wordPositive (restrictedMatrix M T) v)
    (x:FiniteHomotopyClass (probeQuiver (fusionQuiver m (coxeterFusionEdge M) (coxeterFusionEdge_symm M))) (K:=K)) :
    probePositiveWord M T w x=sourceProbePacket M j (probePositiveWord M T v x) := by
  have hw:wordPositive (restrictedMatrix M T) w=wordPositive (restrictedMatrix M T) (j::v):=he
  rw [probePositiveWord_eq_of_positive M T w (j::v) hw,probePositiveWord_cons]

theorem positive_monoid_eq_of_probe_eq (T:Set S) (hT:IsSpherical M T) (a b:List T)
    (he:∀s:T,∀L d,probePositiveWord M T a (sourceInitialProbe M (K:=K) s L d)=
        probePositiveWord M T b (sourceInitialProbe M (K:=K) s L d)) :
    wordPositive (restrictedMatrix M T) a=wordPositive (restrictedMatrix M T) b := by
  induction a using (measure (fun a:List T=>a.length)).wf.induction generalizing b with
  | h a ih=>
    cases a with
    | nil=>
      have hb:b=[]:=by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro s hs
        let L:FusionLabel m:=fun e=>⟨0,by have :=fusionLabelSize_ge_four M e;omega⟩
        have hc:ClassTestUpper _ (probePositiveWord M T [] (sourceInitialProbe M (K:=K) s L false))
            (Set.range (probeCoreInclusion M T)) 1:=by
          exact (probePositiveWord_initial_cap_iff M T [] s L false).mpr (by simp)
        rw [he s L false] at hc
        exact probePositiveWord_initial_cap_not_mem M T b s L false hc hs
      rw [hb]
    | cons s a=>
      let L:FusionLabel m:=fun e=>⟨0,by have :=fusionLabelSize_ge_four M e;omega⟩
      let x:=sourceInitialProbe M (K:=K) s L false
      obtain ⟨l,hl,hcap,j,H,c,htop⟩:=probePositiveWord_initial_top M T (s::a) s (by simp) L false (K:=K)
      have hx:=sourceInitialProbe_cap M (K:=K) T s L false
      obtain ⟨a',ha',halen⟩:=probe_positive_monoid_top_factor M T hT x 1 hx (s::a) j l hl hcap H c htop
      rw [he s L false] at hcap htop
      obtain ⟨b',hb',hblen⟩:=probe_positive_monoid_top_factor M T hT x 1 hx b j l hl hcap H c htop
      have he':∀s:T,∀L d,probePositiveWord M T a' (sourceInitialProbe M (K:=K) s L d)=
          probePositiveWord M T b' (sourceInitialProbe M (K:=K) s L d):=by
        intro t L d
        apply (sourceProbePacket M j).injective
        rw [←probePositiveWord_monoid_factor M T (s::a) a' j ha',←probePositiveWord_monoid_factor M T b b' j hb']
        exact he t L d
      have hi:=ih a' (show a'.length<(s::a).length by omega) b' he'
      rw [ha',hb',hi]

theorem spherical_positive_words_reflect (T:Set S) (hT:IsSpherical M T) (a b:List T)
    (he:wordArtin M (a.map Subtype.val)=wordArtin M (b.map Subtype.val)) :
    wordPositive (restrictedMatrix M T) a=wordPositive (restrictedMatrix M T) b := by
  apply positive_monoid_eq_of_probe_eq (K:=ℚ) M T hT a b
  intro s L d
  simp only [probePositiveWord,he]

theorem spherical_positiveToAmbient_injective (T:Set S) (hT:IsSpherical M T) :
    Function.Injective ((restrictedArtinHom M T).comp (positiveToArtin (restrictedMatrix M T))) := by
  intro a b hab
  obtain ⟨u,rfl⟩:=PresentedMonoid.surjective_mk a
  obtain ⟨v,rfl⟩:=PresentedMonoid.surjective_mk b
  have ha:PresentedMonoid.mk (positiveBraidRelations (restrictedMatrix M T)) u=
      wordPositive (restrictedMatrix M T) (FreeMonoid.toList u):=by rw [wordPositive_mk,FreeMonoid.ofList_toList]
  have hb:PresentedMonoid.mk (positiveBraidRelations (restrictedMatrix M T)) v=
      wordPositive (restrictedMatrix M T) (FreeMonoid.toList v):=by rw [wordPositive_mk,FreeMonoid.ofList_toList]
  rw [ha,hb] at hab ⊢
  apply spherical_positive_words_reflect M T hT
  simpa only [MonoidHom.comp_apply,positiveToArtin_word,restrictedArtinHom_word] using hab

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Cancellation_SphericalPositiveCancelMonoid
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamilyMulAction _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

noncomputable abbrev sphericalPositiveCancelMonoid (T:Set S) (hT:IsSpherical M T) :
    CancelMonoid (PositiveArtin (restrictedMatrix M T)) := by
  let f:PositiveArtin (restrictedMatrix M T) →* Artin M :=
    (restrictedArtinHom M T).comp (positiveToArtin (restrictedMatrix M T))
  exact Function.Injective.cancelMonoid f (spherical_positiveToAmbient_injective M T hT)
    f.map_one f.map_mul f.map_pow

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Coxeter_CanonicalReducedWordLow
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_UnfoldedFullWordMem
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop
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
local notation "hn" => fusionQuiver_no_loops (fusionLabelSize M) (coxeterFusionEdge M)
  (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M)
local notation "C" => canonicalFusionLow (fusionLabelSize M) (coxeterFusionEdge M)
  (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M) (K:=K)

lemma unfolded_full_word_mem (J : Set S) (u : List J) :
    ∀ α∈fusionExpandedWord (fusionLabelSize M) (u.map fun j : J => (Sum.inl (j:S) : S⊕Unit)),
      α∈Set.range (unfoldedInclusion M J) := by
  intro α hα
  have hh:=fusionExpandedWord_mem (fusionLabelSize M) _ α hα
  obtain ⟨j,_,hj⟩:=List.mem_map.mp hh
  exact ⟨(j,α.2),Prod.ext hj rfl⟩

theorem sourceCanonicalLow_termwiseSplit (J : Set S) (hJ : IsSpherical M J)
    (u : List J) (hu : (restrictedMatrix M J).toCoxeterSystem.IsReduced u)
    (q : ℤ) (x : FiniteHomotopyClass Q (K:=K))
    (hlo : ClassLowerBound Q q x) (hhi : ClassUpperBound Q q x) :
    Nonempty (TermwiseSplitInjection Q
      (minimalClassModel Q (C (u.map fun j : J => (Sum.inl (j:S) : S⊕Unit)) q x)).complex
      (minimalClassModel Q x).complex) := by
  rw [sourceCanonicalLow_eq]
  exact canonicalReducedWordLow_termwiseSplit Q hn (Set.range (unfoldedInclusion M J))
    (unfolded_full_simply_laced M J hJ) x q hlo hhi _ (unfolded_full_word_mem M J u)
    (unfolded_full_reduced M J hJ u hu)

theorem sourceCanonicalLow_pure (J : Set S) (hJ : IsSpherical M J)
    (u : List J) (hu : (restrictedMatrix M J).toCoxeterSystem.IsReduced u)
    (q : ℤ) (x : FiniteHomotopyClass Q (K:=K))
    (hlo : ClassLowerBound Q q x) (hhi : ClassUpperBound Q q x) :
    ClassLowerBound Q q (C (u.map fun j : J => (Sum.inl (j:S) : S⊕Unit)) q x) ∧
      ClassUpperBound Q q (C (u.map fun j : J => (Sum.inl (j:S) : S⊕Unit)) q x) := by
  rw [sourceCanonicalLow_eq]
  exact canonicalReducedWordLow_pure Q hn (Set.range (unfoldedInclusion M J))
    (unfolded_full_simply_laced M J hJ) x q hlo hhi _ (unfolded_full_word_mem M J u)
    (unfolded_full_reduced M J hJ u hu)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_CanonicalLowSupport
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex CoxeterExchange

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "hd" => coxeterFusionEdge_symm M
local notation "hdiag" => coxeterFusionEdge_diag M
local notation "Q" => fusionQuiver m d hd
local notation "O" => fusionPacketOrbit m d hd hdiag
local notation "C" => canonicalFusionLow m d hd hdiag (K:=ℂ)

lemma sourceCanonicalLow_support (J:Set S) (u:List J) (z:List ((S⊕Unit)×Bool))
    (s:S⊕Unit) (q:ℤ) (L:FusionLabel m) :
    ClassColorSupport Q (Set.range (unfoldedInclusion M J))
      (C (u.map fun j:J=>(Sum.inl (j:S):S⊕Unit)) q (classLayer Q q (O z s L))) := by
  rw [sourceCanonicalLow_eq]
  exact canonicalWordLow_colorSupport Q _ _ _ q (unfolded_full_word_mem M J u)
    (classLayer_lowerBound Q _ q)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Geometry_ConvexWord
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop
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
local notation "O" => fusionPacketOrbit m d hd hdiag
local notation "σ" => canonicalFusionMultiplicity m d hd hdiag hm

noncomputable def sourceConvexVector (J:Set S) (z:List ((S⊕Unit)×Bool))
    (s:S⊕Unit) (q:ℤ) (w:(restrictedMatrix M J).Group) : S⊕Unit→ℝ :=
  σ ((sourceConvexWord M J w).map (sourceRootInclusion J)) z s q

lemma sourceConvexModel_pure (J:Set S) (hJ:IsSpherical M J) (z:List ((S⊕Unit)×Bool))
    (s:S⊕Unit) (q:ℤ) (w:(restrictedMatrix M J).Group) (L:FusionLabel m) :
    ∀ i,((sourceConvexModel M J z s q w L).complex.placement i).level=q := by
  have h:=sourceCanonicalLow_pure M J hJ (sourceConvexWord M J w)
    (sourceConvexWord_reduced M J w) q (classLayer Q q (O z s L))
    (classLayer_lowerBound Q _ q) (classLayer_upperBound Q _ q)
  exact fun i=>le_antisymm (h.2 i) (h.1 i)

lemma sourceConvexModel_inclusion (J:Set S) (hJ:IsSpherical M J) (z:List ((S⊕Unit)×Bool))
    (s:S⊕Unit) (q:ℤ) (w:(restrictedMatrix M J).Group) (L:FusionLabel m) :
    Nonempty (TermwiseSplitInjection Q (sourceConvexModel M J z s q w L).complex
      (minimalClassModel Q (classLayer Q q (O z s L))).complex) :=
  sourceCanonicalLow_termwiseSplit M J hJ (sourceConvexWord M J w)
    (sourceConvexWord_reduced M J w) q _ (classLayer_lowerBound Q _ q) (classLayer_upperBound Q _ q)

lemma sourceConvexModel_support (J:Set S) (z:List ((S⊕Unit)×Bool))
    (s:S⊕Unit) (q:ℤ) (w:(restrictedMatrix M J).Group) (L:FusionLabel m) :
    ∀ i,((sourceConvexModel M J z s q w L).complex.placement i).color∈Set.range (unfoldedInclusion M J) :=
  sourceCanonicalLow_support M J (sourceConvexWord M J w) z s q L

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Geometry_ConvexInclusion
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop
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
local notation "Y" => fusionOrbitLayer m d hd hdiag

noncomputable def sourceConvexActualInclusion (J:Set S) (hJ:IsSpherical M J)
    (z:List ((S⊕Unit)×Bool)) (s:S⊕Unit) (q:ℤ)
    (w:(restrictedMatrix M J).Group) (L:FusionLabel m) :
    TermwiseSplitInjection Q (sourceConvexModel M J z s q w L).complex (Y z s L q) := by
  let a:=Classical.choice (sourceConvexModel_inclusion M J hJ z s q w L)
  let e:HomotopyEquivalence Q (minimalClassModel Q (classLayer Q q (O z s L))).complex
      (Y z s L q):=minimalClassModelEquivalence Q (Y z s L q)
  have lower : ClassLowerBound Q q (classLayer Q q (O z s L)) :=
    classLowerBound_of_representative Q _ (fun index => le_of_eq index.property.symm)
  have upper : ClassUpperBound Q q (classLayer Q q (O z s L)) :=
    classUpperBound_of_representative Q _ (fun index => le_of_eq index.property)
  have he:∀ i,((minimalClassModel Q (classLayer Q q (O z s L))).complex.placement i).level=q :=
    fun index=>le_antisymm (upper index) (lower index)
  exact a.trans Q ((e.ofPure Q he (fun i=>i.property)).termwiseSplit Q)

noncomputable def sourceConvexRegionInclusion (I J:Set S) (hJI:J⊆I) (hJ:IsSpherical M J)
    (z:List ((S⊕Unit)×Bool)) (s:S⊕Unit) (q:ℤ)
    (hb:∀ L i,((Y z s L q).placement i).color∉colorBoundary Q (fusionColorRegion m (Sum.inl '' I)))
    (w:(restrictedMatrix M J).Group) (L:FusionLabel m) :
    TermwiseSplitInjection Q (sourceConvexModel M J z s q w L).complex
      (fusionOrbitColorLayer m d hd hdiag z s q (Sum.inl '' I) hb L) := by
  apply (sourceConvexActualInclusion M J hJ z s q w L).colorTarget Q
    (sourceConvexModel_pure M J hJ z s q w L) (fun i=>i.property)
    (fusionColorRegion m (Sum.inl '' I)) _ (hb L)
  intro i
  obtain ⟨v,hv⟩:=sourceConvexModel_support M J z s q w L i
  change ((sourceConvexModel M J z s q w L).complex.placement i).color.1∈Sum.inl '' I
  rw [← hv]
  exact ⟨v.1.val,hJI v.1.property,rfl⟩

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_CosetOrbit
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamilyMulAction _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
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
local notation "μ" => fusionOrbitMultiplicity m d hd hdiag hm
local notation "C" => fusionFoldedCartan m d
local notation "aw" => sourceArtinAction M (K:=ℂ)

lemma sourceCosetOrbit_multiplicity_exterior (J:Set S) (z₀:List ((S⊕Unit)×Bool)) (s:S⊕Unit)
    (z:List ((S⊕Unit)×Bool)) (hz:SourceCosetOrbit M J z₀ s z)
    (v:S⊕Unit) (hv:v∉Sum.inl '' J) (k:ℤ) : μ z s k v=μ z₀ s k v := by
  obtain ⟨g,hg,he⟩:=hz
  rw [← fusionFamilyMultiplicity_orbit m d hd hm hdiag z s k,
    ← fusionFamilyMultiplicity_orbit m d hd hm hdiag z₀ s k]
  have hf:(O z s)=(fun L=>aw g (O z₀ s L)):=funext he
  rw [hf]
  exact sourceArtinAction_multiplicity_exterior M J g hg (O z₀ s) v hv k

noncomputable def isolatedDataOfCoset (I J:Set S) (hJI:J⊆I) (hJ:IsSpherical M J)
    (z₀:List ((S⊕Unit)×Bool)) (s:S⊕Unit) (q:ℤ) (c:S⊕Unit→ℝ)
    (hc:∀ v,0 ≤ c v) (hcSupp:∀ v,v∉Sum.inl '' I→c v=0)
    (hcPos:∀ v,v∈Sum.inl '' I→0 < c v)
    (hcNull:∀ v,v∈Sum.inl '' I→(C *ᵥ c) v=0)
    (hdata:∀ v,(v∈Sum.inl '' I ∧ v∉Sum.inl '' J) ∨
      (v∉Sum.inl '' I ∧ ∃ u∈Sum.inl '' I,C v u<0)→μ z₀ s q v=c v)
    (huniv:∀ g∈artinParabolic M J,
      (∀ L,ClassCapOn Q (aw g (O z₀ s L))
        (closedNeighborhood Q (Set.range (unfoldedInclusion M J))) q)→
      ∀ j:J,c (.inl (j:S))<fusionFamilyMultiplicity m d hd hm
        (fun L=>aw g (O z₀ s L)) q (.inl (j:S))) : IsolatedIterationData M where
  I:=I
  J:=J
  hJI:=hJI
  hJ:=hJ
  s:=s
  q:=q
  c:=c
  hc:=hc
  hcSupp:=hcSupp
  hcPos:=hcPos
  hcNull:=hcNull
  valid:=SourceCosetOrbit M J z₀ s
  move:=sourceCosetOrbit_move M J z₀ s
  data:=by
    intro z hz v hv
    have hj:v∉Sum.inl '' J := by
      rcases hv with h|h
      · exact h.2
      · exact fun hj=>h.1 (Set.image_mono hJI hj)
    rw [sourceCosetOrbit_multiplicity_exterior M J z₀ s z hz v hj q]
    exact hdata v hv
  strict:=sourceCosetOrbit_strict M J z₀ s q c huniv

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_TypeComponent
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamilyMulAction _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open _root_.Matrix _root_.OAI.Matrix

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

def sourceTypeComponent (P:Deligne M) (i:S) (hi:i∈P.val.1) : Set S :=
  {j | ∃hj:j∈P.val.1,Relation.ReflTransGen
    (fun a b:P.val.1=>framedCartan M (.inl a.val) (.inl b.val)<0) ⟨i,hi⟩ ⟨j,hj⟩}

end HarmonicArtin

end OAI
end


