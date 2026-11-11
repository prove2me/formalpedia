-- Prove2me | Definitions.Def_OAIQ225Ag013
-- name    : OAIQ225Ag013
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T17:46:25.061905+00:00
-- url     : https://prove2.me/theorems/05b463c7-b560-4cad-a405-f7934cacf77b
-- title:
--   Definitions bundle OAIQ225Ag013 of the split of OpenAI, Harmonic heights and the Artin K(pi,1) conjecture
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.HarmonicArtin.salvetti_cover_contractible`, carved from OpenAI's openai/math development (OpenAI, *Harmonic heights and the Artin K(pi,1) conjecture*, OpenAI Math Release, September 23, 2026, result family 254, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 179 declarations of OpenAI's Lean: 30 definitions and 149 theorems. The definitions and types are `OAI.HarmonicArtin.deligneReindex`, `OAI.HarmonicArtin.fusionOrdinaryAction`, `OAI.HarmonicArtin.isolatedDataOfCoset`, `OAI.HarmonicArtin.liftedLowerFiberIso`, `OAI.HarmonicArtin.positiveUpperBoundaryRestrictionIso`, `OAI.HarmonicArtin.probeBottomWord`, `OAI.HarmonicArtin.probePositiveWord`, `OAI.HarmonicArtin.restrictedCellEmbedding`, `OAI.HarmonicArtin.restrictedLiftedFiberIso`, `OAI.HarmonicArtin.sourceActive`, `OAI.HarmonicArtin.sourceActiveTop`, `OAI.HarmonicArtin.sourceAllEligibleInclusion`, `OAI.HarmonicArtin.sourceAllEligibleProjection`, `OAI.HarmonicArtin.sourceConvexActualInclusion`, `OAI.HarmonicArtin.sourceConvexModel`, `OAI.HarmonicArtin.sourceConvexRegionInclusion`, `OAI.HarmonicArtin.sourceConvexVector`, `OAI.HarmonicArtin.sourceEarlierLowerOrderIso`, `OAI.HarmonicArtin.sourceEarlierUpperOrderIso`, `OAI.HarmonicArtin.sourceIncidence`, `OAI.HarmonicArtin.sourceLowerClose`, `OAI.HarmonicArtin.sourceLowerLevel`, `OAI.HarmonicArtin.sourceLowerRetraction`, `OAI.HarmonicArtin.sourceProbeAction`, `OAI.HarmonicArtin.sourceResidueActive`, `OAI.HarmonicArtin.sourceResidueClose`, `OAI.HarmonicArtin.sourceResidueNegative`, `OAI.HarmonicArtin.sourceResidueUpperClip`, `OAI.HarmonicArtin.sourceUpperClip`, `OAI.HarmonicArtin.sourceUpperLevel`.
--
--   **Sources.** They come from these modules of lean/OAI/Topology, in whole or in part: `ArtinGroups_Coxeter_ParabolicProductMap`, `ArtinGroups_Geometry_ConvexInclusion`, `ArtinGroups_Geometry_ConvexWord`, `ArtinGroups_Harmonic_AllEligibleLower`, `ArtinGroups_Harmonic_ArtinReindex`, `ArtinGroups_Harmonic_Block`, `ArtinGroups_Harmonic_CanonicalFusionMultiplicity`, `ArtinGroups_Harmonic_CanonicalLowSupport`, `ArtinGroups_Harmonic_CartanCommutingZero`, `ArtinGroups_Harmonic_Coset`, `ArtinGroups_Harmonic_CosetBelow`, `ArtinGroups_Harmonic_CosetOrbit`, `ArtinGroups_Harmonic_CosetProfile`, `ArtinGroups_Harmonic_CosetSignUpperTie`, `ArtinGroups_Harmonic_CosetSum`, `ArtinGroups_Harmonic_EarlierLower`, `ArtinGroups_Harmonic_EarlierLowerOrderIso`, `ArtinGroups_Harmonic_EarlierUpper`, `ArtinGroups_Harmonic_Eligible`, `ArtinGroups_Harmonic_FrameFamily`, `ArtinGroups_Harmonic_FusionQuiverSimpleEdge`, `ArtinGroups_Harmonic_FusionSignedPacketExterior`, `ArtinGroups_Harmonic_FusionZeroLabel`, `ArtinGroups_Harmonic_Harmonic`, `ArtinGroups_Harmonic_Incidence`, `ArtinGroups_Harmonic_IncidentNonnegRowPositive`, `ArtinGroups_Harmonic_InitialProbe`, `ArtinGroups_Harmonic_LowerIneligibleLater`, `ArtinGroups_Harmonic_MapPacket`, `ArtinGroups_Harmonic_MultiplicitySum`, `ArtinGroups_Harmonic_PeakSupport`, `ArtinGroups_Harmonic_PositiveComponent`, `ArtinGroups_Harmonic_PositiveUpperBoundaryRestriction`, `ArtinGroups_Harmonic_ProbeCoreInclusion`, `ArtinGroups_Harmonic_ProbeFixedOutside`, `ArtinGroups_Harmonic_ProbePacket`, `ArtinGroups_Harmonic_ProbePacketExterior`, `ArtinGroups_Harmonic_ProbePositiveWord`, `ArtinGroups_Harmonic_ProbePositiveWordAppend`, `ArtinGroups_Harmonic_ProbePositiveWordInitial`, `ArtinGroups_Harmonic_ProbePositiveWordLeft`, `ArtinGroups_Harmonic_ResidueActive`, `ArtinGroups_Harmonic_ResidueAllowed`, `ArtinGroups_Harmonic_ResidueEarlierLower`, `ArtinGroups_Harmonic_RestrictedArtinHomSpherical`, `ArtinGroups_Harmonic_SecondaryAsSum`, `ArtinGroups_Harmonic_TieCode`, `ArtinGroups_Harmonic_TypedRightCoset`, `ArtinGroups_Harmonic_UnfoldedFullWordMem`, `ArtinGroups_Harmonic_UnfoldedInclusionRange`, `ArtinGroups_Realizations_RestrictedCellEmbedding`, `ArtinGroups_Realizations_RestrictedLiftedCell`.
--
--   **Imports.** It imports the published bundle `Def_HarmonicArtin`; the bundles `OAIQ225Ag011` and `OAIQ225Ag012` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ225Ag015`; the statements `OAI.HarmonicArtin.sourceCandidate_zero_block` and `OAI.HarmonicArtin.sourceGroup_probe_euler`; the proofs of `OAI.HarmonicArtin.IsolatedIterationData.separation`, `OAI.HarmonicArtin.IsolatedIterationData.stage_move`, `OAI.HarmonicArtin.sourceCandidate_zero_block`, `OAI.HarmonicArtin.sourceClosedResidue_nonempty` and `OAI.HarmonicArtin.sourceGroup_probe_euler`.
-- source:
--   OpenAI, Harmonic heights and the Artin K(pi,1) conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 254; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Harmonic-heights-and-the-Artin-K-pi-1-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Topology at commit adc7f12

import Mathlib
import Definitions.Def_HarmonicArtin
import Definitions.Def_OAIQ225Ag011
import Definitions.Def_OAIQ225Ag012

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_FusionQuiverSimpleEdge
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.instDecidableRelStringLabelStringAdjacent _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_FusionZeroLabel
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_ProbePacket
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.restrictedArtinHom_generator
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_ProbePositiveWord
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
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

noncomputable def probePositiveWord (J:Set S) (w:List J)
    (x:FiniteHomotopyClass R (K:=K)) : FiniteHomotopyClass R (K:=K) :=
  sourceProbeAction M (wordArtin M (w.map Subtype.val)) x

noncomputable def probeBottomWord (J:Set S) (q:ℤ) (w:List J)
    (x:FiniteHomotopyClass R (K:=K)) : FiniteHomotopyClass R (K:=K) :=
  classLayer R q (probePositiveWord M J w x)

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
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_ProbeCoreInclusion
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
variable {S:Type} [Fintype S] [LinearOrder S] {K:Type*} [Field K]
  (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "Q" => fusionQuiver m (coxeterFusionEdge M) (coxeterFusionEdge_symm M)
local notation "hn" => fusionQuiver_no_loops m (coxeterFusionEdge M)
  (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M)
local notation "R" => probeQuiver Q
local notation "hnR" => probeQuiver_no_loops Q hn

lemma probePositiveWord_core_expanded (J:Set S) (w:List J) (x:FiniteHomotopyClass R (K:=K)) :
    probePositiveWord M J w x=positiveWordAction R
      ((fusionExpandedWord m w).map (probeCoreInclusion M J)) x := by
  simpa only [fusionExpandedWord_map,List.map_map,Function.comp_def,
    probeCoreInclusion,unfoldedInclusion] using probePositiveWord_expanded M J w x

lemma probePositiveWord_testUpper_reflect (J:Set S) (w:List J)
    (x:FiniteHomotopyClass R (K:=K)) {t:ℤ}
    (h:ClassTestUpper R (probePositiveWord M J w x) (Set.range (probeCoreInclusion M J)) t) :
    ClassTestUpper R x (Set.range (probeCoreInclusion M J)) t := by
  rw [probePositiveWord_core_expanded] at h
  exact positiveWordAction_testUpper_reflect R hnR _ x _ (probeCore_word_support M J w) h

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
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_ProbePositiveWordAppend
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_ProbePositiveWordInitial
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_InitialProbe
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.positiveToArtin_generator _root_.OAI.HarmonicArtin.positiveToArtin_word
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_UnfoldedFullWordMem
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_CanonicalLowSupport
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Geometry_ConvexWord
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
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

noncomputable def sourceConvexModel (J:Set S) (z:List ((S⊕Unit)×Bool))
    (s:S⊕Unit) (q:ℤ) (w:(restrictedMatrix M J).Group) (L:FusionLabel m) : FiniteModel Q (K:=ℂ) :=
  minimalClassModel Q (canonicalFusionLow m d hd hdiag
    ((sourceConvexWord M J w).map (sourceRootInclusion J)) q (classLayer Q q (O z s L)))

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
-- module Solutions.OAIQ225_AG.ArtinGroups_Geometry_ConvexInclusion
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_MapPacket
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.positiveLift_one _root_.OAI.HarmonicArtin.positiveToArtin_generator _root_.OAI.HarmonicArtin.positiveToArtin_word _root_.OAI.HarmonicArtin.restrictedArtinHom_generator
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_ProbePacketExterior
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.positiveLift_one _root_.OAI.HarmonicArtin.positiveToArtin_generator _root_.OAI.HarmonicArtin.positiveToArtin_word _root_.OAI.HarmonicArtin.restrictedArtinHom_generator
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
local notation "bw" => sourceProbeAction M (K:=K)

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

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_FusionSignedPacketExterior
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.unfoldedHom_simple _root_.OAI.HarmonicArtin.unfoldedMatrix_apply
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

lemma fusionOrbit_frame_level (w:List (V × Bool)) (s:V) (H L:FusionLabel m) (q:ℤ)
    (hs:∀ b∈w,b.1≠s) :
    classLevelArray Q (fusionPacketOrbit m d hd hdiag w s H) ((s,L),q)=
      if H=L ∧ q=0 then 1 else 0 := by
  rw [fusionPacketOrbit,fusionWord_level_exterior m d hd hdiag w _ s L q hs,
    classLevelArray_initial]
  simp only [Prod.mk.injEq,true_and]

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_UnfoldedInclusionRange
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
local notation "hm" => (fun e=>le_trans (by norm_num) (fusionLabelSize_ge_four M e))
local notation "Q" => fusionQuiver m d hd
local notation "aw" => sourceArtinAction M (K:=ℂ)

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
local notation "O" => fusionPacketOrbit m d hd hdiag
local notation "aw" => sourceArtinAction M (K:=ℂ)

lemma sourceFrameFamily_word (w:List (S×Bool)) :
    sourceFrameFamily M (sourceSignedWord M w)=O (sourcePacketWord w) (.inr ()) := by
  funext L
  rw [sourceFrameFamily,sourceArtinAction_signedWord]
  rfl

lemma sourceFrameFamily_mul (g x:Artin M) (L:FusionLabel m) :
    sourceFrameFamily M (g*x) L=aw g (sourceFrameFamily M x L) := by
  simp only [sourceFrameFamily,map_mul,Equiv.Perm.mul_apply]

lemma sourceMultiplicity_exterior (J:Set S) (g:Artin M) (hg:g∈artinParabolic M J)
    (x:Artin M) (v:S⊕Unit) (hv:v∉Sum.inl '' J) (k:ℤ) :
    sourceMultiplicity M (g*x) k v=sourceMultiplicity M x k v := by
  unfold sourceMultiplicity
  have he:sourceFrameFamily M (g*x)=(fun L=>aw g (sourceFrameFamily M x L)):=
    funext (sourceFrameFamily_mul M g x)
  rw [he]
  exact sourceArtinAction_multiplicity_exterior M J g hg _ v hv k

lemma sourceMultiplicity_frame (x:Artin M) (k:ℤ) :
    sourceMultiplicity M x k (.inr ())=if k=0 then 1 else 0 := by
  obtain ⟨w,rfl⟩:=sourceSignedWord_surjective M x
  have hf:∀ a∈sourcePacketWord w,a.1≠(.inr () : S⊕Unit) := by
    intro a ha
    obtain ⟨b,_,rfl⟩:=List.mem_map.mp ha
    exact Sum.inl_ne_inr
  unfold sourceMultiplicity
  rw [sourceFrameFamily_word]
  unfold fusionFamilyMultiplicity
  simp_rw [classTotalVector_layer_apply,fusionOrbit_frame_level m d hd hdiag _ _ _ _ _ hf]
  by_cases hk:k=0
  · subst k
    simp only [and_true,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,mul_ite,_root_.mul_one,MulZeroClass.mul_zero,
      Finset.sum_ite_eq',Finset.mem_univ,ite_true, if_true]
    exact div_self (ne_of_gt (fusionWeight_pos m hm _))
  · simp only [hk,and_false,ite_false, if_false,Nat.cast_zero,MulZeroClass.mul_zero,Finset.sum_const_zero,zero_div]

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_ProbePositiveWordLeft
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_ProbeFixedOutside
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.positiveToArtin_generator _root_.OAI.HarmonicArtin.positiveToArtin_word
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Coxeter_ParabolicProductMap
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
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

lemma sourceHarmonicAt_outside (T:Set S) (x:Artin M) (k:ℤ) (i:S⊕Unit)
    (hi:i∉(Sum.inl : S→S⊕Unit) '' T) : sourceHarmonicAt M T x k i=sourceMultiplicity M x k i :=
  harmonicExtension_outside _ _ _ hi

lemma sourceHarmonicAt_harmonic (T:Set S) (hT:IsSpherical M T)
    (x:Artin M) (k:ℤ) (i:(Sum.inl : S→S⊕Unit) '' T) :
    (framedCartan M *ᵥ sourceHarmonicAt M T x k) i=0 :=
  harmonicExtension_harmonic _ _ (framed_spherical_posDef M T hT) _ i

lemma sourceHarmonicAt_frame (T:Set S) (x:Artin M) (k:ℤ) :
    sourceHarmonicAt M T x k (.inr ())=if k=0 then 1 else 0 := by
  rw [sourceHarmonicAt_outside M T x k _ (by
    rintro ⟨_,_,he⟩; exact Sum.inl_ne_inr he)]
  exact sourceMultiplicity_frame M x k

lemma sourceHarmonicAt_invariant (T:Set S) (hT:IsSpherical M T)
    (g x:Artin M) (hg:g∈artinParabolic M T) (k:ℤ) :
    sourceHarmonicAt M T (g*x) k=sourceHarmonicAt M T x k := by
  apply harmonicExtension_unique _ _ (framed_spherical_posDef M T hT)
  · intro i hi
    rw [sourceHarmonicAt_outside _ _ _ _ _ hi]
    exact sourceMultiplicity_exterior M T g hg x i hi k
  · exact sourceHarmonicAt_harmonic M T hT (g*x) k

lemma sourceHarmonicAt_of_mem (T:Set S) (hT:IsSpherical M T) (x y:Artin M)
    (hy:y∈rightCoset M T x) (k:ℤ) :
    sourceHarmonicAt M T y k=sourceHarmonicAt M T x k := by
  have h:=sourceHarmonicAt_invariant M T hT (y*x⁻¹) x hy k
  simpa only [mul_assoc,inv_mul_cancel,mul_one] using h

lemma sourceCosetVector_eq (P:Deligne M) (x:Artin M) (hx:x∈P.val.2) (k:ℤ) :
    sourceCosetVector M P k=sourceHarmonicAt M P.val.1 x k := by
  rw [sourceCosetRepresentative_spec] at hx
  exact (sourceHarmonicAt_of_mem M P.val.1 P.property.1 _ x hx k).symm

lemma sourceCosetVector_frame (P:Deligne M) (k:ℤ) :
    sourceCosetVector M P k (.inr ())=if k=0 then 1 else 0 :=
  sourceHarmonicAt_frame M P.val.1 _ k

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

lemma sourceMultiplicity_values_finite (B:ℝ) :
    {r:ℝ | r≤B ∧ ∃ x k v,r=sourceMultiplicity M x k v}.Finite := by
  have h:=finite_normalized_weighted_nat_sums (fusionWeight m) (fusionWeight_pos m hm)
    (fusionWeight m (fusionZeroLabel m hm)) (fusionWeight_pos m hm _) B
  apply h.subset
  rintro r ⟨hr,x,k,v,rfl⟩
  exact ⟨hr,⟨fun L=>classLevelArray Q (sourceFrameFamily M x L)
    ((v,fusionZeroLabel m hm),k),sourceMultiplicity_sum M x k v⟩⟩

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

lemma sourceCosetVector_bounded_finite (B:ℝ) :
    {p:S⊕Unit→ℝ | ∃ P:Deligne M,∃ k:ℤ,sourceCosetSum M P k ≤ B ∧
      p=sourceCosetVector M P k}.Finite := by
  let A:Set ℝ := {0} ∪ {r:ℝ | r≤B ∧ ∃ x k v,r=sourceMultiplicity M x k v}
  have hA:A.Finite := (Set.finite_singleton 0).union (sourceMultiplicity_values_finite M B)
  apply (finite_harmonic_images (framedCartan M) A hA).subset
  rintro p ⟨P,k,hB,rfl⟩
  let T:Set (S⊕Unit) := (Sum.inl : S→S⊕Unit) '' P.val.1
  let v:S⊕Unit→ℝ := fun i=>if i∈T then 0 else sourceCosetVector M P k i
  refine ⟨T,v,?_,?_⟩
  · intro i
    by_cases hi:i∈T
    · exact Or.inl (by simp only [v,ite_eq_left hi,Set.mem_singleton_iff])
    · right
      dsimp only [v]
      rw [ite_eq_right hi]
      refine ⟨(sourceCosetVector_le_sum M P k i).trans hB,?_⟩
      refine ⟨sourceCosetRepresentative M P,k,i,?_⟩
      exact sourceHarmonicAt_outside M P.val.1 _ k i hi
  · change harmonicExtension (framedCartan M) T _=harmonicExtension (framedCartan M) T v
    apply harmonicExtension_congr_exterior
    intro i hi
    simp only [v,ite_eq_right hi]
    exact (sourceHarmonicAt_outside M P.val.1 _ k i hi).symm

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_PositiveComponent
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.positiveLift_one _root_.OAI.HarmonicArtin.positiveToArtin_generator _root_.OAI.HarmonicArtin.positiveToArtin_word _root_.OAI.HarmonicArtin.restrictedArtinHom_generator _root_.OAI.HarmonicArtin.sourceCosetProfile_apply
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

lemma sourceSecondary_bounds (P:Deligne M) (k:ℕ) :
    -(Fintype.card S:ℤ)≤ sourceSecondary M P k ∧ sourceSecondary M P k≤Fintype.card S := by
  have hc:Fintype.card P.val.1≤Fintype.card S:=Fintype.card_le_of_injective _ Subtype.val_injective
  have hl:-(Fintype.card P.val.1:ℤ)≤ sourceSecondary M P k := by
    calc
      _ = ∑_:P.val.1,(-1:ℤ) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun i _=>(sourceSignAt_bounds M _ _ _).1)
  have hu:sourceSecondary M P k≤(Fintype.card P.val.1:ℤ) := by
    calc
      _ ≤ ∑_:P.val.1,(1:ℤ) := Finset.sum_le_sum (fun i _=>(sourceSignAt_bounds M _ _ _).2)
      _ = _ := by simp
  constructor <;> omega

lemma sourceCosetVector_zero_positive (P:Deligne M) (i:S) (hi:i∈P.val.1) :
    0 < sourceCosetVector M P 0 (.inl i) := by
  have hp:=sourceCosetVector_nonneg M P 0
  by_contra hn
  have hz:sourceCosetVector M P 0 (.inl i)=0 := le_antisymm (le_of_not_gt hn) (hp _)
  have hrow:(framedCartan M *ᵥ sourceCosetVector M P 0) (.inl i)=0 :=
    sourceHarmonicAt_harmonic M P.val.1 P.property.1 _ 0 ⟨.inl i,⟨i,hi,rfl⟩⟩
  have hneg:(framedCartan M *ᵥ sourceCosetVector M P 0) (.inl i)<0 := by
    change (∑j,framedCartan M (.inl i) j*sourceCosetVector M P 0 j)<0
    have h: (∑j,framedCartan M (.inl i) j*sourceCosetVector M P 0 j)<∑_:S⊕Unit,(0:ℝ) := by
      apply Finset.sum_lt_sum
      · intro j _
        by_cases hj : (.inl i:S⊕Unit)=j
        · subst j; simp [hz]
        · exact mul_nonpos_of_nonpos_of_nonneg (framedCartan_off M _ _ hj) (hp j)
      · refine ⟨.inr (),Finset.mem_univ _,?_⟩
        rw [sourceCosetVector_frame]
        norm_num [framedCartan]
    simpa using h
  linarith

lemma sourceSecondary_zero (P:Deligne M) :
    sourceSecondary M P 0= -(Fintype.card P.val.1:ℤ) := by
  have h:∀i:P.val.1,sourceCosetSign M P 0 (.inl (i:S))= -1 := by
    intro i
    apply sourceSignAt_level_zero
    exact ne_of_gt (sourceCosetVector_zero_positive M P i i.property)
  simp only [sourceSecondary,h,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Int.mul_neg,
    mul_one]

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_Block
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.decEq Classical.propDecidable
open scoped BigOperators

variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

lemma sourceBlock_bounded_finite (B:ℝ) :
    {b:SourceBlock S | SourceBlockOccurs M b ∧ (ofLex b).1≤B}.Finite := by
  let A:= {p:S⊕Unit→ℝ | ∃P:Deligne M,∃k:ℤ,sourceCosetSum M P k≤B ∧ p=sourceCosetVector M P k}
  let Z:Set ℤ:=Set.Icc (-(Fintype.card S:ℤ)) (Fintype.card S)
  have hA:A.Finite:=sourceCosetVector_bounded_finite M B
  have hZ:Z.Finite:=Set.finite_Icc _ _
  let f:(S⊕Unit→ℝ)×ℤ→SourceBlock S:=fun v=>toLex (∑i,v.1 i,toLex (toLex v.1,v.2))
  apply ((hA.prod hZ).image f |>.insert (sourceZeroBlock (S:=S))).subset
  rintro b ⟨(rfl|⟨P,k,rfl⟩),hb⟩
  · exact Set.mem_insert _ _
  · apply Set.mem_insert_of_mem
    refine ⟨(sourceCosetVector M P k,sourceSecondary M P k),⟨?_,?_⟩,rfl⟩
    · exact ⟨P,k,hb,rfl⟩
    · exact sourceSecondary_bounds M P k

lemma sourceBlock_predecessors_finite (b:SourceBlock S) :
    {a:SourceBlock S | SourceBlockOccurs M a ∧ a<b}.Finite := by
  apply (sourceBlock_bounded_finite M (ofLex b).1).subset
  intro a ha
  exact ⟨ha.1,Prod.Lex.monotone_fst_ofLex ha.2.le⟩

lemma sourceBlockRank_strictMono {b c:SourceBlock S} (hb:SourceBlockOccurs M b) (hbc:b < c) :
    sourceBlockRank M b < sourceBlockRank M c := by
  apply Set.ncard_lt_ncard _ (sourceBlock_predecessors_finite M c)
  refine ⟨fun a ha=>⟨ha.1,ha.2.trans hbc⟩,?_⟩
  intro h
  exact (h ⟨hb,hbc⟩).2.false

lemma sourceBlockRank_lt_iff {b c:SourceBlock S}
    (hb:SourceBlockOccurs M b) (hc:SourceBlockOccurs M c) :
    sourceBlockRank M b < sourceBlockRank M c ↔ b < c := by
  constructor
  · intro h
    by_contra hn
    rcases lt_or_eq_of_le (le_of_not_gt hn) with he|rfl
    · exact (Nat.lt_asymm h (sourceBlockRank_strictMono M hc he))
    · exact h.false
  · exact sourceBlockRank_strictMono M hb

lemma sourceBlockRank_eq_iff {b c:SourceBlock S}
    (hb:SourceBlockOccurs M b) (hc:SourceBlockOccurs M c) :
    sourceBlockRank M b=sourceBlockRank M c ↔ b=c := by
  constructor
  · intro he
    rcases lt_trichotomy b c with h|h|h
    · have := sourceBlockRank_strictMono M hb h; omega
    · exact h
    · have := sourceBlockRank_strictMono M hc h; omega
  · exact congrArg _

lemma sourceHeight_lt_iff (P R:Deligne M) : sourceHeight M P < sourceHeight M R ↔
    ∃k,(∀d,k<d→sourceBlock M P d=sourceBlock M R d) ∧ sourceBlock M P k < sourceBlock M R k := by
  rw [Finsupp.Colex.lt_iff]
  simp only [sourceHeight]
  constructor
  · rintro ⟨k,hk,hlt⟩
    refine ⟨k,fun d hd=>?_,(sourceBlockRank_lt_iff M (Or.inr ⟨P,k,rfl⟩) (Or.inr ⟨R,k,rfl⟩)).mp hlt⟩
    exact (sourceBlockRank_eq_iff M (Or.inr ⟨P,d,rfl⟩) (Or.inr ⟨R,d,rfl⟩)).mp (hk d hd)
  · rintro ⟨k,hk,hlt⟩
    exact ⟨k,fun d hd=>congrArg (sourceBlockRank M) (hk d hd),
      (sourceBlockRank_lt_iff M (Or.inr ⟨P,k,rfl⟩) (Or.inr ⟨R,k,rfl⟩)).mpr hlt⟩

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_Coset
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

lemma sourceCosetVector_harmonic (P:Deligne M) (k:ℤ)
    (i:(Sum.inl:S→S⊕Unit) '' P.val.1) :
    (framedCartan M *ᵥ sourceCosetVector M P k) i=0 :=
  sourceHarmonicAt_harmonic M P.val.1 P.property.1 _ k i

lemma sourceCosetVector_upper_outside {P R:Deligne M} (h:P≤R) (k:ℤ) (i:S⊕Unit)
    (hi:i∉(Sum.inl:S→S⊕Unit) '' R.val.1) :
    sourceCosetVector M R k i=sourceCosetVector M P k i := by
  let x:=sourceCosetRepresentative M P
  have hx:=sourceCosetRepresentative_mem M P
  rw [sourceCosetVector_eq M R x (h.2 hx),sourceCosetVector_eq M P x hx,
    sourceHarmonicAt_outside M R.val.1 x k i hi,
    sourceHarmonicAt_outside M P.val.1 x k i (fun he=>hi (Set.image_mono h.1 he))]

lemma sourceCosetVector_upper_harmonize {P R:Deligne M} (h:P≤R) (k:ℤ) :
    sourceCosetVector M R k=harmonicExtension (framedCartan M)
      ((Sum.inl:S→S⊕Unit) '' R.val.1) (sourceCosetVector M P k) :=
  harmonicExtension_unique _ _ (framed_spherical_posDef M R.val.1 R.property.1) _ _
    (sourceCosetVector_upper_outside M h k) (sourceCosetVector_harmonic M R k)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_CosetProfile
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.positiveLift_one _root_.OAI.HarmonicArtin.positiveToArtin_generator _root_.OAI.HarmonicArtin.positiveToArtin_word _root_.OAI.HarmonicArtin.restrictedArtinHom_generator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

def sourceActive (P:Deligne M) : Set S :=
  {i | i∉P.val.1 ∧ harmonicActive (framedCartan M) (.inr ()) (sourceCosetProfile M P) (.inl i)}

theorem sourceActive_spherical (P:Deligne M) : IsSpherical M (P.val.1 ∪ sourceActive M P) := by
  let K:Set S:=P.val.1 ∪ sourceActive M P
  let T:Set (S⊕Unit):=(Sum.inl:S→S⊕Unit) '' P.val.1
  let L:Set (S⊕Unit):=(Sum.inl:S→S⊕Unit) '' K
  have hL:((framedCartan M).submatrix ((↑):L→S⊕Unit) Subtype.val).PosDef := by
    apply harmonic_active_posDef (framedCartan M) (framedCartan_symm M)
      (framedCartan_off M) (fun i=>by rw [framedCartan_diag]; norm_num) (.inr ())
      (fun i hi=>by cases i with
        | inl i => norm_num [framedCartan]
        | inr u => cases u; exact (hi rfl).elim)
      (sourceCosetProfile M P) (fun k i=>sourceCosetVector_nonneg M P k i)
      (by rw [sourceCosetProfile_apply,sourceCosetVector_frame]; norm_num)
      T (framed_spherical_posDef M P.val.1 P.property.1)
    · intro k i hi
      exact sourceHarmonicAt_harmonic M P.val.1 P.property.1 _ k ⟨i,hi⟩
    · rintro ⟨i,hi,he⟩; exact Sum.inl_ne_inr he
    · rintro i ⟨j,(hj|hj),rfl⟩
      · exact Or.inl ⟨j,hj,rfl⟩
      · exact Or.inr hj.2
  let f:K→L:=fun i=>⟨.inl (i:S),⟨i,i.property,rfl⟩⟩
  have hf:Function.Injective f:=by
    intro i j h
    exact Subtype.ext (Sum.inl.inj (congrArg Subtype.val h))
  apply Geometric.spherical_of_cartan_posDef M K
  convert hL.submatrix hf using 1
  all_goals try with_reducible_and_instances rfl
  ext i j
  rfl

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_Incidence
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.positiveToArtin_generator _root_.OAI.HarmonicArtin.positiveToArtin_word
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open _root_.Matrix _root_.OAI.Matrix

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

noncomputable def sourceIncidence (P:Deligne M) (i:S) : ℕ :=
  incidenceLevel (framedCartan M) (sourceCosetProfile M P) (.inl i)

lemma source_incidence_le (P:Deligne M) {k:ℕ} {i:S}
    (h:levelIncident (framedCartan M) (sourceCosetProfile M P) k (.inl i)) :
    k≤ sourceIncidence M P i := levelIncident_le _ _ h

lemma source_no_incidence {P:Deligne M} {k:ℕ} {i:S} (h:sourceIncidence M P i<k) :
    sourceCosetVector M P k (.inl i)=0 ∧
    (framedCartan M *ᵥ sourceCosetVector M P k) (.inl i)=0 ∧
    sourceCosetSign M P k (.inl i)=0 := by
  have hn:¬levelIncident (framedCartan M) (sourceCosetProfile M P) k (.inl i):=
    fun hi=>Nat.not_lt_of_ge (source_incidence_le M P hi) h
  have hz:sourceCosetVector M P k (.inl i)=0:=le_antisymm
    (le_of_not_gt (fun hp=>hn (Or.inl hp))) (sourceCosetVector_nonneg M P k _)
  refine ⟨hz,?_,sourceSignAt_zero M _ _ _ hz⟩
  exact no_incidence_row_zero (framedCartan M) (framedCartan_off M)
    (sourceCosetProfile M P) (fun k i=>sourceCosetVector_nonneg M P k i) hn

noncomputable def sourceUpperLevel (P R:Deligne M) : ℕ :=
  (R.val.1.toFinset \ P.val.1.toFinset).sup (sourceIncidence M P)

lemma sourceIncidence_le_upperLevel (P R:Deligne M) (i:S)
    (hi:i∈R.val.1) (ht:i∉P.val.1) : sourceIncidence M P i≤ sourceUpperLevel M P R :=
  Finset.le_sup (f:=sourceIncidence M P) (by simp [hi,ht])

lemma sourceUpperLevel_attained {P R:Deligne M} (h:P<R) :
    ∃i, i∈R.val.1 ∧ i∉P.val.1 ∧ sourceIncidence M P i=sourceUpperLevel M P R := by
  have hs:=deligne_lt_type M h
  obtain ⟨i,hi,ht⟩:=Set.exists_of_ssubset hs
  have hf:(R.val.1.toFinset \ P.val.1.toFinset).Nonempty:=⟨i,by simp [hi,ht]⟩
  obtain ⟨j,hj,he⟩:=Finset.exists_mem_eq_sup _ hf (sourceIncidence M P)
  have hm:=Finset.mem_sdiff.mp hj
  exact ⟨j,by simpa using hm.1,by simpa using hm.2,he.symm⟩

lemma sourceCosetVector_eq_of_upper_rows {P R:Deligne M} (h:P≤R) (k:ℤ)
    (hr:∀i∈R.val.1,i∉P.val.1→(framedCartan M *ᵥ sourceCosetVector M P k) (.inl i)=0) :
    sourceCosetVector M R k=sourceCosetVector M P k := by
  rw [sourceCosetVector_upper_harmonize M h k]
  symm
  apply harmonicExtension_unique (framedCartan M)
    ((Sum.inl:S→S⊕Unit) '' R.val.1) (framed_spherical_posDef M R.val.1 R.property.1)
    (sourceCosetVector M P k) (sourceCosetVector M P k)
  · intro _ _; rfl
  · rintro ⟨_,⟨i,hi,rfl⟩⟩
    by_cases ht:i∈P.val.1
    · exact sourceCosetVector_harmonic M P k ⟨.inl i,⟨i,ht,rfl⟩⟩
    · exact hr i hi ht

lemma sourceCosetVector_eq_above_upper {P R:Deligne M} (h:P≤R) {k:ℕ}
    (hk:sourceUpperLevel M P R<k) : sourceCosetVector M R k=sourceCosetVector M P k := by
  apply sourceCosetVector_eq_of_upper_rows M h k
  intro i hi ht
  exact (source_no_incidence M ((sourceIncidence_le_upperLevel M P R i hi ht).trans_lt hk)).2.1

lemma sourceCosetSign_eq_above_upper {P R:Deligne M} (h:P≤R) {k:ℕ}
    (hk:sourceUpperLevel M P R<k) (i:S⊕Unit) :
    sourceCosetSign M R k i=sourceCosetSign M P k i := by
  apply sourceSignAt_congr_above
  intro d hd
  exact sourceCosetVector_eq_above_upper M h (hk.trans_le hd)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_SecondaryAsSum
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

lemma sourceSecondary_as_sum (P:Deligne M) (k:ℕ) :
    sourceSecondary M P k=∑i∈P.val.1.toFinset,sourceCosetSign M P k (.inl i) :=
  (Finset.sum_subtype P.val.1.toFinset (fun _=>Set.mem_toFinset)
    (fun i=>sourceCosetSign M P k (.inl i))).symm

lemma sourceSecondary_upper_change {P R:Deligne M} (h:P≤R) (k:ℕ)
    (hs:∀i,sourceCosetSign M R k i=sourceCosetSign M P k i) :
    sourceSecondary M R k=sourceSecondary M P k+
      ∑i∈(R.val.1.toFinset \ P.val.1.toFinset),sourceCosetSign M P k (.inl i) := by
  rw [sourceSecondary_as_sum,sourceSecondary_as_sum]
  simp only [hs]
  rw [add_comm]
  exact (Finset.sum_sdiff (Set.toFinset_subset_toFinset.mpr h.1)).symm

lemma sourceBlock_eq_above_upper {P R:Deligne M} (h:P≤R) {k:ℕ}
    (hk:sourceUpperLevel M P R<k) : sourceBlock M R k=sourceBlock M P k := by
  have hv:=sourceCosetVector_eq_above_upper M h hk
  have hs:sourceSecondary M R k=sourceSecondary M P k:=by
    rw [sourceSecondary_upper_change M h k (sourceCosetSign_eq_above_upper M h hk)]
    have hz:(∑i∈(R.val.1.toFinset \ P.val.1.toFinset),sourceCosetSign M P k (.inl i))=0:=by
      apply Finset.sum_eq_zero
      intro i hi
      have hh:=Finset.mem_sdiff.mp hi
      have hb:=sourceIncidence_le_upperLevel M P R i (Set.mem_toFinset.mp hh.1)
        (fun ht=>hh.2 (Set.mem_toFinset.mpr ht))
      exact (source_no_incidence M (hb.trans_lt hk)).2.2
    rw [hz,add_zero]
  simp only [sourceBlock,sourceCosetSum,hv,hs]

lemma sourceCosetVector_upper_antitone {P R:Deligne M} (h:P≤R) (k:ℕ)
    (hr:∀i∈R.val.1,i∉P.val.1→0≤(framedCartan M *ᵥ sourceCosetVector M P k) (.inl i)) :
    sourceCosetVector M R k≤ sourceCosetVector M P k := by
  apply harmonic_upper_antitone (framedCartan M) (framedCartan_off M)
    ((Sum.inl:S→S⊕Unit) '' R.val.1) (framed_spherical_posDef M R.val.1 R.property.1)
    (sourceCosetVector M P k) (sourceCosetVector M R k)
    (sourceCosetVector_upper_outside M h k) (sourceCosetVector_harmonic M R k)
  rintro ⟨_,⟨i,hi,rfl⟩⟩
  by_cases ht:i∈P.val.1
  · exact (sourceCosetVector_harmonic M P k ⟨.inl i,⟨i,ht,rfl⟩⟩).ge
  · exact hr i hi ht

lemma sourceCosetVector_upper_monotone {P R:Deligne M} (h:P≤R) (k:ℕ)
    (hr:∀i∈R.val.1,i∉P.val.1→(framedCartan M *ᵥ sourceCosetVector M P k) (.inl i)≤0) :
    sourceCosetVector M P k≤ sourceCosetVector M R k := by
  apply harmonic_upper_monotone (framedCartan M) (framedCartan_off M)
    ((Sum.inl:S→S⊕Unit) '' R.val.1) (framed_spherical_posDef M R.val.1 R.property.1)
    (sourceCosetVector M P k) (sourceCosetVector M R k)
    (sourceCosetVector_upper_outside M h k) (sourceCosetVector_harmonic M R k)
  rintro ⟨_,⟨i,hi,rfl⟩⟩
  by_cases ht:i∈P.val.1
  · exact (sourceCosetVector_harmonic M P k ⟨.inl i,⟨i,ht,rfl⟩⟩).le
  · exact hr i hi ht

lemma sourceBlock_lt_of_sum_lt {P R:Deligne M} {k:ℕ}
    (h:sourceCosetSum M P k < sourceCosetSum M R k) : sourceBlock M P k < sourceBlock M R k :=
  Prod.Lex.lt_iff.mpr (Or.inl h)

lemma sourceBlock_lt_of_secondary_lt {P R:Deligne M} {k:ℕ}
    (hv:sourceCosetVector M P k=sourceCosetVector M R k)
    (hs:sourceSecondary M P k < sourceSecondary M R k) : sourceBlock M P k < sourceBlock M R k := by
  unfold sourceBlock
  apply Prod.Lex.lt_iff.mpr
  refine Or.inr ⟨?_,?_⟩
  · change sourceCosetSum M P k=sourceCosetSum M R k
    simp only [sourceCosetSum,hv]
  · exact Prod.Lex.lt_iff.mpr (Or.inr ⟨congrArg toLex hv,hs⟩)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_PeakSupport
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.positiveToArtin_generator _root_.OAI.HarmonicArtin.positiveToArtin_word
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open _root_.Matrix _root_.OAI.Matrix

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

lemma sourcePeakSupport_mem (P:Deligne M) (i:S) (k:ℕ) :
    k∈sourcePeakSupport M P i ↔ sourceCosetVector M P k (.inl i)≠0 := by
  simp only [sourcePeakSupport,Finset.mem_filter,Finsupp.mem_support_iff,sourceCosetProfile_apply]
  constructor
  · exact And.right
  · intro h
    exact ⟨fun he=>h (congrFun he (.inl i)),h⟩

lemma sourcePeak_bound (P:Deligne M) (i:S) (k:ℕ)
    (h:sourceCosetVector M P k (.inl i)≠0) : k≤ sourcePeak M P i :=
  Finset.le_sup (f:=id) ((sourcePeakSupport_mem M P i k).mpr h)

lemma sourcePeak_above (P:Deligne M) (i:S) {k:ℕ} (h:sourcePeak M P i<k) :
    sourceCosetVector M P k (.inl i)=0 := by
  by_contra hn
  exact Nat.not_lt_of_ge (sourcePeak_bound M P i k hn) h

lemma sourcePeak_nonzero (P:Deligne M) (i:S)
    (h:(sourcePeakSupport M P i).Nonempty) :
    sourceCosetVector M P (sourcePeak M P i) (.inl i)≠0 := by
  apply (sourcePeakSupport_mem M P i _).mp
  obtain ⟨k,hk,he⟩:=Finset.exists_mem_eq_sup _ h id
  change (sourcePeakSupport M P i).sup id∈sourcePeakSupport M P i
  rw [he]
  exact hk

lemma sourcePeak_positive (P:Deligne M) (i:S) (hi:i∈P.val.1) :
    0 < sourceCosetVector M P (sourcePeak M P i) (.inl i) := by
  have hn:sourceCosetVector M P (sourcePeak M P i) (.inl i)≠0:=
    sourcePeak_nonzero M P i ⟨0,(sourcePeakSupport_mem M P i 0).mpr
      (ne_of_gt (sourceCosetVector_zero_positive M P i hi))⟩
  exact lt_of_le_of_ne (sourceCosetVector_nonneg M P _ _) (Ne.symm hn)

lemma sourcePeak_nonzero_of_pos (P:Deligne M) (i:S) (h:0 < sourcePeak M P i) :
    sourceCosetVector M P (sourcePeak M P i) (.inl i)≠0 := by
  apply sourcePeak_nonzero M P i
  by_contra hn
  have he:sourcePeakSupport M P i=∅:=Finset.not_nonempty_iff_eq_empty.mp hn
  simp only [sourcePeak,he,Finset.sup_empty] at h
  exact Nat.not_lt_zero _ h

noncomputable def sourceLowerLevel (P Q:Deligne M) : ℕ :=
  (P.val.1.toFinset \ Q.val.1.toFinset).sup (fun i=>max (sourcePeak M P i) (sourcePeak M Q i))

lemma sourcePeak_le_lowerLevel (P Q:Deligne M) (i:S) (hi:i∈P.val.1) (hq:i∉Q.val.1) :
    sourcePeak M P i≤ sourceLowerLevel M P Q ∧ sourcePeak M Q i≤ sourceLowerLevel M P Q := by
  have hh:=Finset.le_sup (f:=fun i=>max (sourcePeak M P i) (sourcePeak M Q i))
    (show i∈P.val.1.toFinset \ Q.val.1.toFinset by simp [hi,hq])
  exact ⟨(le_max_left _ _).trans hh,(le_max_right _ _).trans hh⟩

lemma sourceLowerLevel_attained {P Q:Deligne M} (h:Q<P) :
    ∃i,i∈P.val.1 ∧ i∉Q.val.1 ∧
      (0 < sourceCosetVector M P (sourceLowerLevel M P Q) (.inl i) ∨
       0 < sourceCosetVector M Q (sourceLowerLevel M P Q) (.inl i)) := by
  obtain ⟨j,hj,hq⟩:=Set.exists_of_ssubset (deligne_lt_type M h)
  have hn:(P.val.1.toFinset \ Q.val.1.toFinset).Nonempty:=⟨j,by simp [hj,hq]⟩
  obtain ⟨i,hi,he⟩:=Finset.exists_mem_eq_sup _ hn
    (fun i=>max (sourcePeak M P i) (sourcePeak M Q i))
  have ha:=Finset.mem_sdiff.mp hi
  have hip:i∈P.val.1:=Set.mem_toFinset.mp ha.1
  have hiq:i∉Q.val.1:=fun hh=>ha.2 (Set.mem_toFinset.mpr hh)
  refine ⟨i,hip,hiq,?_⟩
  by_cases hle:sourcePeak M Q i≤ sourcePeak M P i
  · have hh:sourceLowerLevel M P Q=sourcePeak M P i:=he.trans (max_eq_left hle)
    rw [hh]
    exact Or.inl (sourcePeak_positive M P i hip)
  · have hp:0 < sourcePeak M Q i:=(Nat.zero_le _).trans_lt (lt_of_not_ge hle)
    have hh:sourceLowerLevel M P Q=sourcePeak M Q i:=he.trans (max_eq_right (lt_of_not_ge hle).le)
    rw [hh]
    exact Or.inr (lt_of_le_of_ne (sourceCosetVector_nonneg M Q _ _)
      (Ne.symm (sourcePeak_nonzero_of_pos M Q i hp)))

lemma sourceCosetVector_eq_of_lower_open {P Q:Deligne M} (h:Q≤P) (k:ℕ)
    (ho:∀i∈P.val.1,i∉Q.val.1→sourceCosetVector M Q k (.inl i)=sourceCosetVector M P k (.inl i)) :
    sourceCosetVector M Q k=sourceCosetVector M P k := by
  have hext(i:S⊕Unit)(hi:i∉(Sum.inl:S→S⊕Unit) '' Q.val.1):
      sourceCosetVector M Q k i=sourceCosetVector M P k i:=by
    by_cases hp:i∈(Sum.inl:S→S⊕Unit) '' P.val.1
    · obtain ⟨j,hj,rfl⟩:=hp
      exact ho j hj (fun hq=>hi ⟨j,hq,rfl⟩)
    · exact (sourceCosetVector_upper_outside M h k i hp).symm
  have hq:=harmonicExtension_unique (framedCartan M) ((Sum.inl:S→S⊕Unit) '' Q.val.1)
    (framed_spherical_posDef M Q.val.1 Q.property.1) (sourceCosetVector M P k)
    (sourceCosetVector M Q k) hext (sourceCosetVector_harmonic M Q k)
  have hp:=harmonicExtension_unique (framedCartan M) ((Sum.inl:S→S⊕Unit) '' Q.val.1)
    (framed_spherical_posDef M Q.val.1 Q.property.1) (sourceCosetVector M P k)
    (sourceCosetVector M P k) (fun _ _=>rfl)
    (fun i=>sourceCosetVector_harmonic M P k ⟨i,Set.image_mono h.1 i.property⟩)
  exact hq.trans hp.symm

lemma sourceCosetVector_lower_comparison {P Q:Deligne M} (h:Q≤P) (k:ℕ)
    (ho:∀i∈P.val.1,i∉Q.val.1→sourceCosetVector M P k (.inl i)≤ sourceCosetVector M Q k (.inl i)) :
    sourceCosetVector M P k≤ sourceCosetVector M Q k := by
  apply harmonic_boundary_comparison (framedCartan M) ((Sum.inl:S→S⊕Unit) '' Q.val.1)
    (framed_spherical_posDef M Q.val.1 Q.property.1) (framedCartan_off M)
    (sourceCosetVector M P k) (sourceCosetVector M Q k)
    (fun i=>sourceCosetVector_harmonic M P k ⟨i,Set.image_mono h.1 i.property⟩)
    (sourceCosetVector_harmonic M Q k)
  intro i hi
  by_cases hp:i∈(Sum.inl:S→S⊕Unit) '' P.val.1
  · obtain ⟨j,hj,rfl⟩:=hp
    exact ho j hj (fun hq=>hi ⟨j,hq,rfl⟩)
  · exact (sourceCosetVector_upper_outside M h k i hp).le

lemma sourceCosetVector_lower_comparison_rev {P Q:Deligne M} (h:Q≤P) (k:ℕ)
    (ho:∀i∈P.val.1,i∉Q.val.1→sourceCosetVector M Q k (.inl i)≤ sourceCosetVector M P k (.inl i)) :
    sourceCosetVector M Q k≤ sourceCosetVector M P k := by
  apply harmonic_boundary_comparison (framedCartan M) ((Sum.inl:S→S⊕Unit) '' Q.val.1)
    (framed_spherical_posDef M Q.val.1 Q.property.1) (framedCartan_off M)
    (sourceCosetVector M Q k) (sourceCosetVector M P k)
    (sourceCosetVector_harmonic M Q k)
    (fun i=>sourceCosetVector_harmonic M P k ⟨i,Set.image_mono h.1 i.property⟩)
  intro i hi
  by_cases hp:i∈(Sum.inl:S→S⊕Unit) '' P.val.1
  · obtain ⟨j,hj,rfl⟩:=hp
    exact ho j hj (fun hq=>hi ⟨j,hq,rfl⟩)
  · exact (sourceCosetVector_upper_outside M h k i hp).symm.le

lemma sourceCosetVector_eq_above_lower {P Q:Deligne M} (h:Q≤P) {k:ℕ}
    (hk:sourceLowerLevel M P Q<k) : sourceCosetVector M Q k=sourceCosetVector M P k := by
  apply sourceCosetVector_eq_of_lower_open M h k
  intro i hi hq
  have hb:=sourcePeak_le_lowerLevel M P Q i hi hq
  rw [sourcePeak_above M Q i (hb.2.trans_lt hk),sourcePeak_above M P i (hb.1.trans_lt hk)]

lemma sourceBlock_eq_above_lower {P Q:Deligne M} (h:Q≤P) {k:ℕ}
    (hk:sourceLowerLevel M P Q<k) : sourceBlock M Q k=sourceBlock M P k := by
  have hv:=sourceCosetVector_eq_above_lower M h hk
  have hs:∀i,sourceCosetSign M P k i=sourceCosetSign M Q k i:=by
    apply sourceSignAt_congr_above
    intro d hd
    exact (sourceCosetVector_eq_above_lower M h (hk.trans_le hd)).symm
  have hz:(∑i∈P.val.1.toFinset \ Q.val.1.toFinset,sourceCosetSign M Q k (.inl i))=0:=by
    apply Finset.sum_eq_zero
    intro i hi
    have ht:=Finset.mem_sdiff.mp hi
    exact sourceSignAt_zero M _ _ _ (sourcePeak_above M Q i
      ((sourcePeak_le_lowerLevel M P Q i (Set.mem_toFinset.mp ht.1)
        (fun hq=>ht.2 (Set.mem_toFinset.mpr hq))).2.trans_lt hk))
  have hsec:=sourceSecondary_upper_change M h k hs
  rw [hz,add_zero] at hsec
  simp only [sourceBlock,sourceCosetSum,hv,hsec]

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_Eligible
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

lemma sourceCosetVector_open (Q:Deligne M) (i:S) (hi:i∉Q.val.1) (x:Artin M) (hx:x∈Q.val.2) (k:ℤ) :
    sourceCosetVector M Q k (.inl i)=sourceMultiplicity M x k (.inl i) := by
  rw [sourceCosetVector_eq M Q x hx]
  exact sourceHarmonicAt_outside M Q.val.1 x k _ (by
    rintro ⟨j,hj,he⟩; exact hi ((Sum.inl_injective he) ▸ hj))

lemma source_ineligible_top_ge {P Q:Deligne M}
    (ha:∀i∈P.val.1,i∉Q.val.1→¬SourceEligible M P Q i) :
    ∀i∈P.val.1,i∉Q.val.1→
      sourceCosetVector M P (sourceLowerLevel M P Q) (.inl i)≤
        sourceCosetVector M Q (sourceLowerLevel M P Q) (.inl i) := by
  intro i hi hq
  have hb:=sourcePeak_le_lowerLevel M P Q i hi hq
  rcases eq_or_lt_of_le hb.1 with he|he
  · by_contra hn
    apply ha i hi hq
    refine ⟨hi,hq,?_,Or.inl ?_⟩
    · intro d hd
      exact sourcePeak_above M Q i (hb.2.trans_lt (he ▸ hd))
    · rw [he]
      exact lt_of_not_ge hn
  · rw [sourcePeak_above M P i he]
    exact sourceCosetVector_nonneg M Q _ _

lemma source_eligible_top_le {P Q:Deligne M}
    (ha:∀i∈P.val.1,i∉Q.val.1→SourceEligible M P Q i) :
    ∀i∈P.val.1,i∉Q.val.1→
      sourceCosetVector M Q (sourceLowerLevel M P Q) (.inl i)≤
        sourceCosetVector M P (sourceLowerLevel M P Q) (.inl i) := by
  intro i hi hq
  have hb:=sourcePeak_le_lowerLevel M P Q i hi hq
  have hh:=ha i hi hq
  rcases eq_or_lt_of_le hb.1 with he|he
  · rcases hh.2.2.2 with hl|⟨hl,_⟩
    · rw [he] at hl; exact hl.le
    · rw [he] at hl; exact hl.le
  · rw [sourcePeak_above M P i he,hh.2.2.1 _ he]

lemma sourceCosetSign_eq_at_lower_tie {P Q:Deligne M} (h:Q≤P)
    (hv:sourceCosetVector M Q (sourceLowerLevel M P Q)=sourceCosetVector M P (sourceLowerLevel M P Q))
    (i:S⊕Unit) : sourceCosetSign M Q (sourceLowerLevel M P Q) i=
      sourceCosetSign M P (sourceLowerLevel M P Q) i := by
  apply sourceSignAt_congr_above
  intro d hd
  rcases eq_or_lt_of_le hd with rfl|hd
  · exact hv
  · exact sourceCosetVector_eq_above_lower M h hd

lemma sourceLowerLevel_prescribed_at_tie {P Q:Deligne M} (h:Q<P)
    (hv:sourceCosetVector M Q (sourceLowerLevel M P Q)=sourceCosetVector M P (sourceLowerLevel M P Q)) :
    ∃i,i∈P.val.1 ∧ i∉Q.val.1 ∧ sourcePeak M P i=sourceLowerLevel M P Q := by
  obtain ⟨i,hi,hq,hp⟩:=sourceLowerLevel_attained M h
  have hn:0 < sourceCosetVector M P (sourceLowerLevel M P Q) (.inl i):=by
    rcases hp with hp|hp
    · exact hp
    · rwa [hv] at hp
  exact ⟨i,hi,hq,le_antisymm (sourcePeak_le_lowerLevel M P Q i hi hq).1
    (sourcePeak_bound M P i _ (ne_of_gt hn))⟩

lemma source_ineligible_tie_sign {P Q:Deligne M} (i:S) (hi:i∈P.val.1) (hq:i∉Q.val.1)
    (ha:¬SourceEligible M P Q i)
    (he:sourcePeak M P i=sourceLowerLevel M P Q)
    (hv:sourceCosetVector M Q (sourceLowerLevel M P Q)=sourceCosetVector M P (sourceLowerLevel M P Q)) :
    sourceCosetSign M P (sourceLowerLevel M P Q) (.inl i)= -1 := by
  have hp:=sourcePeak_positive M P i hi
  rw [he] at hp
  have hn:sourceCosetSign M P (sourceLowerLevel M P Q) (.inl i)≠1:=by
    intro hs
    apply ha
    refine ⟨hi,hq,?_,Or.inr ⟨?_,?_⟩⟩
    · intro d hd
      exact sourcePeak_above M Q i ((sourcePeak_le_lowerLevel M P Q i hi hq).2.trans_lt (he ▸ hd))
    · rw [he,hv]
    · rwa [he]
  dsimp only [sourceCosetSign,sourceSignAt] at hn ⊢
  rw [ite_eq_right (ne_of_gt hp)] at hn ⊢
  split_ifs with hs
  · rw [ite_eq_left hs] at hn
    exact (hn rfl).elim
  · rfl

lemma source_eligible_tie_sign {P Q:Deligne M} (i:S)
    (ha:SourceEligible M P Q i) (he:sourcePeak M P i=sourceLowerLevel M P Q)
    (hv:sourceCosetVector M Q (sourceLowerLevel M P Q)=sourceCosetVector M P (sourceLowerLevel M P Q)) :
    sourceCosetSign M P (sourceLowerLevel M P Q) (.inl i)=1 := by
  rcases ha.2.2.2 with hl|⟨_,hs⟩
  · rw [he,hv] at hl
    exact (lt_irrefl _ hl).elim
  · rwa [he] at hs

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_TieCode
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

lemma sourceHeight_eq_blocks {P R:Deligne M} (h:sourceHeight M P=sourceHeight M R) (k:ℕ) :
    sourceBlock M P k=sourceBlock M R k := by
  apply (sourceBlockRank_eq_iff M (Or.inr ⟨P,k,rfl⟩) (Or.inr ⟨R,k,rfl⟩)).mp
  exact congrArg (fun z:Colex (ℕ→₀ℕ)=>(ofColex z) k) h

lemma sourceHeight_ne_of_lt {P R:Deligne M} (h:P<R) : sourceHeight M P≠sourceHeight M R := by
  intro he
  have hb:=sourceHeight_eq_blocks M he 0
  have hs:sourceSecondary M P 0=sourceSecondary M R 0:=
    congrArg (fun b:SourceBlock S=>(ofLex (ofLex b).2).2) hb
  rw [sourceSecondary_zero,sourceSecondary_zero] at hs
  have hc:P.val.1.ncard<R.val.1.ncard:=
    Set.ncard_lt_ncard (deligne_lt_type M h) (Set.toFinite _)
  rw [Set.ncard_eq_toFinset_card',Set.ncard_eq_toFinset_card'] at hc
  have hp:P.val.1.toFinset.card=Fintype.card P.val.1:=Set.toFinset_card _
  have hr:R.val.1.toFinset.card=Fintype.card R.val.1:=Set.toFinset_card _
  omega

lemma sourceEarlier_iff_of_comparable {P R:Deligne M} (h:P<R ∨ R<P) :
    SourceEarlier M P R ↔ sourceHeight M P < sourceHeight M R := by
  have hn:sourceHeight M P≠sourceHeight M R:=by
    rcases h with h|h
    · exact sourceHeight_ne_of_lt M h
    · exact Ne.symm (sourceHeight_ne_of_lt M h)
  change sourceVertexKey M P < sourceVertexKey M R ↔ _
  rw [Prod.Lex.lt_iff]
  simp only [sourceVertexKey,ofLex_toLex,hn,false_and,or_false]

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_LowerIneligibleLater
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.positiveToArtin_generator _root_.OAI.HarmonicArtin.positiveToArtin_word
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open _root_.Matrix _root_.OAI.Matrix

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

lemma sourceLower_ineligible_later {P Q:Deligne M} (h:Q<P)
    (ha:∀i∈P.val.1,i∉Q.val.1→¬SourceEligible M P Q i) : SourceEarlier M P Q := by
  apply (sourceEarlier_iff_of_comparable M (Or.inr h)).mpr
  apply (sourceHeight_lt_iff M P Q).mpr
  refine ⟨sourceLowerLevel M P Q,fun d hd=>(sourceBlock_eq_above_lower M h.le hd).symm,?_⟩
  let H:=sourceLowerLevel M P Q
  by_cases hv:sourceCosetVector M Q H=sourceCosetVector M P H
  · have hs(i:S)(hi:i∈P.val.1)(hq:i∉Q.val.1):sourceCosetSign M P H (.inl i)≤0:=by
      rcases eq_or_lt_of_le (sourcePeak_le_lowerLevel M P Q i hi hq).1 with he|he
      · rw [source_ineligible_tie_sign M i hi hq (ha i hi hq) he hv]
        norm_num
      · have hz:sourceCosetSign M P H (.inl i)=0:=sourceSignAt_zero M
          (fun d=>sourceCosetVector M P (d:ℤ)) H (.inl i) (sourcePeak_above M P i he)
        rw [hz]
    have hp:(∑i∈P.val.1.toFinset \ Q.val.1.toFinset,sourceCosetSign M P H (.inl i))<0:=by
      apply Finset.sum_neg'
      · intro i hi
        have ht:=Finset.mem_sdiff.mp hi
        exact hs i (Set.mem_toFinset.mp ht.1) (fun hq=>ht.2 (Set.mem_toFinset.mpr hq))
      · obtain ⟨i,hi,hq,he⟩:=sourceLowerLevel_prescribed_at_tie M h hv
        refine ⟨i,by simp [hi,hq],?_⟩
        rw [source_ineligible_tie_sign M i hi hq (ha i hi hq) he hv]
        norm_num
    apply sourceBlock_lt_of_secondary_lt M hv.symm
    have hh:=sourceSecondary_upper_change M h.le H
      (fun i=>(sourceCosetSign_eq_at_lower_tie M h.le hv i).symm)
    have hsign(i:S):sourceCosetSign M Q H (.inl i)=sourceCosetSign M P H (.inl i):=
      sourceCosetSign_eq_at_lower_tie M h.le hv (.inl i)
    simp only [hsign] at hh
    rw [hh]
    exact add_lt_of_neg_right _ hp
  · apply sourceBlock_lt_of_sum_lt
    exact harmonic_sum_lt_of_lt _ _
      (sourceCosetVector_lower_comparison M h.le H (source_ineligible_top_ge M ha)) (Ne.symm hv)

theorem sourceLower_earlier_has_eligible {P Q:Deligne M} (h:Q<P) (he:SourceEarlier M Q P) :
    ∃i,SourceEligible M P Q i := by
  by_contra hn
  have hl:=sourceLower_ineligible_later M h (fun i _ _ hi=>hn ⟨i,hi⟩)
  exact lt_asymm hl he

theorem sourceLower_eligible_earlier {P Q:Deligne M} (h:Q<P)
    (ha:∀i∈P.val.1,i∉Q.val.1→SourceEligible M P Q i) : SourceEarlier M Q P := by
  apply (sourceEarlier_iff_of_comparable M (Or.inl h)).mpr
  apply (sourceHeight_lt_iff M Q P).mpr
  refine ⟨sourceLowerLevel M P Q,fun d hd=>sourceBlock_eq_above_lower M h.le hd,?_⟩
  let H:=sourceLowerLevel M P Q
  by_cases hv:sourceCosetVector M Q H=sourceCosetVector M P H
  · have hs(i:S)(hi:i∈P.val.1)(hq:i∉Q.val.1):0≤ sourceCosetSign M P H (.inl i):=by
      rcases eq_or_lt_of_le (sourcePeak_le_lowerLevel M P Q i hi hq).1 with he|he
      · rw [source_eligible_tie_sign M i (ha i hi hq) he hv]
        norm_num
      · have hz:sourceCosetSign M P H (.inl i)=0:=sourceSignAt_zero M
          (fun d=>sourceCosetVector M P (d:ℤ)) H (.inl i) (sourcePeak_above M P i he)
        rw [hz]
    have hp:0<∑i∈P.val.1.toFinset \ Q.val.1.toFinset,sourceCosetSign M P H (.inl i):=by
      apply Finset.sum_pos'
      · intro i hi
        have ht:=Finset.mem_sdiff.mp hi
        exact hs i (Set.mem_toFinset.mp ht.1) (fun hq=>ht.2 (Set.mem_toFinset.mpr hq))
      · obtain ⟨i,hi,hq,he⟩:=sourceLowerLevel_prescribed_at_tie M h hv
        refine ⟨i,by simp [hi,hq],?_⟩
        rw [source_eligible_tie_sign M i (ha i hi hq) he hv]
        norm_num
    apply sourceBlock_lt_of_secondary_lt M hv
    have hh:=sourceSecondary_upper_change M h.le H
      (fun i=>(sourceCosetSign_eq_at_lower_tie M h.le hv i).symm)
    have hsign(i:S):sourceCosetSign M Q H (.inl i)=sourceCosetSign M P H (.inl i):=
      sourceCosetSign_eq_at_lower_tie M h.le hv (.inl i)
    simp only [hsign] at hh
    rw [hh]
    exact lt_add_of_pos_right _ hp
  · apply sourceBlock_lt_of_sum_lt
    exact harmonic_sum_lt_of_lt _ _
      (sourceCosetVector_lower_comparison_rev M h.le H (source_eligible_top_le M ha)) hv

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

lemma sourceEligible_shared {P Q R:Deligne M} (h:Q≤R) (i:S) (hi:i∉R.val.1) :
    SourceEligible M P Q i ↔ SourceEligible M P R i := by
  have hq:i∉Q.val.1:=fun hh=>hi (h.1 hh)
  have he(k:ℕ):sourceCosetVector M Q k (.inl i)=sourceCosetVector M R k (.inl i):=
    (sourceCosetVector_upper_outside M h k (.inl i) (by
      rintro ⟨j,hj,hh⟩; exact hi ((Sum.inl_injective hh) ▸ hj))).symm
  simp only [SourceEligible,he,hq,hi,not_false_eq_true,true_and]

noncomputable def sourceLowerClose (P Q:Deligne M) : Deligne M :=
  sourceCoset M (P.val.1 \ sourceEligibleSet M P Q)
    (source_spherical_mono M Set.sdiff_subset P.property.1) (sourceCosetRepresentative M Q)

lemma le_sourceLowerClose {P Q:Deligne M} (h:Q≤P) : Q≤ sourceLowerClose M P Q := by
  have he:=sourceCoset_eq M Q _ (sourceCosetRepresentative_mem M Q)
  nth_rw 1 [←he]
  exact sourceCoset_le M (show Q.val.1⊆P.val.1 \ sourceEligibleSet M P Q from
    fun i hi=>⟨h.1 hi,fun he=>he.2.1 hi⟩) _

lemma sourceLowerClose_le {P Q:Deligne M} (h:Q≤P) : sourceLowerClose M P Q≤P := by
  have he:=sourceCoset_eq M P _ (h.2 (sourceCosetRepresentative_mem M Q))
  calc
    sourceLowerClose M P Q≤ sourceCoset M P.val.1 P.property.1 (sourceCosetRepresentative M Q):=
      sourceCoset_le M Set.sdiff_subset _
    _=P:=he

lemma sourceLowerClose_all_eligible {P Q:Deligne M} (h:Q≤P) :
    ∀i∈P.val.1,i∉(sourceLowerClose M P Q).val.1→SourceEligible M P (sourceLowerClose M P Q) i := by
  intro i hi hn
  have hh:SourceEligible M P Q i:=by
    by_contra he
    exact hn ⟨hi,he⟩
  exact (sourceEligible_shared M (le_sourceLowerClose M h) i hn).mp hh

lemma sourceLowerClose_mem {P Q:Deligne M} (h:Q<P) (he:SourceEarlier M Q P) :
    sourceLowerClose M P Q<P ∧ SourceEarlier M (sourceLowerClose M P Q) P := by
  obtain ⟨i,hi⟩:=sourceLower_earlier_has_eligible M h he
  have hl:sourceLowerClose M P Q<P:=by
    apply lt_of_le_of_ne (sourceLowerClose_le M h.le)
    intro hh
    have ht:=congrArg (fun K:Deligne M=>K.val.1) hh
    have hm:i∈(sourceLowerClose M P Q).val.1:=by rw [ht]; exact hi.1
    exact hm.2 hi
  exact ⟨hl,sourceLower_eligible_earlier M hl (sourceLowerClose_all_eligible M h.le)⟩

lemma sourceLowerClose_monotone {P Q R:Deligne M} (h:Q≤R) (hr:R≤P) :
    sourceLowerClose M P Q≤ sourceLowerClose M P R := by
  have ht:P.val.1 \ sourceEligibleSet M P Q⊆P.val.1 \ sourceEligibleSet M P R:=by
    intro i hi
    refine ⟨hi.1,?_⟩
    intro hh
    exact hi.2 ((sourceEligible_shared M h i hh.2.1).mpr hh)
  have hx:(sourceCosetRepresentative M Q)∈(sourceLowerClose M P R).val.2:=
    (le_sourceLowerClose M hr).2 (h.2 (sourceCosetRepresentative_mem M Q))
  have he:=sourceCoset_eq M (sourceLowerClose M P R) _ hx
  rw [←he]
  exact sourceCoset_le M ht _

noncomputable def sourceLowerRetraction (P:Deligne M) :
    SourceEarlierLower M P →o SourceEarlierLower M P where
  toFun Q:=⟨sourceLowerClose M P Q,sourceLowerClose_mem M Q.property.1 Q.property.2⟩
  monotone':=fun _ R h=>sourceLowerClose_monotone M h R.property.1.le

lemma le_sourceLowerRetraction (P:Deligne M) (Q:SourceEarlierLower M P) :
    Q≤ sourceLowerRetraction M P Q := le_sourceLowerClose M Q.property.1.le

lemma sourceLowerClose_eq_of_all {P Q:Deligne M}
    (he:∀i∈P.val.1,i∉Q.val.1→SourceEligible M P Q i) (h:Q≤P) : sourceLowerClose M P Q=Q := by
  symm
  apply deligne_eq_of_le_type_eq M (le_sourceLowerClose M h)
  ext i
  change i∈Q.val.1 ↔ i∈P.val.1 ∧ ¬SourceEligible M P Q i
  constructor
  · intro hi
    exact ⟨h.1 hi,fun hh=>hh.2.1 hi⟩
  · rintro ⟨hi,hn⟩
    by_contra hq
    exact hn (he i hi hq)

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

noncomputable def sourceAllEligibleInclusion (P:Deligne M) :
    SourceAllEligibleLower M P →o SourceEarlierLower M P where
  toFun Q:=⟨Q.val,Q.property.1,sourceLower_eligible_earlier M Q.property.1 Q.property.2⟩
  monotone':=fun _ _ h=>h

noncomputable def sourceAllEligibleProjection (P:Deligne M) :
    SourceEarlierLower M P →o SourceAllEligibleLower M P where
  toFun Q:=⟨sourceLowerClose M P Q,(sourceLowerClose_mem M Q.property.1 Q.property.2).1,
    sourceLowerClose_all_eligible M Q.property.1.le⟩
  monotone':=fun _ R h=>sourceLowerClose_monotone M h R.property.1.le

lemma sourceAllEligible_retract (P:Deligne M) :
    (sourceAllEligibleProjection M P).comp (sourceAllEligibleInclusion M P)=OrderHom.id := by
  apply OrderHom.ext
  funext Q
  apply Subtype.ext
  exact sourceLowerClose_eq_of_all M Q.property.2 Q.property.1.le

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_IncidentNonnegRowPositive
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

lemma sourceActive_iff (P:Deligne M) (i:S) :
    i∈sourceActive M P ↔ i∉P.val.1 ∧
      (0<(framedCartan M *ᵥ sourceCosetVector M P (sourceIncidence M P i)) (.inl i) ∨
       (framedCartan M *ᵥ sourceCosetVector M P (sourceIncidence M P i)) (.inl i)=0 ∧
       sourceCosetSign M P (sourceIncidence M P i) (.inl i)= -1) := by
  have hs:=sourceSignAt_neg_iff M (sourceCosetProfile M P) (sourceIncidence M P i)
    (.inl i) (sourceCosetVector_nonneg M P _ _)
  constructor
  · rintro ⟨ht,hr|⟨hz,hpos,hnot⟩⟩
    · exact ⟨ht,Or.inl hr⟩
    · exact ⟨ht,Or.inr ⟨hz,hs.mpr ⟨hpos,hnot⟩⟩⟩
  · rintro ⟨ht,hr|⟨hz,hneg⟩⟩
    · exact ⟨ht,Or.inl hr⟩
    · exact ⟨ht,Or.inr ⟨hz,hs.mp hneg⟩⟩

lemma sourceCosetSign_eq_one_of_not_negative (P:Deligne M) (k:ℕ) (i:S⊕Unit)
    (hi:0 < sourceCosetVector M P k i) (hn:sourceCosetSign M P k i≠ -1) :
    sourceCosetSign M P k i=1 := by
  change (if sourceCosetVector M P k i=0 then 0 else if _ then 1 else -1)=1
  rw [ite_eq_right (ne_of_gt hi)]
  split_ifs with h
  · rfl
  · exact (hn (by simp only [sourceCosetSign,sourceSignAt,ite_eq_right (ne_of_gt hi),
      ite_eq_right h])).elim

lemma source_active_top_rows {P R:Deligne M} (_h:P≤R)
    (ha:∀i∈R.val.1,i∉P.val.1→i∈sourceActive M P) (i:S) (hi:i∈R.val.1) (ht:i∉P.val.1) :
    0≤(framedCartan M *ᵥ sourceCosetVector M P (sourceUpperLevel M P R)) (.inl i) := by
  have hb:=sourceIncidence_le_upperLevel M P R i hi ht
  rcases eq_or_lt_of_le hb with he|he
  · have hh:=((sourceActive_iff M P i).mp (ha i hi ht)).2
    rw [he] at hh
    rcases hh with hh|⟨hh,_⟩
    · exact hh.le
    · exact le_of_eq hh.symm
  · rw [(source_no_incidence M he).2.1]

lemma source_active_sign (P:Deligne M) (i:S) (ha:i∈sourceActive M P)
    (hr:(framedCartan M *ᵥ sourceCosetVector M P (sourceIncidence M P i)) (.inl i)=0) :
    sourceCosetSign M P (sourceIncidence M P i) (.inl i)= -1 := by
  rcases ((sourceActive_iff M P i).mp ha).2 with h|h
  · rw [hr] at h
    exact (lt_irrefl _ h).elim
  · exact h.2

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_CosetSignUpperTie
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.positiveToArtin_generator _root_.OAI.HarmonicArtin.positiveToArtin_word
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open _root_.Matrix _root_.OAI.Matrix

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

lemma sourceCosetSign_eq_at_upper_tie {P R:Deligne M} (h:P≤R)
    (hv:sourceCosetVector M R (sourceUpperLevel M P R)=sourceCosetVector M P (sourceUpperLevel M P R))
    (i:S⊕Unit) : sourceCosetSign M R (sourceUpperLevel M P R) i=
      sourceCosetSign M P (sourceUpperLevel M P R) i := by
  apply sourceSignAt_congr_above
  intro d hd
  rcases eq_or_lt_of_le hd with rfl|hd
  · exact hv
  · exact sourceCosetVector_eq_above_upper M h hd

theorem sourceUpper_active_earlier {P R:Deligne M} (h:P<R)
    (ha:∀i∈R.val.1,i∉P.val.1→i∈sourceActive M P) : SourceEarlier M R P := by
  apply (sourceEarlier_iff_of_comparable M (Or.inr h)).mpr
  apply (sourceHeight_lt_iff M R P).mpr
  refine ⟨sourceUpperLevel M P R,fun d hd=>sourceBlock_eq_above_upper M h.le hd,?_⟩
  let H:=sourceUpperLevel M P R
  by_cases hv:sourceCosetVector M R H=sourceCosetVector M P H
  · have hr(i:S)(hi:i∈R.val.1):(framedCartan M *ᵥ sourceCosetVector M P H) (.inl i)=0:=by
      rw [←hv]
      exact sourceCosetVector_harmonic M R H ⟨.inl i,⟨i,hi,rfl⟩⟩
    have hs(i:S)(hi:i∈R.val.1)(ht:i∉P.val.1):sourceCosetSign M P H (.inl i)≤0:=by
      rcases eq_or_lt_of_le (sourceIncidence_le_upperLevel M P R i hi ht) with he|he
      · have hh:=source_active_sign M P i (ha i hi ht) (by rw [he]; exact hr i hi)
        rw [he] at hh
        rw [hh]; norm_num
      · rw [(source_no_incidence M he).2.2]
    have hp:(∑i∈(R.val.1.toFinset \ P.val.1.toFinset),sourceCosetSign M P H (.inl i))<0:=by
      apply Finset.sum_neg'
      · intro i hi
        have ht:=Finset.mem_sdiff.mp hi
        exact hs i (Set.mem_toFinset.mp ht.1) (fun hi=>ht.2 (Set.mem_toFinset.mpr hi))
      · obtain ⟨i,hi,ht,he⟩:=sourceUpperLevel_attained M h
        refine ⟨i,by simp [hi,ht],?_⟩
        have hh:=source_active_sign M P i (ha i hi ht) (by rw [he]; exact hr i hi)
        rw [he] at hh
        rw [hh]; norm_num
    apply sourceBlock_lt_of_secondary_lt M hv
    rw [sourceSecondary_upper_change M h.le H (sourceCosetSign_eq_at_upper_tie M h.le hv)]
    exact add_lt_of_neg_right _ hp
  · apply sourceBlock_lt_of_sum_lt
    exact harmonic_sum_lt_of_lt _ _
      (sourceCosetVector_upper_antitone M h.le H (source_active_top_rows M h.le ha)) hv

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

noncomputable def sourceActiveTop (P:Deligne M) : Deligne M :=
  sourceCoset M (P.val.1 ∪ sourceActive M P) (sourceActive_spherical M P)
    (sourceCosetRepresentative M P)

noncomputable def sourceUpperClip (P R:Deligne M) : Deligne M :=
  sourceCoset M (R.val.1 ∩ (P.val.1 ∪ sourceActive M P))
    (source_spherical_mono M Set.inter_subset_left R.property.1)
    (sourceCosetRepresentative M P)

lemma le_sourceUpperClip {P R:Deligne M} (h:P≤ R) : P≤ sourceUpperClip M P R := by
  have he:=sourceCoset_eq M P _ (sourceCosetRepresentative_mem M P)
  nth_rw 1 [←he]
  exact sourceCoset_le M (show P.val.1 ⊆ R.val.1 ∩ (P.val.1 ∪ sourceActive M P) from fun i hi=>⟨h.1 hi,Or.inl hi⟩) _

lemma sourceActiveTop_mem (P:Deligne M) (ha:(sourceActive M P).Nonempty) :
    P < sourceActiveTop M P ∧ SourceEarlier M (sourceActiveTop M P) P := by
  have hl:P < sourceActiveTop M P:=by
    apply lt_of_le_of_ne
    · have he:=sourceCoset_eq M P _ (sourceCosetRepresentative_mem M P)
      nth_rw 1 [←he]
      exact sourceCoset_le M Set.subset_union_left _
    · intro he
      obtain ⟨i,hi⟩:=ha
      have hm:i∈(sourceActiveTop M P).val.1:=Or.inr hi
      rw [←he] at hm
      exact hi.1 hm
  exact ⟨hl,sourceUpper_active_earlier M hl (fun _ hi hn=>hi.resolve_left hn)⟩

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_CosetBelow
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.positiveToArtin_generator _root_.OAI.HarmonicArtin.positiveToArtin_word _root_.OAI.HarmonicArtin.sourceCosetProfile_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

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
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_ResidueAllowed
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

lemma sourceCosetVector_lower_compare_int {P Q:Deligne M} (h:Q≤P) (k:ℤ)
    (ho:∀i∈P.val.1,i∉Q.val.1→sourceCosetVector M Q k (.inl i)≤ sourceCosetVector M P k (.inl i)) :
    sourceCosetVector M Q k≤ sourceCosetVector M P k := by
  apply harmonic_boundary_comparison (framedCartan M) ((Sum.inl:S→S⊕Unit) '' Q.val.1)
    (framed_spherical_posDef M Q.val.1 Q.property.1) (framedCartan_off M)
    (sourceCosetVector M Q k) (sourceCosetVector M P k)
    (sourceCosetVector_harmonic M Q k)
    (fun i=>sourceCosetVector_harmonic M P k ⟨i,Set.image_mono h.1 i.property⟩)
  intro i hi
  by_cases hp:i∈(Sum.inl:S→S⊕Unit) '' P.val.1
  · obtain ⟨j,hj,rfl⟩:=hp
    exact ho j hj (fun hq=>hi ⟨j,hq,rfl⟩)
  · exact (sourceCosetVector_upper_outside M h k i hp).symm.le

lemma sourceCosetVector_lower_compare_int_rev {P Q:Deligne M} (h:Q≤P) (k:ℤ)
    (ho:∀i∈P.val.1,i∉Q.val.1→sourceCosetVector M P k (.inl i)≤ sourceCosetVector M Q k (.inl i)) :
    sourceCosetVector M P k≤ sourceCosetVector M Q k := by
  apply harmonic_boundary_comparison (framedCartan M) ((Sum.inl:S→S⊕Unit) '' Q.val.1)
    (framed_spherical_posDef M Q.val.1 Q.property.1) (framedCartan_off M)
    (sourceCosetVector M P k) (sourceCosetVector M Q k)
    (fun i=>sourceCosetVector_harmonic M P k ⟨i,Set.image_mono h.1 i.property⟩)
    (sourceCosetVector_harmonic M Q k)
  intro i hi
  by_cases hp:i∈(Sum.inl:S→S⊕Unit) '' P.val.1
  · obtain ⟨j,hj,rfl⟩:=hp
    exact ho j hj (fun hq=>hi ⟨j,hq,rfl⟩)
  · exact (sourceCosetVector_upper_outside M h k i hp).le

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_CartanCommutingZero
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

lemma sourceCosetProduct_open_left (B C:Set S) (hT:IsSpherical M (B∪C))
    (hd:Disjoint B C) (hc:∀s∈B,∀t∈C,M s t=2) (x:Artin M)
    (P:SourceCosetBelow M B (source_spherical_mono M Set.subset_union_left hT) x ×
      SourceCosetBelow M C (source_spherical_mono M Set.subset_union_right hT) x)
    (i:S) (hi:i∈B) (ho:i∉P.1.val.val.1) (k:ℤ) :
    sourceCosetVector M (sourceCosetProductFun M B C hT x P).val k (.inl i)=
      sourceCosetVector M P.1.val k (.inl i) := by
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
  rw [sourceCosetVector_open M _ i hnot _ hrep,
    sourceCosetVector_open M P.1.val i ho _ hr]
  have he:((b:Artin M)*c)*x=(c:Artin M)*((b:Artin M)*x):=by
    rw [(sourceParabolics_commute M B C hc b c b.property c.property).eq,mul_assoc]
  rw [he]
  apply sourceMultiplicity_exterior M C c c.property
  rintro ⟨s,hs,he⟩
  cases Sum.inl_injective he
  exact Set.disjoint_left.mp hd hi hs

lemma sourceCosetProduct_open_right (B C:Set S) (hT:IsSpherical M (B∪C))
    (hd:Disjoint B C) (x:Artin M)
    (P:SourceCosetBelow M B (source_spherical_mono M Set.subset_union_left hT) x ×
      SourceCosetBelow M C (source_spherical_mono M Set.subset_union_right hT) x)
    (i:S) (hi:i∈C) (ho:i∉P.2.val.val.1) (k:ℤ) :
    sourceCosetVector M (sourceCosetProductFun M B C hT x P).val k (.inl i)=
      sourceCosetVector M P.2.val k (.inl i) := by
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
  rw [sourceCosetVector_open M _ i hnot _ hrep,
    sourceCosetVector_open M P.2.val i ho _ hr,mul_assoc]
  apply sourceMultiplicity_exterior M B b b.property
  rintro ⟨s,hs,he⟩
  cases Sum.inl_injective he
  exact Set.disjoint_left.mp hd hs hi

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_ResidueActive
attribute [-instance] _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open _root_.Matrix _root_.OAI.Matrix Simplicial CategoryTheory

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

lemma sourceCosetVector_upper_antitone_int {X R:Deligne M} (h:X≤R) (q:ℤ)
    (hr:∀i∈R.val.1,i∉X.val.1→0≤(framedCartan M *ᵥ sourceCosetVector M X q) (.inl i)) :
    sourceCosetVector M R q≤ sourceCosetVector M X q := by
  apply harmonic_upper_antitone (framedCartan M) (framedCartan_off M)
    ((Sum.inl:S→S⊕Unit) '' R.val.1) (framed_spherical_posDef M R.val.1 R.property.1)
    (sourceCosetVector M X q) (sourceCosetVector M R q)
    (sourceCosetVector_upper_outside M h q) (sourceCosetVector_harmonic M R q)
  rintro ⟨_,⟨i,hi,rfl⟩⟩
  by_cases ht:i∈X.val.1
  · rw [sourceCosetVector_harmonic M X q ⟨.inl i,⟨i,ht,rfl⟩⟩]
  · exact hr i hi ht

lemma sourceCosetVector_upper_monotone_int {X R:Deligne M} (h:X≤R) (q:ℤ)
    (hr:∀i∈R.val.1,i∉X.val.1→(framedCartan M *ᵥ sourceCosetVector M X q) (.inl i)≤0) :
    sourceCosetVector M X q≤ sourceCosetVector M R q := by
  apply harmonic_upper_monotone (framedCartan M) (framedCartan_off M)
    ((Sum.inl:S→S⊕Unit) '' R.val.1) (framed_spherical_posDef M R.val.1 R.property.1)
    (sourceCosetVector M X q) (sourceCosetVector M R q)
    (sourceCosetVector_upper_outside M h q) (sourceCosetVector_harmonic M R q)
  rintro ⟨_,⟨i,hi,rfl⟩⟩
  by_cases ht:i∈X.val.1
  · rw [sourceCosetVector_harmonic M X q ⟨.inl i,⟨i,ht,rfl⟩⟩]
  · exact hr i hi ht

def sourceResidueActive (P X:Deligne M) (q:ℤ) : Set S :=
  {i | i∈P.val.1 ∧ i∉X.val.1 ∧ 0≤(framedCartan M *ᵥ sourceCosetVector M X q) (.inl i)}

noncomputable def sourceResidueUpperClip (P X R:Deligne M) (q:ℤ) : Deligne M :=
  sourceCoset M (R.val.1 ∩ (X.val.1 ∪ sourceResidueActive M P X q))
    (source_spherical_mono M Set.inter_subset_left R.property.1) (sourceCosetRepresentative M X)

lemma le_sourceResidueUpperClip {P X R:Deligne M} {q:ℤ} (h:X≤R) :
    X≤ sourceResidueUpperClip M P X R q := by
  calc
    X=sourceCoset M X.val.1 X.property.1 (sourceCosetRepresentative M X):=
      (sourceCoset_eq M X _ (sourceCosetRepresentative_mem M X)).symm
    _≤ sourceResidueUpperClip M P X R q:=sourceCoset_le M (show X.val.1⊆R.val.1 ∩ (X.val.1 ∪ sourceResidueActive M P X q) from
      fun i hi=>⟨h.1 hi,Or.inl hi⟩) _

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_ResidueEarlierLower
attribute [-instance] _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open Simplicial CategoryTheory

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

def sourceResidueNegative (X Y:Deligne M) (q:ℤ) : Set S :=
  {i | i∈X.val.1 ∧ i∉Y.val.1 ∧ sourceCosetVector M Y q (.inl i) < sourceCosetVector M X q (.inl i)}

noncomputable def sourceResidueClose (X Y:Deligne M) (q:ℤ) : Deligne M :=
  sourceCoset M (X.val.1 \ sourceResidueNegative M X Y q)
    (source_spherical_mono M Set.sdiff_subset X.property.1) (sourceCosetRepresentative M Y)

lemma le_sourceResidueClose {X Y:Deligne M} {q:ℤ} (h:Y≤X) : Y≤ sourceResidueClose M X Y q := by
  calc
    Y=sourceCoset M Y.val.1 Y.property.1 (sourceCosetRepresentative M Y):=
      (sourceCoset_eq M Y _ (sourceCosetRepresentative_mem M Y)).symm
    _≤ sourceResidueClose M X Y q:=sourceCoset_le M (show Y.val.1⊆X.val.1 \ sourceResidueNegative M X Y q from
      fun i hi=>⟨h.1 hi,fun hn=>hn.2.1 hi⟩) _

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
local notation "hm" => (fun e=>le_trans (by norm_num) (fusionLabelSize_ge_four M e))
local notation "Q" => fusionQuiver m d hd
local notation "O" => fusionPacketOrbit m d hd hdiag
local notation "μ" => fusionOrbitMultiplicity m d hd hdiag hm
local notation "C" => fusionFoldedCartan m d
local notation "aw" => sourceArtinAction M (K:=ℂ)

lemma sourceCosetOrbit_move (J:Set S) (z₀:List ((S⊕Unit)×Bool)) (s:S⊕Unit)
    (z:List ((S⊕Unit)×Bool)) (hz:SourceCosetOrbit M J z₀ s z) (j:J) :
    SourceCosetOrbit M J z₀ s ((.inl j,true)::z) := by
  obtain ⟨g,hg,he⟩:=hz
  refine ⟨generator M j*g,(artinParabolic M J).mul_mem
    (Subgroup.subset_closure ⟨j,j.property,rfl⟩) hg,fun L=>?_⟩
  change fusionPacketPerm m d hd hdiag (.inl j) (O z s L)=_
  rw [he,map_mul,sourceArtinAction_generator]
  rfl

lemma sourceCosetOrbit_multiplicity_exterior (J:Set S) (z₀:List ((S⊕Unit)×Bool)) (s:S⊕Unit)
    (z:List ((S⊕Unit)×Bool)) (hz:SourceCosetOrbit M J z₀ s z)
    (v:S⊕Unit) (hv:v∉Sum.inl '' J) (k:ℤ) : μ z s k v=μ z₀ s k v := by
  obtain ⟨g,hg,he⟩:=hz
  rw [← fusionFamilyMultiplicity_orbit m d hd hm hdiag z s k,
    ← fusionFamilyMultiplicity_orbit m d hd hm hdiag z₀ s k]
  have hf:(O z s)=(fun L=>aw g (O z₀ s L)):=funext he
  rw [hf]
  exact sourceArtinAction_multiplicity_exterior M J g hg (O z₀ s) v hv k

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
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_EarlierLowerOrderIso
attribute [-instance] _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CategoryTheory Simplicial

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

noncomputable def sourceEarlierLowerOrderIso (P:Deligne M) :
    WeightEarlierLower (SourceEarlier M) P ≃o SourceEarlierLower M P where
  toFun Q:=⟨Q.val,Q.property.2,Q.property.1⟩
  invFun Q:=⟨Q.val,Q.property.2,Q.property.1⟩
  left_inv _:=rfl
  right_inv _:=rfl
  map_rel_iff':=Iff.rfl

noncomputable def sourceEarlierUpperOrderIso (P:Deligne M) :
    WeightEarlierUpper (SourceEarlier M) P ≃o SourceEarlierUpper M P where
  toFun Q:=⟨Q.val,Q.property.2,Q.property.1⟩
  invFun Q:=⟨Q.val,Q.property.2,Q.property.1⟩
  left_inv _:=rfl
  right_inv _:=rfl
  map_rel_iff':=Iff.rfl

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

noncomputable def deligneReindex : Deligne M≃oDeligne (M.reindex e) where
  toEquiv:=Equiv.ofBijective (deligneReindexMap M e) ⟨by
    intro P Q h
    exact le_antisymm ((deligneReindex_le_iff M e P Q).mp (le_of_eq h))
      ((deligneReindex_le_iff M e Q P).mp (le_of_eq h.symm)),deligneReindex_surjective M e⟩
  map_rel_iff':=deligneReindex_le_iff M e _ _

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_RestrictedArtinHomSpherical
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.positiveToArtin_generator _root_.OAI.HarmonicArtin.positiveToArtin_word
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

theorem restrictedArtinHom_spherical_injective (T:Set S) (hT:IsSpherical M T) :
    Function.Injective (restrictedArtinHom M T) := by
  apply (injective_iff_map_eq_one (restrictedArtinHom M T)).mpr
  intro g hg
  have : Finite (restrictedMatrix M T).Group := restricted_finite M T hT
  obtain ⟨a,b,hfrac⟩:=finiteArtin_positive_left_fraction (restrictedMatrix M T) g
  have he:wordArtin M (a.map Subtype.val)=wordArtin M (b.map Subtype.val):=by
    have hh:=hg
    rw [hfrac,map_mul,map_inv,restrictedArtinHom_word,restrictedArtinHom_word] at hh
    exact inv_mul_eq_one.mp hh
  have hp:∀s:T,(s:S)∈(Set.univ:Set S)→∀L d,
      probePositiveWord M T a (sourceInitialProbe M (K:=ℚ) s L d)=
        probePositiveWord M T b (sourceInitialProbe M (K:=ℚ) s L d):=by
    intro s _ L d
    simp only [probePositiveWord,he]
  obtain ⟨u,v,hu,hv,heq⟩:=positive_equal_probe_fraction M T hT Set.univ a b hp
  have hun:u=[]:=List.eq_nil_iff_forall_not_mem.mpr (by intro s hs;exact hu s hs (Set.mem_univ _))
  have hvn:v=[]:=List.eq_nil_iff_forall_not_mem.mpr (by intro s hs;exact hv s hs (Set.mem_univ _))
  rw [hfrac,heq,hun,hvn]
  simp [wordArtin]

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_RestrictedLiftedCell
attribute [-instance] _root_.OAI.HarmonicArtin.instPartialOrderLiftedPuncturedBoundary _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S)

lemma restrictedLiftedCell_injective (T : Set S) (hT : IsSpherical M T) :
    Function.Injective (restrictedLiftedCell M T hT) := by
  intro a b h
  apply Prod.ext
  · apply restrictedArtinHom_spherical_injective M T hT
    exact congrArg (fun c : SphericalLiftedFiber M T => c.val.1) h
  · apply Subtype.ext
    have he : Subtype.val '' a.2.val = Subtype.val '' b.2.val :=
      congrArg (fun c : SphericalLiftedFiber M T => c.val.2.val) h
    exact Set.image_injective.mpr Subtype.val_injective he

lemma restrictedLiftedCell_face_iff (T : Set S) (hT : IsSpherical M T)
    (a b : LiftedCell (restrictedMatrix M T)) :
    LiftedFace M (restrictedLiftedCell M T hT a).val
      (restrictedLiftedCell M T hT b).val ↔ LiftedFace (restrictedMatrix M T) a b := by
  constructor
  · rintro ⟨hAB,w,hw,hr,hm,he⟩
    have hwt : ∀ s ∈ w, s ∈ T := by
      intro s hs
      obtain ⟨t,_,ht⟩ := hw s hs
      exact ht ▸ t.property
    let v : List T := w.attach.map fun s => ⟨s.val,hwt s.val s.property⟩
    have hv : v.map Subtype.val = w := by
      simp [v,List.map_map,Function.comp_def]
    have hr' : (restrictedMatrix M T).toCoxeterSystem.length
        (wordCoxeter (restrictedMatrix M T) v) = v.length := by
      rw [←restriction_length M T, restriction_wordCoxeter, hv]
      simpa [v] using hr
    refine ⟨?_,v,?_,hr',?_,?_⟩
    · intro s hs
      obtain ⟨t,ht,he⟩ := hAB ⟨s,hs,rfl⟩
      exact (Subtype.val_injective he) ▸ ht
    · intro s hs
      have hsw : (s:S) ∈ w := hv ▸ List.mem_map_of_mem hs
      obtain ⟨t,ht,he⟩ := hw s hsw
      exact (Subtype.val_injective he) ▸ ht
    · intro q
      have hq : restrictionHom M T q.val ∈ coxeterParabolic M (Subtype.val '' a.2.val) := by
        rw [←restriction_parabolic_map M T a.2.val]
        exact ⟨q.val,q.property,rfl⟩
      have hh := hm ⟨restrictionHom M T q.val,hq⟩
      rw [←hv,←restriction_wordCoxeter,←map_mul,restriction_length,restriction_length] at hh
      exact hh
    · apply restrictedArtinHom_spherical_injective M T hT
      rw [map_mul,restrictedArtinHom_word,hv]
      exact he
  · rintro ⟨hAB,v,hv,hr,hm,he⟩
    refine ⟨Set.image_mono hAB,v.map Subtype.val,?_,?_,?_,?_⟩
    · intro s hs
      obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hs
      exact ⟨t,hv t ht,rfl⟩
    · rw [←restriction_wordCoxeter,restriction_length,List.length_map]
      exact hr
    · intro q
      have hq := q.property
      change q.val ∈ coxeterParabolic M (Subtype.val '' a.2.val) at hq
      rw [←restriction_parabolic_map M T a.2.val] at hq
      obtain ⟨r,hrq,heq⟩ := hq
      have hh := hm ⟨r,hrq⟩
      rw [←restriction_length M T,←restriction_length M T] at hh
      rw [map_mul,restriction_wordCoxeter,heq] at hh
      exact hh
    · change restrictedArtinHom M T a.1 = restrictedArtinHom M T b.1 * _
      rw [he,map_mul,restrictedArtinHom_word]

noncomputable def restrictedLiftedFiberIso (T : Set S) (hT : IsSpherical M T) :
    LiftedCell (restrictedMatrix M T) ≃o SphericalLiftedFiber M T where
  toEquiv := Equiv.ofBijective (restrictedLiftedCell M T hT)
    ⟨restrictedLiftedCell_injective M T hT,restrictedLiftedCell_surjective M T hT⟩
  map_rel_iff' := by
    intro a b
    change (restrictedLiftedCell M T hT a).val ≤ (restrictedLiftedCell M T hT b).val ↔ a ≤ b
    rw [lifted_le_iff_face,lifted_le_iff_face]
    exact restrictedLiftedCell_face_iff M T hT a b

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_RestrictedCellEmbedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S)
variable (T : Set S) (hT : IsSpherical M T)

noncomputable def restrictedCellEmbedding (g : Artin M) :
    LiftedCell (restrictedMatrix M T) ↪o LiftedCell M where
  toFun a := liftedDeck M g (restrictedLiftedCell M T hT a).val
  inj' := by
    intro a b h
    apply restrictedLiftedCell_injective M T hT
    exact Subtype.ext ((liftedDeck M g).injective h)
  map_rel_iff' := by
    intro a b
    change liftedDeck M g (restrictedLiftedCell M T hT a).val ≤
      liftedDeck M g (restrictedLiftedCell M T hT b).val ↔ a ≤ b
    rw [(liftedDeck M g).le_iff_le,lifted_le_iff_face,lifted_le_iff_face]
    exact restrictedLiftedCell_face_iff M T hT a b

lemma restrictedCellEmbedding_full [Finite (restrictedMatrix M T).Group] (g : Artin M) :
    restrictedCellEmbedding M T hT g (fullSphericalCell (restrictedMatrix M T)) = (g,⟨T,hT⟩) := by
  apply Prod.ext
  · change g * restrictedArtinHom M T 1 = g
    rw [map_one,mul_one]
  · apply Subtype.ext
    change Subtype.val '' (Set.univ : Set T) = T
    ext s
    simp only [Set.mem_image,Set.mem_univ,true_and,Subtype.exists,exists_prop,exists_eq_right]

lemma restrictedCellEmbedding_full_preimage [Finite (restrictedMatrix M T).Group]
    (g : Artin M) (b : LiftedCell M)
    (hb : b ≤ restrictedCellEmbedding M T hT g (fullSphericalCell (restrictedMatrix M T))) :
    ∃ a, restrictedCellEmbedding M T hT g a = b := by
  rw [restrictedCellEmbedding_full] at hb
  obtain ⟨hst,w,hw,_,_,he⟩ := (lifted_le_iff_face M _ _).mp hb
  have hp : g⁻¹*b.1 ∈ artinParabolic M T := by
    rw [he,inv_mul_cancel_left]
    exact wordArtin_mem_parabolic M T w hw
  let v : SphericalLiftedFiber M T := ⟨liftedDeck M g⁻¹ b,hst,hp⟩
  refine ⟨(restrictedLiftedFiberIso M T hT).symm v,?_⟩
  change liftedDeck M g ((restrictedLiftedFiberIso M T hT) ((restrictedLiftedFiberIso M T hT).symm v)).val = b
  rw [OrderIso.apply_symm_apply]
  apply Prod.ext
  · exact mul_inv_cancel_left g b.1
  · rfl

lemma restrictedCellEmbedding_top (g : Artin M) (a : LiftedCell (restrictedMatrix M T)) :
    liftedTopVertex M (restrictedCellEmbedding M T hT g a) =
      g * restrictedArtinHom M T (liftedTopVertex (restrictedMatrix M T) a) := by
  change (g * restrictedArtinHom M T a.1) * positiveLift M
    (sphericalLongest M ⟨Subtype.val '' a.2.val, _⟩) =
      g * restrictedArtinHom M T (a.1 * positiveLift (restrictedMatrix M T) (sphericalLongest (restrictedMatrix M T) a.2))
  rw [←restriction_sphericalLongest M T hT a.2,map_mul,restrictedArtinHom_positiveLift,mul_assoc]

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

variable (a : NoncriticalPositiveCell M) (hs : matchingLetter M z hz a ∈ a.val.2.val)
variable [Finite (restrictedMatrix M a.val.2.val).Group]
variable (q : (restrictedMatrix M a.val.2.val).Group)
variable (hq : ∀ w, (restrictedMatrix M a.val.2.val).toCoxeterSystem.length w ≤
  (restrictedMatrix M a.val.2.val).toCoxeterSystem.length q)
variable (inj' : Function.Injective (positiveToArtin (restrictedMatrix M a.val.2.val)))
variable (hc : positiveCellTop (restrictedMatrix M a.val.2.val)
  (positiveFullCell (restrictedMatrix M a.val.2.val)) ≠ 1)

include hs in
lemma restrictedFullMatchingFacet :
    restrictedCellEmbedding M a.val.2.val a.val.2.property (positiveToArtin M a.val.1)
      (positiveCellToLifted (restrictedMatrix M a.val.2.val)
        (positiveMatch (restrictedMatrix M a.val.2.val) q hq inj'
          ⟨positiveFullCell (restrictedMatrix M a.val.2.val),hc⟩).val) =
      positiveCellToLifted M (positiveMatch M z hz inj a).val := by
  let N := restrictedMatrix M a.val.2.val
  let c : NoncriticalPositiveCell N := ⟨positiveFullCell N,hc⟩
  let f := restrictedCellEmbedding M a.val.2.val a.val.2.property (positiveToArtin M a.val.1)
  have hfull : f (positiveCellToLifted N c.val) = positiveCellToLifted M a.val := by
    rw [show c.val = positiveFullCell N from rfl,positiveFullCell_lifted]
    exact restrictedCellEmbedding_full M a.val.2.val a.val.2.property _
  apply lifted_same_top_type_unique M
  · apply Subtype.ext
    change Subtype.val '' (positiveMatch N q hq inj' c).val.2.val =
      (positiveMatch M z hz inj a).val.2.val
    rw [positiveMatch_type,matchingOtherType,ite_eq_left (show matchingLetter N q hq c ∈ c.val.2.val from Set.mem_univ _),
      positiveMatch_type,matchingOtherType,ite_eq_left hs]
    have hl := restrictedFullMatchingLetter M z hz a hs q hq hc
    ext t
    constructor
    · rintro ⟨u,hu,rfl⟩
      refine ⟨u.property,?_⟩
      intro he
      apply hu.2
      apply Subtype.ext
      exact he.trans hl.symm
    · rintro ⟨ht,hne⟩
      refine ⟨⟨t,ht⟩,⟨Set.mem_univ _,?_⟩,rfl⟩
      intro he
      apply hne
      exact (congrArg Subtype.val he).trans hl
  · have he := congrArg (positiveToArtin N) (positiveMatch_top N q hq inj' c)
    rw [positiveCellTop_toArtin,positiveCellTop_toArtin] at he
    have he' := congrArg (fun x => positiveToArtin M a.val.1 * restrictedArtinHom M a.val.2.val x) he
    rw [←restrictedCellEmbedding_top M a.val.2.val a.val.2.property,
        ←restrictedCellEmbedding_top M a.val.2.val a.val.2.property] at he'
    change liftedTopVertex M (f _) = liftedTopVertex M _
    rw [he',hfull,←positiveCellTop_toArtin,←positiveCellTop_toArtin,positiveMatch_top]

include hs in

noncomputable def positiveUpperBoundaryRestrictionIso :
    {b : PositiveCellPoset (restrictedMatrix M a.val.2.val) inj' //
      positiveCellToLifted (restrictedMatrix M a.val.2.val) b <
        positiveCellToLifted (restrictedMatrix M a.val.2.val) (positiveFullCell (restrictedMatrix M a.val.2.val)) ∧
      b ≠ (positiveMatch (restrictedMatrix M a.val.2.val) q hq inj'
        ⟨positiveFullCell (restrictedMatrix M a.val.2.val),hc⟩).val} ≃o
    {b : PositiveCellPoset M inj // positiveCellToLifted M b < positiveCellToLifted M a.val ∧
      b ≠ (positiveMatch M z hz inj a).val} := by
  let N := restrictedMatrix M a.val.2.val
  let c : NoncriticalPositiveCell N := ⟨positiveFullCell N,hc⟩
  let f := restrictedCellEmbedding M a.val.2.val a.val.2.property (positiveToArtin M a.val.1)
  have hf : f (positiveCellToLifted N c.val) = positiveCellToLifted M a.val := by
    rw [show c.val = positiveFullCell N from rfl,positiveFullCell_lifted]
    exact restrictedCellEmbedding_full M a.val.2.val a.val.2.property _
  have hm : f (positiveCellToLifted N (positiveMatch N q hq inj' c).val) =
      positiveCellToLifted M (positiveMatch M z hz inj a).val :=
    restrictedFullMatchingFacet M z hz inj a hs q hq inj' hc
  have hsurj : ∀ b ≤ f (positiveCellToLifted N c.val), ∃ t, f t = b := by
    rw [show c.val = positiveFullCell N from rfl,positiveFullCell_lifted]
    exact restrictedCellEmbedding_full_preimage M a.val.2.val a.val.2.property _
  let e := puncturedBoundaryIso f (positiveCellToLifted N c.val)
    (positiveCellToLifted N (positiveMatch N q hq inj' c).val) hsurj
  rw [hf,hm] at e
  exact ((positivePuncturedBoundaryIso N inj' c.val (positiveMatch N q hq inj' c).val).trans e).trans
    (positivePuncturedBoundaryIso M inj a.val (positiveMatch M z hz inj a).val).symm

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

def liftedLowerFiberIso (T:Set S) (hT:IsSpherical M T) (x:Artin M) :
    {a:LiftedCell M // cellToDeligneOrderHom M a≤typedRightCoset M T hT x} ≃o
      SphericalLiftedFiber M T where
  toFun a:=⟨liftedDeck M x a.val,(cellToDeligne_le_typedRightCoset M a.val T hT x).mp a.property⟩
  invFun a:=⟨liftedDeck M x⁻¹ a.val,by
    apply (cellToDeligne_le_typedRightCoset M _ T hT x).mpr
    exact ⟨a.property.1,by simpa [liftedDeck,mul_assoc] using a.property.2⟩⟩
  left_inv:=by intro a;apply Subtype.ext;ext <;> simp [liftedDeck]
  right_inv:=by intro a;apply Subtype.ext;ext <;> simp [liftedDeck]
  map_rel_iff':=by intro a b;exact (liftedDeck M x).map_rel_iff

end HarmonicArtin

end OAI
end


