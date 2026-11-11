-- Prove2me | Definitions.Def_OAIQ225Ag015
-- name    : OAIQ225Ag015
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T17:57:37.117715+00:00
-- url     : https://prove2.me/theorems/d23bf357-5d0d-4c38-9e14-aff2fe82b791
-- title:
--   Definitions bundle OAIQ225Ag015 of the split of OpenAI, Harmonic heights and the Artin K(pi,1) conjecture
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.HarmonicArtin.salvetti_cover_contractible`, carved from OpenAI's openai/math development (OpenAI, *Harmonic heights and the Artin K(pi,1) conjecture*, OpenAI Math Release, September 23, 2026, result family 254, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 53 declarations of OpenAI's Lean: 14 definitions and 39 theorems. The definitions and types are `OAI.HarmonicArtin.sourceEarlierLower_equiv_allEligible`, `OAI.HarmonicArtin.sourceEligibleProduct`, `OAI.HarmonicArtin.sourceEligibleProductFun`, `OAI.HarmonicArtin.sourceEligibleProductPuncture`, `OAI.HarmonicArtin.sourceResidueEarlierLowerIso`, `OAI.HarmonicArtin.sourceResidueEarlierUpperIso`, `OAI.HarmonicArtin.sourceResidueLowerEquiv`, `OAI.HarmonicArtin.sourceResidueLowerInclusion`, `OAI.HarmonicArtin.sourceResidueLowerProjection`, `OAI.HarmonicArtin.sourceResidueUpperRetraction`, `OAI.HarmonicArtin.sourceResidueUpperTop`, `OAI.HarmonicArtin.sourceResidueZeroLowerIso`, `OAI.HarmonicArtin.sourceUpperCenter`, `OAI.HarmonicArtin.sourceUpperRetraction`.
--
--   **Sources.** They come from these modules of lean/OAI/Topology, in whole or in part: `ArtinGroups_Harmonic_AllEligibleLower`, `ArtinGroups_Harmonic_CosetSignUpperTie`, `ArtinGroups_Harmonic_EarlierUpper`, `ArtinGroups_Harmonic_EligibleFactor`, `ArtinGroups_Harmonic_EligibleWithin`, `ArtinGroups_Harmonic_Incidence`, `ArtinGroups_Harmonic_IncidentNonnegRowPositive`, `ArtinGroups_Harmonic_ResidueActive`, `ArtinGroups_Harmonic_ResidueAllowed`, `ArtinGroups_Harmonic_ResidueEarlierLower`, `ArtinGroups_Harmonic_ResidueEarlierLowerIso`, `ArtinGroups_Harmonic_ResidueHeightZeroVector`, `ArtinGroups_Harmonic_ResidueRank`, `ArtinGroups_Harmonic_ResidueZeroLowerIso`.
--
--   **Imports.** It imports the published bundle `Def_HarmonicArtin`; the bundles `OAIQ225Ag013` and `OAIQ225Ag014` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.HarmonicArtin.salvetti_cover_contractible`, `OAI.HarmonicArtin.sourceEarlierLower_contractible`, `OAI.HarmonicArtin.sourcePositiveBlock_contractible`, `OAI.HarmonicArtin.sourceResidue_lower_weights_contractible` and `OAI.HarmonicArtin.sourceResidue_zero_ne_lower`.
-- source:
--   OpenAI, Harmonic heights and the Artin K(pi,1) conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 254; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Harmonic-heights-and-the-Artin-K-pi-1-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Topology at commit adc7f12

import Mathlib
import Definitions.Def_HarmonicArtin
import Definitions.Def_OAIQ225Ag013
import Definitions.Def_OAIQ225Ag014

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_Incidence
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder _root_.OAI.HarmonicArtin.sourceEligibleWithinTop
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open _root_.Matrix _root_.OAI.Matrix

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

lemma sourceIncidence_incident (P:Deligne M) (i:S) :
    levelIncident (framedCartan M) (sourceCosetProfile M P) (sourceIncidence M P i) (.inl i) := by
  apply incidenceLevel_incident
  refine ⟨0,Or.inr ⟨.inr (),?_,?_⟩⟩
  · norm_num [framedCartan]
  · rw [sourceCosetProfile_apply,sourceCosetVector_frame]; norm_num

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_AllEligibleLower
attribute [-instance] _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder _root_.OAI.HarmonicArtin.sourceEligibleWithinTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open Simplicial CategoryTheory

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

noncomputable def sourceEarlierLower_equiv_allEligible (P:Deligne M) :
    ContinuousMap.HomotopyEquiv |nerve (SourceEarlierLower M P)| |nerve (SourceAllEligibleLower M P)| :=
  nerveOrderRetractionEquiv (sourceAllEligibleProjection M P) (sourceAllEligibleInclusion M P)
    (sourceAllEligible_retract M P) (le_sourceLowerRetraction M P)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_IncidentNonnegRowPositive
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder _root_.OAI.HarmonicArtin.sourceEligibleWithinTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open _root_.Matrix _root_.OAI.Matrix

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

lemma source_inactive_top_rows {P R:Deligne M} (_h:P≤R)
    (ha:∀i∈R.val.1,i∉P.val.1→i∉sourceActive M P) (i:S) (hi:i∈R.val.1) (ht:i∉P.val.1) :
    (framedCartan M *ᵥ sourceCosetVector M P (sourceUpperLevel M P R)) (.inl i)≤0 := by
  have hb:=sourceIncidence_le_upperLevel M P R i hi ht
  rcases eq_or_lt_of_le hb with he|he
  · have hn:=ha i hi ht
    rw [sourceActive_iff] at hn
    have hnrow:¬0<(framedCartan M *ᵥ sourceCosetVector M P (sourceIncidence M P i)) (.inl i):=
      fun hh=>hn ⟨ht,Or.inl hh⟩
    rw [←he]
    exact le_of_not_gt hnrow
  · rw [(source_no_incidence M he).2.1]

lemma source_inactive_sign (P:Deligne M) (i:S) (ht:i∉P.val.1)
    (hn:i∉sourceActive M P)
    (hr:(framedCartan M *ᵥ sourceCosetVector M P (sourceIncidence M P i)) (.inl i)=0) :
    sourceCosetSign M P (sourceIncidence M P i) (.inl i)=1 := by
  apply sourceCosetSign_eq_one_of_not_negative
  · exact source_incident_nonneg_row_positive M P _ i (sourceIncidence_incident M P i)
      (le_of_eq hr.symm)
  · intro hs
    exact hn ((sourceActive_iff M P i).mpr ⟨ht,Or.inr ⟨hr,hs⟩⟩)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_CosetSignUpperTie
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder _root_.OAI.HarmonicArtin.sourceEligibleWithinTop
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

theorem sourceUpper_inactive_later {P R:Deligne M} (h:P<R)
    (ha:∀i∈R.val.1,i∉P.val.1→i∉sourceActive M P) : SourceEarlier M P R := by
  apply (sourceEarlier_iff_of_comparable M (Or.inl h)).mpr
  apply (sourceHeight_lt_iff M P R).mpr
  refine ⟨sourceUpperLevel M P R,fun d hd=>(sourceBlock_eq_above_upper M h.le hd).symm,?_⟩
  let H:=sourceUpperLevel M P R
  by_cases hv:sourceCosetVector M R H=sourceCosetVector M P H
  · have hr(i:S)(hi:i∈R.val.1):(framedCartan M *ᵥ sourceCosetVector M P H) (.inl i)=0:=by
      rw [←hv]
      exact sourceCosetVector_harmonic M R H ⟨.inl i,⟨i,hi,rfl⟩⟩
    have hs(i:S)(hi:i∈R.val.1)(ht:i∉P.val.1):0≤ sourceCosetSign M P H (.inl i):=by
      rcases eq_or_lt_of_le (sourceIncidence_le_upperLevel M P R i hi ht) with he|he
      · have hh:=source_inactive_sign M P i ht (ha i hi ht)
          (by rw [he]; exact hr i hi)
        rw [he] at hh
        rw [hh]; norm_num
      · rw [(source_no_incidence M he).2.2]
    have hp:0<∑i∈(R.val.1.toFinset \ P.val.1.toFinset),sourceCosetSign M P H (.inl i):=by
      apply Finset.sum_pos'
      · intro i hi
        have ht:=Finset.mem_sdiff.mp hi
        exact hs i (Set.mem_toFinset.mp ht.1) (fun hi=>ht.2 (Set.mem_toFinset.mpr hi))
      · obtain ⟨i,hi,ht,he⟩:=sourceUpperLevel_attained M h
        refine ⟨i,by simp [hi,ht],?_⟩
        have hh:=source_inactive_sign M P i ht (ha i hi ht)
          (by rw [he]; exact hr i hi)
        rw [he] at hh
        rw [hh]; norm_num
    apply sourceBlock_lt_of_secondary_lt M hv.symm
    rw [sourceSecondary_upper_change M h.le H (sourceCosetSign_eq_at_upper_tie M h.le hv)]
    exact lt_add_of_pos_right _ hp
  · apply sourceBlock_lt_of_sum_lt
    exact harmonic_sum_lt_of_lt _ _
      (sourceCosetVector_upper_monotone M h.le H (source_inactive_top_rows M h.le ha)) (Ne.symm hv)

theorem sourceUpper_earlier_has_active {P R:Deligne M} (h:P<R) (he:SourceEarlier M R P) :
    ∃i,i∈R.val.1 ∧ i∉P.val.1 ∧ i∈sourceActive M P := by
  by_contra hn
  have hl:SourceEarlier M P R:=sourceUpper_inactive_later M h
    (fun i hi ht ha=>hn ⟨i,hi,ht,ha⟩)
  exact lt_asymm hl he

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_EarlierUpper
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder _root_.OAI.HarmonicArtin.sourceEligibleWithinTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

lemma sourceUpperClip_monotone (P:Deligne M) : Monotone (sourceUpperClip M P) := by
  intro R Q h
  exact sourceCoset_le M (show R.val.1 ∩ (P.val.1 ∪ sourceActive M P) ⊆ Q.val.1 ∩ (P.val.1 ∪ sourceActive M P) from fun i hi=>⟨h.1 hi.1,hi.2⟩) _

lemma sourceUpperClip_mem {P R:Deligne M} (h:P<R) (he:SourceEarlier M R P) :
    P < sourceUpperClip M P R ∧ SourceEarlier M (sourceUpperClip M P R) P := by
  obtain ⟨i,hi,ht,ha⟩:=sourceUpper_earlier_has_active M h he
  have hl:P < sourceUpperClip M P R:=by
    apply lt_of_le_of_ne (le_sourceUpperClip M h.le)
    intro hh
    have hm:i∈(sourceUpperClip M P R).val.1:=⟨hi,Or.inr ha⟩
    rw [←hh] at hm
    exact ht hm
  refine ⟨hl,sourceUpper_active_earlier M hl ?_⟩
  intro j hj hn
  exact hj.2.resolve_left hn

noncomputable def sourceUpperRetraction (P:Deligne M) :
    SourceEarlierUpper M P →o SourceEarlierUpper M P where
  toFun R:=⟨sourceUpperClip M P R,sourceUpperClip_mem M R.property.1 R.property.2⟩
  monotone' := fun _ _ h=>sourceUpperClip_monotone M P h

noncomputable def sourceUpperCenter (P:Deligne M) (ha:(sourceActive M P).Nonempty) :
    SourceEarlierUpper M P:=⟨sourceActiveTop M P,sourceActiveTop_mem M P ha⟩

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_ResidueAllowed
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder _root_.OAI.HarmonicArtin.sourceEligibleWithinTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open _root_.Matrix _root_.OAI.Matrix

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

lemma sourceResidueAllowed_le {strict:Bool} {P Q:Deligne M} {q:ℤ}
    (h:SourceResidueAllowed M strict P Q q) : sourceCosetVector M Q q≤ sourceCosetVector M P q := by
  apply sourceCosetVector_lower_compare_int M h.1.le q
  intro i hi hn
  have hh:=(h.2 i hi hn).2
  cases strict with
  | false => exact hh
  | true => exact hh.le

lemma sourceResidueHeight_nonpos {strict:Bool} {P Q:Deligne M} {q:ℤ}
    (h:SourceResidueAllowed M strict P Q q) : sourceResidueHeight M P Q q≤0 := by
  exact Finset.sum_nonpos (fun i _=>sub_nonpos.mpr (sourceResidueAllowed_le M h (.inl i)))

lemma sourceResidueAllowed_upper {strict:Bool} {P Q R:Deligne M} {q:ℤ}
    (h:SourceResidueAllowed M strict P Q q) (hr:Q≤R) (hp:R<P) :
    SourceResidueAllowed M strict P R q := by
  refine ⟨hp,?_⟩
  intro i hi hn
  have hq:i∉Q.val.1:=fun hh=>hn (hr.1 hh)
  have he(d:ℤ):sourceCosetVector M R d (.inl i)=sourceCosetVector M Q d (.inl i):=
    sourceCosetVector_upper_outside M hr d _ (by
      rintro ⟨j,hj,hh⟩;exact hn ((Sum.inl_injective hh) ▸ hj))
  simp only [he]
  exact h.2 i hi hq

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_EligibleWithin
attribute [-instance] _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

lemma sourceEligibleProduct_left (Ref:Deligne M) (B C:Set S) (hT:IsSpherical M (B∪C))
    (hd:Disjoint B C) (hc:∀s∈B,∀t∈C,M s t=2) (x:Artin M)
    (A:SourceCosetBelow M B (source_spherical_mono M Set.subset_union_left hT) x ×
      SourceCosetBelow M C (source_spherical_mono M Set.subset_union_right hT) x)
    (i:S) (hi:i∈B) :
    SourceEligible M Ref (sourceCosetProductFun M B C hT x A).val i ↔ SourceEligible M Ref A.1.val i := by
  have hn:i∉(sourceCosetProductFun M B C hT x A).val.val.1 ↔i∉A.1.val.val.1:=by
    constructor
    · exact fun h h'=>h (Or.inl h')
    · intro h
      rintro (h'|h')
      · exact h h'
      · exact Set.disjoint_left.mp hd hi (A.2.property.1 h')
  by_cases ho:i∉A.1.val.val.1
  · simp only [SourceEligible,hn,sourceCosetProduct_open_left M B C hT hd hc x A i hi ho]
  · constructor
    · intro h;exact (ho (hn.mp h.2.1)).elim
    · intro h;exact (ho h.2.1).elim

lemma sourceEligibleProduct_right (Ref:Deligne M) (B C:Set S) (hT:IsSpherical M (B∪C))
    (hd:Disjoint B C) (x:Artin M)
    (A:SourceCosetBelow M B (source_spherical_mono M Set.subset_union_left hT) x ×
      SourceCosetBelow M C (source_spherical_mono M Set.subset_union_right hT) x)
    (i:S) (hi:i∈C) :
    SourceEligible M Ref (sourceCosetProductFun M B C hT x A).val i ↔ SourceEligible M Ref A.2.val i := by
  have hn:i∉(sourceCosetProductFun M B C hT x A).val.val.1 ↔i∉A.2.val.val.1:=by
    constructor
    · exact fun h h'=>h (Or.inr h')
    · intro h
      rintro (h'|h')
      · exact Set.disjoint_left.mp hd (A.1.property.1 h') hi
      · exact h h'
  by_cases ho:i∉A.2.val.val.1
  · simp only [SourceEligible,hn,sourceCosetProduct_open_right M B C hT hd x A i hi ho]
  · constructor
    · intro h;exact (ho (hn.mp h.2.1)).elim
    · intro h;exact (ho h.2.1).elim

lemma sourceEligibleProduct_condition (Ref:Deligne M) (B C:Set S) (hT:IsSpherical M (B∪C))
    (hd:Disjoint B C) (hc:∀s∈B,∀t∈C,M s t=2) (x:Artin M)
    (A:SourceCosetBelow M B (source_spherical_mono M Set.subset_union_left hT) x ×
      SourceCosetBelow M C (source_spherical_mono M Set.subset_union_right hT) x) :
    (∀i∈B∪C,i∉(sourceCosetProductFun M B C hT x A).val.val.1→
      SourceEligible M Ref (sourceCosetProductFun M B C hT x A).val i) ↔
    (∀i∈B,i∉A.1.val.val.1→SourceEligible M Ref A.1.val i) ∧
    (∀i∈C,i∉A.2.val.val.1→SourceEligible M Ref A.2.val i) := by
  constructor
  · intro h
    constructor
    · intro i hi ho
      apply (sourceEligibleProduct_left M Ref B C hT hd hc x A i hi).mp
      apply h i (Or.inl hi)
      rintro (ha|ha)
      · exact ho ha
      · exact Set.disjoint_left.mp hd hi (A.2.property.1 ha)
    · intro i hi ho
      apply (sourceEligibleProduct_right M Ref B C hT hd x A i hi).mp
      apply h i (Or.inr hi)
      rintro (ha|ha)
      · exact Set.disjoint_left.mp hd (A.1.property.1 ha) hi
      · exact ho ha
  · rintro ⟨h,h'⟩ i (hi|hi) ho
    · exact (sourceEligibleProduct_left M Ref B C hT hd hc x A i hi).mpr
        (h i hi (fun hh=>ho (Or.inl hh)))
    · exact (sourceEligibleProduct_right M Ref B C hT hd x A i hi).mpr
        (h' i hi (fun hh=>ho (Or.inr hh)))

noncomputable def sourceEligibleProductFun (Ref:Deligne M) (B C:Set S) (hT:IsSpherical M (B∪C))
    (hd:Disjoint B C) (hc:∀s∈B,∀t∈C,M s t=2) (x:Artin M)
    (A:SourceEligibleWithin M Ref (sourceCoset M B (source_spherical_mono M Set.subset_union_left hT) x) ×
      SourceEligibleWithin M Ref (sourceCoset M C (source_spherical_mono M Set.subset_union_right hT) x)) :
    SourceEligibleWithin M Ref (sourceCoset M (B∪C) hT x) := by
  let a:SourceCosetBelow M B (source_spherical_mono M Set.subset_union_left hT) x:=⟨A.1.val,A.1.property.1⟩
  let b:SourceCosetBelow M C (source_spherical_mono M Set.subset_union_right hT) x:=⟨A.2.val,A.2.property.1⟩
  let p:=sourceCosetProductFun M B C hT x (a,b)
  exact ⟨p.val,p.property,(sourceEligibleProduct_condition M Ref B C hT hd hc x (a,b)).mpr
    ⟨A.1.property.2,A.2.property.2⟩⟩

lemma sourceEligibleProductFun_le_iff (Ref:Deligne M) (B C:Set S) (hT:IsSpherical M (B∪C))
    (hd:Disjoint B C) (hc:∀s∈B,∀t∈C,M s t=2) (x:Artin M)
    (A D:SourceEligibleWithin M Ref (sourceCoset M B (source_spherical_mono M Set.subset_union_left hT) x) ×
      SourceEligibleWithin M Ref (sourceCoset M C (source_spherical_mono M Set.subset_union_right hT) x)) :
    sourceEligibleProductFun M Ref B C hT hd hc x A ≤ sourceEligibleProductFun M Ref B C hT hd hc x D ↔ A≤D :=
  sourceCosetProductFun_le_iff M B C hT hd hc x
    (⟨A.1.val,A.1.property.1⟩,⟨A.2.val,A.2.property.1⟩)
    (⟨D.1.val,D.1.property.1⟩,⟨D.2.val,D.2.property.1⟩)

lemma sourceEligibleProductFun_surjective (Ref:Deligne M) (B C:Set S) (hT:IsSpherical M (B∪C))
    (hd:Disjoint B C) (hc:∀s∈B,∀t∈C,M s t=2) (x:Artin M) :
    Function.Surjective (sourceEligibleProductFun M Ref B C hT hd hc x) := by
  intro D
  obtain ⟨⟨a,b⟩,he⟩:=sourceCosetProductFun_surjective M B C hT hd hc x ⟨D.val,D.property.1⟩
  have hprop:∀i∈B∪C,i∉(sourceCosetProductFun M B C hT x (a,b)).val.val.1→
      SourceEligible M Ref (sourceCosetProductFun M B C hT x (a,b)).val i:=by
    rw [he]
    exact D.property.2
  have hh:=(sourceEligibleProduct_condition M Ref B C hT hd hc x (a,b)).mp hprop
  refine ⟨(⟨a.val,a.property,hh.1⟩,⟨b.val,b.property,hh.2⟩),?_⟩
  apply Subtype.ext
  change (sourceCosetProductFun M B C hT x (a,b)).val=D.val
  exact congrArg Subtype.val he

noncomputable def sourceEligibleProduct (Ref:Deligne M) (B C:Set S) (hT:IsSpherical M (B∪C))
    (hd:Disjoint B C) (hc:∀s∈B,∀t∈C,M s t=2) (x:Artin M) :
    (SourceEligibleWithin M Ref (sourceCoset M B (source_spherical_mono M Set.subset_union_left hT) x) ×
      SourceEligibleWithin M Ref (sourceCoset M C (source_spherical_mono M Set.subset_union_right hT) x)) ≃o
    SourceEligibleWithin M Ref (sourceCoset M (B∪C) hT x) :=
  OrderIso.ofSurjective
    (OrderEmbedding.ofMapLEIff (sourceEligibleProductFun M Ref B C hT hd hc x)
      (sourceEligibleProductFun_le_iff M Ref B C hT hd hc x))
    (sourceEligibleProductFun_surjective M Ref B C hT hd hc x)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_ResidueActive
attribute [-instance] _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder _root_.OAI.HarmonicArtin.sourceEligibleWithinTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open _root_.Matrix _root_.OAI.Matrix Simplicial CategoryTheory

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

lemma sourceResidueHeight_lt_of_ne {P Q R:Deligne M} {q:ℤ} (hQ:Q≤P) (hR:R≤P)
    (h:sourceCosetVector M Q q≤ sourceCosetVector M R q)
    (hn:sourceCosetVector M Q q≠sourceCosetVector M R q) :
    sourceResidueHeight M P Q q < sourceResidueHeight M P R q := by
  apply sourceResidueHeight_lt M h
  by_contra he
  apply hn
  funext v
  by_cases hv:v∈(Sum.inl:S→S⊕Unit) '' P.val.1
  · obtain ⟨i,hi,rfl⟩:=hv
    exact le_antisymm (h _) (le_of_not_gt (fun hl=>he ⟨i,hi,hl⟩))
  · exact (sourceCosetVector_upper_outside M hQ q v hv).symm.trans
      (sourceCosetVector_upper_outside M hR q v hv)

lemma sourceResidueUpper_meets {P X R:Deligne M} {q:ℤ} (hr:X<R) (hp:R≤P)
    (hh:sourceResidueHeight M P R q≤ sourceResidueHeight M P X q) :
    ∃i∈R.val.1,i∈sourceResidueActive M P X q := by
  by_contra hn
  have hnrow:∀i∈R.val.1,i∉X.val.1→(framedCartan M *ᵥ sourceCosetVector M X q) (.inl i)<0:=by
    intro i hi hxi
    exact lt_of_not_ge (fun hh=>hn ⟨i,hi,hp.1 hi,hxi,hh⟩)
  have hv:=sourceCosetVector_upper_monotone_int M hr.le q (fun i hi hx=>(hnrow i hi hx).le)
  have hne:sourceCosetVector M X q≠sourceCosetVector M R q:=by
    intro he
    obtain ⟨i,hi,hxi⟩:=Set.exists_of_ssubset (deligne_lt_type M hr)
    have hh:=hnrow i hi hxi
    rw [he,sourceCosetVector_harmonic M R q ⟨.inl i,⟨i,hi,rfl⟩⟩] at hh
    exact lt_irrefl _ hh
  exact (not_lt_of_ge hh) (sourceResidueHeight_lt_of_ne M (hr.le.trans hp) hp hv hne)

lemma sourceResidueUpper_active {P X R:Deligne M} {q:ℤ} (hr:X≤R)
    (ha:∀i∈R.val.1,i∉X.val.1→i∈sourceResidueActive M P X q) :
    sourceResidueHeight M P R q≤ sourceResidueHeight M P X q :=
  sourceResidueHeight_mono M (sourceCosetVector_upper_antitone_int M hr q (fun i hi hn=>(ha i hi hn).2.2))

noncomputable def sourceResidueUpperTop (P X:Deligne M) (q:ℤ) (hx:X≤P) : Deligne M :=
  sourceCoset M (X.val.1 ∪ sourceResidueActive M P X q)
    (source_spherical_mono M (show X.val.1 ∪ sourceResidueActive M P X q⊆P.val.1 from
      fun _ hi=>hi.elim (fun h=>hx.1 h) (fun h=>h.1)) P.property.1)
    (sourceCosetRepresentative M X)

lemma sourceResidueUpperClip_le {P X R:Deligne M} {q:ℤ} (h:X≤R) :
    sourceResidueUpperClip M P X R q≤R := by
  calc
    sourceResidueUpperClip M P X R q≤ sourceCoset M R.val.1 R.property.1 (sourceCosetRepresentative M X):=
      sourceCoset_le M Set.inter_subset_left _
    _=R:=sourceCoset_eq M R _ (h.2 (sourceCosetRepresentative_mem M X))

lemma sourceResidueUpperClip_mem {P X R:Deligne M} {q:ℤ}
    (h: X<R ∧ R<P ∧ sourceResidueHeight M P R q≤ sourceResidueHeight M P X q) :
    X < sourceResidueUpperClip M P X R q ∧ sourceResidueUpperClip M P X R q<P ∧
      sourceResidueHeight M P (sourceResidueUpperClip M P X R q) q≤ sourceResidueHeight M P X q := by
  have hl:=le_sourceResidueUpperClip M (P:=P) (q:=q) h.1.le
  refine ⟨lt_of_le_of_ne hl ?_,(sourceResidueUpperClip_le M h.1.le).trans_lt h.2.1,
    sourceResidueUpper_active M hl (fun _ hi hn=>hi.2.resolve_left hn)⟩
  intro he
  obtain ⟨i,hi,hd⟩:=sourceResidueUpper_meets M h.1 h.2.1.le h.2.2
  have ht:=congrArg (fun K:Deligne M=>K.val.1) he
  have hm:i∈(sourceResidueUpperClip M P X R q).val.1:=⟨hi,Or.inr hd⟩
  rw [←ht] at hm
  exact hd.2.1 hm

noncomputable def sourceResidueUpperRetraction (P X:Deligne M) (q:ℤ) :
    SourceResidueEarlierUpper M P X q →o SourceResidueEarlierUpper M P X q where
  toFun R:=⟨sourceResidueUpperClip M P X R q,sourceResidueUpperClip_mem M R.property⟩
  monotone':=by
    intro Y Z h
    change sourceResidueUpperClip M P X Y q≤ sourceResidueUpperClip M P X Z q
    exact sourceCoset_le M (show Y.val.val.1 ∩ (X.val.1 ∪ sourceResidueActive M P X q)⊆
      Z.val.val.1 ∩ (X.val.1 ∪ sourceResidueActive M P X q) from fun _ hi=>⟨h.1 hi.1,hi.2⟩) _

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_ResidueEarlierLower
attribute [-instance] _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder _root_.OAI.HarmonicArtin.sourceEligibleWithinTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open Simplicial CategoryTheory

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

lemma sourceResidueAllowed_trans {strict:Bool} {P Q R:Deligne M} {q:ℤ}
    (hQ:SourceResidueAllowed M strict P Q q) (hR:SourceResidueAllowed M true Q R q) :
    SourceResidueAllowed M strict P R q := by
  refine ⟨hR.1.trans hQ.1,?_⟩
  intro i hi hn
  by_cases hq:i∈Q.val.1
  · have hr:=hR.2 i hq hn
    have hl:sourceCosetVector M R q (.inl i) < sourceCosetVector M P q (.inl i):=
      lt_of_lt_of_le (by simpa only [↓reduceIte] using hr.2) (sourceResidueAllowed_le M hQ (.inl i))
    refine ⟨hr.1,?_⟩
    cases strict with
    | false => exact hl.le
    | true => exact hl
  · have he(d:ℤ):sourceCosetVector M Q d (.inl i)=sourceCosetVector M R d (.inl i):=
      sourceCosetVector_upper_outside M hR.1.le d _ (by
        rintro ⟨j,hj,hh⟩;exact hq ((Sum.inl_injective hh) ▸ hj))
    simpa only [he] using hQ.2 i hi hq

lemma sourceResidue_strict_height_drop {P Q R:Deligne M} {q:ℤ}
    (hQ:Q≤P) (hR:SourceResidueAllowed M true Q R q) :
    sourceResidueHeight M P R q < sourceResidueHeight M P Q q := by
  apply sourceResidueHeight_lt M (sourceResidueAllowed_le M hR)
  obtain ⟨i,hi,hn⟩:=Set.exists_of_ssubset (deligne_lt_type M hR.1)
  exact ⟨i,hQ.1 hi,by simpa only [↓reduceIte] using (hR.2 i hi hn).2⟩

lemma sourceResidueNegative_nonempty {P X Y:Deligne M} {q:ℤ} (hy:Y≤X)
    (hh:sourceResidueHeight M P Y q < sourceResidueHeight M P X q) :
    (sourceResidueNegative M X Y q).Nonempty := by
  by_contra hn
  have hc:sourceCosetVector M X q≤ sourceCosetVector M Y q:=by
    apply sourceCosetVector_lower_compare_int_rev M hy q
    intro i hi hnY
    exact le_of_not_gt (fun hl=>hn ⟨i,hi,hnY,hl⟩)
  exact (not_lt_of_ge (sourceResidueHeight_mono M hc)) hh

lemma sourceResidueNegative_shared {X Y Z:Deligne M} {q:ℤ} (h:Y≤Z) (i:S) (hi:i∉Z.val.1) :
    i∈sourceResidueNegative M X Y q ↔ i∈sourceResidueNegative M X Z q := by
  have hy:i∉Y.val.1:=fun hh=>hi (h.1 hh)
  have he:=sourceCosetVector_upper_outside M h q (.inl i) (by
    rintro ⟨j,hj,hh⟩;exact hi ((Sum.inl_injective hh) ▸ hj))
  simp only [sourceResidueNegative,Set.mem_ofPred_eq,hy,hi,not_false_eq_true,true_and,he]

lemma sourceResidueClose_le {X Y:Deligne M} {q:ℤ} (h:Y≤X) : sourceResidueClose M X Y q≤X := by
  calc
    sourceResidueClose M X Y q≤ sourceCoset M X.val.1 X.property.1 (sourceCosetRepresentative M Y):=
      sourceCoset_le M Set.sdiff_subset _
    _=X:=sourceCoset_eq M X _ (h.2 (sourceCosetRepresentative_mem M Y))

lemma sourceResidueClose_strict {strict:Bool} {P X Y:Deligne M} {q:ℤ}
    (hy:SourceResidueAllowed M strict P Y q) (hx:X≤P) (hyx:Y≤X)
    (hh:sourceResidueHeight M P Y q < sourceResidueHeight M P X q) :
    SourceResidueAllowed M true X (sourceResidueClose M X Y q) q := by
  refine ⟨lt_of_le_of_ne (sourceResidueClose_le M hyx) ?_,?_⟩
  · intro he
    obtain ⟨i,hi⟩:=sourceResidueNegative_nonempty M hyx hh
    have ht:=congrArg (fun K:Deligne M=>K.val.1) he
    have hm:i∈(sourceResidueClose M X Y q).val.1:=by rw [ht]; exact hi.1
    exact hm.2 hi
  · intro i hi hn
    have hc: i∈sourceResidueNegative M X Y q:=by
      by_contra hnot
      exact hn ⟨hi,hnot⟩
    have he(d:ℤ):sourceCosetVector M (sourceResidueClose M X Y q) d (.inl i)=sourceCosetVector M Y d (.inl i):=
      sourceCosetVector_upper_outside M (le_sourceResidueClose M hyx) d _ (by
        rintro ⟨j,hj,hh⟩;exact hn ((Sum.inl_injective hh) ▸ hj))
    simp only [↓reduceIte,he]
    exact ⟨(hy.2 i (hx.1 hi) hc.2.1).1,hc.2.2⟩

lemma sourceResidueClose_monotone {X Y Z:Deligne M} {q:ℤ} (h:Y≤Z) (hz:Z≤X) :
    sourceResidueClose M X Y q≤ sourceResidueClose M X Z q := by
  have ht:X.val.1 \ sourceResidueNegative M X Y q⊆X.val.1 \ sourceResidueNegative M X Z q:=by
    intro i hi
    refine ⟨hi.1,?_⟩
    intro hh
    exact hi.2 ((sourceResidueNegative_shared M h i hh.2.1).mpr hh)
  calc
    sourceResidueClose M X Y q≤ sourceCoset M (sourceResidueClose M X Z q).val.1
      (sourceResidueClose M X Z q).property.1 (sourceCosetRepresentative M Y):=sourceCoset_le M ht _
    _=sourceResidueClose M X Z q:=sourceCoset_eq M _ _
      ((le_sourceResidueClose M hz).2 (h.2 (sourceCosetRepresentative_mem M Y)))

lemma sourceResidueClose_eq {X Y:Deligne M} {q:ℤ}
    (h:SourceResidueAllowed M true X Y q) : sourceResidueClose M X Y q=Y := by
  symm
  apply deligne_eq_of_le_type_eq M (le_sourceResidueClose M h.1.le)
  ext i
  change i∈Y.val.1 ↔ i∈X.val.1 ∧ ¬i∈sourceResidueNegative M X Y q
  constructor
  · intro hi
    exact ⟨h.1.le.1 hi,fun hn=>hn.2.1 hi⟩
  · rintro ⟨hi,hn⟩
    by_contra hy
    exact hn ⟨hi,hy,by simpa only [↓reduceIte] using (h.2 i hi hy).2⟩

noncomputable def sourceResidueLowerInclusion {strict:Bool} {P X:Deligne M} {q:ℤ}
    (hX:SourceResidueAllowed M strict P X q) :
    SourceResidue M true X q →o SourceResidueEarlierLower M strict P X q where
  toFun Y:=⟨Y.val,sourceResidueAllowed_trans M hX Y.property,Y.property.1,
    sourceResidue_strict_height_drop M hX.1.le Y.property⟩
  monotone':=fun _ _ h=>h

noncomputable def sourceResidueLowerProjection {strict:Bool} {P X:Deligne M} {q:ℤ}
    (hX:SourceResidueAllowed M strict P X q) :
    SourceResidueEarlierLower M strict P X q →o SourceResidue M true X q where
  toFun Y:=⟨sourceResidueClose M X Y q,sourceResidueClose_strict M Y.property.1 hX.1.le
    Y.property.2.1.le Y.property.2.2⟩
  monotone':=fun _ Z h=>sourceResidueClose_monotone M h Z.property.2.1.le

noncomputable def sourceResidueLowerEquiv {strict:Bool} {P X:Deligne M} {q:ℤ}
    (hX:SourceResidueAllowed M strict P X q) :
    ContinuousMap.HomotopyEquiv |CategoryTheory.nerve (SourceResidueEarlierLower M strict P X q)|
      |CategoryTheory.nerve (SourceResidue M true X q)| :=
  nerveOrderRetractionEquiv (sourceResidueLowerProjection M hX) (sourceResidueLowerInclusion M hX)
    (by apply OrderHom.ext; funext Y; apply Subtype.ext; exact sourceResidueClose_eq M Y.property)
    (fun Y=>le_sourceResidueClose M Y.property.2.1.le)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_ResidueHeightZeroVector
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder _root_.OAI.HarmonicArtin.sourceEligibleWithinTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex _root_.Matrix _root_.OAI.Matrix

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

lemma sourceResidueHeight_zero_vector {strict:Bool} {P X:Deligne M} {q:ℤ}
    (hx:SourceResidueAllowed M strict P X q) (hh:sourceResidueHeight M P X q=0) :
    sourceCosetVector M X q=sourceCosetVector M P q := by
  have hn:=sourceResidueAllowed_le M hx
  funext v
  by_cases hp:v∈Sum.inl '' P.val.1
  · obtain ⟨i,hi,rfl⟩:=hp
    have hz:sourceCosetVector M X q (.inl i)-sourceCosetVector M P q (.inl i)=0 :=
      (Finset.sum_eq_zero_iff_of_nonpos (fun j _=>sub_nonpos.mpr (hn (.inl j)))).mp hh i (Set.mem_toFinset.mpr hi)
    exact sub_eq_zero.mp hz
  · exact (sourceCosetVector_upper_outside M hx.1.le q v hp).symm

lemma sourceResidueAllowed_closed_trans {P X Y:Deligne M} {q:ℤ}
    (hX:SourceResidueAllowed M false P X q) (hY:SourceResidueAllowed M false X Y q) :
    SourceResidueAllowed M false P Y q := by
  refine ⟨hY.1.trans hX.1,?_⟩
  intro i hi hni
  by_cases hxi:i∈X.val.1
  · have hv:=sourceResidueAllowed_le M hX (.inl i)
    exact ⟨(hY.2 i hxi hni).1,(hY.2 i hxi hni).2.trans hv⟩
  · have he(k:ℤ):sourceCosetVector M Y k (.inl i)=sourceCosetVector M X k (.inl i):=
      (sourceCosetVector_upper_outside M hY.1.le k _ (by
        rintro ⟨j,hj,hh⟩;exact hxi ((Sum.inl_injective hh) ▸ hj))).symm
    simpa only [he] using hX.2 i hi hxi

lemma sourceResidue_zero_lower_iff {P X Y:Deligne M} {q:ℤ}
    (hx:SourceResidueAllowed M false P X q) (hh:sourceResidueHeight M P X q=0) (hy:Y<X) :
    SourceResidueAllowed M false P Y q ↔ SourceResidueAllowed M false X Y q := by
  constructor
  · intro hY
    refine ⟨hy,?_⟩
    intro i hi hni
    rw [sourceResidueHeight_zero_vector M hx hh]
    exact hY.2 i (hx.1.le.1 hi) hni
  · exact sourceResidueAllowed_closed_trans M hx

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_ResidueRank
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder _root_.OAI.HarmonicArtin.sourceEligibleWithinTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

lemma sourceResidueHeight_range_finite (strict:Bool) (P:Deligne M) (q:ℤ) :
    (Set.range (fun X:SourceResidue M strict P q=>sourceResidueHeight M P X q)).Finite := by
  let A: Set (S⊕Unit→ℝ):={v | ∃X:Deligne M,∃k:ℤ,sourceCosetSum M X k≤ sourceCosetSum M P q ∧ v=sourceCosetVector M X k}
  have hA:A.Finite:=sourceCosetVector_bounded_finite M _
  apply (hA.image (fun v:S⊕Unit→ℝ=>∑i∈P.val.1.toFinset,(v (.inl i)-sourceCosetVector M P q (.inl i)))).subset
  rintro h ⟨X,rfl⟩
  refine ⟨sourceCosetVector M X q,⟨X,q,?_,rfl⟩,rfl⟩
  exact Finset.sum_le_sum (fun i _=>sourceResidueAllowed_le M X.property i)

lemma sourceResidueRank_strictMono (strict:Bool) (P:Deligne M) (q:ℤ) {a b:ℝ}
    (ha:a∈Set.range (fun X:SourceResidue M strict P q=>sourceResidueHeight M P X q)) (hab:a<b) :
    sourceResidueRank M strict P q a < sourceResidueRank M strict P q b := by
  apply Set.ncard_lt_ncard _ ((sourceResidueHeight_range_finite M strict P q).subset (fun _ h=>h.1))
  refine ⟨fun _ h=>⟨h.1,h.2.trans hab⟩,?_⟩
  intro h
  exact (h ⟨ha,hab⟩).2.false

lemma sourceResidueRank_lt_iff (strict:Bool) (P:Deligne M) (q:ℤ)
    (X Y:SourceResidue M strict P q) :
    sourceResidueRank M strict P q (sourceResidueHeight M P X q)<
      sourceResidueRank M strict P q (sourceResidueHeight M P Y q) ↔
      sourceResidueHeight M P X q < sourceResidueHeight M P Y q := by
  constructor
  · intro h
    by_contra hn
    rcases lt_or_eq_of_le (le_of_not_gt hn) with hh|hh
    · have ht:=sourceResidueRank_strictMono M strict P q ⟨Y,rfl⟩ hh
      exact (not_lt_of_ge h.le) ht
    · rw [hh] at h
      exact h.false
  · exact sourceResidueRank_strictMono M strict P q ⟨X,rfl⟩

lemma sourceResidueRank_eq_iff (strict:Bool) (P:Deligne M) (q:ℤ)
    (X Y:SourceResidue M strict P q) :
    sourceResidueRank M strict P q (sourceResidueHeight M P X q)=
      sourceResidueRank M strict P q (sourceResidueHeight M P Y q) ↔
      sourceResidueHeight M P X q=sourceResidueHeight M P Y q := by
  constructor
  · intro he
    rcases lt_trichotomy (sourceResidueHeight M P X q) (sourceResidueHeight M P Y q) with h|h|h
    · have :=(sourceResidueRank_lt_iff M strict P q X Y).mpr h;omega
    · exact h
    · have :=(sourceResidueRank_lt_iff M strict P q Y X).mpr h;omega
  · intro h;rw[h]

lemma sourceResidueEarlier_iff (strict:Bool) (P:Deligne M) (q:ℤ)
    (X Y:SourceResidue M strict P q) :
    SourceResidueEarlier M strict P q X Y ↔
      sourceResidueHeight M P X q < sourceResidueHeight M P Y q ∨
      sourceResidueHeight M P X q=sourceResidueHeight M P Y q ∧
        (sourceResidueSecondary M P X q < sourceResidueSecondary M P Y q ∨
          sourceResidueSecondary M P X q=sourceResidueSecondary M P Y q ∧ sourceTieCode M X < sourceTieCode M Y) := by
  change _< _ ↔ _
  rw [Prod.Lex.lt_iff]
  simp only [sourceResidueKey,ofLex_toLex,sourceResidueRank_lt_iff,sourceResidueRank_eq_iff,Prod.Lex.lt_iff]

lemma sourceResidueEarlier_lower_negative {strict:Bool} {P:Deligne M} {q:ℤ}
    (X Y:SourceResidue M strict P q) (h:Y.val<X.val) (hh:sourceResidueHeight M P X q<0) :
    SourceResidueEarlier M strict P q Y X ↔ sourceResidueHeight M P Y q < sourceResidueHeight M P X q := by
  rw [sourceResidueEarlier_iff]
  have hn:Y.val.val.1.ncard<X.val.val.1.ncard:=Set.ncard_lt_ncard (deligne_lt_type M h) (Set.toFinite _)
  have hb:X.val.val.1.ncard≤Fintype.card S:=by simpa only [Nat.card_eq_fintype_card] using Set.ncard_le_card X.val.val.1
  constructor
  · rintro (h|⟨he,h⟩)
    · exact h
    · have hy:sourceResidueHeight M P Y q<0:=he ▸ hh
      simp only [sourceResidueSecondary,hy,hh,ite_eq_left] at h
      omega
  · exact Or.inl

lemma sourceResidueEarlier_upper_negative {strict:Bool} {P:Deligne M} {q:ℤ}
    (X Y:SourceResidue M strict P q) (h:X.val<Y.val) (hh:sourceResidueHeight M P X q<0) :
    SourceResidueEarlier M strict P q Y X ↔ sourceResidueHeight M P Y q≤ sourceResidueHeight M P X q := by
  rw [sourceResidueEarlier_iff]
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
      have hy:sourceResidueHeight M P Y q<0:=he ▸ hh
      simp only [sourceResidueSecondary,hy,hh,ite_eq_left]
      omega

lemma sourceResidueEarlier_lower_zero {P:Deligne M} {q:ℤ}
    (X Y:SourceResidue M false P q) (h:Y.val<X.val) (hh:sourceResidueHeight M P X q=0) :
    SourceResidueEarlier M false P q Y X := by
  rw [sourceResidueEarlier_iff]
  have hn:Y.val.val.1.ncard<X.val.val.1.ncard:=Set.ncard_lt_ncard (deligne_lt_type M h) (Set.toFinite _)
  rcases lt_or_eq_of_le (sourceResidueHeight_nonpos M Y.property) with h|he
  · exact Or.inl (hh ▸ h)
  · refine Or.inr ⟨he.trans hh.symm,Or.inl ?_⟩
    simpa only [sourceResidueSecondary,he,hh,lt_self_iff_false,ite_false, if_false] using hn

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_ResidueEarlierLowerIso
attribute [-instance] _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder _root_.OAI.HarmonicArtin.sourceEligibleWithinTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

noncomputable def sourceResidueEarlierLowerIso {strict:Bool} {P:Deligne M} {q:ℤ}
    (X:SourceResidue M strict P q) (hh:sourceResidueHeight M P X q<0) :
    WeightEarlierLower (SourceResidueEarlier M strict P q) X ≃o
      SourceResidueEarlierLower M strict P X q where
  toFun Y:=⟨Y.val.val,Y.val.property,Y.property.2,
    (sourceResidueEarlier_lower_negative M X Y.val Y.property.2 hh).mp Y.property.1⟩
  invFun Y:=⟨⟨Y.val,Y.property.1⟩,
    (sourceResidueEarlier_lower_negative M X ⟨Y.val,Y.property.1⟩ Y.property.2.1 hh).mpr Y.property.2.2,
    Y.property.2.1⟩
  left_inv _:=rfl
  right_inv _:=rfl
  map_rel_iff':=by intros;rfl

noncomputable def sourceResidueEarlierUpperIso {strict:Bool} {P:Deligne M} {q:ℤ}
    (X:SourceResidue M strict P q) (hh:sourceResidueHeight M P X q<0) :
    WeightEarlierUpper (SourceResidueEarlier M strict P q) X ≃o
      SourceResidueEarlierUpper M P X q where
  toFun Y:=⟨Y.val.val,Y.property.2,Y.val.property.1,
    (sourceResidueEarlier_upper_negative M X Y.val Y.property.2 hh).mp Y.property.1⟩
  invFun Y:=⟨⟨Y.val,sourceResidueAllowed_upper M X.property Y.property.1.le Y.property.2.1⟩,
    (sourceResidueEarlier_upper_negative M X _ Y.property.1 hh).mpr Y.property.2.2,Y.property.1⟩
  left_inv _:=rfl
  right_inv _:=rfl
  map_rel_iff':=by intros;rfl

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_EligibleFactor
attribute [-instance] _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

noncomputable def sourceEligibleProductPuncture (Ref:Deligne M) (B C:Set S) (hT:IsSpherical M (B∪C))
    (hd:Disjoint B C) (hc:∀s∈B,∀t∈C,M s t=2) (x:Artin M) :
    BinaryProductBoundary
      (SourceEligibleWithin M Ref (sourceCoset M B (source_spherical_mono M Set.subset_union_left hT) x))
      (SourceEligibleWithin M Ref (sourceCoset M C (source_spherical_mono M Set.subset_union_right hT) x)) ≃o
      {V:SourceEligibleWithin M Ref (sourceCoset M (B∪C) hT x) //V≠⊤} :=
  { toFun:=fun V=>⟨sourceEligibleProduct M Ref B C hT hd hc x V.val,by
      intro he
      exact V.property ((sourceEligibleProduct M Ref B C hT hd hc x).injective
        (he.trans (sourceEligibleProduct M Ref B C hT hd hc x).map_top.symm))⟩
    invFun:=fun V=>⟨(sourceEligibleProduct M Ref B C hT hd hc x).symm V.val,by
      intro he
      apply V.property
      rw [←(sourceEligibleProduct M Ref B C hT hd hc x).apply_symm_apply V.val,he,
        (sourceEligibleProduct M Ref B C hT hd hc x).map_top]⟩
    left_inv:=fun V=>Subtype.ext ((sourceEligibleProduct M Ref B C hT hd hc x).symm_apply_apply V.val)
    right_inv:=fun V=>Subtype.ext ((sourceEligibleProduct M Ref B C hT hd hc x).apply_symm_apply V.val)
    map_rel_iff':=by intros;exact (sourceEligibleProduct M Ref B C hT hd hc x).map_rel_iff }

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_ResidueZeroLowerIso
attribute [-instance] _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder _root_.OAI.HarmonicArtin.sourceEligibleWithinTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open Simplicial CategoryTheory
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

noncomputable def sourceResidueZeroLowerIso {P:Deligne M} {q:ℤ}
    (X:SourceResidue M false P q) (hh:sourceResidueHeight M P X q=0) :
    WeightEarlierLower (SourceResidueEarlier M false P q) X ≃o SourceResidue M false X q where
  toFun Y:=⟨Y.val.val,(sourceResidue_zero_lower_iff M X.property hh Y.property.2).mp Y.val.property⟩
  invFun Y:=⟨⟨Y.val,sourceResidueAllowed_closed_trans M X.property Y.property⟩,
    sourceResidueEarlier_lower_zero M X _ Y.property.1 hh,Y.property.1⟩
  left_inv _:=rfl
  right_inv _:=rfl
  map_rel_iff':=by intros;rfl

end HarmonicArtin

end OAI
end


