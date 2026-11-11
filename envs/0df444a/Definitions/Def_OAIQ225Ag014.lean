-- Prove2me | Definitions.Def_OAIQ225Ag014
-- name    : OAIQ225Ag014
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T17:56:46.642303+00:00
-- url     : https://prove2.me/theorems/4c3b911b-b2c2-4782-93ab-5051d4527b8e
-- title:
--   Definitions bundle OAIQ225Ag014 of the split of OpenAI, Harmonic heights and the Artin K(pi,1) conjecture
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.HarmonicArtin.salvetti_cover_contractible`, carved from OpenAI's openai/math development (OpenAI, *Harmonic heights and the Artin K(pi,1) conjecture*, OpenAI Math Release, September 23, 2026, result family 254, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 9 declarations of OpenAI's Lean: 4 definitions, 1 instance and 4 theorems. The definitions and types are `OAI.HarmonicArtin.sourceEligibleFactor`, `OAI.HarmonicArtin.sourceEligiblePuncture`, `OAI.HarmonicArtin.sourceNullPatch`, `OAI.HarmonicArtin.sourceTypeComponent`.
--
--   **Sources.** They come from these modules of lean/OAI/Topology, in whole or in part: [`ArtinGroups_Harmonic_EligibleFactor`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/ArtinGroups/Harmonic/EligibleFactor.lean), [`ArtinGroups_Harmonic_EligibleWithin`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/ArtinGroups/Harmonic/EligibleWithin.lean), [`ArtinGroups_Harmonic_IncidentNonnegRowPositive`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/ArtinGroups/Harmonic/IncidentNonnegRowPositive.lean), [`ArtinGroups_Harmonic_NullPatch2`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/ArtinGroups/Harmonic/NullPatch2.lean), [`ArtinGroups_Harmonic_ResidueAllowed`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/ArtinGroups/Harmonic/ResidueAllowed.lean), [`ArtinGroups_Harmonic_TypeComponent`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/ArtinGroups/Harmonic/TypeComponent.lean).
--
--   **Imports.** It imports the published bundle `Def_HarmonicArtin`; the bundle `OAIQ225Ag011` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ225Ag015`.
-- source:
--   OpenAI, Harmonic heights and the Artin K(pi,1) conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 254; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Harmonic-heights-and-the-Artin-K-pi-1-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Topology at commit adc7f12

import Mathlib
import Definitions.Def_HarmonicArtin
import Definitions.Def_OAIQ225Ag011

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

lemma sourceResidueHeight_mono {P Q R:Deligne M} {q:ℤ}
    (h:sourceCosetVector M Q q≤ sourceCosetVector M R q) :
    sourceResidueHeight M P Q q≤ sourceResidueHeight M P R q :=
  Finset.sum_le_sum (fun i _=>sub_le_sub_right (h (.inl i)) _)

lemma sourceResidueHeight_lt {P Q R:Deligne M} {q:ℤ}
    (h:sourceCosetVector M Q q≤ sourceCosetVector M R q)
    (hn:∃i∈P.val.1,sourceCosetVector M Q q (.inl i) < sourceCosetVector M R q (.inl i)) :
    sourceResidueHeight M P Q q < sourceResidueHeight M P R q := by
  apply Finset.sum_lt_sum (fun i _=>sub_le_sub_right (h (.inl i)) _)
  obtain ⟨i,hi,hl⟩:=hn
  exact ⟨i,Set.mem_toFinset.mpr hi,sub_lt_sub_right hl _⟩

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

instance sourceEligibleWithinTop (P R:Deligne M) : OrderTop (SourceEligibleWithin M P R) where
  top:=⟨R,le_rfl,fun _ h hn=>(hn h).elim⟩
  le_top:=fun Q=>Q.property.1

noncomputable def sourceEligiblePuncture (P:Deligne M) :
    {Q:SourceEligibleWithin M P P //Q≠⊤} ≃o SourceAllEligibleLower M P where
  toFun Q:=⟨Q.val.val,lt_of_le_of_ne Q.val.property.1 (fun he=>Q.property (Subtype.ext he)),Q.val.property.2⟩
  invFun Q:=⟨⟨Q.val,Q.property.1.le,Q.property.2⟩,by intro he;exact Q.property.1.ne (congrArg Subtype.val he)⟩
  left_inv _:=rfl
  right_inv _:=rfl
  map_rel_iff':=Iff.rfl

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

lemma sourceEligible_factor_iff (P R V:Deligne M) (hRP:R.val.1⊆P.val.1)
    (q:ℕ) (strict:Bool) (hp:∀i∈R.val.1,sourcePeak M P i=q)
    (hs:∀i∈R.val.1,sourceCosetSign M P q (.inl i)=if strict then -1 else 1)
    (hv:∀i∈R.val.1,sourceCosetVector M R q (.inl i)=sourceCosetVector M P q (.inl i))
    (i:S) (hi:i∈R.val.1) (ho:i∉V.val.1) :
    SourceEligible M P V i ↔
      (∀d:ℤ,(q:ℤ)<d→sourceCosetVector M V d (.inl i)=0) ∧
      (if strict then sourceCosetVector M V q (.inl i) < sourceCosetVector M R q (.inl i)
        else sourceCosetVector M V q (.inl i) ≤ sourceCosetVector M R q (.inl i)) := by
  have hcap:(∀d:ℕ,q<d→sourceCosetVector M V d (.inl i)=0) ↔
      (∀d:ℤ,(q:ℤ)<d→sourceCosetVector M V d (.inl i)=0):=by
    constructor
    · intro h d hd
      have hn:0≤d:=by omega
      have he:(d.toNat:ℤ)=d:=Int.toNat_of_nonneg hn
      rw [←he]
      exact h d.toNat (by omega)
    · intro h d hd
      exact h d (by exact_mod_cast hd)
  simp only [SourceEligible,hRP hi,ho,true_and,hp i hi,hcap,hs i hi,←hv i hi]
  cases strict <;> simp only [Bool.false_eq_true,↓reduceIte,Int.reduceNeg,Int.reduceEq,not_false_eq_true,true_and,and_true,
    and_false,or_false]
  constructor
  · rintro ⟨ha,hb⟩
    exact ⟨ha,hb.elim le_of_lt le_of_eq⟩
  · rintro ⟨ha,hb⟩
    exact ⟨ha,lt_or_eq_of_le hb⟩

noncomputable def sourceEligibleFactor (P R:Deligne M) (hRP:R.val.1⊆P.val.1)
    (q:ℕ) (strict:Bool) (hp:∀i∈R.val.1,sourcePeak M P i=q)
    (hs:∀i∈R.val.1,sourceCosetSign M P q (.inl i)=if strict then -1 else 1)
    (hv:∀i∈R.val.1,sourceCosetVector M R q (.inl i)=sourceCosetVector M P q (.inl i)) :
    {V:SourceEligibleWithin M P R // V≠⊤} ≃o SourceResidue M strict R q where
  toFun V:=⟨V.val.val,lt_of_le_of_ne V.val.property.1 (fun he=>V.property (Subtype.ext he)),
    fun i hi ho=>(sourceEligible_factor_iff M P R V.val.val hRP q strict hp hs hv i hi ho).mp
      (V.val.property.2 i hi ho)⟩
  invFun V:=⟨⟨V.val,V.property.1.le,fun i hi ho=>
    (sourceEligible_factor_iff M P R V.val hRP q strict hp hs hv i hi ho).mpr (V.property.2 i hi ho)⟩,
    fun he=>V.property.1.ne (congrArg Subtype.val he)⟩
  left_inv _:=rfl
  right_inv _:=rfl
  map_rel_iff':=by intros;rfl

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

lemma source_incident_nonneg_row_positive (P:Deligne M) (k:ℕ) (i:S)
    (hi:levelIncident (framedCartan M) (sourceCosetProfile M P) k (.inl i))
    (hr:0≤(framedCartan M *ᵥ sourceCosetVector M P k) (.inl i)) :
    0 < sourceCosetVector M P k (.inl i) := by
  rcases hi with hi|⟨j,hij,hj⟩
  · exact hi
  by_contra hn
  have hz:sourceCosetVector M P k (.inl i)=0:=
    le_antisymm (le_of_not_gt hn) (sourceCosetVector_nonneg M P k _)
  have ht:∀l∈(Finset.univ:Finset (S⊕Unit)),
      framedCartan M (.inl i) l*sourceCosetVector M P k l≤0:=by
    intro l _
    by_cases hl:(.inl i:S⊕Unit)=l
    · subst l; rw [hz,mul_zero]
    · exact mul_nonpos_of_nonpos_of_nonneg (framedCartan_off M _ _ hl)
        (sourceCosetVector_nonneg M P k l)
  exact (not_lt_of_ge hr) (Finset.sum_neg' ht
    ⟨j,Finset.mem_univ _,mul_neg_of_neg_of_pos hij hj⟩)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_TypeComponent
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.sourceEligibleWithinTop
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

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_NullPatch2
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.sourceEligibleWithinTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open _root_.Matrix _root_.OAI.Matrix ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

noncomputable def sourceNullPatch (P:Deligne M) (q:ℕ) (i:S⊕Unit) (v:S⊕Unit) : ℝ :=
  if v∈sourcePositiveComponent M (sourceCosetVector M P q) i then sourceCosetVector M P q v else 0

end HarmonicArtin

end OAI
end


