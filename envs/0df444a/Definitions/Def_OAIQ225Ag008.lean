-- Prove2me | Definitions.Def_OAIQ225Ag008
-- name    : OAIQ225Ag008
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T17:23:07.828969+00:00
-- url     : https://prove2.me/theorems/0a0c8b79-0d8b-46c5-979b-5fe6288a5cd3
-- title:
--   Definitions bundle OAIQ225Ag008 of the split of OpenAI, Harmonic heights and the Artin K(pi,1) conjecture
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.HarmonicArtin.salvetti_cover_contractible`, carved from OpenAI's openai/math development (OpenAI, *Harmonic heights and the Artin K(pi,1) conjecture*, OpenAI Math Release, September 23, 2026, result family 254, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 94 declarations of OpenAI's Lean: 26 definitions, 2 instances and 66 theorems. The definitions and types are `OAI.HarmonicArtin.fusionArrowAtEquiv`, `OAI.HarmonicArtin.liftedTopVertex`, `OAI.HarmonicArtin.matchingLetter`, `OAI.HarmonicArtin.matchingOtherType`, `OAI.HarmonicArtin.nerveCone`, `OAI.HarmonicArtin.nerveConeMap`, `OAI.HarmonicArtin.nerveToWeights`, `OAI.HarmonicArtin.nerveTopCone`, `OAI.HarmonicArtin.nerveTopConeMap`, `OAI.HarmonicArtin.nerveVertex`, `OAI.HarmonicArtin.nerveWeightsHomeomorph`, `OAI.HarmonicArtin.nerveWeightsMap`, `OAI.HarmonicArtin.nerveWeightsSimplex`, `OAI.HarmonicArtin.positiveCellEmbedding`, `OAI.HarmonicArtin.positiveCellRegionIso`, `OAI.HarmonicArtin.positiveCellToLifted`, `OAI.HarmonicArtin.positivePuncturedBoundaryIso`, `OAI.HarmonicArtin.positiveRegionDeckIso`, `OAI.HarmonicArtin.positiveRootCell`, `OAI.HarmonicArtin.probeCoreInclusion`, `OAI.HarmonicArtin.restrictedLiftedCell`, `OAI.HarmonicArtin.sourceConvexWord`, `OAI.HarmonicArtin.sourceParabolicProductMap`, `OAI.HarmonicArtin.supportedWeightMap`, `OAI.HarmonicArtin.weightDualHomeomorph`, `OAI.HarmonicArtin.weightsToNerve`.
--
--   **Sources.** They come from these modules of lean/OAI/Topology, in whole or in part: `ArtinGroups_Coxeter_ParabolicLongest`, `ArtinGroups_Coxeter_ParabolicProductMap`, `ArtinGroups_Geometry_ConvexWord`, `ArtinGroups_Harmonic_Candidate`, `ArtinGroups_Harmonic_Coset`, `ArtinGroups_Harmonic_CosetBelow`, `ArtinGroups_Harmonic_FusionVertex`, `ArtinGroups_Harmonic_LiftedDeck`, `ArtinGroups_Harmonic_PositiveDegreeHom`, `ArtinGroups_Harmonic_PositiveDescentSet`, `ArtinGroups_Harmonic_PositivePrefix`, `ArtinGroups_Harmonic_PositiveRegion`, `ArtinGroups_Harmonic_PositiveRegionDeckIso`, `ArtinGroups_Harmonic_ProbeCoreInclusion`, `ArtinGroups_Harmonic_ProbeFixedOutside`, `ArtinGroups_Harmonic_PuncturedBoundaryIso`, `ArtinGroups_Harmonic_RestrictedArtinHom`, `ArtinGroups_Harmonic_SphericalLongest`, `ArtinGroups_Harmonic_TopBlockMatchingKey`, `ArtinGroups_Harmonic_UnfoldedFullWordMem`, `ArtinGroups_Harmonic_UnfoldedHom`, `ArtinGroups_Harmonic_UnfoldedInclusion`, `ArtinGroups_Harmonic_WordFrontData`, `ArtinGroups_Realizations_NerveChain`, `ArtinGroups_Realizations_NerveOrderMap`, `ArtinGroups_Realizations_NoncriticalPositiveCell`, `ArtinGroups_Realizations_PositiveCellPoset`, `ArtinGroups_Realizations_PositiveCellPoset2`, `ArtinGroups_Realizations_PositiveLiftedCell`, `ArtinGroups_Realizations_PositiveRootCell`, `ArtinGroups_Realizations_RealizeSimplex`, `ArtinGroups_Realizations_RestrictedCellEmbedding`, `ArtinGroups_Realizations_RestrictedLiftedCell`, `ArtinGroups_Realizations_WeightDual`.
--
--   **Imports.** It imports the published bundle `Def_HarmonicArtin`; the bundles `OAIQ225Ag002`, `OAIQ225Ag003` and `OAIQ225Ag004` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ225Ag010`.
-- source:
--   OpenAI, Harmonic heights and the Artin K(pi,1) conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 254; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Harmonic-heights-and-the-Artin-K-pi-1-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Topology at commit adc7f12

import Mathlib
import Definitions.Def_HarmonicArtin
import Definitions.Def_OAIQ225Ag002
import Definitions.Def_OAIQ225Ag003
import Definitions.Def_OAIQ225Ag004

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_PositiveDegreeHom
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CoxeterExchange

universe u
variable {S:Type u} (M:CoxeterMatrix S)

lemma positiveDegree_zero_iff (a:PositiveArtin M) : positiveDegree M a=0 ↔ a=1 := by
  obtain ⟨w,rfl⟩:=positive_word_surjective M a
  rw [positiveDegree_word]
  constructor
  · intro h;rw [List.eq_nil_of_length_eq_zero h];rfl
  · intro h;simpa only [positiveDegree_word,positiveDegree_one] using congrArg (positiveDegree M) h

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_PositivePrefix
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CoxeterExchange

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type*} (M:CoxeterMatrix S)

lemma positivePrefix_eq_of_degree {a b:PositiveArtin M} (h:PositivePrefix M a b)
    (he:positiveDegree M a=positiveDegree M b) : a=b := by
  obtain ⟨c,rfl⟩:=h
  rw [positiveDegree_mul] at he
  have hc:c=1:=(positiveDegree_zero_iff M c).mp (by omega)
  rw [hc,mul_one]

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Coxeter_ParabolicLongest
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type*} [Fintype S] (M:CoxeterMatrix S)

lemma parabolic_longest_length_mul (T:Set S) (z:M.Group) (hz:IsParabolicLongest M T z)
    (w:M.Group) (hw:w∈coxeterParabolic M T) :
    M.toCoxeterSystem.length (z*w)+M.toCoxeterSystem.length w=M.toCoxeterSystem.length z := by
  have hr:∀x∈coxeterParabolic M T,∃q:(restrictedMatrix M T).Group,restrictionHom M T q=x:=by
    intro x hx
    exact (show x∈(restrictionHom M T).range by rw [restrictionHom_range_eq];exact hx)
  obtain ⟨q,rfl⟩:=hr z hz.1
  obtain ⟨r,rfl⟩:=hr w hw
  have hq:∀v:(restrictedMatrix M T).Group,(restrictedMatrix M T).toCoxeterSystem.length v≤
      (restrictedMatrix M T).toCoxeterSystem.length q:=by
    intro v
    simpa only [restriction_length] using hz.2 _ (Geometric.restrictionHom_mem_parabolic M T v)
  rw [←map_mul,restriction_length,restriction_length,restriction_length]
  exact length_mul_of_all_descents (restrictedMatrix M T).toCoxeterSystem q
    (all_descents_of_longest (restrictedMatrix M T).toCoxeterSystem q hq) r

lemma parabolic_longest_inverse (T:Set S) (z:M.Group) (hz:IsParabolicLongest M T z) : z⁻¹=z := by
  have hh:=parabolic_longest_length_mul M T z hz z hz.1
  have hz2:z*z=1:=M.toCoxeterSystem.length_eq_zero_iff.mp (by omega)
  calc z⁻¹=z⁻¹*(z*z):=by rw [hz2,mul_one]
       _=z:=by group

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_FusionVertex
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_UnfoldedHom
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_UnfoldedInclusion
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instDecidableRelStringLabelStringAdjacent
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_ProbeCoreInclusion
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.liftedPartialOrder
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

abbrev probeCoreInclusion (J:Set S) (α:J × FusionLabel m) : ProbeVertex (FusionVertex (V:=S⊕Unit) m) :=
  Sum.inl (unfoldedInclusion M J α)

omit [Fintype S] in
lemma probeCoreInclusion_injective (J:Set S) : Function.Injective (probeCoreInclusion M J) :=
  fun _ _ he=>unfoldedInclusion_injective M J (Sum.inl.inj he)

lemma probeCore_word_support (J:Set S) (w:List J) :
    ∀ α∈(fusionExpandedWord m w).map (probeCoreInclusion M J),
      α∈Set.range (probeCoreInclusion M J) := by
  intro α hα
  obtain ⟨β,_,rfl⟩:=List.mem_map.mp hα
  exact ⟨β,rfl⟩

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_RestrictedArtinHom
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.liftedPartialOrder
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.positiveToArtin_generator _root_.OAI.HarmonicArtin.positiveToArtin_word _root_.OAI.HarmonicArtin.unfoldedHom_simple
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_UnfoldedFullWordMem
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.liftedPartialOrder
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

lemma unfolded_full_word_mem (J : Set S) (u : List J) :
    ∀ α∈fusionExpandedWord (fusionLabelSize M) (u.map fun j : J => (Sum.inl (j:S) : S⊕Unit)),
      α∈Set.range (unfoldedInclusion M J) := by
  intro α hα
  have hh:=fusionExpandedWord_mem (fusionLabelSize M) _ α hα
  obtain ⟨j,_,hj⟩:=List.mem_map.mp hh
  exact ⟨(j,α.2),Prod.ext hj rfl⟩

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Geometry_ConvexWord
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

noncomputable def sourceConvexWord (J:Set S) (w:(restrictedMatrix M J).Group) : List J :=
  reducedExpression (restrictedMatrix M J) w⁻¹

omit [Fintype S] [LinearOrder S] in
lemma sourceConvexWord_reduced (J:Set S) (w:(restrictedMatrix M J).Group) :
    (restrictedMatrix M J).toCoxeterSystem.IsReduced (sourceConvexWord M J w) :=
  reducedExpression_reduced _ _

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_ProbeFixedOutside
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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

omit [Fintype S] [LinearOrder S] in
lemma sourceParabolic_empty : artinParabolic M ∅=⊥ := by simp [artinParabolic]

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Coxeter_ParabolicProductMap
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.liftedPartialOrder
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.positiveToArtin_generator _root_.OAI.HarmonicArtin.positiveToArtin_word
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

omit [Fintype S] [LinearOrder S] in
lemma sourceGenerators_commute {s t:S} (h:M s t=2) : Commute (generator M s) (generator M t) := by
  have he:=wordArtin_braid M s t
  change generator M s * generator M t = generator M t * generator M s
  simpa [h,CoxeterExchange.altList,wordArtin] using he

omit [Fintype S] [LinearOrder S] in
lemma sourceParabolics_commute (B C:Set S) (h:∀s∈B,∀t∈C,M s t=2)
    (b c:Artin M) (hb:b∈artinParabolic M B) (hc:c∈artinParabolic M C) : Commute b c := by
  have hh:artinParabolic M B≤Subgroup.centralizer (artinParabolic M C:Set (Artin M)):=by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨s,hs,rfl⟩
    change generator M s∈Subgroup.centralizer (Subgroup.closure ((generator M) '' C):Set (Artin M))
    rw [Subgroup.centralizer_closure]
    rintro _ ⟨t,ht,rfl⟩
    exact (sourceGenerators_commute M (h s hs t ht)).symm.eq
  exact (hh hb c hc).symm

omit [Fintype S] [LinearOrder S] in
lemma sourceParabolic_union (B C:Set S) :
    artinParabolic M (B∪C)=artinParabolic M B⊔artinParabolic M C := by
  simp only [artinParabolic,Set.image_union,Subgroup.closure_union]

noncomputable def sourceParabolicProductMap (B C:Set S) (hc:∀s∈B,∀t∈C,M s t=2) :
    artinParabolic M B × artinParabolic M C →* Artin M :=
  (artinParabolic M B).subtype.noncommCoprod (artinParabolic M C).subtype
    (fun b c=>sourceParabolics_commute M B C hc b c b.property c.property)

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
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_Candidate
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.liftedPartialOrder
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_Coset
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
lemma rightCoset_mono {T U:Set S} (h:T⊆U) (x:Artin M) : rightCoset M T x⊆rightCoset M U x :=
  fun _ hy=>artinParabolic_mono M h hy

omit [Fintype S] [LinearOrder S] in
lemma sourceCoset_le {T U:Set S} {hT:IsSpherical M T} {hU:IsSpherical M U}
    (h:T⊆U) (x:Artin M) : sourceCoset M T hT x ≤ sourceCoset M U hU x :=
  ⟨h,rightCoset_mono M h x⟩

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_CosetBelow
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_LiftedDeck
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderLiftedPuncturedBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
universe u
variable {S:Type u} (M:CoxeterMatrix S)

instance instPartialOrderSphericalLiftedFiber (T:Set S) : PartialOrder (SphericalLiftedFiber M T) :=
  inferInstanceAs (PartialOrder {a:LiftedCell M // a.2.val⊆T ∧ a.1∈artinParabolic M T})

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_WordFrontData
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.positiveReverse_generator _root_.OAI.HarmonicArtin.positiveReverse_involutive _root_.OAI.HarmonicArtin.positiveReverse_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CoxeterExchange

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type*} [Fintype S] (M:CoxeterMatrix S)

omit [Fintype S] in
lemma wordFront_mul {u v w x:List S} (h:WordFrontData M u v) (k:WordFrontData M w x) : WordFrontData M (u++w) (v++x) := by
  refine ⟨by rw [wordPositive_append,wordPositive_append,h.1,k.1],by simp only [List.length_append,h.2.1,k.2.1],?_⟩
  intro s us t ts hu hv
  cases u with
  | nil=>
    have he:v=[]:=List.length_eq_zero_iff.mp h.2.1.symm
    subst v
    exact k.2.2 s us t ts hu hv
  | cons r rs=>
    cases v with
    | nil=>have hh:=h.2.1;simp at hh
    | cons q qs=>
      have hs:r=s:=(List.cons.inj hu).1
      have ht:q=t:=(List.cons.inj hv).1
      subst s;subst t
      exact frontLinked_mono M ⟨wordPositive M w,wordPositive_append M _ _⟩
        (h.2.2 r rs q qs rfl rfl)

lemma wordFront_relation (z:M.Group)
    (hz:∀w,M.toCoxeterSystem.length w≤M.toCoxeterSystem.length z) (s t:S) :
    WordFrontData M (altList s t (M s t)) (altList t s (M s t)) := by
  refine ⟨wordPositive_braid M s t,by simp only [length_altList],?_⟩
  intro r rs q qs hr hq
  by_cases hm:M s t=0
  · rw [hm,altList_zero] at hr
    contradiction
  obtain ⟨n,hn⟩:=Nat.exists_eq_succ_of_ne_zero hm
  have hs:s=r:=by rw [hn,altList_succ] at hr;exact (List.cons.inj hr).1
  have ht:t=q:=by rw [hn,altList_succ] at hq;exact (List.cons.inj hq).1
  subst r;subst q
  have hred:=alternating_isReduced_of_longest M z hz s t
  have he:=wordPositive_simple_of_reduced M _ hred
  apply Relation.ReflTransGen.single
  refine ⟨wordCoxeter M (altList s t (M s t)),he ▸ positivePrefix_refl M _,?_,?_⟩
  · rw [←he,hr]
    exact positivePrefix_first M s rs
  · rw [←he,wordPositive_braid,hq]
    exact positivePrefix_first M t qs

lemma wordFront_conGen (z:M.Group)
    (hz:∀w,M.toCoxeterSystem.length w≤M.toCoxeterSystem.length z)
    {u v:FreeMonoid S} (h:ConGen.Rel (positiveBraidRelations M) u v) :
    WordFrontData M u.toList v.toList := by
  induction h with
  | of a b h=>
    obtain ⟨s,t,rfl,rfl⟩:=h
    exact wordFront_relation M z hz s t
  | refl a=>exact wordFront_refl M a.toList
  | symm h ih=>exact wordFront_symm M ih
  | trans h k ih ik=>exact wordFront_trans M ih ik
  | mul h k ih ik=>exact wordFront_mul M ih ik

theorem positive_first_letters_connected (z:M.Group)
    (hz:∀w,M.toCoxeterSystem.length w≤M.toCoxeterSystem.length z)
    (a:PositiveArtin M) (s t:S)
    (hs:PositivePrefix M (positiveGenerator M s) a)
    (ht:PositivePrefix M (positiveGenerator M t) a) : FrontLinked M a s t := by
  obtain ⟨b,hb⟩:=hs
  obtain ⟨c,hc⟩:=ht
  obtain ⟨u,hu⟩:=PresentedMonoid.surjective_mk (rels:=positiveBraidRelations M) b
  obtain ⟨v,hv⟩:=PresentedMonoid.surjective_mk (rels:=positiveBraidRelations M) c
  have hu':wordPositive M u.toList=b:=by rw [wordPositive_mk,FreeMonoid.ofList_toList,hu]
  have hv':wordPositive M v.toList=c:=by rw [wordPositive_mk,FreeMonoid.ofList_toList,hv]
  have he₁:wordPositive M (s::u.toList)=a:=by change positiveGenerator M s*wordPositive M u.toList=a;rw [hu',←hb]
  have he₂:wordPositive M (t::v.toList)=a:=by change positiveGenerator M t*wordPositive M v.toList=a;rw [hv',←hc]
  have he:=he₁.trans he₂.symm
  rw [wordPositive_mk,wordPositive_mk] at he
  have h:ConGen.Rel (positiveBraidRelations M) (FreeMonoid.ofList (s::u.toList)) (FreeMonoid.ofList (t::v.toList)):=PresentedMonoid.mk_eq_mk_iff.mp he
  have hf:=(wordFront_conGen M z hz h).2.2 s u.toList t v.toList rfl rfl
  rw [FreeMonoid.toList_ofList,he₁] at hf
  exact hf

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_PositiveDescentSet
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type*} [Fintype S] (M:CoxeterMatrix S)
variable (z:M.Group) (hz:∀w,M.toCoxeterSystem.length w≤M.toCoxeterSystem.length z)

lemma positiveReverse_simpleLift (w:M.Group) :
    positiveReverse M z hz (positiveSimpleLift M w)=positiveSimpleLift M w⁻¹ := by
  rw [positiveSimpleLift,positiveReverse_word]
  have hr:=(reducedExpression_reduced M w).reverse
  have he:wordCoxeter M (reducedExpression M w).reverse=w⁻¹:=by
    change M.toCoxeterSystem.wordProd (reducedExpression M w).reverse=w⁻¹
    rw [M.toCoxeterSystem.wordProd_reverse]
    change (wordCoxeter M (reducedExpression M w))⁻¹=_
    rw [wordCoxeter_reducedExpression]
  simpa only [he] using (positiveSimpleLift_word M _ hr).symm

lemma type_subset_positiveDescentSet (T:Set S) (q:M.Group) (hq:IsParabolicLongest M T q)
    (a:PositiveArtin M) : T⊆PositiveDescentSet M (a*positiveSimpleLift M q) := by
  intro s hs
  have hmem: M.toCoxeterSystem.simple s∈coxeterParabolic M T:=Subgroup.subset_closure ⟨s,hs,rfl⟩
  have hl:=parabolic_longest_length_mul M T q hq (M.toCoxeterSystem.simple s) hmem
  have he:(q*M.toCoxeterSystem.simple s)*M.toCoxeterSystem.simple s=q:=by rw [mul_assoc,M.toCoxeterSystem.simple_mul_simple_self,mul_one]
  have hp:positiveSimpleLift M q=positiveSimpleLift M (q*M.toCoxeterSystem.simple s)*positiveGenerator M s:=by
    have h:=positiveSimpleLift_mul M (q*M.toCoxeterSystem.simple s) (M.toCoxeterSystem.simple s)
      (by rw [he];exact hl.symm)
    simpa only [he,positiveSimpleLift_simple] using h
  exact ⟨a*positiveSimpleLift M (q*M.toCoxeterSystem.simple s),by rw [hp,mul_assoc]⟩

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_PositiveRegion
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderLiftedPuncturedBoundary _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type*} (M:CoxeterMatrix S)

lemma positiveRegion_face_closed (g:Artin M) {a b:LiftedCell M}
    (h:a≤b) (hb:b∈PositiveRegion M g) : a∈PositiveRegion M g := by
  obtain ⟨p,hp⟩:=hb
  obtain ⟨_,w,_,_,_,he⟩:=(lifted_le_iff_face M _ _).mp h
  refine ⟨p*wordPositive M w,?_⟩
  rw [map_mul,positiveToArtin_word,←mul_assoc,←hp,he]

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_RealizeSimplex
attribute [-instance] _root_.OAI.HarmonicArtin.instPreorderLiftedCell _root_.OAI.HarmonicArtin.liftedPartialOrder
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

lemma map_coneSimplex {n m : SimplexCategory} (f : n ⟶ m)
    (z : Convexity.StdSimplex ℝ (Fin (n.len + 1))) (t : I) :
    Convexity.StdSimplex.map (prependOrdinal f).toOrderHom (coneSimplex n.len (z, t)) =
      coneSimplex m.len (Convexity.StdSimplex.map f.toOrderHom z, t) := by
  have hs : Convexity.StdSimplex.map (prependOrdinal f).toOrderHom (Convexity.StdSimplex.map Fin.succ z) =
      Convexity.StdSimplex.map Fin.succ (Convexity.StdSimplex.map f.toOrderHom z) := by
    rw [← Convexity.StdSimplex.map_comp, ← Convexity.StdSimplex.map_comp]
    rfl
  dsimp only [coneSimplex, ContinuousMap.coe_mk]
  rw [(Convexity.StdSimplex.isAffineMap_map ℝ _).map_convexCombPair,
    Convexity.StdSimplex.map_single, hs]
  rfl

variable (P : Type u) [Preorder P] [OrderBot P]

lemma nerveConeSimplex_natural {n m : SimplexCategory} (f : n ⟶ m)
    (x : (nerve P).obj (op m)) (z : Convexity.StdSimplex ℝ (Fin (n.len + 1))) (t : I) :
    nerveConeSimplex P ((nerve P).map f.op x) z t =
      nerveConeSimplex P x (Convexity.StdSimplex.map f.toOrderHom z) t := by
  change realizeSimplex (nerve P) (prependNerve P ((nerve P).map f.op x))
      (coneSimplex n.len (z, t)) =
    realizeSimplex (nerve P) (prependNerve P x)
      (coneSimplex m.len (Convexity.StdSimplex.map f.toOrderHom z, t))
  rw [prependNerve_natural, realizeSimplex_natural, map_coneSimplex]

noncomputable def nerveConeMap :
    nerve P ⟶ TopCat.toSSet.obj (TopCat.of C(I, |nerve P|)) where
  app n := ↾fun x => (toSimp _ n).symm (nerveConeSimplex P x)
  naturality {n m} f := by
    apply ConcreteCategory.hom_ext
    intro x
    apply (toSimp _ m).injective
    ext z t
    change toSimp (TopCat.of C(I, |nerve P|)) m ((toSimp (TopCat.of C(I, |nerve P|)) m).symm (nerveConeSimplex P ((nerve P).map f.unop.op x))) z t =
      toSimp (TopCat.of C(I, |nerve P|)) m ((TopCat.toSSet.obj (TopCat.of C(I, |nerve P|))).map f ((toSimp (TopCat.of C(I, |nerve P|)) n).symm (nerveConeSimplex P x))) z t
    rw [Equiv.apply_symm_apply]
    have key := toSimp_naturality_apply (Y := (TopCat.of C(I, |nerve P|))) f.unop
      ((toSimp (TopCat.of C(I, |nerve P|)) n).symm (nerveConeSimplex P x)) z
    rw [Equiv.apply_symm_apply] at key
    exact (nerveConeSimplex_natural P f.unop x z t).trans (congrArg (fun c => c t) key.symm)

noncomputable def nerveCone : C(|nerve P|, C(I, |nerve P|)) :=
  ((sSetTopAdj.homEquiv _ _).symm (nerveConeMap P)).hom

section TopCone
variable (Q : Type u) [Preorder Q] [OrderTop Q]

lemma map_topConeSimplex {n m : SimplexCategory} (f : n ⟶ m)
    (z : Convexity.StdSimplex ℝ (Fin (n.len + 1))) (t : I) :
    Convexity.StdSimplex.map (appendOrdinal f).toOrderHom (topConeSimplex n.len (z, t)) =
      topConeSimplex m.len (Convexity.StdSimplex.map f.toOrderHom z, t) := by
  have hs : Convexity.StdSimplex.map (appendOrdinal f).toOrderHom (Convexity.StdSimplex.map Fin.castSucc z) =
      Convexity.StdSimplex.map Fin.castSucc (Convexity.StdSimplex.map f.toOrderHom z) := by
    rw [← Convexity.StdSimplex.map_comp, ← Convexity.StdSimplex.map_comp]
    congr 1
    funext i
    exact appendOrdinal_castSucc f i
  dsimp only [topConeSimplex, ContinuousMap.coe_mk]
  rw [(Convexity.StdSimplex.isAffineMap_map ℝ _).map_convexCombPair,
    Convexity.StdSimplex.map_single, hs, appendOrdinal_last]

lemma nerveTopConeSimplex_natural {n m : SimplexCategory} (f : n ⟶ m)
    (x : (nerve Q).obj (op m)) (z : Convexity.StdSimplex ℝ (Fin (n.len + 1))) (t : I) :
    nerveTopConeSimplex Q ((nerve Q).map f.op x) z t =
      nerveTopConeSimplex Q x (Convexity.StdSimplex.map f.toOrderHom z) t := by
  change realizeSimplex (nerve Q) (appendNerve Q ((nerve Q).map f.op x))
      (topConeSimplex n.len (z, t)) =
    realizeSimplex (nerve Q) (appendNerve Q x)
      (topConeSimplex m.len (Convexity.StdSimplex.map f.toOrderHom z, t))
  rw [appendNerve_natural, realizeSimplex_natural, map_topConeSimplex]

noncomputable def nerveTopConeMap :
    nerve Q ⟶ TopCat.toSSet.obj (TopCat.of C(I, |nerve Q|)) where
  app n := ↾fun x => (toSimp _ n).symm (nerveTopConeSimplex Q x)
  naturality {n m} f := by
    apply ConcreteCategory.hom_ext
    intro x
    apply (toSimp _ m).injective
    ext z t
    change toSimp (TopCat.of C(I, |nerve Q|)) m ((toSimp (TopCat.of C(I, |nerve Q|)) m).symm (nerveTopConeSimplex Q ((nerve Q).map f.unop.op x))) z t =
      toSimp (TopCat.of C(I, |nerve Q|)) m ((TopCat.toSSet.obj (TopCat.of C(I, |nerve Q|))).map f ((toSimp (TopCat.of C(I, |nerve Q|)) n).symm (nerveTopConeSimplex Q x))) z t
    rw [Equiv.apply_symm_apply]
    have key := toSimp_naturality_apply (Y := (TopCat.of C(I, |nerve Q|))) f.unop
      ((toSimp (TopCat.of C(I, |nerve Q|)) n).symm (nerveTopConeSimplex Q x)) z
    rw [Equiv.apply_symm_apply] at key
    exact (nerveTopConeSimplex_natural Q f.unop x z t).trans (congrArg (fun c => c t) key.symm)

noncomputable def nerveTopCone : C(|nerve Q|, C(I, |nerve Q|)) :=
  ((sSetTopAdj.homEquiv _ _).symm (nerveTopConeMap Q)).hom

end TopCone
end HarmonicArtin

end TopologyDependencies

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_NerveChain
attribute [-instance] _root_.OAI.HarmonicArtin.finiteLinearWeightsCompact _root_.OAI.HarmonicArtin.instPreorderLiftedCell _root_.OAI.HarmonicArtin.instT2SpaceOrderWeights _root_.OAI.HarmonicArtin.liftedPartialOrder
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

noncomputable def nerveWeightsSimplex {n:SimplexCategory} (x:(nerve P).obj (op n)) :
    C(StdSimplex ℝ (Fin (n.len+1)),OrderWeights P) :=
  ⟨fun z=>orderWeightsOfChain (nerveChain x) z,orderWeightsChart_continuous x⟩

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

noncomputable def supportedWeightMap {n:ℕ} (x:Fin (n+1)→o P)
    (z:StdSimplex ℝ (Fin (n+1))) :
    Fin (simplexSupportDim z+1) →o Fin (weightDim (orderWeightsOfChain x z)+1) :=
  { toFun:=fun i=>(weightEnum (orderWeightsOfChain x z)).symm
      ⟨x (simplexSupportInclusion z i),chainWeights_support_positive x z (simplexSupportEnum z i).property⟩
    monotone':=fun _ _ h=>(weightEnum (orderWeightsOfChain x z)).symm.monotone
      (x.monotone ((simplexSupportInclusion z).monotone h)) }

lemma supportedWeightMap_chain {n:ℕ} (x:Fin (n+1)→o P)
    (z:StdSimplex ℝ (Fin (n+1))) :
    (weightChain (orderWeightsOfChain x z)).comp (supportedWeightMap x z)=
      x.comp (simplexSupportInclusion z) := by
  apply DFunLike.ext
  intro i
  change ((weightEnum (orderWeightsOfChain x z)) ((weightEnum (orderWeightsOfChain x z)).symm _)).val=_
  exact congrArg Subtype.val ((weightEnum (orderWeightsOfChain x z)).apply_symm_apply _)

lemma supportedWeightMap_simplex {n:ℕ} (x:Fin (n+1)→o P)
    (z:StdSimplex ℝ (Fin (n+1))) :
    StdSimplex.map (supportedWeightMap x z) (simplexSupported z)=
      weightSimplex (orderWeightsOfChain x z) := by
  apply chainWeights_coordinates_injective _ (weightChain_injective _)
  rw [← chainWeights_natural,supportedWeightMap_chain,chainWeights_natural,simplexSupported_map]
  exact congrArg OrderWeights.weights (orderWeightsOfChain_canonical (orderWeightsOfChain x z)).symm

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
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_SphericalLongest
attribute [-instance] _root_.OAI.HarmonicArtin.instPartialOrderLiftedPuncturedBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric
open scoped unitInterval

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type*} [Fintype S] (M:CoxeterMatrix S)

lemma parabolic_longest_unique (T:Set S) (q r:M.Group)
    (hq:IsParabolicLongest M T q) (hr:IsParabolicLongest M T r) : q=r := by
  have hh:=parabolic_longest_length_mul M T q hq r⁻¹ ((coxeterParabolic M T).inv_mem hr.1)
  rw [M.toCoxeterSystem.length_inv] at hh
  have hb:=hr.2 q hq.1
  have he:q*r⁻¹=1:=M.toCoxeterSystem.length_eq_zero_iff.mp (by omega)
  exact mul_inv_eq_one.mp he

lemma sphericalLongest_spec (T:SphericalType M) :
    IsParabolicLongest M T.val (sphericalLongest M T) :=
  (exists_parabolic_longest M T.val T.property).choose_spec

omit [Fintype S] in
lemma positiveToArtin_simpleLift (w:M.Group) :
    positiveToArtin M (positiveSimpleLift M w)=positiveLift M w := by
  simp only [positiveSimpleLift,positiveToArtin_word,positiveLift]

noncomputable def liftedTopVertex (a:LiftedCell M) : Artin M :=
  a.1*positiveLift M (sphericalLongest M a.2)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_TopBlockMatchingKey
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type*} (M:CoxeterMatrix S)

lemma spherical_type_mono {R T:Set S} (h:R⊆T) (hT:IsSpherical M T) : IsSpherical M R := by
  let : Finite (coxeterParabolic M T):=hT
  exact Finite.of_injective
    (fun z:coxeterParabolic M R=>(⟨z,coxeterParabolic_mono M h z.property⟩:coxeterParabolic M T))
    (fun a b he=>Subtype.ext (congrArg (fun z:coxeterParabolic M T=>(z:M.Group)) he))

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_RestrictedLiftedCell
attribute [-instance] _root_.OAI.HarmonicArtin.instPartialOrderLiftedPuncturedBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S)

omit [Fintype S] [LinearOrder S] in
lemma restriction_parabolic_map (T : Set S) (R : Set T) :
    (coxeterParabolic (restrictedMatrix M T) R).map (restrictionHom M T) =
      coxeterParabolic M (Subtype.val '' R) := by
  rw [coxeterParabolic, MonoidHom.map_closure, Set.image_image]
  congr 1
  ext x
  simp only [Set.mem_image]
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨(s:S), ⟨s,hs,rfl⟩, restrictionHom_simple M T s |>.symm⟩
  · rintro ⟨s, ⟨t,ht,rfl⟩, rfl⟩
    exact ⟨t,ht,restrictionHom_simple M T t⟩

omit [Fintype S] [LinearOrder S] in
lemma restriction_wordCoxeter (T : Set S) (w : List T) :
    restrictionHom M T (wordCoxeter (restrictedMatrix M T) w) =
      wordCoxeter M (w.map Subtype.val) :=
  restriction_wordProd M T w

noncomputable def restrictedLiftedCell (T : Set S) (hT : IsSpherical M T)
    (a : LiftedCell (restrictedMatrix M T)) : SphericalLiftedFiber M T :=
  ⟨(restrictedArtinHom M T a.1, ⟨Subtype.val '' a.2.val,
      spherical_type_mono M (by rintro _ ⟨s,_,rfl⟩; exact s.property) hT⟩),
    (by rintro _ ⟨s,_,rfl⟩; exact s.property),
    (by rw [←restrictedArtinHom_range M T]; exact ⟨a.1,rfl⟩)⟩

omit [LinearOrder S] in
lemma restrictedLiftedCell_surjective (T : Set S) (hT : IsSpherical M T) :
    Function.Surjective (restrictedLiftedCell M T hT) := by
  intro a
  have ha : a.val.1 ∈ (restrictedArtinHom M T).range := by
    simpa only [restrictedArtinHom_range] using a.property.2
  obtain ⟨g,hg⟩ := ha
  let R : Set T := Subtype.val ⁻¹' a.val.2.val
  let : Finite (restrictedMatrix M T).Group := restricted_finite M T hT
  have hR : IsSpherical (restrictedMatrix M T) R :=
    show Finite (coxeterParabolic (restrictedMatrix M T) R) from inferInstance
  refine ⟨(g,⟨R,hR⟩),?_⟩
  apply Subtype.ext
  apply Prod.ext hg
  apply Subtype.ext
  change Subtype.val '' R = a.val.2.val
  ext s
  constructor
  · rintro ⟨t,ht,rfl⟩; exact ht
  · intro hs
    exact ⟨⟨s,a.property.1 hs⟩,hs,rfl⟩

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_PositiveRegionDeckIso
attribute [-instance] _root_.OAI.HarmonicArtin.instPartialOrderLiftedPuncturedBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
universe u
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S)

noncomputable def positiveRegionDeckIso (g : Artin M) :
    PositiveRegion M 1 ≃o PositiveRegion M g where
  toFun a := ⟨liftedDeck M g a.val, by
    obtain ⟨p,hp⟩ := a.property
    exact ⟨p, by change g*a.val.1 = _; simpa using congrArg (g * ·) hp⟩⟩
  invFun a := ⟨liftedDeck M g⁻¹ a.val, by
    obtain ⟨p,hp⟩ := a.property
    exact ⟨p, by change g⁻¹*a.val.1 = _; simp [hp]⟩⟩
  left_inv a := by apply Subtype.ext; ext <;> simp [liftedDeck]
  right_inv a := by apply Subtype.ext; ext <;> simp [liftedDeck]
  map_rel_iff' := by intro a b; exact (liftedDeck M g).map_rel_iff

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_PositiveLiftedCell
attribute [-instance] _root_.OAI.HarmonicArtin.instPartialOrderLiftedPuncturedBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type*} [Fintype S] (M:CoxeterMatrix S)

lemma positiveSimpleLift_prefix_longest (T:Set S) (q:M.Group) (hq:IsParabolicLongest M T q)
    (w:M.Group) (hw:w∈coxeterParabolic M T) :
    PositivePrefix M (positiveSimpleLift M w) (positiveSimpleLift M q) := by
  have hh:=parabolic_longest_length_mul M T q hq w hw
  have he:M.toCoxeterSystem.length (w⁻¹*q)=M.toCoxeterSystem.length (q*w):=by
    have h:=M.toCoxeterSystem.length_inv (q*w)
    rw [mul_inv_rev,parabolic_longest_inverse M T q hq] at h
    exact h
  refine ⟨positiveSimpleLift M (w⁻¹*q),?_⟩
  have hlen:M.toCoxeterSystem.length (w*(w⁻¹*q))=
      M.toCoxeterSystem.length w+M.toCoxeterSystem.length (w⁻¹*q):=by
    rw [mul_inv_cancel_left,he]
    omega
  simpa only [mul_inv_cancel_left] using positiveSimpleLift_mul M w (w⁻¹*q) hlen

def positiveCellToLifted (a:PositiveLiftedCell M) : LiftedCell M :=
  (positiveToArtin M a.1,a.2)

lemma positiveCellTop_toArtin (a:PositiveLiftedCell M) :
    positiveToArtin M (positiveCellTop M a)=liftedTopVertex M (positiveCellToLifted M a) := by
  simp only [positiveCellTop,map_mul,positiveToArtin_simpleLift,liftedTopVertex,positiveCellToLifted]

theorem positiveCellTop_prefix_of_face
    (inj:Function.Injective (positiveToArtin M)) (a b:PositiveLiftedCell M)
    (h:LiftedFace M (positiveCellToLifted M a) (positiveCellToLifted M b)) :
    PositivePrefix M (positiveCellTop M a) (positiveCellTop M b) := by
  obtain ⟨hAB,u,hu,hr,hmin,he⟩:=h
  have hr':M.toCoxeterSystem.IsReduced u:=hr
  have ha:a.1=b.1*wordPositive M u:=by
    apply inj
    simpa only [map_mul,positiveToArtin_word,positiveCellToLifted] using he
  let v:=wordCoxeter M u*sphericalLongest M a.2
  have hlen:M.toCoxeterSystem.length v=M.toCoxeterSystem.length (wordCoxeter M u)+
      M.toCoxeterSystem.length (sphericalLongest M a.2):=by
    apply length_mul_of_right_minimum M.toCoxeterSystem a.2.val (wordCoxeter M u)
    · intro x hx
      exact hmin ⟨x,hx⟩
    · exact (sphericalLongest_spec M a.2).1
  have hv:v∈coxeterParabolic M b.2.val:=(coxeterParabolic M b.2.val).mul_mem
    (wordCoxeter_mem_parabolic M _ u hu)
    (coxeterParabolic_mono M hAB (sphericalLongest_spec M a.2).1)
  obtain ⟨r,heq⟩:=positiveSimpleLift_prefix_longest M _ _ (sphericalLongest_spec M b.2) v hv
  have hu':wordPositive M u=positiveSimpleLift M (wordCoxeter M u):=(positiveSimpleLift_word M u hr').symm
  have ha':positiveCellTop M a=b.1*positiveSimpleLift M v:=by
    change a.1*positiveSimpleLift M (sphericalLongest M a.2)=_
    rw [ha,hu',mul_assoc,←positiveSimpleLift_mul M _ _ hlen]
  refine ⟨r,?_⟩
  change b.1*positiveSimpleLift M (sphericalLongest M b.2)=_
  rw [ha',heq,mul_assoc]

lemma positiveCellTop_degree_strict
    (inj:Function.Injective (positiveToArtin M)) (a b:PositiveLiftedCell M)
    (h:positiveCellToLifted M a≤positiveCellToLifted M b)
    (hne:positiveCellTop M a≠positiveCellTop M b) :
    positiveDegree M (positiveCellTop M a)<positiveDegree M (positiveCellTop M b) := by
  have hp:=positiveCellTop_prefix_of_face M inj a b ((lifted_le_iff_face M _ _).mp h)
  exact lt_of_le_of_ne (positivePrefix_degree M hp)
    (fun he=>hne (positivePrefix_eq_of_degree M hp he))

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_NoncriticalPositiveCell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type*} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)
variable (z:M.Group) (hz:∀w,M.toCoxeterSystem.length w≤M.toCoxeterSystem.length z)
variable (inj:Function.Injective (positiveToArtin M))

include inj in
omit [LinearOrder S] in
lemma positiveCell_same_top_type_unique (a b:PositiveLiftedCell M)
    (ht:a.2=b.2) (hb:positiveCellTop M a=positiveCellTop M b) : a=b := by
  apply Prod.ext ?_ ht
  apply inj
  have hp:=congrArg (positiveToArtin M) hb
  simp only [positiveCellTop,map_mul,positiveToArtin_simpleLift,ht] at hp
  exact mul_right_cancel hp

noncomputable def matchingLetter (a:NoncriticalPositiveCell M) : S :=
  firstPositiveDescent M z hz (positiveCellTop M a.val) a.property

noncomputable def matchingOtherType (a:NoncriticalPositiveCell M) : Set S :=
  if matchingLetter M z hz a∈a.val.2.val then a.val.2.val\{matchingLetter M z hz a}
  else insert (matchingLetter M z hz a) a.val.2.val

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_PositiveRootCell
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
lemma positiveDescentSet_one : PositiveDescentSet M 1=∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro s hs
  obtain ⟨p,hp⟩:=hs
  have h:=congrArg (positiveDegree M) hp
  simp only [positiveDegree_one,positiveDegree_mul,positiveDegree_generator] at h
  omega

noncomputable def positiveRootCell : PositiveLiftedCell M :=
  (1,⟨∅,spherical_empty M⟩)

lemma positiveCellTop_eq_one_iff (a:PositiveLiftedCell M) :
    positiveCellTop M a=1 ↔ a=positiveRootCell M := by
  constructor
  · intro h
    have ht:=type_subset_positiveDescentSet M _ _ (sphericalLongest_spec M a.2) a.1
    change a.2.val⊆PositiveDescentSet M (positiveCellTop M a) at ht
    rw [h,positiveDescentSet_one] at ht
    have htype:a.2.val=∅:=Set.subset_empty_iff.mp ht
    have hd:=congrArg (positiveDegree M) h
    simp only [positiveCellTop,positiveDegree_mul,positiveDegree_one] at hd
    apply Prod.ext
    · exact (positiveDegree_zero_iff M a.1).mp (by omega)
    · exact Subtype.ext htype
  · rintro rfl
    have hq: sphericalLongest M (positiveRootCell M).2=1 := by
      have h:=(sphericalLongest_spec M (positiveRootCell M).2).1
      simpa [positiveRootCell,coxeterParabolic] using h
    change 1*positiveSimpleLift M (sphericalLongest M (positiveRootCell M).2)=1
    rw [one_mul,hq]
    apply (positiveDegree_zero_iff M _).mp
    simp only [positiveDegree_simpleLift,M.toCoxeterSystem.length_one]

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_PositiveCellPoset
attribute [-instance] _root_.OAI.HarmonicArtin.instPartialOrderLiftedPuncturedBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type*} [Fintype S] (M : CoxeterMatrix S)

omit [Fintype S] in
lemma positiveCellToLifted_injective (inj : Function.Injective (positiveToArtin M)) :
    Function.Injective (positiveCellToLifted M) := by
  intro a b h
  exact Prod.ext (inj (congrArg (fun c : LiftedCell M => c.1) h))
    (congrArg (fun c : LiftedCell M => c.2) h)

instance instPartialOrderPositiveCellPoset (inj : Function.Injective (positiveToArtin M)) : PartialOrder (PositiveCellPoset M inj) :=
  PartialOrder.lift (positiveCellToLifted M) (positiveCellToLifted_injective M inj)

noncomputable def positiveCellRegionIso (inj : Function.Injective (positiveToArtin M)) :
    PositiveCellPoset M inj ≃o PositiveRegion M 1 where
  toFun a := ⟨positiveCellToLifted M a, a.1, by simp [positiveCellToLifted]⟩
  invFun a := (a.property.choose,a.val.2)
  left_inv a := by
    apply Prod.ext
    · apply inj
      simpa only [positiveCellToLifted,one_mul] using
        (Exists.choose_spec (show ∃ p, (positiveCellToLifted M a).1 = 1*positiveToArtin M p from
            ⟨a.1,by simp [positiveCellToLifted]⟩)).symm
    · rfl
  right_inv a := by
    apply Subtype.ext
    exact Prod.ext (by simpa only [positiveCellToLifted,one_mul] using a.property.choose_spec.symm) rfl
  map_rel_iff' := by intros; rfl

variable [LinearOrder S]
variable (z : M.Group) (hz : ∀ w, M.toCoxeterSystem.length w ≤ M.toCoxeterSystem.length z)
variable (inj : Function.Injective (positiveToArtin M))

lemma positiveEarlier_iff (a b : PositiveCellPoset M inj) :
    PositiveEarlier M z hz inj a b ↔
      positiveDegree M (positiveCellTop M a) < positiveDegree M (positiveCellTop M b) ∨
      positiveDegree M (positiveCellTop M a) = positiveDegree M (positiveCellTop M b) ∧
        (positiveMatchingTypeKey M z hz a < positiveMatchingTypeKey M z hz b ∨
          positiveMatchingTypeKey M z hz a = positiveMatchingTypeKey M z hz b ∧ WellOrderingRel a b) := by
  simp only [PositiveEarlier,Prod.lex_iff]

lemma positiveEarlier_wf : WellFounded (PositiveEarlier M z hz inj) :=
  InvImage.wf (fun a : PositiveCellPoset M inj =>
    (positiveDegree M (positiveCellTop M a),(positiveMatchingTypeKey M z hz a,a)))
      (wellFounded_lt.prod_lex (wellFounded_lt.prod_lex WellOrderingRel.isWellOrder.wf))

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_PuncturedBoundaryIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable

variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S)

noncomputable def positiveCellEmbedding (inj : Function.Injective (positiveToArtin M)) :
    PositiveCellPoset M inj ↪o LiftedCell M where
  toFun := positiveCellToLifted M
  inj' := positiveCellToLifted_injective M inj
  map_rel_iff' := by intros; rfl

omit [Fintype S] [LinearOrder S] in
lemma positiveCellEmbedding_full (inj : Function.Injective (positiveToArtin M))
    (c : PositiveCellPoset M inj) (b : LiftedCell M) (h : b ≤ positiveCellToLifted M c) :
    ∃ a : PositiveCellPoset M inj, positiveCellToLifted M a = b := by
  have hc : positiveCellToLifted M c ∈ PositiveRegion M 1 := ⟨c.1,by simp [positiveCellToLifted]⟩
  obtain ⟨p,hp⟩ := positiveRegion_face_closed M 1 h hc
  refine ⟨(p,b.2),Prod.ext ?_ rfl⟩
  simpa only [positiveCellToLifted,one_mul] using hp.symm

noncomputable def positivePuncturedBoundaryIso (inj : Function.Injective (positiveToArtin M))
    (c d : PositiveCellPoset M inj) :
    {a : PositiveCellPoset M inj // positiveCellToLifted M a < positiveCellToLifted M c ∧ a ≠ d} ≃o
      LiftedPuncturedBoundary M (positiveCellToLifted M c) (positiveCellToLifted M d) :=
  puncturedBoundaryIso (positiveCellEmbedding M inj) c d (positiveCellEmbedding_full M inj c)

omit [LinearOrder S] in
lemma restriction_sphericalLongest (T : Set S) (hT : IsSpherical M T)
    (R : SphericalType (restrictedMatrix M T)) :
    restrictionHom M T (sphericalLongest (restrictedMatrix M T) R) =
      sphericalLongest M ⟨Subtype.val '' R.val, spherical_type_mono M (by rintro _ ⟨s,_,rfl⟩; exact s.property) hT⟩ := by
  let U : SphericalType M := ⟨Subtype.val '' R.val,
    spherical_type_mono M (by rintro _ ⟨s,_,rfl⟩; exact s.property) hT⟩
  apply parabolic_longest_unique M U.val _ _ ?_ (sphericalLongest_spec M U)
  refine ⟨?_,?_⟩
  · rw [show U.val = Subtype.val '' R.val from rfl,←restriction_parabolic_map]
    exact ⟨_,(sphericalLongest_spec (restrictedMatrix M T) R).1,rfl⟩
  · intro w hw
    rw [show U.val = Subtype.val '' R.val from rfl,←restriction_parabolic_map] at hw
    obtain ⟨v,hv,rfl⟩ := hw
    simpa only [restriction_length] using (sphericalLongest_spec (restrictedMatrix M T) R).2 v hv

omit [LinearOrder S] in
lemma restrictedArtinHom_positiveLift (T : Set S) (w : (restrictedMatrix M T).Group) :
    restrictedArtinHom M T (positiveLift (restrictedMatrix M T) w) =
      positiveLift M (restrictionHom M T w) := by
  let v := reducedExpression (restrictedMatrix M T) w
  have hv := reducedExpression_reduced (restrictedMatrix M T) w
  have he := wordCoxeter_reducedExpression (restrictedMatrix M T) w
  have hv' : M.toCoxeterSystem.length (wordCoxeter M (v.map Subtype.val)) = (v.map Subtype.val).length := by
    rw [←restriction_wordCoxeter,restriction_length,List.length_map]
    exact hv
  calc
    _ = wordArtin M (v.map Subtype.val) := by rw [positiveLift,restrictedArtinHom_word]
    _ = positiveLift M (restrictionHom M T w) := by
      rw [←positiveLift_word M _ hv',←restriction_wordCoxeter]
      exact congrArg (fun q => positiveLift M (restrictionHom M T q)) he

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_NerveOrderMap
attribute [-instance] _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
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

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_PositiveCellPoset2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type*} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S)
variable (z : M.Group) (hz : ∀ w, M.toCoxeterSystem.length w ≤ M.toCoxeterSystem.length z)
variable (inj : Function.Injective (positiveToArtin M))

lemma positiveEarlier_of_top_lt (a b : PositiveCellPoset M inj)
    (h : positiveDegree M (positiveCellTop M a) < positiveDegree M (positiveCellTop M b)) :
    PositiveEarlier M z hz inj a b :=
  (positiveEarlier_iff M z hz inj a b).mpr (Or.inl h)

lemma positiveEarlier_of_key_lt (a b : PositiveCellPoset M inj)
    (he : positiveCellTop M a = positiveCellTop M b)
    (h : positiveMatchingTypeKey M z hz a < positiveMatchingTypeKey M z hz b) :
    PositiveEarlier M z hz inj a b :=
  (positiveEarlier_iff M z hz inj a b).mpr
    (Or.inr ⟨congrArg (positiveDegree M) he,Or.inl h⟩)

lemma positiveEarlier_asymm {a b : PositiveCellPoset M inj}
    (h : PositiveEarlier M z hz inj a b) : ¬ PositiveEarlier M z hz inj b a :=
  (positiveEarlier_wf M z hz inj).asymmetric _ _ h

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

omit [LinearOrder S] in
lemma lifted_same_top_type_unique (a b : LiftedCell M)
    (ht : a.2 = b.2) (hb : liftedTopVertex M a = liftedTopVertex M b) : a = b := by
  apply Prod.ext ?_ ht
  dsimp only [liftedTopVertex] at hb
  rw [ht] at hb
  exact mul_right_cancel hb

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_WeightDual
attribute [-instance] _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.instPreorderLiftedCell _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open Simplicial CategoryTheory Opposite

attribute [local instance] Classical.decEq Classical.propDecidable
universe u
variable {P:Type u} [PartialOrder P]

lemma weightDual_continuous : Continuous (weightDual (P:=P)) := by
  rw [orderWeights_continuous_iff]
  intro n x
  let c:=nerveChain x
  let C:Finset Pᵒᵈ:=Finset.univ.image c
  have hc:IsChain (·≤·) (↑C:Set Pᵒᵈ):=by
    rintro a ha b hb hn
    obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp ha
    obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp hb
    exact (le_total i j).symm.imp (fun h=>c.monotone h) (fun h=>c.monotone h)
  have hne:C.Nonempty:=Finset.Nonempty.image Finset.univ_nonempty _
  apply continuous_of_finite_chain_carrier _ C hc hne
  · intro z
    exact chainWeights_support c z
  · intro p
    exact (weightEval_continuous (P:=P) p).comp (chainWeightsChart_continuous c)

noncomputable def weightDualHomeomorph : OrderWeights P≃ₜOrderWeights Pᵒᵈ where
  toFun:=weightDual
  invFun:=weightDual
  left_inv _:=rfl
  right_inv _:=rfl
  continuous_toFun:=weightDual_continuous
  continuous_invFun:=weightDual_continuous

end HarmonicArtin

end OAI
end


