-- Prove2me | Definitions.Def_OAIQ225Ag004
-- name    : OAIQ225Ag004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T17:19:27.608745+00:00
-- url     : https://prove2.me/theorems/4f5dc079-da2e-4134-98db-493d95c12da8
-- title:
--   Definitions bundle OAIQ225Ag004 of the split of OpenAI, Harmonic heights and the Artin K(pi,1) conjecture
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.HarmonicArtin.salvetti_cover_contractible`, carved from OpenAI's openai/math development (OpenAI, *Harmonic heights and the Artin K(pi,1) conjecture*, OpenAI Math Release, September 23, 2026, result family 254, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 57 declarations of OpenAI's Lean: 12 definitions, 2 instances and 43 theorems. The definitions and types are `OAI.HarmonicArtin.IsFrontHead`, `OAI.HarmonicArtin.WordFrontData`, `OAI.HarmonicArtin.binaryBoundaryFiberIso`, `OAI.HarmonicArtin.binaryBoundarySliceIso`, `OAI.HarmonicArtin.cosetVertex`, `OAI.HarmonicArtin.fusionColorWord`, `OAI.HarmonicArtin.fusionD0`, `OAI.HarmonicArtin.fusionOrdinaryMatrix`, `OAI.HarmonicArtin.liftedDeck`, `OAI.HarmonicArtin.simplexSupportEnum`, `OAI.HarmonicArtin.simplexSupportInclusion`, `OAI.HarmonicArtin.simplexSupported`.
--
--   **Sources.** They come from these modules of lean/OAI/Topology, in whole or in part: `ArtinGroups_Harmonic_BinaryProductBoundary`, `ArtinGroups_Harmonic_CosetVertex`, `ArtinGroups_Harmonic_FinsuppMapDomainFiber`, `ArtinGroups_Harmonic_FrameFamily`, `ArtinGroups_Harmonic_FusionColorWord`, `ArtinGroups_Harmonic_FusionFold`, `ArtinGroups_Harmonic_FusionQuiverSimpleEdge`, `ArtinGroups_Harmonic_Harmonic`, `ArtinGroups_Harmonic_LiftedDeck`, `ArtinGroups_Harmonic_LiftedPuncturedBoundary`, `ArtinGroups_Harmonic_MaximalReducedPositivePrefix`, `ArtinGroups_Harmonic_PositiveComponentPositive`, `ArtinGroups_Harmonic_PositiveHead`, `ArtinGroups_Harmonic_PositiveLiftSimple`, `ArtinGroups_Harmonic_PositivePrefix`, `ArtinGroups_Harmonic_ReducedExpression`, `ArtinGroups_Harmonic_SignedLetter`, `ArtinGroups_Harmonic_SimpleFrontLink`, `ArtinGroups_Harmonic_SimplexSupport`, `ArtinGroups_Harmonic_SphericalTypeReindex`, `ArtinGroups_Harmonic_WordFrontData`, `ArtinGroups_Realizations_CellDeligne`.
--
--   **Imports.** It imports the published bundle `Def_HarmonicArtin`; the bundles `OAIQ225Ag000` and `OAIQ225Ag001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ225Ag007` and `OAIQ225Ag008`.
-- source:
--   OpenAI, Harmonic heights and the Artin K(pi,1) conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 254; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Harmonic-heights-and-the-Artin-K-pi-1-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Topology at commit adc7f12

import Mathlib
import Definitions.Def_HarmonicArtin
import Definitions.Def_OAIQ225Ag000
import Definitions.Def_OAIQ225Ag001

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_SimplexSupport
attribute [-instance] _root_.OAI.HarmonicArtin.instPreorderLiftedCell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open Convexity
open scoped BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
universe u
variable {P:Type u} [PartialOrder P]

lemma simplexSupport_nonempty {n:ℕ} (z:StdSimplex ℝ (Fin (n+1))) :
    (simplexSupport z).Nonempty := by
  by_contra hn
  have hz:∀index,z.weights index=0:=by
    intro i
    by_contra h
    exact hn ⟨i,(mem_simplexSupport z i).mpr h⟩
  have ht:=z.total_of_fintype
  simp only [hz,Finset.sum_const_zero] at ht
  norm_num at ht

lemma simplexSupportDim_succ {n:ℕ} (z:StdSimplex ℝ (Fin (n+1))) :
    simplexSupportDim z+1=(simplexSupport z).card := by
  have :=(simplexSupport_nonempty z).card_pos
  unfold simplexSupportDim
  omega

noncomputable def simplexSupportEnum {n:ℕ} (z:StdSimplex ℝ (Fin (n+1))) :
    Fin (simplexSupportDim z+1) ≃o {i // i∈simplexSupport z} :=
  (simplexSupport z).orderIsoOfFin (simplexSupportDim_succ z).symm

noncomputable def simplexSupportInclusion {n:ℕ} (z:StdSimplex ℝ (Fin (n+1))) :
    Fin (simplexSupportDim z+1) →o Fin (n+1) :=
  ⟨fun i=>(simplexSupportEnum z i).val,fun _ _ h=>(simplexSupportEnum z).monotone h⟩

noncomputable def simplexSupported {n:ℕ} (z:StdSimplex ℝ (Fin (n+1))) :
    StdSimplex ℝ (Fin (simplexSupportDim z+1)) :=
  ⟨Finsupp.equivFunOnFinite.symm (fun index=>z.weights (simplexSupportInclusion z index)),
    fun index=>z.nonneg _,by
    rw [Finsupp.sum_fintype _ _ (by intros; rfl)]
    have he:=Equiv.sum_comp (simplexSupportEnum z).toEquiv (fun index=>z.weights index.val)
    change (∑index,z.weights (simplexSupportInclusion z index))=1
    rw [show (∑index,z.weights (simplexSupportInclusion z index))=
      ∑index:simplexSupport z,z.weights index.val from he]
    rw [Finset.sum_coe_sort]
    calc
      _ = ∑index,z.weights index := by
        apply Finset.sum_subset (Finset.subset_univ _)
        intro i _ hi
        exact not_not.mp (fun h=>hi ((mem_simplexSupport z i).mpr h))
      _=1:=z.total_of_fintype⟩

lemma simplexSupported_map {n:ℕ} (z:StdSimplex ℝ (Fin (n+1))) :
    StdSimplex.map (simplexSupportInclusion z) (simplexSupported z)=z := by
  apply StdSimplex.ext
  apply Finsupp.ext
  intro index
  change Finsupp.mapDomain (simplexSupportInclusion z) (simplexSupported z).weights index =
    z.weights index
  by_cases supported:index∈simplexSupport z
  · let supportedIndex:Fin (simplexSupportDim z+1):=
      (simplexSupportEnum z).symm ⟨index,supported⟩
    have imageEq:simplexSupportInclusion z supportedIndex=index:=
      congrArg Subtype.val ((simplexSupportEnum z).apply_symm_apply ⟨index,supported⟩)
    have inclusionInjective:Function.Injective (simplexSupportInclusion z):=
      Subtype.val_injective.comp (simplexSupportEnum z).injective
    rw [← imageEq, Finsupp.mapDomain_apply inclusionInjective]
    rfl
  · have weightZero:z.weights index=0:=
      not_not.mp (fun nonzero=>supported ((mem_simplexSupport z index).mpr nonzero))
    rw [Finsupp.mapDomain_of_notMem_range, weightZero]
    rintro ⟨supportedIndex, imageEq⟩
    exact supported (imageEq ▸ (simplexSupportEnum z supportedIndex).property)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_BinaryProductBoundary
attribute [-instance] _root_.OAI.HarmonicArtin.instPreorderLiftedCell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.decEq Classical.propDecidable
universe u
variable {A B:Type u} [PartialOrder A] [PartialOrder B] [OrderTop A] [OrderTop B]

noncomputable def binaryBoundarySliceIso :
    {x:BinaryProductBoundary A B //x.val.1≠⊤} ≃o BinaryProductBox (⊤:A×B) where
  toFun x:=⟨x.val.val,le_top,x.property⟩
  invFun x:=⟨⟨x.val,by intro he;exact x.property.2 (congrArg Prod.fst he)⟩,x.property.2⟩
  left_inv _:=rfl
  right_inv _:=rfl
  map_rel_iff':=by intros;rfl

noncomputable def binaryBoundaryFiberIso (v:BinaryProductBoundary A B) (hv:v.val.1=⊤) :
    {x:BinaryProductBoundary A B //x.val.1≠⊤ ∧ x<v} ≃o BinaryProductBox v.val where
  toFun x:=⟨x.val.val,x.property.2.le,x.property.1⟩
  invFun x:=⟨⟨x.val,by intro he;exact x.property.2 (congrArg Prod.fst he)⟩,x.property.2,by
    apply lt_of_le_of_ne x.property.1
    intro he
    exact x.property.2 ((congrArg Prod.fst he).trans hv)⟩
  left_inv _:=rfl
  right_inv _:=rfl
  map_rel_iff':=by intros;rfl

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_CosetVertex
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
universe u
variable {S : Type u}

 theorem artinParabolic_mono (M : CoxeterMatrix S) {T U : Set S} (h : T ⊆ U) :
    artinParabolic M T ≤ artinParabolic M U :=
  Subgroup.closure_mono (Set.image_mono h)

 def cosetVertex (M : CoxeterMatrix S) (T : Set S) (hT : IsSpherical M T)
    (x : Artin M) : Deligne M := ⟨(T, rightCoset M T x), hT, x, rfl⟩

open _root_.Matrix

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_FinsuppMapDomainFiber
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
lemma finsupp_mapDomain_fiber {A B M:Type*} [AddCommMonoid M]
    (f g:A →₀ M) (h:A → B) (b:B) (he:∀ a,h a=b → f a=g a) :
    f.mapDomain h b=g.mapDomain h b := by
  classical
  rw [Finsupp.mapDomain,Finsupp.mapDomain,Finsupp.sum_apply,Finsupp.sum_apply]
  rw [Finsupp.sum_of_support_subset f (Finset.subset_union_left) _ (by simp),
    Finsupp.sum_of_support_subset g (Finset.subset_union_right) _ (by simp)]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha:h a=b
  · rw [Finsupp.single_apply,Finsupp.single_apply,ite_eq_left ha,ite_eq_left ha,he a ha]
  · simp only [Finsupp.single_apply,ha,ite_false, if_false]
end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_FusionFold
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instDecidableRelStringLabelStringAdjacent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open _root_.Matrix
open scoped _root_.Matrix BigOperators

variable {E V : Type*} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m : E → ℕ)

noncomputable def fusionD0 : ℝ := ∑ L : FusionLabel m, (fusionWeight m L)^2

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_FusionQuiverSimpleEdge
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instDecidableRelStringLabelStringAdjacent
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.labelSplit_apply _root_.OAI.HarmonicArtin.labelSplit_symm_at _root_.OAI.HarmonicArtin.labelSplit_symm_rest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin

variable {E V : Type*} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m : E → ℕ) (d : V → V → FusionEdge E) (hd : ∀ s t, d s t = d t s)

noncomputable def fusionOrdinaryMatrix : CoxeterMatrix (FusionVertex (V := V) m) where
  M α β := if α=β then 1 else
    if (d α.1 β.1).multiplicity m α.2 β.2 = 0 then 2 else
    if (d α.1 β.1).multiplicity m α.2 β.2 = 1 then 3 else 0
  isSymm := by
    apply Matrix.ext
    intro α β
    change (if β = α then 1 else if (d β.1 α.1).multiplicity m β.2 α.2 = 0 then 2 else if (d β.1 α.1).multiplicity m β.2 α.2 = 1 then 3 else 0) = (if α = β then 1 else if (d α.1 β.1).multiplicity m α.2 β.2 = 0 then 2 else if (d α.1 β.1).multiplicity m α.2 β.2 = 1 then 3 else 0)
    rw [hd β.1 α.1, FusionEdge.multiplicity_symm m _ β.2 α.2]
    by_cases h : α = β <;> simp only [h, eq_comm, ite_true, if_true, ite_false, if_false]
  diagonal α := by simp
  off_diagonal α β h := by
    simp only [ite_eq_right h]
    split_ifs <;> norm_num

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_SignedLetter
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.positiveLift_one _root_.OAI.HarmonicArtin.positiveToArtin_generator _root_.OAI.HarmonicArtin.positiveToArtin_word
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

omit [Fintype S] [LinearOrder S] in
lemma artinParabolic_signed_word (J:Set S) (g:Artin M) (hg:g∈artinParabolic M J) :
    ∃ w:List (S×Bool),(∀ a∈w,a.1∈J) ∧ sourceSignedWord M w=g := by
  apply Subgroup.closure_induction_left
    (p:=fun g _=>∃ w:List (S×Bool),(∀ a∈w,a.1∈J) ∧ sourceSignedWord M w=g) ?_ ?_ ?_ hg
  · exact ⟨[],by simp, rfl⟩
  · rintro g ⟨s,hs,rfl⟩ y hy ⟨w,hw,rfl⟩
    refine ⟨(s,true)::w,?_,?_⟩
    · intro a ha
      rcases List.mem_cons.mp ha with rfl|ha
      · exact hs
      · exact hw a ha
    · simp only [sourceSignedWord_cons,sourceSignedLetter,ite_true, if_true]
  · rintro g ⟨s,hs,rfl⟩ y hy ⟨w,hw,rfl⟩
    refine ⟨(s,false)::w,?_,?_⟩
    · intro a ha
      rcases List.mem_cons.mp ha with rfl|ha
      · exact hs
      · exact hw a ha
    · simp only [sourceSignedWord_cons,sourceSignedLetter,Bool.false_eq_true,ite_false, if_false]

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_FrameFamily
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

omit [Fintype S] [LinearOrder S] in
lemma artinParabolic_univ : artinParabolic M Set.univ=⊤ := by
  change Subgroup.closure ((generator M) '' Set.univ)=⊤
  rw [Set.image_univ]
  exact PresentedGroup.closure_range_of (braidRelators M)

omit [Fintype S] [LinearOrder S] in
lemma sourceSignedWord_surjective : Function.Surjective (sourceSignedWord M) := by
  intro x
  have hx:x∈artinParabolic M Set.univ := by rw [artinParabolic_univ]; trivial
  obtain ⟨w,_,hw⟩:=artinParabolic_signed_word M Set.univ x hx
  exact ⟨w,hw⟩

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_FusionColorWord
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

attribute [local instance] Classical.decEq Classical.propDecidable
variable {E V:Type} {K:Type*} [Field K]
  [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m:E→ℕ) (d:V→V→FusionEdge E) (hd:∀ s t,d s t=d t s)
  (hdiag:∀ s,d s s=.units 0) (hm:∀ e,2 ≤ m e)

noncomputable def fusionColorWord (j:V) : List (FusionVertex (V:=V) m) :=
  (Finset.univ:Finset (FusionLabel m)).toList.map fun L=>(j,L)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_Harmonic
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
lemma rightCoset_self (T:Set S) (x:Artin M) : x∈rightCoset M T x := by
  change x*x⁻¹∈artinParabolic M T
  simp only [mul_inv_cancel]
  exact Subgroup.one_mem _

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_ReducedExpression
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.positiveToArtin_generator _root_.OAI.HarmonicArtin.positiveToArtin_word
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
universe v
variable {S : Type v}
open CoxeterExchange

lemma wordArtin_append (M : CoxeterMatrix S) (u v : List S) :
    wordArtin M (u++v)=wordArtin M u*wordArtin M v := by
  simp only [wordArtin,List.map_append,List.prod_append]

lemma positiveLift_mul [Finite S] (M : CoxeterMatrix S) (a b : M.Group)
    (hab : M.toCoxeterSystem.length (a*b) =
      M.toCoxeterSystem.length a+M.toCoxeterSystem.length b) :
    positiveLift M (a*b)=positiveLift M a*positiveLift M b := by
  let u := reducedExpression M a
  let v := reducedExpression M b
  have hru := reducedExpression_reduced M a
  have hrv := reducedExpression_reduced M b
  have hu : M.toCoxeterSystem.wordProd u=a := wordCoxeter_reducedExpression M a
  have hv : M.toCoxeterSystem.wordProd v=b := wordCoxeter_reducedExpression M b
  have hr : M.toCoxeterSystem.IsReduced (u++v) := by
    change M.toCoxeterSystem.length (M.toCoxeterSystem.wordProd (u++v))=(u++v).length
    rw [M.toCoxeterSystem.wordProd_append,hu,hv,hab,List.length_append]
    rw [← hu,← hv,hru.eq,hrv.eq]
  have hp : wordCoxeter M (u++v)=a*b := by
    change M.toCoxeterSystem.wordProd (u++v)=a*b
    rw [M.toCoxeterSystem.wordProd_append,hu,hv]
  rw [← hp,positiveLift_word M (u++v) hr,wordArtin_append]
  rfl

lemma wordArtin_mem_parabolic (M : CoxeterMatrix S) (J : Set S) (u : List S)
    (hu : ∀ i ∈ u, i ∈ J) : wordArtin M u ∈ artinParabolic M J := by
  induction u with
  | nil => exact (artinParabolic M J).one_mem
  | cons i u ih =>
    change generator M i*wordArtin M u ∈ artinParabolic M J
    exact (artinParabolic M J).mul_mem (Subgroup.subset_closure ⟨i,hu i (by simp),rfl⟩)
      (ih (fun k hk => hu k (List.mem_cons_of_mem i hk)))

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_CellDeligne
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.positiveToArtin_generator _root_.OAI.HarmonicArtin.positiveToArtin_word _root_.OAI.HarmonicArtin.positiveToCoxeter_word
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
universe v
variable {S : Type v}

lemma wordCoxeter_mem_parabolic (M : CoxeterMatrix S) (J : Set S) (u : List S)
    (hu : ∀ i ∈ u, i ∈ J) : wordCoxeter M u ∈ coxeterParabolic M J :=
  CoxeterExchange.wordProd_mem_parabolic M.toCoxeterSystem J u hu

lemma liftedFace_refl (M : CoxeterMatrix S) (a : LiftedCell M) : LiftedFace M a a := by
  refine ⟨Set.Subset.rfl, [], by simp, ?_, ?_, ?_⟩
  · simp [wordCoxeter]
  · intro v
    simp only [wordCoxeter,List.map_nil,List.prod_nil,M.toCoxeterSystem.length_one]
    exact Nat.zero_le _
  · simp [wordArtin]

lemma liftedFace_trans (M : CoxeterMatrix S) {a b c : LiftedCell M}
    (hab : LiftedFace M a b) (hbc : LiftedFace M b c) : LiftedFace M a c := by
  obtain ⟨hAB,u,hu,hur,humin,ha⟩ := hab
  obtain ⟨hBC,v,hv,hvr,hvmin,hb⟩ := hbc
  have huB := wordCoxeter_mem_parabolic M b.2.1 u hu
  have hvadd : ∀ w ∈ coxeterParabolic M b.2.1,
      M.toCoxeterSystem.length (wordCoxeter M v*w) =
        M.toCoxeterSystem.length (wordCoxeter M v)+M.toCoxeterSystem.length w := by
    intro w hw
    exact CoxeterExchange.length_mul_of_right_minimum M.toCoxeterSystem b.2.1
      (wordCoxeter M v) (fun x hx => hvmin ⟨x,hx⟩) w hw
  refine ⟨hAB.trans hBC,v++u,?_,?_,?_,?_⟩
  · intro i hi
    rcases List.mem_append.mp hi with hi | hi
    · exact hv i hi
    · exact hBC (hu i hi)
  · rw [wordCoxeter_append,hvadd _ huB,hvr,hur,List.length_append]
  · intro w
    have hwB : (w : M.Group) ∈ coxeterParabolic M b.2.1 := coxeterParabolic_mono M hAB w.property
    rw [wordCoxeter_append,mul_assoc,hvadd _ huB,
      hvadd _ ((coxeterParabolic M b.2.1).mul_mem huB hwB)]
    exact Nat.add_le_add_left (humin w) _
  · rw [ha,hb,wordArtin_append,mul_assoc]

lemma liftedFace_antisymm (M : CoxeterMatrix S) {a b : LiftedCell M}
    (hab : LiftedFace M a b) (hba : LiftedFace M b a) : a=b := by
  obtain ⟨hAB,u,hu,hur,humin,ha⟩ := hab
  have htype : a.2.1=b.2.1 := hAB.antisymm hba.1
  have humem : wordCoxeter M u ∈ coxeterParabolic M a.2.1 := by
    rw [htype]
    exact wordCoxeter_mem_parabolic M b.2.1 u hu
  have hh := humin ⟨(wordCoxeter M u)⁻¹,(coxeterParabolic M a.2.1).inv_mem humem⟩
  simp only [mul_inv_cancel,M.toCoxeterSystem.length_one] at hh
  have hulen : u.length=0 := by omega
  have hunil := List.eq_nil_of_length_eq_zero hulen
  rw [hunil] at ha
  simp only [wordArtin,List.map_nil,List.prod_nil,mul_one] at ha
  exact Prod.ext ha (Subtype.ext htype)

lemma lifted_le_iff_face (M : CoxeterMatrix S) (a b : LiftedCell M) :
    a ≤ b ↔ LiftedFace M a b := by
  constructor
  · intro h
    induction h with
    | refl => exact liftedFace_refl M _
    | tail h hstep ih => exact liftedFace_trans M ih hstep
  · exact Relation.ReflTransGen.single

lemma lifted_le_antisymm (M : CoxeterMatrix S) {a b : LiftedCell M}
    (hab : a ≤ b) (hba : b ≤ a) : a=b :=
  liftedFace_antisymm M ((lifted_le_iff_face M a b).mp hab) ((lifted_le_iff_face M b a).mp hba)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_LiftedDeck
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.positiveToArtin_generator _root_.OAI.HarmonicArtin.positiveToArtin_word _root_.OAI.HarmonicArtin.positiveToCoxeter_word
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
universe u
variable {S:Type u} (M:CoxeterMatrix S)

instance liftedPartialOrder : PartialOrder (LiftedCell M) where
  toPreorder:=inferInstance
  le_antisymm:=fun _ _=>lifted_le_antisymm M

lemma lifted_eq_of_le_type_eq {a b:LiftedCell M} (h:a≤b) (ht:a.2.val=b.2.val) : a=b := by
  obtain ⟨hab,w,hw,hred,hmin,he⟩:=(lifted_le_iff_face M a b).mp h
  have hmem:wordCoxeter M w∈coxeterParabolic M a.2.val:=by
    rw [ht];exact wordCoxeter_mem_parabolic M b.2.val w hw
  have hl:=hmin ⟨(wordCoxeter M w)⁻¹,(coxeterParabolic M a.2.val).inv_mem hmem⟩
  simp only [mul_inv_cancel,M.toCoxeterSystem.length_one] at hl
  have hn:w=[]:=List.eq_nil_of_length_eq_zero (by omega)
  rw [hn] at he
  simp only [wordArtin,List.map_nil,List.prod_nil,mul_one] at he
  exact Prod.ext he (Subtype.ext ht)

lemma lifted_lt_type {a b:LiftedCell M} (h:a<b) : a.2.val⊂b.2.val :=
  lt_of_le_of_ne ((lifted_le_iff_face M a b).mp h.le).1
    (fun ht=>h.ne (lifted_eq_of_le_type_eq M h.le ht))

lemma liftedFace_deck_iff (g:Artin M) (a b:LiftedCell M) :
    LiftedFace M (g*a.1,a.2) (g*b.1,b.2) ↔ LiftedFace M a b := by
  constructor
  · rintro ⟨ht,w,hw,hr,hm,he⟩
    refine ⟨ht,w,hw,hr,hm,?_⟩
    apply mul_left_cancel (a:=g)
    simpa only [mul_assoc] using he
  · rintro ⟨ht,w,hw,hr,hm,he⟩
    exact ⟨ht,w,hw,hr,hm,by dsimp;rw [he,mul_assoc]⟩

def liftedDeck (g:Artin M) : LiftedCell M≃oLiftedCell M where
  toFun a:=(g*a.1,a.2)
  invFun a:=(g⁻¹*a.1,a.2)
  left_inv:=by intro a;ext <;> simp
  right_inv:=by intro a;ext <;> simp
  map_rel_iff':=by
    intro a b
    rw [lifted_le_iff_face,lifted_le_iff_face]
    exact liftedFace_deck_iff M g a b

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_LiftedPuncturedBoundary
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type*} [Fintype S] (M:CoxeterMatrix S)

instance instPartialOrderLiftedPuncturedBoundary (c d:LiftedCell M) : PartialOrder (LiftedPuncturedBoundary M c d) where
  toPreorder := inferInstanceAs (Preorder {a:LiftedCell M // a < c ∧ a≠d})
  le_antisymm := fun _ _ forward backward =>
    Subtype.ext (lifted_le_antisymm M forward backward)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_MaximalReducedPositivePrefix
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.positiveToArtin_generator _root_.OAI.HarmonicArtin.positiveToArtin_word
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
lemma maximal_reduced_positive_prefix (s:S) (w:List S) :
    ∃ u v:List S, M.toCoxeterSystem.IsReduced u ∧
      wordArtin M (s::w)=wordArtin M u*wordArtin M v ∧
      u.length+v.length=(s::w).length ∧ 0<u.length ∧
      ∀ u' v':List S,M.toCoxeterSystem.IsReduced u'→
        wordArtin M (s::w)=wordArtin M u'*wordArtin M v'→
        u'.length+v'.length=(s::w).length→u'.length≤u.length := by
  let P:ℕ→Prop:=fun n=>∃u v:List S,M.toCoxeterSystem.IsReduced u ∧
    wordArtin M (s::w)=wordArtin M u*wordArtin M v ∧
    u.length+v.length=(s::w).length ∧ u.length=n
  have hP:P 1 := by
    refine ⟨[s],w,?_,?_,by simp [Nat.add_comm],rfl⟩
    · change M.toCoxeterSystem.length (M.toCoxeterSystem.simple s)=1
      exact M.toCoxeterSystem.length_simple s
    · simp [wordArtin]
  have hb:1≤(s::w).length:=by simp
  obtain ⟨u,v,hu,he,hl,hmax⟩:=Nat.findGreatest_spec hb hP
  refine ⟨u,v,hu,he,hl,?_,?_⟩
  · have hh:=Nat.le_findGreatest hb hP
    omega
  · intro u' v' hu' he' hl'
    rw [hmax]
    exact Nat.le_findGreatest (by omega) ⟨u',v',hu',he',hl',rfl⟩

lemma reduced_left_factor (w:List S) (s:S) (hw:M.toCoxeterSystem.IsReduced w)
    (h:¬M.toCoxeterSystem.IsReduced (s::w)) :
    ∃v:List S,M.toCoxeterSystem.IsReduced v ∧
      wordArtin M w=generator M s*wordArtin M v ∧ v.length+1=w.length := by
  let cs:=M.toCoxeterSystem
  have hd:cs.IsLeftDescent (cs.wordProd w) s := by
    by_contra hn
    apply h
    change cs.length (cs.simple s*cs.wordProd w)=w.length+1
    rw [cs.not_isLeftDescent_iff.mp hn,hw.eq]
  obtain ⟨v,hv,he⟩:=cs.exists_isReduced (cs.simple s*cs.wordProd w)
  have hp:cs.wordProd (s::v)=cs.wordProd w := by
    rw [cs.wordProd_cons,←he,cs.simple_mul_simple_cancel_left]
  have hl:v.length+1=w.length := by
    rw [←hv.eq,←he,←hw.eq]
    exact cs.isLeftDescent_iff.mp hd
  have hr:cs.IsReduced (s::v) := by
    change cs.length (cs.wordProd (s::v))=v.length+1
    rw [hp,hw.eq,hl]
  refine ⟨v,hv,?_,hl⟩
  exact wordArtin_eq_of_reduced M w (s::v) hw hr hp.symm

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
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_PositiveComponentPositive
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.liftedPartialOrder
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

omit [LinearOrder S] in
lemma sourceSignAt_neg_iff (p:ℕ→₀(S⊕Unit→ℝ)) (k:ℕ) (i:S⊕Unit)
    (hp:0≤p k i) : sourceSignAt M p k i= -1 ↔
    0<p k i ∧ ¬harmonicPositiveSign (framedCartan M) (.inr ()) p k i := by
  by_cases hz:p k i=0
  · simp [sourceSignAt,hz]
  have hi:0<p k i:=lt_of_le_of_ne hp (Ne.symm hz)
  rw [sourceSignAt,ite_eq_right hz,←sourceNullSign_iff M p k i hi]
  by_cases hn:SourceNullSign M p k i <;> simp [hn,hi]

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_PositivePrefix
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CoxeterExchange

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type*} (M:CoxeterMatrix S)

lemma positivePrefix_refl (a:PositiveArtin M) : PositivePrefix M a a :=⟨1,(mul_one a).symm⟩
lemma positivePrefix_one (a:PositiveArtin M) : PositivePrefix M 1 a :=⟨a,(one_mul a).symm⟩
lemma positivePrefix_trans {a b c:PositiveArtin M} (hab:PositivePrefix M a b) (hbc:PositivePrefix M b c) : PositivePrefix M a c := by
  obtain ⟨u,hu⟩:=hab;obtain ⟨v,hv⟩:=hbc
  exact ⟨u*v,by rw [hv,hu,mul_assoc]⟩

lemma positivePrefix_degree {a b:PositiveArtin M} (h:PositivePrefix M a b) : positiveDegree M a≤positiveDegree M b := by
  obtain ⟨c,rfl⟩:=h
  rw [positiveDegree_mul];omega

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_SimpleFrontLink
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

omit [Fintype S] in
lemma simpleFrontLink_mono {a b:PositiveArtin M} (hab:PositivePrefix M a b) {s t:S}
    (h:SimpleFrontLink M a s t) : SimpleFrontLink M b s t := by
  obtain ⟨w,hwa,hs,ht⟩:=h
  exact ⟨w,positivePrefix_trans M hwa hab,hs,ht⟩

omit [Fintype S] in
lemma frontLinked_mono {a b:PositiveArtin M} (hab:PositivePrefix M a b) {s t:S}
    (h:FrontLinked M a s t) : FrontLinked M b s t := by
  induction h with
  | refl=>exact .refl
  | tail h hst ih=>exact ih.tail (simpleFrontLink_mono M hab hst)

omit [Fintype S] in
lemma frontLinked_symm {a:PositiveArtin M} {s t:S} (h:FrontLinked M a s t) : FrontLinked M a t s := by
  induction h with
  | refl=>exact .refl
  | @tail u v h huv ih=>
    obtain ⟨w,hwa,hu,hv⟩:=huv
    exact (Relation.ReflTransGen.single ⟨w,hwa,hv,hu⟩).trans ih

lemma wordPositive_simple_of_reduced (w:List S) (hw:M.toCoxeterSystem.IsReduced w) :
    wordPositive M w=positiveSimpleLift M (wordCoxeter M w) :=
  (positiveSimpleLift_word M w hw).symm

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_WordFrontData
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CoxeterExchange

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type*} [Fintype S] (M:CoxeterMatrix S)

def WordFrontData (u v:List S) : Prop :=
  wordPositive M u=wordPositive M v ∧ u.length=v.length ∧
    ∀s us t vs,u=s::us→v=t::vs→FrontLinked M (wordPositive M u) s t

omit [Fintype S] in
lemma wordFront_refl (u:List S) : WordFrontData M u u := by
  refine ⟨rfl,rfl,?_⟩
  intro s us t vs hu hv
  have h:s=t:=by simpa only [hu,List.cons.injEq] using (List.cons.inj (hu.symm.trans hv)).1
  subst t
  exact .refl

omit [Fintype S] in
lemma wordFront_symm {u v:List S} (h:WordFrontData M u v) : WordFrontData M v u := by
  refine ⟨h.1.symm,h.2.1.symm,?_⟩
  intro s us t vs hu hv
  rw [←h.1]
  exact frontLinked_symm M (h.2.2 t vs s us hv hu)

omit [Fintype S] in
lemma wordFront_trans {u v w:List S} (h:WordFrontData M u v) (k:WordFrontData M v w) : WordFrontData M u w := by
  refine ⟨h.1.trans k.1,h.2.1.trans k.2.1,?_⟩
  intro s us t ts hu hw
  cases v with
  | nil=>have hh:=h.2.1;rw [hu] at hh;simp at hh
  | cons r rs=>
    have hl:=h.2.2 s us r rs hu rfl
    have hr:=k.2.2 r rs t ts rfl hw
    rw [←h.1] at hr
    exact hl.trans hr

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_PositiveHead
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

def IsFrontHead (a:PositiveArtin M) (s:S) (h:M.Group) : Prop :=
  PositivePrefix M (positiveSimpleLift M h) a ∧
    PositivePrefix M (positiveGenerator M s) (positiveSimpleLift M h) ∧
    ∀w:M.Group,PositivePrefix M (positiveSimpleLift M w) a→
      PositivePrefix M (positiveGenerator M s) (positiveSimpleLift M w)→
      PositivePrefix M (positiveSimpleLift M w) (positiveSimpleLift M h)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_PositiveLiftSimple
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.positiveToArtin_generator _root_.OAI.HarmonicArtin.positiveToArtin_word _root_.OAI.HarmonicArtin.positiveToCoxeter_word
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type*} [Fintype S] (M:CoxeterMatrix S)
local notation "cs" => M.toCoxeterSystem

lemma positiveLift_simple (s:S) : positiveLift M (M.toCoxeterSystem.simple s)=generator M s := by
  have h:M.toCoxeterSystem.IsReduced [s]:=by
    change M.toCoxeterSystem.length (M.toCoxeterSystem.simple s)=1
    exact M.toCoxeterSystem.length_simple s
  simpa [wordCoxeter,wordArtin] using positiveLift_word M [s] h

omit [Fintype S] in
lemma positiveLift_longest_square_positive (z:M.Group) :
    ∃ u:List S,wordArtin M u=positiveLift M z^2 := by
  refine ⟨reducedExpression M z++reducedExpression M z,?_⟩
  rw [wordArtin_append,pow_two]
  rfl

lemma positiveLift_longest_square_complement (z:M.Group)
    (hz:∀w,M.toCoxeterSystem.length w≤M.toCoxeterSystem.length z) (s:S) :
    ∃ u:List S,generator M s*wordArtin M u=positiveLift M z^2 := by
  let c:=M.toCoxeterSystem.simple s*z
  have hlen:=all_left_descents_of_longest cs z hz s
  have hp:positiveLift M z=generator M s*positiveLift M c := by
    have h:=positiveLift_mul M (M.toCoxeterSystem.simple s) c (by
      simp only [c]; rw [← mul_assoc,M.toCoxeterSystem.simple_mul_simple_self,one_mul,M.toCoxeterSystem.length_simple]; omega)
    simpa only [c,← mul_assoc,M.toCoxeterSystem.simple_mul_simple_self,one_mul,positiveLift_simple] using h
  refine ⟨reducedExpression M c++reducedExpression M z,?_⟩
  rw [wordArtin_append,pow_two,← mul_assoc]
  change (generator M s*positiveLift M c)*positiveLift M z=_
  rw [← hp]

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
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_SphericalTypeReindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CoxeterExchange

attribute [local instance] Classical.decEq Classical.propDecidable
universe u v
variable {S : Type u} {T : Type v} (M : CoxeterMatrix S) (e : S ≃ T)

lemma wordCoxeter_reindex (w : List S) :
    wordCoxeter (M.reindex e) (w.map e) = (M.reindexGroupEquiv e).symm (wordCoxeter M w) := by
  exact (wordProd_equiv M.toCoxeterSystem (M.reindex e).toCoxeterSystem e
    (M.reindexGroupEquiv e).symm (fun _ => rfl) w).symm

lemma coxeter_length_reindex (x : M.Group) :
    (M.reindex e).toCoxeterSystem.length ((M.reindexGroupEquiv e).symm x) =
      M.toCoxeterSystem.length x :=
  length_equiv M.toCoxeterSystem (M.reindex e).toCoxeterSystem e
    (M.reindexGroupEquiv e).symm (fun _ => rfl) x

lemma minimal_reindex (A : Set S) (x : M.Group) :
    (∀ w : coxeterParabolic (M.reindex e) (e '' A),
      (M.reindex e).toCoxeterSystem.length ((M.reindexGroupEquiv e).symm x) ≤
        (M.reindex e).toCoxeterSystem.length ((M.reindexGroupEquiv e).symm x * w.val)) ↔
    (∀ w : coxeterParabolic M A,
      M.toCoxeterSystem.length x ≤ M.toCoxeterSystem.length (x * w.val)) := by
  let f := (M.reindexGroupEquiv e).symm
  let p : coxeterParabolic M A ≃* coxeterParabolic (M.reindex e) (e '' A) :=
    (f.subgroupMap (coxeterParabolic M A)).trans (MulEquiv.subgroupCongr (coxeterParabolic_reindex M e A))
  constructor
  · intro h w
    have hh := h (p w)
    change (M.reindex e).toCoxeterSystem.length (f x) ≤
      (M.reindex e).toCoxeterSystem.length (f x * f w.val) at hh
    simpa only [←map_mul,f,coxeter_length_reindex] using hh
  · intro h w
    obtain ⟨a,rfl⟩ := p.surjective w
    change (M.reindex e).toCoxeterSystem.length (f x) ≤
      (M.reindex e).toCoxeterSystem.length (f x * f a.val)
    simpa only [←map_mul,f,coxeter_length_reindex] using h a

end HarmonicArtin

end OAI
end


