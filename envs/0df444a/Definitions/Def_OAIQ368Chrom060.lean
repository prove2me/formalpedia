-- Prove2me | Definitions.Def_OAIQ368Chrom060
-- name    : OAIQ368Chrom060
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T20:17:20.958907+00:00
-- url     : https://prove2.me/theorems/4c0cf929-609b-435c-b81c-4def239f0b79
-- title:
--   Definitions bundle OAIQ368Chrom060 of the split of OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 139 declarations of OpenAI's Lean: 63 definitions, 1 instance and 75 theorems. The definitions and types are `OAI.ElementaryPositivity.ElementaryMatrix.allOnes`, `OAI.ElementaryPositivity.ExactMasks.GradedEquiv`, `OAI.ElementaryPositivity.ExactMasks.Strict`, `OAI.ElementaryPositivity.ExactMasks.exactCompl`, `OAI.ElementaryPositivity.ExactMasks.internalStrict`, `OAI.ElementaryPositivity.ExactMasks.refine`, `OAI.ElementaryPositivity.ExactMasks.step`, `OAI.ElementaryPositivity.ExactMasks.strictEquiv`, `OAI.ElementaryPositivity.ExactMasks.strictFibers`, `OAI.ElementaryPositivity.FiniteMatching.align`, `OAI.ElementaryPositivity.FiniteMatching.cancel`, `OAI.ElementaryPositivity.FiniteMatching.compress`, `OAI.ElementaryPositivity.LaurentPositive.Decoration`, `OAI.ElementaryPositivity.LaurentPositive.centered`, `OAI.ElementaryPositivity.LaurentPositive.gradedEquivOfEnergySum`, `OAI.ElementaryPositivity.LaurentPositive.multiplicity`, `OAI.ElementaryPositivity.LaurentPositive.qLaurent`, `OAI.ElementaryPositivity.NaturalUnitIntervalGraph.Admissible`, `OAI.ElementaryPositivity.NaturalUnitIntervalGraph.PacketColor`, `OAI.ElementaryPositivity.NaturalUnitIntervalGraph.RequiredWord`, `OAI.ElementaryPositivity.NaturalUnitIntervalGraph.inversionChromatic`, `OAI.ElementaryPositivity.NaturalUnitIntervalGraph.nonedgeLT`, `OAI.ElementaryPositivity.NaturalUnitIntervalGraph.requiredColorEquiv`, `OAI.ElementaryPositivity.NaturalUnitIntervalGraph.wordMask`, `OAI.ElementaryPositivity.Packets.AnchorWord`, `OAI.ElementaryPositivity.Packets.EmptyAnchor`, `OAI.ElementaryPositivity.Packets.PacketRows`, `OAI.ElementaryPositivity.Packets.RequiredAnchor`, `OAI.ElementaryPositivity.Packets.RowFamily`, `OAI.ElementaryPositivity.Packets.Sorted`, `OAI.ElementaryPositivity.Packets.anchorRowsEquiv`, `OAI.ElementaryPositivity.Packets.ascentMask`, `OAI.ElementaryPositivity.Packets.card`, `OAI.ElementaryPositivity.Packets.emptyAnchorEquiv`, `OAI.ElementaryPositivity.Packets.fiber`, `OAI.ElementaryPositivity.Packets.fiberIso`, `OAI.ElementaryPositivity.Packets.fiberOrder`, `OAI.ElementaryPositivity.Packets.fromRows`, `OAI.ElementaryPositivity.Packets.gap`, `OAI.ElementaryPositivity.Packets.index` and 23 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `Chromatic_Histories_AnchorEmptyMask`, `Chromatic_Histories_PacketSortedWords`, `Chromatic_Histories_SortedFiberPerm`, `Chromatic_Histories_TriangularCommonHistory`, `Chromatic_QuantumTorus_Admissible`, `Chromatic_Walls_LaurentFiniteDecorations`, `Chromatic_Walls_LaurentGradedFibers`, `Chromatic_Walls_LaurentPolynomialEnergy`, `Chromatic_Witness_ElementaryProductDegree`, `Chromatic_Witness_ElementarySingletonCoefficient`, `Chromatic_Witness_GraphDecoratedHistories`, `Chromatic_Witness_GraphRequiredPackets`, `Chromatic_Witness_ProfilePartition`, `Chromatic_Witness_WitnessTransport`.
--
--   **Imports.** It imports the published bundle `Def_ElementaryPositivity`; the bundles `OAIQ368Chrom000` and `OAIQ368Chrom059` of this split; the published statements `OAI.ElementaryPositivity.TriangularDynamics.graph_common_history` and `OAI.ElementaryPositivity.TriangularDynamics.historyWeight_positive`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ368Chrom065`, `OAIQ368Chrom067` and `OAIQ368Chrom068`; the statement `OAI.ElementaryPositivity.TriangularDynamics.admissible_polynomial_expansion`; the proof of `OAI.ElementaryPositivity.TriangularDynamics.admissible_polynomial_expansion`.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Definitions.Def_ElementaryPositivity
import Definitions.Def_OAIQ368Chrom000
import Definitions.Def_OAIQ368Chrom059
import Theorems.Thm_OAI_ElementaryPositivity_TriangularDynamics_graph_common_history
import Theorems.Thm_OAI_ElementaryPositivity_TriangularDynamics_historyWeight_positive

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Histories_SortedFiberPerm
attribute [-instance] _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersFintype _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.degreesDecidableEq _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFinite _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
attribute [-simp] _root_.OAI.ElementaryPositivity.WallUnits.rescale_C
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.Packets
open scoped BigOperators
open Classical
noncomputable section
variable {n:ℕ} {B:Type*} [DecidableEq B]

def fiber (f:Fin n → B) (b:B) : Finset (Fin n):=Finset.univ.filter (fun i=>f i=b)
def card (f:Fin n → B) (b:B):= (fiber f b).card
@[simp] lemma mem_fiber (f:Fin n → B) (b:B) (i:Fin n) : i∈fiber f b ↔ f i=b:=by simp [fiber]
lemma card_eq (f:Fin n → B) (b:B) : card f b=Fintype.card {i // f i=b}:=by simp [card,fiber,Fintype.card_subtype]

def fiberOrder (f:Fin n → B) (b:B) {k:ℕ} (h:card f b=k) : Fin k ≃o {i // f i=b}:=
  ((fiber f b).orderIsoOfFin h).trans
    (OrderIso.setCongr {i | i∈fiber f b} {i | f i=b} (by ext i; simp))

def fiberIso (f g:Fin n → B) (h:∀b,card f b=card g b) (b:B) :
    {i // f i=b} ≃o {i // g i=b}:=
  (fiberOrder f b rfl).symm.trans (fiberOrder g b (h b).symm)

def sortedPerm (f g:Fin n → B) (h:∀b,card f b=card g b) : Equiv.Perm (Fin n):=
  Equiv.ofFiberEquiv (fun b=>(fiberIso f g h b).toEquiv)
lemma sortedPerm_map (f g:Fin n → B) (h:∀b,card f b=card g b) (i:Fin n) :
    g (sortedPerm f g h i)=f i:=Equiv.ofFiberEquiv_map _ _

def Sorted {A:Type*} [LT A] (f:Fin n → B) (w:Fin n → A) : Prop:=
  ∀i j,f i=f j → i<j → w i<w j
lemma sortedPerm_sorted (f g:Fin n → B) (h:∀b,card f b=card g b) :
    Sorted f (sortedPerm f g h) := by
  intro i j hij hlt
  change (fiberIso f g h (f i) ⟨i,rfl⟩).val <
    (fiberIso f g h (f j) ⟨j,rfl⟩).val
  have hj: (fiberIso f g h (f j) ⟨j,rfl⟩).val=
      (fiberIso f g h (f i) ⟨j,hij.symm⟩).val:=by
    have aux:∀b (hb:f j=b), (fiberIso f g h (f j) ⟨j,rfl⟩).val=
        (fiberIso f g h b ⟨j,hb⟩).val:=by
      intro b hb
      subst b
      rfl
    exact aux _ hij.symm
  rw [hj]
  exact (fiberIso f g h (f i)).strictMono hlt

omit [DecidableEq B] in
lemma sorted_unique (f g:Fin n → B) (w v:Equiv.Perm (Fin n))
    (hw:∀i,g (w i)=f i) (hv:∀i,g (v i)=f i)
    (hsw:Sorted f w) (hsv:Sorted f v) : w=v := by
  let e (u:Equiv.Perm (Fin n)) (hu:∀i,g (u i)=f i) (hs:Sorted f u) (b:B) :
      {i // f i=b} ≃o {i // g i=b}:=
    StrictMono.orderIsoOfSurjective (fun i=>⟨u i,by rw [hu,i.property]⟩)
      (fun i j hij=>hs i j (i.property.trans j.property.symm) hij)
      (by
        intro j
        refine ⟨⟨u.symm j,?_⟩,?_⟩
        · rw [←hu,u.apply_symm_apply]; exact j.property
        · exact Subtype.ext (u.apply_symm_apply j))
  apply Equiv.ext
  intro i
  have H:e w hw hsw (f i)=e v hv hsv (f i):=Subsingleton.elim _ _
  exact congrArg (fun q=> (q ⟨i,rfl⟩).val) H

lemma card_of_perm (f g:Fin n → B) (w:Equiv.Perm (Fin n)) (hw:∀i,g (w i)=f i) :
    ∀b,card f b=card g b := by
  intro b
  rw [card_eq,card_eq]
  exact Fintype.card_congr (w.subtypeEquiv (fun i=>by rw [hw]))
end
end ElementaryPositivity.Packets

end
section
namespace ElementaryPositivity.Packets
open scoped BigOperators
open Classical
noncomputable section
variable {n:ℕ}

def left (t:Fin (n-1)):Fin n:=⟨t.val,by omega⟩
def right (t:Fin (n-1)):Fin n:=⟨t.val+1,by omega⟩
def ascentMask {A:Type*} (R:A → A → Prop) (w:Fin n → A) : Finset (Fin (n-1)):=
  Finset.univ.filter (fun t=>R (w (left t)) (w (right t)))
@[simp] lemma mem_ascentMask {A:Type*} (R:A → A → Prop) (w:Fin n → A) (t:Fin (n-1)) :
    t∈ascentMask R w ↔ R (w (left t)) (w (right t)):=by simp [ascentMask]

def gap (J:Finset (Fin (n-1))) (k:ℕ) : ℕ:=if k∈J.image Fin.val then 0 else 1
def indexVal (J:Finset (Fin (n-1))) (k:ℕ) : ℕ:=∑t∈Finset.range k,gap J t
lemma indexVal_succ (J:Finset (Fin (n-1))) (k:ℕ) :
    indexVal J (k+1)=indexVal J k+gap J k:=by simp [indexVal,Finset.sum_range_succ]
lemma indexVal_mono (J:Finset (Fin (n-1))) : Monotone (indexVal J):=by
  apply monotone_nat_of_le_succ
  intro k
  rw [indexVal_succ]
  omega
lemma indexVal_le (J:Finset (Fin (n-1))) (k:ℕ) : indexVal J k≤k:=by
  induction k with
  | zero=>simp [indexVal]
  | succ k ih=>rw [indexVal_succ]; unfold gap; split_ifs <;> omega

def index (J:Finset (Fin (n-1))) (i:Fin n):Fin (n+1):=
  ⟨indexVal J i.val,by have H:=indexVal_le J i.val; omega⟩
lemma index_mono (J:Finset (Fin (n-1))) : Monotone (index J):=by
  intro i j hij
  exact indexVal_mono J hij
lemma index_adjacent (J:Finset (Fin (n-1))) (i j:Fin n) (h:i.val+1=j.val) :
    index J i=index J j ↔ (⟨i.val,by omega⟩:Fin (n-1))∈J := by
  rw [Fin.ext_iff]
  change indexVal J i.val=indexVal J j.val ↔ _
  rw [←h,indexVal_succ]
  have hm:i.val∈J.image Fin.val ↔ (⟨i.val,by omega⟩:Fin (n-1))∈J:=by
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨t,ht,he⟩
      have H:t=⟨i.val,by omega⟩:=Fin.ext he
      simpa only [←H] using ht
    · intro ht
      exact ⟨⟨i.val,by omega⟩,ht,rfl⟩
  simp only [gap,hm]
  split_ifs <;> simp_all
lemma index_left_right (J:Finset (Fin (n-1))) (t:Fin (n-1)) :
    index J (left t)=index J (right t) ↔ t∈J := by
  exact index_adjacent J _ _ rfl

lemma inside_of_required {A:Type*} (R:A → A → Prop)
    (hR:∀ ⦃first middle last : A⦄, R first middle → R middle last → R first last)
    (J:Finset (Fin (n-1))) (w:Fin n → A) (hw:J⊆ascentMask R w)
    (i j:Fin n) (hij:i<j) (he:index J i=index J j) : R (w i) (w j) := by
  cases n with
  | zero=>exact Fin.elim0 i
  | succ N=>
    have H:∀j:Fin (N+1),∀i:Fin (N+1),i<j → index J i=index J j → R (w i) (w j):=by
      intro j
      induction j using Fin.induction with
      | zero=>intro i hi; exact (not_lt_of_ge (Fin.zero_le i) hi).elim
      | succ k ih=>
        intro i hij he
        have hk:index J k.castSucc=index J k.succ:=by
          apply le_antisymm
          · exact index_mono J (by simp only [Fin.le_def,Fin.val_castSucc,Fin.val_succ]; omega)
          · rw [←he]
            exact index_mono J (by
              change i.val≤k.val
              change i.val<k.val+1 at hij
              omega)
        have hm:(⟨k.val,by omega⟩:Fin ((N+1)-1))∈J:=
          (index_adjacent J k.castSucc k.succ rfl).mp hk
        have hr:R (w k.castSucc) (w k.succ):=by
          exact (mem_ascentMask R w _).mp (hw hm)
        by_cases hik:i=k.castSucc
        · simpa only [hik] using hr
        · have hiv:i.val≠k.val:=fun H=>hik (Fin.ext H)
          have hit:i<k.castSucc:=by
            change i.val<k.val
            change i.val<k.val+1 at hij
            omega
          exact hR (ih i hit (he.trans hk.symm)) hr
    exact H j i hij he
end
end ElementaryPositivity.Packets

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Histories_PacketSortedWords
attribute [-instance] _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersFintype _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.degreesDecidableEq _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFinite _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
attribute [-simp] _root_.OAI.ElementaryPositivity.WallUnits.rescale_C
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.Packets
open scoped BigOperators
open Classical
noncomputable section
variable {n:ℕ} {A B:Type*} [Fintype A] [LinearOrder A] [Fintype B] [DecidableEq B]
variable (π:Fin n → B)

def rows (w:Fin n → A) (b:B):Finset A:=(fiber π b).image w
omit [Fintype A] [Fintype B] in
lemma sorted_injOn (w:Fin n → A) (hw:Sorted π w) (b:B) : Set.InjOn w (fiber π b) := by
  intro i hi j hj he
  have hh:π i=π j:=(mem_fiber π b i).mp hi |>.trans ((mem_fiber π b j).mp hj).symm
  rcases lt_trichotomy i j with h|h|h
  · exact False.elim ((ne_of_lt (hw i j hh h)) he)
  · exact h
  · exact False.elim ((ne_of_lt (hw j i hh.symm h)) he.symm)
omit [Fintype A] [Fintype B] in
lemma rows_card (w:Fin n → A) (hw:Sorted π w) (b:B) : (rows π w b).card=card π b:=
  Finset.card_image_of_injOn (sorted_injOn π w hw b)

def wordCount (w:Fin n → A) : A →₀ ℕ:=∑i,Finsupp.single (w i) 1
omit [Fintype A] in
lemma wordCount_apply (w:Fin n → A) (a:A) : wordCount w a=(Finset.univ.filter (fun i=>w i=a)).card:=by
  simp [wordCount,Finsupp.single_apply,eq_comm]
omit [Fintype A] [LinearOrder A] in
lemma wordCount_degree (w:Fin n → A) : (wordCount w).degree=n := by
  simp [wordCount,map_sum]

omit [Fintype A] in
lemma rows_colCount (w:Fin n → A) (hw:Sorted π w) : ElementaryMatrix.colCount (rows π w)=wordCount w := by
  unfold ElementaryMatrix.colCount rows wordCount
  conv_lhs=>arg 2; ext b; rw [Finset.sum_image (sorted_injOn π w hw b)]
  change (∑b,∑i∈Finset.univ.filter (fun i=>π i=b),Finsupp.single (w i) 1)=_
  rw [Finset.sum_fiberwise]

abbrev RowFamily:= {s:B → Finset A // ∀b,(s b).card=card π b}

def fromRows (s:RowFamily (A:=A) π) (i:Fin n) : A:=
  (s.val (π i)).orderEmbOfFin (s.property (π i)) ((fiberOrder π (π i) rfl).symm ⟨i,rfl⟩)

omit [Fintype A] [Fintype B] in
lemma fromRows_mem (s:RowFamily (A:=A) π) (i:Fin n) : fromRows π s i∈s.val (π i):=
  (s.val (π i)).orderEmbOfFin_mem _ _

omit [Fintype A] [Fintype B] in
lemma fromRows_at (s:RowFamily (A:=A) π) (b:B) (i:{i // π i=b}) :
    fromRows π s i.val=(s.val b).orderEmbOfFin (s.property b) ((fiberOrder π b rfl).symm i) := by
  have hi:=i.property
  rcases i with ⟨i,hi⟩
  dsimp only at hi ⊢
  subst b
  rfl

omit [Fintype A] [Fintype B] in
lemma fromRows_sorted (s:RowFamily (A:=A) π) : Sorted π (fromRows π s) := by
  intro i j hij hlt
  rw [fromRows_at π s (π i) ⟨i,rfl⟩,fromRows_at π s (π i) ⟨j,hij.symm⟩]
  exact ((s.val (π i)).orderEmbOfFin _).strictMono
    ((fiberOrder π (π i) rfl).symm.strictMono hlt)

omit [Fintype A] [Fintype B] in
lemma rows_fromRows (s:RowFamily (A:=A) π) : rows π (fromRows π s)=s.val := by
  funext b
  apply Finset.Subset.antisymm
  · intro a ha
    obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp ha
    have H:=fromRows_mem π s i
    rwa [(mem_fiber π b i).mp hi] at H
  · intro a ha
    let k:=((s.val b).orderIsoOfFin (s.property b)).symm ⟨a,ha⟩
    let i: {i // π i=b}:=fiberOrder π b rfl k
    refine Finset.mem_image.mpr ⟨i.val,(mem_fiber π b i.val).mpr i.property,?_⟩
    rw [fromRows_at π s b i]
    dsimp [i]
    rw [OrderIso.symm_apply_apply]
    exact congrArg Subtype.val (((s.val b).orderIsoOfFin (s.property b)).apply_symm_apply ⟨a,ha⟩)

omit [Fintype B] in
lemma sorted_rows_unique (w v:Fin n → A) (hw:Sorted π w) (hv:Sorted π v)
    (he:rows π w=rows π v) : w=v := by
  let iso (u:Fin n → A) (hu:Sorted π u) (b:B) : {i // π i=b} ≃o (rows π u b):=
    StrictMono.orderIsoOfSurjective (fun i=>⟨u i,Finset.mem_image.mpr ⟨i,(mem_fiber π b i.val).mpr i.property,rfl⟩⟩)
      (fun i j hij=>hu i j (i.property.trans j.property.symm) hij)
      (by
        rintro ⟨a,ha⟩
        obtain ⟨i,hi,he⟩:=Finset.mem_image.mp ha
        exact ⟨⟨i,(mem_fiber π b i).mp hi⟩,Subtype.ext he⟩)
  funext i
  let vIso:= (iso v hv (π i)).trans (OrderIso.setCongr _ _
    (congrArg (fun s:Finset A=>(s:Set A)) (congrFun he.symm (π i))))
  have H:iso w hw (π i)=vIso:=Subsingleton.elim _ _
  exact congrArg (fun q=>(q ⟨i,rfl⟩).val) H

end
end ElementaryPositivity.Packets

end
section
namespace ElementaryPositivity.Packets
open scoped BigOperators
open Classical
noncomputable section
variable {n:ℕ} {A:Type*} [Fintype A] [LinearOrder A]

def packetProfile (J:Finset (Fin (n-1))) : Fin (n+1) →₀ ℕ:=wordCount (index J)
lemma packetProfile_apply (J:Finset (Fin (n-1))) (b:Fin (n+1)) :
    packetProfile J b=card (index J) b:=wordCount_apply _ _
lemma packetProfile_degree (J:Finset (Fin (n-1))) : (packetProfile J).degree=n:=wordCount_degree _

omit [Fintype A] in
lemma anchor_required_iff (J:Finset (Fin (n-1))) (w:Fin n → A) :
    J⊆ascentMask (·<·) w ↔ Sorted (index J) w := by
  constructor
  · intro hw i j he hij
    exact inside_of_required (·<·) (fun _ _ _=>lt_trans) J w hw i j hij he
  · intro hw t ht
    apply (mem_ascentMask _ _ _).mpr
    exact hw (left t) (right t) ((index_left_right J t).mpr ht) (by change t.val<t.val+1; omega)

abbrev AnchorWord (μ:A →₀ ℕ):={w:Fin n → A // wordCount w=μ}
abbrev RequiredAnchor (μ:A →₀ ℕ) (J:Finset (Fin (n-1))):=
  {w:Fin n → A // wordCount w=μ ∧ J⊆ascentMask (·<·) w}
abbrev PacketRows (μ:A →₀ ℕ) (J:Finset (Fin (n-1))):=
  {s:Fin (n+1) → Finset A // ElementaryMatrix.rowCount s=packetProfile J ∧ ElementaryMatrix.colCount s=μ}

def anchorRowsEquiv (μ:A →₀ ℕ) (J:Finset (Fin (n-1))) : RequiredAnchor μ J ≃ PacketRows μ J where
  toFun w:=⟨rows (index J) w.val,by
    have hs:Sorted (index J) w.val:=(anchor_required_iff J w.val).mp w.property.2
    constructor
    · apply (ElementaryMatrix.rowCount_eq _ _).mpr
      intro b
      rw [rows_card _ _ hs,packetProfile_apply]
    · rw [rows_colCount _ _ hs,w.property.1]⟩
  invFun s:=by
    let t:RowFamily (A:=A) (index J):=⟨s.val,fun b=>by
      rw [←packetProfile_apply J b]
      exact (ElementaryMatrix.rowCount_eq _ _).mp s.property.1 b⟩
    exact ⟨fromRows (index J) t,by
      constructor
      · rw [←rows_colCount _ _ (fromRows_sorted _ t),rows_fromRows]
        exact s.property.2
      · exact (anchor_required_iff J _).mpr (fromRows_sorted _ t)⟩
  left_inv w:=by
    apply Subtype.ext
    exact sorted_rows_unique _ _ _ (fromRows_sorted _ _) ((anchor_required_iff J w.val).mp w.property.2)
      (rows_fromRows _ _)
  right_inv s:=by
    apply Subtype.ext
    exact rows_fromRows _ _

lemma requiredAnchor_card {R:Type*} [CommSemiring R] (μ:A →₀ ℕ) (J:Finset (Fin (n-1))) :
    (∏i:A,MvPolynomial.esymm (Fin (n+1)) R (μ i)).coeff (packetProfile J)=
      (Fintype.card (RequiredAnchor μ J):R) := by
  rw [ElementaryMatrix.duality,ElementaryMatrix.elementary_product_coeff]
  rw [Fintype.card_congr (anchorRowsEquiv μ J)]
  simp only [Fintype.card_subtype]
  rw [←Finset.sum_filter]
  simp
end
end ElementaryPositivity.Packets

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Histories_AnchorEmptyMask
attribute [-instance] _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.degreesDecidableEq _root_.OAI.ElementaryPositivity.TriangularDynamics.instAntisymmCellPhaseLE _root_.OAI.ElementaryPositivity.TriangularDynamics.instIsTransCellPhaseLE _root_.OAI.ElementaryPositivity.TriangularDynamics.instTotalCellPhaseLE
attribute [-simp] _root_.OAI.ElementaryPositivity.WallUnits.rescale_C
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.Packets
open scoped BigOperators
open Classical
noncomputable section
variable {n:ℕ} {A:Type*} [Fintype A] [LinearOrder A]

omit [Fintype A] [LinearOrder A] in
lemma wordCount_multiset (w:Fin n → A) : (wordCount w).toMultiset=(List.ofFn w:Multiset A) := by
  induction n with
  | zero=>simp [wordCount]
  | succ n ih=>
    simp only [wordCount,Fin.sum_univ_succ,map_add,Finsupp.toMultiset_single,one_nsmul,List.ofFn_succ]
    rw [←wordCount,ih]
    rfl

omit [Fintype A] in
lemma empty_ascent_iff (w:Fin n → A) : ascentMask (·<·) w=∅ ↔ Antitone w := by
  cases n with
  | zero=>simp only [Finset.eq_empty_iff_forall_notMem]; exact ⟨fun _ i=>Fin.elim0 i,fun _ t=>Fin.elim0 t⟩
  | succ N=>
    rw [Fin.antitone_iff_succ_le]
    constructor
    · intro h i
      by_contra hn
      let t:Fin ((N+1)-1):=⟨i.val,by omega⟩
      have ht:t∈ascentMask (·<·) w:=by
        apply (mem_ascentMask _ _ _).mpr
        exact lt_of_not_ge hn
      rw [h] at ht
      exact Finset.notMem_empty t ht
    · intro h
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro t ht
      have H:=h ⟨t.val,by omega⟩
      exact (not_lt_of_ge H) ((mem_ascentMask _ _ _).mp ht)

omit [Fintype A] in
lemma antitone_word_unique (w v:Fin n → A) (hw:Antitone w) (hv:Antitone v)
    (hc:wordCount w=wordCount v) : w=v := by
  have hm:(List.ofFn w:Multiset A)=(List.ofFn v:Multiset A):=by rw [←wordCount_multiset,←wordCount_multiset,hc]
  have hp:(List.ofFn w).Perm (List.ofFn v):=Quotient.exact hm
  have hl:List.ofFn w=List.ofFn v:=List.Perm.eq_of_pairwise' (r:=fun a b:A=>a≥b)
    (List.pairwise_ofFn.mpr (fun i j hij=>hw hij.le))
    (List.pairwise_ofFn.mpr (fun i j hij=>hv hij.le)) hp
  exact List.ofFn_injective hl

omit [Fintype A] in
lemma exists_antitone_word (μ:A →₀ ℕ) (hμ:μ.degree=n) :
    ∃w:Fin n → A,wordCount w=μ ∧ Antitone w := by
  let l:=μ.toMultiset.sort (·≥·)
  have hl:l.length=n:=by
    rw [Multiset.length_sort,Finsupp.card_toMultiset]
    exact hμ
  have H:∃w:Fin l.length → A,wordCount w=μ ∧ Antitone w:=by
    refine ⟨l.get,?_,?_⟩
    · apply Finsupp.orderIsoMultiset.injective
      change (wordCount l.get).toMultiset=μ.toMultiset
      rw [wordCount_multiset,List.ofFn_get]
      exact Multiset.sort_eq _ _
    · intro i j hij
      rcases lt_or_eq_of_le hij with hit|rfl
      · exact (List.pairwise_iff_get.mp (Multiset.pairwise_sort μ.toMultiset (·≥·))) i j hit
      · exact le_rfl
  exact hl ▸ H

abbrev EmptyAnchor (μ:A →₀ ℕ):={w:AnchorWord (n:=n) μ // ascentMask (·<·) w.val=∅}

def emptyAnchorEquiv (μ:A →₀ ℕ) (hμ:μ.degree=n) : EmptyAnchor (n:=n) μ ≃ PUnit where
  toFun _:=PUnit.unit
  invFun _:=⟨⟨(exists_antitone_word μ hμ).choose,(exists_antitone_word μ hμ).choose_spec.1⟩,
    (empty_ascent_iff _).mpr (exists_antitone_word μ hμ).choose_spec.2⟩
  left_inv w:=by
    apply Subtype.ext
    apply Subtype.ext
    apply antitone_word_unique
    · exact (exists_antitone_word μ hμ).choose_spec.2
    · exact (empty_ascent_iff _).mp w.property
    · exact (exists_antitone_word μ hμ).choose_spec.1.trans w.val.property.symm
  right_inv _:=rfl
end
end ElementaryPositivity.Packets

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Histories_TriangularCommonHistory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.TriangularDynamics
open QuantumTorus WallUnits LatticeExtension LatticeRealization PowerSeries PowerSeriesAdjoint
open scoped BigOperators
open Classical
noncomputable section
variable {n:ℕ}

lemma leafProfile_degree {E:Type*} [AddCommGroup E] [Module ℝ E] (N:ℕ)
    (p:LocalHistoryFormula (Extended (Vertex n (Cell n))) E)
    (l:{l:p.Leaf // AnchoredLeaf N p l}) : (leafProfile N p l).degree=N := l.property.choose_spec.1
end
end ElementaryPositivity.TriangularDynamics

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_Admissible
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersFintype _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.degreesDecidableEq _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
attribute [-simp] _root_.OAI.ElementaryPositivity.WallUnits.rescale_C
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.NaturalUnitIntervalGraph
variable {n : ℕ} (G : ElementaryPositivity.NaturalUnitIntervalGraph n)

def Admissible (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ i j : Fin n, i.val + 1 = j.val → σ i < σ j → G.Edge (σ i) (σ j)

instance instDecidableAdmissible (σ : Equiv.Perm (Fin n)) : Decidable (G.Admissible σ) :=
  inferInstanceAs (Decidable (∀ i j : Fin n,
    i.val + 1 = j.val → σ i < σ j → G.Edge (σ i) (σ j)))

theorem graphInversions_eq_card_invertedEdges (σ : Equiv.Perm (Fin n)) :
    G.graphInversions σ = (G.invertedEdges σ).card := by
  unfold graphInversions
  apply Finset.card_bij (fun ij _ => (σ ij.2, σ ij.1))
  · rintro ⟨i,j⟩ hij
    obtain ⟨hij,hlt,he⟩ := (Finset.mem_filter.mp hij).2
    simp only [mem_invertedEdges, Equiv.symm_apply_apply]
    exact ⟨hlt, (G.edge_comm _ _).mp he, hij⟩
  · rintro ⟨i,j⟩ _ ⟨k,l⟩ _ heq
    have hj := σ.injective (congrArg Prod.fst heq)
    have hi := σ.injective (congrArg Prod.snd heq)
    exact Prod.ext hi hj
  · rintro ⟨a,b⟩ hab
    obtain ⟨hab,he,hpos⟩ := (G.mem_invertedEdges σ _).mp hab
    refine ⟨(σ.symm b, σ.symm a), ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Equiv.apply_symm_apply]
      exact ⟨hpos, hab, (G.edge_comm _ _).mp he⟩
    · simp

noncomputable def inversionChromatic (r : ℕ) : MvPolynomial (Fin r) (Polynomial ℕ) :=
  ∑ f ∈ Finset.univ.filter (G.Proper (r := r)),
    MvPolynomial.C (Polynomial.X ^ G.coloringInversions f) *
      ∏ i : Fin n, MvPolynomial.X (f i)

end ElementaryPositivity.NaturalUnitIntervalGraph

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_LaurentFiniteDecorations
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.LaurentPositive
open WallUnits
open scoped BigOperators
open Classical
noncomputable section

def multiplicity (w:LaurentSeries ℚ) (h:Positive w) (j:ℤ) : ℕ:=(h j).choose
lemma multiplicity_cast (w:LaurentSeries ℚ) (h:Positive w) (j:ℤ) :
    (multiplicity w h j:ℚ)=w.coeff j:=(h j).choose_spec.symm
lemma coeff_nonneg (w:LaurentSeries ℚ) (h:Positive w) (j:ℤ) : 0≤w.coeff j:=by
  rw [←multiplicity_cast w h j]
  exact Nat.cast_nonneg _

lemma coeff_mul_natCast (w:LaurentSeries ℚ) (k:ℕ) (j:ℤ) :
    (w*k).coeff j=w.coeff j*k := by
  calc
    _ = (k • w).coeff j:=by rw [nsmul_eq_mul,mul_comm]
    _ = k • w.coeff j:=congrFun HahnSeries.coeff_nsmul j
    _ = _:=by simp only [nsmul_eq_mul,mul_comm]

lemma support_of_positive_sum {L:Type*} [Fintype L] (w:L → LaurentSeries ℚ)
    (hw:∀l,Positive (w l)) (c:L → ℕ) (hc:∀l,0 < c l)
    (P:ℤ → Prop) (H:∀j,¬P j → (∑l,w l*c l).coeff j=0) :
    ∀l j,(w l).coeff j≠0 → P j := by
  intro l j hj
  by_contra hn
  have Hz:=H j hn
  rw [HahnSeries.coeff_sum] at Hz
  simp only [coeff_mul_natCast] at Hz
  have hnon:∀i,0≤(w i).coeff j*(c i:ℚ):=fun i=>mul_nonneg (coeff_nonneg _ (hw i) j) (Nat.cast_nonneg _)
  have hle:=Finset.single_le_sum (f:=fun i=>(w i).coeff j*(c i:ℚ))
    (fun i _=>hnon i) (Finset.mem_univ l)
  rw [Hz] at hle
  have hp:0<(w l).coeff j:=lt_of_le_of_ne (coeff_nonneg _ (hw l) j) (Ne.symm hj)
  have hcp:0<(c l:ℚ):=Nat.cast_pos.mpr (hc l)
  exact (not_lt_of_ge hle) (mul_pos hp hcp)

lemma exponent_injective (M:ℕ) : Function.Injective (fun k:Fin (M+1)=>(M:ℤ)-2*(k.val:ℤ)) := by
  intro k l h
  change (M:ℤ)-2*(k.val:ℤ)=(M:ℤ)-2*(l.val:ℤ) at h
  apply Fin.ext
  omega

lemma finite_expansion (w:LaurentSeries ℚ) (hw:Positive w) (M:ℕ)
    (hs:∀j,w.coeff j≠0 → ∃k:Fin (M+1),j=(M:ℤ)-2*(k.val:ℤ)) :
    w=∑k:Fin (M+1),HahnSeries.single ((M:ℤ)-2*k.val)
      (multiplicity w hw ((M:ℤ)-2*k.val):ℚ) := by
  ext j
  rw [HahnSeries.coeff_sum]
  by_cases he:∃k:Fin (M+1),j=(M:ℤ)-2*(k.val:ℤ)
  · obtain ⟨k,rfl⟩:=he
    rw [Finset.sum_eq_single k]
    · rw [HahnSeries.coeff_single,ite_eq_left rfl,multiplicity_cast]
    · intro l hl hlk
      exact HahnSeries.coeff_single_of_ne (fun H=>hlk ((exponent_injective M) H.symm))
    · simp
  · rw [not_exists] at he
    have hz:w.coeff j=0:=by
      by_contra hn
      obtain ⟨k,hk⟩:=hs j hn
      exact he k hk
    rw [hz]
    apply Eq.symm
    apply Finset.sum_eq_zero
    intro k hk
    exact HahnSeries.coeff_single_of_ne (he k)

abbrev Decoration (w:LaurentSeries ℚ) (hw:Positive w) (M:ℕ) :=
  Σk:Fin (M+1),Fin (multiplicity w hw ((M:ℤ)-2*k.val))

lemma decoration_expansion (w:LaurentSeries ℚ) (hw:Positive w) (M:ℕ)
    (hs:∀j,w.coeff j≠0 → ∃k:Fin (M+1),j=(M:ℤ)-2*(k.val:ℤ)) :
    w=∑d:Decoration w hw M,(↑(LaurentRay.vUnit^(2*(d.1.val:ℤ)-(M:ℤ))):LaurentSeries ℚ) := by
  calc
    w = ∑k:Fin (M+1),HahnSeries.single ((M:ℤ)-2*k.val)
      (multiplicity w hw ((M:ℤ)-2*k.val):ℚ) := finite_expansion w hw M hs
    _ = _ := ?_
  unfold Decoration
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [LaurentRay.vUnit_zpow,Finset.sum_const,Finset.card_univ,Fintype.card_fin]
  have he:-(2*(k.val:ℤ)-(M:ℤ))=(M:ℤ)-2*k.val:=by omega
  rw [he]
  ext j
  simp only [HahnSeries.coeff_nsmul,HahnSeries.coeff_single]
  by_cases hj:j=(M:ℤ)-2*k.val <;> simp [hj,nsmul_eq_mul]
end
end ElementaryPositivity.LaurentPositive

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Witness_WitnessTransport
attribute [-instance] _root_.OAI.ElementaryPositivity.ExactMasks.exactFintype _root_.OAI.ElementaryPositivity.ExactMasks.requiredFintype _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersFintype _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.degreesDecidableEq _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
attribute [-simp] _root_.OAI.ElementaryPositivity.WallUnits.rescale_C
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity
namespace FiniteMatching

variable {A B : Type*} [DecidableEq B]
variable {P : A → Prop} {Q : B → Prop}

def align (e : A ≃ B) (f : {a // P a} ≃ {b // Q b}) (a : {a // P a}) : A ≃ B :=
  e.trans (Equiv.swap (e a.val) (f a).val)

@[simp] theorem align_at (e : A ≃ B) (f : {a // P a} ≃ {b // Q b})
    (a : {a // P a}) : align e f a a.val = (f a).val := by
  simp [align]

theorem align_preserves (e : A ≃ B) (f : {a // P a} ≃ {b // Q b})
    (a b : {a // P a}) (hb : e b.val = (f b).val) :
    align e f a b.val = (f b).val := by
  by_cases hab : a = b
  · subst b
    exact align_at _ _ _
  · have habval : a.val ≠ b.val := fun h => hab (Subtype.ext h)
    have he : (f b).val ≠ e a.val := by
      rw [← hb]
      exact fun h => habval (e.injective h.symm)
    have hf : (f b).val ≠ (f a).val :=
      fun h => hab (f.injective (Subtype.ext h.symm))
    simp [align, hb, Equiv.swap_apply_of_ne_of_ne he hf]

def compress (e : A ≃ B) (f : {a // P a} ≃ {b // Q b}) :
    List {a // P a} → A ≃ B
  | [] => e
  | a :: as => compress (align e f a) f as

 theorem compress_preserves (e : A ≃ B) (f : {a // P a} ≃ {b // Q b})
    (as : List {a // P a}) (b : {a // P a}) (hb : e b.val = (f b).val) :
    compress e f as b.val = (f b).val := by
  induction as generalizing e with
  | nil => exact hb
  | cons a as ih =>
    exact ih _ (align_preserves e f a b hb)

 theorem compress_at (e : A ≃ B) (f : {a // P a} ≃ {b // Q b})
    (as : List {a // P a}) (b : {a // P a}) (hb : b ∈ as) :
    compress e f as b.val = (f b).val := by
  induction as generalizing e with
  | nil => simp at hb
  | cons a as ih =>
    rcases List.mem_cons.mp hb with h | h
    · subst b
      exact compress_preserves (align e f a) f as a (align_at e f a)
    · exact ih (align e f a) h

omit [DecidableEq B] in
 theorem membership_iff (e : A ≃ B) (f : {a // P a} ≃ {b // Q b})
    (he : ∀ a : {a // P a}, e a.val = (f a).val) (a : A) :
    P a ↔ Q (e a) := by
  constructor
  · intro ha
    rw [he ⟨a, ha⟩]
    exact (f ⟨a, ha⟩).property
  · intro hq
    let a' := f.symm ⟨e a, hq⟩
    have haa : a'.val = a := by
      apply e.injective
      rw [he a']
      exact congrArg Subtype.val (f.apply_symm_apply ⟨e a, hq⟩)
    exact haa ▸ a'.property

def cancel (e : A ≃ B) (f : {a // P a} ≃ {b // Q b})
    (as : List {a // P a}) (complete : ∀ a, a ∈ as) :
    {a // ¬P a} ≃ {b // ¬Q b} :=
  (compress e f as).subtypeEquiv fun a =>
    not_congr (membership_iff (compress e f as) f
      (fun b => compress_at e f as b (complete b)) a)

variable {W : Type*}

 theorem swap_preserves (energy : B → W) (x y : B) (h : energy x = energy y)
    (b : B) : energy (Equiv.swap x y b) = energy b := by
  by_cases hx : b = x
  · subst b
    simpa using h.symm
  · by_cases hy : b = y
    · subst b
      simpa using h
    · rw [Equiv.swap_apply_of_ne_of_ne hx hy]

 theorem align_energy (energyA : A → W) (energyB : B → W)
    (e : A ≃ B) (f : {a // P a} ≃ {b // Q b})
    (he : ∀ a, energyB (e a) = energyA a)
    (hf : ∀ a, energyB (f a).val = energyA a.val)
    (a : {a // P a}) (x : A) : energyB (align e f a x) = energyA x := by
  change energyB (Equiv.swap (e a.val) (f a).val (e x)) = _
  rw [swap_preserves energyB _ _ ((he a.val).trans (hf a).symm)]
  exact he x

 theorem compress_energy (energyA : A → W) (energyB : B → W)
    (e : A ≃ B) (f : {a // P a} ≃ {b // Q b})
    (he : ∀ a, energyB (e a) = energyA a)
    (hf : ∀ a, energyB (f a).val = energyA a.val)
    (as : List {a // P a}) (x : A) : energyB (compress e f as x) = energyA x := by
  induction as generalizing e with
  | nil => exact he x
  | cons a as ih => exact ih _ (align_energy energyA energyB e f he hf a)

 theorem cancel_energy (energyA : A → W) (energyB : B → W)
    (e : A ≃ B) (f : {a // P a} ≃ {b // Q b})
    (he : ∀ a, energyB (e a) = energyA a)
    (hf : ∀ a, energyB (f a).val = energyA a.val)
    (as : List {a // P a}) (complete : ∀ a, a ∈ as) (x : {a // ¬P a}) :
    energyB (cancel e f as complete x).val = energyA x.val :=
  compress_energy energyA energyB e f he hf as x.val

end FiniteMatching
end ElementaryPositivity

namespace ElementaryPositivity
namespace ExactMasks

variable {A B I W : Type*} [DecidableEq I]

def Strict (mask : A → Finset I) (J : Finset I) := {a // J ⊂ mask a}

def GradedEquiv (energyA : A → W) (energyB : B → W) :=
  {e : A ≃ B // ∀ a, energyB (e a) = energyA a}

def strictFibers (mask : A → Finset I) (J : Finset I) :
    Strict mask J ≃ Σ K : {K : Finset I // J ⊂ K}, Exact mask K.val where
  toFun a := ⟨⟨mask a.val, a.property⟩, ⟨a.val, rfl⟩⟩
  invFun a := ⟨a.2.val, by simpa only [a.2.property] using a.1.property⟩
  left_inv _ := rfl
  right_inv a := by
    rcases a with ⟨⟨K, hk⟩, ⟨a, ha⟩⟩
    dsimp only at ha
    subst K
    rfl

def internalStrict (mask : A → Finset I) (J : Finset I) :
    {a : Required mask J // mask a.val ≠ J} ≃ Strict mask J where
  toFun a := ⟨a.val.val, Finset.ssubset_iff_subset_ne.mpr
    ⟨a.val.property, Ne.symm a.property⟩⟩
  invFun a := ⟨⟨a.val, (Finset.ssubset_iff_subset_ne.mp a.property).1⟩,
    Ne.symm ((Finset.ssubset_iff_subset_ne.mp a.property).2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

def exactCompl (mask : A → Finset I) (J : Finset I) :
    Exact mask J ≃ {a : Required mask J // ¬mask a.val ≠ J} where
  toFun a := ⟨⟨a.val, by rw [a.property]⟩, not_not.mpr a.property⟩
  invFun a := ⟨a.val.val, not_not.mp a.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def strictEquiv (maskA : A → Finset I) (maskB : B → Finset I) (J : Finset I)
    (ih : ∀ K, J ⊂ K → Exact maskA K ≃ Exact maskB K) :
    Strict maskA J ≃ Strict maskB J :=
  (strictFibers maskA J).trans
    ((Equiv.sigmaCongrRight fun K : {K : Finset I // J ⊂ K} => ih K.val K.property).trans
      (strictFibers maskB J).symm)

omit [DecidableEq I] in
 theorem strictEquiv_energy (maskA : A → Finset I) (maskB : B → Finset I)
    (energyA : A → W) (energyB : B → W) (J : Finset I)
    (ih : ∀ K, J ⊂ K → Exact maskA K ≃ Exact maskB K)
    (hh : ∀ K h a, energyB (ih K h a).val = energyA a.val)
    (a : Strict maskA J) :
    energyB (strictEquiv maskA maskB J ih a).val = energyA a.val := by
  exact hh (maskA a.val) a.property ⟨a.val, rfl⟩

variable [Fintype A] [Encodable A] [DecidableEq B]

def step (maskA : A → Finset I) (maskB : B → Finset I)
    (energyA : A → W) (energyB : B → W) (J : Finset I)
    (required : GradedEquiv
      (fun a : Required maskA J => energyA a.val)
      (fun b : Required maskB J => energyB b.val))
    (ih : ∀ K, J ⊂ K → GradedEquiv
      (fun a : Exact maskA K => energyA a.val)
      (fun b : Exact maskB K => energyB b.val)) :
    GradedEquiv (fun a : Exact maskA J => energyA a.val)
      (fun b : Exact maskB J => energyB b.val) := by
  letI : DecidableEq (Required maskB J) :=
    inferInstanceAs (DecidableEq {b : B // J ⊆ maskB b})
  letI : Fintype (Required maskA J) :=
    inferInstanceAs (Fintype {a : A // J ⊆ maskA a})
  letI : Encodable (Required maskA J) :=
    inferInstanceAs (Encodable {a : A // J ⊆ maskA a})
  let ilarge := strictEquiv maskA maskB J (fun K h => (ih K h).val)
  let internal := (internalStrict maskA J).trans
    (ilarge.trans (internalStrict maskB J).symm)
  let enumeration := Encodable.sortedUniv {a : Required maskA J // maskA a.val ≠ J}
  have complete : ∀ a, a ∈ enumeration := fun a => Encodable.mem_sortedUniv a
  let cancelled := FiniteMatching.cancel required.val internal enumeration complete
  refine ⟨(exactCompl maskA J).trans (cancelled.trans (exactCompl maskB J).symm), ?_⟩
  intro a
  apply FiniteMatching.cancel_energy
    (fun a : Required maskA J => energyA a.val)
    (fun b : Required maskB J => energyB b.val)
    required.val internal required.property
  intro x
  exact strictEquiv_energy maskA maskB energyA energyB J
    (fun K h => (ih K h).val) (fun K h => (ih K h).property)
    (internalStrict maskA J x)

def refine [Fintype I] (maskA : A → Finset I) (maskB : B → Finset I)
    (energyA : A → W) (energyB : B → W)
    (required : ∀ J, GradedEquiv
      (fun a : Required maskA J => energyA a.val)
      (fun b : Required maskB J => energyB b.val)) (J : Finset I) :
    GradedEquiv (fun a : Exact maskA J => energyA a.val)
      (fun b : Exact maskB J => energyB b.val) :=
  step maskA maskB energyA energyB J (required J)
    (fun K _ => refine maskA maskB energyA energyB required K)
termination_by Fintype.card I - J.card
decreasing_by
  rename_i strictSubset
  have hjk := Finset.card_lt_card strictSubset
  have hk := Finset.card_le_univ K
  omega

end ExactMasks
end ElementaryPositivity

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_LaurentGradedFibers
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.LaurentPositive
open WallUnits
open scoped BigOperators
open Classical
noncomputable section
variable {A B:Type*} [Fintype A] [Fintype B]

lemma coefficient_energy_sum (M:ℕ) (E:A → ℕ) (k:ℕ) :
    (∑a,(↑(LaurentRay.vUnit^(2*(E a:ℤ)-(M:ℤ))):LaurentSeries ℚ)).coeff ((M:ℤ)-2*(k:ℤ))=
      (Fintype.card {a // E a=k}:ℚ) := by
  rw [HahnSeries.coeff_sum]
  simp only [LaurentRay.vUnit_zpow,HahnSeries.coeff_single]
  have he:∀a,((M:ℤ)-2*(k:ℤ)= -(2*(E a:ℤ)-(M:ℤ))) ↔ E a=k:=by intro a; omega
  simp_rw [he]
  rw [←Finset.sum_filter]
  simp [Fintype.card_subtype]

lemma fiber_card_of_energy_sum (M:ℕ) (EA:A → ℕ) (EB:B → ℕ)
    (h:(∑a,(↑(LaurentRay.vUnit^(2*(EA a:ℤ)-(M:ℤ))):LaurentSeries ℚ))=
      ∑b,(↑(LaurentRay.vUnit^(2*(EB b:ℤ)-(M:ℤ))):LaurentSeries ℚ)) (k:ℕ) :
    Fintype.card {a // EA a=k}=Fintype.card {b // EB b=k} := by
  have H:=congrArg (fun w:LaurentSeries ℚ=>w.coeff ((M:ℤ)-2*(k:ℤ))) h
  rw [coefficient_energy_sum,coefficient_energy_sum] at H
  exact_mod_cast H

def gradedEquivOfEnergySum (M:ℕ) (EA:A → ℕ) (EB:B → ℕ)
    (h:(∑a,(↑(LaurentRay.vUnit^(2*(EA a:ℤ)-(M:ℤ))):LaurentSeries ℚ))=
      ∑b,(↑(LaurentRay.vUnit^(2*(EB b:ℤ)-(M:ℤ))):LaurentSeries ℚ)) :
    ExactMasks.GradedEquiv EA EB :=
  ⟨Equiv.ofFiberEquiv (fun k=>Fintype.equivOfCardEq (fiber_card_of_energy_sum M EA EB h k)),
    Equiv.ofFiberEquiv_map _⟩
end
end ElementaryPositivity.LaurentPositive

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_LaurentPolynomialEnergy
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.LaurentPositive
open WallUnits
open scoped BigOperators
open Classical
noncomputable section

def qLaurent : Polynomial ℕ →+* LaurentSeries ℚ:=
  Polynomial.eval₂RingHom (Nat.castRingHom _) (HahnSeries.single (-2) 1)

def centered (M:ℕ) (p:Polynomial ℕ):LaurentSeries ℚ:=HahnSeries.single (M:ℤ) 1*qLaurent p
end
end ElementaryPositivity.LaurentPositive

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Witness_ElementarySingletonCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.ElementaryMatrix
open scoped BigOperators
open Classical
noncomputable section
variable {A:Type*} [Fintype A] [DecidableEq A]
variable {R:Type*} [CommSemiring R]

def allOnes (n:ℕ) : Fin n →₀ ℕ:=Finsupp.equivFunOnFinite.symm (fun _=>1)
lemma allOnes_apply (n:ℕ) (i:Fin n) : allOnes n i=1:=rfl
lemma allOnes_degree (n:ℕ) : (allOnes n).degree=n := by
  change (allOnes n).sum (fun _ k=>k)=n
  rw [Finsupp.sum_fintype _ _ (fun _=>rfl)]
  simp [allOnes_apply]

lemma singleton_coefficient {n:ℕ} (μ:A →₀ ℕ) (hμ:μ.degree=n) :
    (∏i:A,MvPolynomial.esymm (Fin n) R (μ i)).coeff (allOnes n)=(μ.multinomial:R) := by
  rw [duality]
  simp only [allOnes_apply,MvPolynomial.esymm_one,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  change μ.sum (fun _ k=>k)=n at hμ
  rw [MvPolynomial.coeff_sum_X_pow_of_fintype,ite_eq_left hμ]

omit [Fintype A] [DecidableEq A] in
lemma profile_multinomial_pos (μ:A →₀ ℕ) : 0<μ.multinomial := Nat.multinomial_pos _ _
end
end ElementaryPositivity.ElementaryMatrix

end
section
namespace ElementaryPositivity.TriangularDynamics
open QuantumTorus WallUnits LatticeExtension LatticeRealization
open scoped BigOperators
open Classical
noncomputable section
variable {n:ℕ} (G:NaturalUnitIntervalGraph n)

def historyProfile (l:HistoryLeaf G) := leafProfile n (historySyntax G) l
lemma historyProfile_degree (l:HistoryLeaf G) : (historyProfile G l).degree=n :=
  leafProfile_degree n (historySyntax G) l

lemma history_coefficient (r:ℕ) (a:Fin r →₀ ℕ) (ha:a.degree=n) :
    (∑κ:Fin n → Fin r,
      if G.Proper κ ∧ (∀i,(Finset.univ.filter (fun j=>κ j=i)).card=a i) then
        (↑(LaurentRay.vUnit^(2*(G.coloringInversions κ:ℤ)-(G.edgeCount:ℤ))):LaurentSeries ℚ) else 0)=
    ∑l:HistoryLeaf G,historyWeight G l *
      (∏i:Fin (historyDimension G+1),MvPolynomial.esymm (Fin r) (LaurentSeries ℚ)
        (historyProfile G l i)).coeff a :=
  (graph_common_history G).choose_spec.choose_spec.2 r a ha

lemma history_singleton :
    (∑κ:Fin n → Fin n,
      if G.Proper κ ∧ (∀i,(Finset.univ.filter (fun j=>κ j=i)).card=1) then
        (↑(LaurentRay.vUnit^(2*(G.coloringInversions κ:ℤ)-(G.edgeCount:ℤ))):LaurentSeries ℚ) else 0)=
    ∑l:HistoryLeaf G,historyWeight G l*(historyProfile G l).multinomial := by
  have he:=history_coefficient G n (ElementaryMatrix.allOnes n) (ElementaryMatrix.allOnes_degree n)
  simp only [ElementaryMatrix.allOnes_apply] at he
  apply he.trans
  apply Finset.sum_congr rfl
  intro l hl
  rw [ElementaryMatrix.singleton_coefficient _ (historyProfile_degree G l)]

lemma historyWeight_support (l:HistoryLeaf G) (j:ℤ) (hj:(historyWeight G l).coeff j≠0) :
    ∃k:Fin (G.edgeCount+1),j=(G.edgeCount:ℤ)-2*(k.val:ℤ) := by
  apply LaurentPositive.support_of_positive_sum (historyWeight G) (historyWeight_positive G)
    (fun l=>(historyProfile G l).multinomial)
    (fun l=>ElementaryMatrix.profile_multinomial_pos _) _ _ l j hj
  intro j hn
  rw [←history_singleton G,HahnSeries.coeff_sum]
  apply Finset.sum_eq_zero
  intro κ hκ
  split_ifs
  · rw [LaurentRay.vUnit_zpow]
    apply HahnSeries.coeff_single_of_ne
    intro he
    apply hn
    refine ⟨⟨G.coloringInversions κ,by
      have H:G.coloringInversions κ≤G.edgeCount:=Finset.card_le_card (Finset.filter_subset _ _)
      omega⟩,?_⟩
    change j=(G.edgeCount:ℤ)-2*(G.coloringInversions κ:ℤ)
    omega
  · rfl
end
end ElementaryPositivity.TriangularDynamics

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Witness_GraphRequiredPackets
attribute [-instance] _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersFintype _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.degreesDecidableEq _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
attribute [-simp] _root_.OAI.ElementaryPositivity.WallUnits.rescale_C
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.NaturalUnitIntervalGraph
open Packets
open scoped BigOperators
open Classical
noncomputable section
variable {n:ℕ} (G:NaturalUnitIntervalGraph n)

def nonedgeLT (a b:Fin n):Prop:=a<b ∧ ¬G.Edge a b
lemma nonedgeLT_trans : ∀ ⦃first middle last : Fin n⦄,
    G.nonedgeLT first middle → G.nonedgeLT middle last → G.nonedgeLT first last := by
  intro a b c hab hbc
  refine ⟨hab.1.trans hbc.1,?_⟩
  intro hac
  rcases hac with hac|hca
  · exact hab.2 (Or.inl ⟨hab.1,hbc.1.le.trans hac.2⟩)
  · exact (not_lt_of_ge (hab.1.trans hbc.1).le) hca.1

def wordMask (w:Equiv.Perm (Fin n)):=ascentMask G.nonedgeLT w
lemma wordMask_empty (w:Equiv.Perm (Fin n)) : G.wordMask w=∅ ↔ G.Admissible w := by
  constructor
  · intro he i j hij hlt
    by_contra hn
    let t:Fin (n-1):=⟨i.val,by omega⟩
    have hi:left t=i:=Fin.ext rfl
    have hj:right t=j:=Fin.ext hij
    have ht:t∈G.wordMask w:=(mem_ascentMask _ _ _).mpr (by change _ < _ ∧ ¬_; simpa only [hi,hj] using And.intro hlt hn)
    rw [he] at ht
    exact Finset.notMem_empty t ht
  · intro hw
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro t ht
    exact ((mem_ascentMask _ _ _).mp ht).2
      (hw (left t) (right t) rfl ((mem_ascentMask _ _ _).mp ht).1)

lemma required_sorted (J:Finset (Fin (n-1))) (w:Equiv.Perm (Fin n))
    (hw:J⊆G.wordMask w):Sorted (index J) w:=by
  intro i j he hij
  exact (inside_of_required G.nonedgeLT G.nonedgeLT_trans J w hw i j hij he).1
lemma required_proper (J:Finset (Fin (n-1))) (w:Equiv.Perm (Fin n))
    (hw:J⊆G.wordMask w):G.Proper (fun a=>index J (w.symm a)):=by
  intro a b hab he
  rcases lt_trichotomy (w.symm a) (w.symm b) with h|h|h
  · have H:=inside_of_required G.nonedgeLT G.nonedgeLT_trans J w hw _ _ h he
    exact H.2 (by simpa only [w.apply_symm_apply] using hab)
  · have hh:a=b:=w.symm.injective h
    subst b
    exact G.edge_irrefl a hab
  · have H:=inside_of_required G.nonedgeLT G.nonedgeLT_trans J w hw _ _ h he.symm
    exact H.2 (by simpa only [w.apply_symm_apply] using (G.edge_comm a b).mp hab)

lemma required_of_sorted (J:Finset (Fin (n-1))) (κ:Fin n → Fin (n+1))
    (hκ:G.Proper κ) (w:Equiv.Perm (Fin n)) (hw:∀i,κ (w i)=index J i)
    (hs:Sorted (index J) w) : J⊆G.wordMask w := by
  intro t ht
  apply (mem_ascentMask _ _ _).mpr
  have he:index J (left t)=index J (right t):=(index_left_right J t).mpr ht
  refine ⟨hs _ _ he (by change t.val<t.val+1; omega),?_⟩
  intro hedge
  exact hκ _ _ hedge (by rw [hw,hw,he])

abbrev RequiredWord (J:Finset (Fin (n-1))):= {w:Equiv.Perm (Fin n) // J⊆G.wordMask w}
abbrev PacketColor (J:Finset (Fin (n-1))):=
  {κ:Fin n → Fin (n+1) // G.Proper κ ∧ ∀c,card κ c=card (index J) c}

def requiredColorEquiv (J:Finset (Fin (n-1))) : G.RequiredWord J ≃ G.PacketColor J where
  toFun w:=⟨fun a=>index J (w.val.symm a),G.required_proper J w.val w.property,
    fun c=>(card_of_perm (index J) (fun a=>index J (w.val.symm a)) w.val (by intro i; simp) c).symm⟩
  invFun κ:=⟨sortedPerm (index J) κ.val (fun c=>(κ.property.2 c).symm),
    G.required_of_sorted J κ.val κ.property.1 _ (sortedPerm_map _ _ _) (sortedPerm_sorted _ _ _)⟩
  left_inv w:=by
    apply Subtype.ext
    change sortedPerm (index J) (fun a=>index J (w.val.symm a)) _=w.val
    apply sorted_unique (index J) (fun a=>index J (w.val.symm a))
    · exact sortedPerm_map (index J) (fun a=>index J (w.val.symm a)) _
    · intro i; simp
    · exact sortedPerm_sorted (index J) (fun a=>index J (w.val.symm a)) _
    · exact G.required_sorted _ _ w.property
  right_inv κ:=by
    apply Subtype.ext
    funext a
    have H:=sortedPerm_map (index J) κ.val (fun c=>(κ.property.2 c).symm)
      ((sortedPerm (index J) κ.val (fun c=>(κ.property.2 c).symm)).symm a)
    simpa only [Equiv.apply_symm_apply] using H.symm

lemma packet_energy (J:Finset (Fin (n-1))) (κ:Fin n → Fin (n+1))
    (hκ:G.Proper κ) (w:Equiv.Perm (Fin n)) (hw:∀i,κ (w i)=index J i) :
    G.coloringInversions κ=G.graphInversions w := by
  rw [G.graphInversions_eq_card_invertedEdges,coloringInversions,invertedEdges]
  congr 1
  apply Finset.filter_congr
  intro ab hab
  have hedge:G.Edge ab.1 ab.2:=(Finset.mem_filter.mp hab).2.2
  have hne:κ ab.1≠κ ab.2:=hκ _ _ hedge
  have hcolor:∀a,κ a=index J (w.symm a):=fun a=>by simpa using hw (w.symm a)
  rw [hcolor ab.1,hcolor ab.2] at hne ⊢
  constructor
  · intro h
    by_contra hn
    exact (not_lt_of_ge (index_mono J (le_of_not_gt hn))) h
  · intro h
    exact lt_of_le_of_ne (index_mono J h.le) hne.symm

lemma requiredColorEquiv_energy (J:Finset (Fin (n-1))) (w:G.RequiredWord J) :
    G.coloringInversions (G.requiredColorEquiv J w).val=G.graphInversions w.val:=by
  apply G.packet_energy J _ (G.required_proper J w.val w.property) w.val
  intro i
  simp
end
end ElementaryPositivity.NaturalUnitIntervalGraph

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Witness_GraphDecoratedHistories
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity
open WallUnits
open scoped BigOperators
open Classical
noncomputable section
lemma sum_subtype_ite {A R:Type*} [Fintype A] [AddCommMonoid R] (P:A → Prop) [DecidablePred P] (f:A → R) :
    (∑a:{a // P a},f a.val)=∑a,if P a then f a else 0 := by
  rw [←Finset.sum_filter]
  exact (Finset.sum_subtype _ (by simp) f).symm
end
namespace TriangularDynamics
open Packets
open WallUnits
open scoped BigOperators
open Classical
noncomputable section
variable {n:ℕ} (G:NaturalUnitIntervalGraph n)

abbrev DecoratedLeaf:=Σl:HistoryLeaf G,
  LaurentPositive.Decoration (historyWeight G l) (historyWeight_positive G l) G.edgeCount

def leafEnergy (d:DecoratedLeaf G):ℕ:=d.2.1.val
abbrev DecoratedWord:=Σd:DecoratedLeaf G,AnchorWord (n:=n) (historyProfile G d.1)
def decoratedMask (w:DecoratedWord G):Finset (Fin (n-1)):=ascentMask (·<·) w.2.val
def decoratedEnergy (w:DecoratedWord G):ℕ:=leafEnergy G w.1
abbrev RequiredDecorated (J:Finset (Fin (n-1))):={w:DecoratedWord G // J⊆decoratedMask G w}

def requiredDecoratedEquiv (J:Finset (Fin (n-1))) : RequiredDecorated G J ≃
    Σd:DecoratedLeaf G,RequiredAnchor (n:=n) (historyProfile G d.1) J where
  toFun w:=⟨w.val.1,⟨w.val.2.val,w.val.2.property,w.property⟩⟩
  invFun w:=⟨⟨w.1,⟨w.2.val,w.2.property.1⟩⟩,w.2.property.2⟩
  left_inv _:=rfl
  right_inv _:=rfl

lemma decorated_coefficient (r:ℕ) (a:Fin r →₀ ℕ) (ha:a.degree=n) :
    (∑κ:Fin n → Fin r,
      if G.Proper κ ∧ (∀i,(Finset.univ.filter (fun j=>κ j=i)).card=a i) then
        (↑(LaurentRay.vUnit^(2*(G.coloringInversions κ:ℤ)-(G.edgeCount:ℤ))):LaurentSeries ℚ) else 0)=
    ∑d:DecoratedLeaf G,(↑(LaurentRay.vUnit^(2*(leafEnergy G d:ℤ)-(G.edgeCount:ℤ))):LaurentSeries ℚ) *
      (∏i:Fin (historyDimension G+1),MvPolynomial.esymm (Fin r) (LaurentSeries ℚ)
        (historyProfile G d.1 i)).coeff a := by
  rw [history_coefficient G r a ha]
  symm
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro l hl
  change (∑d:LaurentPositive.Decoration (historyWeight G l) (historyWeight_positive G l) G.edgeCount,
    (↑(LaurentRay.vUnit^(2*(d.1.val:ℤ)-(G.edgeCount:ℤ))):LaurentSeries ℚ)*
      (∏i:Fin (historyDimension G+1),MvPolynomial.esymm (Fin r) (LaurentSeries ℚ)
        (historyProfile G l i)).coeff a)=_
  rw [←Finset.sum_mul,←LaurentPositive.decoration_expansion _ _ _ (historyWeight_support G l)]

lemma required_energy_sum (J:Finset (Fin (n-1))) :
    (∑w:G.RequiredWord J,
      (↑(LaurentRay.vUnit^(2*(G.graphInversions w.val:ℤ)-(G.edgeCount:ℤ))):LaurentSeries ℚ))=
    ∑w:RequiredDecorated G J,
      (↑(LaurentRay.vUnit^(2*(decoratedEnergy G w.val:ℤ)-(G.edgeCount:ℤ))):LaurentSeries ℚ) := by
  have hc:(∑w:G.RequiredWord J,
      (↑(LaurentRay.vUnit^(2*(G.graphInversions w.val:ℤ)-(G.edgeCount:ℤ))):LaurentSeries ℚ))=
      ∑κ:G.PacketColor J,
      (↑(LaurentRay.vUnit^(2*(G.coloringInversions κ.val:ℤ)-(G.edgeCount:ℤ))):LaurentSeries ℚ):=by
    rw [←Equiv.sum_comp (G.requiredColorEquiv J)]
    apply Finset.sum_congr rfl
    intro w hw
    rw [G.requiredColorEquiv_energy]
  rw [hc]
  change (∑κ:{κ:Fin n → Fin (n+1) // G.Proper κ ∧ ∀c,card κ c=card (index J) c},
    (↑(LaurentRay.vUnit^(2*(G.coloringInversions κ.val:ℤ)-(G.edgeCount:ℤ))):LaurentSeries ℚ))=_
  rw [sum_subtype_ite (fun κ:Fin n → Fin (n+1)=>G.Proper κ ∧ ∀c,card κ c=card (index J) c)
    (fun κ=>(↑(LaurentRay.vUnit^(2*(G.coloringInversions κ:ℤ)-(G.edgeCount:ℤ))):LaurentSeries ℚ))]
  have hd:=decorated_coefficient G (n+1) (packetProfile J) (packetProfile_degree J)
  simp only [packetProfile_apply] at hd
  change (∑κ:Fin n → Fin (n+1),if G.Proper κ ∧ (∀i,card κ i=card (index J) i) then
    (↑(LaurentRay.vUnit^(2*(G.coloringInversions κ:ℤ)-(G.edgeCount:ℤ))):LaurentSeries ℚ) else 0)=_ at hd
  apply hd.trans
  rw [←Equiv.sum_comp (requiredDecoratedEquiv G J).symm]
  conv_rhs => rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro d hd
  rw [requiredAnchor_card]
  change (↑(LaurentRay.vUnit^(2*(leafEnergy G d:ℤ)-(G.edgeCount:ℤ))):LaurentSeries ℚ)*
    (Fintype.card (RequiredAnchor (historyProfile G d.1) J):LaurentSeries ℚ)=
      ∑y:RequiredAnchor (historyProfile G d.1) J,
        (↑(LaurentRay.vUnit^(2*(leafEnergy G d:ℤ)-(G.edgeCount:ℤ))):LaurentSeries ℚ)
  simp [mul_comm]

end
end TriangularDynamics
end ElementaryPositivity

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Witness_ProfilePartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity
open scoped BigOperators
open Classical
noncomputable section
variable {A:Type*} [Fintype A] {n:ℕ}

def profilePartition (μ:A →₀ ℕ) (hμ:μ.degree=n):Nat.Partition n:=
  Nat.Partition.ofSums n (Finset.univ.val.map μ) (by
    change (∑i:A,μ i)=n
    rw [←Finsupp.degree_eq_sum]
    exact hμ)

lemma esymmPart_profile {B R:Type*} [Fintype B] [CommSemiring R]
    (μ:A →₀ ℕ) (hμ:μ.degree=n) :
    MvPolynomial.esymmPart B R (profilePartition μ hμ)=∏i:A,MvPolynomial.esymm B R (μ i) := by
  have H:∀l:Multiset ℕ,((l.filter (·≠0)).map (MvPolynomial.esymm B R)).prod=
      (l.map (MvPolynomial.esymm B R)).prod:=by
    intro l
    induction l using Multiset.induction_on with
    | empty=>simp
    | cons k l ih=>
      by_cases hk:k=0
      · subst k; simp [MvPolynomial.esymm_zero,ih]
      · simp [hk,ih]
  unfold MvPolynomial.esymmPart profilePartition
  rw [Nat.Partition.ofSums_parts,H,Multiset.map_map]
  rfl
end
end ElementaryPositivity

end
section
namespace ElementaryPositivity.TriangularDynamics
open Packets
open scoped BigOperators
open Classical
noncomputable section
variable {n:ℕ} (G:NaturalUnitIntervalGraph n)

def requiredHistoryMatching (J:Finset (Fin (n-1))) :
    ExactMasks.GradedEquiv
      (fun w:ExactMasks.Required G.wordMask J=>G.graphInversions w.val)
      (fun w:ExactMasks.Required (decoratedMask G) J=>decoratedEnergy G w.val) :=
  LaurentPositive.gradedEquivOfEnergySum G.edgeCount _ _ (required_energy_sum G J)

def exactHistoryMatching (J:Finset (Fin (n-1))) :
    ExactMasks.GradedEquiv
      (fun w:ExactMasks.Exact G.wordMask J=>G.graphInversions w.val)
      (fun w:ExactMasks.Exact (decoratedMask G) J=>decoratedEnergy G w.val) := by
  letI:Encodable (Equiv.Perm (Fin n)):=Fintype.toEncodable _
  exact ExactMasks.refine G.wordMask (decoratedMask G) G.graphInversions (decoratedEnergy G)
    (requiredHistoryMatching G) J

def admissibleExactEquiv : {w:Equiv.Perm (Fin n) // G.Admissible w} ≃ ExactMasks.Exact G.wordMask ∅ where
  toFun w:=⟨w.val,(G.wordMask_empty w.val).mpr w.property⟩
  invFun w:=⟨w.val,(G.wordMask_empty w.val).mp w.property⟩
  left_inv _:=rfl
  right_inv _:=rfl

def emptyDecoratedEquiv : ExactMasks.Exact (decoratedMask G) ∅ ≃ DecoratedLeaf G where
  toFun w:=w.val.1
  invFun d:=⟨⟨d,((emptyAnchorEquiv.{0,1} (historyProfile G d.1) (historyProfile_degree G d.1)).symm PUnit.unit.{1}).val⟩,
    ((emptyAnchorEquiv.{0,1} (historyProfile G d.1) (historyProfile_degree G d.1)).symm PUnit.unit.{1}).property⟩
  left_inv w:=by
    rcases w with ⟨⟨d,w⟩,hw⟩
    have H: (emptyAnchorEquiv.{0,1} (historyProfile G d.1) (historyProfile_degree G d.1)).symm PUnit.unit.{1}=
        (⟨w,hw⟩:EmptyAnchor (n:=n) (historyProfile G d.1)):=
      (emptyAnchorEquiv.{0,1} (historyProfile G d.1) (historyProfile_degree G d.1)).symm_apply_apply ⟨w,hw⟩
    apply Subtype.ext
    exact congrArg (fun z:EmptyAnchor (n:=n) (historyProfile G d.1)=> (⟨d,z.val⟩:DecoratedWord G)) H
  right_inv _:=rfl

def admissibleHistoryEquiv : {w:Equiv.Perm (Fin n) // G.Admissible w} ≃ DecoratedLeaf G:=
  (admissibleExactEquiv G).trans ((exactHistoryMatching G ∅).val.trans (emptyDecoratedEquiv G))

def leafPartition (d:DecoratedLeaf G):Nat.Partition n:=
  profilePartition (historyProfile G d.1) (historyProfile_degree G d.1)

def admissiblePartition (w:{w:Equiv.Perm (Fin n) // G.Admissible w}):Nat.Partition n:=
  leafPartition G (admissibleHistoryEquiv G w)
end
end ElementaryPositivity.TriangularDynamics

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Witness_ElementaryProductDegree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.ElementaryMatrix
open scoped BigOperators
open Classical
noncomputable section
variable {A B:Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
omit [Fintype A] [DecidableEq A] [DecidableEq B] in
lemma colCount_degree (s:B → Finset A) : (colCount s).degree=(rowCount s).degree := by
  simp only [colCount,map_sum,Finsupp.degree_single,Finset.sum_const,smul_eq_mul,mul_one]
  rw [Finsupp.degree_eq_sum]
  rfl

lemma elementary_product_coeff_zero {R:Type*} [CommSemiring R]
    (μ:A →₀ ℕ) (a:B →₀ ℕ) (h:a.degree≠μ.degree) :
    (∏i:A,MvPolynomial.esymm B R (μ i)).coeff a=0 := by
  rw [elementary_product_coeff]
  apply Finset.sum_eq_zero
  intro s hs
  rw [ite_eq_right]
  rintro ⟨hr,hc⟩
  exact h (by rw [←hc,colCount_degree,hr])
end
end ElementaryPositivity.ElementaryMatrix

end
section
namespace ElementaryPositivity.Packets
open scoped BigOperators
variable {n:ℕ} {A R:Type*} [Fintype A] [LinearOrder A] [CommSemiring R]
omit [Fintype A] [LinearOrder A] in
lemma coloring_monomial (κ:Fin n → A) :
    (∏i:Fin n,MvPolynomial.X (κ i):MvPolynomial A R)=MvPolynomial.monomial (wordCount κ) 1 := by
  rw [wordCount,MvPolynomial.monomial_sum_one]
  rfl
end ElementaryPositivity.Packets

end

end OAI
end


