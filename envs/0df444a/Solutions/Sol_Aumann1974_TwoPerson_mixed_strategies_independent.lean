-- Prove2me | solution 1 for Aumann1974.TwoPerson.mixed_strategies_independent
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T17:27:02.408878+00:00
-- url     : https://prove2.me/submissions/016140a0-edc6-4431-9a5d-5f033d7f9770

import Definitions.Def_Aumann1974_TwoPerson_RandomizingStructure
import Mathlib.Tactic

namespace AumannFactor
open MeasureTheory Aumann1974.TwoPerson Finset

lemma factor_with {ι Ω:Type*} [Fintype ι] [DecidableEq ι] {mΩ:MeasurableSpace Ω}
    (R:RandomizingStructure ι Ω mΩ) (i:ι) (A:ι→Set Ω)
    (hm:∀j,MeasurableSet[R.J j] (A j))
    (hs:∀j,j≠i→IsSecret R j (A j)) (B:Set Ω) (hB:MeasurableSet[R.J i] B)
    (T:Finset ι) (hi:i∉T) :
    R.p i {ω|ω∈B ∧ ∀j∈T,ω∈A j}=R.p i B*∏j∈T,R.p i (A j) := by
  induction T using Finset.induction_on with
  | empty => simp
  | @insert j T hj ih =>
    have hji:j≠i:=by intro he;subst j;exact hi (mem_insert_self _ _)
    have hiT:i∉T:=fun h=>hi (mem_insert_of_mem h)
    let D:Set Ω:={ω|ω∈B ∧ ∀k∈T,ω∈A k}
    have hD:MeasurableSet[⨆(k:ι)(_ : k≠j),R.J k] D:=by
      have he:D=B∩⋂k∈T,A k:=by ext ω;simp [D]
      rw [he]
      have hleft:MeasurableSet[⨆(k:ι)(_ : k≠j),R.J k] B:=by
        have hle:R.J i≤⨆(k:ι)(_ : k≠j),R.J k:=le_iSup_of_le i (le_iSup_of_le hji.symm le_rfl)
        exact hle _ hB
      apply hleft.inter
      apply MeasurableSet.biInter (Finset.countable_toSet T)
      intro k hk
      have hkj:k≠j:=by intro he;subst k;exact hj hk
      have hle:R.J k≤⨆(k:ι)(_ : k≠j),R.J k:=le_iSup_of_le k (le_iSup_of_le hkj le_rfl)
      exact hle _ (hm k)
    have hh : {ω|ω∈B ∧ ∀k∈insert j T,ω∈A k}=A j∩D:=by
      ext ω;simp [D];tauto
    rw [hh,(hs j hji).2 i hji.symm D hD]
    rw [show R.p i D=R.p i B*∏k∈T,R.p i (A k) from ih hiT,Finset.prod_insert hj]
    ring

lemma factor_all {ι Ω:Type*} [Fintype ι] [DecidableEq ι] {mΩ:MeasurableSpace Ω}
    (R:RandomizingStructure ι Ω mΩ) (i:ι) (A:ι→Set Ω)
    (hm:∀j,MeasurableSet[R.J j] (A j))
    (hs:∀j,j≠i→IsSecret R j (A j)) :
    R.p i (⋂j,A j)=∏j,R.p i (A j) := by
  have hh:=factor_with R i A hm hs (A i) (hm i) (univ.erase i) (by simp)
  have he:{ω|ω∈A i ∧ ∀j∈univ.erase i,ω∈A j}=(⋂j,A j):=by
    ext ω;simp only [Set.mem_setOf_eq,Set.mem_iInter,Finset.mem_erase,Finset.mem_univ,and_true]
    constructor
    · rintro ⟨hi,h⟩ j
      by_cases hj:j=i
      · simpa [hj] using hi
      · exact h j hj
    · intro h;exact ⟨h i,fun j _=>h j⟩
  rw [he] at hh
  simpa only [Finset.mul_prod_erase univ (fun j=>R.p i (A j)) (Finset.mem_univ i)] using hh

lemma secret_univ {ι Ω:Type*} {mΩ:MeasurableSpace Ω} (R:RandomizingStructure ι Ω mΩ) (i:ι) :
    IsSecret R i Set.univ := by
  refine ⟨MeasurableSet.univ,?_⟩
  intro j hj B hB
  simp

lemma independent {ι Ω:Type*} [Fintype ι] [DecidableEq ι] {mΩ:MeasurableSpace Ω}
    {S:ι→Type*} (R:RandomizingStructure ι Ω mΩ) (s:∀j,Ω→S j)
    (hs:∀j,IsMixed R j (s j)) : IsUncorrelated R s := by
  intro a i B hB
  apply factor_all R i B
  · intro j
    rcases hB j with h|h
    · rw [h];exact (hs j (a j)).1
    · rw [h];exact MeasurableSet.univ
  · intro j hj
    rcases hB j with h|h
    · rw [h];exact hs j (a j)
    · rw [h];exact secret_univ R j

lemma profile {ι Ω:Type*} [Fintype ι] [DecidableEq ι] {mΩ:MeasurableSpace Ω}
    {S:ι→Type*} (R:RandomizingStructure ι Ω mΩ) (s:∀j,Ω→S j)
    (hs:∀j,IsStrategy R j (s j)) (a:∀j,S j) (i:ι)
    (hmix:∀j,j≠i→IsMixed R j (s j)) :
    R.p i {ω|∀j,s j ω=a j}=R.p i {ω|s i ω=a i}*R.p i {ω|∀j,j≠i→s j ω=a j} ∧
    R.p i {ω|s i ω=a i}*R.p i {ω|∀j,j≠i→s j ω=a j}=∏j,R.p i {ω|s j ω=a j} := by
  let A:ι→Set Ω:=fun j=>{ω|s j ω=a j}
  have hm:∀j,MeasurableSet[R.J j] (A j):=fun j=>hs j (a j)
  have hsec:∀j,j≠i→IsSecret R j (A j):=fun j hj=>hmix j hj (a j)
  have hall:=factor_all R i A hm hsec
  have hrest:=factor_with R i A hm hsec Set.univ MeasurableSet.univ (univ.erase i) (by simp)
  simp only [Set.mem_univ,true_and,Finset.mem_erase,Finset.mem_univ,and_true,measure_univ,one_mul] at hrest
  have hproduct:R.p i (A i)*R.p i {ω|∀j,j≠i→ω∈A j}=∏j,R.p i (A j):=by
    rw [hrest,Finset.mul_prod_erase univ (fun j=>R.p i (A j)) (Finset.mem_univ i)]
  constructor
  · simpa only [A,Set.iInter_setOf,Set.mem_setOf_eq] using hall.trans hproduct.symm
  · exact hproduct

end AumannFactor

open MeasureTheory Aumann1974.TwoPerson

theorem solution {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    {mΩ : MeasurableSpace Ω} {S : ι → Type*} [∀ i, Fintype (S i)]
    (R : RandomizingStructure ι Ω mΩ) (hII : AssumptionII R)
    (s : ∀ j, Ω → S j) (hmix : ∀ j, IsMixed R j (s j)) :
    IsUncorrelated R s := by
  exact AumannFactor.independent R s hmix
