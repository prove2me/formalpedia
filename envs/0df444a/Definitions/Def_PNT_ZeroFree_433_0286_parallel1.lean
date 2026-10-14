-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0286_parallel1
-- name    : PNT_ZeroFree_433_0286_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T12:11:06.156947+00:00
-- url     : https://prove2.me/theorems/82c14163-6e73-4ab8-a44b-6f16fb72a1f5
-- title:
--   Zero-free region foundations: RowCompletion.FreePrimePools [0286_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.RowCompletion.FreePrimePools
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/RowCompletion/FreePrimePools.lean#L85-L646

import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0048
import Definitions.Def_PNT_ZeroFree_433_0061
import Definitions.Def_PNT_ZeroFree_433_0150_parallel1
import Definitions.Def_PNT_ZeroFree_433_0153_parallel1
import Definitions.Def_PNT_ZeroFree_433_0154_parallel1
import Definitions.Def_PNT_ZeroFree_433_0183_parallel1
import Definitions.Def_PNT_ZeroFree_433_0197_parallel1
import Definitions.Def_PNT_ZeroFree_433_0237_parallel1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/RowCompletion/FreePrimePools.lean
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

section
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

section
open scoped BigOperators Classical

namespace CanonicalRowCompletion

section
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O

def freePrimePool (lengthScale Q0:Ideal Eis) : Finset (Ideal Eis) :=
  (CompletedGauss.primeSupport lengthScale).filter (fun P=>¬Q0≤P)

lemma mem_freePrimePool (lengthScale Q0 P:Ideal Eis) :
    P∈freePrimePool lengthScale Q0 ↔ P∈CompletedGauss.primeSupport lengthScale ∧ ¬Q0≤P := by
  simp only [freePrimePool,Finset.mem_filter]


end


section

variable {α β γ:Type*} [Fintype α] [Fintype β] [Fintype γ]

def optionalPrimeActive (e:α⊕β ≃ γ) (A:Finset γ) : Finset β :=
  Finset.univ.filter (fun b=>e (Sum.inr b)∈A)

omit [Fintype α] [Fintype γ] in
lemma mem_optionalPrimeActive (e:α⊕β ≃ γ) (A:Finset γ) (b:β) :
    b∈optionalPrimeActive e A ↔ e (Sum.inr b)∈A := by
  simp only [optionalPrimeActive,Finset.mem_filter,Finset.mem_univ,true_and]

def activePrimeUnionMap (e:α⊕β ≃ γ) (A:Finset γ)
    (hA:∀a:α,e (Sum.inl a)∈A) : α⊕optionalPrimeActive e A → A :=
  Sum.elim (fun a=>⟨e (Sum.inl a),hA a⟩)
    (fun b=>⟨e (Sum.inr b.val),(mem_optionalPrimeActive e A b.val).mp b.property⟩)

omit [Fintype α] [Fintype γ] in
lemma activePrimeUnionMap_bijective (e:α⊕β ≃ γ) (A:Finset γ)
    (hA:∀a:α,e (Sum.inl a)∈A) : Function.Bijective (activePrimeUnionMap e A hA) := by
  constructor
  · intro x y hxy
    have hv:=congrArg Subtype.val hxy
    cases x with
    | inl x=>cases y with
      | inl y=>exact congrArg Sum.inl (Sum.inl.inj (e.injective hv))
      | inr y=>cases e.injective hv
    | inr x=>cases y with
      | inl y=>cases e.injective hv
      | inr y=>exact congrArg Sum.inr (Subtype.ext (Sum.inr.inj (e.injective hv)))
  · intro a
    obtain ⟨x,hx⟩:=e.surjective a.val
    cases x with
    | inl x=>exact ⟨Sum.inl x,Subtype.ext hx⟩
    | inr x=>
      have hm:x∈optionalPrimeActive e A:=(mem_optionalPrimeActive e A x).mpr (hx.symm ▸ a.property)
      exact ⟨Sum.inr ⟨x,hm⟩,Subtype.ext hx⟩

noncomputable def activePrimeUnionEquiv (e:α⊕β ≃ γ) (A:Finset γ)
    (hA:∀a:α,e (Sum.inl a)∈A) : α⊕optionalPrimeActive e A ≃ A :=
  Equiv.ofBijective (activePrimeUnionMap e A hA) (activePrimeUnionMap_bijective e A hA)

omit [Fintype α] [Fintype γ] in
lemma activePrimeUnionEquiv_inl (e:α⊕β ≃ γ) (A:Finset γ)
    (hA:∀a:α,e (Sum.inl a)∈A) (a:α) :
    (activePrimeUnionEquiv e A hA (Sum.inl a)).val=e (Sum.inl a) := rfl

omit [Fintype α] [Fintype γ] in
lemma activePrimeUnionEquiv_inr (e:α⊕β ≃ γ) (A:Finset γ)
    (hA:∀a:α,e (Sum.inl a)∈A) (b:optionalPrimeActive e A) :
    (activePrimeUnionEquiv e A hA (Sum.inr b)).val=e (Sum.inr b.val) := rfl

omit [Fintype γ] in
theorem prod_activePrimeUnionEquiv {M:Type*} [CommMonoid M]
    (e:α⊕β ≃ γ) (A:Finset γ) (hA:∀a:α,e (Sum.inl a)∈A) (f:A → M) :
    (∏a:A,f a)=
      (∏a:α,f (activePrimeUnionEquiv e A hA (Sum.inl a)))*
        (∏b:optionalPrimeActive e A,f (activePrimeUnionEquiv e A hA (Sum.inr b))) := by
  calc
    _=(∏x:α⊕optionalPrimeActive e A,f (activePrimeUnionEquiv e A hA x)):=
      (Fintype.prod_equiv (activePrimeUnionEquiv e A hA) _ _ (fun _=>rfl)).symm
    _=_:=Fintype.prod_sum_type _

omit [Fintype γ] in
theorem sum_activePrimeUnionEquiv {M:Type*} [AddCommMonoid M]
    (e:α⊕β ≃ γ) (A:Finset γ) (hA:∀a:α,e (Sum.inl a)∈A) (f:A → M) :
    (∑a:A,f a)=
      (∑a:α,f (activePrimeUnionEquiv e A hA (Sum.inl a)))+
        (∑b:optionalPrimeActive e A,f (activePrimeUnionEquiv e A hA (Sum.inr b))) := by
  calc
    _=(∑x:α⊕optionalPrimeActive e A,f (activePrimeUnionEquiv e A hA x)):=
      (Fintype.sum_equiv (activePrimeUnionEquiv e A hA) _ _ (fun _=>rfl)).symm
    _=_:=Fintype.sum_sum_type _

theorem sum_prime_active_sets {M:Type*} [AddCommMonoid M]
    (e:α⊕β ≃ γ) (f:Finset γ → M) :
    (∑A:Finset γ,f A)=∑A:Finset (α⊕β),f (A.map e.toEmbedding) := by
  exact (Fintype.sum_equiv e.finsetCongr _ _ (fun _=>rfl)).symm

end


open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O


end CanonicalRowCompletion

local instance (priority := 2000) residualLabelDecidableEq (A B:Type*) : DecidableEq (A⊕B) :=
  Classical.decEq _
namespace CompletedGauss
open ActualEisensteinCubic LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O
variable {α β:Type*} [Fintype α] [Fintype β]

def residualZeroLabel (e:β→Fin 3) : α⊕β→Fin 3 := Sum.elim (fun _=>0) e

theorem sum_labels_drop_residual (f:(α⊕β→Fin 3)→ℂ)
    (hzero:∀e,(∃i:α,e (Sum.inl i)≠0)→f e=0) :
    (∑e:α⊕β→Fin 3,f e)=∑e:β→Fin 3,f (residualZeroLabel e) := by
  rw [←(Equiv.sumArrowEquivProdArrow α β (Fin 3)).symm.sum_comp]
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  rw [Finset.sum_eq_single (fun _ : α=>0)]
  · rfl
  · intro d hd hn
    apply hzero
    have hx:∃i:α,d i≠0:=by
      by_contra h
      push Not at h
      exact hn (funext h)
    obtain ⟨i,hi⟩:=hx
    exact ⟨i,hi⟩
  · simp

lemma reflectedBranch_residual_label_zero
    (P:α⊕β→Ideal Eis) [∀i,(P i).IsMaximal] (hg:∀i,lambda∉P i)
    (j:α⊕β→ℕ) (hj:∀i:α,j (Sum.inl i)=1)
    (e:α⊕β→Fin 3) (hbad:∃i:α,e (Sum.inl i)≠0) (n b:Eis) :
    reflectedBranch P hg j e n b=0 := by
  obtain ⟨i,hi⟩:=hbad
  unfold reflectedBranch
  apply Finset.prod_eq_zero (Finset.mem_univ (Sum.inl i))
  simp only [reflectedLocalPiece,hj,show (1:ℕ)≠4 by decide,ite_false,if_neg hi]

lemma reflectionExtractedDivisor_drop_residual
    (P:α⊕β→Ideal Eis) (j:α⊕β→ℕ) (hj:∀i:α,j (Sum.inl i)=1)
    (e:α⊕β→Fin 3) (v:Fin 3) :
    reflectionExtractedDivisor P j e v=
      reflectionExtractedDivisor (fun i:β=>P (Sum.inr i)) (fun i=>j (Sum.inr i))
        (fun i=>e (Sum.inr i)) v := by
  simp only [reflectionExtractedDivisor,Fintype.prod_sum_type]
  have hz:(∏i:α,reflectionExtractedPrime (P (Sum.inl i)) (j (Sum.inl i)) (e (Sum.inl i)) v)=1 := by
    simp only [hj,reflectionExtractedPrime,show (1:ℕ)≠4 by decide,show (1:ℕ)≠0 by decide,
      false_and,false_or,ite_false,Finset.prod_const_one]
  rw [hz,one_mul]

lemma reflectedBranch_drop_residual
    (P:α⊕β→Ideal Eis) [∀i,(P i).IsMaximal] (hg:∀i,lambda∉P i)
    (j:α⊕β→ℕ) (hj:∀i:α,j (Sum.inl i)=1)
    (e:β→Fin 3) (n b:Eis) :
    reflectedBranch P hg j (residualZeroLabel e) n b=
      (∏i:α,bracket (actualSextic (P (Sum.inl i)) (hg (Sum.inl i))) 1
        (Ideal.Quotient.mk _ (n*b^3)))*
      reflectedBranch (fun i:β=>P (Sum.inr i)) (fun i=>hg (Sum.inr i))
        (fun i=>j (Sum.inr i)) e n b := by
  simp only [reflectedBranch,Fintype.prod_sum_type,residualZeroLabel,Sum.elim_inl,Sum.elim_inr]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  simp only [reflectedLocalPiece,hj,show (1:ℕ)≠4 by decide,ite_false,ite_true]

end CompletedGauss
end

open scoped BigOperators Classical

local instance (priority := 2000) residualEquivDecidableEq (A B:Type*) : DecidableEq (A⊕B) :=
  Classical.decEq _
namespace CompletedGauss
open ActualEisensteinCubic LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O
variable {α β ι:Type*} [Fintype α] [Fintype β] [Fintype ι]

def residualLabelVia (E:α⊕β≃ι) (e:β→Fin 3) : ι→Fin 3 :=
  residualZeroLabel e ∘ E.symm

omit [Fintype α] [Fintype β] [Fintype ι] in
lemma residualLabelVia_apply (E:α⊕β≃ι) (e:β→Fin 3) (i:α⊕β) :
    residualLabelVia E e (E i)=residualZeroLabel e i := by
  simp only [residualLabelVia,Function.comp_apply,Equiv.symm_apply_apply]

theorem sum_labels_drop_residual_equiv (E:α⊕β≃ι) (f:(ι→Fin 3)→ℂ)
    (hzero:∀e,(∃i:α,e (E (Sum.inl i))≠0)→f e=0) :
    (∑e:ι→Fin 3,f e)=∑e:β→Fin 3,f (residualLabelVia E e) := by
  let e:=Equiv.arrowCongr E (Equiv.refl (Fin 3))
  rw [←e.sum_comp f]
  apply sum_labels_drop_residual
  intro l hl
  apply hzero
  obtain ⟨i,hi⟩:=hl
  refine ⟨i,?_⟩
  simpa only [e,Equiv.arrowCongr_apply,Function.comp_apply,Equiv.refl_apply,Equiv.symm_apply_apply] using hi

omit [Fintype α] [Fintype β] in
lemma reflectedBranch_residual_zero_equiv (E:α⊕β≃ι)
    (P:ι→Ideal Eis) [∀i,(P i).IsMaximal] (hg:∀i,lambda∉P i)
    (j:ι→ℕ) (hj:∀i:α,j (E (Sum.inl i))=1)
    (e:ι→Fin 3) (hbad:∃i:α,e (E (Sum.inl i))≠0) (n b:Eis) :
    reflectedBranch P hg j e n b=0 := by
  obtain ⟨i,hi⟩:=hbad
  unfold reflectedBranch
  apply Finset.prod_eq_zero (Finset.mem_univ (E (Sum.inl i)))
  simp only [reflectedLocalPiece,hj,show (1:ℕ)≠4 by decide,ite_false,if_neg hi]

lemma reflectionExtractedDivisor_drop_residual_equiv (E:α⊕β≃ι)
    (P:ι→Ideal Eis) (j:ι→ℕ) (hj:∀i:α,j (E (Sum.inl i))=1)
    (e:β→Fin 3) (v:Fin 3) :
    reflectionExtractedDivisor P j (residualLabelVia E e) v=
      reflectionExtractedDivisor (fun i:β=>P (E (Sum.inr i))) (fun i=>j (E (Sum.inr i))) e v := by
  calc
    _=reflectionExtractedDivisor (fun i=>P (E i)) (fun i=>j (E i)) (residualZeroLabel e) v := by
      unfold reflectionExtractedDivisor
      rw [←E.prod_comp]
      apply Finset.prod_congr rfl
      intro i hi
      rw [residualLabelVia_apply]
    _=_:=reflectionExtractedDivisor_drop_residual _ _ hj _ _

lemma reflectedBranch_drop_residual_equiv (E:α⊕β≃ι)
    (P:ι→Ideal Eis) [∀i,(P i).IsMaximal] (hg:∀i,lambda∉P i)
    (j:ι→ℕ) (hj:∀i:α,j (E (Sum.inl i))=1)
    (e:β→Fin 3) (n b:Eis) :
    reflectedBranch P hg j (residualLabelVia E e) n b=
      (∏i:α,bracket (actualSextic (P (E (Sum.inl i))) (hg (E (Sum.inl i)))) 1
        (Ideal.Quotient.mk _ (n*b^3)))*
      reflectedBranch (fun i:β=>P (E (Sum.inr i))) (fun i=>hg (E (Sum.inr i)))
        (fun i=>j (E (Sum.inr i))) e n b := by
  calc
    _=reflectedBranch (fun i=>P (E i)) (fun i=>hg (E i)) (fun i=>j (E i)) (residualZeroLabel e) n b := by
      unfold reflectedBranch
      rw [←E.prod_comp]
      apply Finset.prod_congr rfl
      intro i hi
      rw [residualLabelVia_apply]
    _=_:=reflectedBranch_drop_residual _ _ _ hj _ _ _

end CompletedGauss

end

end OAI

end


