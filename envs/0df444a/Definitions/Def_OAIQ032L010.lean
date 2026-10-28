-- Prove2me | Definitions.Def_OAIQ032L010
-- name    : OAIQ032L010
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T19:46:36.663956+00:00
-- url     : https://prove2.me/theorems/689efe08-b74f-46e4-b3a3-111afd4ab568
-- title:
--   Definitions bundle OAIQ032L010 of the split of OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 94 declarations of OpenAI's Lean: 26 definitions, 1 instance and 67 theorems. The definitions and types are `OAI.Lech.AlternatingCech.augmentationShortComplex`, `OAI.Lech.AlternatingCech.cochainsSorted`, `OAI.Lech.AlternatingCech.cochainsSortedIso`, `OAI.Lech.AlternatingCech.complex`, `OAI.Lech.AlternatingCech.complexMap`, `OAI.Lech.AlternatingCech.complexSequence`, `OAI.Lech.AlternatingCech.delta`, `OAI.Lech.AlternatingCech.differential`, `OAI.Lech.AlternatingCech.extra`, `OAI.Lech.AlternatingCech.post`, `OAI.Lech.AlternatingCech.prism`, `OAI.Lech.AlternatingCech.pullback`, `OAI.Lech.AlternatingCech.rawDelta`, `OAI.Lech.AlternatingCech.sortedComplex`, `OAI.Lech.AlternatingCech.sortedFamilyEquiv`, `OAI.Lech.AlternatingCech.sortedFamilyIso`, `OAI.Lech.AlternatingCech.sortedUnaugmentedFamilyIso`, `OAI.Lech.AlternatingCech.sortedZeroEquiv`, `OAI.Lech.AlternatingCech.unaugmentedComplex`, `OAI.Lech.AlternatingCech.unaugmented_homology_one`, `OAI.Lech.AlternatingCech.vertexMap`, `OAI.Lech.ArbitraryCoefficientField.quotientSectionData`, `OAI.Lech.ArbitraryCoefficientField.sectionMap`, `OAI.Lech.ArbitraryCoefficientField.stage`, `OAI.Lech.FiniteCoverCech.delta`, `OAI.Lech.FiniteCoverCech.extra`.
--
--   **Sources.** They come from these modules of lean/OAI/RingTheory/Multiplicity, in whole or in part: `Multiplicity_AlternatingCechAlt`, `Multiplicity_AlternatingCechPost`, `Multiplicity_AlternatingCechUnaugmentedComplex`, `Multiplicity_ArbitraryCoefficientField`, `Multiplicity_FilteredFractionReesDenominatorTheory`, `Multiplicity_LechConnectingIso`, `Multiplicity_LechSignedUnit`, `Multiplicity_ProductSourceCoverAllowedEmpty`, `Multiplicity_ProductSourceCoverFaceSlice`, `Multiplicity_ProductSourceCoverHighThreshold`.
--
--   **Imports.** It imports the bundles `OAIQ032L000` and `OAIQ032L001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ032L019` and `OAIQ032L021`.
-- source:
--   OpenAI, Lech's multiplicity conjecture (result family 194), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 194; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Lechs-multiplicity-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RingTheory/Multiplicity at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ032L000
import Definitions.Def_OAIQ032L001

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FilteredFractionReesDenominatorTheory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian

open scoped BigOperators


namespace Lech.FiniteCoverCech
open scoped BigOperators
universe u v w
variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
variable {ι : Type w}

def delta (n : ℕ) : Row M (ι := ι) n →ₗ[R] Row M (ι := ι) (n+1) where
  toFun f a := ∑ i : Fin (n+1),(-1:R)^i.val • f (a ∘ i.succAbove)
  map_add' _ _ := by ext a;simp only [Pi.add_apply,smul_add,Finset.sum_add_distrib]
  map_smul' r f := by
    ext a
    simp only [Pi.smul_apply,RingHom.id_apply,Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact smul_comm _ _ _
def extra (j : ι) (n : ℕ) : Row M (ι := ι) (n+1) →ₗ[R] Row M (ι := ι) n where
  toFun f a := f (Fin.cons j a)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
lemma extra_delta (j : ι) (n : ℕ) (f : Row M (ι := ι) (n+1)) :
    extra R M j (n+1) (delta R M (n+1) f)+delta R M n (extra R M j n f)=f := by
  ext a
  change (∑ i : Fin (n+2),(-1:R)^i.val • f (Fin.cons j a ∘ i.succAbove))+
    (∑ i : Fin (n+1),(-1:R)^i.val • f (Fin.cons j (a ∘ i.succAbove)))=f a
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero,pow_zero,one_smul,delete_insert_zero,Fin.val_succ,
    pow_succ,delete_insert_succ,mul_neg_one,neg_smul,Finset.sum_neg_distrib]
  abel
lemma delta_square (n : ℕ) (f : Row M (ι := ι) n) : delta R M (n+1) (delta R M n f)=0 := by
  induction n with
  | zero =>
    ext a
    have hf (b : Fin 0 → ι) : f b=f Fin.elim0 := congrArg f (Subsingleton.elim _ _)
    simp [delta,Fin.sum_univ_two,hf]
  | succ n ih =>
    have hh (j : ι) : extra R M j (n+2) (delta R M (n+2) (delta R M (n+1) f))=0 := by
      have h₁ := extra_delta R M j (n+1) (delta R M (n+1) f)
      have h₂ := congrArg (delta R M (n+1)) (extra_delta R M j n f)
      rw [map_add,ih,add_zero] at h₂
      rw [h₂] at h₁
      exact add_right_cancel (h₁.trans (zero_add _).symm)
    ext a
    have he := congrFun (hh (a 0)) (fun i => a i.succ)
    change delta R M (n+2) (delta R M (n+1) f) (Fin.cons (a 0) (Fin.tail a))=0 at he
    rw [Fin.cons_self_tail] at he
    exact he

variable [Fintype ι] [DecidableEq ι]
omit [Fintype ι] in
lemma intersection_cons {n : ℕ} (j : ι) (a : Fin n → ι) :
    intersection (Fin.cons j a)=insert j (intersection a) := by
  ext i
  simp only [intersection,Finset.mem_image,Finset.mem_univ,true_and,Finset.mem_insert]
  constructor
  · rintro ⟨k,hk⟩
    revert hk
    refine Fin.cases ?_ (fun k => ?_) k
    · intro hk;left;exact hk.symm
    · intro hk;right;exact ⟨k,hk⟩
  · rintro (rfl|⟨k,rfl⟩)
    · exact ⟨0,Fin.cons_zero _ _⟩
    · exact ⟨k.succ,Fin.cons_succ _ _ _⟩
variable (F : Finset ι → Submodule R M) (hF : Monotone F)
include hF in
omit [Fintype ι] in
lemma delta_mem (n : ℕ) {f : Row M (ι := ι) n} (hf : f∈cochains R M F n) :
    delta R M n f∈cochains R M F (n+1) := by
  intro a
  change (∑ i : Fin (n+1),(-1:R)^i.val • f (a ∘ i.succAbove))∈F (intersection a)
  apply (F _).sum_mem
  intro i _
  exact (F _).smul_mem _ (hF (intersection_delete a i) (hf _))
end Lech.FiniteCoverCech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_AlternatingCechAlt
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open scoped BigOperators
namespace Lech.AlternatingCech
open scoped BigOperators
universe u v w
variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
variable {ι : Type w} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι] in
lemma evaluation_injective (n : ℕ) : Function.Injective (evaluation R M (ι := ι) n) := by
  intro f g h
  apply (basis R (ι := ι)).ext_alternating
  intro a _
  exact congrFun h a

def delta (n : ℕ) : Alt R M (ι := ι) n →ₗ[R] Alt R M (ι := ι) (n+1) where
  toFun f := AlternatingMap.alternatizeUncurryFin ((epsilon R).smulRight f)
  map_add' f g := by
    ext v
    simp [AlternatingMap.alternatizeUncurryFin_apply,smul_add,Finset.sum_add_distrib]
  map_smul' r f := by
    ext v
    simp only [AlternatingMap.alternatizeUncurryFin_apply,LinearMap.smulRight_apply,
      AlternatingMap.smul_apply,RingHom.id_apply,Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [smul_comm (epsilon R (v i)) r,smul_comm ((-1:ℤ)^i.val) r]
lemma evaluation_delta (n : ℕ) (f : Alt R M (ι := ι) n) :
    evaluation R M (n+1) (delta R M n f)=FiniteCoverCech.delta R M n (evaluation R M n f) := by
  ext a
  simp only [evaluation,LinearMap.coe_mk,AddHom.coe_mk,delta,
    AlternatingMap.alternatizeUncurryFin_apply,LinearMap.smulRight_apply,
    epsilon_basis,one_smul,FiniteCoverCech.delta]
  apply Finset.sum_congr rfl
  intro i _
  rw [←Int.cast_smul_eq_zsmul R]
  simp only [Int.cast_pow,Int.cast_neg,Int.cast_one]
  rfl

def extra (j : ι) (n : ℕ) : Alt R M (ι := ι) (n+1) →ₗ[R] Alt R M (ι := ι) n where
  toFun f := f.curryLeft (basis R j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
omit [DecidableEq ι] in
lemma evaluation_extra (j : ι) (n : ℕ) (f : Alt R M (ι := ι) (n+1)) :
    evaluation R M n (extra R M j n f)=FiniteCoverCech.extra R M j n (evaluation R M (n+1) f) := by
  ext a
  change f (Fin.cons (basis R j) (fun i => basis R (a i)))=
    f (fun i => basis R ((Fin.cons j a : Fin (n+1) → ι) i))
  congr 1
  funext i
  exact Fin.cases rfl (fun _ => rfl) i
lemma delta_square (n : ℕ) (f : Alt R M (ι := ι) n) : delta R M (n+1) (delta R M n f)=0 := by
  apply evaluation_injective R M (n+2)
  rw [evaluation_delta,evaluation_delta,map_zero,FiniteCoverCech.delta_square]
lemma extra_delta (j : ι) (n : ℕ) (f : Alt R M (ι := ι) (n+1)) :
    extra R M j (n+1) (delta R M (n+1) f)+delta R M n (extra R M j n f)=f := by
  apply evaluation_injective R M (n+1)
  rw [map_add,evaluation_extra,evaluation_delta,evaluation_delta,evaluation_extra]
  exact FiniteCoverCech.extra_delta R M j n (evaluation R M (n+1) f)

variable (F : Finset ι → Submodule R M) (hF : Monotone F)
include hF in
lemma delta_mem (n : ℕ) {f : Alt R M (ι := ι) n} (hf : f∈cochains R M F n) :
    delta R M n f∈cochains R M F (n+1) := by
  change evaluation R M (n+1) (delta R M n f)∈FiniteCoverCech.cochains R M F (n+1)
  rw [evaluation_delta]
  exact FiniteCoverCech.delta_mem R M F hF n hf
end Lech.AlternatingCech


namespace Lech.AlternatingCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped BigOperators
universe u
variable (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (F : Finset ι → Submodule R M) (hF : Monotone F)
def differential (n : ℕ) : cochains R M F n →ₗ[R] cochains R M F (n+1) :=
  (delta R M n).restrict (fun _ h => delta_mem R M F hF n h)
lemma differential_square (n : ℕ) (f : cochains R M F n) :
    differential R M F hF (n+1) (differential R M F hF n f)=0 := by
  apply Subtype.ext
  exact delta_square R M n f.val
 

def complex : CochainComplex (ModuleCat.{u} R) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of R (cochains R M F n))
    (fun n => ModuleCat.ofHom (differential R M F hF n)) (fun n => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      exact differential_square R M F hF n f)
lemma complex_d (n : ℕ) : (complex R M F hF).d n (n+1)=
    ModuleCat.ofHom (differential R M F hF n) := by
  change CochainComplex.of.d (fun n => ModuleCat.of R (cochains R M F n))
    (fun n => ModuleCat.ofHom (differential R M F hF n)) n (n+1)=_
  exact CochainComplex.of_d _ _ n
variable (q : ι → R) (hq : Ideal.span (Set.range q)=⊤)
variable (hclear : ∀ (s : Finset ι) (j : ι) (x : M),x∈F (insert j s) → ∃ N : ℕ,q j^N • x∈F s)
omit [DecidableEq ι] in
lemma extra_delta_zero (j : ι) (f : Alt R M (ι := ι) 0) :
    extra R M j 0 (delta R M 0 f)=f := by
  classical
  ext v
  change AlternatingMap.alternatizeUncurryFin ((epsilon R).smulRight f)
    (Fin.cons (basis R j) v)=f v
  simp [AlternatingMap.alternatizeUncurryFin_apply]
  change (epsilon R) (basis R j) • f v = f v
  rw [epsilon_basis,one_smul]
end Lech.AlternatingCech


namespace Lech.AlternatingCech
open scoped BigOperators
open Set
universe u v w
variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
variable {ι : Type w} [Fintype ι] [LinearOrder ι]

omit [Fintype ι] in
lemma tuple_sort {n : ℕ} (a : Fin n → ι) (ha : Function.Injective a) :
    ∃ s : powersetCard ι n,∃ σ : Equiv.Perm (Fin n),
      FiniteCoverCech.intersection a=s.val ∧ a=(s.val.orderEmbOfFin s.property) ∘ σ := by
  let s : powersetCard ι n := ⟨FiniteCoverCech.intersection a,by
    change (FiniteCoverCech.intersection a).card=n
    rw [FiniteCoverCech.intersection,Finset.card_image_of_injective _ ha,Finset.card_univ,Fintype.card_fin]⟩
  let e : Fin n ≃ s.val := Equiv.ofBijective
    (fun i => ⟨a i,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩)
    ⟨fun i j h => ha (congrArg Subtype.val h),by
      intro j
      obtain ⟨i,_,hi⟩ := Finset.mem_image.mp j.property
      exact ⟨i,Subtype.ext hi⟩⟩
  let σ : Equiv.Perm (Fin n) := e.trans (s.val.orderIsoOfFin s.property).symm.toEquiv
  refine ⟨s,σ,rfl,?_⟩
  funext i
  change a i = ((s.val.orderIsoOfFin s.property) ((s.val.orderIsoOfFin s.property).symm (e i))).val
  rw [OrderIso.apply_symm_apply]
  rfl
omit [Fintype ι] in
lemma sorted_intersection (n : ℕ) (s : powersetCard ι n) :
    FiniteCoverCech.intersection (s.val.orderEmbOfFin s.property)=s.val := by
  ext i
  simp only [FiniteCoverCech.intersection,Finset.mem_image,Finset.mem_univ,true_and]
  change (∃ j, s.val.orderEmbOfFin s.property j=i) ↔ _
  change i∈Set.range (s.val.orderEmbOfFin s.property) ↔ i∈s.val
  exact Iff.of_eq (congrArg (fun S : Set ι => i∈S) (Finset.range_orderEmbOfFin s.val s.property))

variable (F : Finset ι → Submodule R M)
lemma mem_cochains_iff_sorted (n : ℕ) (f : Alt R M (ι := ι) n) :
    f∈cochains R M F n ↔ ∀ s : powersetCard ι n,sortedCoordinates R M n f s∈F s.val := by
  constructor
  · intro hf s
    rw [sortedCoordinates_apply]
    have h := hf (s.val.orderEmbOfFin s.property)
    rw [sorted_intersection] at h
    exact h
  · intro hf a
    by_cases ha : Function.Injective a
    · obtain ⟨s,σ,hs,hσ⟩ := tuple_sort a ha
      change f (fun i => basis R (a i))∈F (FiniteCoverCech.intersection a)
      rw [hs,hσ]
      change f ((fun i => basis R (s.val.orderEmbOfFin s.property i)) ∘ σ)∈F s.val
      rw [f.map_perm]
      have hh := hf s
      rw [sortedCoordinates_apply] at hh
      change ((Equiv.Perm.sign σ : ℤ) • f (fun i => basis R (s.val.orderEmbOfFin s.property i)))∈F s.val
      rw [←Int.cast_smul_eq_zsmul R]
      exact (F s.val).smul_mem _ hh
    · change f (fun i => basis R (a i))∈F (FiniteCoverCech.intersection a)
      rw [f.map_eq_zero_of_not_injective _ (fun hh => ha (fun i j hij => hh (congrArg (basis R) hij)))]
      exact (F _).zero_mem
 

def cochainsSorted (n : ℕ) : cochains R M F n ≃ₗ[R] (∀ s : powersetCard ι n,F s.val) where
  toFun f s := ⟨sortedCoordinates R M n f.val s,(mem_cochains_iff_sorted R M F n f.val).mp f.property s⟩
  invFun f := ⟨(sortedCoordinates R M n).symm (fun s => (f s).val),
    (mem_cochains_iff_sorted R M F n _).mpr (by
      intro s
      simpa only [LinearEquiv.apply_symm_apply] using (f s).property)⟩
  left_inv f := Subtype.ext ((sortedCoordinates R M n).symm_apply_apply f.val)
  right_inv f := by ext s; exact congrFun ((sortedCoordinates R M n).apply_symm_apply (fun s => (f s).val)) s
  map_add' f g := by
    ext s
    exact congrFun ((sortedCoordinates R M n).map_add f.val g.val) s
  map_smul' r f := by
    ext s
    exact congrFun ((sortedCoordinates R M n).map_smul r f.val) s
end Lech.AlternatingCech


namespace Lech.AlternatingCech
open Set
open scoped BigOperators
universe u
variable (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M]
variable {ι : Type} [Fintype ι] [LinearOrder ι]
def vertexMap (τ : ι → ι) : (ι → R) →ₗ[R] (ι → R) :=
  (basis R).constr R (fun i => basis R (τ i))
omit [LinearOrder ι] in
lemma vertexMap_basis (τ : ι → ι) (i : ι) : vertexMap R τ (basis R i)=basis R (τ i) := by
  simp [vertexMap]
def pullback (τ : ι → ι) (p : ℕ) : Alt R M (ι:=ι) p →ₗ[R] Alt R M (ι:=ι) p where
  toFun f := f.compLinearMap (vertexMap R τ)
  map_add' f g := by ext v;rfl
  map_smul' r f := by ext v;rfl
omit [LinearOrder ι] in
lemma pullback_eval (τ : ι → ι) (p : ℕ) (f : Alt R M (ι:=ι) p) (a : Fin p → ι) :
    evaluation R M p (pullback R M τ p f) a = evaluation R M p f (τ ∘ a) := by
  change f (fun i => vertexMap R τ (basis R (a i)))=f (fun i => basis R (τ (a i)))
  simp only [vertexMap_basis]
omit [LinearOrder ι] in
lemma pullback_delta (τ : ι → ι) (p : ℕ) (f : Alt R M (ι:=ι) p) :
    pullback R M τ (p+1) (delta R M p f)=delta R M p (pullback R M τ p f) := by
  apply evaluation_injective R M (p+1)
  ext a
  rw [pullback_eval,evaluation_delta,evaluation_delta]
  simp only [FiniteCoverCech.delta,LinearMap.coe_mk,AddHom.coe_mk]
  apply Finset.sum_congr rfl
  intro i _
  rw [pullback_eval]
  rfl
 

def prism (τ : ι → ι) : (p : ℕ) → Alt R M (ι:=ι) (p+1) →ₗ[R] Alt R M (ι:=ι) p
  | 0 => 0
  | p+1 =>
    (sortedCoordinates R M (p+1)).symm.toLinearMap.comp
      (LinearMap.pi (fun s : powersetCard ι (p+1) =>
        let c := τ (s.val.orderEmbOfFin s.property 0)
        (LinearMap.proj s).comp ((sortedCoordinates R M (p+1)).toLinearMap.comp
          ((extra R M c (p+1)) - (delta R M p).comp ((prism τ p).comp (extra R M c (p+1)))))))
lemma prism_succ (τ : ι → ι) (p : ℕ) (f : Alt R M (ι:=ι) (p+2)) (s : powersetCard ι (p+1)) :
    sortedCoordinates R M (p+1) (prism R M τ (p+1) f) s =
    let c := τ (s.val.orderEmbOfFin s.property 0)
    sortedCoordinates R M (p+1) (extra R M c (p+1) f - delta R M p (prism R M τ p (extra R M c (p+1) f))) s := by
  change (sortedCoordinates R M (p+1)) ((sortedCoordinates R M (p+1)).symm _) s=_
  rw [LinearEquiv.apply_symm_apply]
  rfl
omit [LinearOrder ι] in
lemma pullback_zero (τ : ι → ι) (f : Alt R M (ι:=ι) 0) : pullback R M τ 0 f=f := by
  ext v
  change f _=f v
  congr 1
  exact Subsingleton.elim _ _
lemma pullback_extra_sorted_zero (τ : ι → ι) (p : ℕ) (f : Alt R M (ι:=ι) (p+2))
    (s : powersetCard ι (p+1)) :
    sortedCoordinates R M (p+1)
      (pullback R M τ (p+1) (extra R M (τ (s.val.orderEmbOfFin s.property 0)) (p+1) f)) s=0 := by
  rw [sortedCoordinates_apply]
  change evaluation R M (p+1)
    (pullback R M τ (p+1) (extra R M (τ (s.val.orderEmbOfFin s.property 0)) (p+1) f))
    (s.val.orderEmbOfFin s.property)=0
  rw [pullback_eval,evaluation_extra]
  let a : Fin (p+1) → ι := s.val.orderEmbOfFin s.property
  change f (fun i => basis R ((Fin.cons (τ (a 0)) (τ ∘ a) : Fin (p+2) → ι) i))=0
  apply f.map_eq_zero_of_eq (i:=0) (j:=Fin.succ 0)
  · rfl
  · exact (Fin.succ_ne_zero (0 : Fin (p+1))).symm
lemma prism_identity_step (τ : ι → ι) (p : ℕ)
    (h : ∀ g : Alt R M (ι:=ι) p,
      delta R M p (prism R M τ p (delta R M p g))=
        delta R M p g-pullback R M τ (p+1) (delta R M p g))
    (f : Alt R M (ι:=ι) (p+1)) :
    prism R M τ (p+1) (delta R M (p+1) f)+delta R M p (prism R M τ p f)=
      f-pullback R M τ (p+1) f := by
  apply (sortedCoordinates R M (p+1)).injective
  ext s
  rw [map_add,Pi.add_apply,prism_succ]
  let c := τ (s.val.orderEmbOfFin s.property 0)
  let g := extra R M c p f
  have he : extra R M c (p+1) (delta R M (p+1) f)=f-delta R M p g :=
    eq_sub_iff_add_eq.mpr (extra_delta R M c p f)
  have hp : pullback R M τ (p+1) (delta R M p g)=
      pullback R M τ (p+1) f - pullback R M τ (p+1) (extra R M c (p+1) (delta R M (p+1) f)) := by
    rw [he,map_sub]
    abel
  have hh : extra R M c (p+1) (delta R M (p+1) f)-
      delta R M p (prism R M τ p (extra R M c (p+1) (delta R M (p+1) f)))+
      delta R M p (prism R M τ p f)=
      f-pullback R M τ (p+1) f+
        pullback R M τ (p+1) (extra R M c (p+1) (delta R M (p+1) f)) := by
    rw [he,map_sub,map_sub,h g,hp,he]
    abel
  have hs := congrArg (fun z => sortedCoordinates R M (p+1) z s) hh
  simpa only [c,map_add,Pi.add_apply,pullback_extra_sorted_zero,add_zero] using hs
 

lemma prism_identity (τ : ι → ι) (p : ℕ) (f : Alt R M (ι:=ι) (p+1)) :
    prism R M τ (p+1) (delta R M (p+1) f)+delta R M p (prism R M τ p f)=
      f-pullback R M τ (p+1) f := by
  induction p with
  | zero =>
    apply prism_identity_step
    intro g
    rw [prism,LinearMap.zero_apply,map_zero,pullback_delta,pullback_zero,sub_self]
  | succ p ih =>
    apply prism_identity_step
    intro g
    have hi := congrArg (delta R M (p+1)) (ih g)
    rw [map_add,delta_square,add_zero,map_sub,←pullback_delta] at hi
    exact hi


lemma sortedCoordinates_eq_evaluation (p : ℕ) (f : Alt R M (ι:=ι) p) (s : powersetCard ι p) :
    sortedCoordinates R M p f s=evaluation R M p f (s.val.orderEmbOfFin s.property) :=
  sortedCoordinates_apply R M p f s
lemma evaluation_mem_of_sorted (T : Finset ι) (P : Submodule R M) (p : ℕ) (f : Alt R M (ι:=ι) p)
    (hf : ∀ s : powersetCard ι p,s.val⊆T → sortedCoordinates R M p f s∈P)
    (a : Fin p → ι) (ha : ∀ i,a i∈T) : evaluation R M p f a∈P := by
  let F : Finset ι → Submodule R M := fun s => if s⊆T then P else ⊤
  have hh : f∈cochains R M F p := (mem_cochains_iff_sorted R M F p f).mpr (by
    intro s
    by_cases hs : s.val⊆T
    · simpa only [F,ite_eq_left hs] using hf s hs
    · simp only [F,ite_eq_right hs,Submodule.mem_top])
  have hs : FiniteCoverCech.intersection a⊆T := by
    intro i hi
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hi
    exact ha j
  simpa only [F,ite_eq_left hs] using hh a
 

lemma prism_local (τ : ι → ι) (T : Finset ι) (hT : ∀ i∈T,τ i∈T)
    (P : Submodule R M) (p : ℕ) (f : Alt R M (ι:=ι) (p+1))
    (hf : ∀ a : Fin (p+1) → ι,(∀ i,a i∈T) → evaluation R M (p+1) f a∈P)
    (a : Fin p → ι) (ha : ∀ i,a i∈T) : evaluation R M p (prism R M τ p f) a∈P := by
  induction p with
  | zero => simpa only [prism,LinearMap.zero_apply,map_zero,Pi.zero_apply] using P.zero_mem
  | succ p ih =>
    apply evaluation_mem_of_sorted R M T P (p+1) _ ?_ a ha
    intro s hs
    let c := τ (s.val.orderEmbOfFin s.property 0)
    rw [prism_succ]
    change sortedCoordinates R M (p+1)
      (extra R M c (p+1) f-delta R M p (prism R M τ p (extra R M c (p+1) f))) s∈P
    rw [map_sub,Pi.sub_apply]
    have hc : c∈T := hT _ (hs (s.val.orderEmbOfFin_mem s.property 0))
    have hextra : ∀ b : Fin (p+1) → ι,(∀ i,b i∈T) →
        evaluation R M (p+1) (extra R M c (p+1) f) b∈P := by
      intro b hb
      rw [evaluation_extra]
      change evaluation R M (p+2) f (Fin.cons c b)∈P
      apply hf
      intro i
      exact Fin.cases hc (fun i => hb i) i
    apply P.sub_mem
    · rw [sortedCoordinates_eq_evaluation]
      exact hextra _ (fun i => hs (s.val.orderEmbOfFin_mem s.property i))
    · rw [sortedCoordinates_eq_evaluation,evaluation_delta]
      change (∑ i : Fin (p+1),(-1:R)^i.val •
        evaluation R M p (prism R M τ p (extra R M c (p+1) f))
          ((s.val.orderEmbOfFin s.property) ∘ i.succAbove))∈P
      apply P.sum_mem
      intro i _
      apply P.smul_mem
      apply ih (extra R M c (p+1) f) hextra
      intro j
      exact hs (s.val.orderEmbOfFin_mem s.property (i.succAbove j))


end Lech.AlternatingCech
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_AlternatingCechPost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option synthInstance.maxHeartbeats 200000
namespace OAI

section
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open scoped BigOperators
namespace Lech.AlternatingCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped BigOperators
universe u
variable (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
def post (n : ℕ) (P : M →ₗ[R] M) : Alt R M (ι:=ι) n →ₗ[R] Alt R M (ι:=ι) n where
  toFun f := P.compAlternatingMap f
  map_add' _ _ := by ext v;exact P.map_add _ _
  map_smul' r f := by ext v;exact P.map_smul r (f v)
omit [DecidableEq ι] in
lemma evaluation_post (n : ℕ) (P : M →ₗ[R] M) (f : Alt R M (ι:=ι) n) (a : Fin n → ι) :
    evaluation R M n (post R M n P f) a=P (evaluation R M n f a) := rfl
lemma delta_post (n : ℕ) (P : M →ₗ[R] M) (f : Alt R M (ι:=ι) n) :
    delta R M n (post R M n P f)=post R M (n+1) P (delta R M n f) := by
  apply evaluation_injective R M (n+1)
  ext a
  rw [evaluation_delta,evaluation_post,evaluation_delta]
  change (∑ i : Fin (n+1),(-1:R)^i.val • evaluation R M n (post R M n P f) (a ∘ i.succAbove)) =
    P (∑ i : Fin (n+1),(-1:R)^i.val • evaluation R M n f (a ∘ i.succAbove))
  simp only [map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro i _
  rw [evaluation_post]
variable (F : Finset ι → Submodule R M) (hF : Monotone F)
variable (P : ι → M →ₗ[R] M) (hP : ∀ x,∑ j,P j x=x)
  (hmem : ∀ s j x,x∈F (insert j s) → P j x∈F s)
include hP hmem in
 

lemma projection_exact (n : ℕ) (f : cochains R M F (n+1)) (hf : delta R M (n+1) f.val=0) :
    ∃ g : cochains R M F n,delta R M n g.val=f.val := by
  let g : Alt R M (ι:=ι) n := ∑ j,post R M n (P j) (extra R M j n f.val)
  have hg : g∈cochains R M F n := by
    intro a
    change evaluation R M n g a∈F (FiniteCoverCech.intersection a)
    simp only [g,map_sum,Finset.sum_apply,evaluation_post,evaluation_extra]
    apply (F _).sum_mem
    intro j _
    apply hmem _ j _
    have hj := f.property (Fin.cons j a)
    change evaluation R M (n+1) f.val (Fin.cons j a) ∈ F _
    simpa only [FiniteCoverCech.intersection_cons] using hj
  refine ⟨⟨g,hg⟩,?_⟩
  have hj (j : ι) : delta R M n (extra R M j n f.val)=f.val := by
    have h := extra_delta R M j n f.val
    rw [hf,map_zero,zero_add] at h
    exact h
  simp only [g,map_sum,delta_post,hj]
  apply evaluation_injective R M (n+1)
  ext a
  simp only [map_sum,Finset.sum_apply,evaluation_post]
  exact hP _
include hP hmem in
lemma projection_complex_exactAt (n : ℕ) : (complex R M F hF).ExactAt (n+1) := by
  apply ((complex R M F hF).exactAt_iff' (i:=n) (j:=n+1) (k:=n+2) (by simp) (by simp)).mpr
  rw [ShortComplex.moduleCat_exact_iff]
  intro f hf
  change ((complex R M F hF).d (n+1) (n+2)).hom f=0 at hf
  rw [complex_d] at hf
  obtain ⟨g,hg⟩ := projection_exact R M F P hP hmem n f (congrArg Subtype.val hf)
  refine ⟨g,?_⟩
  change ((complex R M F hF).d n (n+1)).hom g=f
  rw [complex_d]
  exact Subtype.ext hg
lemma complex_exactAt_zero_of_nonempty [Nonempty ι] : (complex R M F hF).ExactAt 0 := by
  apply ((complex R M F hF).exactAt_iff' (i:=0) (j:=0) (k:=1) (by simp) (by simp)).mpr
  rw [ShortComplex.moduleCat_exact_iff]
  intro f hf
  change ((complex R M F hF).d 0 1).hom f=0 at hf
  rw [complex_d] at hf
  have hδ : delta R M 0 f.val=0 := congrArg Subtype.val hf
  have h := extra_delta_zero R M (Classical.choice (inferInstance : Nonempty ι)) f.val
  rw [hδ,map_zero] at h
  have hf0 : f=0 := Subtype.ext h.symm
  exact ⟨0,by simp [hf0]⟩
include hP hmem in
lemma projection_complex_acyclic [Nonempty ι] : (complex R M F hF).Acyclic := by
  intro n
  cases n with
  | zero => exact complex_exactAt_zero_of_nonempty R M F hF
  | succ n => exact projection_complex_exactAt R M F hF P hP hmem n
end Lech.AlternatingCech


namespace Lech.AlternatingCech
open Set CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped BigOperators
universe u
variable (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M]
variable {ι : Type} [Fintype ι] [LinearOrder ι]
lemma post_prism_mem (τ : ι → ι) (hτ : ∀ i,τ (τ i)=τ i) (P : M →ₗ[R] M)
    (F : Finset ι → Submodule R M) (hF : Monotone F)
    (hcarrier : ∀ s x,x∈F (s∪s.image τ) → P x∈F s) (p : ℕ)
    (f : Alt R M (ι:=ι) (p+1)) (hf : f∈cochains R M F (p+1)) :
    post R M p P (prism R M τ p f)∈cochains R M F p := by
  apply (mem_cochains_iff_sorted R M F p _).mpr
  intro s
  rw [sortedCoordinates_eq_evaluation,evaluation_post]
  change evaluation R M p (prism R M τ p f) (s.val.orderEmbOfFin s.property)∈(F s.val).comap P
  have hstable : ∀ i∈s.val∪s.val.image τ,τ i∈s.val∪s.val.image τ := by
    intro i hi
    rcases Finset.mem_union.mp hi with hi|hi
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,hi,rfl⟩)
    · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hi
      rw [hτ]
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j,hj,rfl⟩)
  apply prism_local R M τ (s.val∪s.val.image τ) hstable ((F s.val).comap P) p f
  · intro a ha
    apply hcarrier s.val
    apply hF ?_ (hf a)
    intro i hi
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hi
    exact ha j
  · intro i
    exact Finset.mem_union_left _ (s.val.orderEmbOfFin_mem s.property i)
omit [LinearOrder ι] in
lemma post_pullback_zero (τ : ι → ι) (P : M →ₗ[R] M)
    (F : Finset ι → Submodule R M)
    (hzero : ∀ (s : Finset ι) x,x∈F (s.image τ) → P x=0) (p : ℕ)
    (f : Alt R M (ι:=ι) p) (hf : f∈cochains R M F p) :
    post R M p P (pullback R M τ p f)=0 := by
  apply evaluation_injective R M p
  ext a
  rw [evaluation_post,pullback_eval,map_zero,Pi.zero_apply]
  apply hzero (FiniteCoverCech.intersection a)
  have h := hf (τ ∘ a)
  have he : FiniteCoverCech.intersection (τ ∘ a)=(FiniteCoverCech.intersection a).image τ := by
    simp only [FiniteCoverCech.intersection,Finset.image_image,Function.comp_def]
  simpa only [he] using h
variable {κ : Type} [Fintype κ]
variable (F : Finset ι → Submodule R M) (hF : Monotone F)
variable (P : κ → M →ₗ[R] M) (hP : ∀ x,∑ j,P j x=x)
  (τ : κ → ι → ι) (hτ : ∀ j i,τ j (τ j i)=τ j i)
  (hcarrier : ∀ s j x,x∈F (s∪s.image (τ j)) → P j x∈F s)
  (hzero : ∀ (s : Finset ι) j x,x∈F (s.image (τ j)) → P j x=0)
include hF hP hτ hcarrier hzero in
 

lemma projection_prism_exact (p : ℕ) (f : cochains R M F (p+1)) (hf : delta R M (p+1) f.val=0) :
    ∃ g : cochains R M F p,delta R M p g.val=f.val := by
  let g : Alt R M (ι:=ι) p := ∑ j,post R M p (P j) (prism R M (τ j) p f.val)
  have hg : g∈cochains R M F p :=
    (cochains R M F p).sum_mem (fun j _ => post_prism_mem R M (τ j) (hτ j) (P j) F hF
      (fun s x hx => hcarrier s j x hx) p f.val f.property)
  refine ⟨⟨g,hg⟩,?_⟩
  have hj (j : κ) : delta R M p (post R M p (P j) (prism R M (τ j) p f.val))=post R M (p+1) (P j) f.val := by
    have h := prism_identity R M (τ j) p f.val
    rw [hf,map_zero,zero_add] at h
    rw [delta_post,h,map_sub,post_pullback_zero R M (τ j) (P j) F
      (fun s x hx => hzero s j x hx) (p+1) f.val f.property,sub_zero]
  simp only [g,map_sum,hj]
  apply evaluation_injective R M (p+1)
  ext a
  simp only [map_sum,Finset.sum_apply,evaluation_post]
  exact hP _
include hP hτ hcarrier hzero in
lemma projection_prism_exactAt (p : ℕ) : (complex R M F hF).ExactAt (p+1) := by
  apply ((complex R M F hF).exactAt_iff' (i:=p) (j:=p+1) (k:=p+2) (by simp) (by simp)).mpr
  rw [ShortComplex.moduleCat_exact_iff]
  intro f hf
  change ((complex R M F hF).d (p+1) (p+2)).hom f=0 at hf
  rw [complex_d] at hf
  obtain ⟨g,hg⟩ := projection_prism_exact R M F hF P hP τ hτ hcarrier hzero p f (congrArg Subtype.val hf)
  refine ⟨g,?_⟩
  change ((complex R M F hF).d p (p+1)).hom g=f
  rw [complex_d]
  exact Subtype.ext hg
include hP hτ hcarrier hzero in
lemma projection_prism_acyclic [Nonempty ι] : (complex R M F hF).Acyclic := by
  intro p
  cases p with
  | zero => exact complex_exactAt_zero_of_nonempty R M F hF
  | succ p => exact projection_prism_exactAt R M F hF P hP τ hτ hcarrier hzero p
end Lech.AlternatingCech

open scoped Classical
end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ProductSourceCoverFaceSlice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open scoped BigOperators
open scoped Classical


namespace Lech.AlternatingCech
open scoped BigOperators
open Set
universe u
variable (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M]
variable {ι : Type} [Fintype ι] [LinearOrder ι]
attribute [local instance] OAI.Lech.AlternatingCech.faceSliceSortedDecEq
lemma sortedCoordinates_delta (n : ℕ) (f : Alt R M (ι := ι) n) (s : powersetCard ι (n+1)) :
    sortedCoordinates R M (n+1) (delta R M n f) s=
      ∑ i : Fin (n+1),(-1:ℤ)^i.val • sortedCoordinates R M n f (delete s i) := by
  rw [sortedCoordinates_apply]
  simp only [delta,LinearMap.coe_mk,AddHom.coe_mk,AlternatingMap.alternatizeUncurryFin_apply,
    LinearMap.smulRight_apply,epsilon_basis,one_smul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [sortedCoordinates_apply]
  change f (fun j => basis R (powersetCard.ofFinEmbEquiv.symm s (i.succAbove j)))=
    f (fun j => basis R (powersetCard.ofFinEmbEquiv.symm (delete s i) j))
  rw [delete_sorted]
  rfl
variable (F : Finset ι → Submodule R M) (hF : Monotone F)
lemma cochainsSorted_delta (n : ℕ) (f : cochains R M F n) :
    cochainsSorted R M F (n+1) (differential R M F hF n f)=
      sortedDelta R M F hF n (cochainsSorted R M F n f) := by
  ext s
  change sortedCoordinates R M (n+1) (delta R M n f.val) s=_
  rw [sortedCoordinates_delta]
  simp only [sortedDelta,LinearMap.coe_mk,AddHom.coe_mk,Submodule.coe_sum]
  rfl
lemma sortedDelta_square (n : ℕ) (f : sorted R M F n) :
    sortedDelta R M F hF (n+1) (sortedDelta R M F hF n f)=0 := by
  obtain ⟨g,rfl⟩ := (cochainsSorted R M F n).surjective f
  rw [←cochainsSorted_delta,←cochainsSorted_delta,differential_square,map_zero]
end Lech.AlternatingCech


namespace Lech.BicomplexTotal

section
open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂
universe u
variable {R : Type u} [CommRing R]
variable (F : Row (R := R))
lemma into_single_comm (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) :
    intoSingle F i ≫ (totalSingleZero F).d i j=F.d i j ≫ intoSingle F j := by
  simp only [intoSingle,Category.assoc,total_d,Preadditive.comp_add,
    ι_D₁,ι_D₂,single_d₁,comp_zero,zero_add]
  rw [d₂_eq _ _ 0 hij j (by simp)]
  dsimp
  simp only [one_smul]
  rw [←Category.assoc,HomologicalComplex.Hom.comm,Category.assoc]


end


open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂
universe u
end Lech.BicomplexTotal


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechConnectingIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open scoped BigOperators
open scoped Classical


namespace Lech.AlternatingCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M]
variable {ι : Type} [Fintype ι] [LinearOrder ι]
attribute [local instance] OAI.Lech.AlternatingCech.connectingSortedDecEq
variable (F : Finset ι → Submodule R M) (hF : Monotone F)
 
def sortedComplex : CochainComplex (ModuleCat.{u} R) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of R (sorted R M F n))
    (fun n => ModuleCat.ofHom (sortedDelta R M F hF n)) (fun n => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      exact sortedDelta_square R M F hF n)
lemma sortedComplex_d (n : ℕ) : (sortedComplex R M F hF).d n (n+1)=
    ModuleCat.ofHom (sortedDelta R M F hF n) := by
  change CochainComplex.of.d (fun n => ModuleCat.of R (sorted R M F n))
    (fun n => ModuleCat.ofHom (sortedDelta R M F hF n)) n (n+1)=_
  exact CochainComplex.of_d _ _ n
 

def cochainsSortedIso : complex R M F hF ≅ sortedComplex R M F hF :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (cochainsSorted R M F n).toModuleIso)
    (fun n m h => by
      obtain rfl : n+1=m := h
      rw [complex_d,sortedComplex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      exact (cochainsSorted_delta R M F hF n f).symm)
variable (q : ι → R) (hq : Ideal.span (Set.range q)=⊤)
variable (hclear : ∀ (s : Finset ι) (j : ι) (x : M),x∈F (insert j s) → ∃ N : ℕ,q j^N • x∈F s)
lemma sortedComplex_bounded (n : ℕ) (hn : Fintype.card ι<n) :
    IsZero ((sortedComplex R M F hF).X n) := by
  have : Subsingleton (sorted R M F n) := ⟨fun f g => funext fun s => by
    have hs : s.val.card=n := s.property
    have h := Finset.card_le_univ s.val
    omega⟩
  exact ModuleCat.isZero_of_subsingleton (ModuleCat.of R (sorted R M F n))
end Lech.AlternatingCech


namespace Lech.AlternatingCech
universe u v
variable (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M]
variable {ι : Type v} [DecidableEq ι]


lemma zeroAugmentation_mono (F : Finset ι → Submodule R M) (hF : Monotone F) :
    Monotone (zeroAugmentation R M F) := by
  intro s t hst
  by_cases hs : s=∅
  · simp [zeroAugmentation,hs]
  · have ht : t≠∅ := fun ht => hs (Finset.subset_empty.mp (ht ▸ hst))
    simpa only [zeroAugmentation,ite_eq_right hs,ite_eq_right ht] using hF hst
end Lech.AlternatingCech


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_AlternatingCechUnaugmentedComplex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option synthInstance.maxHeartbeats 200000
namespace OAI

section
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open scoped BigOperators
open scoped Classical
namespace Lech.AlternatingCech
open Set CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped BigOperators
universe u
variable (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M]
variable {ι : Type} [Fintype ι] [LinearOrder ι]
variable (F : Finset ι → Submodule R M) (hF : Monotone F)
abbrev unaugmentedComplex := sortedComplex R M (zeroAugmentation R M F) (zeroAugmentation_mono R M F hF)
omit [Fintype ι] in
lemma unaugmentedInclusion_delta (p : ℕ) (f : sorted R M (zeroAugmentation R M F) p) :
    unaugmentedInclusion R M F (p+1) (sortedDelta R M (zeroAugmentation R M F) (zeroAugmentation_mono R M F hF) p f)=
      sortedDelta R M F hF p (unaugmentedInclusion R M F p f) := by
  ext s
  simp only [unaugmentedInclusion,sortedDelta,LinearMap.coe_mk,AddHom.coe_mk,
    Submodule.coe_sum,Submodule.coe_smul_of_tower]
  rfl
lemma unaugmented_isZero_zero : IsZero ((unaugmentedComplex R M F hF).X 0) := by
  have : Subsingleton (sorted R M (zeroAugmentation R M F) 0) := ⟨fun f g => by
    ext s
    rw [DoubleCech.zeroIndex_eq s]
    have hf : (f DoubleCech.emptyIndex:M)=0 := by simpa [DoubleCech.emptyIndex, zeroAugmentation] using (f DoubleCech.emptyIndex).property
    have hg : (g DoubleCech.emptyIndex:M)=0 := by simpa [DoubleCech.emptyIndex, zeroAugmentation] using (g DoubleCech.emptyIndex).property
    exact hf.trans hg.symm⟩
  exact ModuleCat.isZero_of_subsingleton (ModuleCat.of R (sorted R M (zeroAugmentation R M F) 0))
 

lemma unaugmented_exactAt (p : ℕ) (h : (sortedComplex R M F hF).ExactAt (p+2)) :
    (unaugmentedComplex R M F hF).ExactAt (p+2) := by
  apply ((unaugmentedComplex R M F hF).exactAt_iff' (i:=p+1) (j:=p+2) (k:=p+3) (by simp) (by simp)).mpr
  rw [ShortComplex.moduleCat_exact_iff]
  intro f hf
  change sorted R M (zeroAugmentation R M F) (p+2) at f
  change ((unaugmentedComplex R M F hF).d (p+2) (p+3)).hom f=0 at hf
  rw [sortedComplex_d] at hf
  change sortedDelta R M (zeroAugmentation R M F) (zeroAugmentation_mono R M F hF) (p+2) f=0 at hf
  have he := ((sortedComplex R M F hF).exactAt_iff' (i:=p+1) (j:=p+2) (k:=p+3) (by simp) (by simp)).mp h
  rw [ShortComplex.moduleCat_exact_iff] at he
  obtain ⟨g,hg⟩ := he (unaugmentedInclusion R M F (p+2) f) (by
    change ((sortedComplex R M F hF).d (p+2) (p+3)).hom _=0
    rw [sortedComplex_d]
    change sortedDelta R M F hF (p+2) (unaugmentedInclusion R M F (p+2) f)=0
    rw [←unaugmentedInclusion_delta R M F hF,hf,map_zero])
  change sorted R M F (p+1) at g
  change ((sortedComplex R M F hF).d (p+1) (p+2)).hom g = _ at hg
  rw [sortedComplex_d] at hg
  obtain ⟨g',rfl⟩ := unaugmentedInclusion_surjective R M F (p+1) (by omega) g
  refine ⟨g',?_⟩
  change ((unaugmentedComplex R M F hF).d (p+1) (p+2)).hom g'=f
  rw [sortedComplex_d]
  change sortedDelta R M (zeroAugmentation R M F) (zeroAugmentation_mono R M F hF) (p+1) g'=f
  apply unaugmentedInclusion_injective R M F (p+2)
  rw [unaugmentedInclusion_delta R M F hF]
  exact hg
 

def sortedZeroEquiv : sorted R M F 0 ≃ₗ[R] F ∅ where
  toFun f := f DoubleCech.emptyIndex
  invFun x s := (DoubleCech.zeroIndex_eq s).symm ▸ x
  left_inv f := by funext s;cases DoubleCech.zeroIndex_eq s;rfl
  right_inv x := rfl
  map_add' f g := rfl
  map_smul' r f := rfl
variable [Nonempty ι]
omit [Fintype ι] in
lemma sorted_zero_injective : Function.Injective (sortedDelta R M F hF 0) := by
  intro f g h
  apply (sortedZeroEquiv R M F).injective
  let i : ι := Classical.choice (inferInstance : Nonempty ι)
  let s : powersetCard ι 1 := ⟨{i},Finset.card_singleton _⟩
  have hv := congrArg (fun z : sorted R M F 1 => (z s:M)) h
  apply Subtype.ext
  change (∑ j : Fin 1,(-1:ℤ)^j.val • (f (delete s j):M))=(∑ j : Fin 1,(-1:ℤ)^j.val • (g (delete s j):M)) at hv
  simp only [Fin.sum_univ_one,Fin.val_zero,pow_zero,one_zsmul] at hv
  rw [DoubleCech.zeroIndex_eq (delete s 0)] at hv
  exact hv

omit [Nonempty ι] in
lemma unaugmentedAugmentation_square :
    (sortedDelta R M (zeroAugmentation R M F) (zeroAugmentation_mono R M F hF) 1).comp
      (unaugmentedAugmentation R M F hF)=0 := by
  apply LinearMap.ext
  intro f
  change sortedDelta R M (zeroAugmentation R M F) (zeroAugmentation_mono R M F hF) 1 (unaugmentedAugmentation R M F hF f)=0
  apply unaugmentedInclusion_injective R M F 2
  rw [map_zero,unaugmentedInclusion_delta R M F hF]
  change sortedDelta R M F hF 1 ((unaugmentedEquiv R M F 1 (by omega))
    ((unaugmentedEquiv R M F 1 (by omega)).symm (sortedDelta R M F hF 0 f)))=0
  rw [LinearEquiv.apply_symm_apply,sortedDelta_square]
def augmentationShortComplex := ShortComplex.moduleCatMk (unaugmentedAugmentation R M F hF)
    (sortedDelta R M (zeroAugmentation R M F) (zeroAugmentation_mono R M F hF) 1)
    (unaugmentedAugmentation_square R M F hF)
omit [Nonempty ι] in
lemma augmentationShortComplex_exact (h : (sortedComplex R M F hF).ExactAt 1) :
    (augmentationShortComplex R M F hF).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro f hf
  change sorted R M (zeroAugmentation R M F) 1 at f
  change sortedDelta R M (zeroAugmentation R M F) (zeroAugmentation_mono R M F hF) 1 f=0 at hf
  have he := ((sortedComplex R M F hF).exactAt_iff' (i:=0) (j:=1) (k:=2) (by simp) (by simp)).mp h
  rw [ShortComplex.moduleCat_exact_iff] at he
  obtain ⟨g,hg⟩ := he (unaugmentedInclusion R M F 1 f) (by
    change ((sortedComplex R M F hF).d 1 2).hom _=0
    rw [sortedComplex_d]
    change sortedDelta R M F hF 1 (unaugmentedInclusion R M F 1 f)=0
    rw [←unaugmentedInclusion_delta R M F hF,hf,map_zero])
  change sorted R M F 0 at g
  change ((sortedComplex R M F hF).d 0 1).hom g = _ at hg
  rw [sortedComplex_d] at hg
  refine ⟨g,?_⟩
  apply (unaugmentedEquiv R M F 1 (by omega)).injective
  change (unaugmentedEquiv R M F 1 (by omega))
    ((unaugmentedEquiv R M F 1 (by omega)).symm (sortedDelta R M F hF 0 g))=_
  rw [LinearEquiv.apply_symm_apply]
  exact hg
instance augmentationShortComplex_mono : Mono (augmentationShortComplex R M F hF).f := by
  apply (ModuleCat.mono_iff_injective _).mpr
  exact (unaugmentedEquiv R M F 1 (by omega)).symm.injective.comp (sorted_zero_injective R M F hF)
 

def unaugmented_homology_one (h : (sortedComplex R M F hF).ExactAt 1) :
    (unaugmentedComplex R M F hF).homology 1 ≅ ModuleCat.of R (F ∅) := by
  let U := unaugmentedComplex R M F hF
  let S := U.sc' 0 1 2
  have hf : S.f=0 := (unaugmented_isZero_zero R M F hF).eq_of_src _ _
  let T := augmentationShortComplex R M F hF
  let c : KernelFork S.g := KernelFork.ofι T.f (by
    exact T.zero)
  have hc : IsLimit c := (augmentationShortComplex_exact R M F hF h).fIsKernel
  exact U.homologyIsoSc' 0 1 2 (by simp) (by simp) ≪≫
    (ShortComplex.LeftHomologyData.ofIsLimitKernelFork S hf c hc).homologyIso ≪≫
    (sortedZeroEquiv R M F).toModuleIso
end Lech.AlternatingCech


namespace Lech.AlternatingCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped BigOperators Classical
universe u
variable (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (F : Finset ι → Submodule R M)
lemma zeroAug_cochains_le (p : ℕ) : cochains R M (zeroAugmentation R M F) p ≤ cochains R M F p := by
  intro f hf a
  have h := hf a
  by_cases hs : FiniteCoverCech.intersection a=∅
  · have hz : evaluation R M p f a=0 := by
      simpa [zeroAugmentation,hs] using h
    rw [hz]
    exact (F _).zero_mem
  · simpa only [zeroAugmentation,ite_eq_right hs] using h
lemma zeroAug_cochains_pos (p : ℕ) (hp : 0<p) :
    cochains R M (zeroAugmentation R M F) p=cochains R M F p := by
  apply le_antisymm (zeroAug_cochains_le R M F p)
  intro f hf a
  have hs : FiniteCoverCech.intersection a≠∅ := by
    intro he
    have hm : a ⟨0,hp⟩∈FiniteCoverCech.intersection a := by simp [FiniteCoverCech.intersection]
    rw [he] at hm
    exact Finset.notMem_empty _ hm
  simpa only [zeroAugmentation,ite_eq_right hs] using hf a
lemma zeroAug_cochains_zero (f : Alt R M (ι:=ι) 0)
    (hf : f∈cochains R M (zeroAugmentation R M F) 0) : f=0 := by
  apply evaluation_injective R M 0
  apply funext;intro a
  have he : FiniteCoverCech.intersection a=∅ := by simp [FiniteCoverCech.intersection]
  have h := hf a
  simpa [zeroAugmentation,he] using h
end Lech.AlternatingCech


namespace Lech.AlternatingCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable (R : Type u) [CommRing R]
variable (M N : Type u) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable (F : Finset ι → Submodule R M) (G : Finset κ → Submodule R N)
variable (hF : Monotone F) (hG : Monotone G)
variable (t : ∀ p,Alt R M (ι:=ι) p →ₗ[R] Alt R N (ι:=κ) p)
variable (ht : ∀ p f,f∈cochains R M F p → t p f∈cochains R N G p)
variable (hc : ∀ p f,t (p+1) (delta R M p f)=delta R N p (t p f))
 

def complexMap : complex R M F hF ⟶ complex R N G hG :=
  CochainComplex.ofHom (fun p => ModuleCat.ofHom ((t p).restrict (ht p))) (fun p => by
    rw [complex_d,complex_d]
    apply ModuleCat.hom_ext;apply LinearMap.ext;intro f
    exact Subtype.ext (hc p f.val).symm)
end Lech.AlternatingCech


end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ArbitraryCoefficientField
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.ArbitraryCoefficientField
variable {k R : Type*} [Field k] [CommRing R]
  (p : ℕ) [Fact p.Prime] [CharP k p] [CharP R p] (I : Ideal R) [I.IsMaximal]

lemma exists_next (n : ℕ) (f : k →+* R ⧸ I^(p^n)) :
    ∃ g : k →+* R ⧸ I^(p^(n+1)),
      (Ideal.Quotient.factorPow I ((power_strictMono p).monotone (Nat.le_succ n))).comp g=f := by
  let : Nontrivial (R ⧸ I^(p^(n+1))) := Ideal.Quotient.nontrivial_iff.mpr
    (ne_top_of_le_ne_top (Ideal.IsMaximal.ne_top inferInstance)
      (Ideal.pow_le_self (pow_ne_zero _ (Nat.Prime.ne_zero Fact.out))))
  let : CharP (R ⧸ I^(p^(n+1))) p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr
    (by rw [← map_natCast (Ideal.Quotient.mk _),CharP.cast_eq_zero,map_zero])
  exact FieldLift.exists_lift_surjective p _ (Ideal.Quotient.factor_surjective _)
    (transition_ker p I n) f

 
def stage (f : k →+* R ⧸ I) : (n : ℕ) → k →+* R ⧸ I^(p^n)
  | 0 => (Ideal.quotEquivOfEq (by simp : I=I^(p^0))).toRingHom.comp f
  | n+1 => (exists_next p I n (stage f n)).choose

lemma stage_compatible (f : k →+* R ⧸ I) (n : ℕ) :
    (Ideal.Quotient.factorPow I ((power_strictMono p).monotone (Nat.le_succ n))).comp
      (stage p I f (n+1))=stage p I f n :=
  (exists_next p I n (stage p I f n)).choose_spec

variable [IsAdicComplete I R]
 
def sectionMap (f : k →+* R ⧸ I) : k →+* R :=
  IsAdicComplete.StrictMono.liftRingHom I (power_strictMono p) (stage p I f)
    (fun {n} => stage_compatible p I f n)

lemma sectionMap_mod (f : k →+* R ⧸ I) (x : k) :
    Ideal.Quotient.mk I (sectionMap p I f x)=f x := by
  have h := IsAdicComplete.StrictMono.mk_liftRingHom I (power_strictMono p)
    (stage p I f) (fun {n} => stage_compatible p I f n) (n:=0) x
  change Ideal.Quotient.mk (I^(p^0)) (sectionMap p I f x)=
    (Ideal.quotEquivOfEq (by simp : I=I^(p^0))) (f x) at h
  apply (Ideal.quotEquivOfEq (by simp : I=I^(p^0))).injective
  simpa only [Ideal.quotEquivOfEq_mk] using h

end Lech.ArbitraryCoefficientField

namespace Lech.ArbitraryCoefficientField
open IsLocalRing
variable (R : Type*) [CommRing R] [IsLocalRing R]
  (p : ℕ) [Fact p.Prime] [CharP R p] [IsAdicComplete (maximalIdeal R) R]
 

def quotientSectionData : {g : R ⧸ maximalIdeal R →+* R //
    Function.RightInverse g (Ideal.Quotient.mk (maximalIdeal R))} := by
  let : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
  let : CharP (R ⧸ maximalIdeal R) p :=
    (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr
      (by rw [← map_natCast (Ideal.Quotient.mk (maximalIdeal R)),CharP.cast_eq_zero,map_zero])
  refine ⟨sectionMap (k:=R ⧸ maximalIdeal R) p (maximalIdeal R) (RingHom.id _),?_⟩
  intro x
  exact sectionMap_mod p (maximalIdeal R) (RingHom.id _) x


end Lech.ArbitraryCoefficientField

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ProductSourceCoverAllowedEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open scoped BigOperators
open scoped Classical


namespace Lech.AlternatingCech
open Set
open scoped BigOperators
universe u
variable (R : Type u) [CommRing R]
variable {ι : Type} [LinearOrder ι]
variable (M : Type u) [AddCommGroup M] [Module R M]
def rawDelta (n : ℕ) : (powersetCard ι n → M) →ₗ[R] (powersetCard ι (n+1) → M) where
  toFun f s := ∑ i : Fin (n+1),(-1:ℤ)^i.val • f (delete s i)
  map_add' f g := by ext s;simp [smul_add,Finset.sum_add_distrib]
  map_smul' r f := by
    ext s
    simp only [Pi.smul_apply,Finset.smul_sum,RingHom.id_apply]
    apply Finset.sum_congr rfl
    intro i _
    exact smul_comm _ _ _
variable (F : Finset ι → Submodule R M) (hF : Monotone F)
lemma rawDelta_sorted (n : ℕ) (f : sorted R M F n) :
    rawDelta R M n (fun s => (f s:M))=(fun s => (sortedDelta R M F hF n f s:M)) := by
  ext s
  simp only [rawDelta,sortedDelta,LinearMap.coe_mk,AddHom.coe_mk,Submodule.coe_sum]
  rfl
variable (N : Type u) [AddCommGroup N] [Module R N]
lemma rawDelta_post (φ : M →ₗ[R] N) (n : ℕ) (f : powersetCard ι n → M) :
    rawDelta R N n (fun s => φ (f s))=(fun s => φ (rawDelta R M n f s)) := by
  ext s
  change (∑ i : Fin (n+1),(-1:ℤ)^i.val • φ (f (delete s i))) =
    φ (∑ i : Fin (n+1),(-1:ℤ)^i.val • f (delete s i))
  rw [map_sum]
  simp only [map_zsmul]
end Lech.AlternatingCech


namespace Lech.AlternatingCech
open Set CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable (R : Type u) [CommRing R]
variable (M : Type u) [AddCommGroup M] [Module R M]
variable (N : Type u) [AddCommGroup N] [Module R N]
variable {ι : Type}
variable (F : Finset ι → Submodule R M) (G : Finset ι → Submodule R N)
variable (φ : M →ₗ[R] N) (hφ : Function.Injective φ) (hFG : ∀ s,(F s).map φ=G s)
variable [Fintype ι] [LinearOrder ι]
def sortedFamilyEquiv (p : ℕ) : sorted R M F p ≃ₗ[R] sorted R N G p :=
  LinearEquiv.piCongrRight (fun s => familyEquiv R M N F G φ hφ hFG s.val)
omit [Fintype ι] [LinearOrder ι] in
lemma sortedFamilyEquiv_apply (p : ℕ) (f : sorted R M F p) (s : powersetCard ι p) :
    (sortedFamilyEquiv R M N F G φ hφ hFG p f s:N)=φ (f s:M) := rfl
variable (hF : Monotone F) (hG : Monotone G)
omit [Fintype ι] in
lemma sortedFamilyEquiv_delta (p : ℕ) (f : sorted R M F p) :
    sortedFamilyEquiv R M N F G φ hφ hFG (p+1) (sortedDelta R M F hF p f)=
      sortedDelta R N G hG p (sortedFamilyEquiv R M N F G φ hφ hFG p f) := by
  ext s
  simp only [sortedFamilyEquiv_apply,sortedDelta,LinearMap.coe_mk,AddHom.coe_mk,Submodule.coe_sum,
    Submodule.coe_smul_of_tower,map_sum,map_zsmul]
  rfl
 

def sortedFamilyIso : sortedComplex R M F hF ≅ sortedComplex R N G hG :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p => (sortedFamilyEquiv R M N F G φ hφ hFG p).toModuleIso) (fun p q hpq => by
      obtain rfl : p+1=q := hpq
      rw [sortedComplex_d,sortedComplex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      exact (sortedFamilyEquiv_delta R M N F G φ hφ hFG hF hG p f).symm)
end Lech.AlternatingCech


namespace Lech.AlternatingCech
open CategoryTheory
universe u
variable (R : Type u) [CommRing R]
variable (M N : Type u) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable {ι : Type} [Fintype ι] [LinearOrder ι]
def sortedUnaugmentedFamilyIso (F : Finset ι → Submodule R M) (G : Finset ι → Submodule R N)
    (f : M →ₗ[R] N) (hf : Function.Injective f) (hfg : ∀ s,(F s).map f=G s)
    (hF : Monotone F) (hG : Monotone G) :
    unaugmentedComplex R M F hF ≅ unaugmentedComplex R N G hG :=
  sortedFamilyIso R M N (zeroAugmentation R M F) (zeroAugmentation R N G) f hf
    (fun s => by
      by_cases hs : s=∅
      · simp [zeroAugmentation,hs]
      · simpa only [zeroAugmentation,ite_eq_right hs] using hfg s)
    (zeroAugmentation_mono R M F hF) (zeroAugmentation_mono R N G hG)
end Lech.AlternatingCech


namespace Lech.AlternatingCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable (R : Type u) [CommRing R]
variable (M N P : Type u) [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
variable {ι κ μ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype μ] [DecidableEq μ]
variable (F : Finset ι → Submodule R M) (G : Finset κ → Submodule R N) (H : Finset μ → Submodule R P)
variable (hF : Monotone F) (hG : Monotone G) (hH : Monotone H)
variable (s : ∀ p,Alt R M (ι:=ι) p →ₗ[R] Alt R N (ι:=κ) p)
variable (t : ∀ p,Alt R N (ι:=κ) p →ₗ[R] Alt R P (ι:=μ) p)
variable (hs : ∀ p f,f∈cochains R M F p → s p f∈cochains R N G p)
variable (ht : ∀ p f,f∈cochains R N G p → t p f∈cochains R P H p)
variable (hsc : ∀ p f,s (p+1) (delta R M p f)=delta R N p (s p f))
variable (htc : ∀ p f,t (p+1) (delta R N p f)=delta R P p (t p f))
variable (hzero : ∀ p f,f∈cochains R M F p → t p (s p f)=0)
def complexSequence : ShortComplex (CochainComplex (ModuleCat.{u} R) ℕ) :=
  ShortComplex.mk (complexMap R M N F G hF hG s hs hsc) (complexMap R N P G H hG hH t ht htc) (by
    ext p : 1
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    exact Subtype.ext (hzero p f.val f.property))
lemma complexSequence_shortExact
    (hinj : ∀ p,Function.Injective ((s p).restrict (hs p)))
    (hexa : ∀ p f,f∈cochains R N G p → t p f=0 → ∃ g,g∈cochains R M F p ∧ s p g=f)
    (hsur : ∀ p f,f∈cochains R P H p → ∃ g,g∈cochains R N G p ∧ t p g=f) :
    (complexSequence R M N P F G H hF hG hH s t hs ht hsc htc hzero).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro p
  refine CategoryTheory.ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.moduleCat_exact_iff]
    intro f hf
    have hf' : t p f.val=0 := congrArg Subtype.val hf
    obtain ⟨g,hg,hgf⟩ := hexa p f.val f.property hf'
    exact ⟨⟨g,hg⟩,Subtype.ext hgf⟩
  · exact (ModuleCat.mono_iff_injective _).mpr (hinj p)
  · apply (ModuleCat.epi_iff_surjective _).mpr
    intro f
    obtain ⟨g,hg,hgf⟩ := hsur p f.val f.property
    exact ⟨⟨g,hg⟩,Subtype.ext hgf⟩
lemma complexSequence_shortExact_injective
    (hinj : ∀ p,Function.Injective (s p))
    (hexa : ∀ p f,f∈cochains R N G p → t p f=0 → ∃ g,g∈cochains R M F p ∧ s p g=f)
    (hsur : ∀ p f,f∈cochains R P H p → ∃ g,g∈cochains R N G p ∧ t p g=f) :
    (complexSequence R M N P F G H hF hG hH s t hs ht hsc htc hzero).ShortExact := by
  apply complexSequence_shortExact R M N P F G H hF hG hH s t hs ht hsc htc hzero _ hexa hsur
  intro p f g h
  exact Subtype.ext (hinj p (congrArg Subtype.val h))
end Lech.AlternatingCech


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ProductSourceCoverHighThreshold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option synthInstance.maxHeartbeats 200000
namespace OAI

section
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open scoped BigOperators
open scoped Classical


namespace Lech.AlternatingCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped BigOperators
universe u
variable (R : Type u) [CommRing R] (K : Type u) [CommRing K] [Algebra R K]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (F : Finset ι → Submodule R K)
variable (A : Type u) [CommRing A] [Algebra R A] (φ : A →ₐ[R] K)
variable (hstable : ∀ (s : Finset ι) (a : A) (x : K),x∈F s → φ a*x∈F s)
variable (q : ι → A) (hq : Ideal.span (Set.range q)=⊤)
variable (hclear : ∀ (s : Finset ι) (j : ι) (x : K),x∈F (insert j s) → ∃ N : ℕ,φ (q j)^N*x∈F s)
include hstable hclear in
lemma scalar_uniform_clear (n : ℕ) (f : cochains R K F (n+1)) :
    ∃ N : ℕ,∀ (j : ι) (a : Fin n → ι),φ (q j)^N*evaluation R K (n+1) f.val (Fin.cons j a)∈F (FiniteCoverCech.intersection a) := by
  choose m hm using fun (p : ι × (Fin n → ι)) =>
    hclear (FiniteCoverCech.intersection p.2) p.1 (evaluation R K (n+1) f.val (Fin.cons p.1 p.2)) (by
      rw [←FiniteCoverCech.intersection_cons];exact f.property _)
  let N := Finset.univ.sup m
  refine ⟨N,fun j a => ?_⟩
  have hn : m (j,a)≤N := Finset.le_sup (Finset.mem_univ _)
  rw [←Nat.sub_add_cancel hn,pow_add,mul_assoc,←map_pow]
  exact hstable _ _ _ (hm (j,a))
include hstable hq hclear in
 

theorem scalar_exact (n : ℕ) (f : cochains R K F (n+1)) (hf : delta R K (n+1) f.val=0) :
    ∃ g : cochains R K F n,delta R K n g.val=f.val := by
  obtain ⟨N,hN⟩ := scalar_uniform_clear R K F A φ hstable q hclear n f
  obtain ⟨c,hc⟩ := FiniteCoverCech.partition A q hq N
  let P (j : ι) : K →ₗ[R] K := LinearMap.mulLeft R (φ (c j*q j^N))
  let g : Alt R K (ι:=ι) n := ∑ j,post R K n (P j) (extra R K j n f.val)
  have hg : g∈cochains R K F n := by
    intro a
    change evaluation R K n g a∈F (FiniteCoverCech.intersection a)
    simp only [g,map_sum,Finset.sum_apply,evaluation_post,evaluation_extra]
    apply (F _).sum_mem
    intro j _
    change φ (c j*q j^N)*evaluation R K (n+1) f.val (Fin.cons j a)∈_
    rw [map_mul,map_pow,mul_assoc]
    exact hstable _ _ _ (hN j a)
  refine ⟨⟨g,hg⟩,?_⟩
  have hj (j : ι) : delta R K n (extra R K j n f.val)=f.val := by
    have h := extra_delta R K j n f.val
    rw [hf,map_zero,zero_add] at h
    exact h
  simp only [g,map_sum,delta_post,hj]
  apply evaluation_injective R K (n+1)
  ext a
  simp only [map_sum,Finset.sum_apply,evaluation_post]
  change (∑ j,φ (c j*q j^N)*evaluation R K (n+1) f.val a)=_
  rw [←Finset.sum_mul,←map_sum,hc,map_one,one_mul]
include hstable hq hclear in
lemma scalar_complex_acyclic [Nonempty ι] (hF : Monotone F) : (complex R K F hF).Acyclic := by
  intro n
  cases n with
  | zero => exact complex_exactAt_zero_of_nonempty R K F hF
  | succ n =>
    apply ((complex R K F hF).exactAt_iff' (i:=n) (j:=n+1) (k:=n+2) (by simp) (by simp)).mpr
    rw [ShortComplex.moduleCat_exact_iff]
    intro f hf
    change ((complex R K F hF).d (n+1) (n+2)).hom f=0 at hf
    rw [complex_d] at hf
    obtain ⟨g,hg⟩ := scalar_exact R K F A φ hstable q hq hclear n f (congrArg Subtype.val hf)
    refine ⟨g,?_⟩
    change ((complex R K F hF).d n (n+1)).hom g=f
    rw [complex_d]
    exact Subtype.ext hg
end Lech.AlternatingCech


end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechSignedUnit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open scoped BigOperators
open scoped Classical


namespace Lech.AlternatingCech
open Set CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M]
variable {ι : Type} [Fintype ι] [LinearOrder ι] [Nonempty ι]
variable (F : Finset ι → Submodule R M) (hF : Monotone F)
 

lemma empty_mem_of_singletons (h : (sortedComplex R M F hF).ExactAt 1)
    (x : M) (hx : ∀ i,x∈F {i}) : x∈F ∅ := by
  let f : sorted R M F 1 := fun s => ⟨x,by
    obtain ⟨i,hi⟩ := Finset.card_eq_one.mp s.property
    rw [hi];exact hx i⟩
  have hf : sortedDelta R M F hF 1 f=0 := by
    funext s
    apply Subtype.ext
    change (∑ i : Fin 2,(-1:ℤ)^i.val • x)=0
    simp [Fin.sum_univ_two]
  have he := ((sortedComplex R M F hF).exactAt_iff' (i:=0) (j:=1) (k:=2) (by simp) (by simp)).mp h
  rw [ShortComplex.moduleCat_exact_iff] at he
  obtain ⟨g,hg⟩ := he f (by
    change ((sortedComplex R M F hF).d 1 2).hom f=0
    rw [sortedComplex_d];exact hf)
  change ((sortedComplex R M F hF).d 0 1).hom g=f at hg
  rw [sortedComplex_d] at hg
  let i : ι := Classical.choice (inferInstance : Nonempty ι)
  let s : powersetCard ι 1 := ⟨{i},Finset.card_singleton _⟩
  have hv := congrArg (fun z : sorted R M F 1 => (z s:M)) hg
  change (∑ j : Fin 1,(-1:ℤ)^j.val • (g (delete s j):M))=x at hv
  simp only [Fin.sum_univ_one,Fin.val_zero,pow_zero,one_zsmul] at hv
  rw [DoubleCech.zeroIndex_eq (delete s 0)] at hv
  exact hv ▸ (g DoubleCech.emptyIndex).property
end Lech.AlternatingCech
end

end OAI
end


