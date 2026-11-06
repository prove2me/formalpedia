-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_Detector_GramCommonParam
-- name    : OAI_NumberTheory_DirichletL_Detector_GramCommonParam
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:45:41.953008+00:00
-- url     : https://prove2.me/theorems/13f12956-bdb8-4c4c-aa83-d6030b523145
-- title:
--   Gram Common Param
-- statement:
--   Definitions and structural lemmas for Gram Common Param, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Detector/GramCommonParam.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_Moments_FullCorrelation
import Theorems.Thm_OAI_SevenEighths_CenteredMomentCorrelation_scaledResidue_congruence
import Theorems.Thm_OAI_SevenEighths_CenteredMomentCorrelation_scaledResidue_injective
import Theorems.Thm_OAI_SevenEighths_CenteredMomentCorrelation_scaledResidue_mk
attribute [local simp] OAI.SevenEighths.CenteredMomentCorrelation.scaledResidue_mk


set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open CenteredMomentCorrelation
variable {A : Type*} [CommRing A] [IsDomain A]
abbrev ResidueQ (a : A) := A⧸Ideal.span {a}
def condition (C n₁ n₂ k : A) (p : ResidueQ (C*n₁) × ResidueQ (C*n₂)) : Prop :=
  scaledResidue (C*n₁) (C*n₂) ((C*n₁)*(C*n₂)) rfl p.1-
    scaledResidue (C*n₂) (C*n₁) ((C*n₁)*(C*n₂)) (mul_comm _ _) p.2=
    Ideal.Quotient.mk (Ideal.span {(C*n₁)*(C*n₂)}) (C*k)
abbrev Solutions (C n₁ n₂ k : A) := {p : ResidueQ (C*n₁) × ResidueQ (C*n₂) // condition C n₁ n₂ k p}
def leftParam (C n₁ b k : A) (t : ResidueQ C) : ResidueQ (C*n₁) :=
  Ideal.Quotient.mk _ (b*k)+scaledResidue C n₁ (C*n₁) rfl t
def rightParam (C n₂ a k : A) (t : ResidueQ C) : ResidueQ (C*n₂) :=
  Ideal.Quotient.mk _ (-a*k)+scaledResidue C n₂ (C*n₂) rfl t
omit [IsDomain A] in
@[simp] lemma leftParam_mk (C n₁ b k t : A) :
    leftParam C n₁ b k (Ideal.Quotient.mk _ t)=Ideal.Quotient.mk _ (b*k+n₁*t) := by
  simp only [leftParam,scaledResidue_mk,map_add]
omit [IsDomain A] in
@[simp] lemma rightParam_mk (C n₂ a k t : A) :
    rightParam C n₂ a k (Ideal.Quotient.mk _ t)=Ideal.Quotient.mk _ (-a*k+n₂*t) := by
  simp only [rightParam,scaledResidue_mk,map_add]
omit [IsDomain A] in
lemma param_condition (C n₁ n₂ a b k : A) (hab : a*n₁+b*n₂=1) (t : ResidueQ C) :
    condition C n₁ n₂ k (leftParam C n₁ b k t,rightParam C n₂ a k t) := by
  obtain ⟨t,rfl⟩ := Ideal.Quotient.mk_surjective t
  rw [leftParam_mk,rightParam_mk]
  unfold condition
  rw [scaledResidue_congruence]
  have he : C*n₂*(b*k+n₁*t)-C*n₁*(-a*k+n₂*t)-C*k=C*k*(a*n₁+b*n₂-1) := by ring
  rw [he,hab,sub_self,mul_zero]
  exact dvd_zero _
def param (C n₁ n₂ a b k : A) (hab : a*n₁+b*n₂=1) (t : ResidueQ C) : Solutions C n₁ n₂ k :=
  ⟨(leftParam C n₁ b k t,rightParam C n₂ a k t),param_condition C n₁ n₂ a b k hab t⟩
lemma param_injective (C n₁ n₂ a b k : A) (hab : a*n₁+b*n₂=1) (hn₁ : n₁≠0) :
    Function.Injective (param C n₁ n₂ a b k hab) := by
  intro t u he
  have hl : leftParam C n₁ b k t=leftParam C n₁ b k u := congrArg (fun p=>p.val.1) he
  apply scaledResidue_injective C n₁ (C*n₁) rfl hn₁
  exact add_left_cancel hl
lemma condition_divided (C n₁ n₂ k x y : A) (hC : C≠0)
    (hc : condition C n₁ n₂ k (Ideal.Quotient.mk _ x,Ideal.Quotient.mk _ y)) :
    C*n₁*n₂∣n₂*x-n₁*y-k := by
  unfold condition at hc
  rw [scaledResidue_congruence] at hc
  have hh : C*(C*n₁*n₂)∣C*(n₂*x-n₁*y-k) := by convert hc using 1 <;> ring
  exact (mul_dvd_mul_iff_left hC).mp hh
lemma param_surjective (C n₁ n₂ a b k : A) (hC : C≠0) (hab : a*n₁+b*n₂=1) :
    Function.Surjective (param C n₁ n₂ a b k hab) := by
  intro p
  obtain ⟨x,hx⟩ := Ideal.Quotient.mk_surjective p.val.1
  obtain ⟨y,hy⟩ := Ideal.Quotient.mk_surjective p.val.2
  have hc : condition C n₁ n₂ k (Ideal.Quotient.mk _ x,Ideal.Quotient.mk _ y) := by
    rw [hx,hy]
    exact p.property
  have hd := condition_divided C n₁ n₂ k x y hC hc
  refine ⟨Ideal.Quotient.mk _ (a*x+b*y),?_⟩
  apply Subtype.ext
  apply Prod.ext
  · change leftParam C n₁ b k (Ideal.Quotient.mk _ (a*x+b*y))=p.val.1
    rw [leftParam_mk,←hx,Ideal.Quotient.eq]
    apply Ideal.mem_span_singleton.mpr
    have hh : C*n₁∣n₂*x-n₁*y-k := (dvd_mul_right (C*n₁) n₂).trans hd
    have he : b*k+n₁*(a*x+b*y)-x= -b*(n₂*x-n₁*y-k) := by
      linear_combination x*hab
    rw [he]
    exact dvd_mul_of_dvd_right hh _
  · change rightParam C n₂ a k (Ideal.Quotient.mk _ (a*x+b*y))=p.val.2
    rw [rightParam_mk,←hy,Ideal.Quotient.eq]
    apply Ideal.mem_span_singleton.mpr
    have hh : C*n₂∣n₂*x-n₁*y-k := by
      apply dvd_trans _ hd
      exact ⟨n₁,by ring⟩
    have he : -a*k+n₂*(a*x+b*y)-y=a*(n₂*x-n₁*y-k) := by
      linear_combination y*hab
    rw [he]
    exact dvd_mul_of_dvd_right hh _
def solutionEquiv (C n₁ n₂ a b k : A) (hC : C≠0) (hn₁ : n₁≠0)
    (hab : a*n₁+b*n₂=1) : ResidueQ C≃Solutions C n₁ n₂ k :=
  Equiv.ofBijective (param C n₁ n₂ a b k hab)
    ⟨param_injective C n₁ n₂ a b k hab hn₁,param_surjective C n₁ n₂ a b k hC hab⟩
end SevenEighths.ProbeGramCommon
end
end OAI


