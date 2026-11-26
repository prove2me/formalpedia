-- Prove2me | Definitions.Def_TunnellMap_ResidualBalance
-- name    : TunnellMap_ResidualBalance
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:43:59.355983+00:00
-- url     : https://prove2.me/theorems/e340f755-bbe8-5793-814a-96e0fdf9d0b1
-- title:
--   Residual Balance
-- statement:
--   Definitions and structural lemmas for Residual Balance, from Aakash Gurung (GrgAakash/tunnell-two-to-one-map; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Two-to-one executable map between Tunnell representation sets development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ResidualBalance.lean

import Definitions.Def_TunnellMap_Antipodal
import Theorems.Thm_TunnellMap_DirectDomain1_quotient_unique
import Theorems.Thm_TunnellMap_DirectDomain2_quotient_unique
import Theorems.Thm_TunnellMap_DirectDomain3_quotient_unique
import Theorems.Thm_TunnellMap_DirectImage1_quotient_unique
import Theorems.Thm_TunnellMap_DirectImage2_quotient_unique
import Theorems.Thm_TunnellMap_DirectImage3_quotient_unique
import Theorems.Thm_TunnellMap_direct_domains_pairwise_disjoint
import Theorems.Thm_TunnellMap_direct_images_pairwise_disjoint
import Theorems.Thm_TunnellMap_evenEquiv_apply
import Theorems.Thm_TunnellMap_evenEquiv_symm_apply
import Theorems.Thm_TunnellMap_qForm_aLift
import Theorems.Thm_TunnellMap_qForm_bLift
attribute [local simp] TunnellMap.evenEquiv_apply
attribute [local simp] TunnellMap.evenEquiv_symm_apply
attribute [local simp] TunnellMap.qForm_aLift
attribute [local simp] TunnellMap.qForm_bLift


set_option autoImplicit true
namespace TunnellMap
section ThreePredicates
variable {X : Type*} (P₁ P₂ P₃ : X → Prop)
noncomputable def threeUnionEquiv
    (h₁₂ : ∀ x, ¬ (P₁ x ∧ P₂ x))
    (h₁₃ : ∀ x, ¬ (P₁ x ∧ P₃ x))
    (h₂₃ : ∀ x, ¬ (P₂ x ∧ P₃ x)) :
    {x // P₁ x} ⊕ ({x // P₂ x} ⊕ {x // P₃ x}) ≃
      {x // P₁ x ∨ P₂ x ∨ P₃ x} := by
  classical
  refine
    { toFun := fun s => match s with
        | Sum.inl x => ⟨x.1, Or.inl x.2⟩
        | Sum.inr (Sum.inl x) => ⟨x.1, Or.inr (Or.inl x.2)⟩
        | Sum.inr (Sum.inr x) => ⟨x.1, Or.inr (Or.inr x.2)⟩
      invFun := fun x =>
        if h₁ : P₁ x.1 then Sum.inl ⟨x.1, h₁⟩
        else if h₂ : P₂ x.1 then Sum.inr (Sum.inl ⟨x.1, h₂⟩)
        else Sum.inr (Sum.inr ⟨x.1, x.2.resolve_left h₁ |>.resolve_left h₂⟩)
      left_inv := ?_
      right_inv := ?_ }
  · intro s
    rcases s with x | x
    · dsimp
      rw [dif_pos x.2]
    · rcases x with x | x
      · have hn₁ : ¬ P₁ x.1 := fun hp => h₁₂ x.1 ⟨hp, x.2⟩
        dsimp
        rw [dif_neg hn₁, dif_pos x.2]
      · have hn₁ : ¬ P₁ x.1 := fun hp => h₁₃ x.1 ⟨hp, x.2⟩
        have hn₂ : ¬ P₂ x.1 := fun hp => h₂₃ x.1 ⟨hp, x.2⟩
        dsimp
        rw [dif_neg hn₁, dif_neg hn₂]
  · intro x
    by_cases h₁ : P₁ x.1
    · apply Subtype.ext
      dsimp
      rw [dif_pos h₁]
    · by_cases h₂ : P₂ x.1
      · apply Subtype.ext
        dsimp
        rw [dif_neg h₁, dif_pos h₂]
      · apply Subtype.ext
        dsimp
        rw [dif_neg h₁, dif_neg h₂]
end ThreePredicates
noncomputable def domain1SubtypeEquiv (n : ℤ) :
    DirectDomain1 n ≃ {p : BOddRep n // DirectPredicate1 p} := by
  classical
  refine
    { toFun := fun p => ⟨p.rep, ⟨p.quotient, p.equation⟩⟩
      invFun := fun p => ⟨p.1, Classical.choose p.2, Classical.choose_spec p.2⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro p
    apply DirectDomain1.ext
    · rfl
    · let h : DirectPredicate1 p.rep := ⟨p.quotient, p.equation⟩
      change Classical.choose h = p.quotient
      exact p.quotient_unique (Classical.choose_spec h)
  · intro p
    apply Subtype.ext
    rfl
noncomputable def domain2SubtypeEquiv (n : ℤ) :
    DirectDomain2 n ≃ {p : BOddRep n // DirectPredicate2 p} := by
  classical
  refine
    { toFun := fun p => ⟨p.rep, ⟨p.quotient, p.equation⟩⟩
      invFun := fun p => ⟨p.1, Classical.choose p.2, Classical.choose_spec p.2⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro p
    apply DirectDomain2.ext
    · rfl
    · let h : DirectPredicate2 p.rep := ⟨p.quotient, p.equation⟩
      change Classical.choose h = p.quotient
      exact p.quotient_unique (Classical.choose_spec h)
  · intro p
    apply Subtype.ext
    rfl
noncomputable def domain3SubtypeEquiv (n : ℤ) :
    DirectDomain3 n ≃ {p : BOddRep n // DirectPredicate3 p} := by
  classical
  refine
    { toFun := fun p => ⟨p.rep, ⟨p.quotient, p.equation⟩⟩
      invFun := fun p => ⟨p.1, Classical.choose p.2, Classical.choose_spec p.2⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro p
    apply DirectDomain3.ext
    · rfl
    · let h : DirectPredicate3 p.rep := ⟨p.quotient, p.equation⟩
      change Classical.choose h = p.quotient
      exact p.quotient_unique (Classical.choose_spec h)
  · intro p
    apply Subtype.ext
    rfl
noncomputable def image1SubtypeEquiv (n : ℤ) :
    DirectImage1 n ≃ {p : ARep n // ImagePredicate1 p} := by
  classical
  refine
    { toFun := fun p => ⟨p.rep, ⟨p.quotient, p.quotient_odd, p.equation⟩⟩
      invFun := fun p => ⟨p.1, Classical.choose p.2, (Classical.choose_spec p.2).2,
        (Classical.choose_spec p.2).1⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro p
    apply DirectImage1.ext
    · rfl
    · let h : ImagePredicate1 p.rep :=
        ⟨p.quotient, p.quotient_odd, p.equation⟩
      change Classical.choose h = p.quotient
      exact p.quotient_unique (Classical.choose_spec h).2
  · intro p
    apply Subtype.ext
    rfl
noncomputable def image2SubtypeEquiv (n : ℤ) :
    DirectImage2 n ≃ {p : ARep n // ImagePredicate2 p} := by
  classical
  refine
    { toFun := fun p => ⟨p.rep, ⟨p.quotient, p.quotient_odd, p.equation⟩⟩
      invFun := fun p => ⟨p.1, Classical.choose p.2, (Classical.choose_spec p.2).2,
        (Classical.choose_spec p.2).1⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro p
    apply DirectImage2.ext
    · rfl
    · let h : ImagePredicate2 p.rep :=
        ⟨p.quotient, p.quotient_odd, p.equation⟩
      change Classical.choose h = p.quotient
      exact p.quotient_unique (Classical.choose_spec h).2
  · intro p
    apply Subtype.ext
    rfl
noncomputable def image3SubtypeEquiv (n : ℤ) :
    DirectImage3 n ≃ {p : ARep n // ImagePredicate3 p} := by
  classical
  refine
    { toFun := fun p => ⟨p.rep, ⟨p.quotient, p.quotient_odd, p.equation⟩⟩
      invFun := fun p => ⟨p.1, Classical.choose p.2, (Classical.choose_spec p.2).2,
        (Classical.choose_spec p.2).1⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro p
    apply DirectImage3.ext
    · rfl
    · let h : ImagePredicate3 p.rep :=
        ⟨p.quotient, p.quotient_odd, p.equation⟩
      change Classical.choose h = p.quotient
      exact p.quotient_unique (Classical.choose_spec h).2
  · intro p
    apply Subtype.ext
    rfl
noncomputable def directSourceUnionEquiv {n : ℤ} (hn : Odd n) :
    DirectDomain n ≃ {p : BOddRep n // DirectSourceUsed p} :=
  (Equiv.sumCongr (domain1SubtypeEquiv n)
      (Equiv.sumCongr (domain2SubtypeEquiv n) (domain3SubtypeEquiv n))).trans
    (threeUnionEquiv DirectPredicate1 DirectPredicate2 DirectPredicate3
      (fun p => (direct_domains_pairwise_disjoint hn p).1)
      (fun p => (direct_domains_pairwise_disjoint hn p).2.1)
      (fun p => (direct_domains_pairwise_disjoint hn p).2.2))
noncomputable def directTargetUnionEquiv {n : ℤ} (hn : Odd n) :
    DirectImage n ≃ {p : ARep n // DirectTargetUsed p} :=
  (Equiv.sumCongr (image1SubtypeEquiv n)
      (Equiv.sumCongr (image2SubtypeEquiv n) (image3SubtypeEquiv n))).trans
    (threeUnionEquiv ImagePredicate1 ImagePredicate2 ImagePredicate3
      (fun p => (direct_images_pairwise_disjoint hn p).1)
      (fun p => (direct_images_pairwise_disjoint hn p).2.1)
      (fun p => (direct_images_pairwise_disjoint hn p).2.2))
noncomputable def directSubsetEquiv {n : ℤ} (hn : Odd n) :
    {p : BOddRep n // DirectSourceUsed p} ≃ {p : ARep n // DirectTargetUsed p} :=
  (directSourceUnionEquiv hn).symm.trans
    ((directEquiv n).trans (directTargetUnionEquiv hn))
noncomputable instance bResidualFintype {n : ℤ} [Fintype (BOddRep n)] :
    Fintype (BResidual n) := Fintype.ofFinite _
noncomputable instance aResidualFintype {n : ℤ} [Fintype (ARep n)] :
    Fintype (AResidual n) := Fintype.ofFinite _
end TunnellMap


