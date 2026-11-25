-- Prove2me | Definitions.Def_PretorsionImageClosed_IndecomposableClosures_ImageClosure
-- name    : PretorsionImageClosed_IndecomposableClosures_ImageClosure
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T06:57:41.630434+00:00
-- url     : https://prove2.me/theorems/389789e0-f89e-512f-80f5-83287ec754c5
-- title:
--   Image Closure
-- statement:
--   Definitions and structural lemmas for Image Closure, from Haruhisa Enomoto (haruhisa-enomoto/pretorsion-image-closed; see pinned Apache-2.0 LICENSE)'s pinned Pretorsion theories and image-closed subcategories of finite-dimensional algebras development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/ImageClosure.lean

module
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_Subcategories
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_SplitProjective
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_Compact
public import Definitions.Def_PretorsionImageClosed_Realizations_LeastRealization
public import Definitions.Def_PretorsionImageClosed_Length_Modules
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_addOf_indOf
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_inAdd_mono
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_indOf_addOf
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_mem_qClosure_iff_inFac
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_mem_qSet_iff
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_mem_sClosure_iff_inSub
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_mem_sSet_iff
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_prop_iff_inAdd_indOf
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_qSet_empty
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_reject_empty
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_sSet_empty
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_trace_empty
public import Theorems.Thm_PretorsionImageClosed_SetClosure_coe_bot
public import Theorems.Thm_PretorsionImageClosed_SetClosure_coe_iInf
public import Theorems.Thm_PretorsionImageClosed_SetClosure_coe_iSup
public import Theorems.Thm_PretorsionImageClosed_SetClosure_coe_inf
public import Theorems.Thm_PretorsionImageClosed_SetClosure_coe_pointClosure
public import Theorems.Thm_PretorsionImageClosed_SetClosure_coe_sSup
public import Theorems.Thm_PretorsionImageClosed_SetClosure_coe_sup
public import Theorems.Thm_PretorsionImageClosed_SetClosure_coe_top
public import Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_ext
public import Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_op_unop
public import Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_unop_op
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_op_prop
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_op_unop
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_unop_op
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_unop_prop
public import Theorems.Thm_PretorsionImageClosed_Statement_le_gen_inf_cogen
public import Theorems.Thm_PretorsionImageClosed_idealKernel_bot
public import Theorems.Thm_PretorsionImageClosed_idealKernel_top
public import Theorems.Thm_PretorsionImageClosed_idealRange_bot
public import Theorems.Thm_PretorsionImageClosed_idealRange_top
public import Theorems.Thm_PretorsionImageClosed_mem_endNonunitsIdeal_iff
attribute [local simp] PretorsionImageClosed.IndecomposableSkeleton.mem_qClosure_iff_inFac
attribute [local simp] PretorsionImageClosed.IndecomposableSkeleton.mem_sClosure_iff_inSub
attribute [local simp] PretorsionImageClosed.IndecomposableSkeleton.qSet_empty
attribute [local simp] PretorsionImageClosed.IndecomposableSkeleton.reject_empty
attribute [local simp] PretorsionImageClosed.IndecomposableSkeleton.sSet_empty
attribute [local simp] PretorsionImageClosed.IndecomposableSkeleton.trace_empty
attribute [local simp] PretorsionImageClosed.SetClosure.coe_bot
attribute [local simp] PretorsionImageClosed.SetClosure.coe_iInf
attribute [local simp] PretorsionImageClosed.SetClosure.coe_iSup
attribute [local simp] PretorsionImageClosed.SetClosure.coe_inf
attribute [local simp] PretorsionImageClosed.SetClosure.coe_pointClosure
attribute [local simp] PretorsionImageClosed.SetClosure.coe_sSup
attribute [local simp] PretorsionImageClosed.SetClosure.coe_sup
attribute [local simp] PretorsionImageClosed.SetClosure.coe_top
attribute [local simp] PretorsionImageClosed.Statement.PretorsionTheory.op_unop
attribute [local simp] PretorsionImageClosed.Statement.PretorsionTheory.unop_op
attribute [local simp] PretorsionImageClosed.Statement.Subcategory.op_prop
attribute [local simp] PretorsionImageClosed.Statement.Subcategory.op_unop
attribute [local simp] PretorsionImageClosed.Statement.Subcategory.unop_op
attribute [local simp] PretorsionImageClosed.Statement.Subcategory.unop_prop
attribute [local simp] PretorsionImageClosed.idealKernel_bot
attribute [local simp] PretorsionImageClosed.idealKernel_top
attribute [local simp] PretorsionImageClosed.idealRange_bot
attribute [local simp] PretorsionImageClosed.idealRange_top
attribute [local simp] PretorsionImageClosed.mem_endNonunitsIdeal_iff


set_option autoImplicit true
@[expose] public section
@[expose] public section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits Set
namespace PretorsionImageClosed.IndecomposableSkeleton
universe u v w
variable {R : Type u} [Ring R] [IsNoetherianRing R] {ι : Type v}
  (σ : IndecomposableSkeleton.{u, v, w} R ι)
attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts
def iSet (S : Set ι) : Set ι := σ.qSet S ∩ σ.sSet S
def iClosure : SetClosure ι where
  toFun := σ.iSet
  monotone' _ _ h := inter_subset_inter (qSet_monotone σ h) (sSet_monotone σ h)
  le_closure' S := subset_inter (subset_qSet σ S) (subset_sSet σ S)
  idempotent' S := by
    apply Subset.antisymm
    · refine subset_inter ?_ ?_
      · exact inter_subset_left.trans
          ((qSet_monotone σ inter_subset_left).trans (qSet_idempotent σ S).le)
      · exact inter_subset_right.trans
          ((sSet_monotone σ inter_subset_right).trans (sSet_idempotent σ S).le)
    · exact subset_inter (subset_qSet σ _) (subset_sSet σ _)
theorem mem_iClosure_iff (S : Set ι) (i : ι) :
    i ∈ σ.iClosure S ↔
      Statement.Gen (σ.addOf S) (σ.obj i) ∧ Statement.Cogen (σ.addOf S) (σ.obj i) :=
  and_congr (σ.mem_qSet_iff S i) (σ.mem_sSet_iff S i)
variable [IsArtinianRing R]
omit [IsArtinianRing R] in
theorem gen_of_retract {Z : Statement.Subcategory (FGModuleCat.{w} R)}
    {X Y : FGModuleCat.{w} R} (h : Retract Y X) (hX : Statement.Gen Z X) : Statement.Gen Z Y := by
  obtain ⟨N, hN, p, hp⟩ := hX
  exact ⟨N, hN, p ≫ h.r, epi_comp _ _⟩
omit [IsArtinianRing R] in
theorem cogen_of_retract {Z : Statement.Subcategory (FGModuleCat.{w} R)}
    {X Y : FGModuleCat.{w} R} (h : Retract Y X) (hX : Statement.Cogen Z X) :
    Statement.Cogen Z Y := by
  obtain ⟨N, hN, i, hi⟩ := hX
  exact ⟨N, hN, h.i ≫ i, mono_comp _ _⟩
theorem isImageClosed_iff_isClosed_indOf (Z : Statement.Subcategory (FGModuleCat.{w} R)) :
    Z.IsImageClosed ↔ σ.iClosure.IsClosed (σ.indOf Z) := by
  rw [Statement.isImageClosed_iff_eq_gen_inf_cogen, ClosureOperator.isClosed_iff_closure_le]
  constructor
  · intro h i hi
    rw [mem_iClosure_iff, addOf_indOf] at hi
    show Z.prop (σ.obj i)
    rw [h]
    exact hi
  · intro h
    apply le_antisymm (Statement.le_gen_inf_cogen Z)
    intro X hX
    rw [σ.prop_iff_inAdd_indOf Z X]
    obtain ⟨n, a, ⟨e⟩⟩ := σ.decomposes X
    refine ⟨{ index := FintypeCat.of (Fin n), label := a, mem := (fun t => ?_), iso := e }⟩
    let rt : Retract (σ.obj (a t)) X :=
      { i := biproduct.ι (fun j : Fin n ↦ σ.obj (a j)) t ≫ e.inv
        r := e.hom ≫ biproduct.π (fun j : Fin n ↦ σ.obj (a j)) t
        retract := by simp }
    apply h
    rw [mem_iClosure_iff, addOf_indOf]
    exact ⟨gen_of_retract rt hX.1, cogen_of_retract rt hX.2⟩
theorem isImageClosed_addOf_iff (S : Set ι) :
    (σ.addOf S).IsImageClosed ↔ σ.iClosure.IsClosed S := by
  rw [isImageClosed_iff_isClosed_indOf, indOf_addOf]
omit [IsArtinianRing R] in
theorem indOf_subset_iff {Z Z' : Statement.Subcategory (FGModuleCat.{w} R)} :
    σ.indOf Z ⊆ σ.indOf Z' ↔ Z ≤ Z' := by
  constructor
  · intro h X hX
    rw [σ.prop_iff_inAdd_indOf] at hX ⊢
    exact inAdd_mono σ h hX
  · intro h i hi
    exact h _ hi
def imageClosedOrderIso :
    {Z : Statement.Subcategory (FGModuleCat.{w} R) // Z.IsImageClosed} ≃o σ.iClosure.Closeds where
  toFun Z := ⟨σ.indOf Z.1, (σ.isImageClosed_iff_isClosed_indOf Z.1).1 Z.2⟩
  invFun C := ⟨σ.addOf C.1, (σ.isImageClosed_addOf_iff C.1).2 C.2⟩
  left_inv Z := Subtype.ext (σ.addOf_indOf Z.1)
  right_inv C := Subtype.ext (σ.indOf_addOf C.1)
  map_rel_iff' := σ.indOf_subset_iff
def IsSplittingProjective (Z : Statement.Subcategory (FGModuleCat.{w} R)) (X : FGModuleCat.{w} R) :
    Prop :=
  ∀ {N : FGModuleCat.{w} R} (p : N ⟶ X), Z.prop N → Epi p → IsSplitEpi p
def IsSplittingInjective (Z : Statement.Subcategory (FGModuleCat.{w} R)) (X : FGModuleCat.{w} R) :
    Prop :=
  ∀ {N : FGModuleCat.{w} R} (i : X ⟶ N), Z.prop N → Mono i → IsSplitMono i
variable [∀ i : ι, IsArtinianRing (Module.End R (σ.obj i))]
end PretorsionImageClosed.IndecomposableSkeleton


