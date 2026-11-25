-- Prove2me | Definitions.Def_PretorsionImageClosed_IndecomposableClosures_Subcategories
-- name    : PretorsionImageClosed_IndecomposableClosures_Subcategories
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T05:50:07.637803+00:00
-- url     : https://prove2.me/theorems/66a29ed9-084e-437b-8566-4efea38458cc
-- title:
--   Subcategories
-- statement:
--   Definitions and structural lemmas for Subcategories, from Haruhisa Enomoto (haruhisa-enomoto/pretorsion-image-closed; see pinned Apache-2.0 LICENSE)'s pinned Pretorsion theories and image-closed subcategories of finite-dimensional algebras development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/Subcategories.lean

module
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_SplitInjective
public import Definitions.Def_PretorsionImageClosed_Subcategories_Biproducts
public import Definitions.Def_PretorsionImageClosed_Statement
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_mem_qClosure_iff_inFac
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_mem_sClosure_iff_inSub
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_not_splitMono_of_labels_ne
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_qSet_empty
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_reject_empty
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_sSet_empty
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_trace_empty
public import Theorems.Thm_PretorsionImageClosed_Statement_IsTrivial_mono
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
open CategoryTheory CategoryTheory.Limits
namespace PretorsionImageClosed.IndecomposableSkeleton
universe u v w
variable {R : Type u} [Ring R] [IsNoetherianRing R] {ι : Type v}
  (σ : IndecomposableSkeleton.{u, v, w} R ι)
attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts
theorem inAdd_of_iso {S : Set ι} {X Y : FGModuleCat.{w} R} (e : X ≅ Y) (hX : σ.InAdd S X) :
    σ.InAdd S Y := by
  obtain ⟨P⟩ := hX
  exact ⟨{
    index := P.index, label := P.label, mem := P.mem, iso := e.symm ≪≫ P.iso }⟩
theorem inAdd_biproduct {S : Set ι} (J : FintypeCat.{0}) (F : J → FGModuleCat.{w} R)
    (hF : ∀ j, σ.InAdd S (F j)) : σ.InAdd S (biproduct F) := by
  classical
  let inner : ∀ j : J, σ.AddPresentation S (F j) := fun j ↦ Classical.choice (hF j)
  let K : FintypeCat.{0} := FintypeCat.of (Σ j : J, (inner j).index)
  let a : K → ι := fun p ↦ (inner p.1).label p.2
  let componentIso : (⨁ F) ≅ (⨁ fun j : J ↦ σ.sumOver (inner j).index (inner j).label) :=
    biproduct.mapIso fun j ↦ (inner j).iso
  let flattenIso : (⨁ fun j : J ↦ σ.sumOver (inner j).index (inner j).label) ≅ σ.sumOver K a :=
    biproductBiproductIso (fun j : J ↦ (inner j).index) (fun j t ↦ σ.obj ((inner j).label t))
  exact ⟨{
    index := K
    label := a
    mem := fun p ↦ (inner p.1).mem p.2
    iso := componentIso ≪≫ flattenIso }⟩
theorem index_mem_of_retract_inAdd {S : Set ι} {i : ι} {Y : FGModuleCat.{w} R}
    (r : Retract (σ.obj i) Y) (hY : σ.InAdd S Y) : i ∈ S := by
  classical
  obtain ⟨P⟩ := hY
  let g : σ.obj i ⟶ σ.sumOver P.index P.label := r.i ≫ P.iso.hom
  let s : SplitMono g := { retraction := P.iso.inv ≫ r.r, id := by simp [g] }
  letI : IsSplitMono g := ⟨⟨s⟩⟩
  let Q : σ.SubPresentation S (σ.obj i) :=
    { index := P.index, label := P.label, mem := P.mem, map := g, mono := inferInstance }
  by_contra hi
  have hne : ∀ t, i ≠ Q.label t := by
    intro t hit
    apply hi
    simpa only [Q] using hit ▸ P.mem t
  exact (not_splitMono_of_labels_ne σ Q hne) ⟨s⟩
theorem inAdd_of_retract {S : Set ι} {X Y : FGModuleCat.{w} R} (r : Retract X Y)
    (hY : σ.InAdd S Y) : σ.InAdd S X := by
  classical
  obtain ⟨n, a, ⟨e⟩⟩ := σ.decomposes X
  have ha : ∀ t : Fin n, a t ∈ S := by
    intro t
    let rt : Retract (σ.obj (a t)) X :=
      { i := biproduct.ι (fun j : Fin n ↦ σ.obj (a j)) t ≫ e.inv
        r := e.hom ≫ biproduct.π (fun j : Fin n ↦ σ.obj (a j)) t
        retract := by simp }
    exact index_mem_of_retract_inAdd σ (rt.trans r) hY
  exact ⟨{
    index := FintypeCat.of (Fin n), label := a, mem := ha, iso := e }⟩
def addOf (S : Set ι) : Statement.Subcategory (FGModuleCat.{w} R) where
  prop := σ.InAdd S
  prop_of_retract h hY := inAdd_of_retract σ h hY
  prop_biprod {X Y} hX hY := by
    let f : Fin 2 → FGModuleCat.{w} R := ![X, Y]
    have hf : σ.InAdd S (⨁ f) := inAdd_biproduct σ (FintypeCat.of (Fin 2)) f (by
      intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · exact hX
      · have : j = 0 := Subsingleton.elim _ _
        subst this
        exact hY)
    refine inAdd_of_iso σ ((biproductFinSuccIso f).trans ?_) hf
    exact biprod.mapIso (Iso.refl _) (biproductUniqueIso _)
  prop_of_isZero {X} h := by
    let a : Fin 0 → ι := fun t => t.elim0
    refine ⟨{ index := FintypeCat.of (Fin 0), label := a, mem := (fun t => t.elim0), iso := ?_ }⟩
    refine h.iso ?_
    rw [IsZero.iff_id_eq_zero]
    apply biproduct.hom_ext'
    intro t
    exact t.elim0
def indOf (Z : Statement.Subcategory (FGModuleCat.{w} R)) : Set ι := {i | Z.prop (σ.obj i)}
end PretorsionImageClosed.IndecomposableSkeleton


