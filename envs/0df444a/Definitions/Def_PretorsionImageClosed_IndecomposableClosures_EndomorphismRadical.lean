-- Prove2me | Definitions.Def_PretorsionImageClosed_IndecomposableClosures_EndomorphismRadical
-- name    : PretorsionImageClosed_IndecomposableClosures_EndomorphismRadical
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T05:02:40.979121+00:00
-- url     : https://prove2.me/theorems/792fdeca-5c10-4f93-a776-86de8785b57f
-- title:
--   Endomorphism Radical
-- statement:
--   Definitions and structural lemmas for Endomorphism Radical, from Haruhisa Enomoto (haruhisa-enomoto/pretorsion-image-closed; see pinned Apache-2.0 LICENSE)'s pinned Pretorsion theories and image-closed subcategories of finite-dimensional algebras development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/EndomorphismRadical.lean

module
public import Mathlib.RingTheory.Artinian.Ring
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_ModuleTraces
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_mem_qClosure_iff_inFac
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_mem_sClosure_iff_inSub
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_qSet_empty
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_reject_empty
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_sSet_empty
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_trace_empty
public import Theorems.Thm_PretorsionImageClosed_IsIndecomposableModule_nontrivial
public import Theorems.Thm_PretorsionImageClosed_isLocalRing_end_of_isIndecomposable
attribute [local simp] PretorsionImageClosed.IndecomposableSkeleton.mem_qClosure_iff_inFac
attribute [local simp] PretorsionImageClosed.IndecomposableSkeleton.mem_sClosure_iff_inSub
attribute [local simp] PretorsionImageClosed.IndecomposableSkeleton.qSet_empty
attribute [local simp] PretorsionImageClosed.IndecomposableSkeleton.reject_empty
attribute [local simp] PretorsionImageClosed.IndecomposableSkeleton.sSet_empty
attribute [local simp] PretorsionImageClosed.IndecomposableSkeleton.trace_empty


set_option autoImplicit true
@[expose] public section
@[expose] public section
noncomputable section
open Function
namespace PretorsionImageClosed
universe u v
variable {A : Type u} {X : Type v}
variable [Ring A] [AddCommGroup X] [Module A X]
theorem isUnit_right_of_isUnit_comp
    (hXlen : IsFiniteLength A X)
    (f g : Module.End A X)
    (hunit : IsUnit (f.comp g)) :
    IsUnit g := by
  obtain ⟨hNoetherian, hArtinian⟩ :=
    isFiniteLength_iff_isNoetherian_isArtinian.mp hXlen
  letI : IsNoetherian A X := hNoetherian
  letI : IsArtinian A X := hArtinian
  have hcomp_bij : Function.Bijective (f.comp g) :=
    (Module.End.isUnit_iff _).mp hunit
  have hg_inj : Function.Injective g := by
    intro x y hxy
    exact hcomp_bij.1 (by simp [hxy])
  have hg_surj : Function.Surjective g :=
    IsArtinian.surjective_of_injective_endomorphism g hg_inj
  exact (Module.End.isUnit_iff g).mpr ⟨hg_inj, hg_surj⟩
def endNonunitsIdeal
    (hX : PretorsionImageClosed.IsIndecomposableModule A X)
    (hXlen : IsFiniteLength A X) :
    Ideal (Module.End A X) := by
  letI : Nontrivial X := hX.nontrivial
  letI : IsLocalRing (Module.End A X) :=
    PretorsionImageClosed.isLocalRing_end_of_isIndecomposable hXlen hX
  exact
    { carrier := nonunits (Module.End A X)
      zero_mem' := not_isUnit_zero
      add_mem' := fun hx hy ↦ IsLocalRing.nonunits_add hx hy
      smul_mem' := by
        intro f g hg
        change ¬ IsUnit (f * g)
        rw [Module.End.mul_eq_comp]
        exact fun hfg ↦
          hg (isUnit_right_of_isUnit_comp hXlen f g hfg) }
def idealRange (I : Ideal (Module.End A X)) : Submodule A X :=
  ⨆ f : I, LinearMap.range (f : Module.End A X)
def idealKernel (I : Ideal (Module.End A X)) : Submodule A X :=
  ⨅ f : I, LinearMap.ker (f : Module.End A X)
end PretorsionImageClosed


