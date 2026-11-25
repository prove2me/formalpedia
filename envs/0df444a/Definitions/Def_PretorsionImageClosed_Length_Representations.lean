-- Prove2me | Definitions.Def_PretorsionImageClosed_Length_Representations
-- name    : PretorsionImageClosed_Length_Representations
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T01:15:48.758926+00:00
-- url     : https://prove2.me/theorems/0f7b41ab-d2c0-4d27-b39a-4b8670870820
-- title:
--   Representations
-- statement:
--   Definitions and structural lemmas for Representations, from Haruhisa Enomoto (haruhisa-enomoto/pretorsion-image-closed; see pinned Apache-2.0 LICENSE)'s pinned Pretorsion theories and image-closed subcategories of finite-dimensional algebras development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Length/Representations.lean

module
public import Definitions.Def_PretorsionImageClosed_Length_Basic
public import Definitions.Def_PretorsionImageClosed_Modules_FiniteModules
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Theorems.Thm_PretorsionImageClosed_FGModuleCat_epi_iff_surjective
public import Theorems.Thm_PretorsionImageClosed_FGModuleCat_isIso_iff_bijective
public import Theorems.Thm_PretorsionImageClosed_FGModuleCat_isZero_iff_subsingleton
public import Theorems.Thm_PretorsionImageClosed_FGModuleCat_mono_iff_injective
public import Theorems.Thm_PretorsionImageClosed_length_eq_of_iso
public import Theorems.Thm_PretorsionImageClosed_length_eq_zero_iff
public import Theorems.Thm_PretorsionImageClosed_length_lt_of_epi
public import Theorems.Thm_PretorsionImageClosed_length_lt_of_mono

set_option autoImplicit true
@[expose] public section
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace PretorsionImageClosed
open CategoryTheory Limits
namespace Representations
variable {k : Type*} [Field k] {J : Type*} [Category J] [Fintype J]
def totalDim (X : J ⥤ FGModuleCat k) : ℕ := ∑ j, Module.finrank k (X.obj j)
theorem finrank_le_of_mono {X Y : FGModuleCat k} (f : X ⟶ Y) [Mono f] :
    Module.finrank k X ≤ Module.finrank k Y :=
  LinearMap.finrank_le_finrank_of_injective ((FGModuleCat.mono_iff_injective f).1 inferInstance)
theorem finrank_lt_of_mono {X Y : FGModuleCat k} (f : X ⟶ Y) [Mono f] (h : ¬ IsIso f) :
    Module.finrank k X < Module.finrank k Y := by
  have hinj := (FGModuleCat.mono_iff_injective f).1 inferInstance
  have hns : LinearMap.range f.hom.hom ≠ ⊤ := fun ht =>
    h ((FGModuleCat.isIso_iff_bijective f).2 ⟨hinj, LinearMap.range_eq_top.1 ht⟩)
  rw [← LinearMap.finrank_range_of_inj hinj]
  exact Submodule.finrank_lt hns
theorem finrank_le_of_epi {X Y : FGModuleCat k} (f : X ⟶ Y) [Epi f] :
    Module.finrank k Y ≤ Module.finrank k X := by
  have hs := (FGModuleCat.epi_iff_surjective f).1 inferInstance
  have := LinearMap.finrank_range_add_finrank_ker f.hom.hom
  rw [LinearMap.range_eq_top.2 hs, finrank_top] at this
  change Module.finrank k Y.obj ≤ Module.finrank k X.obj
  omega
theorem finrank_lt_of_epi {X Y : FGModuleCat k} (f : X ⟶ Y) [Epi f] (h : ¬ IsIso f) :
    Module.finrank k Y < Module.finrank k X := by
  have hs := (FGModuleCat.epi_iff_surjective f).1 inferInstance
  have hk : LinearMap.ker f.hom.hom ≠ ⊥ := fun hb =>
    h ((FGModuleCat.isIso_iff_bijective f).2 ⟨LinearMap.ker_eq_bot.1 hb, hs⟩)
  have hpos : 0 < Module.finrank k (LinearMap.ker f.hom.hom) :=
    Nat.pos_of_ne_zero (fun h0 => hk (Submodule.finrank_eq_zero.1 h0))
  have := LinearMap.finrank_range_add_finrank_ker f.hom.hom
  rw [LinearMap.range_eq_top.2 hs, finrank_top] at this
  change Module.finrank k Y.obj < Module.finrank k X.obj
  omega
instance : HasLength (J ⥤ FGModuleCat k) where
  length := totalDim
  length_eq_zero_iff X := by
    rw [totalDim, Finset.sum_eq_zero_iff, Functor.isZero_iff]
    simp only [Finset.mem_univ, true_implies]
    refine forall_congr' fun j => ?_
    rw [FGModuleCat.isZero_iff_subsingleton, Module.finrank_zero_iff]
  length_eq_of_iso e := by
    change totalDim _ = totalDim _
    exact Finset.sum_congr rfl fun j _ =>
      LinearEquiv.finrank_eq (FGModuleCat.isoToLinearEquiv (e.app j))
  length_lt_of_mono {X Y} f hf hni := by
    change totalDim X < totalDim Y
    rw [NatTrans.mono_iff_mono_app] at hf
    have : ∃ j, ¬ IsIso (f.app j) := not_forall.1 fun h => by
      haveI := h
      exact hni (NatIso.isIso_of_isIso_app f)
    obtain ⟨j, hj⟩ := this
    refine Finset.sum_lt_sum (fun i _ => ?_) ⟨j, Finset.mem_univ _, ?_⟩
    · haveI := hf i
      exact finrank_le_of_mono (f.app i)
    · haveI := hf j
      exact finrank_lt_of_mono (f.app j) hj
  length_lt_of_epi {X Y} f hf hni := by
    change totalDim Y < totalDim X
    rw [NatTrans.epi_iff_epi_app] at hf
    have : ∃ j, ¬ IsIso (f.app j) := not_forall.1 fun h => by
      haveI := h
      exact hni (NatIso.isIso_of_isIso_app f)
    obtain ⟨j, hj⟩ := this
    refine Finset.sum_lt_sum (fun i _ => ?_) ⟨j, Finset.mem_univ _, ?_⟩
    · haveI := hf i
      exact finrank_le_of_epi (f.app i)
    · haveI := hf j
      exact finrank_lt_of_epi (f.app j) hj
end Representations
end PretorsionImageClosed


