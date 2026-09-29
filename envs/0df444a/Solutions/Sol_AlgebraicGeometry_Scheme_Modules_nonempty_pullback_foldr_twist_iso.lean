-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.nonempty_pullback_foldr_twist_iso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/0eb5f288-b24a-5f54-b6cf-3ee753e2fef9

import Mathlib
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_IdealSheafModuleMaps
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicCurve_RelCartier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_mul
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isIso_pullbackModuleComparison
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_pullback_invModule_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_foldr_twist_iso

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_foldr_twist_iso.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.pullback Scheme Scheme.Modules Scheme.IdealSheafData Scheme.IdealSheafData.module Scheme.IdealSheafData.invModule"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Modules.pullback empty Modules IdealSheafData IdealSheafData.module IdealSheafData.invModule"
namespace IdealSheafData
p2m_export "AlgebraicGeometry.Scheme.IdealSheafData" "one_eq_top comap_top ideal comap module invModule pullbackModuleComparison IsInvertible isInvertible_top IsInvertible.mul comap_mul IsInvertible.isIso_pullbackModuleComparison IsInvertible.nonempty_pullback_invModule_iso IsInvertible.pow"
p2m_open "AlgebraicGeometry.Scheme.IdealSheafData AlgebraicGeometry.Scheme AlgebraicGeometry"

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

theorem comap_pow (I : Y.IdealSheafData) (n : ℕ) : (I ^ n).comap f = I.comap f ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, one_eq_top, comap_top]; rfl
  | succ k ih => rw [pow_succ, pow_succ, comap_mul, ih]

theorem comap_finset_prod {ι : Type*} (s : Finset ι) (I : ι → Y.IdealSheafData) :
    (∏ i ∈ s, I i).comap f = ∏ i ∈ s, (I i).comap f := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.prod_empty, one_eq_top, comap_top]; rfl
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, comap_mul, ih]

namespace IsInvertible p2m_export "AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible" "mul isIso_pullbackModuleComparison nonempty_pullback_invModule_iso pow" end IsInvertible
p2m_open_scoped "AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible" in
theorem IsInvertible.finset_prod {ι : Type*} (s : Finset ι) (I : ι → Y.IdealSheafData)
    (hI : ∀ i ∈ s, (I i).IsInvertible) : (∏ i ∈ s, I i).IsInvertible := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty]; exact isInvertible_top
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact IsInvertible.mul (hI a (Finset.mem_insert_self a s)) (ih fun i hi => hI i (Finset.mem_insert_of_mem hi))

namespace IsInvertible
p2m_open_scoped "AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible" in

private noncomputable def _root_.AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.pullbackModuleIso {I : Y.IdealSheafData} (hI : I.IsInvertible)
    (hI' : (I.comap f).IsInvertible) : (Scheme.Modules.pullback f).obj I.module ≅ (I.comap f).module :=
  @asIso _ _ _ _ (I.pullbackModuleComparison f) (IsInvertible.isIso_pullbackModuleComparison f hI hI')

end IsInvertible
p2m_export "AlgebraicGeometry.Scheme.IdealSheafData" "IsInvertible.pullbackModuleIso"
namespace IsInvertible
p2m_open_scoped "AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible" in

private noncomputable def _root_.AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.pullbackInvModuleIso {I : Y.IdealSheafData} (hI : I.IsInvertible)
    (hI' : (I.comap f).IsInvertible) : (Scheme.Modules.pullback f).obj I.invModule ≅ (I.comap f).invModule :=
  (IsInvertible.nonempty_pullback_invModule_iso f hI hI').some

end IsInvertible
p2m_export "AlgebraicGeometry.Scheme.IdealSheafData" "IsInvertible.pullbackInvModuleIso"
end AlgebraicGeometry.Scheme.IdealSheafData

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.pullback Scheme Scheme.Modules Scheme.IdealSheafData Scheme.IdealSheafData.module Scheme.IdealSheafData.invModule"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Modules.pullback empty Modules IdealSheafData IdealSheafData.module IdealSheafData.invModule"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "pullback IsInvertible pullbackTensorObjIso"
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

p2m_open "AlgebraicGeometry.Scheme.IdealSheafData P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_foldr_twist_iso.AlgebraicGeometry.Scheme.IdealSheafData"

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

theorem nonempty_pullback_prod_pow_twist_iso {ι : Type*} [Fintype ι] (C : ι → Y.IdealSheafData)
    (aplus aminus : ι → ℕ) (hC : ∀ F, (C F).IsInvertible) (hC' : ∀ F, ((C F).comap f).IsInvertible) :
    Nonempty ((Scheme.Modules.pullback f).obj
        ((∏ F, C F ^ aplus F).invModule ⊗ (∏ F, C F ^ aminus F).module) ≅
      (∏ F, (C F).comap f ^ aplus F).invModule ⊗ (∏ F, (C F).comap f ^ aminus F).module) := by
  have hprod : ∀ a : ι → ℕ, (∏ F, C F ^ a F).IsInvertible := fun a =>
    IsInvertible.finset_prod _ _ fun F _ => IsInvertible.pow (hC F) _
  have hcomap : ∀ a : ι → ℕ, (∏ F, C F ^ a F).comap f = ∏ F, (C F).comap f ^ a F := fun a => by
    rw [comap_finset_prod]
    exact Finset.prod_congr rfl fun F _ => comap_pow f (C F) (a F)
  have hprod' : ∀ a : ι → ℕ, ((∏ F, C F ^ a F).comap f).IsInvertible := fun a => by
    rw [hcomap]; exact IsInvertible.finset_prod _ _ fun F _ => IsInvertible.pow (hC' F) _
  exact ⟨pullbackTensorObjIso f _ _ ≪≫
    (((hprod aplus).pullbackInvModuleIso f (hprod' aplus) ≪≫
        eqToIso (congrArg Scheme.IdealSheafData.invModule (hcomap aplus))) ⊗ᵢ
      ((hprod aminus).pullbackModuleIso f (hprod' aminus) ≪≫
        eqToIso (congrArg Scheme.IdealSheafData.module (hcomap aminus))))⟩

theorem nonempty_pullback_foldr_twist_iso {m : ℕ} (K : Fin m → Y.IdealSheafData) (pos neg : Fin m → ℕ)
    {ι : Type*} [Fintype ι] (C : ι → Y.IdealSheafData) (aplus aminus : ι → ℕ)
    (hK : ∀ j, (K j).IsInvertible) (hC : ∀ F, (C F).IsInvertible)
    (hK' : ∀ j, ((K j).comap f).IsInvertible) (hC' : ∀ F, ((C F).comap f).IsInvertible) :
    Nonempty ((Scheme.Modules.pullback f).obj
        ((List.finRange m).foldr (fun j N => (K j ^ pos j).invModule ⊗ (K j ^ neg j).module ⊗ N)
          ((∏ F, C F ^ aplus F).invModule ⊗ (∏ F, C F ^ aminus F).module)) ≅
      (List.finRange m).foldr (fun j N => ((K j).comap f ^ pos j).invModule ⊗ ((K j).comap f ^ neg j).module ⊗ N)
        ((∏ F, (C F).comap f ^ aplus F).invModule ⊗ (∏ F, (C F).comap f ^ aminus F).module)) := by
  suffices key : ∀ l : List (Fin m), Nonempty ((Scheme.Modules.pullback f).obj
        (l.foldr (fun j N => (K j ^ pos j).invModule ⊗ (K j ^ neg j).module ⊗ N)
          ((∏ F, C F ^ aplus F).invModule ⊗ (∏ F, C F ^ aminus F).module)) ≅
      l.foldr (fun j N => ((K j).comap f ^ pos j).invModule ⊗ ((K j).comap f ^ neg j).module ⊗ N)
        ((∏ F, (C F).comap f ^ aplus F).invModule ⊗ (∏ F, (C F).comap f ^ aminus F).module)) from key _
  intro l
  induction l with
  | nil => exact nonempty_pullback_prod_pow_twist_iso f C aplus aminus hC hC'
  | cons j l ih =>
    obtain ⟨e⟩ := ih
    have hp : ∀ n : ℕ, (K j ^ n).IsInvertible := fun n => IsInvertible.pow (hK j) n
    have hp' : ∀ n : ℕ, ((K j ^ n).comap f).IsInvertible := fun n => by
      rw [comap_pow]; exact IsInvertible.pow (hK' j) n
    simp only [List.foldr_cons]
    exact ⟨pullbackTensorObjIso f _ _ ≪≫
      (((hp (pos j)).pullbackInvModuleIso f (hp' (pos j)) ≪≫
          eqToIso (congrArg Scheme.IdealSheafData.invModule (comap_pow f (K j) (pos j)))) ⊗ᵢ
        (pullbackTensorObjIso f _ _ ≪≫
          (((hp (neg j)).pullbackModuleIso f (hp' (neg j)) ≪≫
              eqToIso (congrArg Scheme.IdealSheafData.module (comap_pow f (K j) (neg j)))) ⊗ᵢ e)))⟩

end AlgebraicGeometry.Scheme.Modules

open _root_.AlgebraicGeometry.Scheme.Modules _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_foldr_twist_iso.AlgebraicGeometry.Scheme.Modules in
theorem solution
    {X Y : Scheme.{u}} (f : X ⟶ Y) {m : ℕ} (K : Fin m → Y.IdealSheafData) (pos neg : Fin m → ℕ)
    {ι : Type*} [Fintype ι] (C : ι → Y.IdealSheafData) (aplus aminus : ι → ℕ)
    (hK : ∀ j, (K j).IsInvertible) (hC : ∀ F, (C F).IsInvertible)
    (hK' : ∀ j, ((K j).comap f).IsInvertible) (hC' : ∀ F, ((C F).comap f).IsInvertible) :
    Nonempty ((Scheme.Modules.pullback f).obj
        ((List.finRange m).foldr (fun j N => (K j ^ pos j).invModule ⊗ (K j ^ neg j).module ⊗ N)
          ((∏ F, C F ^ aplus F).invModule ⊗ (∏ F, C F ^ aminus F).module)) ≅
      (List.finRange m).foldr (fun j N => ((K j).comap f ^ pos j).invModule ⊗ ((K j).comap f ^ neg j).module ⊗ N)
        ((∏ F, (C F).comap f ^ aplus F).invModule ⊗ (∏ F, (C F).comap f ^ aminus F).module)) :=
  AlgebraicGeometry.Scheme.Modules.nonempty_pullback_foldr_twist_iso f K pos neg C aplus aminus hK hC hK' hC'

end S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_foldr_twist_iso
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_foldr_twist_iso (solution)
