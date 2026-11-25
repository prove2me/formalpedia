-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_Artin_PlacesInfinite
-- name    : GroundTheory_GlobalFields_Artin_PlacesInfinite
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T02:46:45.374411+00:00
-- url     : https://prove2.me/theorems/440c6d4a-a094-5b9d-b662-070f2c29f0a4
-- title:
--   Places Infinite
-- statement:
--   Definitions and structural lemmas for Places Infinite, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/PlacesInfinite.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_Places
import Theorems.Thm_GroundTheory_Global_Artin_extendByZero_coe
import Theorems.Thm_GroundTheory_Global_Artin_subfieldPlaceEquiv_mk
import Theorems.Thm_GroundTheory_GroupCoh_doubleCosetMap_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.Artin.extendByZero_coe
attribute [local simp] GroundTheory.Global.Artin.subfieldPlaceEquiv_mk
attribute [local simp] GroundTheory.GroupCoh.doubleCosetMap_mk


set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open scoped Pointwise
open NumberField IntermediateField
namespace GroundTheory.Global.Artin
section Group
variable {G α : Type*} [Group G] [MulAction G α]
end Group
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (H : Subgroup Gal(L/K))
section Aut
def toFixedFieldAlgEquiv (h : H) : Gal(L/fixedField H) :=
  AlgEquiv.ofRingEquiv (f := (h : Gal(L/K)).toRingEquiv)
    (fun m ↦ (mem_fixedField_iff H (m : L)).1 m.2 h h.2)
omit [NumberField K] [NumberField L] [IsGalois K L] in
@[simp]
theorem toFixedFieldAlgEquiv_apply (h : H) (y : L) : toFixedFieldAlgEquiv H h y = (h : Gal(L/K)) y :=
  rfl
omit [IsGalois K L] in

theorem restrictScalars_mem (σ : Gal(L/fixedField H)) : σ.restrictScalars K ∈ H := by
  have hmem : σ.restrictScalars K ∈ fixingSubgroup (fixedField H) :=
    (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun y hy ↦ σ.commutes ⟨y, hy⟩
  exact (IntermediateField.fixingSubgroup_fixedField H).le hmem
omit [NumberField K] [NumberField L] [IsGalois K L] in
theorem smul_infinitePlace_toFixedFieldAlgEquiv (h : H) (w : InfinitePlace L) :
    toFixedFieldAlgEquiv H h • w = (h : Gal(L/K)) • w := by
  refine InfinitePlace.ext _ _ fun y ↦ ?_
  rw [InfinitePlace.smul_eq_comap, InfinitePlace.smul_eq_comap, InfinitePlace.comap_apply,
    InfinitePlace.comap_apply]
  congr 1
end Aut
section Infinite
variable (w : InfinitePlace L)
def subfieldInfinitePlace (x : Gal(L/K)) : InfinitePlace (fixedField H) :=
  (x • w).comap (algebraMap (fixedField H) L)
omit [NumberField K] [NumberField L] in

theorem comap_subfieldInfinitePlace (x : Gal(L/K)) :
    (subfieldInfinitePlace H w x).comap (algebraMap K (fixedField H)) =
      w.comap (algebraMap K L) := by
  rw [subfieldInfinitePlace, ← InfinitePlace.comap_comp, ← IsScalarTower.algebraMap_eq]
  exact ((InfinitePlace.mem_orbit_iff (k := K)).1 ⟨x, rfl⟩).symm
theorem subfieldInfinitePlace_eq_iff (x y : Gal(L/K)) :
    subfieldInfinitePlace H w x = subfieldInfinitePlace H w y ↔
      DoubleCoset.mk H (MulAction.stabilizer Gal(L/K) w) x =
        DoubleCoset.mk H (MulAction.stabilizer Gal(L/K) w) y := by
  rw [DoubleCoset.eq]
  constructor
  · intro hxy
    obtain ⟨σ, hσ⟩ := InfinitePlace.exists_smul_eq_of_comap_eq (k := fixedField H) hxy
    have hh : σ.restrictScalars K • x • w = y • w := hσ
    refine ⟨σ.restrictScalars K, restrictScalars_mem H σ, (y⁻¹ * σ.restrictScalars K * x)⁻¹,
      Subgroup.inv_mem _ ?_, by group⟩
    rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, hh, inv_smul_smul]
  · rintro ⟨h, hh, d, hd, rfl⟩
    rw [subfieldInfinitePlace, subfieldInfinitePlace, mul_smul, mul_smul,
      MulAction.mem_stabilizer_iff.1 hd]
    rw [show h = ((⟨h, hh⟩ : H) : Gal(L/K)) from rfl,
      ← smul_infinitePlace_toFixedFieldAlgEquiv]
    exact (InfinitePlace.mem_orbit_iff (k := fixedField H)).1 ⟨_, rfl⟩
omit [NumberField K] [NumberField L] in

theorem exists_subfieldInfinitePlace_eq (u : InfinitePlace (fixedField H))
    (hu : u.comap (algebraMap K (fixedField H)) = w.comap (algebraMap K L)) :
    ∃ x : Gal(L/K), subfieldInfinitePlace H w x = u := by
  obtain ⟨w', rfl⟩ := InfinitePlace.comap_surjective (k := fixedField H) (K := L) u
  dsimp only at hu
  have h' : w.comap (algebraMap K L) = w'.comap (algebraMap K L) := by
    rw [← hu, ← InfinitePlace.comap_comp, ← IsScalarTower.algebraMap_eq]
  obtain ⟨x, hx⟩ := InfinitePlace.exists_smul_eq_of_comap_eq h'
  exact ⟨x, by rw [subfieldInfinitePlace, hx]⟩
def subfieldInfinitePlaceEquiv :
    DoubleCoset.Quotient (H : Set Gal(L/K)) (MulAction.stabilizer Gal(L/K) w) ≃
      {u : InfinitePlace (fixedField H) //
        u.comap (algebraMap K (fixedField H)) = w.comap (algebraMap K L)} :=
  Equiv.ofBijective
    (Quotient.lift (fun x ↦ ⟨subfieldInfinitePlace H w x, comap_subfieldInfinitePlace H w x⟩)
      (fun a b hab ↦ Subtype.ext ((subfieldInfinitePlace_eq_iff H w a b).2 (Quotient.sound hab))))
    ⟨by
      rintro ⟨a⟩ ⟨b⟩ hab
      exact (subfieldInfinitePlace_eq_iff H w a b).1 (congrArg Subtype.val hab),
    by
      rintro ⟨u, hu⟩
      obtain ⟨x, hx⟩ := exists_subfieldInfinitePlace_eq H w u hu
      exact ⟨DoubleCoset.mk _ _ x, Subtype.ext hx⟩⟩
end Infinite
end GroundTheory.Global.Artin


