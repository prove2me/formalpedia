-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_SplittingOfSandwichAndPairing
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_SplittingOfSandwichAndPairing
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T09:52:03.921101+00:00
-- url     : https://prove2.me/theorems/16d0c86a-d23d-4dbb-b66b-48088b65b4f1
-- title:
--   Splitting Of Sandwich And Pairing
-- statement:
--   Definitions and structural lemmas for Splitting Of Sandwich And Pairing, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/SplittingOfSandwichAndPairing.lean

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.FlB
noncomputable section
namespace GlobalTheory.CompanionTheory.RgSplit
section Lat
variable {L : Type} [NontriviallyNormedField L] {V : Type} [AddCommGroup V] [Module L V]
variable [IsUltrametricDist L]
def latOf {m : ℕ} (b : Module.Basis (Fin m) L V) : AddSubgroup V where
  carrier := {x | ∀ i, ‖b.repr x i‖ ≤ 1}
  add_mem' := fun {x y} hx hy i => by
    simp only [map_add, Finsupp.add_apply]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hx i) (hy i))
  zero_mem' := fun i => by simp
  neg_mem' := fun {x} hx i => by simpa using hx i
def bigLat {V' : Type} [AddCommGroup V'] [Module L V'] (p q : V →ₗ[L] L) (P : V →ₗ[L] V')
    (N : AddSubgroup V') : AddSubgroup V where
  carrier := {x | ‖p x‖ ≤ 1 ∧ ‖q x‖ ≤ 1 ∧ P x ∈ N}
  add_mem' := fun {x y} hx hy => by
    refine ⟨?_, ?_, ?_⟩
    · rw [map_add]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx.1 hy.1)
    · rw [map_add]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx.2.1 hy.2.1)
    · rw [map_add]
      exact N.add_mem hx.2.2 hy.2.2
  zero_mem' := by simp [N.zero_mem]
  neg_mem' := fun {x} hx => by
    refine ⟨?_, ?_, ?_⟩
    · simpa using hx.1
    · simpa using hx.2.1
    · rw [map_neg]
      exact N.neg_mem hx.2.2
end Lat
section Form
variable {L : Type} [NontriviallyNormedField L] {V : Type} [AddCommGroup V] [Module L V]
  {s : L →+* L} {h : V → V → L}
def hlin (hh : IsHerm s h) (x : V) : V →ₗ[L] L where
  toFun := h x
  map_add' := hh.1 x
  map_smul' a y := by simpa using hh.2.1 a x y
@[simp] theorem hlin_apply (hh : IsHerm s h) (x y : V) : hlin hh x y = h x y := rfl
def ca (hh : IsHerm s h) (δ : L) (f : V) : V →ₗ[L] L := (s δ)⁻¹ • hlin hh f
def cb (hh : IsHerm s h) (δ : L) (e : V) : V →ₗ[L] L := δ⁻¹ • hlin hh e
def pr (hh : IsHerm s h) (δ : L) (e f : V) : V →ₗ[L] V :=
  LinearMap.id - (ca hh δ f).smulRight e - (cb hh δ e).smulRight f
theorem ca_apply (hh : IsHerm s h) (δ : L) (f x : V) : ca hh δ f x = (s δ)⁻¹ * h f x := rfl
theorem cb_apply (hh : IsHerm s h) (δ : L) (e x : V) : cb hh δ e x = δ⁻¹ * h e x := rfl
theorem pr_apply (hh : IsHerm s h) (δ : L) (e f x : V) :
    pr hh δ e f x = x - ca hh δ f x • e - cb hh δ e x • f := by
  simp [pr]
variable {δ : L} {e f : V}
theorem h_fe (hh : IsHerm s h) (hef : h e f = δ) : h f e = s δ := by
  rw [hh.2.2.1 e f, hef]
theorem pr_orth (hh : IsHerm s h) (hδ : δ ≠ 0) (he : h e e = 0) (hf : h f f = 0)
    (hef : h e f = δ) (x : V) : h e (pr hh δ e f x) = 0 ∧ h f (pr hh δ e f x) = 0 := by
  have hsδ : s δ ≠ 0 := (map_ne_zero s).2 hδ
  have hfe := h_fe hh hef
  constructor
  · change hlin hh e _ = 0
    rw [pr_apply, map_sub, map_sub, map_smul, map_smul]
    simp only [hlin_apply, he, hef, cb_apply, smul_eq_mul]
    field_simp
    ring
  · change hlin hh f _ = 0
    rw [pr_apply, map_sub, map_sub, map_smul, map_smul]
    simp only [hlin_apply, hf, hfe, ca_apply, smul_eq_mul]
    field_simp
    ring
end Form
section Main
variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L]
  {V : Type} [AddCommGroup V] [Module L V] {s : L →+* L} {h : V → V → L} {δ : L} {e f : V}
variable {U : Submodule L V}
def prU (hh : IsHerm s h) (hδ : δ ≠ 0) (he : h e e = 0) (hf : h f f = 0) (hef : h e f = δ)
    (hU : ∀ x, x ∈ U ↔ h e x = 0 ∧ h f x = 0) : V →ₗ[L] U :=
  LinearMap.codRestrict U (pr hh δ e f) fun x => (hU _).2 (pr_orth hh hδ he hf hef x)
end Main
end GlobalTheory.CompanionTheory.RgSplit


