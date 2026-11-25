-- Prove2me | Definitions.Def_GroundTheory_LocalFields_CompleteTrivialLocal
-- name    : GroundTheory_LocalFields_CompleteTrivialLocal
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T01:03:42.988553+00:00
-- url     : https://prove2.me/theorems/00567d7a-ab0d-4dd4-848e-83769bdb7dc8
-- title:
--   Complete Trivial Local
-- statement:
--   Definitions and structural lemmas for Complete Trivial Local, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/CompleteTrivialLocal.lean

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivial
import Definitions.Def_GroundTheory_LocalFields_NormalLattice
import Theorems.Thm_GroundTheory_LocalField_StableFiltration_coe_smul_F
import Theorems.Thm_GroundTheory_LocalField_algEquiv_mem_normalLattice
import Theorems.Thm_GroundTheory_LocalField_exists_unit_one_add
import Theorems.Thm_GroundTheory_LocalField_mul_mem_normalLattice_succ
import Theorems.Thm_GroundTheory_LocalField_normalLattice_antitone
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.StableFiltration.coe_smul_F


set_option autoImplicit false
noncomputable section
namespace GroundTheory.LocalField
open ValuativeRel Finset
section Action
variable {K L : Type*} [Field K] [Field L] [Algebra K L] [ValuativeRel L]
abbrev unitVal (u : 𝒪[L]ˣ) : L := ((u : 𝒪[L]) : L)
theorem unitVal_injective : Function.Injective (unitVal (L := L)) :=
  fun _ _ h => Units.ext (Subtype.ext h)
variable (V : Subgroup 𝒪[L]ˣ)
  (hV : ∀ σ : Gal(L/K), ∀ u ∈ V, ∃ w ∈ V, unitVal w = σ (unitVal u))
def stableSMul (σ : Gal(L/K)) (u : V) : V :=
  ⟨(hV σ u u.2).choose, (hV σ u u.2).choose_spec.1⟩
theorem unitVal_stableSMul (σ : Gal(L/K)) (u : V) :
    unitVal (stableSMul V hV σ u : 𝒪[L]ˣ) = σ (unitVal u) :=
  (hV σ u u.2).choose_spec.2
@[instance_reducible]
def stableUnitsAction : MulDistribMulAction Gal(L/K) V where
  smul := stableSMul V hV
  one_smul u := Subtype.ext (unitVal_injective (by
    show unitVal (stableSMul V hV 1 u : 𝒪[L]ˣ) = unitVal u
    rw [unitVal_stableSMul, AlgEquiv.one_apply]))
  mul_smul σ τ u := Subtype.ext (unitVal_injective (by
    show unitVal (stableSMul V hV (σ * τ) u : 𝒪[L]ˣ) =
      unitVal (stableSMul V hV σ (stableSMul V hV τ u) : 𝒪[L]ˣ)
    rw [unitVal_stableSMul, unitVal_stableSMul, unitVal_stableSMul, AlgEquiv.mul_apply]))
  smul_mul σ u w := Subtype.ext (unitVal_injective (by
    show unitVal (stableSMul V hV σ (u * w) : 𝒪[L]ˣ) =
      unitVal ((stableSMul V hV σ u * stableSMul V hV σ w : V) : 𝒪[L]ˣ)
    rw [unitVal_stableSMul]
    simp only [unitVal, Subgroup.coe_mul, Units.val_mul, Subring.coe_mul] at *
    rw [map_mul]
    exact congrArg₂ (· * ·) ((hV σ u u.2).choose_spec.2).symm ((hV σ w w.2).choose_spec.2).symm))
  smul_one σ := Subtype.ext (unitVal_injective (by
    show unitVal (stableSMul V hV σ 1 : 𝒪[L]ˣ) = unitVal ((1 : V) : 𝒪[L]ˣ)
    rw [unitVal_stableSMul]
    simp [unitVal]))
theorem unitVal_smul (σ : Gal(L/K)) (u : V) :
    letI := stableUnitsAction V hV
    unitVal ((σ • u : V) : 𝒪[L]ˣ) = σ (unitVal u) :=
  (hV σ u u.2).choose_spec.2
end Action
section Data
variable (K L : Type*) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
  [FiniteDimensional K L]
structure NormalLatticeData where

  π : 𝒪[K]
  irreducible : Irreducible π

  θ : L
  linearIndependent : LinearIndependent K fun σ : Gal(L/K) => σ θ
  integer : ∀ σ : Gal(L/K), σ θ ∈ 𝒪[L]

  r : ℕ
  mul_mem : ∀ σ τ : Gal(L/K), π ^ r • (σ θ * τ θ) ∈ normalLattice π θ 0
namespace NormalLatticeData
variable {K L} (D : NormalLatticeData K L)
abbrev lat (s : ℕ) : Submodule 𝒪[K] L := normalLattice D.π D.θ s
abbrev k : ℕ := D.r + 1
omit [FiniteDimensional K L] in
theorem lat_antitone {s t : ℕ} (h : s ≤ t) : D.lat t ≤ D.lat s := normalLattice_antitone _ _ h
theorem mul_mem_lat {s t : ℕ} (hs : D.k ≤ s) {x y : L} (hx : x ∈ D.lat s) (hy : y ∈ D.lat t) :
    x * y ∈ D.lat (t + 1) :=
  mul_mem_normalLattice_succ D.π D.θ D.mul_mem (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hs) hx hy
variable [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeExtension K L]
theorem exists_unit {s : ℕ} (hs : D.k ≤ s) {x : L} (hx : x ∈ D.lat s) :
    ∃ u : 𝒪[L]ˣ, unitVal u = 1 + x ∧ unitVal u⁻¹ - 1 ∈ D.lat s :=
  exists_unit_one_add D.irreducible D.linearIndependent D.integer D.mul_mem
    (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hs) hx
def units (j : ℕ) : Subgroup 𝒪[L]ˣ where
  carrier := {u | unitVal u - 1 ∈ D.lat (D.k + j)}
  one_mem' := by
    show unitVal (1 : 𝒪[L]ˣ) - 1 ∈ D.lat (D.k + j)
    simp [unitVal]
  mul_mem' {u w} hu hw := by
    have e : unitVal (u * w) - 1 = (unitVal u - 1) + (unitVal w - 1) +
        (unitVal u - 1) * (unitVal w - 1) := by
      simp only [unitVal, Units.val_mul, Subring.coe_mul]
      ring
    show unitVal (u * w) - 1 ∈ D.lat (D.k + j)
    rw [e]
    exact add_mem (add_mem hu hw)
      (D.lat_antitone (Nat.le_succ _) (D.mul_mem_lat (Nat.le_add_right _ _) hu hw))
  inv_mem' {u} hu := by
    obtain ⟨v, hv, hvi⟩ := D.exists_unit (Nat.le_add_right _ j) hu
    have : v = u := unitVal_injective (by rw [hv]; ring)
    rw [← this]
    exact hvi
theorem mem_units {j : ℕ} {u : 𝒪[L]ˣ} : u ∈ D.units j ↔ unitVal u - 1 ∈ D.lat (D.k + j) := Iff.rfl
theorem units_antitone : Antitone D.units := fun _ _ h _ hu =>
  D.lat_antitone (by omega) hu
theorem exists_mem_units_eq (j : ℕ) (σ : Gal(L/K)) {u : 𝒪[L]ˣ} (hu : u ∈ D.units j) :
    ∃ w ∈ D.units j, unitVal w = σ (unitVal u) := by
  have hx : σ (unitVal u - 1) ∈ D.lat (D.k + j) := algEquiv_mem_normalLattice _ _ σ hu
  obtain ⟨w, hw, -⟩ := D.exists_unit (Nat.le_add_right _ j) hx
  refine ⟨w, ?_, ?_⟩
  · rw [mem_units, hw, add_sub_cancel_left]
    exact hx
  · rw [hw, map_sub, map_one]
    ring
end NormalLatticeData
variable [TopologicalSpace K] [IsNonarchimedeanLocalField K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [ValuativeExtension K L] [IsGalois K L]
end Data
section Units
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
namespace NormalLatticeData
variable (D : NormalLatticeData K L)
theorem units_zero_stable :
    ∀ σ : Gal(L/K), ∀ u ∈ D.units 0, ∃ w ∈ D.units 0, unitVal w = σ (unitVal u) :=
  fun σ _ hu => D.exists_mem_units_eq 0 σ hu
@[instance_reducible]
def action : MulDistribMulAction Gal(L/K) (D.units 0) :=
  stableUnitsAction (D.units 0) D.units_zero_stable
attribute [local instance] action
abbrev val (x : D.units 0) : L := unitVal (x : 𝒪[L]ˣ)
theorem val_one : D.val 1 = 1 := by simp [val, unitVal]
theorem val_mul (x y : D.units 0) : D.val (x * y) = D.val x * D.val y := by
  simp [val, unitVal]
theorem val_smul (σ : Gal(L/K)) (x : D.units 0) : D.val (σ • x) = σ (D.val x) :=
  unitVal_smul (D.units 0) D.units_zero_stable σ x
def filt : StableFiltration Gal(L/K) (D.units 0) where
  F j := (D.units j).subgroupOf (D.units 0)
  antitone := fun _ _ h _ hx => D.units_antitone h hx
  smul_mem j σ {x} hx := by
    show D.val (σ • x) - 1 ∈ D.lat (D.k + j)
    rw [val_smul, ← map_one σ, ← map_sub]
    exact algEquiv_mem_normalLattice _ _ σ hx
theorem mem_filt {j : ℕ} {x : D.units 0} : x ∈ D.filt.F j ↔ D.val x - 1 ∈ D.lat (D.k + j) :=
  Iff.rfl
end NormalLatticeData
end Units
section Graded
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
namespace NormalLatticeData
variable (D : NormalLatticeData K L)
attribute [local instance] action
abbrev Q (j : ℕ) : AddSubgroup L := (D.lat (D.k + j + 1)).toAddSubgroup
def grHom (j : ℕ) : D.filt.F j →* Multiplicative (L ⧸ D.Q j) where
  toFun x := Multiplicative.ofAdd ((D.val x - 1 : L) : L ⧸ D.Q j)
  map_one' := by simp [val_one]
  map_mul' x y := by
    rw [← ofAdd_add, ← QuotientAddGroup.mk_add]
    congr 1
    rw [QuotientAddGroup.eq_iff_sub_mem, Submodule.mem_toAddSubgroup]
    have e : D.val ((x * y : D.filt.F j) : D.units 0) - 1 - ((D.val x - 1) + (D.val y - 1)) =
        (D.val x - 1) * (D.val y - 1) := by
      rw [Subgroup.coe_mul, val_mul]
      ring
    rw [e]
    exact D.mul_mem_lat (Nat.le_add_right _ _) (D.mem_filt.mp x.2) (D.mem_filt.mp y.2)
end NormalLatticeData
end Graded
section Main
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L]
namespace NormalLatticeData
variable (D : NormalLatticeData K L)
attribute [local instance] action
end NormalLatticeData
end Main
end GroundTheory.LocalField


