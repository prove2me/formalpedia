-- Prove2me | Definitions.Def_GroundTheory_LocalFields_PrincipalUnitsRank
-- name    : GroundTheory_LocalFields_PrincipalUnitsRank
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T08:35:09.146544+00:00
-- url     : https://prove2.me/theorems/b94f8938-9b65-508e-9a5a-5ac1ad42d490
-- title:
--   Principal Units Rank
-- statement:
--   Definitions and structural lemmas for Principal Units Rank, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/PrincipalUnitsRank.lean

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_PadicLogLinear
import Definitions.Def_GroundTheory_LocalFields_Integers
import Theorems.Thm_GroundTheory_LocalField_CharZero_valuation_padicHom_padicInt_le_one
import Theorems.Thm_GroundTheory_LocalField_exists_normalizedValuation_eq
import Theorems.Thm_GroundTheory_LocalField_mem_valBall
import Theorems.Thm_GroundTheory_LocalField_mul_mem_valBall
import Theorems.Thm_GroundTheory_LocalField_normalizedValuation_le_one_iff
import Theorems.Thm_GroundTheory_LocalField_padicHom_padicInt_mem_valBall_zero
import Theorems.Thm_GroundTheory_LocalField_padicLog_smul
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply


set_option autoImplicit false
namespace GroundTheory.LocalField
open ValuativeRel IsLocalRing Topology Filter
open scoped WithZero
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
namespace PadicRank
variable (p : ℕ) [hp : Fact p.Prime]
theorem mem_integer_padic_iff (x : ℚ_[p]) : x ∈ 𝒪[ℚ_[p]] ↔ ‖x‖ ≤ 1 := by
  rw [Valuation.mem_integer_iff, ← map_one (valuation ℚ_[p]), ← Valuation.vle_iff_le,
    Valuation.Compatible.vle_iff_le (v := Padic.mulValuation),
    GroundTheory.LocalField.Padic.mulValuation_le_iff_norm_le, norm_one]
noncomputable def padicIntEquivInteger : ℤ_[p] ≃+* 𝒪[ℚ_[p]] where
  toFun x := ⟨x, (mem_integer_padic_iff p x).mpr x.2⟩
  invFun y := ⟨y, (mem_integer_padic_iff p y).mp y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
variable [CharP 𝓀[K] p] [CharZero K]
variable (K) in

noncomputable def padicIntHom : ℤ_[p] →+* K :=
  (CharZero.padicHom K p).comp PadicInt.Coe.ringHom
theorem padicIntHom_mem (a : ℤ_[p]) : padicIntHom K p a ∈ 𝒪[K] :=
  CharZero.valuation_padicHom_padicInt_le_one K p a
variable (K) in

noncomputable def padicIntHomInteger : ℤ_[p] →+* 𝒪[K] :=
  (padicIntHom K p).codRestrict 𝒪[K] (padicIntHom_mem p)
variable (K) in

noncomputable abbrev algebraK : Algebra ℤ_[p] K := (padicIntHom K p).toAlgebra
variable (K) in

noncomputable abbrev algebraInteger : Algebra ℤ_[p] 𝒪[K] := (padicIntHomInteger K p).toAlgebra
attribute [local instance] algebraK algebraInteger
theorem padicIntHom_mem_valBall_zero (a : ℤ_[p]) : padicIntHom K p a ∈ valBall K 0 :=
  padicHom_padicInt_mem_valBall_zero p a
variable (K) in

noncomputable def valBallSubmodule (m : ℤ) : Submodule ℤ_[p] K where
  carrier := valBall K m
  add_mem' := add_mem
  zero_mem' := zero_mem _
  smul_mem' a x hx := by
    rw [Algebra.smul_def]
    have h := mul_mem_valBall (padicIntHom_mem_valBall_zero p a) hx
    rw [zero_add] at h
    exact h
theorem mem_valBallSubmodule {m : ℤ} {x : K} : x ∈ valBallSubmodule K p m ↔ x ∈ valBall K m :=
  Iff.rfl
variable (K) in

noncomputable def valBallSubmoduleZeroEquiv : valBallSubmodule K p 0 ≃ₗ[ℤ_[p]] 𝒪[K] where
  toFun x := ⟨x, mem_integer_of_mem_valBall le_rfl x.2⟩
  invFun y := ⟨y, by
    rw [mem_valBallSubmodule, mem_valBall, neg_zero, WithZero.exp_zero,
      normalizedValuation_le_one_iff]; exact y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
variable (K) in

noncomputable def valBallSubmoduleEquiv (m : ℤ) :
    valBallSubmodule K p 0 ≃ₗ[ℤ_[p]] valBallSubmodule K p m :=
  have hy := exists_normalizedValuation_eq K (-m)
  let y := hy.choose
  have hy0 : y ≠ 0 := by
    intro h
    have := hy.choose_spec
    rw [show hy.choose = y from rfl, h, map_zero] at this
    exact WithZero.exp_ne_zero this.symm
  { toFun x := ⟨y * x, (mem_valBallSubmodule p).mpr (by
      have := mul_mem_valBall (show y ∈ valBall K m by
        rw [mem_valBall, show y = hy.choose from rfl, hy.choose_spec]) x.2
      simpa using this)⟩
    invFun x := ⟨y⁻¹ * x, (mem_valBallSubmodule p).mpr (by
      have := mul_mem_valBall (show y⁻¹ ∈ valBall K (-m) by
        rw [mem_valBall, map_inv₀, show y = hy.choose from rfl, hy.choose_spec,
          ← WithZero.exp_neg]) x.2
      simpa using this)⟩
    left_inv x := by ext; simp [hy0]
    right_inv x := by ext; simp [hy0]
    map_add' x x' := by ext; simp [mul_add]
    map_smul' a x := by
      ext
      simp only [SetLike.val_smul, Algebra.smul_def, RingHom.id_apply]
      ring }
variable (K) in

noncomputable def padicLogLinear : Additive (unitFiltrationUnits K 1) →ₗ[ℤ_[p]] K where
  toFun := padicLog K
  map_add' := map_add _
  map_smul' a u := by
    rw [padicLog_smul p a u, RingHom.id_apply, Algebra.smul_def]
    rfl
end PadicRank
section Rank
open PadicRank
attribute [local instance] algebraK algebraInteger
end Rank
end GroundTheory.LocalField


