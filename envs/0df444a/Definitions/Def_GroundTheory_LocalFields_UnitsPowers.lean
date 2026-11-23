-- Prove2me | Definitions.Def_GroundTheory_LocalFields_UnitsPowers
-- name    : GroundTheory_LocalFields_UnitsPowers
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T07:23:00.539199+00:00
-- url     : https://prove2.me/theorems/82f9385d-1c1e-403b-b063-ae066ce41692
-- title:
--   Units Powers
-- statement:
--   Definitions and structural lemmas for Units Powers, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnitsPowers.lean

import Theorems.Thm_P2M_UpperTheory_Reformulated_B_AdicCompleteRootExistence_exists_root_of_dvd__8130b8fccf10
import Mathlib
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsRootOfAdicComplete
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.LocalField
open ValuativeRel IsLocalRing Polynomial
open scoped WithZero
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {K}
theorem exists_root_of_dvd {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) (f : 𝒪[K][X]) (a : 𝒪[K]) (k : ℕ)
    (ε : 𝒪[K]ˣ) (hd : f.derivative.eval a = ϖ ^ k * ε) (hf : ϖ ^ (2 * k + 1) ∣ f.eval a) :
    ∃ b, f.eval b = 0 ∧ ϖ ^ (k + 1) ∣ b - a :=
  _root_.P2M_UpperTheory_Reformulated_B_AdicCompleteRootExistence_exists_root_of_dvd__8130b8fccf10 hϖ f a k ε hd hf
theorem eq_one_of_pow_eq_one {m : ℕ} (hm : (m : 𝓀[K]) ≠ 0) {u : 𝒪[K]ˣ}
    (hu : u ∈ unitFiltration K 1) (h : u ^ m = 1) : u = 1 := by
  have hres : residue 𝒪[K] (u : 𝒪[K]) = 1 := by
    have := (residue_eq_zero_iff _).mpr (by have := mem_unitFiltration.mp hu; rwa [pow_one] at this)
    rwa [map_sub, map_one, sub_eq_zero] at this
  have hgeom := geom_sum_mul (u : 𝒪[K]) m
  rw [← Units.val_pow_eq_pow_val, h, Units.val_one, sub_self] at hgeom
  have hS : IsUnit (∑ i ∈ Finset.range m, (u : 𝒪[K]) ^ i) := by
    rw [← residue_ne_zero_iff_isUnit]
    simpa [map_sum, hres] using hm
  have := (hS.mul_right_eq_zero).mp hgeom
  ext
  simpa [sub_eq_zero] using this
section Teichmuller
variable (K)
theorem one_lt_card_residueField : 1 < Nat.card 𝓀[K] := Finite.one_lt_card
theorem natCast_card_residueField_sub_one_ne_zero : ((Nat.card 𝓀[K] - 1 : ℕ) : 𝓀[K]) ≠ 0 := by
  have : Fintype 𝓀[K] := Fintype.ofFinite _
  have hq : ((Nat.card 𝓀[K] : ℕ) : 𝓀[K]) = 0 := by
    rw [Nat.card_eq_fintype_card]; exact FiniteField.cast_card_eq_zero _
  rw [Nat.cast_sub (one_lt_card_residueField K).le, hq, Nat.cast_one, zero_sub]
  exact neg_ne_zero.mpr one_ne_zero
variable {K}
theorem exists_teichmuller_lift (ζ : 𝓀[K]ˣ) :
    ∃ u : 𝒪[K]ˣ, u ^ (Nat.card 𝓀[K] - 1) = 1 ∧ unitsToResidue K u = ζ := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  set n := Nat.card 𝓀[K] - 1 with hn
  have hn0 : n ≠ 0 := by have := one_lt_card_residueField K; omega
  obtain ⟨a, ha⟩ := residue_surjective (ζ : 𝓀[K])
  have hζ : ζ ^ n = 1 := by
    rw [hn, ← Nat.card_units]; exact pow_card_eq_one'
  set f : 𝒪[K][X] := X ^ n - 1
  have hfa : f.eval a ∈ 𝓂[K] := by
    rw [← residue_eq_zero_iff]
    simp [f, ha, ← Units.val_pow_eq_pow_val, hζ]
  have hd : IsUnit (f.derivative.eval a) := by
    rw [← residue_ne_zero_iff_isUnit]
    simp only [f, derivative_sub, derivative_X_pow, derivative_one, sub_zero, eval_mul,
      eval_pow, eval_X, eval_natCast, map_mul, map_natCast, map_pow, ha]
    exact mul_ne_zero (natCast_card_residueField_sub_one_ne_zero K) (pow_ne_zero _ ζ.ne_zero)
  obtain ⟨b, hb, hba⟩ := exists_root_of_dvd hϖ f a 0 hd.unit (by simp)
    (by simpa using (mem_maximalIdeal_iff_dvd hϖ).mp hfa)
  have hbn : b ^ n = 1 := by simpa [f, sub_eq_zero] using hb
  have hbu : IsUnit b := (isUnit_pow_iff hn0).mp (hbn ▸ isUnit_one)
  refine ⟨hbu.unit, ?_, ?_⟩
  · ext; simp [hbn]
  · ext
    rw [coe_unitsToResidue, IsUnit.unit_spec, ← ha, ← sub_eq_zero, ← map_sub,
      residue_eq_zero_iff, mem_maximalIdeal_iff_dvd hϖ]
    simpa using hba
theorem eq_of_pow_card_sub_one {u w : 𝒪[K]ˣ} (hu : u ^ (Nat.card 𝓀[K] - 1) = 1)
    (hw : w ^ (Nat.card 𝓀[K] - 1) = 1) (h : unitsToResidue K u = unitsToResidue K w) :
    u = w := by
  have hmem : u * w⁻¹ ∈ unitFiltration K 1 := by
    rw [← ker_unitsToResidue, MonoidHom.mem_ker, map_mul, map_inv, h, mul_inv_cancel]
  have := eq_one_of_pow_eq_one (natCast_card_residueField_sub_one_ne_zero K) hmem
    (by rw [mul_pow, inv_pow, hu, hw, inv_one, mul_one])
  rwa [mul_inv_eq_one] at this
variable (K)
noncomputable def teichmuller : 𝓀[K]ˣ →* 𝒪[K]ˣ where
  toFun ζ := (exists_teichmuller_lift ζ).choose
  map_one' := eq_of_pow_card_sub_one (exists_teichmuller_lift 1).choose_spec.1 (one_pow _)
    (by rw [(exists_teichmuller_lift 1).choose_spec.2, map_one])
  map_mul' ζ η := eq_of_pow_card_sub_one (exists_teichmuller_lift (ζ * η)).choose_spec.1
    (by rw [mul_pow, (exists_teichmuller_lift ζ).choose_spec.1,
      (exists_teichmuller_lift η).choose_spec.1, one_mul])
    (by rw [(exists_teichmuller_lift (ζ * η)).choose_spec.2, map_mul,
      (exists_teichmuller_lift ζ).choose_spec.2, (exists_teichmuller_lift η).choose_spec.2])
variable {K}
@[simp]
theorem unitsToResidue_teichmuller (ζ : 𝓀[K]ˣ) : unitsToResidue K (teichmuller K ζ) = ζ :=
  (exists_teichmuller_lift ζ).choose_spec.2
theorem unitsMulInvTeichmuller_mem (u : 𝒪[K]ˣ) :
    u * (teichmuller K (unitsToResidue K u))⁻¹ ∈ unitFiltration K 1 := by
  rw [← ker_unitsToResidue, MonoidHom.mem_ker, map_mul, map_inv, unitsToResidue_teichmuller,
    mul_inv_cancel]
variable (K)
noncomputable def unitsEquivResidueProd : 𝒪[K]ˣ ≃* 𝓀[K]ˣ × unitFiltration K 1 where
  toFun u := (unitsToResidue K u, ⟨_, unitsMulInvTeichmuller_mem u⟩)
  invFun p := teichmuller K p.1 * p.2
  left_inv u := by simp
  right_inv p := by
    obtain ⟨ζ, v, hv⟩ := p
    have hv' : unitsToResidue K v = 1 := by rwa [← MonoidHom.mem_ker, ker_unitsToResidue]
    ext
    · simp [hv']
    · simp [hv']
  map_mul' u w := by
    ext
    · simp
    · simp only [map_mul, mul_inv_rev, Prod.snd_mul, Subgroup.coe_mul]
      simp only [mul_comm, mul_left_comm, mul_assoc]
end Teichmuller
section Powers
end Powers
end GroundTheory.LocalField


