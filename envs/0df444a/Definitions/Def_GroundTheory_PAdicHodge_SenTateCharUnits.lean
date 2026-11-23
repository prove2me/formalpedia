-- Prove2me | Definitions.Def_GroundTheory_PAdicHodge_SenTateCharUnits
-- name    : GroundTheory_PAdicHodge_SenTateCharUnits
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T18:23:16.35754+00:00
-- url     : https://prove2.me/theorems/404b5a4b-57d9-4b1c-8542-2526aa0cbf66
-- title:
--   Sen Tate Char Units
-- statement:
--   Definitions and structural lemmas for Sen Tate Char Units, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/SenTateCharUnits.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.PAdicHodge
namespace SenTateChar
variable (p : ℕ) [hp : Fact p.Prime]
def unitsOneAdd (k : ℕ) : Subgroup ℤ_[p]ˣ where
  carrier := {u | (p : ℤ_[p]) ^ k ∣ (u : ℤ_[p]) - 1}
  one_mem' := by simp
  mul_mem' := fun {a b} ha hb => by
    have e : ((a * b : ℤ_[p]ˣ) : ℤ_[p]) - 1 =
        (a : ℤ_[p]) * ((b : ℤ_[p]) - 1) + ((a : ℤ_[p]) - 1) := by push_cast; ring
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [e]
    exact dvd_add (dvd_mul_of_dvd_right hb _) ha
  inv_mem' := fun {a} ha => by
    have e : ((a⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) - 1 = -(((a⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * ((a : ℤ_[p]) - 1)) := by
      rw [mul_sub, Units.inv_mul, mul_one]; ring
    simp only [Set.mem_ofPred_eq] at ha ⊢
    rw [e]
    exact (dvd_mul_of_dvd_right ha _).neg_right
variable {p}
theorem mem_unitsOneAdd {k : ℕ} {u : ℤ_[p]ˣ} :
    u ∈ unitsOneAdd p k ↔ (p : ℤ_[p]) ^ k ∣ (u : ℤ_[p]) - 1 := Iff.rfl
@[simp]
theorem unitsOneAdd_zero : unitsOneAdd p 0 = ⊤ := by
  ext u; simp [mem_unitsOneAdd]
def levelQuot {k : ℕ} (u : unitsOneAdd p k) : ℤ_[p] :=
  Classical.choose (mem_unitsOneAdd.1 u.2)
theorem levelQuot_spec {k : ℕ} (u : unitsOneAdd p k) :
    ((u : ℤ_[p]ˣ) : ℤ_[p]) - 1 = (p : ℤ_[p]) ^ k * levelQuot u :=
  Classical.choose_spec (mem_unitsOneAdd.1 u.2)
theorem levelQuot_eq {k : ℕ} (u : unitsOneAdd p k) {c : ℤ_[p]}
    (hc : ((u : ℤ_[p]ˣ) : ℤ_[p]) - 1 = (p : ℤ_[p]) ^ k * c) : levelQuot u = c := by
  have hp0 : (p : ℤ_[p]) ^ k ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  exact mul_left_cancel₀ hp0 ((levelQuot_spec u).symm.trans hc)
theorem toZMod_natCast_prime_pow {k : ℕ} (hk : 1 ≤ k) :
    PadicInt.toZMod ((p : ℤ_[p]) ^ k) = 0 := by
  rw [map_pow, map_natCast, ZMod.natCast_self, zero_pow (by omega)]
variable (p) in

def levelHom (k : ℕ) (hk : 1 ≤ k) : unitsOneAdd p k →* Multiplicative (ZMod p) where
  toFun u := Multiplicative.ofAdd (PadicInt.toZMod (levelQuot u))
  map_one' := by
    have : levelQuot (1 : unitsOneAdd p k) = 0 := levelQuot_eq _ (by simp)
    rw [this, map_zero, ofAdd_zero]
  map_mul' u v := by
    have e : (((u * v : unitsOneAdd p k) : ℤ_[p]ˣ) : ℤ_[p]) - 1 = (p : ℤ_[p]) ^ k *
        (levelQuot u + levelQuot v + (p : ℤ_[p]) ^ k * levelQuot u * levelQuot v) := by
      have hu := levelQuot_spec u
      have hv := levelQuot_spec v
      have : (((u * v : unitsOneAdd p k) : ℤ_[p]ˣ) : ℤ_[p]) =
          ((u : ℤ_[p]ˣ) : ℤ_[p]) * ((v : ℤ_[p]ˣ) : ℤ_[p]) := rfl
      rw [this]
      linear_combination (((v : ℤ_[p]ˣ) : ℤ_[p])) * hu + (1 + (p : ℤ_[p]) ^ k * levelQuot u) * hv
    rw [levelQuot_eq _ e, ← ofAdd_add]
    congr 1
    rw [map_add, map_add, map_mul, map_mul, toZMod_natCast_prime_pow hk, zero_mul, zero_mul, add_zero]
end SenTateChar
end GroundTheory.PAdicHodge


