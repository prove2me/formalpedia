-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_PadicUnitsLog
-- name    : GroundTheory_GlobalFields_CyclotomicCharacters_PadicUnitsLog
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T00:17:20.563341+00:00
-- url     : https://prove2.me/theorems/f5307bca-0bf4-4e2e-b5f5-acff32ed9ee4
-- title:
--   Padic Units Log
-- statement:
--   Definitions and structural lemmas for Padic Units Log, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/PadicUnitsLog.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_ProfinitePadic
import Theorems.Thm_GroundTheory_Global_Cyclotomic_continuous_toZModPow
import Theorems.Thm_GroundTheory_Global_Cyclotomic_padicEquiv_apply
import Theorems.Thm_GroundTheory_Global_Cyclotomic_padicEquiv_symm_apply
import Theorems.Thm_GroundTheory_Global_Cyclotomic_val_unitsPadicEquiv_apply
import Theorems.Thm_UpperTheory_Reformulated_B_Yde3_continuous_toZModPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.Cyclotomic.padicEquiv_apply
attribute [local simp] GroundTheory.Global.Cyclotomic.padicEquiv_symm_apply
attribute [local simp] GroundTheory.Global.Cyclotomic.val_unitsPadicEquiv_apply


set_option autoImplicit false
open scoped GroundTheory.LocalField.Abstract
namespace GroundTheory.Global
namespace Cyclotomic
section Discrete
variable (ℓ : ℕ) [hℓ : Fact ℓ.Prime]
def unitsLevel : ℕ := if ℓ = 2 then 3 else 1
def torsionExponent : ℕ := if ℓ = 2 then 2 else ℓ - 1
omit hℓ in
theorem unitsLevel_ne_zero : unitsLevel ℓ ≠ 0 := by
  unfold unitsLevel; split_ifs <;> norm_num
theorem unitsLevel_add_two_le : unitsLevel ℓ + 2 ≤ ℓ * unitsLevel ℓ := by
  unfold unitsLevel
  split_ifs with h
  · subst h; norm_num
  · have := hℓ.out.two_le
    omega
theorem torsionExponent_pos : 0 < torsionExponent ℓ := by
  unfold torsionExponent
  split_ifs
  · norm_num
  · have := hℓ.out.two_le
    omega
theorem pow_torsionExponent (x : (ZMod (ℓ ^ unitsLevel ℓ))ˣ) : x ^ torsionExponent ℓ = 1 := by
  by_cases h : ℓ = 2
  · subst h
    have key : ∀ y : ZMod 8, (∃ z : ZMod 8, y * z = 1) → y ^ 2 = 1 := by decide
    have h8 : (2 : ℕ) ^ unitsLevel 2 = 8 := by simp [unitsLevel]
    rw [torsionExponent, if_pos rfl]
    refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    revert x
    rw [h8]
    intro x
    exact key _ ⟨_, x.mul_inv⟩
  · have : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
    have hc : Fintype.card (ZMod (ℓ ^ unitsLevel ℓ))ˣ = ℓ - 1 := by
      rw [ZMod.card_units_eq_totient, unitsLevel, if_neg h, pow_one, Nat.totient_prime hℓ.out]
    rw [torsionExponent, if_neg h, ← hc, pow_card_eq_one]
def unitsKer (n : ℕ) : Subgroup (ZMod (ℓ ^ (n + unitsLevel ℓ)))ˣ :=
  (ZMod.unitsMap (pow_dvd_pow ℓ (Nat.le_add_left (unitsLevel ℓ) n))).ker
theorem card_unitsKer (n : ℕ) : Nat.card (unitsKer ℓ n) = ℓ ^ n := by
  have : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  have h1 := Subgroup.card_mul_index (unitsKer ℓ n)
  rw [unitsKer, Subgroup.index_ker, MonoidHom.range_eq_top.2 (ZMod.unitsMap_surjective _),
    Subgroup.card_top, Nat.card_eq_fintype_card (α := (ZMod (ℓ ^ unitsLevel ℓ))ˣ),
    Nat.card_eq_fintype_card (α := (ZMod (ℓ ^ (n + unitsLevel ℓ)))ˣ), ZMod.card_units_eq_totient,
    ZMod.card_units_eq_totient, Nat.totient_prime_pow hℓ.out (Nat.pos_of_ne_zero
      (unitsLevel_ne_zero ℓ)), Nat.totient_prime_pow hℓ.out (by
        have := unitsLevel_ne_zero ℓ; omega)] at h1
  have hr : n + unitsLevel ℓ - 1 = n + (unitsLevel ℓ - 1) := by
    have := unitsLevel_ne_zero ℓ; omega
  have hpos : 0 < ℓ ^ (unitsLevel ℓ - 1) * (ℓ - 1) :=
    Nat.mul_pos (pow_pos hℓ.out.pos _) (by have := hℓ.out.two_le; omega)
  have h2 : Nat.card (unitsKer ℓ n) * (ℓ ^ (unitsLevel ℓ - 1) * (ℓ - 1)) =
      ℓ ^ n * (ℓ ^ (unitsLevel ℓ - 1) * (ℓ - 1)) := by
    rw [← mul_assoc (ℓ ^ n), ← pow_add, ← hr]
    exact h1
  exact Nat.eq_of_mul_eq_mul_right hpos h2
theorem coprime_one_add_pow (k : ℕ) : Nat.Coprime (1 + ℓ ^ unitsLevel ℓ) (ℓ ^ k) := by
  refine Nat.Coprime.pow_right _ ?_
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hℓ.out]
  intro h
  rw [add_comm] at h
  exact hℓ.out.not_dvd_one
    ((Nat.dvd_add_right (dvd_pow_self ℓ (unitsLevel_ne_zero ℓ))).1 h)
def genUnit (n : ℕ) : (ZMod (ℓ ^ (n + unitsLevel ℓ)))ˣ :=
  ZMod.unitOfCoprime (1 + ℓ ^ unitsLevel ℓ) (coprime_one_add_pow ℓ _)
@[simp] theorem coe_genUnit (n : ℕ) :
    (genUnit ℓ n : ZMod (ℓ ^ (n + unitsLevel ℓ))) = 1 + (ℓ : ZMod _) ^ unitsLevel ℓ := by
  simp [genUnit]
theorem orderOf_genUnit (n : ℕ) : orderOf (genUnit ℓ n) = ℓ ^ n := by
  rw [← orderOf_units, coe_genUnit]
  have := ZMod.orderOf_one_add_mul_prime_pow hℓ.out (unitsLevel ℓ) (unitsLevel_ne_zero ℓ)
    (unitsLevel_add_two_le ℓ) 1 (by norm_cast; exact hℓ.out.not_dvd_one) n
  simpa using this
theorem genUnit_pow_eq_one (n : ℕ) : genUnit ℓ n ^ (ℓ ^ n) = 1 := by
  have := pow_orderOf_eq_one (genUnit ℓ n)
  rwa [orderOf_genUnit] at this
theorem genUnit_mem_unitsKer (n : ℕ) : genUnit ℓ n ∈ unitsKer ℓ n := by
  rw [unitsKer, MonoidHom.mem_ker]
  refine Units.ext ?_
  simp only [ZMod.unitsMap_def, Units.coe_map, MonoidHom.coe_coe, coe_genUnit, map_add, map_one,
    map_pow, map_natCast, Units.val_one]
  rw [← Nat.cast_pow, ZMod.natCast_self, add_zero]
theorem zpowers_genUnit (n : ℕ) : Subgroup.zpowers (genUnit ℓ n) = unitsKer ℓ n :=
  Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 (genUnit_mem_unitsKer ℓ n))
    (by rw [card_unitsKer, Nat.card_zpowers, orderOf_genUnit])
theorem genUnit_pow_val_eq (n : ℕ) {a b : ℕ} (h : a ≡ b [MOD ℓ ^ n]) :
    genUnit ℓ n ^ a = genUnit ℓ n ^ b := by
  rw [pow_eq_pow_iff_modEq, orderOf_genUnit]
  exact h
def expHom (n : ℕ) : Multiplicative (ZMod (ℓ ^ n)) →* (ZMod (ℓ ^ (n + unitsLevel ℓ)))ˣ where
  toFun a := genUnit ℓ n ^ (Multiplicative.toAdd a).val
  map_one' := by simp
  map_mul' a b := by
    have : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
    rw [← pow_add, toAdd_mul]
    exact genUnit_pow_val_eq ℓ n (by rw [ZMod.val_add]; exact Nat.mod_modEq _ _)
theorem expHom_apply (n : ℕ) (a : Multiplicative (ZMod (ℓ ^ n))) :
    expHom ℓ n a = genUnit ℓ n ^ (Multiplicative.toAdd a).val :=
  rfl
theorem expHom_injective (n : ℕ) : Function.Injective (expHom ℓ n) := by
  have : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  refine (injective_iff_map_eq_one _).2 fun a ha => ?_
  rw [expHom_apply] at ha
  have h1 : ℓ ^ n ∣ (Multiplicative.toAdd a).val := by
    have := orderOf_dvd_of_pow_eq_one ha
    rwa [orderOf_genUnit] at this
  have h2 := Nat.eq_zero_of_dvd_of_lt h1 (ZMod.val_lt _)
  rw [ZMod.val_eq_zero] at h2
  exact h2
theorem range_expHom (n : ℕ) : (expHom ℓ n).range = unitsKer ℓ n := by
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨a, rfl⟩
    rw [← zpowers_genUnit]
    exact Subgroup.npow_mem_zpowers _ _
  · rw [card_unitsKer, ← Nat.card_congr (MonoidHom.ofInjective (expHom_injective ℓ n)).toEquiv]
    exact (Nat.card_zmod _).ge
noncomputable def expEquiv (n : ℕ) : Multiplicative (ZMod (ℓ ^ n)) ≃* unitsKer ℓ n :=
  (MonoidHom.ofInjective (expHom_injective ℓ n)).trans (MulEquiv.subgroupCongr (range_expHom ℓ n))
theorem coe_expEquiv (n : ℕ) (a : Multiplicative (ZMod (ℓ ^ n))) :
    (expEquiv ℓ n a : (ZMod (ℓ ^ (n + unitsLevel ℓ)))ˣ) = expHom ℓ n a :=
  rfl
def powKer (n : ℕ) : (ZMod (ℓ ^ (n + unitsLevel ℓ)))ˣ →* unitsKer ℓ n :=
  (powMonoidHom (torsionExponent ℓ)).codRestrict (unitsKer ℓ n) fun x => by
    rw [unitsKer, MonoidHom.mem_ker, powMonoidHom_apply, map_pow, pow_torsionExponent]
noncomputable def logMod (n : ℕ) : (ZMod (ℓ ^ (n + unitsLevel ℓ)))ˣ →* Multiplicative (ZMod (ℓ ^ n)) :=
  (expEquiv ℓ n).symm.toMonoidHom.comp (powKer ℓ n)
theorem expHom_logMod (n : ℕ) (x : (ZMod (ℓ ^ (n + unitsLevel ℓ)))ˣ) :
    expHom ℓ n (logMod ℓ n x) = x ^ torsionExponent ℓ := by
  have := congrArg Subtype.val ((expEquiv ℓ n).apply_symm_apply (powKer ℓ n x))
  rw [coe_expEquiv] at this
  exact this
theorem logMod_eq_iff (n : ℕ) (x : (ZMod (ℓ ^ (n + unitsLevel ℓ)))ˣ)
    (a : Multiplicative (ZMod (ℓ ^ n))) :
    logMod ℓ n x = a ↔ expHom ℓ n a = x ^ torsionExponent ℓ :=
  ⟨fun h => h ▸ expHom_logMod ℓ n x,
    fun h => expHom_injective ℓ n (by rw [expHom_logMod, h])⟩
theorem unitsMap_genUnit {m n : ℕ} (h : m ≤ n) :
    ZMod.unitsMap (pow_dvd_pow ℓ (by omega : m + unitsLevel ℓ ≤ n + unitsLevel ℓ)) (genUnit ℓ n) =
      genUnit ℓ m := by
  refine Units.ext ?_
  simp only [ZMod.unitsMap_def, Units.coe_map, MonoidHom.coe_coe, coe_genUnit, map_add, map_one,
    map_pow, map_natCast]
theorem castHom_logMod {m n : ℕ} (h : m ≤ n) (x : (ZMod (ℓ ^ (n + unitsLevel ℓ)))ˣ) :
    ZMod.castHom (pow_dvd_pow ℓ h) (ZMod (ℓ ^ m)) (Multiplicative.toAdd (logMod ℓ n x)) =
      Multiplicative.toAdd (logMod ℓ m
        (ZMod.unitsMap (pow_dvd_pow ℓ (by omega : m + unitsLevel ℓ ≤ n + unitsLevel ℓ)) x)) := by
  have : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  set a := Multiplicative.toAdd (logMod ℓ n x) with ha
  have key : logMod ℓ m
      (ZMod.unitsMap (pow_dvd_pow ℓ (by omega : m + unitsLevel ℓ ≤ n + unitsLevel ℓ)) x) =
        Multiplicative.ofAdd (ZMod.castHom (pow_dvd_pow ℓ h) (ZMod (ℓ ^ m)) a) := by
    rw [logMod_eq_iff, expHom_apply, toAdd_ofAdd, ← map_pow, ← expHom_logMod ℓ n x, expHom_apply,
      map_pow, unitsMap_genUnit ℓ h, ← ha]
    refine genUnit_pow_val_eq ℓ m ?_
    rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast]
    exact Nat.mod_modEq _ _
  rw [key, toAdd_ofAdd]
end Discrete
section Limit
variable (ℓ : ℕ) [hℓ : Fact ℓ.Prime]
def compatibleFamilies : Subring (∀ n : ℕ, ZMod (ℓ ^ n)) :=
  ⨅ (m : ℕ) (n : ℕ) (h : m ≤ n), RingHom.eqLocus
    ((ZMod.castHom (pow_dvd_pow ℓ h) (ZMod (ℓ ^ m))).comp
      (Pi.evalRingHom (fun k => ZMod (ℓ ^ k)) n)) (Pi.evalRingHom (fun k => ZMod (ℓ ^ k)) m)
omit hℓ in
theorem mem_compatibleFamilies {x : ∀ n : ℕ, ZMod (ℓ ^ n)} :
    x ∈ compatibleFamilies ℓ ↔
      ∀ (m n : ℕ) (h : m ≤ n), ZMod.castHom (pow_dvd_pow ℓ h) (ZMod (ℓ ^ m)) (x n) = x m := by
  simp [compatibleFamilies, Subring.mem_iInf, RingHom.mem_eqLocus]
noncomputable def limFamilies : compatibleFamilies ℓ →+* ℤ_[ℓ] :=
  PadicInt.lift (f := fun n => (Pi.evalRingHom (fun k => ZMod (ℓ ^ k)) n).comp
    (compatibleFamilies ℓ).subtype) fun m n h => by
      ext x
      exact (mem_compatibleFamilies ℓ).1 x.2 m n h
theorem toZModPow_limFamilies (x : compatibleFamilies ℓ) (n : ℕ) :
    PadicInt.toZModPow n (limFamilies ℓ x) = (x : ∀ n : ℕ, ZMod (ℓ ^ n)) n :=
  RingHom.congr_fun (PadicInt.lift_spec _ n) x
noncomputable def redUnits (k : ℕ) : ℤ_[ℓ]ˣ →* (ZMod (ℓ ^ k))ˣ :=
  Units.map (PadicInt.toZModPow k).toMonoidHom
@[simp] theorem coe_redUnits (k : ℕ) (u : ℤ_[ℓ]ˣ) :
    (redUnits ℓ k u : ZMod (ℓ ^ k)) = PadicInt.toZModPow k (u : ℤ_[ℓ]) :=
  rfl
theorem unitsMap_redUnits {k k' : ℕ} (h : k ≤ k') (u : ℤ_[ℓ]ˣ) :
    ZMod.unitsMap (pow_dvd_pow ℓ h) (redUnits ℓ k' u) = redUnits ℓ k u := by
  refine Units.ext ?_
  simp only [ZMod.unitsMap_def, Units.coe_map, MonoidHom.coe_coe, coe_redUnits,
    ZMod.castHom_apply]
  exact PadicInt.cast_toZModPow _ _ h _
theorem logFamily_mem (u : ℤ_[ℓ]ˣ) :
    (fun n => Multiplicative.toAdd (logMod ℓ n (redUnits ℓ (n + unitsLevel ℓ) u))) ∈
      compatibleFamilies ℓ := by
  rw [mem_compatibleFamilies]
  intro m n h
  rw [castHom_logMod ℓ h,
    unitsMap_redUnits ℓ (k := m + unitsLevel ℓ) (k' := n + unitsLevel ℓ) (by omega)]
noncomputable def padicUnitsLog : ℤ_[ℓ]ˣ →* Multiplicative ℤ_[ℓ] where
  toFun u := Multiplicative.ofAdd (limFamilies ℓ ⟨_, logFamily_mem ℓ u⟩)
  map_one' := by
    refine congrArg Multiplicative.ofAdd (PadicInt.ext_of_toZModPow.mp fun n => ?_)
    rw [toZModPow_limFamilies, map_zero]
    simp
  map_mul' u v := by
    rw [← ofAdd_add]
    refine congrArg Multiplicative.ofAdd (PadicInt.ext_of_toZModPow.mp fun n => ?_)
    rw [map_add, toZModPow_limFamilies, toZModPow_limFamilies, toZModPow_limFamilies]
    simp
theorem toZModPow_padicUnitsLog (u : ℤ_[ℓ]ˣ) (n : ℕ) :
    PadicInt.toZModPow n (Multiplicative.toAdd (padicUnitsLog ℓ u)) =
      Multiplicative.toAdd (logMod ℓ n (redUnits ℓ (n + unitsLevel ℓ) u)) :=
  toZModPow_limFamilies ℓ _ n
theorem continuous_redUnits (k : ℕ) : Continuous (redUnits ℓ k) := by
  rw [Units.continuous_iff]
  refine ⟨(continuous_toZModPow k).comp Units.continuous_val, ?_⟩
  have : (fun u : ℤ_[ℓ]ˣ => ((redUnits ℓ k u)⁻¹ : (ZMod (ℓ ^ k))ˣ).val) =
      fun u => PadicInt.toZModPow k ((u⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) := by
    funext u; rw [← map_inv]; rfl
  rw [this]
  exact (continuous_toZModPow k).comp (Units.continuous_val.comp continuous_inv)
theorem continuous_padicUnitsLog : Continuous (padicUnitsLog ℓ) := by
  have hc : Continuous fun u : ℤ_[ℓ]ˣ => Multiplicative.toAdd (padicUnitsLog ℓ u) :=
    continuous_of_continuous_toZModPow fun n =>
      ((continuous_of_discreteTopology (f := fun v : (ZMod (ℓ ^ (n + unitsLevel ℓ)))ˣ =>
        Multiplicative.toAdd (logMod ℓ n v))).comp (continuous_redUnits ℓ _)).congr fun u =>
          (toZModPow_padicUnitsLog ℓ u n).symm
  exact continuous_ofAdd.comp hc
def genNat : ℕ := if ℓ = 2 then 3 else ℓ + 1
def genLog : ℕ := if ℓ = 2 then 1 else ℓ - 1
theorem genNat_pow : genNat ℓ ^ torsionExponent ℓ = (1 + ℓ ^ unitsLevel ℓ) ^ genLog ℓ := by
  unfold genNat torsionExponent unitsLevel genLog
  split_ifs with h
  · subst h; norm_num
  · rw [pow_one, add_comm]
theorem coprime_genNat : Nat.Coprime ℓ (genNat ℓ) := by
  rw [Nat.Prime.coprime_iff_not_dvd hℓ.out]
  unfold genNat
  split_ifs with h
  · subst h; norm_num
  · intro hd
    exact hℓ.out.not_dvd_one ((Nat.dvd_add_right (dvd_refl ℓ)).1 hd)
theorem coprime_genLog : Nat.Coprime ℓ (genLog ℓ) := by
  rw [Nat.Prime.coprime_iff_not_dvd hℓ.out]
  unfold genLog
  split_ifs with h
  · subst h; norm_num
  · have := hℓ.out.two_le
    exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
theorem isUnit_natCast_of_coprime {k : ℕ} (hk : Nat.Coprime ℓ k) : IsUnit (k : ℤ_[ℓ]) :=
  PadicInt.isUnit_iff.2 (PadicInt.norm_natCast_eq_one_iff.2 hk)
noncomputable def genPadicUnit : ℤ_[ℓ]ˣ := (isUnit_natCast_of_coprime ℓ (coprime_genNat ℓ)).unit
theorem padicUnitsLog_genPadicUnit :
    Multiplicative.toAdd (padicUnitsLog ℓ (genPadicUnit ℓ)) = (genLog ℓ : ℤ_[ℓ]) := by
  refine PadicInt.ext_of_toZModPow.mp fun n => ?_
  rw [toZModPow_padicUnitsLog, map_natCast]
  have : logMod ℓ n (redUnits ℓ (n + unitsLevel ℓ) (genPadicUnit ℓ)) =
      Multiplicative.ofAdd ((genLog ℓ : ℕ) : ZMod (ℓ ^ n)) := by
    rw [logMod_eq_iff, expHom_apply, toAdd_ofAdd, pow_val_natCast (genUnit_pow_eq_one ℓ n)]
    refine Units.ext ?_
    simp only [Units.val_pow_eq_pow_val, coe_genUnit, coe_redUnits, genPadicUnit,
      IsUnit.unit_spec, map_natCast]
    rw [← Nat.cast_pow (genNat ℓ), genNat_pow]
    push_cast
    ring
  rw [this, toAdd_ofAdd]
theorem padicUnitsLog_surjective : Function.Surjective (padicUnitsLog ℓ) := by
  have hc : Continuous fun u : ℤ_[ℓ]ˣ => Multiplicative.toAdd (padicUnitsLog ℓ u) :=
    continuous_toAdd.comp (continuous_padicUnitsLog ℓ)
  set s : ℤ_[ℓ] := (genLog ℓ : ℤ_[ℓ])
  have hs : IsUnit s := isUnit_natCast_of_coprime ℓ (coprime_genLog ℓ)
  set R : Set ℤ_[ℓ] := Set.range fun u : ℤ_[ℓ]ˣ => Multiplicative.toAdd (padicUnitsLog ℓ u)
  have hR : IsClosed R := (isCompact_range hc).isClosed
  have hmem : ∀ t : ℤ_[ℓ], s * t ∈ R := fun t =>
    PadicInt.denseRange_natCast.induction_on t
      (hR.preimage (continuous_const.mul continuous_id)) fun k =>
        ⟨genPadicUnit ℓ ^ k, by
          show Multiplicative.toAdd (padicUnitsLog ℓ (genPadicUnit ℓ ^ k)) = s * k
          rw [map_pow, toAdd_pow, padicUnitsLog_genPadicUnit, nsmul_eq_mul, mul_comm]⟩
  intro y
  obtain ⟨u, hu⟩ := hmem (↑hs.unit⁻¹ * Multiplicative.toAdd y)
  have hu : Multiplicative.toAdd (padicUnitsLog ℓ u) = s * (↑hs.unit⁻¹ * Multiplicative.toAdd y) :=
    hu
  refine ⟨u, ?_⟩
  apply Multiplicative.toAdd.injective
  rw [hu, ← mul_assoc, IsUnit.mul_val_inv, one_mul]
theorem padicUnitsLog_eq_one_of_pow_eq_one {u : ℤ_[ℓ]ˣ} {k : ℕ} (hk : 0 < k) (h : u ^ k = 1) :
    padicUnitsLog ℓ u = 1 := by
  have h1 := congrArg (fun v => Multiplicative.toAdd (padicUnitsLog ℓ v)) h
  simp only [map_pow, toAdd_pow, map_one, toAdd_one, nsmul_eq_mul] at h1
  rcases mul_eq_zero.1 h1 with h2 | h2
  · exact absurd h2 (Nat.cast_ne_zero.2 hk.ne')
  · exact congrArg Multiplicative.ofAdd h2
theorem padicUnitsLog_eq_one_iff (u : ℤ_[ℓ]ˣ) :
    padicUnitsLog ℓ u = 1 ↔ u ^ torsionExponent ℓ = 1 := by
  refine ⟨fun h => ?_, padicUnitsLog_eq_one_of_pow_eq_one ℓ (torsionExponent_pos ℓ)⟩
  have hk : ∀ k, PadicInt.toZModPow (k + unitsLevel ℓ) ((u ^ torsionExponent ℓ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) =
      1 := fun k => by
    have h1 := toZModPow_padicUnitsLog ℓ u k
    rw [h, toAdd_one, map_zero] at h1
    have h2 : logMod ℓ k (redUnits ℓ (k + unitsLevel ℓ) u) = 1 :=
      congrArg Multiplicative.ofAdd h1.symm
    rw [logMod_eq_iff, map_one] at h2
    have h3 := congrArg Units.val h2
    rw [Units.val_one, Units.val_pow_eq_pow_val, coe_redUnits, ← map_pow] at h3
    rw [Units.val_pow_eq_pow_val]
    exact h3.symm
  refine Units.ext (PadicInt.ext_of_toZModPow.mp fun k => ?_)
  rw [← PadicInt.zmod_cast_comp_toZModPow k (k + unitsLevel ℓ) (Nat.le_add_right _ _),
    RingHom.comp_apply, RingHom.comp_apply, hk]
  simp
theorem ker_padicUnitsLog : (padicUnitsLog ℓ).ker = CommGroup.torsion ℤ_[ℓ]ˣ := by
  ext u
  rw [MonoidHom.mem_ker, CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
  constructor
  · intro h
    exact ⟨_, torsionExponent_pos ℓ, (padicUnitsLog_eq_one_iff ℓ u).1 h⟩
  · rintro ⟨k, hk, h⟩
    exact padicUnitsLog_eq_one_of_pow_eq_one ℓ hk h
noncomputable def unitsModTorsionEquiv :
    ℤ_[ℓ]ˣ ⧸ CommGroup.torsion ℤ_[ℓ]ˣ ≃* Multiplicative ℤ_[ℓ] :=
  (QuotientGroup.quotientMulEquivOfEq (ker_padicUnitsLog ℓ).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (padicUnitsLog_surjective ℓ))
end Limit
end Cyclotomic
end GroundTheory.Global


