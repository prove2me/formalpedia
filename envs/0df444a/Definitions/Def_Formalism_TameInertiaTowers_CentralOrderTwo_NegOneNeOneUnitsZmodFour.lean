-- Prove2me | Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_NegOneNeOneUnitsZmodFour
-- name    : Formalism_TameInertiaTowers_CentralOrderTwo_NegOneNeOneUnitsZmodFour
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T12:44:31.489615+00:00
-- url     : https://prove2.me/theorems/b7f83386-0333-4129-ad80-2872aa1f3f34
-- title:
--   Neg One Ne One Units Zmod Four
-- statement:
--   Definitions and structural lemmas for Neg One Ne One Units Zmod Four, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/NegOneNeOneUnitsZmodFour.lean

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementGroup
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_TwoAdic
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_twoAdicOrder

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.TwoAdicCyclotomicDecomposition
lemma pv24 : padicValInt 2 ((5:ℤ) ^ 2 - 1) = 3 := by
  have h : ((5:ℤ) ^ 2 - 1) = ((2 ^ 3 * 3 : ℕ) : ℤ) := by norm_num
  rw [h, padicValInt.of_nat, padicValNat.mul (show 2 ^ 3 ≠ 0 by norm_num) (show 3 ≠ 0 by norm_num),
    padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (show ¬ 2 ∣ 3 by norm_num)]
lemma five_unit_coe_int (n : ℕ) : ((u5 n : (ZMod (2 ^ n))ˣ) : ZMod (2 ^ n)) = ((5 : ℤ) : ZMod (2 ^ n)) := by simp [u5, ZMod.coe_unitOfCoprime]
lemma intCast_five_zmod_two_pow_eq_one_iff (n : ℕ) : ((5:ℤ) : ZMod (2 ^ n)) = 1 ↔ (2:ℤ) ^ n ∣ 4 := by
  have h := ZMod.intCast_eq_intCast_iff_dvd_sub 5 1 (2 ^ n)
  rw [Int.cast_one] at h
  rw [h]
  push_cast
  constructor <;> intro h' <;> simpa using h'
lemma ord5 (m : ℕ) : orderOf (u5 (m + 2)) = 2 ^ m := by
  have h := twoAdicOrder (m + 2) 5 ⟨2, by norm_num⟩ (by norm_num)
  rw [pv24] at h
  rw [← orderOf_units, five_unit_coe_int, h]
  rcases m with _ | k
  · rw [if_pos ((intCast_five_zmod_two_pow_eq_one_iff (0 + 2)).2 ⟨1, by norm_num⟩)]
    rfl
  · rw [if_neg]
    · congr 1
    · intro h1
      have h2 := (intCast_five_zmod_two_pow_eq_one_iff (k + 1 + 2)).1 h1
      have h8 : (8:ℤ) ∣ 2 ^ (k + 1 + 2) := ⟨2 ^ k, by ring⟩
      have h3 := h8.trans h2
      omega
lemma unitsMap_five {a b : ℕ} (h : 2 ^ b ∣ 2 ^ a) : ZMod.unitsMap h (u5 a) = u5 b := by
  ext
  rw [ZMod.unitsMap_def, Units.coe_map, five_unit_coe_int, five_unit_coe_int]
  exact map_intCast (ZMod.castHom h (ZMod (2 ^ b))) 5
lemma unitsMap_neg_one' {a b : ℕ} (h : b ∣ a) : ZMod.unitsMap h (-1) = -1 := by
  ext
  simp [ZMod.unitsMap_def]
noncomputable def r4 (n : ℕ) : (ZMod (2 ^ (n + 2)))ˣ →* (ZMod (2 ^ 2))ˣ :=
  ZMod.unitsMap (pow_dvd_pow 2 (by omega))
lemma five_unit_mod_four : u5 2 = 1 := by
  ext
  rw [five_unit_coe_int, Units.val_one]
  exact (intCast_five_zmod_two_pow_eq_one_iff 2).2 ⟨1, by norm_num⟩
lemma mod_four_reduction_five (n : ℕ) : r4 n (u5 (n + 2)) = 1 := by rw [r4, unitsMap_five, five_unit_mod_four]
lemma mod_four_reduction_neg_one (n : ℕ) : r4 n (-1) = -1 := by rw [r4, unitsMap_neg_one']
lemma neg_one_ne_one_units_zmod_four : (-1 : (ZMod (2 ^ 2))ˣ) ≠ 1 := by
  haveI : Fact (2 < 2 ^ 2) := ⟨by norm_num⟩
  intro h
  apply ZMod.neg_one_ne_one (n := 2 ^ 2)
  simpa using congrArg Units.val h
lemma neg_ne_one (n : ℕ) : (-1 : (ZMod (2 ^ (n + 2)))ˣ) ≠ 1 := by
  intro h
  apply neg_one_ne_one_units_zmod_four
  have h1 := congrArg (r4 n) h
  rwa [mod_four_reduction_neg_one, map_one] at h1
lemma neg_one_ne_pow_five (n k : ℕ) : (-1 : (ZMod (2 ^ (n + 2)))ˣ) ≠ u5 (n + 2) ^ k := by
  intro h
  have h1 := congrArg (r4 n) h
  rw [mod_four_reduction_neg_one, map_pow, mod_four_reduction_five, one_pow] at h1
  exact neg_one_ne_one_units_zmod_four h1
lemma mem_zpowers_sq {G : Type*} [Group G] {g x : G} (hg : g ^ 2 = 1) :
    x ∈ Subgroup.zpowers g ↔ x = 1 ∨ x = g := by
  constructor
  · intro hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    have h2 : g ^ (2:ℤ) = 1 := by rw [zpow_two, ← pow_two]; exact hg
    obtain ⟨j, rfl | rfl⟩ := Int.even_or_odd' k
    · left
      rw [zpow_mul, h2, one_zpow]
    · right
      rw [zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _
lemma neg_one_sq_units {n : ℕ} : (-1 : (ZMod (2 ^ n))ˣ) ^ 2 = 1 := neg_one_sq
lemma gen_sq {n : ℕ} : ((-1, 1, 1) : GalL n) ^ 2 = 1 := by
  rw [Prod.pow_mk, Prod.pow_mk, neg_one_sq_units, one_pow]
  all_goals rfl
abbrev QQ (s : ℕ) : Type := (ZMod (2 ^ (s + 2)))ˣ ⧸ Subgroup.zpowers (-1 : (ZMod (2 ^ (s + 2)))ˣ)
lemma card_units (s : ℕ) : Nat.card (ZMod (2 ^ (s + 2)))ˣ = 2 ^ (s + 1) := by
  rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime_pow Nat.prime_two (by omega),
    show s + 2 - 1 = s + 1 by omega]
  norm_num
lemma card_zp_neg (s : ℕ) : Nat.card (Subgroup.zpowers (-1 : (ZMod (2 ^ (s + 2)))ˣ)) = 2 := by
  rw [Nat.card_zpowers]
  exact orderOf_eq_prime neg_one_sq_units (neg_ne_one s)
lemma card_QQ (s : ℕ) : Nat.card (QQ s) = 2 ^ s := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.zpowers (-1 : (ZMod (2 ^ (s + 2)))ˣ))
  rw [card_units, card_zp_neg, pow_succ] at h
  exact (Nat.eq_of_mul_eq_mul_right (by norm_num) h).symm
lemma ord_QQ (s : ℕ) : orderOf (QuotientGroup.mk (u5 (s + 2)) : QQ s) = 2 ^ s := by
  rcases s with _ | k
  · simp [five_unit_mod_four]
  · apply orderOf_eq_prime_pow
    · rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_zpowers_sq neg_one_sq_units]
      rintro (h | h)
      · refine pow_ne_one_of_lt_orderOf (by positivity) ?_ h
        rw [ord5, pow_succ]
        have := Nat.two_pow_pos k
        omega
      · exact neg_one_ne_pow_five (k + 1) (2 ^ k) h.symm
    · have h1 := pow_orderOf_eq_one (u5 (k + 1 + 2))
      rw [ord5] at h1
      rw [← QuotientGroup.mk_pow, h1, QuotientGroup.mk_one]
lemma cyc_QQ (s : ℕ) : IsCyclic (QQ s) := by
  exact isCyclic_of_orderOf_eq_card (QuotientGroup.mk (u5 (s + 2)) : QQ s) (by rw [ord_QQ, card_QQ])
lemma card_mz (n : ℕ) : Nat.card (Multiplicative (ZMod n)) = n := by
  rw [Nat.card_congr Multiplicative.ofAdd.symm, Nat.card_zmod]
noncomputable def eQQ (s : ℕ) : QQ s ≃* Multiplicative (ZMod (2 ^ s)) :=
  @mulEquivOfCyclicCardEq _ _ _ _ (cyc_QQ s) _ (by rw [card_QQ, card_mz])
noncomputable def phiE (s : ℕ) : GalL (s + 2) →* QQ s × ℤˣ × ℤˣ :=
  MonoidHom.prodMap (QuotientGroup.mk' _) (MonoidHom.id _)
lemma phiE_surj (s : ℕ) : Function.Surjective (phiE s) := by
  rintro ⟨q, b⟩
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective _ q
  exact ⟨(u, b), rfl⟩
lemma phiE_ker (s : ℕ) : (phiE s).ker = Subgroup.zpowers ((-1, 1, 1) : GalL (s + 2)) := by
  ext ⟨u, b⟩
  rw [MonoidHom.mem_ker, mem_zpowers_sq gen_sq]
  change (QuotientGroup.mk' _ u, b) = 1 ↔ _
  rw [Prod.mk_eq_one, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_zpowers_sq neg_one_sq_units]
  simp only [Prod.ext_iff, Prod.fst_one, Prod.snd_one]
  tauto
noncomputable def eGamE (s : ℕ) : GamE s ≃* Multiplicative (ZMod (2 ^ s)) × ℤˣ × ℤˣ :=
  ((QuotientGroup.quotientMulEquivOfEq (phiE_ker s).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (phiE_surj s))).trans
    (MulEquiv.prodCongr (eQQ s) (MulEquiv.refl _))
noncomputable def iota (n : ℕ) : ℤˣ →* (ZMod (2 ^ n))ˣ :=
  Units.map (Int.castRingHom (ZMod (2 ^ n))).toMonoidHom
noncomputable def wgen (s m : ℕ) : (ZMod (2 ^ (m + 2)))ˣ := u5 (m + 2) ^ (2 ^ s)
lemma ord_w {s m : ℕ} (h : s ≤ m) : orderOf (wgen s m) = 2 ^ (m - s) := by
  have hd : 2 ^ s ∣ orderOf (u5 (m + 2)) := by
    rw [ord5]
    exact pow_dvd_pow 2 h
  rw [wgen, orderOf_pow_of_dvd (by positivity) hd, ord5, Nat.pow_div h (by norm_num)]
noncomputable def psi {s m : ℕ} (h : s ≤ m) :
    ℤˣ × Multiplicative (ZMod (2 ^ (m - s))) →* GalL (m + 2) :=
  MonoidHom.mk' (fun p => (iota (m + 2) p.1 * wgen s m ^ (Multiplicative.toAdd p.2).val, 1, 1))
    (by
      rintro ⟨e1, k1⟩ ⟨e2, k2⟩
      simp only [Prod.mk_mul_mk, mul_one, toAdd_mul, map_mul]
      congr 1
      have key : ∀ n : ℕ, wgen s m ^ (n % 2 ^ (m - s)) = wgen s m ^ n := fun n => by
        rw [← ord_w h, pow_mod_orderOf]
      rw [ZMod.val_add, key, pow_add (wgen s m)]
      exact mul_mul_mul_comm _ _ _ _)
end Formalism.TwoAdicCyclotomicDecomposition


