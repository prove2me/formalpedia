-- Prove2me | Definitions.Def_Polychromatic_FourThree_Combi_CaseTwo
-- name    : Polychromatic_FourThree_Combi_CaseTwo
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T08:46:54.544792+00:00
-- url     : https://prove2.me/theorems/485b1c31-f66e-41bb-8bc0-30ff4e62e019
-- title:
--   Case Two
-- statement:
--   Definitions and structural lemmas for Case Two, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Combi/CaseTwo.lean

import Definitions.Def_Polychromatic_FourThree_Combi_BlockColour
import Theorems.Thm_hasPolychromColouring_neg
import Theorems.Thm_hasPolychromColouring_univ
import Theorems.Thm_isUnit_intCast_of_natAbs_coprime
import Theorems.Thm_polychromNumber_pair
import Theorems.Thm_polychromNumber_singleton
import Theorems.Thm_polychromNumber_univ
attribute [local simp] hasPolychromColouring_neg
attribute [local simp] hasPolychromColouring_univ
attribute [local simp] polychromNumber_pair
attribute [local simp] polychromNumber_singleton
attribute [local simp] polychromNumber_univ


set_option autoImplicit true
open Finset Pointwise
section Case2_MultipleCycles
variable {m : ℕ} {a b : ℤ}
local notation "d₁" => Nat.gcd b.natAbs m
local notation "d₂" => Nat.gcd (Int.natAbs (b - a)) m
local notation "e₁" => m / d₁
def cycle_coloring (d e : ℕ) : ZMod d × ZMod e → Fin 3 := fun ⟨i, j⟩ =>
  if i.val = d - 1 ∧ ¬Even d then ⟨1 + j.val % 2, by grind⟩
  else if i.val % 2 = 0 then ⟨j.val % 2, by grind⟩
  else ⟨2 * (j.val % 2), by grind⟩
lemma d₁_dvd_m : d₁ ∣ m := Nat.gcd_dvd_right _ _
lemma m_eq_d₁_mul_e₁ : m = d₁ * e₁ := (Nat.mul_div_cancel' (d₁_dvd_m (b := b))).symm
instance neZero_d₁ [NeZero m] : NeZero d₁ :=
  ⟨fun h => absurd (by grind) (NeZero.ne m)⟩
instance neZero_e₁ [NeZero m] : NeZero e₁ :=
  ⟨fun h => absurd (by grind only [m_eq_d₁_mul_e₁]) (NeZero.ne m)⟩
section OrbitFramework
def orbitMap (m : ℕ) (a b : ℤ) : ZMod d₁ × ZMod e₁ → ZMod m :=
  fun p => (p.1.val : ZMod m) * ↑(b - a) + (p.2.val : ZMod m) * ↑b
lemma addOrderOf_b_eq [NeZero m] : addOrderOf (b : ZMod m) = e₁ := by
  have key : addOrderOf (b.natAbs : ZMod m) = e₁ := by
    rw [ZMod.addOrderOf_coe b.natAbs (NeZero.ne m), Nat.gcd_comm]
  rcases Int.natAbs_eq b with h | h
  · have : (b : ZMod m) = (b.natAbs : ZMod m) := by rw [h]; simp
    grind
  · have : (b : ZMod m) = -(b.natAbs : ZMod m) := by rw [h]; simp
    rwa [this, addOrderOf_neg]
lemma d₁_dvd_b : (d₁ : ℤ) ∣ b :=
  Int.natCast_dvd.mpr (Nat.gcd_dvd_left b.natAbs m)
lemma b_zero_mod_d1 [NeZero m] : (b : ZMod d₁) = 0 :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (d₁_dvd_b (b := b))
lemma ba_coprime_d1 (h_gcd_coprime : Nat.gcd d₁ d₂ = 1) :
    Nat.Coprime (b - a).natAbs d₁ :=
  Nat.dvd_one.mp (h_gcd_coprime ▸ Nat.dvd_gcd (Nat.gcd_dvd_right _ _)
      (Nat.dvd_gcd (Nat.gcd_dvd_left _ _) (dvd_trans (Nat.gcd_dvd_right _ _) d₁_dvd_m)))
lemma orbitMap_i_eq [NeZero m] (h_gcd_coprime : Nat.gcd d₁ d₂ = 1)
    {i₁ i₂ : ZMod d₁} {j₁ j₂ : ZMod e₁}
    (heq : orbitMap m a b (i₁, j₁) = orbitMap m a b (i₂, j₂)) : i₁ = i₂ := by
  have hba_unit := isUnit_intCast_of_natAbs_coprime (ba_coprime_d1 h_gcd_coprime)
  simp only [orbitMap] at heq
  have := congr_arg (ZMod.castHom d₁_dvd_m (ZMod d₁)) heq
  simp only [map_add, map_mul, map_natCast, map_intCast] at this
  simp only [b_zero_mod_d1, mul_zero, add_zero, ZMod.natCast_val, ZMod.cast_id] at this
  exact hba_unit.mul_right_cancel this
lemma orbitMap_j_eq [NeZero m] {j₁ j₂ : ZMod e₁}
    (hj_smul : (j₁.val : ℕ) • (b : ZMod m) = (j₂.val : ℕ) • (b : ZMod m)) : j₁ = j₂ := by
  wlog h : j₁.val ≤ j₂.val with H
  · exact (H hj_smul.symm (Nat.le_of_not_le h)).symm
  · have h3 : (j₂.val - j₁.val) • (b : ZMod m) = 0 :=
      add_left_cancel (a := j₁.val • (b : ZMod m))
        (by rw [add_zero, ← add_nsmul, Nat.add_sub_cancel' h]; exact hj_smul.symm)
    have := Nat.eq_zero_of_dvd_of_lt
      ((addOrderOf_b_eq (b := b) (m := m)) ▸ addOrderOf_dvd_of_nsmul_eq_zero h3)
      (by grind [ZMod.val_lt j₁, ZMod.val_lt j₂])
    exact ZMod.val_injective _ (by grind)
lemma orbitMap_injective [NeZero m] (h_gcd_coprime : Nat.gcd d₁ d₂ = 1) :
    Function.Injective (orbitMap m a b : ZMod d₁ × ZMod e₁ → ZMod m) := by
  intro ⟨i₁, j₁⟩ ⟨i₂, j₂⟩ heq
  have hi := orbitMap_i_eq h_gcd_coprime heq
  subst hi
  simp only [orbitMap] at heq
  have hj_smul : (j₁.val : ℕ) • (b : ZMod m) = (j₂.val : ℕ) • (b : ZMod m) := by grind
  exact Prod.ext rfl (orbitMap_j_eq hj_smul)
lemma orbitMap_bijective [NeZero m] (h_gcd_coprime : Nat.gcd d₁ d₂ = 1) :
    Function.Bijective (orbitMap m a b : ZMod d₁ × ZMod e₁ → ZMod m) :=
  (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨orbitMap_injective h_gcd_coprime, by
      simp only [Fintype.card_prod, ZMod.card]
      linarith [m_eq_d₁_mul_e₁ (m := m) (b := b)]⟩
noncomputable def orbitEquiv [NeZero m]
    (h_gcd_coprime : Nat.gcd d₁ d₂ = 1) : ZMod d₁ × ZMod e₁ ≃ ZMod m :=
  Equiv.ofBijective (orbitMap m a b) (orbitMap_bijective h_gcd_coprime)
def case2b_coloring (d e : ℕ) : ZMod d × ZMod e → Fin 3 := fun ⟨i, j⟩ =>
  if i.val % 2 = 0 -- even cycle
  then if j.val = e - 1 then 1 else if j.val % 2 = 0 then 0 else 1
  else if j.val = 0 then 2 else if j.val % 2 = 0 then 0 else 2
def case2c_pattern (d k₀ i : ℕ) : Fin 3 :=
  if i = d - 1 ∧ d % 2 = 1 then if k₀ % 3 = 2 then 1 else 2
  else if i % 2 = 0 then 0
  else if k₀ % 3 = 2 then 2 else 1
def case2d_u (e : ℕ) : ℕ := e / 3 + e % 3
def case2d_v (e : ℕ) : ℕ := if e % 3 = 1 then e / 3 + 1 else e / 3
def basePattern (e : ℕ) (j : ℕ) : Fin 3 := let u := case2d_u e
  let v := case2d_v e
  if j < u then if j % 2 = 0 then 0 else 1
  else if j < u + v then if (j - u) % 2 = 0 then 1 else 2
  else if (j - u - v) % 2 = 0 then 2 else 0
def whichInterval (e j : ℕ) : Fin 3 := let u := case2d_u e
  let v := case2d_v e
  if j < u then 0 else if j < u + v then 1 else 2
def intervalColors : Fin 3 → Finset (Fin 3)
  | 0 => {0, 1}
  | 1 => {1, 2}
  | 2 => {0, 2}
end OrbitFramework
end Case2_MultipleCycles


