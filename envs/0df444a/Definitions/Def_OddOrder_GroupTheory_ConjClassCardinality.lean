-- Prove2me | Definitions.Def_OddOrder_GroupTheory_ConjClassCardinality
-- name    : OddOrder_GroupTheory_ConjClassCardinality
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:40:13.960203+00:00
-- url     : https://prove2.me/theorems/b20c4b73-e77b-4bba-941d-3fb6ec084f97
-- title:
--   Conjugacy-class cardinality: centralizer index and Sylow coprimality
-- statement:
--   A small generic lemma file extracted from the class-sum congruence development so that downstream files need not import the class-sum machinery. It contains the orbit–stabilizer fact that the size of a conjugacy class equals the index of the centralizer, $|\llbracket z\rrbracket|=[G:C_G(z)]$.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 2 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/ConjClassCardinality.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/ConjClassCardinality.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Sylow
import Mathlib.RingTheory.Int.Basic

namespace OddOrder.RepresentationTheory

variable {G : Type*} [Group G]

open MulAction

variable [Finite G]

/-- **The conjugacy-class size is the index of the centralizer** (orbit-stabilizer).  The number of
elements in the class `⟦z⟧` (`{x ∣ mk x = mk z}`) equals `[G : C_G(z)]`.  This is the
orbit-stabilizer theorem for the conjugation action `ConjAct G ↷ G`, whose orbit at `z` is the
class `(mk z).carrier` and whose stabilizer is the centralizer `C_G(z)`. -/
theorem card_class_eq_index_centralizer (z : G) :
    Nat.card { x : G // ConjClasses.mk x = ConjClasses.mk z }
      = (Subgroup.centralizer {z}).index := by
  classical
  let : Fintype G := Fintype.ofFinite G
  -- `|C_G(z)| = |stabilizer (ConjAct G) z|`: the isomorphism `toConjAct : G ≃* ConjAct G` carries
  -- `C_G(z)` bijectively onto the stabilizer (`stabilizer_eq_centralizer`).
  have hcard_cent : Nat.card (Subgroup.centralizer ({z} : Set G))
      = Nat.card (stabilizer (ConjAct G) z) := by
    refine Nat.card_congr (Equiv.subtypeEquiv (ConjAct.toConjAct (G := G)).toEquiv fun x => ?_)
    rw [ConjAct.stabilizer_eq_centralizer]
    simp only [MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe, Subgroup.mem_centralizer_iff,
      Set.mem_singleton_iff, forall_eq]
    constructor
    · intro h
      rw [← ConjAct.toConjAct_mul, ← ConjAct.toConjAct_mul, h]
    · intro h
      have := congrArg ConjAct.ofConjAct h
      simpa using this
  -- Orbit-stabilizer (`Fintype.card`): `|orbit| * |stabilizer| = |ConjAct G| = |G|`.
  have hos := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct G) z
  rw [ConjAct.card] at hos
  -- The orbit is the class `(mk z).carrier`, so `|class| * |C_G(z)| = |G|`.
  have hclass : Nat.card { x : G // ConjClasses.mk x = ConjClasses.mk z }
      * Nat.card (Subgroup.centralizer ({z} : Set G)) = Nat.card G := by
    rw [hcard_cent]
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    rw [← hos]
    congr 1
    -- `{x // mk x = mk z} ≃ orbit (ConjAct G) z` via `orbit = (mk z).carrier`.
    refine Fintype.card_congr (Equiv.subtypeEquiv (Equiv.refl G) fun x => ?_)
    rw [ConjAct.orbit_eq_carrier_conjClasses]
    rw [ConjClasses.mem_carrier_iff_mk_eq]
    rfl
  -- `[G : C_G(z)] * |C_G(z)| = |G|` too (`index_mul_card`); cancel the positive `|C_G(z)|`.
  have hidx := (Subgroup.centralizer ({z} : Set G)).index_mul_card
  have hpos : 0 < Nat.card (Subgroup.centralizer ({z} : Set G)) := Nat.card_pos
  have := hclass.trans hidx.symm
  exact Nat.eq_of_mul_eq_mul_right hpos this

/-- **Peterfalvi (6.7.3), coprimality atom `(|C₁|, p) = 1`.** Under the (6.7) setup, with `z` an
element centralized by all of the Sylow `p`-subgroup `P` (`P ≤ C_G(z)`, which holds when
`z ∈ Z(P)`), the size `|C₁| = |⟦z⟧|` of the conjugacy class of `z` is coprime (over `ℤ`) to the
order `|P|`.

Reason: `|⟦z⟧| = [G : C_G(z)]` (orbit-stabilizer).  Since `P ≤ C_G(z)`, `[G : C_G(z)] ∣ [G : P]`
(`index_dvd_of_le`), and `p ∤ [G : P]` (`Sylow.not_dvd_index`), so `p ∤ |⟦z⟧|`.  As `|P| = p^k`,
this gives `IsCoprime |⟦z⟧| |P|`. -/
theorem coprime_card_class_card_sylow {p : ℕ} [Fact p.Prime] (P : Sylow p G) {z : G}
    (hPz : (P : Subgroup G) ≤ Subgroup.centralizer {z}) :
    IsCoprime (Nat.card { x : G // ConjClasses.mk x = ConjClasses.mk z } : ℤ)
      (Nat.card (P : Subgroup G) : ℤ) := by
  -- `p ∤ |⟦z⟧|`: `|⟦z⟧| = [G:C_G(z)]`, which divides `[G:P]`, and `p ∤ [G:P]`.
  have hndvd : ¬ p ∣ Nat.card { x : G // ConjClasses.mk x = ConjClasses.mk z } := by
    rw [card_class_eq_index_centralizer]
    intro hp
    exact P.not_dvd_index (hp.trans (Subgroup.index_dvd_of_le hPz))
  -- `|P| = p ^ k`.
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card.mp P.2)
  -- Coprimality in `ℕ` (`|⟦z⟧|` coprime to `p ^ k`), transferred to `ℤ`.
  have hcopN : Nat.Coprime (Nat.card { x : G // ConjClasses.mk x = ConjClasses.mk z })
      (Nat.card (P : Subgroup G)) := by
    rw [hk]
    exact ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hndvd).symm.pow_right k
  exact_mod_cast hcopN.isCoprime

end OddOrder.RepresentationTheory


