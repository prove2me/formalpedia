-- Prove2me | Definitions.Def_Formalism_TameInertiaTowers_StatementGroup
-- name    : Formalism_TameInertiaTowers_StatementGroup
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:45:49.043973+00:00
-- url     : https://prove2.me/theorems/3c86bde1-17c8-4989-93b6-275143ecfa86
-- title:
--   Statement Group
-- statement:
--   Definitions and structural lemmas for Statement Group, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/StatementGroup.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Subgroup
open scoped commutatorElement
namespace Formalism.TwoAdicCyclotomicDecomposition
abbrev GalL (n : ℕ) : Type := (ZMod (2 ^ n))ˣ × ℤˣ × ℤˣ
def JJ (n : ℕ) : GalL n := (-1, -1, -1)
def D2 (n : ℕ) : Subgroup (GalL n) :=
  ((MonoidHom.snd ℤˣ ℤˣ).comp (MonoidHom.snd (ZMod (2 ^ n))ˣ (ℤˣ × ℤˣ))).ker
def I2 (n : ℕ) : Subgroup (GalL n) := (MonoidHom.snd (ZMod (2 ^ n))ˣ (ℤˣ × ℤˣ)).ker
def Iq (n : ℕ) : Subgroup (GalL n) := Subgroup.zpowers ((1, -1, 1) : GalL n)
def Id (n : ℕ) : Subgroup (GalL n) := Subgroup.zpowers ((1, 1, -1) : GalL n)
def u5 (n : ℕ) : (ZMod (2 ^ n))ˣ := ZMod.unitOfCoprime 5 (Nat.Coprime.pow_right n (by norm_num))
def u3 (n : ℕ) : (ZMod (2 ^ n))ˣ := ZMod.unitOfCoprime 3 (Nat.Coprime.pow_right n (by norm_num))
def resMap {s m : ℕ} (h : s ≤ m) : GalL (m + 2) →* GalL (s + 2) :=
  MonoidHom.prodMap (ZMod.unitsMap (pow_dvd_pow 2 (by omega))) (MonoidHom.id (ℤˣ × ℤˣ))
abbrev GamE (s : ℕ) : Type := GalL (s + 2) ⧸ Subgroup.zpowers ((-1, 1, 1) : GalL (s + 2))
def GG {s m : ℕ} (h : s ≤ m) : Subgroup (GalL (m + 2)) :=
  ((QuotientGroup.mk' (Subgroup.zpowers ((-1, 1, 1) : GalL (s + 2)))).comp (resMap h)).ker
def UnitsTwoPow : Prop :=
  ∀ n : ℕ,
    Nat.card (ZMod (2 ^ (n + 3)))ˣ = 2 ^ (n + 2) ∧
    orderOf (u5 (n + 3)) = 2 ^ (n + 1) ∧ orderOf (u3 (n + 3)) = 2 ^ (n + 1) ∧
    (-1 : (ZMod (2 ^ (n + 3)))ˣ) ∉ Subgroup.zpowers (u5 (n + 3)) ∧
    (-1 : (ZMod (2 ^ (n + 3)))ˣ) ∉ Subgroup.zpowers (u3 (n + 3)) ∧
    ∀ u : (ZMod (2 ^ (n + 3)))ˣ, ∃! p : Bool × Fin (2 ^ (n + 1)),
      u = (if p.1 then -1 else 1) * u5 (n + 3) ^ (p.2 : ℕ)
def QuotCyclic : Prop :=
  ∀ n : ℕ,
    IsCyclic ((ZMod (2 ^ (n + 2)))ˣ ⧸ Subgroup.zpowers (-1 : (ZMod (2 ^ (n + 2)))ˣ)) ∧
    Nat.card ((ZMod (2 ^ (n + 2)))ˣ ⧸ Subgroup.zpowers (-1 : (ZMod (2 ^ (n + 2)))ˣ)) = 2 ^ n ∧
    orderOf (QuotientGroup.mk (s := Subgroup.zpowers (-1 : (ZMod (2 ^ (n + 2)))ˣ))
      (u5 (n + 2))) = 2 ^ n ∧
    orderOf (QuotientGroup.mk (s := Subgroup.zpowers (-1 : (ZMod (2 ^ (n + 2)))ˣ))
      (u3 (n + 2))) = 2 ^ n
def TwoAdicOrder : Prop :=
  ∀ (N : ℕ) (a : ℤ), Odd a → a ^ 2 ≠ 1 →
    orderOf (a : ZMod (2 ^ N)) =
      if (a : ZMod (2 ^ N)) = 1 then 1 else 2 ^ max 1 (N + 1 - padicValInt 2 (a ^ 2 - 1))
def TwoAdicVal : Prop :=
  ∀ (a : ℤ), Odd a → a ^ 2 ≠ 1 → ∀ e : ℕ, 0 < e →
    padicValInt 2 (a ^ e - 1) =
      (if Even e then padicValInt 2 (a ^ 2 - 1) + padicValNat 2 e - 1
        else padicValInt 2 (a - 1)) ∧
    padicValInt 2 (a ^ e - 1) ≤ padicValInt 2 (a ^ 2 - 1) + Nat.log 2 e
def DecompModel : Prop :=
  ∀ n : ℕ, JJ n ∉ D2 n ∧ (D2 n).index = 2 ∧
    Function.Bijective (fun x : D2 n =>
      (QuotientGroup.mk (x : GalL n) : GalL n ⧸ Subgroup.zpowers (JJ n)))
def GmRank : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    Nat.card (GalL n ⧸ Subgroup.zpowers (JJ n)) = 2 ^ n ∧
    Nat.card ((GalL n ⧸ Subgroup.zpowers (JJ n)) ⧸
      (powMonoidHom 2 : (GalL n ⧸ Subgroup.zpowers (JJ n)) →* _).range) ≤ 8 ∧
    (3 ≤ n → Nat.card ((GalL n ⧸ Subgroup.zpowers (JJ n)) ⧸
      (powMonoidHom 2 : (GalL n ⧸ Subgroup.zpowers (JJ n)) →* _).range) = 8)
def GensModel : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    I2 n ⊔ Iq n ⊔ Id n = ⊤ ∧
    I2 n = Subgroup.closure {((-1, 1, 1) : GalL n), ((u5 n, 1, 1) : GalL n)} ∧
    Nat.card (Iq n) = 2 ∧ Nat.card (Id n) = 2 ∧
    Subgroup.closure {((-1, 1, 1) : GalL n), ((u5 n, 1, 1) : GalL n),
      ((1, -1, 1) : GalL n), ((1, 1, -1) : GalL n)} = ⊤
def GamEModel : Prop :=
  ∀ s : ℕ,
    Nat.card (GamE s) = 2 ^ (s + 2) ∧
    Nonempty (GamE s ≃* Multiplicative (ZMod (2 ^ s)) × ℤˣ × ℤˣ) ∧
    (QuotientGroup.mk (JJ (s + 2)) : GamE s) = QuotientGroup.mk ((1, -1, -1) : GalL (s + 2)) ∧
    orderOf (QuotientGroup.mk (JJ (s + 2)) : GamE s) = 2
def GGModel : Prop :=
  ∀ (s m : ℕ) (h : s ≤ m),
    Nat.card (GG h) = 2 ^ (m - s + 1) ∧
    Nonempty (GG h ≃* ℤˣ × Multiplicative (ZMod (2 ^ (m - s)))) ∧
    GG h = Subgroup.closure {((-1, 1, 1) : GalL (m + 2)), ((u5 (m + 2) ^ (2 ^ s), 1, 1) : GalL (m + 2))}
def CentralExtAbelian : Prop :=
  ∀ (H G : Type) [Group H] [CommGroup G] (π : H →* G), Function.Surjective π →
    π.ker ≤ Subgroup.center H → ∀ D : Subgroup H, D.map π = ⊤ →
    (D ⊓ π.ker = ⊥ ∨ (D = ⊤ ∧ ∀ x ∈ D, ∀ y ∈ D, x * y = y * x)) →
    ∀ x y : H, x * y = y * x
def CommGen : Prop :=
  ∀ (H : Type) [Group H] (g : Fin 4 → H),
    Subgroup.closure (Set.range g) = ⊤ → commutator H ≤ Subgroup.center H →
    g 0 * g 1 = g 1 * g 0 →
    commutator H = Subgroup.closure
      {⁅g 0, g 2⁆, ⁅g 0, g 3⁆, ⁅g 1, g 2⁆, ⁅g 1, g 3⁆, ⁅g 2, g 3⁆} ∧
    ((∀ x ∈ commutator H, x ^ 2 = 1) → Nat.card (commutator H) ≤ 2 ^ 5)
def RankBound : Prop :=
  ∀ r : ℕ, 1 ≤ r → (r * (r - 1) / 2 ≤ 3 + (r - 1) ↔ r ≤ 4)
def NormalOrderTwoCentral : Prop :=
  ∀ (H : Type) [Group H] (N : Subgroup H), N.Normal → Nat.card N = 2 → N ≤ Subgroup.center H
def TwistVal : Prop :=
  ∀ s e : ℕ, 0 < e → padicValInt 2 ((5 : ℤ) ^ (2 ^ s * e) - 1) = s + 2 + padicValNat 2 e
def CoinvLength : Prop :=
  ∀ (N : ℕ) (u : ℤ), Odd u → u ≠ 1 →
    Nat.card (ZMod (2 ^ N) ⧸ AddSubgroup.zmultiples (((u - 1 : ℤ)) : ZMod (2 ^ N))) =
      2 ^ min N (padicValInt 2 (u - 1))
def PGroupGen : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (H : Type) [Group H] [Finite H], IsPGroup p H →
    ∀ S : Set H, Subgroup.normalClosure S = ⊤ → Subgroup.closure S = ⊤
def GenusModel : Prop :=
  ∀ n : ℕ, JJ n = ((-1, 1, 1) : GalL n) * ((1, -1, 1) : GalL n) * ((1, 1, -1) : GalL n) ∧
    ((-1, 1, 1) : GalL n) ∈ I2 n ∧ ((1, -1, 1) : GalL n) ∈ Iq n ∧
    ((1, 1, -1) : GalL n) ∈ Id n ∧ ((1, -1, 1) : GalL n) ≠ 1
def GenusAbelian : Prop :=
  ∀ (G : Type) [CommGroup G] [Finite G] (A B C : Subgroup G), A ⊔ B ⊔ C = ⊤ →
    Nat.card G = Nat.card A * Nat.card B * Nat.card C →
    ∀ a ∈ A, ∀ b ∈ B, ∀ c ∈ C, a * b * c = 1 → a = 1 ∧ b = 1 ∧ c = 1
end Formalism.TwoAdicCyclotomicDecomposition


