-- Prove2me | Definitions.Def_OddOrder_GroupTheory_NilpotentCoprimeCommute
-- name    : OddOrder_GroupTheory_NilpotentCoprimeCommute
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:49:52.184635+00:00
-- url     : https://prove2.me/theorems/fb03cd33-8aca-4b73-8502-779c0968095a
-- title:
--   Coprime-order elements of a finite nilpotent group commute
-- statement:
--   A general theorem of finite group theory, independent of either book: a finite nilpotent group is the internal direct product of its Sylow subgroups, so two elements of coprime orders lie in complementary factors and commute. It was originally written as a helper for Bender–Glauberman Proposition 10.11(d).
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 1 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/NilpotentCoprimeCommute.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/NilpotentCoprimeCommute.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Isaacs_Ch01_Sylow_Main

namespace OddOrder.GroupTheory

open OddOrder.Isaacs

/-- In a finite nilpotent group, two elements of coprime order commute.

A finite nilpotent group is the internal direct product of its Sylow subgroups
(`Sylow.directProductOfNormal`); two coprime-order elements have disjoint sets of relevant
primes, so in every Sylow factor at least one of their components is trivial. -/
theorem commute_of_coprime_orderOf_of_isNilpotent {L : Type*} [Group L] [Finite L]
    [Group.IsNilpotent L] {x y : L} (hxy : Nat.Coprime (orderOf x) (orderOf y)) :
    Commute x y := by
  classical
  have := Fintype.ofFinite L
  have hn : ∀ {q : ℕ} [Fact q.Prime] (Q : Sylow q L), Q.Normal := fun Q =>
    Ch01.Sylow.normal_of_isNilpotent Q
  set e := Sylow.directProductOfNormal hn with he
  -- Componentwise: the `(p, P)`-components of `e.symm x` and `e.symm y` commute in the
  -- `p`-group `↥P`, since at least one of them is trivial.
  have hcomp : ∀ (p : (Nat.card L).primeFactors) (P : Sylow (p : ℕ) L),
      Commute (e.symm x p P) (e.symm y p P) := by
    intro p P
    have : Fact (p : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
    -- The order of a component divides the order of the original element.
    have hdvd : ∀ z : L, orderOf (e.symm z p P) ∣ orderOf z := by
      intro z
      apply orderOf_dvd_of_pow_eq_one
      have h1 : (e.symm z) ^ orderOf z = 1 := by rw [← map_pow, pow_orderOf_eq_one, map_one]
      have h2 := congrFun (congrFun h1 p) P
      simpa [Pi.pow_apply, Pi.one_apply] using h2
    -- Each component has prime-power order (it lies in the `p`-group `↥P`).
    have hppow : ∀ z : L, ∃ k, orderOf (e.symm z p P) = (p : ℕ) ^ k := fun z =>
      (IsPGroup.iff_orderOf.mp P.isPGroup') (e.symm z p P)
    by_cases hpx : (p : ℕ) ∣ orderOf x
    · -- Then `p ∤ orderOf y`, so the `y`-component is trivial.
      have hpy : ¬ (p : ℕ) ∣ orderOf y := fun hpy =>
        (Nat.prime_of_mem_primeFactors p.2).ne_one (Nat.dvd_one.mp (hxy ▸ Nat.dvd_gcd hpx hpy))
      obtain ⟨k, hk⟩ := hppow y
      have hk0 : k = 0 := by
        by_contra hkne
        exact hpy ((hk ▸ dvd_pow_self (p : ℕ) hkne).trans (hdvd y))
      have hy1 : e.symm y p P = 1 := orderOf_eq_one_iff.mp (by rw [hk, hk0, pow_zero])
      rw [hy1]; exact Commute.one_right _
    · -- `p ∤ orderOf x`, so the `x`-component is trivial.
      obtain ⟨k, hk⟩ := hppow x
      have hk0 : k = 0 := by
        by_contra hkne
        exact hpx ((hk ▸ dvd_pow_self (p : ℕ) hkne).trans (hdvd x))
      have hx1 : e.symm x p P = 1 := orderOf_eq_one_iff.mp (by rw [hk, hk0, pow_zero])
      rw [hx1]; exact Commute.one_left _
  -- Assemble componentwise commutation, then transport along the isomorphism `e`.
  have hkey : e.symm x * e.symm y = e.symm y * e.symm x := by
    funext p P
    simpa [Pi.mul_apply, commute_iff_eq] using hcomp p P
  have hcong := congrArg e hkey
  rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at hcong

end OddOrder.GroupTheory


