-- Prove2me | Definitions.Def_OddOrder_GroupTheory_CyclicSubgroupUniqueness
-- name    : OddOrder_GroupTheory_CyclicSubgroupUniqueness
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:40:22.281261+00:00
-- url     : https://prove2.me/theorems/252700a4-cecd-4bb5-9de3-8ad3532df051
-- title:
--   Subgroups of a finite cyclic group are determined by their order
-- statement:
--   In a finite cyclic group $C$, the subgroup of any given order is unique: two subgroups of equal cardinality are equal. The proof identifies an order-$d$ subgroup with the kernel of the $d$-th power map. This is a general fact of finite group theory, consolidating three identical copies that previously existed in the Bender–Glauberman files.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 1 supporting lemma used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/CyclicSubgroupUniqueness.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/CyclicSubgroupUniqueness.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Mathlib.GroupTheory.SpecificGroups.Cyclic

namespace OddOrder.GroupTheory

/-- In a finite cyclic group, two subgroups of the same order coincide.

Both subgroups are shown to equal `(powMonoidHom d).ker` for `d` their common order: the
inclusion `≤` holds because every element of an order-`d` subgroup satisfies `g ^ d = 1`, and
the reverse follows by counting, since the kernel has order `gcd d (Nat.card C) = d`. -/
theorem cyclic_subgroup_eq_of_card_eq {C : Type*} [Group C] [Finite C] [IsCyclic C]
    {H₁ H₂ : Subgroup C} (h : Nat.card H₁ = Nat.card H₂) : H₁ = H₂ := by
  let : CommGroup C := IsCyclic.commGroup
  have key : ∀ {N : Subgroup C} {d : ℕ},
      Nat.card N = d → N = (powMonoidHom d : C →* C).ker := by
    intro N d hN
    have hN_le : N ≤ (powMonoidHom d : C →* C).ker := by
      intro g hg
      rw [MonoidHom.mem_ker, powMonoidHom_apply]
      have hg1 : (⟨g, hg⟩ : N) ^ Nat.card N = 1 := pow_card_eq_one'
      have := congrArg (Subtype.val) hg1
      rwa [SubmonoidClass.coe_pow, OneMemClass.coe_one, hN] at this
    have hd_dvd : d ∣ Nat.card C := hN ▸ N.card_subgroup_dvd_card
    have hker_card : Nat.card (powMonoidHom d : C →* C).ker = d := by
      rw [IsCyclic.card_powMonoidHom_ker (G := C) d, Nat.gcd_eq_right hd_dvd]
    exact Subgroup.eq_of_le_of_card_ge hN_le (by rw [hker_card, hN])
  exact (key (d := Nat.card H₁) rfl).trans (key (d := Nat.card H₁) h.symm).symm

end OddOrder.GroupTheory


