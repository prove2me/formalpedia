-- Prove2me | Definitions.Def_OddOrder_GroupTheory_OpResidual
-- name    : OddOrder_GroupTheory_OpResidual
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:49:42.362091+00:00
-- url     : https://prove2.me/theorems/c8e6198b-cfb1-4434-88a3-e6fb42f61f0a
-- title:
--   $O_\pi(G)$: the largest normal $\pi$-subgroup (definitional skeleton)
-- statement:
--   A definitional skeleton for the largest normal $\pi$-subgroup of a finite group, for a set of primes $\pi$. It supports Bender–Glauberman §1 Prop. 1.4 and §6 (Thm 6.4), which use the $O_\pi$ machinery generalizing the single-prime $O_p$. Mathlib does not define $O_\pi$.
--
--   Main definitions: `Subgroup.IsPiSubgroup` (all primes dividing $|N|$ lie in $\pi$) and `Subgroup.opPi` (the supremum of all normal $\pi$-subgroups of $G$).
--
--   The bundle also proves 3 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/OpResidual.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/OpResidual.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Isaacs_Ch01_Sylow_Main
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.SchurZassenhaus
import Mathlib.Data.SetLike.Fintype

namespace Subgroup

variable {G : Type*} [Group G]

/-- A subgroup is a `π`-subgroup if every prime dividing its order lies in `π`. -/
def IsPiSubgroup (π : Set ℕ) (N : Subgroup G) : Prop :=
  ∀ p ∈ (Nat.card N).primeFactors, p ∈ π

namespace IsPiSubgroup

variable {π : Set ℕ} {N M : Subgroup G}

@[simp] theorem bot : (⊥ : Subgroup G).IsPiSubgroup π := by
  intro p hp
  simp at hp

theorem mono {π₁ π₂ : Set ℕ} (h : π₁ ⊆ π₂) (hN : N.IsPiSubgroup π₁) :
    N.IsPiSubgroup π₂ :=
  fun p hp => h (hN p hp)

end IsPiSubgroup

/-- A `p`-group is a `π`-subgroup whenever `p ∈ π` (its order is a power of `p`, so `p` is
the only prime dividing it). -/
theorem isPiSubgroup_of_isPGroup_of_mem {G : Type*} [Group G] [Finite G] {π : Set ℕ} {p : ℕ}
    [Fact p.Prime] {X : Subgroup G} (hX : IsPGroup p ↥X) (hp : p ∈ π) : X.IsPiSubgroup π := by
  intro q hq
  obtain ⟨k, hk⟩ := hX.exists_card_eq
  rw [hk] at hq
  have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hqp : q = p :=
    (Nat.prime_dvd_prime_iff_eq hq_prime Fact.out).mp
      (hq_prime.dvd_of_dvd_pow (Nat.mem_primeFactors.mp hq).2.1)
  rwa [hqp]

end Subgroup


