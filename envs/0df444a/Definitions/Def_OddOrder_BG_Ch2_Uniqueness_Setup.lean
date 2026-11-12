-- Prove2me | Definitions.Def_OddOrder_BG_Ch2_Uniqueness_Setup
-- name    : OddOrder_BG_Ch2_Uniqueness_Setup
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:44:16.550516+00:00
-- url     : https://prove2.me/theorems/e31f92df-9367-49f8-a20d-25665c60a101
-- title:
--   The fixed minimal counterexample $G$ (BG §7)
-- statement:
--   Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, §7: assume the main theorem is false and let $G$ be a counterexample of minimal order, a nonabelian simple group. This is the ambient hypothesis under which Chapters II-IV (BG §7-§16) operate.
--
--   The main structure is `IsMinimalSimpleOdd`, the working hypotheses of the fixed minimal counterexample $G$.
--
--   The bundle also proves 7 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch2_Uniqueness/Setup.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch2_Uniqueness/Setup.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_MaximalSubgroup
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Nilpotent
import Mathlib.SetTheory.Cardinal.Finite

namespace OddOrder.BG

/-- **BG fixed counterexample `G`** (§7, mmd L2133): the working hypotheses of a *minimal
counterexample of odd order* to the Odd Order Theorem. `G` is finite of odd order, simple,
non-solvable (a genuine counterexample, hence nonabelian simple), and — by minimality of the
order — every proper subgroup of `G` is solvable.

All of BG Chapters II–IV (§7–§16) are stated under `(hG : IsMinimalSimpleOdd G)`. -/
structure IsMinimalSimpleOdd (G : Type*) [Group G] [Finite G] : Prop where
  /-- `|G|` is odd. -/
  odd : Odd (Nat.card G)
  /-- `G` is simple. -/
  simple : IsSimpleGroup G
  /-- `G` is not solvable (it is a counterexample). Together with `simple` this is "`G` is a
  nonabelian simple group" (BG: "Of course `G` is a nonabelian simple group"). -/
  notSolvable : ¬ Group.IsSolvable G
  /-- Minimality of the counterexample: every proper subgroup of `G` is solvable. -/
  properSolvable : ∀ M : Subgroup G, M < ⊤ → Group.IsSolvable M

namespace IsMinimalSimpleOdd

variable {G : Type*} [Group G] [Finite G]

/-- A minimal simple counterexample is nontrivial (it is simple, hence has `> 1` element). -/
theorem nontrivial (hG : IsMinimalSimpleOdd G) : Nontrivial G :=
  have : IsSimpleGroup G := hG.simple
  inferInstance

/-- Every proper subgroup of a minimal counterexample is solvable. -/
theorem isSolvable_of_lt_top (hG : IsMinimalSimpleOdd G) (M : Subgroup G) (hM : M < ⊤) :
    Group.IsSolvable M :=
  hG.properSolvable M hM

/-- Every maximal subgroup of a minimal counterexample is solvable. -/
theorem isSolvable_of_isCoatom (hG : IsMinimalSimpleOdd G) {M : Subgroup G} (hM : IsCoatom M) :
    Group.IsSolvable M :=
  hG.isSolvable_of_lt_top M hM.lt_top

/-- A minimal simple group is perfect: `G' = G`.

`G'` is normal, so simplicity leaves `⊥` or `⊤`; `G' = ⊥` would make `G` solvable of derived
length `1`. -/
theorem commutator_eq_top (hG : IsMinimalSimpleOdd G) : commutator G = ⊤ := by
  refine (hG.simple.eq_bot_or_eq_top_of_normal (commutator G) inferInstance).resolve_left ?_
  intro h
  exact hG.notSolvable ⟨1, by rw [derivedSeries_one]; exact h⟩

/-- The `ℳ`-membership form of `isSolvable_of_isCoatom`. -/
theorem isSolvable_of_mem_maximalSubgroups (hG : IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ OddOrder.GroupTheory.maximalSubgroups G) :
    Group.IsSolvable M :=
  hG.isSolvable_of_isCoatom (OddOrder.GroupTheory.mem_maximalSubgroups.mp hM)

/-- A maximal subgroup of a minimal counterexample is nontrivial. If `⊥` were maximal,
any nontrivial Sylow subgroup would be all of `G`, making `G` a finite `p`-group and hence
solvable. -/
theorem ne_bot_of_isCoatom (hG : IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : IsCoatom M) :
    M ≠ ⊥ := by
  classical
  intro hMbot
  have : Nontrivial G := hG.nontrivial
  have hcard_ne : Nat.card G ≠ 1 := ne_of_gt (Finite.one_lt_card (α := G))
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hcard_ne
  have : Fact p.Prime := ⟨hp⟩
  let P : Sylow p G := Classical.arbitrary (Sylow p G)
  have hP_ne : (P : Subgroup G) ≠ ⊥ := P.ne_bot_of_dvd_card hpdvd
  have hbot_co : IsCoatom (⊥ : Subgroup G) := by simpa [hMbot] using hM
  have hP_top : (P : Subgroup G) = ⊤ := by
    exact (hbot_co.le_iff.mp bot_le).resolve_right hP_ne
  have hPp : IsPGroup p G :=
    (hP_top ▸ P.isPGroup' : IsPGroup p ↥(⊤ : Subgroup G)).of_equiv Subgroup.topEquiv
  have : Group.IsNilpotent G := IsPGroup.isNilpotent hPp
  exact hG.notSolvable IsNilpotent.to_isSolvable

/-- The `ℳ`-membership form of `ne_bot_of_isCoatom`. -/
theorem ne_bot_of_mem_maximalSubgroups (hG : IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ OddOrder.GroupTheory.maximalSubgroups G) :
    M ≠ ⊥ :=
  hG.ne_bot_of_isCoatom (OddOrder.GroupTheory.mem_maximalSubgroups.mp hM)

end IsMinimalSimpleOdd

end OddOrder.BG


