-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S14_MaximalI_CentralizerContainment
-- name    : OddOrder_Peterfalvi_S14_MaximalI_CentralizerContainment
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T14:12:27.431532+00:00
-- url     : https://prove2.me/theorems/253c252d-b1d8-4c67-b85f-845d7a9565ea
-- title:
--   Peterfalvi (8.6.a)/(8.16): centralizer containment for type $P$ maximals
-- statement:
--   Collects the centralizer-containment facts of Peterfalvi (8.6.a) and (8.16) for type $P$ maximal subgroups. The bundle consists of lemmas only.
--
--   The bundle also proves 3 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S14_MaximalI/CentralizerContainment.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S14_MaximalI/CentralizerContainment.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S14_MaximalI_FrobeniusStructure

namespace OddOrder.Peterfalvi.S14

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **Normalizer bridge** (used by (12.10) and (12.17)): a maximal subgroup `L` of a minimal
simple group of odd order is the normalizer of its maximal nilpotent normal Hall subgroup `L_F`,
as soon as `L_F ≠ ⊥`.

`L ≤ N_G(L_F)` is `maxNilpotentNormalHall_le_normalizer`.  If `N_G(L_F) = ⊤` then `L_F ⊴ G`, so by
simplicity `L_F = ⊥` or `⊤`; both are excluded (`L_F ≠ ⊥` by hypothesis, `L_F ≤ L < ⊤`).  Hence
`L ≤ N_G(L_F) < ⊤`, and `L` being a coatom upgrades the containment to equality. -/
theorem maximalSubgroup_eq_normalizer_maxNilpotentNormalHall [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {L : Subgroup G} (hL : L ∈ maximalSubgroups G)
    (hne : maxNilpotentNormalHall L ≠ ⊥) :
    L = Subgroup.normalizer (maxNilpotentNormalHall L : Set G) := by
  have hco : IsCoatom L := hL
  have hLleN : L ≤ Subgroup.normalizer (maxNilpotentNormalHall L : Set G) :=
    OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer L
  refine le_antisymm hLleN ?_
  rcases hLleN.lt_or_eq with hlt | heq
  · -- `L < N_G(L_F)` would force `N_G(L_F) = ⊤`, making `L_F ⊴ G`, which simplicity excludes.
    exfalso
    have hNtop : Subgroup.normalizer (maxNilpotentNormalHall L : Set G) = ⊤ := hco.2 _ hlt
    have hHnormal : (maxNilpotentNormalHall L).Normal := Subgroup.normalizer_eq_top_iff.mp hNtop
    rcases hG.simple.eq_bot_or_eq_top_of_normal (maxNilpotentNormalHall L) hHnormal with hb | ht
    · exact hne hb
    · have hle : maxNilpotentNormalHall L ≤ L := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le L
      rw [ht] at hle
      exact hco.1 (top_le_iff.mp hle)
  · exact heq.ge

/-- **Peterfalvi (8.6.a) centralizer containment for type-`P` kernels**: for a maximal `L` of
type II–IV — i.e. carrying the `TypePNontrivialCore` of Definition (8.6), whose clause (a) makes
`L_F^#` a TI-subset with normalizer `N_G(L_F)` — every nonidentity `y ∈ L_F` has `C_G(y) ≤ L`.

An element `c ∈ C_G(y)` fixes `y ∈ L_F^# ∩ (L_F^#)^c`, so the TI property puts
`c ∈ N_G(L_F) = L` (`maximalSubgroup_eq_normalizer_maxNilpotentNormalHall`).  This is the (8.16)
proof's "`(8.6.a)` implies `R(a) = 1`" mechanism, exposed as the containment the (12.10) type
exclusions consume.  (The textbook (8.6.a) states the TI property for the full Fitting subgroup
`F(L)^# ⊇ L_F^#`; the Lean `TypePNontrivialCore` carries the `L_F`-form, which is what we use.) -/
theorem typeP_core_centralizer_le_of_mem_fitting [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {L : Subgroup G} (hL : L ∈ maximalSubgroups G)
    {data : TypePData L} (hcore : TypePNontrivialCore L data)
    {y : G} (hy : y ∈ maxNilpotentNormalHall L) (hy1 : y ≠ 1) :
    Subgroup.centralizer ({y} : Set G) ≤ L := by
  obtain ⟨-, -, hTI⟩ := hcore
  have hne : maxNilpotentNormalHall L ≠ ⊥ := by
    intro hb
    rw [hb] at hy
    exact hy1 (Subgroup.mem_bot.mp hy)
  have hNL := maximalSubgroup_eq_normalizer_maxNilpotentNormalHall hG hL hne
  intro c hc
  have hcy : c * y * c⁻¹ = y := by
    rw [mul_inv_eq_iff_eq_mul]
    exact Subgroup.mem_centralizer_singleton_iff.mp hc
  have hysharp : y ∈ OddOrder.GroupTheory.sharpSubgroup (maxNilpotentNormalHall L) :=
    ⟨hy, by simpa using hy1⟩
  rw [hNL]
  exact hTI c ⟨y, hysharp, by rw [hcy]; exact hysharp⟩

/-- **Peterfalvi (8.16) centralizer-containment, Type II**: for a maximal subgroup `L` of
Type II, `C_G(y) ⊆ L` for every nonidentity `y ∈ L_s` (`L_s = L_F` for Type II).

This is the "By (8.16), `C_G(y) ⊆ L` for all `y ∈ A(L)`" step of (12.10), restricted to the
`A_1(L) = L_s^#` core the witness argument uses.  Peterfalvi's (8.16) proof reduces the `A_1(L)`
case to exactly clause (a) of Definition (8.6) — the kernel-sharp TI-set — which the Lean
`TypeIIData` carries in its `TypePNontrivialCore`; the containment is then
`typeP_core_centralizer_le_of_mem_fitting`. -/
theorem typeII_centralizer_le_of_mem_mainSubgroup [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {L : Subgroup G} (hL : L ∈ maximalSubgroups G)
    (hII : IsTypeII L) {y : G} (hy : y ∈ mainSubgroup L PeterfalviType.II) (hy1 : y ≠ 1) :
    Subgroup.centralizer ({y} : Set G) ≤ L := by
  obtain ⟨iiData⟩ := hII
  exact typeP_core_centralizer_le_of_mem_fitting hG hL iiData.common
    (by simpa [mainSubgroup] using hy) hy1

end OddOrder.Peterfalvi.S14


