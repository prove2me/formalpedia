-- Prove2me | Definitions.Def_OddOrder_BG_Ch2_Uniqueness_S09_Uniqueness
-- name    : OddOrder_BG_Ch2_Uniqueness_S09_Uniqueness
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T06:41:22.586198+00:00
-- url     : https://prove2.me/theorems/aad3a1d8-163a-4dc9-9487-aac896e174c0
-- title:
--   BG §9: the Uniqueness Theorem (Theorem 9.6)
-- statement:
--   Formalizes Theorem 9.6 (the Uniqueness Theorem) of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, §9: if $r(K)\ge 2$ and either $r(K)\ge 3$ or $r(C_G(K))\ge 3$, then $K\in\mathcal{U}$. The file is the capstone of §9 and a hub that gathers the Theorem 9.1, Corollaries and Lemma 9.5 files so that later sections can import all of §9.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 3 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch2_Uniqueness/S09_Uniqueness.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch2_Uniqueness/S09_Uniqueness.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch2_Uniqueness_Setup
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S05_NarrowPGroups
import Definitions.Def_OddOrder_BG_Ch2_Uniqueness_S07_Transitivity
import Definitions.Def_OddOrder_BG_Ch2_Uniqueness_S08_FittingOfMaximal
import Definitions.Def_OddOrder_GroupTheory_MaximalSubgroup
import Definitions.Def_OddOrder_GroupTheory_AInvariantPiSubgroups
import Definitions.Def_OddOrder_GroupTheory_PRank
import Definitions.Def_OddOrder_GroupTheory_OmegaSubgroup
import Definitions.Def_OddOrder_GroupTheory_ElementaryAbelianFamily
import Definitions.Def_OddOrder_BG_Ch2_Uniqueness_S09_Theorem91
import Definitions.Def_OddOrder_BG_Ch2_Uniqueness_S09_Corollaries
import Definitions.Def_OddOrder_BG_Ch2_Uniqueness_S09_Lemma95

namespace OddOrder.BG.Ch2.S09

open OddOrder.GroupTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **BG Theorem 9.6 (The Uniqueness Theorem)** (mmd L2627): `K < G`, `r(K) ≥ 2`、
`r(K) ≥ 3` または `r(C_G(K)) ≥ 3` ⇒ `K ∈ 𝒰`。線形チェーン 9.1→9.5 の終結。

Proof gate: mmd L2629 applies BG Lem 5.1 to obtain an `SCN₃(P)` subgroup inside a
Sylow `p`-subgroup containing an elementary abelian subgroup of rank 3. This is the
direct §5 dependency for §9 and should not be replaced by Peterfalvi-style type
classification hypotheses. Lean carries `K < ⊤` explicitly because `K ∈ 𝒰` includes
properness by definition. -/
theorem uniquenessTheorem [Finite G] (hG : IsMinimalSimpleOdd G)
    {K : Subgroup G} (hKlt : K < ⊤) (hr2 : 2 ≤ rank ↥K)
    (hr3 : 3 ≤ rank ↥K ∨ 3 ≤ rank ↥(Subgroup.centralizer (K : Set G))) :
    IsUniquelyMaximal K := by
  rcases hr3 with h3K | h3C
  · exact isUniquelyMaximal_of_three_le_rank_of_lt_top hG hKlt h3K
  · let C : Subgroup G := Subgroup.centralizer (K : Set G)
    have hClt : C < ⊤ := centralizer_lt_top_of_two_le_rank hG hr2
    have hCU : IsUniquelyMaximal C :=
      isUniquelyMaximal_of_three_le_rank_of_lt_top hG hClt h3C
    have hKleCC : K ≤ Subgroup.centralizer (C : Set G) := by
      intro k hk
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      exact (Subgroup.mem_centralizer_iff.mp hc k hk).symm
    exact isUniquelyMaximal_of_le_centralizer_of_two_le_rank hG hCU hKleCC hr2

/-- If an elementary abelian subgroup of order `p^2` is not maximal among elementary abelian
`p`-subgroups, then its centralizer has rank at least three. This is the rank bridge behind
BG Theorem 9.6's "in particular" clause. -/
private theorem three_le_rank_centralizer_of_mem_e2_not_maximal [Finite G]
    {p : ℕ} [Fact p.Prime] {A : Subgroup G} (hA2 : A ∈ elemAbelianOfRank G p 2)
    (hAns : ¬ IsMaximalElementaryAbelian p A) :
    3 ≤ rank ↥(Subgroup.centralizer (A : Set G)) := by
  classical
  have hAea : A.IsElementaryAbelian p := hA2.1
  have hAcard : Nat.card A = p ^ 2 := hA2.2
  have hnot_max :
      ¬ ∀ F : Subgroup G, F.IsElementaryAbelian p → A ≤ F → F = A := by
    intro hmax
    exact hAns ⟨hAea, hmax⟩
  push Not at hnot_max
  obtain ⟨F, hFea, hAF, hFne⟩ := hnot_max
  have hAlt : A < F := lt_of_le_of_ne hAF (fun h => hFne h.symm)
  have hAcard_lt_Fcard : Nat.card A < Nat.card F :=
    Set.Finite.card_lt_card (Set.toFinite (F : Set G)) (hAlt : (A : Set G) ⊂ (F : Set G))
  have hp2_lt_Fcard : p ^ 2 < Nat.card F := by
    simpa [hAcard] using hAcard_lt_Fcard
  obtain ⟨k, hFcard_pow⟩ := IsPGroup.iff_card.mp hFea.isPGroup
  have htwo_lt_k : 2 < k := by
    have hpow_lt : p ^ 2 < p ^ k := by
      simpa [hFcard_pow] using hp2_lt_Fcard
    exact (Nat.pow_lt_pow_iff_right (Fact.out : p.Prime).one_lt).mp hpow_lt
  have hp3_le_Fcard : p ^ 3 ≤ Nat.card F := by
    rw [hFcard_pow]
    exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos (by omega)
  let C : Subgroup G := Subgroup.centralizer (A : Set G)
  have hFC : F ≤ C := by
    intro f hf
    dsimp [C]
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact congrArg Subtype.val (hFea.comm ⟨a, hAF ha⟩ ⟨f, hf⟩)
  let Fsub : Subgroup C := F.subgroupOf C
  have hFsub_elem : Fsub.IsElementaryAbelian p :=
    IsElementaryAbelian.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hFC).symm hFea
  have hFsub_card : Nat.card Fsub = Nat.card F :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFC).toEquiv
  have hlog_ge : 3 ≤ Nat.log p (Nat.card Fsub) := by
    rw [hFsub_card]
    exact Nat.le_log_of_pow_le (Fact.out : p.Prime).one_lt hp3_le_Fcard
  have h3pRank : 3 ≤ pRank C p := hlog_ge.trans (le_pRank Fsub hFsub_elem)
  exact h3pRank.trans (pRank_le_rank (G := ↥C) p)

/-- **BG Theorem 9.6 系** (mmd L2627 "In particular"): `A ∈ ℰ²(G) − ℰ*(G)` (位数 `p²` の
elem-ab で極大でない) なら `A ∈ 𝒰`。 -/
theorem isUniquelyMaximal_of_mem_e2_not_maximal [Finite G] (hG : IsMinimalSimpleOdd G)
    {p : ℕ} [Fact p.Prime] {A : Subgroup G} (hA2 : A ∈ elemAbelianOfRank G p 2)
    (hAns : ¬ IsMaximalElementaryAbelian p A) :
    IsUniquelyMaximal A := by
  have hAea : A.IsElementaryAbelian p := hA2.1
  have h2pRank : 2 ≤ pRank ↥A p := by
    have hlog_le : Nat.log p (Nat.card A) ≤ pRank ↥A p := hAea.log_card_le_pRank
    have hlog : Nat.log p (Nat.card A) = 2 := by
      rw [hA2.2, Nat.log_pow (Fact.out : p.Prime).one_lt]
    exact (le_of_eq hlog.symm).trans hlog_le
  have hr2 : 2 ≤ rank ↥A := h2pRank.trans (pRank_le_rank (G := ↥A) p)
  have hAlt : A < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro hAtop
    have hcomm : ∀ a b : G, a * b = b * a := by
      intro a b
      exact congrArg Subtype.val
        (hAea.comm (⟨a, hAtop ▸ Subgroup.mem_top a⟩ : A)
          (⟨b, hAtop ▸ Subgroup.mem_top b⟩ : A))
    exact hG.notSolvable (Group.isSolvable_of_comm hcomm)
  exact uniquenessTheorem hG hAlt hr2
    (Or.inr (three_le_rank_centralizer_of_mem_e2_not_maximal hA2 hAns))

end OddOrder.BG.Ch2.S09


