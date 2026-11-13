-- Prove2me | Definitions.Def_OddOrder_BG_Ch2_Uniqueness_S09_Corollaries
-- name    : OddOrder_BG_Ch2_Uniqueness_S09_Corollaries
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T06:33:23.752172+00:00
-- url     : https://prove2.me/theorems/80770080-ae65-491f-ad4f-746f3f458832
-- title:
--   BG §9: Corollaries 9.2, 9.3 and Lemma 9.4 (centralizer and rank criteria)
-- statement:
--   Formalizes Corollaries 9.2 and 9.3 and Lemma 9.4 of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, §9. These extend Theorem 9.1 by turning the criterion for membership in $\mathcal{U}$ into criteria in terms of centralizers and ranks.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 29 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch2_Uniqueness/S09_Corollaries.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch2_Uniqueness/S09_Corollaries.lean
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

namespace OddOrder.BG.Ch2.S09

open OddOrder.GroupTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **BG Corollary 9.2** (mmd L2541): `L ∈ 𝒰`, `K ≤ C_G(L)`, `r(K) ≥ 2` ⇒ `K ∈ 𝒰`。 -/
theorem isUniquelyMaximal_of_le_centralizer_of_two_le_rank [Finite G] (hG : IsMinimalSimpleOdd G)
    {L K : Subgroup G} (hL : IsUniquelyMaximal L) (hKL : K ≤ Subgroup.centralizer (L : Set G))
    (hr : 2 ≤ rank ↥K) :
    IsUniquelyMaximal K := by
  classical
  obtain ⟨p, hp, A, hAea, hAK, hAnc⟩ :=
    exists_isElementaryAbelian_not_isCyclic_le_of_two_le_rank K hr
  have : Fact p.Prime := ⟨hp⟩
  let M : Subgroup G := hL.uniqueMaximalSubgroup
  have hKleM : K ≤ M := by
    intro k hk
    by_cases hk1 : k = 1
    · simp [M, hk1]
    · have hkL : k ∈ Subgroup.centralizer (L : Set G) := hKL hk
      have hCGleM : Subgroup.centralizer ({k} : Set G) ≤ M :=
        centralizer_singleton_le_uniqueMaximalSubgroup_of_mem_centralizer hG hL hkL hk1
      exact hCGleM (by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst y
        rfl)
  have hAleM : A ≤ M := hAK.trans hKleM
  have hcent : ∀ b : G, b ∈ A → b ≠ 1 → Subgroup.centralizer ({b} : Set G) ≤ M := by
    intro b hb hb1
    have hbL : b ∈ Subgroup.centralizer (L : Set G) := hKL (hAK hb)
    exact centralizer_singleton_le_uniqueMaximalSubgroup_of_mem_centralizer hG hL hbL hb1
  have hAU : IsUniquelyMaximal A :=
    noncyclic_isUniquelyMaximal_of_centralizer_le hG
      (hM := hL.uniqueMaximalSubgroup_isCoatom) hAea hAleM hAnc (Or.inl hcent)
  have hKlt : K < ⊤ :=
    lt_of_le_of_lt hKleM hL.uniqueMaximalSubgroup_isCoatom.1.lt_top
  exact hAU.of_le_of_lt_top hAK hKlt

/-- An abelian rank-three `p`-subgroup has centralizer of `pRank` at least three. -/
private theorem three_le_pRank_centralizer_of_isMulCommutative_of_isPGroup_of_three_le_rank
    [Finite G] {p : ℕ} [Fact p.Prime] {A : Subgroup G}
    (hAab : IsMulCommutative A) (hAp : IsPGroup p A) (hr : 3 ≤ rank ↥A) :
    3 ≤ pRank ↥(Subgroup.centralizer (A : Set G)) p := by
  have h3A : 3 ≤ pRank ↥A p := three_le_pRank_of_isPGroup_of_three_le_rank hAp hr
  have hA_le_C : A ≤ Subgroup.centralizer (A : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (isMulCommutative_iff.mp hAab ⟨y, hy⟩ ⟨x, hx⟩)
  exact h3A.trans
    (pRank_le_of_injective (f := Subgroup.inclusion hA_le_C)
      (Subgroup.inclusion_injective hA_le_C))

/-- Rank at least two rules out cyclicity. -/
private theorem not_isCyclic_of_two_le_rank [Finite G] {A : Subgroup G}
    (hr : 2 ≤ rank ↥A) :
    ¬ IsCyclic ↥A := by
  obtain ⟨q, hq, E, _hEea, hEA, hEnc⟩ :=
    exists_isElementaryAbelian_not_isCyclic_le_of_two_le_rank A hr
  intro hAcyc
  exact hEnc
    (isCyclic_of_injective (Subgroup.inclusion hEA)
      (Subgroup.inclusion_injective hEA))

/-- A finite odd `p`-group of `pRank` at least three has a normal elementary abelian
subgroup of order `p^2`.

This is the local S09 package of BG Lemma 5.1(b) followed by BG Lemma 1.22: first get a
normal elementary abelian subgroup of order `p^3`, then take a normal subgroup of order
`p^2` inside it. -/
private theorem exists_normal_isElementaryAbelian_card_prime_sq_of_three_le_pRank
    {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]
    (hp : Odd p) (hR : IsPGroup p R) (h3 : 3 ≤ pRank R p) :
    ∃ D : Subgroup R, D.Normal ∧ D.IsElementaryAbelian p ∧ Nat.card D = p ^ 2 := by
  obtain ⟨A, hA⟩ := OddOrder.BG.Ch1.S05.scn3_nonempty_of_three_le_pRank hp hR h3
  obtain ⟨B, hB_normal, hB_elem, hBcard⟩ :=
    OddOrder.BG.Ch1.S05.exists_normal_isElementaryAbelian_card_prime_cube_of_scn3 hR hA
  have : B.Normal := hB_normal
  have hB_dvd : p ^ 2 ∣ Nat.card B := by
    rw [hBcard]
    exact pow_dvd_pow p (by norm_num : 2 ≤ 3)
  obtain ⟨D, hD_normal, hD_le_B, hDcard⟩ :=
    OddOrder.BG.Ch1.S01.normal_subgroup_card_pow_le_of_pGroup
      (G := R) (p := p) hR (N := B) (r := 2) hB_dvd
  have hD_elem : D.IsElementaryAbelian p := by
    have hD_sub_elem : (D.subgroupOf B).IsElementaryAbelian p :=
      hB_elem.to_subgroup (D.subgroupOf B)
    exact IsElementaryAbelian.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hD_le_B)
      hD_sub_elem
  exact ⟨D, hD_normal, hD_elem, hDcard⟩

/-- In a minimal odd group, a rank-three `p`-subgroup forces `p` to be odd. -/
private theorem odd_prime_of_isPGroup_of_three_le_rank [Finite G]
    (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime] {A : Subgroup G}
    (hAp : IsPGroup p A) (hmA : 3 ≤ rank ↥A) :
    Odd p := by
  classical
  have h3pRankA : 3 ≤ pRank ↥A p :=
    three_le_pRank_of_isPGroup_of_three_le_rank hAp hmA
  obtain ⟨A₀, hA₀ea, hA₀log⟩ :=
    exists_isElementaryAbelian_log_card_ge_of_pos_le_pRank
      (G := ↥A) (p := p) (n := 3) (by norm_num) h3pRankA
  let Astar : Subgroup G := A₀.map A.subtype
  have hAstar_ea : Astar.IsElementaryAbelian p := by
    change (A₀.map A.subtype).IsElementaryAbelian p
    exact Subgroup.IsElementaryAbelian.map A.subtype_injective hA₀ea
  have hAstar_log : 3 ≤ Nat.log p (Nat.card Astar) := by
    change 3 ≤ Nat.log p (Nat.card (A₀.map A.subtype))
    rw [Subgroup.card_map_of_injective A.subtype_injective]
    exact hA₀log
  have hAstar_p : IsPGroup p Astar := hAstar_ea.isPGroup
  have hp_dvd_Astar : p ∣ Nat.card Astar := by
    obtain ⟨n, hn⟩ := hAstar_p.exists_card_eq
    have hnpos : 0 < n := by
      by_contra hn0
      have hn_zero : n = 0 := by omega
      rw [hn_zero, pow_zero] at hn
      rw [hn] at hAstar_log
      norm_num at hAstar_log
    rw [hn]
    exact dvd_pow_self p hnpos.ne'
  exact hG.odd.of_dvd_nat (hp_dvd_Astar.trans (Subgroup.card_subgroup_dvd_card Astar))

/-- Ambient form of the normal `E_{p^2}` witness inside an overgroup `P`.

If `A ≤ P`, `A` is a rank-three `p`-subgroup, and `P` is a finite `p`-group, then `P`
contains an ambient subgroup `D ≤ P` such that `D.subgroupOf P` is normal in `P`, `D` is
integer elementary abelian of order `p^2`. -/
private theorem exists_normal_isElementaryAbelian_card_prime_sq_in_overgroup_of_pSubgroup_rank_three
    [Finite G] {p : ℕ} [Fact p.Prime] {A P : Subgroup G}
    (hp : Odd p) (hPp : IsPGroup p P) (hAp : IsPGroup p A) (hAP : A ≤ P)
    (hmA : 3 ≤ rank ↥A) :
    ∃ D : Subgroup G,
      D ≤ P ∧ (D.subgroupOf P).Normal ∧ D.IsElementaryAbelian p ∧ Nat.card D = p ^ 2 := by
  classical
  have h3pRankA : 3 ≤ pRank ↥A p :=
    three_le_pRank_of_isPGroup_of_three_le_rank hAp hmA
  obtain ⟨A₀, hA₀ea, hA₀log⟩ :=
    exists_isElementaryAbelian_log_card_ge_of_pos_le_pRank
      (G := ↥A) (p := p) (n := 3) (by norm_num) h3pRankA
  let Astar : Subgroup G := A₀.map A.subtype
  have hAstar_ea : Astar.IsElementaryAbelian p := by
    change (A₀.map A.subtype).IsElementaryAbelian p
    exact Subgroup.IsElementaryAbelian.map A.subtype_injective hA₀ea
  have hAstar_log : 3 ≤ Nat.log p (Nat.card Astar) := by
    change 3 ≤ Nat.log p (Nat.card (A₀.map A.subtype))
    rw [Subgroup.card_map_of_injective A.subtype_injective]
    exact hA₀log
  have hAstarP : Astar ≤ P := by
    intro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨y, _hy, rfl⟩ := hx
    exact hAP y.2
  let AstarP : Subgroup ↥P := Astar.subgroupOf P
  have hAstarP_ea : AstarP.IsElementaryAbelian p := by
    change (Astar.subgroupOf P).IsElementaryAbelian p
    exact IsElementaryAbelian.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hAstarP).symm
      hAstar_ea
  have hAstarP_log : 3 ≤ Nat.log p (Nat.card AstarP) := by
    change 3 ≤ Nat.log p (Nat.card (Astar.subgroupOf P))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAstarP).toEquiv]
    exact hAstar_log
  have h3P : 3 ≤ pRank ↥P p := hAstarP_log.trans (le_pRank AstarP hAstarP_ea)
  obtain ⟨D₀, hD₀norm, hD₀ea, hD₀card⟩ :=
    exists_normal_isElementaryAbelian_card_prime_sq_of_three_le_pRank
      (R := ↥P) hp hPp h3P
  let D : Subgroup G := D₀.map P.subtype
  have hDP : D ≤ P := by
    change D₀.map P.subtype ≤ P
    exact Subgroup.map_subtype_le D₀
  have hDnormP : (D.subgroupOf P).Normal := by
    have htarget : D.subgroupOf P = D₀ := by
      apply (Subgroup.map_subtype_inj (H := P)).mp
      rw [Subgroup.map_subgroupOf_eq_of_le hDP]
    rwa [htarget]
  have hDea : D.IsElementaryAbelian p := by
    change (D₀.map P.subtype).IsElementaryAbelian p
    exact Subgroup.IsElementaryAbelian.map P.subtype_injective hD₀ea
  have hDcard : Nat.card D = p ^ 2 := by
    change Nat.card (D₀.map P.subtype) = p ^ 2
    rw [Subgroup.card_map_of_injective P.subtype_injective]
    exact hD₀card
  exact ⟨D, hDP, hDnormP, hDea, hDcard⟩

/-- A normal elementary abelian subgroup D of order p^2 cuts rank at most one from a
rank-three elementary abelian subgroup.

This is the cardinal-to-rank bridge used in BG Corollary 9.3 after Lemma 4.5 supplies the
normal E_{p^2} witness. The proof reuses the §5 conjugation-count estimate
|B0 ∩ C_G(D)| >= p^2 for an elementary abelian B0 of order p^3, then converts the
resulting cardinal lower bound back into rank >= 2. -/
private theorem two_le_rank_inf_centralizer_of_normal_card_prime_sq_of_log_three [Finite G]
    {p : ℕ} [Fact p.Prime] {D Bstar : Subgroup G} [D.Normal]
    (hDea : D.IsElementaryAbelian p) (hDcard : Nat.card D = p ^ 2)
    (hBstarea : Bstar.IsElementaryAbelian p)
    (hBstarlog : 3 ≤ Nat.log p (Nat.card Bstar)) :
    2 ≤ rank ↥(Bstar ⊓ Subgroup.centralizer (D : Set G)) := by
  classical
  have hBstar_card_ge : p ^ 3 ≤ Nat.card Bstar :=
    Nat.pow_le_of_le_log Nat.card_pos.ne' hBstarlog
  obtain ⟨B₀, hB₀card⟩ :=
    Sylow.exists_subgroup_card_pow_prime_of_le_card (n := 3)
      (Fact.out : p.Prime) hBstarea.isPGroup hBstar_card_ge
  let B₀G : Subgroup G := B₀.map Bstar.subtype
  have hB₀G_ea : B₀G.IsElementaryAbelian p := by
    change (B₀.map Bstar.subtype).IsElementaryAbelian p
    exact Subgroup.IsElementaryAbelian.map Bstar.subtype_injective
      (hBstarea.to_subgroup B₀)
  have hB₀Gcard : Nat.card B₀G = p ^ 3 := by
    change Nat.card (B₀.map Bstar.subtype) = p ^ 3
    rw [Subgroup.card_map_of_injective Bstar.subtype_injective, hB₀card]
  let H : Subgroup G := B₀G ⊓ Subgroup.centralizer (D : Set G)
  have hHcard : p ^ 2 ≤ Nat.card H := by
    change p ^ 2 ≤ Nat.card ↥(B₀G ⊓ Subgroup.centralizer (D : Set G))
    exact OddOrder.BG.Ch1.S05.card_inf_centralizer_ge_prime_sq_of_card_prime_cube
      (E := D) (B := B₀G) hDea hDcard hB₀G_ea hB₀Gcard
  have hH_ea : H.IsElementaryAbelian p := by
    have hH_le_B₀G : H ≤ B₀G := by
      dsimp [H]
      exact inf_le_left
    have hH_sub_ea : (H.subgroupOf B₀G).IsElementaryAbelian p :=
      hB₀G_ea.to_subgroup (H.subgroupOf B₀G)
    exact IsElementaryAbelian.of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hH_le_B₀G) hH_sub_ea
  have hHlog : 2 ≤ Nat.log p (Nat.card H) :=
    Nat.le_log_of_pow_le (Fact.out : p.Prime).one_lt hHcard
  have h2pRankH : 2 ≤ pRank ↥H p := hHlog.trans hH_ea.log_card_le_pRank
  let K : Subgroup G := Bstar ⊓ Subgroup.centralizer (D : Set G)
  have hB₀G_le_Bstar : B₀G ≤ Bstar := by
    change B₀.map Bstar.subtype ≤ Bstar
    exact Subgroup.map_subtype_le B₀
  have hHleK : H ≤ K := by
    intro x hx
    exact ⟨hB₀G_le_Bstar hx.1, hx.2⟩
  have hmono : pRank ↥H p ≤ pRank ↥K p :=
    pRank_le_of_injective (f := Subgroup.inclusion hHleK)
      (Subgroup.inclusion_injective hHleK)
  exact (h2pRankH.trans hmono).trans (pRank_le_rank (G := ↥K) p)

/-- Local-overgroup form of the preceding rank-drop bridge.

If `D` is normal in an overgroup `P`, the same rank drop can be proved inside `P` and then
transported back to the ambient group `G`. This is the form needed for BG Corollary 9.3,
where Lemma 4.5 supplies `D ⊴ P` for a Sylow `p`-subgroup rather than `D ⊴ G`. -/
private theorem two_le_rank_inf_centralizer_of_normal_in_overgroup_card_prime_sq_of_log_three
    [Finite G] {p : ℕ} [Fact p.Prime] {P D Bstar : Subgroup G}
    (hDP : D ≤ P) (hBstarP : Bstar ≤ P) (hDnormP : (D.subgroupOf P).Normal)
    (hDea : D.IsElementaryAbelian p) (hDcard : Nat.card D = p ^ 2)
    (hBstarea : Bstar.IsElementaryAbelian p)
    (hBstarlog : 3 ≤ Nat.log p (Nat.card Bstar)) :
    2 ≤ rank ↥(Bstar ⊓ Subgroup.centralizer (D : Set G)) := by
  classical
  let DP : Subgroup P := D.subgroupOf P
  let BP : Subgroup P := Bstar.subgroupOf P
  have : DP.Normal := by
    simpa [DP] using hDnormP
  have hDP_ea : DP.IsElementaryAbelian p := by
    dsimp [DP]
    exact IsElementaryAbelian.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hDP).symm hDea
  have hDP_card : Nat.card DP = p ^ 2 := by
    dsimp [DP]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDP).toEquiv, hDcard]
  have hBP_ea : BP.IsElementaryAbelian p := by
    dsimp [BP]
    exact IsElementaryAbelian.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hBstarP).symm
      hBstarea
  have hBP_log : 3 ≤ Nat.log p (Nat.card BP) := by
    dsimp [BP]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBstarP).toEquiv]
    exact hBstarlog
  let KP : Subgroup P := BP ⊓ Subgroup.centralizer (DP : Set P)
  let KG : Subgroup G := Bstar ⊓ Subgroup.centralizer (D : Set G)
  have hKP_rank : 2 ≤ rank ↥KP := by
    dsimp [KP]
    exact two_le_rank_inf_centralizer_of_normal_card_prime_sq_of_log_three
      (G := P) (D := DP) (Bstar := BP) hDP_ea hDP_card hBP_ea hBP_log
  let H : Subgroup G := KP.map P.subtype
  have hHleKG : H ≤ KG := by
    intro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨?_, ?_⟩
    · change (y : G) ∈ Bstar
      simpa [BP, Subgroup.mem_subgroupOf] using hy.1
    · change (y : G) ∈ Subgroup.centralizer (D : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro d hd
      let dP : P := ⟨d, hDP hd⟩
      have hdP : dP ∈ DP := by
        change (d : G) ∈ D
        exact hd
      have hcommP := Subgroup.mem_centralizer_iff.mp hy.2 dP hdP
      exact congrArg Subtype.val hcommP
  have hKP_rank_le_H : rank ↥KP ≤ rank ↥H :=
    rank_le_of_injective
      (f := (Subgroup.equivMapOfInjective KP P.subtype P.subtype_injective).toMonoidHom)
      (Subgroup.equivMapOfInjective KP P.subtype P.subtype_injective).injective
  have hH_rank_le_KG : rank ↥H ≤ rank ↥KG :=
    rank_le_of_injective (f := Subgroup.inclusion hHleKG)
      (Subgroup.inclusion_injective hHleKG)
  exact (hKP_rank.trans hKP_rank_le_H).trans hH_rank_le_KG

/-- `A`-side local rank-drop bridge for BG Corollary 9.3.

If a finite `p`-subgroup `A ≤ P` has BG rank at least three and `D ⊴ P` is elementary
abelian of order `p^2`, then `A ∩ C_G(D)` has rank at least two. The proof extracts a
rank-three elementary abelian subgroup of `A` at the same prime `p`, applies the already
proved elementary abelian rank-drop inside `P`, then includes back into `A ∩ C_G(D)`. -/
private theorem two_le_rank_inf_centralizer_of_pSubgroup_rank_three [Finite G]
    {p : ℕ} [Fact p.Prime] {P D A : Subgroup G}
    (hAp : IsPGroup p A) (hAP : A ≤ P) (hDP : D ≤ P)
    (hDnormP : (D.subgroupOf P).Normal)
    (hDea : D.IsElementaryAbelian p) (hDcard : Nat.card D = p ^ 2)
    (hmA : 3 ≤ rank ↥A) :
    2 ≤ rank ↥(A ⊓ Subgroup.centralizer (D : Set G)) := by
  classical
  have h3pRankA : 3 ≤ pRank ↥A p :=
    three_le_pRank_of_isPGroup_of_three_le_rank hAp hmA
  obtain ⟨A₀, hA₀ea, hA₀log⟩ :=
    exists_isElementaryAbelian_log_card_ge_of_pos_le_pRank
      (G := ↥A) (p := p) (n := 3) (by norm_num) h3pRankA
  let Astar : Subgroup G := A₀.map A.subtype
  have hAstar_ea : Astar.IsElementaryAbelian p := by
    change (A₀.map A.subtype).IsElementaryAbelian p
    exact Subgroup.IsElementaryAbelian.map A.subtype_injective hA₀ea
  have hAstar_log : 3 ≤ Nat.log p (Nat.card Astar) := by
    change 3 ≤ Nat.log p (Nat.card (A₀.map A.subtype))
    rw [Subgroup.card_map_of_injective A.subtype_injective]
    exact hA₀log
  have hAstarP : Astar ≤ P := by
    intro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨y, _hy, rfl⟩ := hx
    exact hAP y.2
  have hAstar_le_A : Astar ≤ A := by
    intro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨y, _hy, rfl⟩ := hx
    exact y.2
  have hAstar_rank :
      2 ≤ rank ↥(Astar ⊓ Subgroup.centralizer (D : Set G)) :=
    two_le_rank_inf_centralizer_of_normal_in_overgroup_card_prime_sq_of_log_three
      (P := P) (D := D) (Bstar := Astar) hDP hAstarP hDnormP hDea hDcard
      hAstar_ea hAstar_log
  have hle :
      Astar ⊓ Subgroup.centralizer (D : Set G) ≤
        A ⊓ Subgroup.centralizer (D : Set G) := by
    intro x hx
    exact ⟨hAstar_le_A hx.1, hx.2⟩
  exact hAstar_rank.trans
    (rank_le_of_injective (f := Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle))

/-- BG Corollary 9.3's Corollary-9.2 cascade, after the Lemma-4.5 witness `D` and the
two cyclic-quotient rank drops have been supplied.

In the book proof, `D ⊴ P`, `|D| = p²`, and `B* ≤ C_G(B)` with `m(B*) = 3` are chosen so
that `m(C_A(D)) ≥ 2` and `m(C_{B*}(D)) ≥ 2`. This lemma formalizes the remaining
successive applications of Corollary 9.2:
`A → C_A(D) → D → C_{B*}(D) → B* → B`. -/
private theorem isUniquelyMaximal_of_rank_drop_witness [Finite G]
    (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime] {A B D Bstar : Subgroup G}
    (hAab : IsMulCommutative A) (hAU : IsUniquelyMaximal A)
    (hBp : IsPGroup p B) (hBnc : ¬ IsCyclic ↥B)
    (hDea : D.IsElementaryAbelian p) (hDcard : Nat.card D = p ^ 2)
    (hBstarea : Bstar.IsElementaryAbelian p)
    (hBstarlog : 3 ≤ Nat.log p (Nat.card Bstar))
    (hBstar_le_CB : Bstar ≤ Subgroup.centralizer (B : Set G))
    (hrCAD : 2 ≤ rank ↥(A ⊓ Subgroup.centralizer (D : Set G)))
    (hrCBD : 2 ≤ rank ↥(Bstar ⊓ Subgroup.centralizer (D : Set G))) :
    IsUniquelyMaximal B := by
  classical
  let CAD : Subgroup G := A ⊓ Subgroup.centralizer (D : Set G)
  let CBD : Subgroup G := Bstar ⊓ Subgroup.centralizer (D : Set G)
  have hCAD_le_CA : CAD ≤ Subgroup.centralizer (A : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact congrArg Subtype.val
      ((hAab.is_comm.comm (⟨x, hx.1⟩ : A) (⟨a, ha⟩ : A)).symm)
  have hCADU : IsUniquelyMaximal CAD :=
    isUniquelyMaximal_of_le_centralizer_of_two_le_rank hG hAU hCAD_le_CA hrCAD
  have hD_le_CCAD : D ≤ Subgroup.centralizer (CAD : Set G) := by
    intro d hd
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    exact (Subgroup.mem_centralizer_iff.mp hc.2 d hd).symm
  have hrD : 2 ≤ rank ↥D := by
    have hlog_le : Nat.log p (Nat.card D) ≤ pRank ↥D p := hDea.log_card_le_pRank
    have hlog : Nat.log p (Nat.card D) = 2 := by
      rw [hDcard, Nat.log_pow (Fact.out : p.Prime).one_lt]
    exact ((le_of_eq hlog.symm).trans hlog_le).trans (pRank_le_rank (G := ↥D) p)
  have hDU : IsUniquelyMaximal D :=
    isUniquelyMaximal_of_le_centralizer_of_two_le_rank hG hCADU hD_le_CCAD hrD
  have hCBD_le_CD : CBD ≤ Subgroup.centralizer (D : Set G) := inf_le_right
  have hCBDU : IsUniquelyMaximal CBD :=
    isUniquelyMaximal_of_le_centralizer_of_two_le_rank hG hDU hCBD_le_CD hrCBD
  have hBstar_le_CCBD : Bstar ≤ Subgroup.centralizer (CBD : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    exact congrArg Subtype.val
      ((hBstarea.comm (⟨b, hb⟩ : Bstar) (⟨c, hc.1⟩ : Bstar)).symm)
  have hrBstar : 2 ≤ rank ↥Bstar := by
    have hlog_le : Nat.log p (Nat.card Bstar) ≤ pRank ↥Bstar p :=
      hBstarea.log_card_le_pRank
    exact ((by omega : 2 ≤ Nat.log p (Nat.card Bstar)).trans hlog_le).trans
      (pRank_le_rank (G := ↥Bstar) p)
  have hBstarU : IsUniquelyMaximal Bstar :=
    isUniquelyMaximal_of_le_centralizer_of_two_le_rank hG hCBDU hBstar_le_CCBD hrBstar
  have hB_le_CBstar : B ≤ Subgroup.centralizer (Bstar : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro bstar hbstar
    exact (Subgroup.mem_centralizer_iff.mp (hBstar_le_CB hbstar) b hb).symm
  have hrB : 2 ≤ rank ↥B := two_le_rank_of_noncyclic_pSubgroup hG hBp hBnc
  exact isUniquelyMaximal_of_le_centralizer_of_two_le_rank hG hBstarU hB_le_CBstar hrB

/-- `MulAut` pointwise action on subgroups is the corresponding subgroup map. -/
private theorem mulAut_smul_eq_map (φ : MulAut G) (H : Subgroup G) :
    φ • H = H.map (φ : G →* G) := by
  rw [Subgroup.pointwise_smul_def]
  rfl

/-- Any finite `p`-subgroup can be conjugated into a chosen Sylow `p`-subgroup.

This is the Sylow-conjugacy bridge used in BG Corollary 9.3's line "replacing by
conjugates": after extracting a `p`-subgroup witness, choose a Sylow containing it and
conjugate that Sylow to the fixed one. -/
private theorem exists_conj_le_sylow_of_isPGroup [Finite G]
    {p : ℕ} [Fact p.Prime] {Q : Subgroup G} (hQ : IsPGroup p Q) (P : Sylow p G) :
    ∃ g : G, ((MulAut.conj g) • Q : Subgroup G) ≤ (P : Subgroup G) := by
  classical
  obtain ⟨Q', hQQ'⟩ := hQ.exists_le_sylow
  have : MulAction.IsPretransitive G (Sylow p G) := Sylow.isPretransitive_of_finite
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q' P
  refine ⟨g, ?_⟩
  have hle : ((MulAut.conj g) • Q : Subgroup G) ≤
      ((MulAut.conj g) • (Q' : Subgroup G) : Subgroup G) :=
    (Subgroup.pointwise_smul_le_pointwise_smul_iff).mpr hQQ'
  have hQ'eq : ((MulAut.conj g) • (Q' : Subgroup G) : Subgroup G) =
      (P : Subgroup G) := by
    have := congrArg Sylow.toSubgroup hg
    rwa [Sylow.coe_subgroup_smul] at this
  exact hle.trans (le_of_eq hQ'eq)

/-- Centralizer containment is preserved when both sides are conjugated by the same element.

This is the Corollary 9.3 bookkeeping needed after replacing `B*` by a conjugate: the
subgroup `B` must be conjugated at the same time for `B* ≤ C_G(B)` to remain true. -/
private theorem conj_smul_le_centralizer_conj_smul {B Bstar : Subgroup G} {g : G}
    (hBstar_le_CB : Bstar ≤ Subgroup.centralizer (B : Set G)) :
    ((MulAut.conj g) • Bstar : Subgroup G) ≤
      Subgroup.centralizer (((MulAut.conj g) • B : Subgroup G) : Set G) := by
  rintro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rcases hx with ⟨x0, hx0, rfl⟩
  rcases hy with ⟨y0, hy0, rfl⟩
  have hcomm : y0 * x0 = x0 * y0 :=
    Subgroup.mem_centralizer_iff.mp (hBstar_le_CB hx0) y0 hy0
  simpa [map_mul] using congrArg (MulAut.conj g) hcomm

/-- BG Corollary 9.3 cascade with the `B*`-side rank drop supplied by a normal
`E_{p^2}` witness inside an overgroup `P`.

This leaves only the `A ∩ C_G(D)` rank drop explicit. In the book proof, that is the other
cyclic-quotient calculation after choosing the same Lemma 4.5 witness `D ⊴ P`. -/
private theorem isUniquelyMaximal_of_overgroup_rank_drop_witness [Finite G]
    (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime] {A B D Bstar P : Subgroup G}
    (hAab : IsMulCommutative A) (hAU : IsUniquelyMaximal A)
    (hBp : IsPGroup p B) (hBnc : ¬ IsCyclic ↥B)
    (hDP : D ≤ P) (hBstarP : Bstar ≤ P) (hDnormP : (D.subgroupOf P).Normal)
    (hDea : D.IsElementaryAbelian p) (hDcard : Nat.card D = p ^ 2)
    (hBstarea : Bstar.IsElementaryAbelian p)
    (hBstarlog : 3 ≤ Nat.log p (Nat.card Bstar))
    (hBstar_le_CB : Bstar ≤ Subgroup.centralizer (B : Set G))
    (hrCAD : 2 ≤ rank ↥(A ⊓ Subgroup.centralizer (D : Set G))) :
    IsUniquelyMaximal B := by
  classical
  have hrCBD : 2 ≤ rank ↥(Bstar ⊓ Subgroup.centralizer (D : Set G)) :=
    two_le_rank_inf_centralizer_of_normal_in_overgroup_card_prime_sq_of_log_three
      (P := P) (D := D) (Bstar := Bstar) hDP hBstarP hDnormP hDea hDcard
      hBstarea hBstarlog
  exact isUniquelyMaximal_of_rank_drop_witness hG hAab hAU hBp hBnc hDea hDcard
    hBstarea hBstarlog hBstar_le_CB hrCAD hrCBD

/-- BG Corollary 9.3 cascade with both cyclic-quotient rank drops discharged from a
single normal `E_{p^2}` witness `D ⊴ P`.

This is the form left after choosing the Lemma-4.5 witness and a rank-three elementary
abelian subgroup `B* ≤ C_G(B)` inside the same overgroup `P`. -/
private theorem isUniquelyMaximal_of_overgroup_rank_three_witness [Finite G]
    (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime] {A B D Bstar P : Subgroup G}
    (hAab : IsMulCommutative A) (hAp : IsPGroup p A) (hAU : IsUniquelyMaximal A)
    (hBp : IsPGroup p B) (hBnc : ¬ IsCyclic ↥B)
    (hAP : A ≤ P) (hDP : D ≤ P) (hBstarP : Bstar ≤ P)
    (hDnormP : (D.subgroupOf P).Normal)
    (hDea : D.IsElementaryAbelian p) (hDcard : Nat.card D = p ^ 2)
    (hBstarea : Bstar.IsElementaryAbelian p)
    (hBstarlog : 3 ≤ Nat.log p (Nat.card Bstar))
    (hBstar_le_CB : Bstar ≤ Subgroup.centralizer (B : Set G))
    (hmA : 3 ≤ rank ↥A) :
    IsUniquelyMaximal B := by
  classical
  have hrCAD : 2 ≤ rank ↥(A ⊓ Subgroup.centralizer (D : Set G)) :=
    two_le_rank_inf_centralizer_of_pSubgroup_rank_three
      (P := P) (D := D) (A := A) hAp hAP hDP hDnormP hDea hDcard hmA
  exact isUniquelyMaximal_of_overgroup_rank_drop_witness hG hAab hAU hBp hBnc hDP
    hBstarP hDnormP hDea hDcard hBstarea hBstarlog hBstar_le_CB hrCAD

/-- Conjugate the `B*` side into the chosen overgroup, run the rank-three witness wrapper,
and transport uniqueness back to the original `B`.

This packages the Corollary 9.3 replacement step where `B*` is conjugated into the Sylow
overgroup containing `A`; the centralizer hypothesis is kept valid by conjugating `B` by the
same element. -/
private theorem isUniquelyMaximal_of_conj_overgroup_rank_three_witness [Finite G]
    (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime] {A B D Bstar P : Subgroup G}
    {g : G} (hAab : IsMulCommutative A) (hAp : IsPGroup p A)
    (hAU : IsUniquelyMaximal A) (hBp : IsPGroup p B) (hBnc : ¬ IsCyclic ↥B)
    (hAP : A ≤ P) (hDP : D ≤ P)
    (hBstarP : ((MulAut.conj g) • Bstar : Subgroup G) ≤ P)
    (hDnormP : (D.subgroupOf P).Normal)
    (hDea : D.IsElementaryAbelian p) (hDcard : Nat.card D = p ^ 2)
    (hBstarea : Bstar.IsElementaryAbelian p)
    (hBstarlog : 3 ≤ Nat.log p (Nat.card Bstar))
    (hBstar_le_CB : Bstar ≤ Subgroup.centralizer (B : Set G))
    (hmA : 3 ≤ rank ↥A) :
    IsUniquelyMaximal B := by
  classical
  let φ : MulAut G := MulAut.conj g
  let Bconj : Subgroup G := φ • B
  let Bstarconj : Subgroup G := φ • Bstar
  have hBconj_eq : Bconj = B.map (φ : G →* G) := by
    change φ • B = B.map (φ : G →* G)
    exact mulAut_smul_eq_map φ B
  have hBstarconj_eq : Bstarconj = Bstar.map (φ : G →* G) := by
    change φ • Bstar = Bstar.map (φ : G →* G)
    exact mulAut_smul_eq_map φ Bstar
  have hBconj_p : IsPGroup p Bconj := by
    rw [hBconj_eq]
    exact hBp.map (φ : G →* G)
  have hBconj_nc : ¬ IsCyclic ↥Bconj := by
    intro hcyc
    apply hBnc
    rw [hBconj_eq] at hcyc
    let e : ↥B ≃* ↥(B.map (φ : G →* G)) :=
      Subgroup.equivMapOfInjective B (φ : G →* G) φ.injective
    let : IsCyclic ↥(B.map (φ : G →* G)) := hcyc
    exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
  have hBstarconj_ea : Bstarconj.IsElementaryAbelian p := by
    rw [hBstarconj_eq]
    exact Subgroup.IsElementaryAbelian.map φ.injective hBstarea
  have hBstarconj_log : 3 ≤ Nat.log p (Nat.card Bstarconj) := by
    rw [hBstarconj_eq, Subgroup.card_map_of_injective φ.injective]
    exact hBstarlog
  have hBstarconj_le_CBconj :
      Bstarconj ≤ Subgroup.centralizer (Bconj : Set G) := by
    change ((MulAut.conj g) • Bstar : Subgroup G) ≤
      Subgroup.centralizer (((MulAut.conj g) • B : Subgroup G) : Set G)
    exact conj_smul_le_centralizer_conj_smul hBstar_le_CB
  have hBconjU : IsUniquelyMaximal Bconj :=
    isUniquelyMaximal_of_overgroup_rank_three_witness hG hAab hAp hAU hBconj_p
      hBconj_nc hAP hDP hBstarP hDnormP hDea hDcard hBstarconj_ea
      hBstarconj_log hBstarconj_le_CBconj hmA
  have hBmapU : IsUniquelyMaximal (B.map (φ : G →* G)) := by
    simpa [hBconj_eq] using hBconjU
  have hback :
      IsUniquelyMaximal ((B.map (φ : G →* G)).comap (φ : G →* G)) :=
    hBmapU.comap_equiv φ
  have hcomap : (B.map (φ : G →* G)).comap (φ : G →* G) = B :=
    Subgroup.comap_map_eq_self_of_injective (f := (φ : G →* G)) φ.injective B
  simpa [hcomap] using hback

/-- Extract the rank-three elementary abelian subgroup `B* ≤ C_G(B)` used in
BG Corollary 9.3 from the `pRank` hypothesis. -/
private theorem exists_elementaryAbelian_le_centralizer_of_three_le_pRank [Finite G]
    {p : ℕ} [Fact p.Prime] {B : Subgroup G}
    (hrB : 3 ≤ pRank ↥(Subgroup.centralizer (B : Set G)) p) :
    ∃ Bstar : Subgroup G,
      Bstar.IsElementaryAbelian p ∧
        Bstar ≤ Subgroup.centralizer (B : Set G) ∧
          3 ≤ Nat.log p (Nat.card Bstar) := by
  classical
  let C : Subgroup G := Subgroup.centralizer (B : Set G)
  obtain ⟨B₀, hB₀ea, hB₀log⟩ :=
    exists_isElementaryAbelian_log_card_ge_of_pos_le_pRank
      (G := ↥C) (p := p) (n := 3) (by norm_num) hrB
  let Bstar : Subgroup G := B₀.map C.subtype
  refine ⟨Bstar, ?_, ?_, ?_⟩
  · change (B₀.map C.subtype).IsElementaryAbelian p
    exact Subgroup.IsElementaryAbelian.map C.subtype_injective hB₀ea
  · change B₀.map C.subtype ≤ C
    exact Subgroup.map_subtype_le B₀
  · change 3 ≤ Nat.log p (Nat.card (B₀.map C.subtype))
    rw [Subgroup.card_map_of_injective C.subtype_injective]
    exact hB₀log

/-- **BG Corollary 9.3** (mmd L2545): `p` prime, `A` abelian `p`-部分群, `B` noncyclic
`p`-部分群、`A ∈ 𝒰`, `m(A) ≥ 3`, `r_p(C_G(B)) ≥ 3` ⇒ `B ∈ 𝒰`。 -/
theorem isUniquelyMaximal_of_abelian_rank_three [Finite G] (hG : IsMinimalSimpleOdd G)
    {p : ℕ} [Fact p.Prime] {A B : Subgroup G} (hAab : IsMulCommutative A) (hAp : IsPGroup p A)
    (hBp : IsPGroup p B) (hBnc : ¬ IsCyclic ↥B) (hAU : IsUniquelyMaximal A)
    (hmA : 3 ≤ rank ↥A) (hrB : 3 ≤ pRank ↥(Subgroup.centralizer (B : Set G)) p) :
    IsUniquelyMaximal B := by
  classical
  obtain ⟨Bstar, hBstarea, hBstar_le_CB, hBstarlog⟩ :=
    exists_elementaryAbelian_le_centralizer_of_three_le_pRank (B := B) hrB
  obtain ⟨P, hAP⟩ := hAp.exists_le_sylow
  have hp_odd : Odd p := odd_prime_of_isPGroup_of_three_le_rank hG hAp hmA
  obtain ⟨g, hBstarP⟩ :=
    exists_conj_le_sylow_of_isPGroup hBstarea.isPGroup P
  obtain ⟨D, hDP, hDnormP, hDea, hDcard⟩ :=
    exists_normal_isElementaryAbelian_card_prime_sq_in_overgroup_of_pSubgroup_rank_three
      (P := (P : Subgroup G)) hp_odd P.isPGroup' hAp hAP hmA
  exact isUniquelyMaximal_of_conj_overgroup_rank_three_witness hG hAab hAp hAU hBp
    hBnc hAP hDP hBstarP hDnormP hDea hDcard hBstarea hBstarlog hBstar_le_CB hmA

/-- **BG Lemma 9.4** (mmd L2555): `p` prime, `M ∈ ℳ`, `r_p(F(M)) ≥ 3` ⇒ `𝒰` は rank `≥ 3` の
すべての abelian `p`-群を含む。 -/
theorem abelian_rank_three_isUniquelyMaximal_of_fitting [Finite G] (hG : IsMinimalSimpleOdd G)
    {p : ℕ} [Fact p.Prime] {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hr : 3 ≤ pRank ↥(S08.fittingInG M) p) :
    ∀ A : Subgroup G, IsMulCommutative A → IsPGroup p A → 3 ≤ rank ↥A → IsUniquelyMaximal A := by
  classical
  have hpF : p ∈ (Nat.card ↥(S08.fittingInG M)).primeFactors :=
    mem_primeFactors_card_of_pos_pRank (H := ↥(S08.fittingInG M))
      (p := p) (by omega)
  obtain ⟨A₀, hA₀max, hA₀rank⟩ :=
    exists_isMaxElemAbelianIn_rank_three_of_three_le_pRank
      (H := S08.fittingInG M) hr
  have hWitness :
      ∃ U : Subgroup G,
        IsMulCommutative U ∧ IsPGroup p U ∧ IsUniquelyMaximal U ∧ 3 ≤ rank ↥U := by
    by_cases hFp : IsPGroup p ↥(S08.fittingInG M)
    · have hFpM : IsPGroup p ((S08.fittingInG M).subgroupOf M) :=
        hFp.of_equiv (Subgroup.subgroupOfEquivOfLe (S08.fittingInG_le M)).symm
      obtain ⟨P, hFP⟩ := hFpM.exists_le_sylow
      have h3Fsub : 3 ≤ pRank ↥((S08.fittingInG M).subgroupOf M) p :=
        hr.trans
          (pRank_le_of_injective
            (f := (Subgroup.subgroupOfEquivOfLe (S08.fittingInG_le M)).symm.toMonoidHom)
            (Subgroup.subgroupOfEquivOfLe (S08.fittingInG_le M)).symm.injective)
      have h3P : 3 ≤ pRank ↥(P : Subgroup ↥M) p :=
        h3Fsub.trans
          (pRank_le_of_injective (f := Subgroup.inclusion hFP)
            (Subgroup.inclusion_injective hFP))
      have hp_dvd_G : p ∣ Nat.card G :=
        (Nat.mem_primeFactors.mp hpF).2.1.trans
          (Subgroup.card_subgroup_dvd_card (S08.fittingInG M))
      have hp_odd : Odd p := hG.odd.of_dvd_nat hp_dvd_G
      obtain ⟨Asc, hAsc_scn⟩ :=
        OddOrder.BG.Ch1.S05.scn3_nonempty_of_three_le_pRank hp_odd P.isPGroup' h3P
      let A_M : Subgroup ↥M := Asc.map (P : Subgroup ↥M).subtype
      have hA_MP : A_M ≤ (P : Subgroup ↥M) := by
        change Asc.map (P : Subgroup ↥M).subtype ≤ (P : Subgroup ↥M)
        exact Subgroup.map_subtype_le Asc
      have hA_M_scn : IsSCN₃ p (A_M.subgroupOf (P : Subgroup ↥M)) := by
        have htarget : A_M.subgroupOf (P : Subgroup ↥M) = Asc := by
          apply (Subgroup.map_subtype_inj (H := (P : Subgroup ↥M))).mp
          rw [Subgroup.map_subgroupOf_eq_of_le hA_MP]
        rwa [htarget]
      have h8 :=
        (S08.sylow_isSylow_and_scn3_isUniquelyMaximal_of_pGroup
          hG hM hpF hA₀max hA₀rank P hFp).2 A_M hA_MP hA_M_scn
      let U : Subgroup G := A_M.map M.subtype
      have hA_Mab : IsMulCommutative A_M := by
        have : IsMulCommutative Asc := hAsc_scn.isSCN.isMulCommutative
        change IsMulCommutative (Asc.map (P : Subgroup ↥M).subtype)
        exact Subgroup.map_isMulCommutative Asc (P : Subgroup ↥M).subtype
      have hUab : IsMulCommutative U := by
        have : IsMulCommutative A_M := hA_Mab
        change IsMulCommutative (A_M.map M.subtype)
        exact Subgroup.map_isMulCommutative A_M M.subtype
      have hA_Mp : IsPGroup p A_M := by
        change IsPGroup p (Asc.map (P : Subgroup ↥M).subtype)
        exact (P.isPGroup'.to_subgroup Asc).map (P : Subgroup ↥M).subtype
      have hUp : IsPGroup p U := by
        change IsPGroup p (A_M.map M.subtype)
        exact hA_Mp.map M.subtype
      have hA_M_rank : 3 ≤ pRank ↥A_M p := by
        let ePM := Subgroup.equivMapOfInjective Asc (P : Subgroup ↥M).subtype
          (P : Subgroup ↥M).subtype_injective
        exact hAsc_scn.le_pRank.trans
          (pRank_le_of_injective (f := ePM.toMonoidHom) ePM.injective)
      have hUrank : 3 ≤ rank ↥U := by
        let eMG := Subgroup.equivMapOfInjective A_M M.subtype M.subtype_injective
        have hUpRank : 3 ≤ pRank ↥U p :=
          hA_M_rank.trans
            (pRank_le_of_injective (f := eMG.toMonoidHom) eMG.injective)
        exact hUpRank.trans (pRank_le_rank (G := ↥U) p)
      exact ⟨U, hUab, hUp, h8.2, hUrank⟩
    · have hCFU : IsUniquelyMaximal (S08.cFittingInG M A₀) :=
        S08.cFitting_isUniquelyMaximal_of_not_pGroup hG hM hpF hA₀max hA₀rank hFp
      have hA₀_le_CF : A₀ ≤ Subgroup.centralizer (S08.cFittingInG M A₀ : Set G) := by
        intro a ha
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        change x ∈ Subgroup.centralizer (A₀ : Set G) ⊓ S08.fittingInG M at hx
        exact (Subgroup.mem_centralizer_iff.mp hx.1 a ha).symm
      have hA₀U : IsUniquelyMaximal A₀ :=
        isUniquelyMaximal_of_le_centralizer_of_two_le_rank hG hCFU hA₀_le_CF
          (by omega)
      have hA₀ea : A₀.IsElementaryAbelian p :=
        S08.isMaxElemAbelianIn_isElementaryAbelian hA₀max
      have hA₀ab : IsMulCommutative A₀ := IsMulCommutative.of_comm hA₀ea.comm
      have hA₀p : IsPGroup p A₀ := hA₀ea.isPGroup
      exact ⟨A₀, hA₀ab, hA₀p, hA₀U, hA₀rank⟩
  obtain ⟨U, hUab, hUp, hUU, hUrank⟩ := hWitness
  intro A hAab hAp hArank
  have hAnc : ¬ IsCyclic ↥A := not_isCyclic_of_two_le_rank (A := A) (by omega)
  have hCA_rank : 3 ≤ pRank ↥(Subgroup.centralizer (A : Set G)) p :=
    three_le_pRank_centralizer_of_isMulCommutative_of_isPGroup_of_three_le_rank
      hAab hAp hArank
  exact isUniquelyMaximal_of_abelian_rank_three hG hUab hUp hAp hAnc hUU hUrank hCA_rank

/-- A global `SCN₃(p)` subgroup is abelian in the ambient group. -/
theorem isMulCommutative_of_mem_scn3Global [Finite G]
    {p : ℕ} [Fact p.Prime] {A : Subgroup G} (hA : A ∈ S07.scn3Global p G) :
    IsMulCommutative A := by
  obtain ⟨P, hAP, hAscn3⟩ := hA
  exact IsMulCommutative.of_setLike_mul_comm fun a ha b hb =>
    congrArg Subtype.val (isMulCommutative_iff_of_setLike.mp hAscn3.isSCN.isMulCommutative
      (⟨a, hAP ha⟩ : ↥(P : Subgroup G)) (Subgroup.mem_subgroupOf.mpr ha)
      ⟨b, hAP hb⟩ (Subgroup.mem_subgroupOf.mpr hb))

/-- A global `SCN₃(p)` subgroup is a `p`-subgroup in the ambient group. -/
theorem isPGroup_of_mem_scn3Global [Finite G]
    {p : ℕ} [Fact p.Prime] {A : Subgroup G} (hA : A ∈ S07.scn3Global p G) :
    IsPGroup p A := by
  obtain ⟨P, hAP, _hAscn3⟩ := hA
  exact (P.isPGroup').to_le hAP

/-- A global `SCN₃(p)` subgroup has ambient rank at least three. -/
theorem three_le_rank_of_mem_scn3Global [Finite G]
    {p : ℕ} [Fact p.Prime] {A : Subgroup G} (hA : A ∈ S07.scn3Global p G) :
    3 ≤ rank ↥A := by
  obtain ⟨P, hAP, hAscn3⟩ := hA
  have h3A : 3 ≤ pRank ↥A p :=
    hAscn3.le_pRank.trans
      (pRank_le_of_injective
        (f := (Subgroup.subgroupOfEquivOfLe hAP).toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hAP).injective)
  exact h3A.trans (pRank_le_rank (G := ↥A) p)

/-- If the ambient `SCN₃` subgroup `A` is not in the uniqueness class, then no
subgroup of `A` can already be in it.  This is the formal bridge for the step
"since `A ∉ 𝒰`, the cocyclic subgroup `B ≤ Ω₁(A)` is not in `𝒰`" in BG Lemma
9.5. -/
theorem not_isUniquelyMaximal_of_le_scn3_counterexample [Finite G]
    (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime] {A B : Subgroup G}
    (hAcomm_set : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hA : A ∈ S07.scn3Global p G) (hBA : B ≤ A)
    (hAnot : ¬ IsUniquelyMaximal A) :
    ¬ IsUniquelyMaximal B := by
  intro hBU
  have hA_le_CB : A ≤ Subgroup.centralizer (B : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (hAcomm_set a ha b (hBA hb)).symm
  have h2A : 2 ≤ rank ↥A :=
    (by omega : (2 : ℕ) ≤ 3).trans (three_le_rank_of_mem_scn3Global hA)
  exact hAnot (isUniquelyMaximal_of_le_centralizer_of_two_le_rank hG hBU hA_le_CB h2A)

/-- The centralizer of a global `SCN₃(p)` subgroup is proper in a minimal odd simple group. -/
theorem centralizer_lt_top_of_mem_scn3Global [Finite G]
    (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime] {A : Subgroup G}
    (hA : A ∈ S07.scn3Global p G) :
    Subgroup.centralizer (A : Set G) < ⊤ := by
  classical
  have hZbot : Subgroup.center G = ⊥ := by
    rcases hG.simple.eq_bot_or_eq_top_of_normal (Subgroup.center G) inferInstance with h | h
    · exact h
    · exact absurd (Group.isSolvable_of_comm fun a b =>
        (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top a) b).symm) hG.notSolvable
  have hArank : 2 ≤ rank ↥A := (by omega : (2 : ℕ) ≤ 3).trans
    (three_le_rank_of_mem_scn3Global hA)
  have hAne : A ≠ ⊥ := by
    obtain ⟨q, hq, E, _hEea, hEA, hEnc⟩ :=
      exists_isElementaryAbelian_not_isCyclic_le_of_two_le_rank A hArank
    intro hAbot
    have hEbot : E = ⊥ := le_bot_iff.mp (hEA.trans (le_of_eq hAbot))
    have : Nontrivial ↥E := Nontrivial.of_not_isCyclic hEnc
    exact ((Subgroup.nontrivial_iff_ne_bot E).mp inferInstance) hEbot
  rw [lt_top_iff_ne_top]
  intro hCtop
  have hAleZ : A ≤ Subgroup.center G :=
    Subgroup.centralizer_eq_top_iff_subset.mp hCtop
  exact hAne (le_bot_iff.mp (hAleZ.trans (le_of_eq hZbot)))

/-- A global `SCN₃(p)` subgroup has at least one maximal subgroup over its centralizer. -/
theorem exists_maximalSubgroupsContaining_centralizer_of_mem_scn3Global [Finite G]
    (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime] {A : Subgroup G}
    (hA : A ∈ S07.scn3Global p G) :
    ∃ M : Subgroup G, M ∈ maximalSubgroupsContaining (Subgroup.centralizer (A : Set G)) := by
  classical
  have hClt : Subgroup.centralizer (A : Set G) < ⊤ :=
    centralizer_lt_top_of_mem_scn3Global hG hA
  obtain ⟨M, hM, hCM⟩ :=
    (eq_top_or_exists_le_coatom (Subgroup.centralizer (A : Set G))).resolve_left hClt.ne
  exact ⟨M, hM, hCM⟩

/-- A global `SCN₃(p)` subgroup is nontrivial. -/
theorem ne_bot_of_mem_scn3Global [Finite G]
    {p : ℕ} [Fact p.Prime] {A : Subgroup G} (hA : A ∈ S07.scn3Global p G) :
    A ≠ ⊥ := by
  have hAp : IsPGroup p A := isPGroup_of_mem_scn3Global hA
  have hArank : 3 ≤ rank ↥A := three_le_rank_of_mem_scn3Global hA
  have h3pRankA : 3 ≤ pRank ↥A p :=
    three_le_pRank_of_isPGroup_of_three_le_rank hAp hArank
  have hpA : p ∣ Nat.card A :=
    (Nat.mem_primeFactors.mp
      (mem_primeFactors_card_of_pos_pRank (H := ↥A) (p := p) (by omega))).2.1
  intro hAbot
  rw [hAbot, Subgroup.card_bot] at hpA
  exact (Fact.out : p.Prime).ne_one (Nat.dvd_one.mp hpA)

/-- The prime set of a global `SCN₃(p)` subgroup is exactly `{p}`. -/
theorem primesOf_eq_singleton_of_mem_scn3Global [Finite G]
    {p : ℕ} [Fact p.Prime] {A : Subgroup G} (hA : A ∈ S07.scn3Global p G) :
    S07.primesOf A = ({p} : Set ℕ) := by
  have hAp : IsPGroup p A := isPGroup_of_mem_scn3Global hA
  have hAne : A ≠ ⊥ := ne_bot_of_mem_scn3Global hA
  obtain ⟨n, hn⟩ := hAp.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    exact hAne (Subgroup.card_eq_one.mp hn)
  ext q
  simp only [S07.primesOf, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  rw [hn, Nat.primeFactors_prime_pow hn0 (Fact.out : p.Prime), Finset.mem_singleton]

/-- A global `SCN₃(p)` subgroup forces `p ∣ |G|`. -/
theorem prime_dvd_card_of_mem_scn3Global [Finite G]
    {p : ℕ} [Fact p.Prime] {A : Subgroup G} (hA : A ∈ S07.scn3Global p G) :
    p ∣ Nat.card G := by
  have hAp : IsPGroup p A := isPGroup_of_mem_scn3Global hA
  have hArank : 3 ≤ rank ↥A := three_le_rank_of_mem_scn3Global hA
  have h3pRankA : 3 ≤ pRank ↥A p :=
    three_le_pRank_of_isPGroup_of_three_le_rank hAp hArank
  have hpA : p ∣ Nat.card A :=
    (Nat.mem_primeFactors.mp
      (mem_primeFactors_card_of_pos_pRank (H := ↥A) (p := p) (by omega))).2.1
  exact hpA.trans (Subgroup.card_subgroup_dvd_card A)

/-- A subgroup of a finite `p`-group is subnormal in that `p`-group. -/
theorem subgroupOf_isSubnormal_of_isPGroup [Finite G]
    {p : ℕ} [Fact p.Prime] {A R : Subgroup G} (hRp : IsPGroup p R) :
    (A.subgroupOf R).IsSubnormal := by
  have : Group.IsNilpotent ↥R := hRp.isNilpotent
  exact OddOrder.Isaacs.Ch02.isSubnormal_of_isNilpotent_finite (A.subgroupOf R)

end OddOrder.BG.Ch2.S09


