-- Prove2me | Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S15_MF_WitnessPGroup
-- name    : OddOrder_BG_Ch4_FamilyOfMaximal_S15_MF_WitnessPGroup
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T10:20:06.340004+00:00
-- url     : https://prove2.me/theorems/ec8ab24f-ee5f-4aa9-88bf-2ba54749ef0d
-- title:
--   BG Theorem 15.7(e): pinning the witness prime to the TI-failure intersection
-- statement:
--   Theorem 15.7(e) of Bender–Glauberman, *Local Analysis for the Odd Order Theorem* states its second and third cases in terms of $p=|X|$ where $X=F(M)\cap F(M)^g$ witnesses the failure of $F(M)$ to be TI. This file carries out the three steps identifying $p$, starting with that $X$ is a $p$-group.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 2 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch4_FamilyOfMaximal/S15_MF/WitnessPGroup.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch4_FamilyOfMaximal/S15_MF/WitnessPGroup.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S15_MF_TIFailure

namespace OddOrder.BG.Ch4.S15

open OddOrder.GroupTheory

open OddOrder.Isaacs

open OddOrder.BG.Ch3.S12

open OddOrder.BG.Ch4.S14

open scoped Pointwise

open scoped IsMulCommutative

open scoped commutatorElement

variable {G : Type*} [Group G]

/-- **BG Theorem 15.7(e), conjunct A per-prime witness** (Coq `oZ`: `|Ω₁(Z(O_q(H)))| = q`): for the
non-TI witness data and a non-abelian `M_F`, every prime `q ∈ π(M_F)` has an order-`q` subgroup `Z`
of `M_F` that is normal in `M` (hence `td.U0`-invariant), feeding
`typeF_exponent_dvd_sub_one_of_invariant_card`.

* `q ≠ p`: `O_q(M_F) ≤ O_{p'}(M_F)` is cyclic (`typeF_nonabelian_cyclic_opiCore_compl`),
  so its unique
  order-`q` subgroup `Ω₁(O_q(M_F))` is characteristic (`characteristic_of_subgroup_of_isCyclic`) in
  `O_q(M_F)`, characteristic in `M_F`, hence normal in `M`.
* `q = p`: `Z = Ω₁(Z(O_p(M_F)))`; `|Z| = p` because `B = X₁ ⊔ Z` is elementary abelian of `p`-rank
  `≤ rank (M_F ⊓ C_G(X₁)) < 3`, forcing `pRank Z ≤ 1`, and `Z ≠ ⊥` (`O_p(M_F)` is a nontrivial
  `p`-group); `X₁ ⊄ Z` because `O_p(M_F)` is non-abelian (else `M_F = O_p ⊔ O_{p'}` abelian).

The conclusion also records `¬ X₁ ≤ Z` (`X₁ ⊄ Z`): for `q = p` this is the structural fact above;
for `q ≠ p` it is immediate from `|X₁| = p`, `|Z| = q` coprime.  This feeds the type-V Singer-case
faithfulness `K ⊓ C_G(O_p(M_F)) = ⊥` (`kappaHall_inf_centralizer_opiCore_eq_bot`). -/
theorem exists_orderQ_le_mf_normal_in_M_of_not_fittingIsTI [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {p : ℕ} {X₁ : Subgroup G} (hp : p.Prime)
    (hX₁card : Nat.card ↥X₁ = p) (hX₁MF : X₁ ≤ MF M)
    (hCGnotM : ¬ Subgroup.centralizer (X₁ : Set G) ≤ M)
    (hrank3 : rank ↥(MF M ⊓ Subgroup.centralizer (X₁ : Set G)) < 3)
    (hnab : ¬ IsMulCommutative ↥(MF M))
    {q : ℕ} (hq : q.Prime) (hqπ : q ∈ (Nat.card ↥(MF M)).primeFactors) :
    ∃ Z : Subgroup G, Z ≤ MF M ∧ Nat.card ↥Z = q ∧
      M ≤ Subgroup.normalizer (Z : Set G) ∧ ¬ X₁ ≤ Z ∧
      (q = p → Z = OddOrder.BG.Ch3.S10.omega1CenterInG (opiCoreInG ({p} : Set ℕ) (MF M)) p) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact q.Prime := ⟨hq⟩
  have hMFnil : Group.IsNilpotent ↥(MF M) := maxNilpotentNormalHall_isNilpotent M
  have hMNMF : M ≤ Subgroup.normalizer ((MF M : Subgroup G) : Set G) :=
    maxNilpotentNormalHall_le_normalizer M
  by_cases hqp : q = p
  · -- `q = p`: `Z = Ω₁(Z(O_p(M_F)))`, `|Z| = p` by the rank argument (Coq `oZ0`, L1085-1117).
    set P : Subgroup G := opiCoreInG ({p} : Set ℕ) (MF M) with hPdef
    -- `X₁ ≤ P`, and `P` is a nontrivial `p`-group.
    have hX₁ne : X₁ ≠ ⊥ :=
      fun h => hp.one_lt.ne' (by rw [← hX₁card, h, Subgroup.card_bot])
    have hX₁pg : IsPGroup p ↥X₁ := IsPGroup.of_card (n := 1) (by rw [hX₁card, pow_one])
    have hX₁P : X₁ ≤ P :=
      OddOrder.BG.Ch2.S08.le_opiCoreInG_singleton_of_isPGroup_of_le_nilpotent hMFnil hX₁MF hX₁pg
    have hPne : P ≠ ⊥ := fun h => hX₁ne (le_bot_iff.mp (h ▸ hX₁P))
    have : Nontrivial ↥P := (Subgroup.nontrivial_iff_ne_bot P).mpr hPne
    have hPpg : IsPGroup p ↥P := isPGroup_opiCoreInG_singleton (MF M)
    -- `P` non-abelian; `C₁ = C_{M_F}(X₁)` abelian.
    have hPnab : ¬ IsMulCommutative ↥P :=
      opiCore_singleton_not_isMulCommutative_of_witness hG hM hp hX₁card hX₁MF hCGnotM hnab
    set C1 : Subgroup G := MF M ⊓ Subgroup.centralizer (X₁ : Set G) with hC1def
    have hC1ab : IsMulCommutative ↥C1 :=
      isMulCommutative_mf_inf_centralizer_of_not_le hG hM hX₁ne hCGnotM
    -- `Z := Ω₁(Z(P))`, elementary abelian, `≤ P ≤ M_F`.
    set Z : Subgroup G := OddOrder.BG.Ch3.S10.omega1CenterInG P p with hZdef
    have hZP : Z ≤ P := OddOrder.BG.Ch3.S10.omega1CenterInG_le P p
    have hZMF : Z ≤ MF M := hZP.trans (opiCoreInG_le _ _)
    have hWea : (omega1OfAbelian ↥P (Subgroup.center ↥P) p
        (fun _ hx y _ => (Subgroup.mem_center_iff.mp hx y).symm)).IsElementaryAbelian p :=
      omega1OfAbelian_isElementaryAbelian
    have hZea : Z.IsElementaryAbelian p := by rw [hZdef]; exact hWea.map P.subtype_injective
    -- `X₁` centralizes `Z` (`Z ≤ Z(P)`, `X₁ ≤ P`).
    have hX₁CZ : X₁ ≤ Subgroup.centralizer (Z : Set G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [SetLike.mem_coe, hZdef, OddOrder.BG.Ch3.S10.omega1CenterInG, Subgroup.mem_map] at hz
      obtain ⟨z', hz', hz'eq⟩ := hz
      have hz'c : z' ∈ Subgroup.center ↥P := (mem_omega1OfAbelian.mp hz').1
      rw [← hz'eq]
      simpa using (congrArg Subtype.val (Subgroup.mem_center_iff.mp hz'c ⟨x, hX₁P hx⟩)).symm
    -- `X₁ ⊄ Z`: else `X₁ ≤ Z(P)` ⟹ `P ≤ C_G(X₁)` ⟹ `P ≤ C₁` abelian (vs `hPnab`).
    have hX₁notZ : ¬ X₁ ≤ Z := by
      intro hsub
      refine hPnab ⟨⟨fun a b => Subtype.ext ?_⟩⟩
      have hPCX₁ : P ≤ Subgroup.centralizer (X₁ : Set G) := by
        intro g hg
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        have hxZ : x ∈ Z := hsub hx
        rw [hZdef, OddOrder.BG.Ch3.S10.omega1CenterInG, Subgroup.mem_map] at hxZ
        obtain ⟨x', hx', hx'eq⟩ := hxZ
        have hx'c : x' ∈ Subgroup.center ↥P := (mem_omega1OfAbelian.mp hx').1
        rw [← hx'eq]
        simpa using (congrArg Subtype.val (Subgroup.mem_center_iff.mp hx'c ⟨g, hg⟩)).symm
      have hPC1 : P ≤ C1 := le_inf (opiCoreInG_le _ _) hPCX₁
      simpa using congrArg Subtype.val
        (isMulCommutative_iff.mp hC1ab ⟨(a : G), hPC1 a.2⟩ ⟨(b : G), hPC1 b.2⟩)
    -- `X₁ ⊓ Z = ⊥` (`X₁` prime order, `X₁ ⊄ Z`).
    have hX₁Zbot : X₁ ⊓ Z = ⊥ := by
      have hdvd : Nat.card ↥(X₁ ⊓ Z) ∣ p :=
        hX₁card ▸ Subgroup.card_dvd_of_le inf_le_left
      rcases (Nat.dvd_prime hp).mp hdvd with h1 | hpp
      · exact Subgroup.eq_bot_of_card_eq _ h1
      · exact absurd (inf_eq_left.mp (Subgroup.eq_of_le_of_card_ge inf_le_left
          (by rw [hX₁card, hpp]))) hX₁notZ
    -- `B = X₁ ⊔ Z` elementary abelian, `≤ C₁`.
    have hX₁ea : X₁.IsElementaryAbelian p :=
      Subgroup.IsElementaryAbelian.of_card_prime hX₁card
    have hBea : (X₁ ⊔ Z).IsElementaryAbelian p :=
      isElementaryAbelian_sup_of_le_centralizer hX₁ea hZea hX₁CZ
    have hX₁C1 : X₁ ≤ C1 :=
      le_inf hX₁MF (le_centralizer_self_of_isElementaryAbelian hX₁ea)
    have hZC1 : Z ≤ C1 := by
      refine le_inf hZMF (fun z hz => ?_)
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact (Subgroup.mem_centralizer_iff.mp (hX₁CZ hx) z hz).symm
    have hBC1 : (X₁ ⊔ Z) ≤ C1 := sup_le hX₁C1 hZC1
    -- `|X₁ ⊔ Z| = p · |Z|`.
    have hX₁NZ : X₁ ≤ Subgroup.normalizer Z :=
      hX₁CZ.trans (Subgroup.centralizer_le_normalizer (Z : Set G))
    have hcoe : (↑X₁ * ↑Z : Set G) = ↑(X₁ ⊔ Z) :=
      (Subgroup.coe_mul_of_left_le_normalizer_right X₁ Z hX₁NZ).symm
    have hcardform : Nat.card ↥(X₁ ⊔ Z) = p * Nat.card ↥Z := by
      have h := Subgroup.card_HK_mul_card_inf_eq_card_mul_card X₁ Z
      rw [hcoe, hX₁Zbot, Subgroup.card_bot, mul_one, hX₁card] at h
      exact h
    -- `log_p |X₁ ⊔ Z| ≤ rank C₁ < 3`.
    have hBlog : Nat.log p (Nat.card ↥(X₁ ⊔ Z)) ≤ 2 := by
      have hB'ea : ((X₁ ⊔ Z).subgroupOf C1).IsElementaryAbelian p :=
        OddOrder.GroupTheory.IsElementaryAbelian.of_mulEquiv
          (Subgroup.subgroupOfEquivOfLe hBC1).symm hBea
      have hB'card : Nat.card ↥((X₁ ⊔ Z).subgroupOf C1) = Nat.card ↥(X₁ ⊔ Z) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBC1).toEquiv
      have h1 : Nat.log p (Nat.card ↥(X₁ ⊔ Z)) ≤ pRank ↥C1 p := by
        rw [← hB'card]; exact le_pRank _ hB'ea
      have h2 : pRank ↥C1 p ≤ rank ↥C1 := pRank_le_rank p
      have h3 : rank ↥C1 < 3 := hrank3
      omega
    -- `Z` is a nontrivial `p`-group, so `|Z| = p`.
    have hZpow : Nat.card ↥Z = p ^ (Nat.log p (Nat.card ↥Z)) := by
      rw [hZea.log_card_eq_finrank]; exact hZea.card_eq_pow_finrank
    have hZne : Z ≠ ⊥ := by
      have hcNt : Nontrivial ↥(Subgroup.center ↥P) := hPpg.center_nontrivial
      have hcdvd : Nat.card ↥(Subgroup.center ↥P) ∣ Nat.card ↥P :=
        Subgroup.card_subgroup_dvd_card _
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hPpg
      have hpdvd : p ∣ Nat.card ↥(Subgroup.center ↥P) := by
        have h1 : 1 < Nat.card ↥(Subgroup.center ↥P) :=
          Finite.one_lt_card_iff_nontrivial.mpr hcNt
        rw [hk] at hcdvd
        obtain ⟨j, _, hjeq⟩ := (Nat.dvd_prime_pow hp).mp hcdvd
        rcases Nat.eq_zero_or_pos j with rfl | hjpos
        · rw [pow_zero] at hjeq; omega
        · rw [hjeq]; exact dvd_pow_self p hjpos.ne'
      obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center ↥P)) p hpdvd
      have hwne : ((w : ↥P) : G) ≠ 1 := by
        intro hcoe1
        have : (w : ↥P) = 1 := by ext; simpa using hcoe1
        have hw1 : w = 1 := by ext; simpa using this
        rw [hw1, orderOf_one] at hw; exact hp.one_lt.ne' hw.symm
      refine fun hbot => hwne ?_
      have hmem : ((w : ↥P) : G) ∈ Z := by
        rw [hZdef, OddOrder.BG.Ch3.S10.omega1CenterInG]
        refine Subgroup.mem_map.mpr ⟨(w : ↥P), mem_omega1OfAbelian.mpr ⟨w.2, ?_⟩, rfl⟩
        have : w ^ p = 1 := by rw [← hw]; exact pow_orderOf_eq_one w
        simpa using congrArg (Subtype.val (p := fun a => a ∈ Subgroup.center ↥P)) this
      rw [hbot] at hmem; simpa using hmem
    obtain ⟨d, hd⟩ : ∃ d, Nat.card ↥Z = p ^ d := ⟨_, hZpow⟩
    have hsupeq : Nat.card ↥(X₁ ⊔ Z) = p ^ (d + 1) := by rw [hcardform, hd, pow_succ']
    rw [hsupeq, Nat.log_pow hp.one_lt] at hBlog
    have hd_ge : 1 ≤ d := by
      by_contra h
      have hd0 : d = 0 := by omega
      rw [hd0, pow_zero] at hd
      exact hZne (Subgroup.eq_bot_of_card_eq _ hd)
    have hZcard : Nat.card ↥Z = p := by
      rw [hd, show d = 1 from le_antisymm (by omega) hd_ge, pow_one]
    -- `M ≤ N(Z)`: `M ≤ N(P) ≤ N(Ω₁(Z(P))) = N(Z)`.
    have hMNP : M ≤ Subgroup.normalizer (P : Set G) :=
      le_normalizer_opiCoreInG_of_le_normalizer ({p} : Set ℕ) hMNMF
    have hMNZ : M ≤ Subgroup.normalizer (Z : Set G) := by
      rw [hZdef]
      exact hMNP.trans (OddOrder.BG.Ch3.S10.normalizer_le_normalizer_omega1CenterInG P p)
    exact ⟨Z, hZMF, hZcard.trans hqp.symm, hMNZ, hX₁notZ, fun _ => hZdef⟩
  · -- `q ≠ p`: `O_q(M_F) ≤ O_{p'}(M_F)` is cyclic; take its order-`q` subgroup.
    have hqdvd : q ∣ Nat.card ↥(MF M) := (Nat.mem_primeFactors.mp hqπ).2.1
    obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' (G := ↥(MF M)) q hqdvd
    set Z : Subgroup G := (Subgroup.zpowers x).map (MF M).subtype with hZdef
    have hZcard : Nat.card ↥Z = q := by
      rw [hZdef, Subgroup.card_map_of_injective (MF M).subtype_injective, Nat.card_zpowers, hxord]
    have hZMF : Z ≤ MF M := hZdef ▸ Subgroup.map_subtype_le _
    have hZpg : IsPGroup q ↥Z := IsPGroup.of_card (n := 1) (by rw [hZcard, pow_one])
    -- `Z ≤ O_q(M_F)` (a `q`-group inside the nilpotent `M_F`).
    have hZOq : Z ≤ opiCoreInG ({q} : Set ℕ) (MF M) :=
      OddOrder.BG.Ch2.S08.le_opiCoreInG_singleton_of_isPGroup_of_le_nilpotent hMFnil hZMF hZpg
    -- `O_q(M_F) ≤ O_{p'}(M_F)` (as `q ≠ p`), and `O_{p'}(M_F)` is cyclic, so `O_q(M_F)` is cyclic.
    have hcyc : IsCyclic ↥(opiCoreInG (({p} : Set ℕ)ᶜ) (MF M)) :=
      (typeF_nonabelian_cyclic_opiCore_compl hG hM hp hX₁card hX₁MF hCGnotM hnab).2
    have hOqle : opiCoreInG ({q} : Set ℕ) (MF M) ≤ opiCoreInG (({p} : Set ℕ)ᶜ) (MF M) :=
      Subgroup.map_mono (OddOrder.Isaacs.Ch03.oPiCore_mono
        (Set.singleton_subset_iff.mpr (Set.mem_compl_singleton_iff.mpr hqp)) ↥(MF M))
    have : IsCyclic ↥(opiCoreInG (({p} : Set ℕ)ᶜ) (MF M)) := hcyc
    have hOqcyc : IsCyclic ↥(opiCoreInG ({q} : Set ℕ) (MF M)) := Subgroup.isCyclic_of_le hOqle
    -- `Z.subgroupOf O_q(M_F)` is characteristic (subgroup of a cyclic group).
    have hWchar : (Z.subgroupOf (opiCoreInG ({q} : Set ℕ) (MF M))).Characteristic :=
      OddOrder.Isaacs.Ch04.characteristic_of_subgroup_of_isCyclic _
    -- `M ≤ N(O_q(M_F)) ≤ N(Z)`.
    have hMNOq : M ≤ Subgroup.normalizer ((opiCoreInG ({q} : Set ℕ) (MF M) : Subgroup G) : Set G) :=
      le_normalizer_opiCoreInG_of_le_normalizer ({q} : Set ℕ) hMNMF
    have hZeq : (Z.subgroupOf (opiCoreInG ({q} : Set ℕ) (MF M))).map
        (opiCoreInG ({q} : Set ℕ) (MF M)).subtype = Z :=
      Subgroup.map_subgroupOf_eq_of_le hZOq
    have hMNZ : M ≤ Subgroup.normalizer (Z : Set G) := by
      rw [← hZeq]
      exact hMNOq.trans (OddOrder.Isaacs.Ch07.normalizer_le_normalizer_map_of_characteristic)
    -- `¬ X₁ ≤ Z`: `|X₁| = p`, `|Z| = q`, `p ≠ q`, so `X₁ ≤ Z` would force `p ∣ q`.
    have hX₁notZ : ¬ X₁ ≤ Z := by
      intro hle
      have hdvd : p ∣ q := by
        have h := Subgroup.card_dvd_of_le hle; rwa [hX₁card, hZcard] at h
      exact hqp ((Nat.prime_dvd_prime_iff_eq hp hq).mp hdvd).symm
    exact ⟨Z, hZMF, hZcard, hMNZ, hX₁notZ, fun h => absurd h hqp⟩

/-- **`O_p(M_F)` is a Sylow `p`-subgroup of `G`** (Coq `sylP_G`): for a maximal `M` with
`M_F = M_σ` and `p ∈ σ(M)`, the `p`-core `P = O_p(M_F)` is a Sylow `p`-subgroup of `G`.

`P` is a `{p}`-Hall (hence Sylow) subgroup of the nilpotent `M_F = M_σ`
(`oPiCore_isHall_of_isNilpotent`: `p ∤ [M_F : P]`), so `|P| = p^{v_p(|M_F|)}` is the full `p`-part
of
`|M_σ|`; and since `M_σ` is the `σ`-Hall of `G` with `p ∈ σ` (`Msigma_isHall`: `p ∤ [G : M_σ]`),
that
`p`-part equals `v_p(|G|)`.  Thus `|P| = p^{v_p(|G|)}`, so `Sylow.ofCard` exhibits `P` as a Sylow
`p`-subgroup of `G`.  This is the `mFT_rank2_Sylow_cprod` Sylow input for the type-V Singer case
(`card_opiCore_eq_prime_cube_singer`). -/
theorem exists_sylow_eq_opiCore_of_mf_eq_msigma [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hmf : MF M = OddOrder.BG.Ch3.S10.Msigma M) {p : ℕ} (hp : p.Prime)
    (hpσ : p ∈ OddOrder.BG.Ch3.S10.sigma M) :
    ∃ S : Sylow p G, (S : Subgroup G) = opiCoreInG ({p} : Set ℕ) (MF M) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hMFnil : Group.IsNilpotent ↥(MF M) := maxNilpotentNormalHall_isNilpotent M
  set P : Subgroup G := opiCoreInG ({p} : Set ℕ) (MF M) with hPdef
  -- `P` is a `p`-group: `|P| = p^a`.
  have hPpg : IsPGroup p ↥P := isPGroup_opiCoreInG_singleton (MF M)
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hPpg
  suffices hcard : Nat.card ↥P = p ^ (Nat.card G).factorization p by
    exact ⟨Sylow.ofCard P hcard, Sylow.coe_ofCard P hcard⟩
  -- `v_p(|M_F|) = a`: `P = O_p(M_F)` is a `{p}`-Hall of `M_F` (`p ∤ [M_F : P]`).
  have hP'hall : Ch03.IsHallSubgroup ({p} : Set ℕ) (Ch03.oPiCore ({p} : Set ℕ) ↥(MF M)) :=
    OddOrder.BG.Ch3.S10.oPiCore_isHall_of_isNilpotent _
  have hPcard : Nat.card ↥P = Nat.card ↥(Ch03.oPiCore ({p} : Set ℕ) ↥(MF M)) :=
    Subgroup.card_map_of_injective (MF M).subtype_injective
  have hpidxP : ¬ p ∣ (Ch03.oPiCore ({p} : Set ℕ) ↥(MF M)).index := fun h =>
    hP'hall.2 p (Nat.mem_primeFactors.mpr ⟨hp, h, Subgroup.index_ne_zero_of_finite⟩)
      (Set.mem_singleton_iff.mpr rfl)
  have hMFfact : (Nat.card ↥(MF M)).factorization p = a := by
    rw [← Subgroup.card_mul_index (Ch03.oPiCore ({p} : Set ℕ) ↥(MF M)),
      Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hpidxP, add_zero, ← hPcard, ha,
      Nat.factorization_pow_self hp]
  -- `v_p(|G|) = v_p(|M_σ|)`: `M_σ` is the `σ`-Hall of `G`, `p ∈ σ`, so `p ∤ [G : M_σ]`.
  have hσHall := OddOrder.BG.Ch3.S10.Msigma_isHall hG hM
  have hpidxσ : ¬ p ∣ (OddOrder.BG.Ch3.S10.Msigma M).index := fun h =>
    hσHall.2 p (Nat.mem_primeFactors.mpr ⟨hp, h, Subgroup.index_ne_zero_of_finite⟩) hpσ
  have hGa : (Nat.card G).factorization p = a := by
    rw [← Subgroup.card_mul_index (OddOrder.BG.Ch3.S10.Msigma M),
      Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hpidxσ, add_zero, ← hmf, hMFfact]
  rw [ha, hGa]

end OddOrder.BG.Ch4.S15


