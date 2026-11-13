-- Prove2me | Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S14_TypePCounting_Basics
-- name    : OddOrder_BG_Ch4_FamilyOfMaximal_S14_TypePCounting_Basics
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T09:07:10.033799+00:00
-- url     : https://prove2.me/theorems/5bc76d76-3478-4995-b274-1633ca25ec77
-- title:
--   BG §14: split-extension derived subgroup, $\kappa(M)$, type-$\mathcal{P}$ families, $\sigma$-length
-- statement:
--   The first file of the §14 type-$\mathcal{P}$ counting development of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, split off from the former monolithic file: the derived subgroup of a split extension, $\kappa(M)$, the families of type-$\mathcal{P}$ maximal subgroups and the $\sigma$-length.
--
--   Main declarations: `maximalTypePFamily` (The family `M_P` of type-P maximal subgroups); `maximalSigmaSubgroupsOfElement` (BG `M_sigma(x)`: maximal subgroups whose `M_sigma` contains the element `x`); `sigmaSharp` (The nonidentity part `M_σ^#` of `M_σ` (`= sharpSubgroup M_σ`)); `sigmaConjugacySaturation` (The conjugacy saturation `C_G(M_tilde)` used in the counting formulas); and 7 more.
--
--   The bundle also proves 30 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch4_FamilyOfMaximal/S14_TypePCounting/Basics.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch4_FamilyOfMaximal/S14_TypePCounting/Basics.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S13_PrimeAction
import Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S13_PrimeActionTransition
import Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S12_Theorem125
import Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S12_Lemma1211
import Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S12_Lemma1217
import Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S14_Prop142Support
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S03c_Thm37
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S03g_Thm310
import Definitions.Def_OddOrder_GroupTheory_MaximalSubgroupType
import Definitions.Def_OddOrder_GroupTheory_MaximalSubgroupTypeConj
import Definitions.Def_OddOrder_GroupTheory_PiElementDecomposition
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S14_TypePCounting_TypeClassification

namespace OddOrder.BG.Ch4.S14

open OddOrder.GroupTheory

open OddOrder.Isaacs

open OddOrder.BG.Ch3.S12

open OddOrder.BG.Ch3.S13

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **BG Prop 14.2(a), case `κ ⊆ τ₁`, `E₃`-half** (mmd L3840, "by Lemma 13.7"): if `κ(M) ∩ τ₃(M)`
is empty (`κ ⊆ τ₁`) then `E₁` acts regularly on `E₃` (i.e. `C_{E₃}(g) = 1` for `g ∈ E₁#`).
Otherwise Lemma 13.7 makes `E₁E₃` act in a prime manner on `M_σ`, and since
`C_{M_σ}(E₁) = K^* ≠ 1`, prime action gives `C_{M_σ}(x) ≠ 1` for every `x ∈ E₃#`, producing a
prime of `κ(M) ∩ τ₃(M)` — a contradiction. -/
theorem actsRegularlyOn_E3_E1_of_kappa_inf_tau3_empty [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M E E₁ E₂ E₃ : Subgroup G}
    (h : SubgroupESetup M E E₁ E₂ E₃) (hE1ne : E₁ ≠ ⊥)
    (hKstar : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (E₁ : Set G) ≠ ⊥)
    (hτ3 : ¬ (kappa M ∩ tau3 M).Nonempty) :
    ActsRegularlyOn E₃ E₁ := by
  classical
  by_contra hreg
  have hE3ne : E₃ ≠ ⊥ := fun hb => hreg (hb ▸ actsRegularlyOn_bot_left E₁)
  -- Lemma 13.7: `E₁E₃` acts in a prime manner on `M_σ`.
  have hprime : ActsPrimeOn (OddOrder.BG.Ch3.S10.Msigma M) (E₁ ⊔ E₃) :=
    E1E3_actsPrime hG h hE1ne hreg
  -- `C_{M_σ}(E₁ ⊔ E₃) = C_{M_σ}(E₁) = K^* ≠ ⊥`.
  have hfix : fixedBy (OddOrder.BG.Ch3.S10.Msigma M) (E₁ ⊔ E₃)
      = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (E₁ : Set G) :=
    (fixedBy_eq_of_le_of_ne_bot hprime le_sup_left hE1ne).symm
  -- A witness `x ∈ E₃#` then has `C_{M_σ}(x) = C_{M_σ}(E₁ ⊔ E₃) ≠ ⊥`.
  obtain ⟨⟨x, hxE3⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hE3ne
  have hx1' : x ≠ 1 := fun hc => hx1 (Subtype.ext hc)
  have hxC : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer ({x} : Set G) ≠ ⊥ := by
    have hpx := hprime x (Subgroup.mem_sup_right hxE3) hx1'
    rw [fixedByElement_def] at hpx
    rw [hpx, hfix]; exact hKstar
  -- Build a `κ(M) ∩ τ₃(M)` witness: a rank-one `R ≤ ⟨x⟩ ≤ E₃` of prime order `r ∈ τ₃(M)`.
  refine hτ3 ?_
  have hxM : x ∈ M := h.E3_le_M hxE3
  have hxzpM : Subgroup.zpowers x ≤ E₃ := Subgroup.zpowers_le.mpr hxE3
  obtain ⟨r, hr, hrdvd⟩ :=
    (orderOf x).exists_prime_and_dvd (by rwa [Ne, orderOf_eq_one_iff])
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.zpowers x)) r
    (by rw [Nat.card_zpowers]; exact hrdvd)
  -- `R = ⟨z⟩`, with `z ∈ ⟨x⟩ ≤ E₃`, of order `r`.
  have hzx : (z : G) ∈ Subgroup.zpowers x := z.2
  have hRcard : Nat.card ↥(Subgroup.zpowers (z : G)) = r := by
    rw [Nat.card_zpowers]
    exact (orderOf_injective (Subgroup.zpowers x).subtype
      (Subgroup.zpowers x).subtype_injective z).trans hz
  have hRelem : Subgroup.zpowers (z : G) ∈ elemAbelianOfRank G r 1 :=
    ⟨Subgroup.IsElementaryAbelian.of_card_prime hRcard, by rw [hRcard, pow_one]⟩
  have hRE3 : Subgroup.zpowers (z : G) ≤ E₃ := (Subgroup.zpowers_le.mpr (hxzpM hzx))
  have hRM : Subgroup.zpowers (z : G) ≤ M := hRE3.trans (h.E3_le_M)
  -- `r ∈ τ₃(M)` (it divides `|E₃|`).
  have hrE3 : r ∈ (Nat.card ↥E₃).primeFactors :=
    Nat.mem_primeFactors.mpr
      ⟨hr, hRcard ▸ Subgroup.card_dvd_of_le hRE3, Nat.card_pos.ne'⟩
  have hrτ3 : r ∈ tau3 M := by
    have hc3 : Nat.card ↥(E₃.subgroupOf E) = Nat.card ↥E₃ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₃_le).toEquiv
    exact h.E₃_hall.1 r (hc3 ▸ hrE3)
  -- `C_{M_σ}(R) ⊇ C_{M_σ}(x) ≠ ⊥` (`z ∈ ⟨x⟩`, so centralizing `x` centralizes `⟨z⟩`).
  have hCle : Subgroup.centralizer ({x} : Set G) ≤
      Subgroup.centralizer ((Subgroup.zpowers (z : G) : Subgroup G) : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff] at ha ⊢
    intro y hy
    rw [SetLike.mem_coe, Subgroup.mem_zpowers_iff] at hy
    obtain ⟨j, rfl⟩ := hy
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hzx
    have hxa : Commute x a := ha x rfl
    rw [← hm]
    exact ((hxa.zpow_left m).zpow_left j).eq
  have hRC : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer
      ((Subgroup.zpowers (z : G) : Subgroup G) : Set G) ≠ ⊥ :=
    fun hb => hxC (le_bot_iff.mp (hb ▸ inf_le_inf_left _ hCle))
  exact ⟨r, ⟨hr, Or.inr hrτ3, Subgroup.zpowers (z : G), hRelem, hRM, hRC⟩, hrτ3⟩

/-- `pRank` is preserved on passing to a subgroup of index coprime to `p` (the `p`-part of the
order is unchanged).  (Replicated here from the `private` copy in `S12_Corollary1216`.) -/
theorem pRank_eq_of_le_of_not_dvd_index [Finite G] {p : ℕ} [Fact p.Prime]
    {H K : Subgroup G} (hHK : H ≤ K) (hidx : ¬ p ∣ (H.subgroupOf K).index) :
    pRank ↥H p = pRank ↥K p := by
  obtain ⟨R⟩ : Nonempty (Sylow p ↥H) := inferInstance
  set Rincl : Subgroup ↥K := (R : Subgroup ↥H).map (Subgroup.inclusion hHK) with hRincl
  have hcardRincl : Nat.card ↥Rincl = p ^ (Nat.card ↥K).factorization p := by
    have hidxcard : Nat.card ↥H * (H.subgroupOf K).index = Nat.card ↥K := by
      rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHK).toEquiv]
      exact (H.subgroupOf K).card_mul_index
    have hidx_ne : (H.subgroupOf K).index ≠ 0 := by
      intro hh; rw [hh, mul_zero] at hidxcard; exact (Nat.card_pos).ne' hidxcard.symm
    have hfact : (Nat.card ↥K).factorization p = (Nat.card ↥H).factorization p := by
      rw [← hidxcard, Nat.factorization_mul (Nat.card_pos).ne' hidx_ne, Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd hidx, add_zero]
    rw [hRincl, Subgroup.card_map_of_injective (Subgroup.inclusion_injective hHK),
      R.card_eq_multiplicity, hfact]
  have eR : ↥(R : Subgroup ↥H) ≃* ↥Rincl :=
    hRincl ▸ Subgroup.equivMapOfInjective _ (Subgroup.inclusion hHK)
      (Subgroup.inclusion_injective hHK)
  have hSylK : pRank ↥Rincl p = pRank ↥K p := by
    have hh := pRank_sylow_eq (Sylow.ofCard Rincl hcardRincl)
    rwa [Sylow.coe_ofCard] at hh
  rw [← pRank_sylow_eq R, ← hSylK]
  exact le_antisymm (pRank_le_of_injective (f := eR.toMonoidHom) eR.injective)
    (pRank_le_of_injective (f := eR.symm.toMonoidHom) eR.symm.injective)

/-- For `q ∈ τ₂(M)` and a `q`-element `y' ∈ E₂#`, the `q`-torsion `Ω₁(E₂)` is a rank-two
elementary abelian `q`-subgroup of `E` containing `y'`.  (`E₂` is abelian by Corollary 12.10(b),
and `r_q(E₂) = r_q(E) = r_q(M) = 2` since the index steps `E₂ ≤ E ≤ M` are `q`-coprime.) -/
theorem exists_elemAb_rank_two_le_E_mem_of_tau2 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M E E₁ E₂ E₃ : Subgroup G}
    (h : SubgroupESetup M E E₁ E₂ E₃) {q : ℕ} [Fact q.Prime] (hq : q ∈ tau2 M)
    {y' : G} (hy'E2 : y' ∈ E₂) (hy'q : y' ^ q = 1) (_hy'1 : y' ≠ 1) :
    ∃ A ∈ elemAbelianOfRank G q 2, A ≤ E ∧ y' ∈ A := by
  classical
  have hE2comm : IsMulCommutative ↥E₂ := (nilpotent_sigmaComplement_abelian hG h).2.1.1
  have hcomm : ∀ x ∈ E₂, ∀ y ∈ E₂, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE2comm.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  set A : Subgroup G := omega1OfAbelian G E₂ q hcomm with hAdef
  have hAelem : A.IsElementaryAbelian q := omega1OfAbelian_isElementaryAbelian
  have hAE2 : A ≤ E₂ := omega1OfAbelian_le
  have hAE : A ≤ E := hAE2.trans h.E₂_le
  have hy'A : y' ∈ A := (mem_omega1OfAbelian).mpr ⟨hy'E2, hy'q⟩
  -- `r_q(E₂) = 2`: two `q`-coprime index steps `E₂ ≤ E ≤ M`, then `r_q(M) = 2`.
  have hpRankE2 : pRank ↥E₂ q = 2 := by
    have hr1 : pRank ↥E₂ q = pRank ↥E q :=
      pRank_eq_of_le_of_not_dvd_index h.E₂_le (fun hdvd =>
        h.E₂_hall.index_no_pi q (Nat.mem_primeFactors.mpr
          ⟨Fact.out, hdvd, Subgroup.index_ne_zero_of_finite⟩) hq)
    have hr2 : pRank ↥E q = pRank ↥M q := by
      refine pRank_eq_of_le_of_not_dvd_index h.E_le (fun hdvd => ?_)
      have hqσ : q ∉ OddOrder.BG.Ch3.S10.sigma M := tau2_subset_sigma_compl M hq
      have hidxeq : (E.subgroupOf M).index = Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) := by
        rw [h.isComplement'_subgroupOf.index_eq_card,
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe (OddOrder.BG.Ch3.S10.Msigma_le M)).toEquiv]
      rw [hidxeq] at hdvd
      exact hqσ (OddOrder.BG.Ch3.S10.Msigma_isPiGroup M q
        (Nat.mem_primeFactors.mpr ⟨Fact.out, hdvd, Nat.card_pos.ne'⟩))
    rw [hr1, hr2, tau2_pRank_eq_two hq]
  -- `|A| = q²` from `q² ∣ |A|` (rank ≥ 2) and `log_q |A| ≤ r_q(E₂) = 2`.
  have hAcard : Nat.card ↥A = q ^ 2 := by
    have hdvd : q ^ 2 ∣ Nat.card ↥A :=
      hAdef ▸ pow_dvd_card_omega1OfAbelian_of_pos_le_pRank (by norm_num) hpRankE2.ge
    have hlog_le : Nat.log q (Nat.card ↥A) ≤ 2 := by
      have hAsub : (A.subgroupOf E₂).IsElementaryAbelian q :=
        IsElementaryAbelian.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hAE2).symm hAelem
      have hcardeq : Nat.card ↥(A.subgroupOf E₂) = Nat.card ↥A :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAE2).toEquiv
      have hle := le_pRank (A.subgroupOf E₂) hAsub
      rwa [hcardeq, hpRankE2] at hle
    have hcardpow : Nat.card ↥A = q ^ Nat.log q (Nat.card ↥A) := by
      rw [hAelem.log_card_eq_finrank, hAelem.card_eq_pow_finrank]
    have h2le : 2 ≤ Nat.log q (Nat.card ↥A) := by
      rw [hcardpow] at hdvd
      exact (Nat.pow_dvd_pow_iff_le_right (Fact.out : q.Prime).one_lt).mp hdvd
    rw [hcardpow]; congr 1; omega
  exact ⟨A, ⟨hAelem, hAcard⟩, hAE, hy'A⟩

/-- **BG Prop 14.2(a), case `κ ⊆ τ₁`, `E₂`-half** (mmd L3840, "by Lemma 13.12"): if
`C_{M_σ}(E₁) = K^* ≠ 1` (i.e. `M` is type `P` in the `κ ⊆ τ₁` case) then `E₁` acts regularly on
`E₂`.  If some `g ∈ E₁#` centralized `y' ∈ E₂#` (of prime order `q ∈ τ₂(M)`), the rank-two
`A = Ω₁(E₂) ∋ y'` would give `C_A(⟨g₀⟩) ≠ 1`, so Lemma 13.12 forces `C_{M_σ}(⟨g₀⟩) = 1`,
contradicting `C_{M_σ}(⟨g₀⟩) = C_{M_σ}(E₁) = K^* ≠ 1` (prime action). -/
theorem actsRegularlyOn_E2_E1_of_actsPrime [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M E E₁ E₂ E₃ : Subgroup G}
    (h : SubgroupESetup M E E₁ E₂ E₃) (hE1ne : E₁ ≠ ⊥)
    (hKstar : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (E₁ : Set G) ≠ ⊥) :
    ActsRegularlyOn E₂ E₁ := by
  classical
  have hE1prime : ActsPrimeOn (OddOrder.BG.Ch3.S10.Msigma M) E₁ := E1_actsPrime hG h hE1ne
  intro g hgE1 hg1
  rw [fixedByElement_def]
  by_contra hne
  -- A witness `y ∈ E₂#` centralizing `g`.
  obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hyE2 : y ∈ E₂ := hy.1
  have hyCg : y ∈ Subgroup.centralizer ({g} : Set G) := hy.2
  have hy1' : y ≠ 1 := fun hc => hy1 (Subtype.ext hc)
  -- `g₀ ∈ ⟨g⟩` of prime order `p ∈ τ₁(M)`, `P = ⟨g₀⟩`.
  obtain ⟨p, hp, hpdvd⟩ :=
    (orderOf g).exists_prime_and_dvd (by rwa [Ne, orderOf_eq_one_iff])
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨g₀, hg₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.zpowers g)) p
    (by rw [Nat.card_zpowers]; exact hpdvd)
  have hg₀g : (g₀ : G) ∈ Subgroup.zpowers g := g₀.2
  have hgE1' : Subgroup.zpowers g ≤ E₁ := Subgroup.zpowers_le.mpr hgE1
  have hg₀E1 : (g₀ : G) ∈ E₁ := hgE1' hg₀g
  have hPcard : Nat.card ↥(Subgroup.zpowers (g₀ : G)) = p := by
    rw [Nat.card_zpowers]
    exact (orderOf_injective (Subgroup.zpowers g).subtype
      (Subgroup.zpowers g).subtype_injective g₀).trans hg₀
  have hPelem : Subgroup.zpowers (g₀ : G) ∈ elemAbelianOfRank G p 1 :=
    ⟨Subgroup.IsElementaryAbelian.of_card_prime hPcard, by rw [hPcard, pow_one]⟩
  have hPbot : Subgroup.zpowers (g₀ : G) ≠ ⊥ := ne_bot_of_mem_elemAbelianOfRank_one hPelem
  have hPE1 : Subgroup.zpowers (g₀ : G) ≤ E₁ := Subgroup.zpowers_le.mpr hg₀E1
  have hPE : Subgroup.zpowers (g₀ : G) ≤ E := hPE1.trans h.E₁_le
  -- `p ∈ τ₁(M)`.
  have hpτ1 : p ∈ tau1 M := by
    have hc1 : Nat.card ↥(E₁.subgroupOf E) = Nat.card ↥E₁ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₁_le).toEquiv
    refine h.E₁_hall.1 p (hc1 ▸ Nat.mem_primeFactors.mpr ⟨hp, ?_, Nat.card_pos.ne'⟩)
    exact hPcard ▸ Subgroup.card_dvd_of_le hPE1
  -- `C_{M_σ}(P) = C_{M_σ}(E₁) = K^* ≠ ⊥`.
  have hCP : OddOrder.BG.Ch3.S10.Msigma M ⊓
      Subgroup.centralizer ((Subgroup.zpowers (g₀ : G) : Subgroup G) : Set G) ≠ ⊥ := by
    have := fixedBy_eq_of_le_of_ne_bot hE1prime hPE1 hPbot
    rw [fixedBy_def, fixedBy_def] at this
    rw [this]; exact hKstar
  -- `y' ∈ ⟨y⟩` of prime order `q ∈ τ₂(M)`.
  obtain ⟨q, hq, hqdvd⟩ :=
    (orderOf y).exists_prime_and_dvd (by rwa [Ne, orderOf_eq_one_iff])
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨y', hy'⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.zpowers y)) q
    (by rw [Nat.card_zpowers]; exact hqdvd)
  have hy'y : (y' : G) ∈ Subgroup.zpowers y := y'.2
  have hyE2' : Subgroup.zpowers y ≤ E₂ := Subgroup.zpowers_le.mpr hyE2
  have hy'E2 : (y' : G) ∈ E₂ := hyE2' hy'y
  have hy'ord : orderOf (y' : G) = q :=
    (orderOf_injective (Subgroup.zpowers y).subtype
      (Subgroup.zpowers y).subtype_injective y').trans hy'
  have hy'q : (y' : G) ^ q = 1 := by rw [← hy'ord]; exact pow_orderOf_eq_one _
  have hy'1 : (y' : G) ≠ 1 := by
    intro hc; rw [hc, orderOf_one] at hy'ord; exact hq.ne_one hy'ord.symm
  -- `q ∈ τ₂(M)`.
  have hqτ2 : q ∈ tau2 M := by
    have hc2 : Nat.card ↥(E₂.subgroupOf E) = Nat.card ↥E₂ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₂_le).toEquiv
    have hy'zpE2 : Subgroup.zpowers (y' : G) ≤ E₂ := Subgroup.zpowers_le.mpr hy'E2
    have hqdvdE2 : q ∣ Nat.card ↥E₂ := by
      have h1 : Nat.card ↥(Subgroup.zpowers (y' : G)) = q := by rw [Nat.card_zpowers, hy'ord]
      exact h1 ▸ Subgroup.card_dvd_of_le hy'zpE2
    exact h.E₂_hall.1 q (hc2 ▸ Nat.mem_primeFactors.mpr ⟨hq, hqdvdE2, Nat.card_pos.ne'⟩)
  -- rank-two `A = Ω₁(E₂) ∋ y'`.
  obtain ⟨A, hAmem, hAE, hy'A⟩ := exists_elemAb_rank_two_le_E_mem_of_tau2 hG h hqτ2 hy'E2 hy'q hy'1
  -- `y'` centralizes `g₀` (`y` centralizes `g`; `g₀ ∈ ⟨g⟩`, `y' ∈ ⟨y⟩`).
  have hComm_gy : Commute g y := hyCg g rfl
  have hy'Cg₀ : (y' : G) ∈ Subgroup.centralizer
      ((Subgroup.zpowers (g₀ : G) : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [SetLike.mem_coe, Subgroup.mem_zpowers_iff] at hw
    obtain ⟨i, rfl⟩ := hw
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hg₀g
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy'y
    rw [← hj, ← hk]
    exact (((hComm_gy.zpow_left j).zpow_left i).zpow_right k).eq
  have hCAP : A ⊓ Subgroup.centralizer ((Subgroup.zpowers (g₀ : G) : Subgroup G) : Set G) ≠ ⊥ :=
    fun hb => hy'1 (Subgroup.mem_bot.mp (hb ▸ Subgroup.mem_inf.mpr ⟨hy'A, hy'Cg₀⟩))
  -- Lemma 13.12: `C_{M_σ}(P) = ⊥`, contradicting `C_{M_σ}(P) = K^* ≠ ⊥`.
  exact hCP (Msigma_centralizer_eq_bot_of_tau1_tau2 hG h hpτ1 hqτ2 hPelem hPE hAmem hAE hCAP)

/-- **BG Prop 14.2(a), case `κ ⊆ τ₁`: `E₁` acts regularly on `U = E₂E₃`** (mmd L3840,
"acts regularly on `U = E₂E₃`").  Combines the `E₃`- and `E₂`-halves: `E = E₁ ⋉ (E₂E₃)` with
`E₃ ⊴ E` (Lemma 12.1(b)) and `E₁` normalizing `E₂` (Lemma 12.1(e)), so for `g ∈ E₁#` a fixed
`u = u₃u₂ ∈ E₂E₃` has both factors fixed (`E₂ ⊓ E₃ = 1`), forcing `u = 1`. -/
theorem actsRegularlyOn_E23_E1_of_caseTau1 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M E E₁ E₂ E₃ : Subgroup G}
    (h : SubgroupESetup M E E₁ E₂ E₃) (hE1ne : E₁ ≠ ⊥)
    (hKstar : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (E₁ : Set G) ≠ ⊥)
    (hτ3 : ¬ (kappa M ∩ tau3 M).Nonempty) :
    ActsRegularlyOn (E₂ ⊔ E₃) E₁ := by
  classical
  have hregE3 : ActsRegularlyOn E₃ E₁ :=
    actsRegularlyOn_E3_E1_of_kappa_inf_tau3_empty hG h hE1ne hKstar hτ3
  have hregE2 : ActsRegularlyOn E₂ E₁ :=
    actsRegularlyOn_E2_E1_of_actsPrime hG h hE1ne hKstar
  have hEnormE3 : E ≤ Subgroup.normalizer (E₃ : Set G) := (subgroupE_basic hG h).2.1.2
  have hE12normE2 : E₁ ⊔ E₂ ≤ Subgroup.normalizer (E₂ : Set G) :=
    (subgroupE_basic hG h).2.2.2.2.1.2.2
  -- `E₂ ⊓ E₃ = ⊥` (coprime: `τ₂ ∩ τ₃ = ∅`).
  have hcop23 : Nat.Coprime (Nat.card ↥E₂) (Nat.card ↥E₃) := by
    by_contra hnc
    obtain ⟨s, hs, hsm, hsn⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnc
    have hc2 : Nat.card ↥(E₂.subgroupOf E) = Nat.card ↥E₂ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₂_le).toEquiv
    have hc3 : Nat.card ↥(E₃.subgroupOf E) = Nat.card ↥E₃ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₃_le).toEquiv
    have hsτ2 : s ∈ tau2 M :=
      h.E₂_hall.1 s (hc2 ▸ Nat.mem_primeFactors.mpr ⟨hs, hsm, Nat.card_pos.ne'⟩)
    have hsτ3 : s ∈ tau3 M :=
      h.E₃_hall.1 s (hc3 ▸ Nat.mem_primeFactors.mpr ⟨hs, hsn, Nat.card_pos.ne'⟩)
    have h2 := tau2_pRank_eq_two hsτ2
    have h1 := tau3_pRank_eq_one hsτ3
    omega
  have hE23disj : E₂ ⊓ E₃ = ⊥ := by
    have hd1 : Nat.card ↥(E₂ ⊓ E₃) ∣ Nat.card ↥E₂ := Subgroup.card_dvd_of_le inf_le_left
    have hd2 : Nat.card ↥(E₂ ⊓ E₃) ∣ Nat.card ↥E₃ := Subgroup.card_dvd_of_le inf_le_right
    have hc1 : Nat.card ↥(E₂ ⊓ E₃) = 1 := Nat.dvd_one.mp (hcop23 ▸ Nat.dvd_gcd hd1 hd2)
    exact Subgroup.card_eq_one.mp hc1
  have hE3normSub : (E₃.subgroupOf E).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.E₃_le).mpr hEnormE3
  intro g hgE1 hg1
  rw [fixedByElement_def]
  have hgNE2 : g ∈ Subgroup.normalizer (E₂ : Set G) := hE12normE2 (Subgroup.mem_sup_left hgE1)
  have hgNE3 : g ∈ Subgroup.normalizer (E₃ : Set G) := hEnormE3 (h.E₁_le hgE1)
  refine le_antisymm ?_ bot_le
  intro u hu
  rw [Subgroup.mem_inf] at hu
  obtain ⟨huU, huCg⟩ := hu
  -- `gug⁻¹ = u`.
  have hgu : g * u = u * g := huCg g rfl
  -- decompose `u = u₃ * u₂` in `↥E` (`E₃` normal).
  have huE : u ∈ E := (sup_le h.E₂_le h.E₃_le) huU
  have hsupSub : (E₂ ⊔ E₃).subgroupOf E = E₃.subgroupOf E ⊔ E₂.subgroupOf E := by
    rw [Subgroup.subgroupOf_sup h.E₂_le h.E₃_le, sup_comm]
  obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup_of_normal_left.mp
    (hsupSub ▸ Subgroup.mem_subgroupOf.mpr huU :
      (⟨u, huE⟩ : ↥E) ∈ E₃.subgroupOf E ⊔ E₂.subgroupOf E)
  have hu3 : (a : G) ∈ E₃ := Subgroup.mem_subgroupOf.mp ha
  have hu2 : (b : G) ∈ E₂ := Subgroup.mem_subgroupOf.mp hb
  have hu32 : (a : G) * (b : G) = u := by have hh := congrArg Subtype.val hab; simpa using hh
  -- `g·u₃·g⁻¹ ∈ E₃`, `g·u₂·g⁻¹ ∈ E₂`.
  have hw3 : g * (a : G) * g⁻¹ ∈ E₃ := (Subgroup.mem_normalizer_iff.mp hgNE3 (a : G)).mp hu3
  have hw2 : g * (b : G) * g⁻¹ ∈ E₂ := (Subgroup.mem_normalizer_iff.mp hgNE2 (b : G)).mp hu2
  -- `(g u₃ g⁻¹)(g u₂ g⁻¹) = u₃ u₂`.
  have hconj : (g * (a : G) * g⁻¹) * (g * (b : G) * g⁻¹) = (a : G) * (b : G) := by
    have hgug : g * u * g⁻¹ = u := by rw [hgu]; group
    calc (g * (a : G) * g⁻¹) * (g * (b : G) * g⁻¹)
        = g * ((a : G) * (b : G)) * g⁻¹ := by group
      _ = g * u * g⁻¹ := by rw [hu32]
      _ = u := hgug
      _ = (a : G) * (b : G) := hu32.symm
  -- `c := u₃⁻¹·(g u₃ g⁻¹) = u₂·(g u₂ g⁻¹)⁻¹ ∈ E₂ ⊓ E₃ = 1`.
  set c : G := (a : G)⁻¹ * (g * (a : G) * g⁻¹) with hcdef
  have hcE3 : c ∈ E₃ := E₃.mul_mem (E₃.inv_mem hu3) hw3
  have hcE2 : c = (b : G) * (g * (b : G) * g⁻¹)⁻¹ := by
    have hw3eq : g * (a : G) * g⁻¹ = (a : G) * (b : G) * (g * (b : G) * g⁻¹)⁻¹ := by
      rw [← hconj]; group
    rw [hcdef, hw3eq]; group
  have hcE2' : c ∈ E₂ := hcE2 ▸ E₂.mul_mem hu2 (E₂.inv_mem hw2)
  have hc1 : c = 1 := Subgroup.mem_bot.mp (hE23disj ▸ Subgroup.mem_inf.mpr ⟨hcE2', hcE3⟩)
  -- so `g u₃ g⁻¹ = u₃` and (symmetrically) `g u₂ g⁻¹ = u₂`; both centralized ⟹ in `E_i ⊓ C(g) = ⊥`.
  have hu3fix : g * (a : G) * g⁻¹ = (a : G) := (inv_mul_eq_one.mp (hcdef ▸ hc1)).symm
  have hw2fix : g * (b : G) * g⁻¹ = (b : G) :=
    (mul_inv_eq_one.mp (by rw [← hcE2]; exact hc1)).symm
  have hu3bot : (a : G) = 1 := by
    have hmem : (a : G) ∈ E₃ ⊓ Subgroup.centralizer ({g} : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨hu3, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro y hy; rw [Set.mem_singleton_iff.mp hy]
      exact (mul_inv_eq_iff_eq_mul.mp hu3fix)
    have hr := hregE3 g hgE1 hg1
    rw [fixedByElement_def] at hr
    exact Subgroup.mem_bot.mp (hr ▸ hmem)
  have hu2bot : (b : G) = 1 := by
    have hmem : (b : G) ∈ E₂ ⊓ Subgroup.centralizer ({g} : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨hu2, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro y hy; rw [Set.mem_singleton_iff.mp hy]
      exact (mul_inv_eq_iff_eq_mul.mp hw2fix)
    have hr := hregE2 g hgE1 hg1
    rw [fixedByElement_def] at hr
    exact Subgroup.mem_bot.mp (hr ▸ hmem)
  rw [Subgroup.mem_bot, ← hu32, hu3bot, hu2bot, mul_one]

/-- **BG Prop 14.2(b1), case `κ ⊆ τ₁`: `N_E(X) ≤ E₁`** for `X ∈ ℰ¹(E₁)` (the Frobenius
normalizer fact).  Writing `e = u·k` (`u ∈ E₂E₃`, `k ∈ E₁`), `E₁` abelian gives `kgk⁻¹ = g`, so
`ugu⁻¹ = ege⁻¹ ∈ X ≤ E₁`; then `[u,g] ∈ E₁ ⊓ E₂E₃ = 1`, so `u` centralizes `g` and lies in
`C_{E₂E₃}(g) = 1` (regular action), forcing `u = 1`, i.e. `e = k ∈ E₁`. -/
theorem normalizer_inf_E_le_E1_of_caseTau1 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M E E₁ E₂ E₃ : Subgroup G}
    (h : SubgroupESetup M E E₁ E₂ E₃) (hE1ne : E₁ ≠ ⊥)
    (hKstar : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (E₁ : Set G) ≠ ⊥)
    (hτ3 : ¬ (kappa M ∩ tau3 M).Nonempty)
    {X : Subgroup G} {p : ℕ} [Fact p.Prime] (hX : X ∈ elemAbelianOfRank G p 1)
    (hXE1 : X ≤ E₁) :
    Subgroup.normalizer (X : Set G) ⊓ E ≤ E₁ := by
  classical
  have hreg23 : ActsRegularlyOn (E₂ ⊔ E₃) E₁ :=
    actsRegularlyOn_E23_E1_of_caseTau1 hG h hE1ne hKstar hτ3
  have hE1cyc : IsCyclic ↥E₁ := (subgroupE_basic hG h).2.2.2.1.1
  have hEnormE3 : E ≤ Subgroup.normalizer (E₃ : Set G) := (subgroupE_basic hG h).2.1.2
  have hE23norm : E ≤ Subgroup.normalizer ((E₂ ⊔ E₃ : Subgroup G) : Set G) :=
    (subgroupE_basic hG h).2.2.2.2.1.2.1
  have hEsup : E = E₁ ⊔ E₂ ⊔ E₃ := (subgroupE_basic hG h).2.2.2.2.1.1
  let : CommGroup ↥E₁ := hE1cyc.commGroup
  -- generator `g` of `X`.
  obtain ⟨⟨g, hgX⟩, hg1⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.mp (ne_bot_of_mem_elemAbelianOfRank_one hX)
  have hg1' : g ≠ 1 := fun hc => hg1 (Subtype.ext hc)
  have hgE1 : g ∈ E₁ := hXE1 hgX
  -- `E₁ ⊓ (E₂⊔E₃) = ⊥` (coprime `τ₁` vs `τ₂ ∪ τ₃`).
  have hc1E : Nat.card ↥(E₁.subgroupOf E) = Nat.card ↥E₁ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₁_le).toEquiv
  have hc2E : Nat.card ↥(E₂.subgroupOf E) = Nat.card ↥E₂ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₂_le).toEquiv
  have hc3E : Nat.card ↥(E₃.subgroupOf E) = Nat.card ↥E₃ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₃_le).toEquiv
  have hcop2 : Nat.Coprime (Nat.card ↥E₁) (Nat.card ↥E₂) := by
    by_contra hnc
    obtain ⟨s, hs, hsm, hsn⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnc
    have := tau1_pRank_eq_one
      (h.E₁_hall.1 s (hc1E ▸ Nat.mem_primeFactors.mpr ⟨hs, hsm, Nat.card_pos.ne'⟩))
    have := tau2_pRank_eq_two
      (h.E₂_hall.1 s (hc2E ▸ Nat.mem_primeFactors.mpr ⟨hs, hsn, Nat.card_pos.ne'⟩))
    omega
  have hcop3 : Nat.Coprime (Nat.card ↥E₁) (Nat.card ↥E₃) := by
    by_contra hnc
    obtain ⟨s, hs, hsm, hsn⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnc
    exact not_mem_tau3_of_mem_tau1
      (h.E₁_hall.1 s (hc1E ▸ Nat.mem_primeFactors.mpr ⟨hs, hsm, Nat.card_pos.ne'⟩))
      (h.E₃_hall.1 s (hc3E ▸ Nat.mem_primeFactors.mpr ⟨hs, hsn, Nat.card_pos.ne'⟩))
  have hE23disj : E₂ ⊓ E₃ = ⊥ := by
    have hd1 : Nat.card ↥(E₂ ⊓ E₃) ∣ Nat.card ↥E₂ := Subgroup.card_dvd_of_le inf_le_left
    have hd2 : Nat.card ↥(E₂ ⊓ E₃) ∣ Nat.card ↥E₃ := Subgroup.card_dvd_of_le inf_le_right
    have hcop23 : Nat.Coprime (Nat.card ↥E₂) (Nat.card ↥E₃) := by
      by_contra hnc
      obtain ⟨s, hs, hsm, hsn⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnc
      have := tau2_pRank_eq_two
        (h.E₂_hall.1 s (hc2E ▸ Nat.mem_primeFactors.mpr ⟨hs, hsm, Nat.card_pos.ne'⟩))
      have := tau3_pRank_eq_one
        (h.E₃_hall.1 s (hc3E ▸ Nat.mem_primeFactors.mpr ⟨hs, hsn, Nat.card_pos.ne'⟩))
      omega
    exact Subgroup.card_eq_one.mp (Nat.dvd_one.mp (hcop23 ▸ Nat.dvd_gcd hd1 hd2))
  have hcard23 : Nat.card ↥(E₂ ⊔ E₃) = Nat.card ↥E₂ * Nat.card ↥E₃ :=
    card_sup_eq_mul_of_le_normalizer_of_disjoint (h.E₂_le.trans hEnormE3) hE23disj
  have hE1_23_disj : E₁ ⊓ (E₂ ⊔ E₃) = ⊥ := by
    have hd1 : Nat.card ↥(E₁ ⊓ (E₂ ⊔ E₃)) ∣ Nat.card ↥E₁ := Subgroup.card_dvd_of_le inf_le_left
    have hd2 : Nat.card ↥(E₁ ⊓ (E₂ ⊔ E₃)) ∣ Nat.card ↥(E₂ ⊔ E₃) :=
      Subgroup.card_dvd_of_le inf_le_right
    have hcop : Nat.Coprime (Nat.card ↥E₁) (Nat.card ↥(E₂ ⊔ E₃)) :=
      hcard23 ▸ Nat.Coprime.mul_right hcop2 hcop3
    exact Subgroup.card_eq_one.mp (Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd hd1 hd2))
  -- the normalizer membership.
  intro e he
  rw [Subgroup.mem_inf] at he
  obtain ⟨heN, heE⟩ := he
  -- decompose `e = u * k`, `u ∈ E₂⊔E₃` (normal), `k ∈ E₁`.
  have hUnorm : ((E₂ ⊔ E₃).subgroupOf E).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (sup_le h.E₂_le h.E₃_le)).mpr hE23norm
  have hsuptop : ((E₂ ⊔ E₃).subgroupOf E) ⊔ (E₁.subgroupOf E) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (sup_le h.E₂_le h.E₃_le) h.E₁_le, Subgroup.subgroupOf_eq_top,
      hEsup]
    exact sup_le (sup_le le_sup_right (le_sup_left.trans le_sup_left))
      (le_sup_right.trans le_sup_left)
  obtain ⟨u, hu, k, hk, huk⟩ := Subgroup.mem_sup_of_normal_left.mp
    (hsuptop ▸ Subgroup.mem_top (⟨e, heE⟩ : ↥E))
  have huU : (u : G) ∈ E₂ ⊔ E₃ := Subgroup.mem_subgroupOf.mp hu
  have hkE1 : (k : G) ∈ E₁ := Subgroup.mem_subgroupOf.mp hk
  have huke : (u : G) * (k : G) = e := by have hh := congrArg Subtype.val huk; simpa using hh
  -- `k` commutes with `g` (`E₁` abelian).
  have hkg : (k : G) * g = g * (k : G) :=
    congrArg Subtype.val (mul_comm (⟨(k : G), hkE1⟩ : ↥E₁) (⟨g, hgE1⟩ : ↥E₁))
  -- `e g e⁻¹ = u g u⁻¹ ∈ X ≤ E₁`.
  have hege : e * g * e⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp heN g).mp hgX
  have hugu : (u : G) * g * (u : G)⁻¹ = e * g * e⁻¹ := by
    have hkgk : (k : G) * g * (k : G)⁻¹ = g := by rw [hkg]; group
    rw [← huke]
    calc (u : G) * g * (u : G)⁻¹
        = (u : G) * ((k : G) * g * (k : G)⁻¹) * (u : G)⁻¹ := by rw [hkgk]
      _ = (u : G) * (k : G) * g * ((u : G) * (k : G))⁻¹ := by group
  have huguE1 : (u : G) * g * (u : G)⁻¹ ∈ E₁ := hXE1 (hugu ▸ hege)
  -- `[u,g] ∈ E₁ ⊓ (E₂⊔E₃) = ⊥`.
  have hcommE1 : (u : G) * g * (u : G)⁻¹ * g⁻¹ ∈ E₁ := E₁.mul_mem huguE1 (E₁.inv_mem hgE1)
  have hgU : g ∈ Subgroup.normalizer ((E₂ ⊔ E₃ : Subgroup G) : Set G) := hE23norm (h.E₁_le hgE1)
  have hcommU : (u : G) * g * (u : G)⁻¹ * g⁻¹ ∈ E₂ ⊔ E₃ := by
    have h1 : g * (u : G)⁻¹ * g⁻¹ ∈ E₂ ⊔ E₃ :=
      (Subgroup.mem_normalizer_iff.mp hgU (u : G)⁻¹).mp ((E₂ ⊔ E₃).inv_mem huU)
    have heq : (u : G) * g * (u : G)⁻¹ * g⁻¹ = (u : G) * (g * (u : G)⁻¹ * g⁻¹) := by group
    rw [heq]; exact (E₂ ⊔ E₃).mul_mem huU h1
  have hcomm1 : (u : G) * g * (u : G)⁻¹ * g⁻¹ = 1 :=
    Subgroup.mem_bot.mp (hE1_23_disj ▸ Subgroup.mem_inf.mpr ⟨hcommE1, hcommU⟩)
  -- `u ∈ C_{E₂⊔E₃}(g) = ⊥`, so `u = 1` and `e = k ∈ E₁`.
  have hu1 : (u : G) = 1 := by
    have hug : (u : G) * g = g * (u : G) :=
      mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp hcomm1)
    have hmem : (u : G) ∈ (E₂ ⊔ E₃) ⊓ Subgroup.centralizer ({g} : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨huU, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro y hy; rw [Set.mem_singleton_iff.mp hy]; exact hug.symm
    have hr := hreg23 g hgE1 hg1'
    rw [fixedByElement_def] at hr
    exact Subgroup.mem_bot.mp (hr ▸ hmem)
  rw [← huke, hu1, one_mul]; exact hkE1

/-- **The §12 complement `E` is a Frobenius group** in case `τ₁` with `U = E₂E₃ ≠ 1`.
`E₁` acts regularly (fixed-point-freely) on the normal subgroup `U = E₂ ⊔ E₃`
(`actsRegularlyOn_E23_E1_of_caseTau1`), and `E = E₁ ⋉ U` (`SubgroupESetup.eq_sup`), so `E` is a
Frobenius group with kernel `U` and complement `E₁`.  This is the Frobenius structure that
Proposition 14.2(g) feeds to Theorem 3.10(a). -/
theorem isFrobeniusGroup_E_of_caseTau1 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M E E₁ E₂ E₃ : Subgroup G}
    (h : SubgroupESetup M E E₁ E₂ E₃) (hE1ne : E₁ ≠ ⊥)
    (hKstar : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (E₁ : Set G) ≠ ⊥)
    (hτ3 : ¬ (kappa M ∩ tau3 M).Nonempty)
    (hUne : (E₂ ⊔ E₃ : Subgroup G) ≠ ⊥) :
    OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥E
      ((E₂ ⊔ E₃).subgroupOf E) (E₁.subgroupOf E) := by
  classical
  have hreg : ActsRegularlyOn (E₂ ⊔ E₃) E₁ :=
    actsRegularlyOn_E23_E1_of_caseTau1 hG h hE1ne hKstar hτ3
  have hE23le : (E₂ ⊔ E₃ : Subgroup G) ≤ E := sup_le h.E₂_le h.E₃_le
  have hE1le : E₁ ≤ E := h.E₁_le
  have hE23norm : E ≤ Subgroup.normalizer ((E₂ ⊔ E₃ : Subgroup G) : Set G) := h.E23_normal hG
  -- `E₁ ⊓ (E₂ ⊔ E₃) = ⊥` (a nonidentity common element would centralize itself, contra FPF).
  have hdisj : E₁ ⊓ (E₂ ⊔ E₃) = ⊥ := by
    refine le_antisymm (fun g hg => ?_) bot_le
    rw [Subgroup.mem_inf] at hg
    obtain ⟨hgE1, hgU⟩ := hg
    rw [Subgroup.mem_bot]
    by_contra hg1
    have hr := hreg g hgE1 hg1
    rw [fixedByElement_def, eq_bot_iff] at hr
    refine hg1 (Subgroup.mem_bot.mp (hr ?_))
    exact Subgroup.mem_inf.mpr ⟨hgU, Subgroup.mem_centralizer_iff.mpr
      (fun y hy => by rw [Set.mem_singleton_iff.mp hy])⟩
  -- normality of the kernel.
  have hKnorm : ((E₂ ⊔ E₃).subgroupOf E).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hE23norm
  refine ⟨hKnorm, ?_, ?_, ?_, ?_⟩
  · -- complement: disjoint + product covers `↥E`.
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [disjoint_iff]
      have hi : (E₂ ⊔ E₃).subgroupOf E ⊓ E₁.subgroupOf E = ((E₂ ⊔ E₃) ⊓ E₁).subgroupOf E := rfl
      rw [hi, inf_comm, hdisj, Subgroup.bot_subgroupOf]
    · have := hKnorm
      have hsupG : (E₂ ⊔ E₃) ⊔ E₁ = E := by rw [h.eq_sup hG]; ac_rfl
      have hsup : (E₂ ⊔ E₃).subgroupOf E ⊔ E₁.subgroupOf E = ⊤ := by
        rw [← Subgroup.subgroupOf_sup hE23le hE1le, hsupG, Subgroup.subgroupOf_self]
      have hmul := Subgroup.normal_mul ((E₂ ⊔ E₃).subgroupOf E) (E₁.subgroupOf E)
      rw [hsup, Subgroup.coe_top] at hmul
      exact hmul.symm
  · rw [ne_eq, Subgroup.subgroupOf_eq_bot]
    exact fun hd => hUne (hd.eq_bot_of_le hE23le)
  · rw [ne_eq, Subgroup.subgroupOf_eq_bot]
    exact fun hd => hE1ne (hd.eq_bot_of_le hE1le)
  · -- Frobenius condition from the fixed-point-free action.
    intro a ha hane n hn hnne
    simp only [Subgroup.mem_subgroupOf] at ha hn
    intro hcontra
    have hval : (a : G) * (n : G) * (a : G)⁻¹ = (n : G) := by
      have := congrArg (Subtype.val) hcontra; push_cast at this; exact this
    have hane' : (a : G) ≠ 1 := fun hc => hane (Subtype.ext (by simpa using hc))
    have hnne' : (n : G) ≠ 1 := fun hc => hnne (Subtype.ext (by simpa using hc))
    have hr := hreg (a : G) ha hane'
    rw [fixedByElement_def, eq_bot_iff] at hr
    refine hnne' (Subgroup.mem_bot.mp (hr ?_))
    exact Subgroup.mem_inf.mpr ⟨hn, Subgroup.mem_centralizer_iff.mpr
      (fun y hy => by rw [Set.mem_singleton_iff.mp hy]; exact mul_inv_eq_iff_eq_mul.mp hval)⟩

/-- The family `M_P` of type-P maximal subgroups. -/
def maximalTypePFamily (G : Type*) [Group G] : Set (Subgroup G) :=
  {M | M ∈ maximalSubgroups G ∧ IsTypeP M}

/-- BG `M_sigma(x)`: maximal subgroups whose `M_sigma` contains the element `x`. -/
def maximalSigmaSubgroupsOfElement (x : G) : Set (Subgroup G) :=
  {M | M ∈ maximalSubgroups G ∧ x ∈ OddOrder.BG.Ch3.S10.Msigma M}

/-- The nonidentity part `M_σ^#` of `M_σ` (`= sharpSubgroup M_σ`).

**Naming caveat:** BG's `M̃` — used in Lemma 14.5(c), Theorem 14.7(e), and the Corollary 14.9
covering — is the *larger* set `{ x x' | x ∈ M_σ^#, x' ∈ R(x) }`, where `R(x)` is the normal
Hall subgroup of `C_G(x)` from Theorem 14.4 (it adjoins the `ℓ_σ = 2` "twisted" elements).  So
this `sigmaSharp` is only the `ℓ_σ = 1` core `M_σ^#`, a strict under-approximation of `M̃`;
downstream uses that intend BG's `M̃` must take `Conjugacy145C.Mtilde` instead
(`sigmaSharp_subset_Mtilde` is the easy inclusion).  `R(x)` is `Conjugacy145C.Rsub`, and
`S16_MainResults.Notation` carries its Theorem D(3) properties (`FT_signalizer_isHall`,
`FT_signalizer_normal_in_centralizer`).  See `notes/bg/s14_typeP_counting.md`. -/
def sigmaSharp (M : Subgroup G) : Set G :=
  sharpSubgroup (OddOrder.BG.Ch3.S10.Msigma M)

/-- The conjugacy saturation `C_G(M_tilde)` used in the counting formulas. -/
def sigmaConjugacySaturation (M : Subgroup G) : Set G :=
  conjClassSet (sigmaSharp M)

/-- Subgroup conjugacy in the ambient group. -/
def IsConjugateSubgroup (M N : Subgroup G) : Prop :=
  ∃ g : G, MulAut.conj g • M = N

/-- Subgroup conjugacy is reflexive (conjugate by `1`). -/
@[refl] theorem IsConjugateSubgroup.refl (M : Subgroup G) : IsConjugateSubgroup M M :=
  ⟨1, by rw [map_one, one_smul]⟩

/-- Subgroup conjugacy is symmetric (conjugate back by `g⁻¹`). -/
theorem IsConjugateSubgroup.symm {M N : Subgroup G} (h : IsConjugateSubgroup M N) :
    IsConjugateSubgroup N M := by
  obtain ⟨g, hg⟩ := h
  exact ⟨g⁻¹, by rw [← hg, ← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]⟩

/-- Subgroup conjugacy is transitive (compose the conjugators). -/
theorem IsConjugateSubgroup.trans {M N P : Subgroup G} (h₁ : IsConjugateSubgroup M N)
    (h₂ : IsConjugateSubgroup N P) : IsConjugateSubgroup M P := by
  obtain ⟨g, hg⟩ := h₁
  obtain ⟨g', hg'⟩ := h₂
  exact ⟨g' * g, by rw [map_mul, mul_smul, hg, hg']⟩

/-- A conjugate of a maximal subgroup is maximal: `IsConjugateSubgroup` preserves
`maximalSubgroups`.  The type-`P` conjugacy arguments of Theorem 14.7 and Corollary 14.8 move
maximal subgroups around by conjugation, so they need maximality to be conjugacy-stable. -/
theorem mem_maximalSubgroups_of_isConjugateSubgroup {M N : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (h : IsConjugateSubgroup M N) :
    N ∈ maximalSubgroups G := by
  obtain ⟨g, rfl⟩ := h
  exact mem_maximalSubgroups.mpr
    (OddOrder.BG.Ch3.S12.isCoatom_conj_smul (mem_maximalSubgroups.mp hM))

/-- `Z_tilde = Z - (K union K*)` in Theorem 14.7. -/
def zTilde (K Kstar : Subgroup G) : Set G :=
  ((K ⊔ Kstar : Subgroup G) : Set G) \ ((K : Set G) ∪ (Kstar : Set G))

/-- The `π`-part of a finite-order element `g`, as a *function*: the `π`-element factor of the
unique two-block decomposition `g = (π-part) * (π′-part)` (`exists_isPiElement_mul`, made into a
function via `Classical.choose`).  This is Coq's `g.`_π`. -/
noncomputable def piPart [Finite G] (π : Set ℕ) (g : G) : G :=
  (exists_isPiElement_mul π g).choose

/-- The decomposition behind `piPart`: there is a commuting `π′`-element `b`, a power of `g`, with
`piPart π g * b = g`. -/
theorem piPart_spec [Finite G] (π : Set ℕ) (g : G) :
    ∃ b : G, piPart π g * b = g ∧ Commute (piPart π g) b ∧
      IsPiElement π (piPart π g) ∧ IsPiElement πᶜ b ∧
      piPart π g ∈ Subgroup.zpowers g ∧ b ∈ Subgroup.zpowers g :=
  (exists_isPiElement_mul π g).choose_spec

/-- `piPart π g` is a `π`-element. -/
theorem isPiElement_piPart [Finite G] (π : Set ℕ) (g : G) : IsPiElement π (piPart π g) := by
  obtain ⟨_, _, _, h, _, _, _⟩ := piPart_spec π g; exact h

/-- The identity has trivial `π`-part. -/
theorem piPart_one [Finite G] (π : Set ℕ) : piPart π (1 : G) = 1 := by
  obtain ⟨b, hmul, hcomm, hpiA, hpiB, -, -⟩ := piPart_spec π (1 : G)
  exact (isPiElement_mul_unique hmul hcomm hpiA hpiB (one_mul (1 : G)) (Commute.refl 1)
    (isPiElement_one π) (isPiElement_one πᶜ)).1

/-- If the `π`-part of `g` is trivial, then `g` itself is a `π′`-element. -/
theorem isPiElement_compl_of_piPart_eq_one [Finite G] {π : Set ℕ} {g : G}
    (h : piPart π g = 1) : IsPiElement πᶜ g := by
  obtain ⟨b, hmul, -, -, hpiB, -, -⟩ := piPart_spec π g
  rw [h, one_mul] at hmul
  rwa [hmul] at hpiB

/-- Conjugation preserves the `π`-element property (the conjugate has the same order). -/
theorem isPiElement_conj {π : Set ℕ} (h : G) {a : G} (ha : IsPiElement π a) :
    IsPiElement π (h * a * h⁻¹) := by
  have key : orderOf (h * a * h⁻¹) = orderOf a := by
    have hh := orderOf_injective (MulAut.conj h).toMonoidHom (MulAut.conj h).injective a
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hh
  intro p hp
  rw [key] at hp
  exact ha p hp

/-- **The `π`-part is conjugation-equivariant** (`piPart π (h x h⁻¹) = h (piPart π x) h⁻¹`).
Conjugating the unique decomposition `x = (π-part)(π′-part)` gives a decomposition of `h x h⁻¹`;
uniqueness identifies its `π`-part with `h (piPart π x) h⁻¹`. -/
theorem piPart_conj [Finite G] (π : Set ℕ) (h x : G) :
    piPart π (h * x * h⁻¹) = h * piPart π x * h⁻¹ := by
  obtain ⟨bx, hxmul, hxcomm, hxpiA, hxpiB, -, -⟩ := piPart_spec π x
  obtain ⟨b', hmul', hcomm', hpiA', hpiB', -, -⟩ := piPart_spec π (h * x * h⁻¹)
  have hprod : (h * piPart π x * h⁻¹) * (h * bx * h⁻¹) = h * x * h⁻¹ := by
    calc (h * piPart π x * h⁻¹) * (h * bx * h⁻¹)
        = h * (piPart π x * bx) * h⁻¹ := by group
      _ = h * x * h⁻¹ := by rw [hxmul]
  have hBcomm : Commute (h * piPart π x * h⁻¹) (h * bx * h⁻¹) := by
    have hm := hxcomm.map (MulAut.conj h)
    simpa only [MulAut.conj_apply] using hm
  exact (isPiElement_mul_unique hmul' hcomm' hpiA' hpiB' hprod hBcomm
    (isPiElement_conj h hxpiA) (isPiElement_conj h hxpiB)).1

/-- A `π`-element is its own `π`-part. -/
theorem piPart_self_of_isPiElement [Finite G] {π : Set ℕ} {g : G} (hg : IsPiElement π g) :
    piPart π g = g := by
  obtain ⟨b, hmul, hcomm, hpiA, hpiB, -, -⟩ := piPart_spec π g
  exact (isPiElement_mul_unique hmul hcomm hpiA hpiB (mul_one g) (Commute.one_right g)
    hg (isPiElement_one πᶜ)).1

/-- A `π′`-element has trivial `π`-part. -/
theorem piPart_eq_one_of_isPiElement_compl [Finite G] {π : Set ℕ} {g : G}
    (hg : IsPiElement πᶜ g) : piPart π g = 1 := by
  obtain ⟨b, hmul, hcomm, hpiA, hpiB, -, -⟩ := piPart_spec π g
  exact (isPiElement_mul_unique hmul hcomm hpiA hpiB (one_mul g) (Commute.one_left g)
    (isPiElement_one π) hg).1

/-- The `π`-part of `g` is a power of `g`. -/
theorem piPart_mem_zpowers [Finite G] (π : Set ℕ) (g : G) :
    piPart π g ∈ Subgroup.zpowers g := by
  obtain ⟨_, _, _, _, _, hz, _⟩ := piPart_spec π g; exact hz

/-- A prime of `π` dividing `orderOf g` also divides `orderOf (piPart π g)` (it cannot land in the
`π′`-part `b`, whose order is coprime to `π`). -/
theorem prime_dvd_orderOf_piPart [Finite G] {π : Set ℕ} {p : ℕ} (hp : p.Prime) (hpπ : p ∈ π)
    {g : G} (hpg : p ∣ orderOf g) : p ∣ orderOf (piPart π g) := by
  obtain ⟨b, hmul, hcomm, _, hpiB, _, _⟩ := piPart_spec π g
  have hdvd : orderOf g ∣ orderOf (piPart π g) * orderOf b := by
    have h := hcomm.orderOf_mul_dvd_mul_orderOf; rwa [hmul] at h
  rcases hp.dvd_mul.mp (hpg.trans hdvd) with h | h
  · exact h
  · exact absurd hpπ (hpiB p (Nat.mem_primeFactors.mpr ⟨hp, h, (orderOf_pos b).ne'⟩))

/-- **The `π`-part is multiplicative on commuting elements** (Coq `consttM`): for commuting `x, y`,
`piPart π (x * y) = piPart π x * piPart π y`.  Both `π`-parts are powers of `x`, `y`, so they
commute
(as do the two `π′`-parts and the cross pairs), letting `x * y = (xπ yπ)(xπ′ yπ′)` be rearranged
into
a commuting `π`-element times `π′`-element; uniqueness of the `π`-decomposition
(`isPiElement_mul_unique`) identifies its `π`-part with `xπ yπ`.  The computational tool behind the
`σ`-decomposition of a `σ`-cover element `x · R(x)` (BG Lemma 14.5). -/
theorem piPart_mul_of_commute [Finite G] {π : Set ℕ} {x y : G} (hcomm : Commute x y) :
    piPart π (x * y) = piPart π x * piPart π y := by
  obtain ⟨cx, hxmul, hxc, hxπ, hxπ', hxz, hcxz⟩ := piPart_spec π x
  obtain ⟨cy, hymul, hyc, hyπ, hyπ', hyz, hcyz⟩ := piPart_spec π y
  obtain ⟨c, hmul, hc, hπ, hπ', -, -⟩ := piPart_spec π (x * y)
  -- powers of `x` commute with powers of `y` (as `x, y` commute).
  have hcross : ∀ {a b : G}, a ∈ Subgroup.zpowers x → b ∈ Subgroup.zpowers y → Commute a b := by
    intro a b ha hb
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact hcomm.zpow_zpow m n
  have hcyx : Commute (piPart π y) cx := (hcross hcxz hyz).symm
  have hprod : (piPart π x * piPart π y) * (cx * cy) = x * y := by
    calc (piPart π x * piPart π y) * (cx * cy)
        = piPart π x * (piPart π y * cx) * cy := by group
      _ = piPart π x * (cx * piPart π y) * cy := by rw [hcyx]
      _ = (piPart π x * cx) * (piPart π y * cy) := by group
      _ = x * y := by rw [hxmul, hymul]
  have hABcomm : Commute (piPart π x * piPart π y) (cx * cy) :=
    Commute.mul_left (Commute.mul_right hxc (hcross hxz hcyz))
      (Commute.mul_right (hcross hcxz hyz).symm hyc)
  exact (isPiElement_mul_unique hmul hc hπ hπ' hprod hABcomm
    (isPiElement_mul_of_commute (hcross hxz hyz) hxπ hyπ)
    (isPiElement_mul_of_commute (hcross hcxz hcyz) hxπ' hyπ')).1

/-- The `σ(M)`-part of an element `x` (Coq `x.`_{σ(M)}`): its `σ(M)`-component in the two-block
π-part decomposition. -/
noncomputable def sigmaPart [Finite G] (M : Subgroup G) (x : G) : G :=
  piPart (OddOrder.BG.Ch3.S10.sigma M) x

/-- **BG `sigma_decomposition x`** (Coq `sigma_decomposition`): the set of nonidentity `σ(M)`-parts
of `x` ranging over the maximal subgroups `M`. -/
noncomputable def sigmaDecomposition [Finite G] (x : G) : Set G :=
  {y | ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ y = sigmaPart M x} \ {1}

/-- **BG `sigma_length x = #|sigma_decomposition x|`** (Coq `sigma_length`).
`sigmaLength_eq_zero_iff`
(Coq `ell_sigma0P`) is proved further down, after `exists_mem_sigma_of_prime_dvd_card`. -/
noncomputable def sigmaLength [Finite G] (x : G) : ℕ :=
  (sigmaDecomposition x).ncard

/-- Every element of `M_σ` is a `σ(M)`-element (its order divides `|M_σ|`, a `σ(M)`-number). -/
theorem isPiElement_sigma_of_mem_Msigma [Finite G] {M : Subgroup G} {x : G}
    (hx : x ∈ OddOrder.BG.Ch3.S10.Msigma M) :
    IsPiElement (OddOrder.BG.Ch3.S10.sigma M) x := by
  intro p hp
  have horx : orderOf x = orderOf (⟨x, hx⟩ : ↥(OddOrder.BG.Ch3.S10.Msigma M)) := by
    simp
  have hdvd : orderOf x ∣ Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) := by
    rw [horx]; exact orderOf_dvd_natCard _
  exact OddOrder.BG.Ch3.S10.Msigma_isPiGroup M p
    (Nat.primeFactors_mono hdvd (Nat.card_pos).ne' hp)

/-- **`M_σ`-membership is exactly being a `σ(M)`-element** (for `x ∈ M`).  `M_σ` is the *normal*
`σ(M)`-Hall of `M` (`Msigma_isHall`), so it absorbs every `σ(M)`-subgroup; hence `x ∈ M_σ ⟺ ⟨x⟩` is
a `σ(M)`-group `⟺ x` is a `σ(M)`-element.  In particular `M_σ`-membership of an element of `M` is
determined by its order, so it is conjugation-invariant (`isPiElement_conj`) — the BG Theorem E
"distinct orders across pieces" content for the `M_σ` piece. -/
theorem mem_Msigma_iff_isPiElement_sigma [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {x : G} (hxM : x ∈ M) :
    x ∈ OddOrder.BG.Ch3.S10.Msigma M ↔ IsPiElement (OddOrder.BG.Ch3.S10.sigma M) x := by
  refine ⟨isPiElement_sigma_of_mem_Msigma, fun hpi => ?_⟩
  have hzpi : Ch03.Subgroup.IsPiGroup (OddOrder.BG.Ch3.S10.sigma M) (Subgroup.zpowers x) := by
    intro p hp
    rw [Nat.card_zpowers] at hp
    exact hpi p hp
  exact OddOrder.BG.Ch3.S10.sigma_subgroup_le_Msigma_of_isHall
    (OddOrder.BG.Ch3.S10.Msigma_isHall hG hM) (Subgroup.zpowers_le.mpr hxM) hzpi
    (Subgroup.mem_zpowers x)

/-- **An element of `M` whose order is coprime to `[M : N]` lies in the normal `N ≤ M`.**  Pure
group theory: `x^[M:N] ∈ N` (`Subgroup.pow_index_mem`), and `x ∈ ⟨x^[M:N]⟩` because `[M:N]` is
coprime to `orderOf x` (`exists_pow_eq_self_of_coprime`).  The engine for "a normal `π′`-Hall of `M`
absorbs every `π′`-element of `M`" (apply with `[M:N]` a `π`-number and `x` a `π′`-element) — used
for the `A(M)` / `κ(M)′`-Hall piece of BG Theorem E's "distinct orders". -/
theorem mem_of_coprime_index [Finite G] {M N : Subgroup G} (_hNM : N ≤ M)
    [(N.subgroupOf M).Normal] {x : G} (hxM : x ∈ M)
    (hcop : Nat.Coprime ((N.subgroupOf M).index) (orderOf x)) : x ∈ N := by
  have hpow : x ^ (N.subgroupOf M).index ∈ N := by
    have h := Subgroup.pow_index_mem (N.subgroupOf M) ⟨x, hxM⟩
    rw [Subgroup.mem_subgroupOf] at h
    simpa using h
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hm]
  exact pow_mem hpow m

/-- **The index `[M : U ⊔ M_σ]` is a `κ(M)`-number** (`M` maximal, `M_σ` the `σ(M)`-Hall, `U` a
`(κ∪σ)′`-Hall).  Since `M_σ ≤ U ⊔ M_σ` and `U ≤ U ⊔ M_σ`, `[M : U⊔M_σ]` divides both `[M : M_σ]` (a
`σ′`-number, `Msigma_subgroupOf_isHall`) and `[M : U]` (a `κ∪σ`-number, `hU`), so each of its primes
avoids `σ` yet lies in `κ ∪ σ`, i.e. in `κ(M)`.  Combined with `mem_of_coprime_index`, this gives
the
`A(M)`-piece absorption "a `κ(M)′`-element of `M` lies in `U ⊔ M_σ`" of BG Theorem E. -/
theorem index_U_sup_Msigma_primeFactors_subset_kappa [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M U : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {p : ℕ} (hp : p ∈ ((U ⊔ OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).index.primeFactors) :
    p ∈ kappa M := by
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpdvd : p ∣ ((U ⊔ OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).index :=
    Nat.dvd_of_mem_primeFactors hp
  have hdvdMσ : ((U ⊔ OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).index ∣
      ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).index :=
    Subgroup.index_dvd_of_le (Subgroup.subgroupOf_mono M le_sup_right)
  have hdvdU : ((U ⊔ OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).index ∣ (U.subgroupOf M).index :=
    Subgroup.index_dvd_of_le (Subgroup.subgroupOf_mono M le_sup_left)
  have hpnσ : p ∉ OddOrder.BG.Ch3.S10.sigma M :=
    (OddOrder.BG.Ch3.S10.Msigma_subgroupOf_isHall hG hM).index_no_pi p
      (Nat.mem_primeFactors.mpr ⟨hpp, hpdvd.trans hdvdMσ, Subgroup.index_ne_zero_of_finite⟩)
  have hpnκσ : p ∉ (kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ :=
    hU.index_no_pi p
      (Nat.mem_primeFactors.mpr ⟨hpp, hpdvd.trans hdvdU, Subgroup.index_ne_zero_of_finite⟩)
  simp only [Set.mem_compl_iff, not_not, Set.mem_union] at hpnκσ
  exact hpnκσ.resolve_right hpnσ

/-- **`|H ⊔ N|` divides `|H| · |N|`** for `N ◁ G` (Noether's second isomorphism: `[H⊔N : N] =
[H : H⊓N]`, so `|H⊔N| = [H : H⊓N]·|N|` with `[H : H⊓N] ∣ |H|`).  Used to bound `π(U ⊔ M_σ) ⊆ κ′`
from `π(U) ⊆ (κ∪σ)′` and `π(M_σ) ⊆ σ` (the `A(M)`-piece forward, with `M_σ ◁ M`). -/
theorem card_sup_dvd_mul_of_normal {H N : Subgroup G} [N.Normal] :
    Nat.card ↥(H ⊔ N) ∣ Nat.card ↥H * Nat.card ↥N := by
  have e : (N.subgroupOf H).index = (N.subgroupOf (H ⊔ N)).index := by
    have h := Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalQuotient H N).toEquiv
    simpa [Subgroup.index] using h
  have hN : Nat.card ↥(N.subgroupOf (H ⊔ N)) = Nat.card ↥N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  have h1 : Nat.card ↥(H ⊔ N) = (N.subgroupOf (H ⊔ N)).index * Nat.card ↥N := by
    rw [← Subgroup.card_mul_index (N.subgroupOf (H ⊔ N)), hN, mul_comm]
  rw [h1, ← e]
  exact mul_dvd_mul_right (N.subgroupOf H).index_dvd_card (Nat.card ↥N)

/-- **`U ⊔ M_σ`-membership is exactly being a `κ(M)′`-element** (for `x ∈ M`, given `U⊔M_σ ◁ M` as
`hnorm`).  `U⊔M_σ` is the normal `κ(M)′`-Hall of `M`: forward, `|U⊔M_σ| ∣ |U||M_σ|`
(`card_sup_dvd_mul_of_normal`, `M_σ ◁ M`) and `π(U), π(M_σ) ⊆ κ′`, so any `x ∈ U⊔M_σ` is a
`κ′`-element; backward, `[M:U⊔M_σ]` is a `κ`-number
(`index_U_sup_Msigma_primeFactors_subset_kappa`),
coprime to a `κ′`-element's order, so `mem_of_coprime_index` puts it in `U⊔M_σ`.  The `A(M)`-piece
of
BG Theorem E's "distinct orders": `U⊔M_σ`-membership of an element of `M` is order-determined. -/
theorem mem_U_sup_Msigma_iff_isPiElement_kappa_compl [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M U : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hUM : U ≤ M)
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hnorm : ((U ⊔ OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).Normal)
    {x : G} (hxM : x ∈ M) :
    x ∈ U ⊔ OddOrder.BG.Ch3.S10.Msigma M ↔ IsPiElement (kappa M)ᶜ x := by
  have := hnorm
  have hMσM : OddOrder.BG.Ch3.S10.Msigma M ≤ M := OddOrder.BG.Ch3.S10.Msigma_le M
  refine ⟨fun hx p hp => ?_, fun hpi => ?_⟩
  · -- forward: `x ∈ U⊔M_σ ⟹` `p ∈ π(orderOf x) ⟹ p ∉ κ`.
    have hpord : p ∣ orderOf x := Nat.dvd_of_mem_primeFactors hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have h1 : orderOf x ∣ Nat.card ↥(U ⊔ OddOrder.BG.Ch3.S10.Msigma M) := by
      have heq : orderOf x = orderOf (⟨x, hx⟩ : ↥(U ⊔ OddOrder.BG.Ch3.S10.Msigma M)) :=
        orderOf_injective (U ⊔ OddOrder.BG.Ch3.S10.Msigma M).subtype
          (U ⊔ OddOrder.BG.Ch3.S10.Msigma M).subtype_injective ⟨x, hx⟩
      rw [heq]; exact orderOf_dvd_natCard _
    have h2 : Nat.card ↥(U ⊔ OddOrder.BG.Ch3.S10.Msigma M) ∣
        Nat.card ↥U * Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) := by
      have : ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).Normal := by
        rw [OddOrder.BG.Ch3.S10.Msigma_subgroupOf]; infer_instance
      have hdvd := card_sup_dvd_mul_of_normal (H := U.subgroupOf M)
        (N := (OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M)
      rw [← Subgroup.subgroupOf_sup hUM hMσM,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe (sup_le hUM hMσM)).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMσM).toEquiv] at hdvd
      exact hdvd
    have hp2 : p ∣ Nat.card ↥U * Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) :=
      (hpord.trans h1).trans h2
    rcases (hpp.dvd_mul.mp hp2) with hpU | hpMσ
    · have hpfU : p ∈ (Nat.card ↥(U.subgroupOf M)).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hpp,
          (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM).toEquiv) ▸ hpU, Nat.card_pos.ne'⟩
      have := hU.primeFactors_card_subset p hpfU
      simp only [Set.mem_compl_iff, Set.mem_union, not_or] at this
      exact this.1
    · have hpfMσ : p ∈ (Nat.card ↥((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M)).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hpp,
          (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMσM).toEquiv) ▸ hpMσ, Nat.card_pos.ne'⟩
      exact fun hpκ => kappa_subset_sigmaCompl hpκ
        ((OddOrder.BG.Ch3.S10.Msigma_subgroupOf_isHall hG hM).primeFactors_card_subset p hpfMσ)
  · -- backward: `κ′`-element of `M` lies in `U⊔M_σ`.
    refine mem_of_coprime_index (sup_le hUM hMσM) hxM ?_
    refine (Nat.disjoint_primeFactors Subgroup.index_ne_zero_of_finite
      (orderOf_pos x).ne').mp ?_
    rw [Finset.disjoint_left]
    intro p hpfκ hpfo
    exact (hpi p hpfo) (index_U_sup_Msigma_primeFactors_subset_kappa hG hM hU hpfκ)

/-- For a `σ(M)`-element `x`, every `σ(L)`-part (`L` maximal) is either `x` or `1`: if `L` is
conjugate to `M` then `σ(L) = σ(M)` contains all primes of `x` (`sigmaPart L x = x`); otherwise
`σ(M) ∩ σ(L) = ∅` (`sigma_disjoint_of_nonconjugate`) so `x` avoids `σ(L)` (`sigmaPart L x = 1`). -/
theorem sigmaPart_eq_self_or_one_of_isPiElement_sigma [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {x : G} (hx : IsPiElement (OddOrder.BG.Ch3.S10.sigma M) x) {L : Subgroup G}
    (hL : L ∈ maximalSubgroups G) :
    sigmaPart L x = x ∨ sigmaPart L x = 1 := by
  simp only [sigmaPart]
  by_cases hconj : ∃ g : G, MulAut.conj g • M = L
  · obtain ⟨g, rfl⟩ := hconj
    exact Or.inl (piPart_self_of_isPiElement (fun p hp => by
      have : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
      exact OddOrder.BG.Ch3.S10.sigma_conj g (hx p hp)))
  · refine Or.inr (piPart_eq_one_of_isPiElement_compl (fun p hp hpL => ?_))
    exact Set.disjoint_left.mp (sigma_disjoint_of_nonconjugate hG hM hL hconj) (hx p hp) hpL

/-- **BG `Msigma_ell1`** (Coq BGsection14): a nonidentity element of `M_σ` has σ-length `1`.  As a
`σ(M)`-element, its σ-decomposition collapses to the single block `{x}`: every `σ(L)`-part is `x`
or `1` (`sigmaPart_eq_self_or_one_of_isPiElement_sigma`), and `sigmaPart M x = x ≠ 1`.  This is the
genuine form of the `ℓ_σ(x) = 1` property that the `SigmaDecompositionData` scaffold posits for
`x ∈ M_σ^#` (`length_one_of_isPiElement_sigma`). -/
theorem Msigma_ell1 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) {x : G} (hx : x ∈ OddOrder.BG.Ch3.S10.Msigma M) (hx1 : x ≠ 1) :
    sigmaLength x = 1 := by
  have hxσ : IsPiElement (OddOrder.BG.Ch3.S10.sigma M) x := isPiElement_sigma_of_mem_Msigma hx
  have hself : sigmaPart M x = x := piPart_self_of_isPiElement hxσ
  have hset : sigmaDecomposition x = {x} := by
    refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨⟨M, hM, hself.symm⟩, ?_⟩, ?_⟩
    · simp only [Set.mem_singleton_iff]; exact hx1
    · rintro y ⟨⟨L, hL, rfl⟩, hy⟩
      rcases sigmaPart_eq_self_or_one_of_isPiElement_sigma hG hM hxσ hL with h | h
      · exact h
      · exact absurd (Set.mem_singleton_iff.mpr h) hy
  rw [sigmaLength, hset, Set.ncard_singleton]

/-- A named carrier for the sigma-decomposition / sigma-length data of BG §14.

The actual construction comes from Theorem 13.9 and the Hall decomposition of
finite groups.  Keeping it as explicit data avoids a false placeholder
`def sigmaLength := 0` while still letting §§15--16 state their dependencies. -/
structure SigmaDecompositionData (G : Type*) [Group G] where
  length : G → ℕ
  length_one_iff : ∀ x : G,
    length x = 1 ↔ x ≠ 1 ∧ (maximalSigmaSubgroupsOfElement x).Nonempty

end OddOrder.BG.Ch4.S14


