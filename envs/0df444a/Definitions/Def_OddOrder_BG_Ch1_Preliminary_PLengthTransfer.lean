-- Prove2me | Definitions.Def_OddOrder_BG_Ch1_Preliminary_PLengthTransfer
-- name    : OddOrder_BG_Ch1_Preliminary_PLengthTransfer
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:06:56.751553+00:00
-- url     : https://prove2.me/theorems/30ba7034-6b32-49cb-b16a-6c38992c4f29
-- title:
--   BG Lemma 1.21: transfer lemmas for $p$-length one (foundation)
-- statement:
--   Foundation for Lemma 1.21 of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, §1, the transfer lemmas for `hasPLengthOne`. It proves that $G/O_{p',p}(G)\cong (G/O_{p'}(G))/O_p(\cdot)$ by a third isomorphism theorem argument, giving the common starting point for parts (a)–(e), which are used downstream in the reductions for BG Theorem 3.6 and Theorem 10.6.
--
--   The main declaration: `quotientProd_mulEquiv` (Quotient of a product by a product subgroup splits: `(A × B) / (H ×' K) ≃* (A/H) × (B/K)`).
--
--   The bundle also proves 19 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch1_Preliminary/PLengthTransfer.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch1_Preliminary/PLengthTransfer.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_PLength

namespace OddOrder.BG.Ch1

open OddOrder.Isaacs

variable {p : ℕ}

/-- **Bridge** (third isomorphism): `|G / O_{p',p}(G)| = |(G/O_{p'}(G)) / O_p(G/O_{p'}(G))|`.
`O_{p',p}(G)` is by definition the preimage of `O_p(G/O_{p'}(G))` under `G → G/O_{p'}(G)`, so the
two quotients are isomorphic. This is the computational form of `hasPLengthOne` used to derive the
Lemma 1.21 transfer lemmas. -/
theorem card_quotient_oPiPrimePiCore_eq (G : Type*) [Group G] [Finite G] :
    Nat.card (G ⧸ Ch03.oPiPrimePiCore ({p} : Set ℕ) G) =
      Nat.card ((G ⧸ Ch03.oPiCore (({p} : Set ℕ)ᶜ) G) ⧸
        Ch03.oPiCore ({p} : Set ℕ) (G ⧸ Ch03.oPiCore (({p} : Set ℕ)ᶜ) G)) := by
  classical
  set K : Subgroup G := Ch03.oPiCore (({p} : Set ℕ)ᶜ) G with hK
  set q : G →* G ⧸ K := QuotientGroup.mk' K with hq
  have hsurj : Function.Surjective q := QuotientGroup.mk'_surjective K
  have hKle : K ≤ Ch03.oPiPrimePiCore ({p} : Set ℕ) G :=
    Ch03.oPiCore_compl_le_oPiPrimePiCore ({p} : Set ℕ) G
  -- `(O_{p',p}(G)).map q = O_p(G/K)` since `O_{p',p}(G) = comap q (O_p(G/K))` and `q` surjective.
  have hmap : (Ch03.oPiPrimePiCore ({p} : Set ℕ) G).map q
      = Ch03.oPiCore ({p} : Set ℕ) (G ⧸ K) := by
    rw [hq]
    exact Subgroup.map_comap_eq_self_of_surjective hsurj _
  refine Nat.card_congr ?_
  rw [← hmap]
  exact (QuotientGroup.quotientQuotientEquivQuotient K _ hKle).toEquiv.symm

/-- `hasPLengthOne` rephrased via the bridge: `G` has `p`-length one iff the `p`-core
`O_p(G/O_{p'}(G))` contains a full Sylow `p`-subgroup of `G/O_{p'}(G)` (its quotient is `p'`). -/
theorem hasPLengthOne_iff_card_quotient (G : Type*) [Group G] [Finite G] :
    hasPLengthOne p G ↔
      ¬ p ∣ Nat.card ((G ⧸ Ch03.oPiCore (({p} : Set ℕ)ᶜ) G) ⧸
        Ch03.oPiCore ({p} : Set ℕ) (G ⧸ Ch03.oPiCore (({p} : Set ℕ)ᶜ) G)) := by
  rw [hasPLengthOne, card_quotient_oPiPrimePiCore_eq G]

/-- The `π`-core commutes with quotient by a normal `π`-subgroup:
`O_π(G/H) = O_π(G) / H` when `H ⊴ G` is a `π`-subgroup. (The reusable engine for the
Lemma 1.21 transfer lemmas: (b) uses `π = {p}ᶜ`, (c) uses `π = {p}`.) -/
theorem oPiCore_quotient_eq_of_isPiGroup {G : Type*} [Group G] [Finite G] (π : Set ℕ)
    {H : Subgroup G} [H.Normal] (hπH : Ch03.Subgroup.IsPiGroup π H) :
    Ch03.oPiCore π (G ⧸ H) = (Ch03.oPiCore π G).map (QuotientGroup.mk' H) := by
  classical
  set q : G →* G ⧸ H := QuotientGroup.mk' H with hq
  have hsurj : Function.Surjective q := QuotientGroup.mk'_surjective H
  refine le_antisymm ?_ (Ch03.oPiCore.map_le_of_surjective _ q hsurj)
  set Kbar : Subgroup (G ⧸ H) := Ch03.oPiCore π (G ⧸ H) with hKbar
  have hKbarN : Kbar.Normal := by rw [hKbar]; infer_instance
  set N : Subgroup G := Kbar.comap q with hN
  have hNnormal : N.Normal := by rw [hN]; infer_instance
  have hKbar_pi : Ch03.Subgroup.IsPiGroup π Kbar := by rw [hKbar]; exact Ch03.oPiCore.isPiGroup _
  -- `|N| = |H| · |Kbar|` (the restriction `q : N → Kbar` is onto with kernel `H`).
  have hidx : N.index = Kbar.index := by
    rw [hN]; exact Subgroup.index_comap_of_surjective Kbar hsurj
  have hKpos : 0 < Kbar.index := Nat.card_pos
  have hcardN : Nat.card N = Nat.card H * Nat.card Kbar := by
    have key : Nat.card N * Kbar.index = (Nat.card H * Nat.card Kbar) * Kbar.index :=
      calc Nat.card N * Kbar.index = Nat.card N * N.index := by rw [hidx]
        _ = Nat.card G := Subgroup.card_mul_index N
        _ = Nat.card H * Nat.card (G ⧸ H) := (Subgroup.card_mul_index H).symm
        _ = Nat.card H * (Nat.card Kbar * Kbar.index) := by
              rw [← Subgroup.card_mul_index Kbar]
        _ = (Nat.card H * Nat.card Kbar) * Kbar.index := by ring
    exact Nat.eq_of_mul_eq_mul_right hKpos key
  -- `N` is a `π`-group: `π(|N|) = π(|H|) ∪ π(|Kbar|) ⊆ π`.
  have hNpi : Ch03.Subgroup.IsPiGroup π N := by
    intro r hr
    rw [hcardN, Nat.primeFactors_mul Nat.card_pos.ne' Nat.card_pos.ne'] at hr
    rcases Finset.mem_union.mp hr with h | h
    · exact hπH r h
    · exact hKbar_pi r h
  have hNle : N ≤ Ch03.oPiCore π G := Ch03.Subgroup.IsPiGroup.le_oPiCore hNpi
  have hKN : Kbar = N.map q := (Subgroup.map_comap_eq_self_of_surjective hsurj Kbar).symm
  rw [hKN]; exact Subgroup.map_mono hNle

/-- A normal subgroup with order prime to `p` is a `{p}ᶜ`-group. -/
private theorem isPiGroup_compl_of_not_dvd {G : Type*} [Group G] {H : Subgroup G}
    (hHp' : ¬ p ∣ Nat.card H) : Ch03.Subgroup.IsPiGroup (({p} : Set ℕ)ᶜ) H := by
  intro r hr
  have hrp : r ≠ p := fun h => hHp' (h ▸ Nat.dvd_of_mem_primeFactors hr)
  simpa using hrp

/-- **BG Lemma 1.21(b)** (mmd L567): if `H ⊴ G` is a normal `p'`-subgroup and `G/H` has
`p`-length one, then `G` has `p`-length one. -/
theorem hasPLengthOne_of_isPiPrime_normal_quotient [Fact p.Prime] {G : Type*} [Group G]
    [Finite G] {H : Subgroup G} [H.Normal] (hHp' : ¬ p ∣ Nat.card H)
    (hquot : hasPLengthOne p (G ⧸ H)) : hasPLengthOne p G := by
  classical
  rw [hasPLengthOne_iff_card_quotient] at hquot ⊢
  have hHle : H ≤ Ch03.oPiCore (({p} : Set ℕ)ᶜ) G :=
    Ch03.Subgroup.IsPiGroup.le_oPiCore (isPiGroup_compl_of_not_dvd hHp')
  have hcorr : Ch03.oPiCore (({p} : Set ℕ)ᶜ) (G ⧸ H)
      = (Ch03.oPiCore (({p} : Set ℕ)ᶜ) G).map (QuotientGroup.mk' H) :=
    oPiCore_quotient_eq_of_isPiGroup _ (isPiGroup_compl_of_not_dvd hHp')
  have hmapN : ((Ch03.oPiCore (({p} : Set ℕ)ᶜ) G).map (QuotientGroup.mk' H)).Normal :=
    Subgroup.Normal.map inferInstance (QuotientGroup.mk' H) (QuotientGroup.mk'_surjective H)
  -- `φ : (G/H)/O_{p'}(G/H) ≃* G/O_{p'}(G)`.
  have φ : ((G ⧸ H) ⧸ Ch03.oPiCore (({p} : Set ℕ)ᶜ) (G ⧸ H)) ≃*
      (G ⧸ Ch03.oPiCore (({p} : Set ℕ)ᶜ) G) :=
    (QuotientGroup.quotientMulEquivOfEq hcorr).trans
      (QuotientGroup.quotientQuotientEquivQuotient H _ hHle)
  -- `O_p` commutes with `φ`, so the `O_p`-quotient indices match.
  have hOp : (Ch03.oPiCore ({p} : Set ℕ)
        ((G ⧸ H) ⧸ Ch03.oPiCore (({p} : Set ℕ)ᶜ) (G ⧸ H))).map φ
      = Ch03.oPiCore ({p} : Set ℕ) (G ⧸ Ch03.oPiCore (({p} : Set ℕ)ᶜ) G) :=
    Ch03.oPiCore.map_eq_of_mulEquiv ({p} : Set ℕ) φ
  have hcard_quot :
      Nat.card ((G ⧸ Ch03.oPiCore (({p} : Set ℕ)ᶜ) G) ⧸
          Ch03.oPiCore ({p} : Set ℕ) (G ⧸ Ch03.oPiCore (({p} : Set ℕ)ᶜ) G))
        = Nat.card (((G ⧸ H) ⧸ Ch03.oPiCore (({p} : Set ℕ)ᶜ) (G ⧸ H)) ⧸
          Ch03.oPiCore ({p} : Set ℕ) ((G ⧸ H) ⧸ Ch03.oPiCore (({p} : Set ℕ)ᶜ) (G ⧸ H))) := by
    change (Ch03.oPiCore ({p} : Set ℕ) (G ⧸ Ch03.oPiCore (({p} : Set ℕ)ᶜ) G)).index
        = (Ch03.oPiCore ({p} : Set ℕ)
            ((G ⧸ H) ⧸ Ch03.oPiCore (({p} : Set ℕ)ᶜ) (G ⧸ H))).index
    rw [← hOp]
    exact Subgroup.index_map_equiv _ φ
  rw [hcard_quot]; exact hquot

/-- When `O_{p'}(G) = ⊥`, the `p`-length-one core simplifies: `O_{p',p}(G) = O_p(G)`. -/
theorem oPiPrimePiCore_eq_oPiCore_of_compl_bot {G : Type*} [Group G] [Finite G]
    (h : Ch03.oPiCore (({p} : Set ℕ)ᶜ) G = ⊥) :
    Ch03.oPiPrimePiCore ({p} : Set ℕ) G = Ch03.oPiCore ({p} : Set ℕ) G := by
  have key : ∀ (M : Subgroup G) [M.Normal], M = ⊥ →
      Subgroup.comap (QuotientGroup.mk' M) (Ch03.oPiCore ({p} : Set ℕ) (G ⧸ M))
        = Ch03.oPiCore ({p} : Set ℕ) G := by
    intro M _ hM
    subst hM
    rw [show (QuotientGroup.mk' (⊥ : Subgroup G))
        = (QuotientGroup.quotientBot (G := G)).symm.toMonoidHom from rfl]
    rw [Subgroup.comap_equiv_eq_map_symm']
    simp only [MulEquiv.symm_symm]
    exact Ch03.oPiCore.map_eq_of_mulEquiv ({p} : Set ℕ) (QuotientGroup.quotientBot (G := G))
  exact key _ h

/-- A normal `p`-subgroup is a `{p}`-group. -/
private theorem isPiGroup_singleton_of_isPGroup [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    {H : Subgroup G} (hHp : IsPGroup p ↥H) : Ch03.Subgroup.IsPiGroup ({p} : Set ℕ) H := by
  intro r hr
  have hrp : r.Prime := Nat.prime_of_mem_primeFactors hr
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hHp
  have hrdvd : r ∣ p ^ k := hk ▸ Nat.dvd_of_mem_primeFactors hr
  exact (Nat.prime_dvd_prime_iff_eq hrp Fact.out).mp (hrp.prime.dvd_of_dvd_pow hrdvd)

/-- **BG Lemma 1.21(c)** (mmd L568): if `H ⊴ G` is a normal `p`-subgroup with `O_{p'}(G/H) = 1`
and `G/H` has `p`-length one, then `G` has `p`-length one. -/
theorem hasPLengthOne_of_isPGroup_normal_quotient [Fact p.Prime] {G : Type*} [Group G]
    [Finite G] {H : Subgroup G} [H.Normal] (hHp : IsPGroup p ↥H)
    (hOp' : Ch03.oPiCore (({p} : Set ℕ)ᶜ) (G ⧸ H) = ⊥)
    (hquot : hasPLengthOne p (G ⧸ H)) : hasPLengthOne p G := by
  classical
  -- `O_{p'}(G) ≤ H` (it maps into `O_{p'}(G/H) = ⊥`), and being `≤ H` it is a `p`-group; also
  -- a `{p}ᶜ`-group, hence trivial.
  have hOp'G : Ch03.oPiCore (({p} : Set ℕ)ᶜ) G = ⊥ := by
    have hle : Ch03.oPiCore (({p} : Set ℕ)ᶜ) G ≤ H := by
      have h1 : (Ch03.oPiCore (({p} : Set ℕ)ᶜ) G).map (QuotientGroup.mk' H)
          ≤ Ch03.oPiCore (({p} : Set ℕ)ᶜ) (G ⧸ H) :=
        Ch03.oPiCore.map_le_of_surjective _ _ (QuotientGroup.mk'_surjective H)
      rw [hOp', le_bot_iff, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h1
      exact h1
    have hpgroup : IsPGroup p ↥(Ch03.oPiCore (({p} : Set ℕ)ᶜ) G) :=
      hHp.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
    have hp_ndvd : ¬ p ∣ Nat.card ↥(Ch03.oPiCore (({p} : Set ℕ)ᶜ) G) := fun hd =>
      (Ch03.oPiCore.isPiGroup _ p (Nat.mem_primeFactors.mpr ⟨Fact.out, hd, Nat.card_pos.ne'⟩))
        (Set.mem_singleton p)
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hpgroup
    have hk0 : k = 0 := by by_contra hk0; exact hp_ndvd (hk ▸ dvd_pow_self p hk0)
    exact Subgroup.card_eq_one.mp (by rw [hk, hk0, pow_zero])
  -- Reduce both sides to `O_p`-quotients via `O_{p',p} = O_p` (since `O_{p'} = ⊥`).
  rw [hasPLengthOne, oPiPrimePiCore_eq_oPiCore_of_compl_bot hOp'G]
  rw [hasPLengthOne, oPiPrimePiCore_eq_oPiCore_of_compl_bot hOp'] at hquot
  -- `H ≤ O_p(G)` and `O_p(G/H) = O_p(G).map mk'`, so `(G/H)/O_p(G/H) ≃* G/O_p(G)`.
  have hHpi : Ch03.Subgroup.IsPiGroup ({p} : Set ℕ) H := isPiGroup_singleton_of_isPGroup hHp
  have hHleOp : H ≤ Ch03.oPiCore ({p} : Set ℕ) G := Ch03.Subgroup.IsPiGroup.le_oPiCore hHpi
  have hcorr : Ch03.oPiCore ({p} : Set ℕ) (G ⧸ H)
      = (Ch03.oPiCore ({p} : Set ℕ) G).map (QuotientGroup.mk' H) :=
    oPiCore_quotient_eq_of_isPiGroup _ hHpi
  have hmapN : ((Ch03.oPiCore ({p} : Set ℕ) G).map (QuotientGroup.mk' H)).Normal :=
    Subgroup.Normal.map inferInstance (QuotientGroup.mk' H) (QuotientGroup.mk'_surjective H)
  have φ : ((G ⧸ H) ⧸ Ch03.oPiCore ({p} : Set ℕ) (G ⧸ H)) ≃*
      (G ⧸ Ch03.oPiCore ({p} : Set ℕ) G) :=
    (QuotientGroup.quotientMulEquivOfEq hcorr).trans
      (QuotientGroup.quotientQuotientEquivQuotient H _ hHleOp)
  rw [(Nat.card_congr φ.toEquiv).symm]
  exact hquot

/-- If `K ⊴ G` has `p`-group image in `G/O_{p'}(G)`, then `K ≤ O_{p',p}(G)`. (The `≤ O_{p',p}`
half used for subgroup monotonicity Lemma 1.21(a): the image is a normal `p`-subgroup of
`G/O_{p'}(G)`, hence lies in `O_p(G/O_{p'}(G))`, whose preimage is `O_{p',p}(G)`.) -/
theorem le_oPiPrimePiCore_of_quotient_isPGroup [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    {K : Subgroup G} [K.Normal]
    (hK : IsPGroup p ↥(K.map (QuotientGroup.mk' (Ch03.oPiCore (({p} : Set ℕ)ᶜ) G)))) :
    K ≤ Ch03.oPiPrimePiCore ({p} : Set ℕ) G := by
  classical
  set Op' : Subgroup G := Ch03.oPiCore (({p} : Set ℕ)ᶜ) G with hOp'
  have : (K.map (QuotientGroup.mk' Op')).Normal :=
    Subgroup.Normal.map inferInstance (QuotientGroup.mk' Op') (QuotientGroup.mk'_surjective Op')
  have hle : K.map (QuotientGroup.mk' Op') ≤ Ch03.oPiCore ({p} : Set ℕ) (G ⧸ Op') :=
    Ch03.Subgroup.IsPiGroup.le_oPiCore (isPiGroup_singleton_of_isPGroup hK)
  exact Subgroup.map_le_iff_le_comap.mp hle

/-- The image of `O_{p',p}(G)` in `G/O_{p'}(G)` is a `p`-group — it is exactly `O_p(G/O_{p'}(G))`.
(Building block for Lemma 1.21(a): `O_{p',p}(G)/O_{p'}(G)` is a `p`-group.) -/
theorem isPGroup_map_oPiPrimePiCore [Fact p.Prime] {G : Type*} [Group G] [Finite G] :
    IsPGroup p ↥((Ch03.oPiPrimePiCore ({p} : Set ℕ) G).map
      (QuotientGroup.mk' (Ch03.oPiCore (({p} : Set ℕ)ᶜ) G))) := by
  have heq : (Ch03.oPiPrimePiCore ({p} : Set ℕ) G).map
        (QuotientGroup.mk' (Ch03.oPiCore (({p} : Set ℕ)ᶜ) G))
      = Ch03.oPiCore ({p} : Set ℕ) (G ⧸ Ch03.oPiCore (({p} : Set ℕ)ᶜ) G) :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _
  rw [heq]
  exact IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne'
    (fun {d} hd hdvd => Set.mem_singleton_iff.mp
      (Ch03.oPiCore.isPiGroup ({p} : Set ℕ) d
        (Nat.mem_primeFactors.mpr ⟨hd, hdvd, Nat.card_pos.ne'⟩))))

/-- `O_{p'}(G) ∩ H` lands in `O_{p'}(↥H)` — it is a normal `{p}ᶜ`-subgroup of `↥H`.
(Building block for Lemma 1.21(a).) -/
theorem oPiCore_compl_subgroupOf_le [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    {H : Subgroup G} :
    (Ch03.oPiCore (({p} : Set ℕ)ᶜ) G).subgroupOf H
      ≤ Ch03.oPiCore (({p} : Set ℕ)ᶜ) ↥H := by
  have : ((Ch03.oPiCore (({p} : Set ℕ)ᶜ) G).subgroupOf H).Normal :=
    Subgroup.Normal.comap inferInstance H.subtype
  refine Ch03.Subgroup.IsPiGroup.le_oPiCore ?_
  intro r hr
  have hcard : Nat.card ↥((Ch03.oPiCore (({p} : Set ℕ)ᶜ) G).subgroupOf H)
      ∣ Nat.card ↥(Ch03.oPiCore (({p} : Set ℕ)ᶜ) G) := by
    rw [← Subgroup.card_map_of_injective H.subtype_injective,
      Subgroup.subgroupOf_map_subtype]
    exact Subgroup.card_dvd_of_le inf_le_left
  exact Ch03.oPiCore.isPiGroup (({p} : Set ℕ)ᶜ) r
    (Nat.primeFactors_mono hcard Nat.card_pos.ne' hr)

/-- The image of `O_{p',p}(G) ⊓ H` in `G/O_{p'}(G)` is a `p`-group (it sits inside the
`p`-group `O_{p',p}(G).map mk'`). Building block for Lemma 1.21(a). -/
theorem isPGroup_inf_map_oPiPrimePiCore [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    {H : Subgroup G} :
    IsPGroup p ↥((Ch03.oPiPrimePiCore ({p} : Set ℕ) G ⊓ H).map
      (QuotientGroup.mk' (Ch03.oPiCore (({p} : Set ℕ)ᶜ) G))) := by
  have hle : (Ch03.oPiPrimePiCore ({p} : Set ℕ) G ⊓ H).map
        (QuotientGroup.mk' (Ch03.oPiCore (({p} : Set ℕ)ᶜ) G))
      ≤ (Ch03.oPiPrimePiCore ({p} : Set ℕ) G).map
        (QuotientGroup.mk' (Ch03.oPiCore (({p} : Set ℕ)ᶜ) G)) :=
    Subgroup.map_mono inf_le_left
  exact isPGroup_map_oPiPrimePiCore.of_injective
    (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)

/-- **Crux of Lemma 1.21(a)**: `O_{p',p}(G) ∩ H ≤ O_{p',p}(↥H)` (as a subgroup of `↥H`).
Both the `G/O_{p'}(G)`-image and the `↥H/O_{p'}(↥H)`-image of `A := O_{p',p}(G) ⊓ H` are
quotients of `↥A`; the former is a `p`-group and has the smaller kernel
(`O_{p'}(G)∩H ≤ O_{p'}(↥H)`), so the latter — which is `K.map mk'` — has order dividing it,
hence is a `p`-group; `le_oPiPrimePiCore_of_quotient_isPGroup` finishes. -/
theorem oPiPrimePiCore_subgroupOf_le [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    {H : Subgroup G} :
    (Ch03.oPiPrimePiCore ({p} : Set ℕ) G).subgroupOf H
      ≤ Ch03.oPiPrimePiCore ({p} : Set ℕ) ↥H := by
  classical
  have hKnorm : ((Ch03.oPiPrimePiCore ({p} : Set ℕ) G).subgroupOf H).Normal :=
    Subgroup.Normal.comap inferInstance H.subtype
  apply le_oPiPrimePiCore_of_quotient_isPGroup
  set A : Subgroup G := Ch03.oPiPrimePiCore ({p} : Set ℕ) G ⊓ H with hAdef
  have hAH : A ≤ H := inf_le_right
  set gA : ↥A →* G ⧸ Ch03.oPiCore (({p} : Set ℕ)ᶜ) G :=
    (QuotientGroup.mk' (Ch03.oPiCore (({p} : Set ℕ)ᶜ) G)).comp A.subtype with hgA
  set fA : ↥A →* ↥H ⧸ Ch03.oPiCore (({p} : Set ℕ)ᶜ) ↥H :=
    (QuotientGroup.mk' (Ch03.oPiCore (({p} : Set ℕ)ᶜ) ↥H)).comp (Subgroup.inclusion hAH) with hfA
  -- `range gA = A.map mk'` is a `p`-group.
  have hgA_range : gA.range = A.map (QuotientGroup.mk' (Ch03.oPiCore (({p} : Set ℕ)ᶜ) G)) := by
    rw [hgA, MonoidHom.range_comp, Subgroup.range_subtype]
  have hgA_pg : IsPGroup p ↥gA.range := by rw [hgA_range]; exact isPGroup_inf_map_oPiPrimePiCore
  -- `range fA = K.map mk'` (the goal's subject).
  have hfA_range : fA.range
      = ((Ch03.oPiPrimePiCore ({p} : Set ℕ) G).subgroupOf H).map
          (QuotientGroup.mk' (Ch03.oPiCore (({p} : Set ℕ)ᶜ) ↥H)) := by
    rw [hfA, MonoidHom.range_comp, Subgroup.inclusion_range, hAdef,
      Subgroup.inf_subgroupOf_right]
  -- `ker gA ≤ ker fA`.
  have hker_le : gA.ker ≤ fA.ker := by
    intro a ha
    rw [hgA, MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at ha
    rw [hfA, MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    apply oPiCore_compl_subgroupOf_le
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_inclusion]
    exact ha
  -- `|range fA| ∣ |range gA|` (= p-power), so `range fA` is a `p`-group.
  rw [← hfA_range]
  have hcard_dvd : Nat.card ↥fA.range ∣ Nat.card ↥gA.range := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange fA).toEquiv,
      ← Nat.card_congr (QuotientGroup.quotientKerEquivRange gA).toEquiv]
    exact Subgroup.index_dvd_of_le hker_le
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hgA_pg
  rw [hn] at hcard_dvd
  obtain ⟨m, _, hm⟩ := (Nat.dvd_prime_pow Fact.out).mp hcard_dvd
  exact IsPGroup.of_card hm

/-- **BG Lemma 1.21(a)** (mmd L566): `p`-length one passes to subgroups — if `G` has
`p`-length one and `H ≤ G`, then `H` has `p`-length one. Index chain:
`[↥H : O_{p',p}(↥H)] ∣ [↥H : (O_{p',p}(G)).subgroupOf H] = (O_{p',p}(G)).relIndex H ∣
[G : O_{p',p}(G)]` (the last step uses `O_{p',p}(G) ◁ G`). -/
theorem hasPLengthOne_subgroup [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    (hpl : hasPLengthOne p G) (H : Subgroup G) : hasPLengthOne p ↥H := by
  rw [hasPLengthOne] at hpl ⊢
  have hchain : (Ch03.oPiPrimePiCore ({p} : Set ℕ) ↥H).index
      ∣ (Ch03.oPiPrimePiCore ({p} : Set ℕ) G).index :=
    dvd_trans (Subgroup.index_dvd_of_le oPiPrimePiCore_subgroupOf_le)
      (Subgroup.relIndex_dvd_index_of_normal (Ch03.oPiPrimePiCore ({p} : Set ℕ) G) H)
  exact fun hdvd => hpl (dvd_trans hdvd hchain)

/-- The `π`-core of a product is the product of the `π`-cores. -/
theorem oPiCore_prod {A B : Type*} [Group A] [Group B] [Finite A] [Finite B] (π : Set ℕ) :
    Ch03.oPiCore π (A × B) = (Ch03.oPiCore π A).prod (Ch03.oPiCore π B) := by
  classical
  have hfst : Function.Surjective (MonoidHom.fst A B) := fun a => ⟨(a, 1), rfl⟩
  have hsnd : Function.Surjective (MonoidHom.snd A B) := fun b => ⟨(1, b), rfl⟩
  refine le_antisymm ?_ ?_
  · rw [Subgroup.le_prod_iff]
    refine ⟨?_, ?_⟩
    · have : ((Ch03.oPiCore π (A × B)).map (MonoidHom.fst A B)).Normal :=
        Subgroup.Normal.map inferInstance (MonoidHom.fst A B) hfst
      refine Ch03.Subgroup.IsPiGroup.le_oPiCore (fun r hr => ?_)
      exact Ch03.oPiCore.isPiGroup π r
        (Nat.primeFactors_mono (Subgroup.card_map_dvd _ _) Nat.card_pos.ne' hr)
    · have : ((Ch03.oPiCore π (A × B)).map (MonoidHom.snd A B)).Normal :=
        Subgroup.Normal.map inferInstance (MonoidHom.snd A B) hsnd
      refine Ch03.Subgroup.IsPiGroup.le_oPiCore (fun r hr => ?_)
      exact Ch03.oPiCore.isPiGroup π r
        (Nat.primeFactors_mono (Subgroup.card_map_dvd _ _) Nat.card_pos.ne' hr)
  · refine Ch03.Subgroup.IsPiGroup.le_oPiCore (fun r hr => ?_)
    rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod,
      Nat.primeFactors_mul Nat.card_pos.ne' Nat.card_pos.ne'] at hr
    rcases Finset.mem_union.mp hr with h | h
    · exact Ch03.oPiCore.isPiGroup π r h
    · exact Ch03.oPiCore.isPiGroup π r h

/-- `hasPLengthOne` is invariant under group isomorphism. Transport the double quotient
`(G/O_{p'}(G)) / O_p(G/O_{p'}(G))` of the bridge `hasPLengthOne_iff_card_quotient` across `e`
in two stages: `O_{p'}` and then `O_p`, each via `QuotientGroup.congr` +
`oPiCore.map_eq_of_mulEquiv`. -/
theorem hasPLengthOne_of_mulEquiv [Fact p.Prime] {G G' : Type*} [Group G] [Finite G]
    [Group G'] [Finite G'] (e : G ≃* G') (h : hasPLengthOne p G) : hasPLengthOne p G' := by
  rw [hasPLengthOne_iff_card_quotient] at h ⊢
  have hmapN : (Ch03.oPiCore (({p} : Set ℕ)ᶜ) G).map e = Ch03.oPiCore (({p} : Set ℕ)ᶜ) G' :=
    Ch03.oPiCore.map_eq_of_mulEquiv _ e
  -- descending iso on the `O_{p'}`-quotient
  let ē := QuotientGroup.congr _ _ e hmapN
  have hmapO : (Ch03.oPiCore ({p} : Set ℕ) (G ⧸ Ch03.oPiCore (({p} : Set ℕ)ᶜ) G)).map ē
      = Ch03.oPiCore ({p} : Set ℕ) (G' ⧸ Ch03.oPiCore (({p} : Set ℕ)ᶜ) G') :=
    Ch03.oPiCore.map_eq_of_mulEquiv _ ē
  -- descending iso on the `O_p`-quotient gives the double-quotient iso
  rw [← Nat.card_congr (QuotientGroup.congr _ _ ē hmapO).toEquiv]
  exact h

/-- Quotient of a product by a product subgroup splits: `(A × B) / (H ×' K) ≃* (A/H) × (B/K)`.
(`prodMap (mk' H) (mk' K)` is surjective with kernel `H ×' K`.) -/
noncomputable def quotientProd_mulEquiv {A B : Type*} [Group A] [Group B]
    (H : Subgroup A) [H.Normal] (K : Subgroup B) [K.Normal] :
    (A × B) ⧸ H.prod K ≃* (A ⧸ H) × (B ⧸ K) := by
  have hker : ((QuotientGroup.mk' H).prodMap (QuotientGroup.mk' K)).ker = H.prod K := by
    rw [MonoidHom.ker_prodMap, QuotientGroup.ker_mk', QuotientGroup.ker_mk']
  have hsurj : Function.Surjective ⇑((QuotientGroup.mk' H).prodMap (QuotientGroup.mk' K)) := by
    rw [MonoidHom.coe_prodMap]
    exact (QuotientGroup.mk'_surjective H).prodMap (QuotientGroup.mk'_surjective K)
  exact (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ hsurj)

/-- **Lemma 1.21(e) product step**: `p`-length one is closed under direct products.
The double quotient `((A×B)/O_{p'}) / O_p` splits as a product (via `oPiCore_prod` at both
`O_{p'}` and `O_p` levels, plus `quotientProd_mulEquiv`), so its order is the product of the
two factors' double-quotient orders; `p` prime divides neither. -/
theorem hasPLengthOne_prod [Fact p.Prime] {A B : Type*} [Group A] [Finite A] [Group B] [Finite B]
    (hA : hasPLengthOne p A) (hB : hasPLengthOne p B) : hasPLengthOne p (A × B) := by
  rw [hasPLengthOne_iff_card_quotient] at hA hB ⊢
  -- `(A×B)/O_{p'}(A×B) ≃* (A/O_{p'}A) × (B/O_{p'}B)`
  have e1 : (A × B) ⧸ Ch03.oPiCore (({p} : Set ℕ)ᶜ) (A × B) ≃*
      (A ⧸ Ch03.oPiCore (({p} : Set ℕ)ᶜ) A) × (B ⧸ Ch03.oPiCore (({p} : Set ℕ)ᶜ) B) :=
    (QuotientGroup.quotientMulEquivOfEq (oPiCore_prod _)).trans (quotientProd_mulEquiv _ _)
  -- transport `O_p` across `e1`
  have hmapO : (Ch03.oPiCore ({p} : Set ℕ) ((A × B) ⧸ Ch03.oPiCore (({p} : Set ℕ)ᶜ) (A × B))).map e1
      = Ch03.oPiCore ({p} : Set ℕ)
          ((A ⧸ Ch03.oPiCore (({p} : Set ℕ)ᶜ) A) × (B ⧸ Ch03.oPiCore (({p} : Set ℕ)ᶜ) B)) :=
    Ch03.oPiCore.map_eq_of_mulEquiv _ e1
  -- the double-quotient splits: `DQ(A×B) ≃* DQ(A) × DQ(B)`
  let Φ := (QuotientGroup.congr _ _ e1 hmapO).trans
    ((QuotientGroup.quotientMulEquivOfEq (oPiCore_prod ({p} : Set ℕ))).trans
      (quotientProd_mulEquiv _ _))
  rw [Nat.card_congr Φ.toEquiv, Nat.card_prod]
  exact fun hd => ((Nat.Prime.dvd_mul Fact.out).mp hd).elim hA hB

/-- **BG Lemma 1.21(e)** (mmd L570): if `H, N ⊴ G` with `H ∩ N = 1` and both `G/H` and `G/N`
have `p`-length one, then `G` has `p`-length one. Since `H ∩ N = 1`, the map
`G → (G/H) × (G/N)` is injective, embedding `G` as a subgroup of the product; the product is
`p`-length one (`hasPLengthOne_prod`), the subgroup inherits it (Lemma 1.21(a)), and the
embedding transfers it back to `G` (`hasPLengthOne_of_mulEquiv`). -/
theorem hasPLengthOne_of_inf_eq_bot [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    {H N : Subgroup G} [H.Normal] [N.Normal] (hHN : H ⊓ N = ⊥)
    (hH : hasPLengthOne p (G ⧸ H)) (hN : hasPLengthOne p (G ⧸ N)) : hasPLengthOne p G := by
  have hker : ((QuotientGroup.mk' H).prod (QuotientGroup.mk' N)).ker = ⊥ := by
    rw [MonoidHom.ker_prod, QuotientGroup.ker_mk', QuotientGroup.ker_mk']; exact hHN
  have hinj : Function.Injective ⇑((QuotientGroup.mk' H).prod (QuotientGroup.mk' N)) :=
    (MonoidHom.ker_eq_bot_iff _).mp hker
  have hrange : hasPLengthOne p ↥((QuotientGroup.mk' H).prod (QuotientGroup.mk' N)).range :=
    hasPLengthOne_subgroup (hasPLengthOne_prod hH hN) _
  exact hasPLengthOne_of_mulEquiv (MonoidHom.ofInjective hinj).symm hrange

/-- **`p`-length one lifts along `p'`-quotients** (the dual of BG Lemma 1.21(b); equivalently a
consequence of Lemma 1.21(d), since `Γ/N` a `p'`-group forces all `p`-elements of `Γ` into `N`):
if `N ⊴ Γ` with `Γ/N` a `p'`-group and `↥N` has `p`-length one, then `Γ` has `p`-length one.
BG uses this in the `r_p ≥ 3` branch of Theorem 10.6: `M_α ⊴ M` is a Hall `α(M)`-subgroup with
`p ∈ α(M)`, so `M/M_α` is a `p'`-group, and once `M_α` is shown to have `p`-length one, so does
`M`.

`W = O_{p',p}(↥N)` is characteristic in `↥N` (`oPiPrimePiCore` is a `comap` of characteristic
cores), so `K = W.map N.subtype ⊴ Γ`. The image of `K` in `Γ/O_{p'}(Γ)` is the image of the
`p`-group `W/O_{p'}(↥N)` under the quotient map induced by `N.subtype`, hence a `p`-group; by
`le_oPiPrimePiCore_of_quotient_isPGroup`, `K ≤ O_{p',p}(Γ)`. Finally
`[Γ : O_{p',p}(Γ)] ∣ [Γ : K]` and `[Γ : K] = [↥N : W] · [Γ : N]`, with `p` dividing neither
factor. -/
theorem hasPLengthOne_of_normal_pPrime_quotient [Fact p.Prime] {Γ : Type*} [Group Γ] [Finite Γ]
    {N : Subgroup Γ} [N.Normal] (hquot : ¬ p ∣ Nat.card (Γ ⧸ N))
    (hpl : hasPLengthOne p ↥N) : hasPLengthOne p Γ := by
  classical
  set Op'N : Subgroup ↥N := Ch03.oPiCore (({p} : Set ℕ)ᶜ) ↥N with hOp'N
  set Op'Γ : Subgroup Γ := Ch03.oPiCore (({p} : Set ℕ)ᶜ) Γ with hOp'Γ
  set W : Subgroup ↥N := Ch03.oPiPrimePiCore ({p} : Set ℕ) ↥N with hW
  -- `W` is characteristic in `↥N`, so `K = W.map N.subtype ⊴ Γ`.
  have hWchar : W.Characteristic :=
    Subgroup.Characteristic.comap_quotient_mk (Ch03.oPiCore.characteristic _ _)
  set K : Subgroup Γ := W.map N.subtype with hK
  -- Induced quotient map `ρ : ↥N/O_{p'}(↥N) → Γ/O_{p'}(Γ)`.
  have hOp'_le : Op'N ≤ Op'Γ.comap N.subtype := by
    rw [← Subgroup.map_le_iff_le_comap]
    have : (Op'N.map N.subtype).Normal := by rw [hOp'N]; infer_instance
    refine Ch03.Subgroup.IsPiGroup.le_oPiCore ?_
    intro r hr
    have hcard : Nat.card ↥(Op'N.map N.subtype) = Nat.card ↥Op'N :=
      Subgroup.card_map_of_injective N.subtype_injective
    rw [hcard] at hr
    exact Ch03.oPiCore.isPiGroup _ r hr
  set ρ : (↥N ⧸ Op'N) →* (Γ ⧸ Op'Γ) := QuotientGroup.map Op'N Op'Γ N.subtype hOp'_le with hρ
  -- `K.map (mk' Op'Γ) = A.map ρ` where `A = W.map (mk' Op'N)` is a `p`-group.
  have hAp : IsPGroup p ↥(W.map (QuotientGroup.mk' Op'N)) := isPGroup_map_oPiPrimePiCore
  have himg_eq : K.map (QuotientGroup.mk' Op'Γ)
      = (W.map (QuotientGroup.mk' Op'N)).map ρ := by
    rw [hK, Subgroup.map_map, Subgroup.map_map]
    congr 1
  have himg_pg : IsPGroup p ↥(K.map (QuotientGroup.mk' Op'Γ)) := by
    rw [himg_eq]; exact hAp.map ρ
  have hKle : K ≤ Ch03.oPiPrimePiCore ({p} : Set ℕ) Γ :=
    le_oPiPrimePiCore_of_quotient_isPGroup himg_pg
  -- Index bookkeeping: `[Γ : O_{p',p}(Γ)] ∣ [Γ : K] = [↥N : W] · [Γ : N]`.
  have hKN : K ≤ N := hK ▸ Subgroup.map_subtype_le W
  have hsub : K.subgroupOf N = W := by
    rw [hK, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective N.subtype_injective]
  have hrelW : K.relIndex N = W.index := by rw [Subgroup.relIndex, hsub]
  have hKidx : K.index = W.index * N.index := by
    rw [← hrelW, Subgroup.relIndex_mul_index hKN]
  have hpW : ¬ p ∣ W.index := by rw [hasPLengthOne] at hpl; exact hpl
  have hpN : ¬ p ∣ N.index := hquot
  have hpK : ¬ p ∣ K.index := by
    rw [hKidx]; exact fun hd => (Nat.Prime.dvd_mul Fact.out).mp hd |>.elim hpW hpN
  exact fun hd => hpK (dvd_trans hd (Subgroup.index_dvd_of_le hKle))

end OddOrder.BG.Ch1


