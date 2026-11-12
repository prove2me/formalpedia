-- Prove2me | Definitions.Def_OddOrder_BG_Ch1_Preliminary_S03f_OrbitParity
-- name    : OddOrder_BG_Ch1_Preliminary_S03f_OrbitParity
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:45:58.984904+00:00
-- url     : https://prove2.me/theorems/f8e6c426-4ebd-48df-9a7f-673f6649a499
-- title:
--   BG §3: the orbit-parity contradiction closing Theorem 3.6 ((3.38))
-- statement:
--   The terminal step (Phase F) of the minimal-counterexample proof of Theorem 3.6 of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, §3, stated as a standalone lemma (3.38). It uses only the facts (3.11)–(3.37) from the earlier phases, with $K$ elementary abelian of order $>q^2$ acting faithfully and fixed-point-freely, and derives the final contradiction by an orbit-parity argument.
--
--   The main declaration: `orbit_parity_contradiction`.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch1_Preliminary/S03f_OrbitParity.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch1_Preliminary/S03f_OrbitParity.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S01b_Prop116
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S03f_Prelim

namespace OddOrder.BG.Ch1.S03f

open scoped commutatorElement Pointwise IsMulCommutative

open OddOrder.GroupTheory

set_option maxHeartbeats 800000 in
-- the scoped `IsMulCommutative` instances (priority 50) cycle with `CommMagma.to_isCommutative`;
-- failing class searches on quotients of `↥KG` must exhaust that branch (cf. `S03f_Thm36`)
set_option synthInstance.maxHeartbeats 400000 in
/-- **BG (3.38), the orbit-parity contradiction** (mmd L1154-L1196): the terminal step of the
minimal-counterexample proof of Theorem 3.6, against the facts established in phases A-E.
`K` elementary abelian of order `> q²` ((3.36)/(3.37)) acting faithfully ((3.28) via (3.16))
and fixed-point-freely ((3.14)) on the elementary abelian `p`-group `V`, with `A = P·R₀`
normalizing `K`, `⁅P,R₀⁆ = P` ((3.21)), `⁅K,P⁆ = K` ((3.24)), `|C_{V}(R₀)| = p` ((3.19)) and
`[K : ⁅K,R₀⁆] = q` ((3.36) step 1), is impossible. -/
theorem orbit_parity_contradiction
    {G : Type*} [Group G] [Finite G]
    {p q r : ℕ} (hp : p.Prime) (hq_prime : q.Prime) (hr_prime : r.Prime)
    (hq_ne_p : q ≠ p) (hpr : p ≠ r) (hodd : Odd (Nat.card G))
    {H : Subgroup G} {V K P : Subgroup ↥H} {R₀ VG KG A : Subgroup G}
    (hVG : VG = V.map H.subtype) (hKG : KG = K.map H.subtype)
    [hVGnorm : VG.Normal]
    (hVGelem : IsElementaryAbelian p ↥VG)
    (hV_ne_bot : V ≠ ⊥)
    (hKcomm : ∀ a b : ↥KG, a * b = b * a)
    (hK_exp : Monoid.exponent ↥KG = q)
    (hKGq : IsPGroup q ↥KG)
    (h337 : q ^ 2 < Nat.card ↥KG)
    (h314C : V ⊓ Subgroup.centralizer (K : Set ↥H) = ⊥)
    (hVK_inf : V ⊓ K = ⊥)
    (hCHV : Subgroup.centralizer ((V : Subgroup ↥H) : Set ↥H) = V)
    (hPp : IsPGroup p ↥P)
    (hr_card : Nat.card ↥R₀ = r)
    (hAdef : A = (P.map H.subtype : Subgroup G) ⊔ R₀)
    (hA_le_N : A ≤ Subgroup.normalizer (KG : Set G))
    (h311 : ∀ (A' B' : Subgroup G) [A'.Normal] [B'.Normal], A' ≤ H → B' ≤ H →
      A' ⊓ B' = ⊥ → A' = ⊥ ∨ B' = ⊥)
    (h313G : (⁅KG, (P.map H.subtype : Subgroup G)⁆ : Subgroup G) ≠ ⊥)
    (h319 : Nat.card ↥(VG ⊓ Subgroup.centralizer (R₀ : Set G)) = p)
    (h321G : (⁅(P.map H.subtype : Subgroup G), R₀⁆ : Subgroup G) = P.map H.subtype)
    (h323G : VG ⊔ KG ⊔ (P.map H.subtype) ⊔ R₀ = ⊤)
    (h324 : (⁅KG, (P.map H.subtype : Subgroup G)⁆ : Subgroup G) = KG)
    (hKRs_index : ((⁅KG, R₀⁆ : Subgroup G).subgroupOf KG).index = q) :
    False := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact q.Prime := ⟨hq_prime⟩
  have hVG_le_H : VG ≤ H := hVG ▸ Subgroup.map_subtype_le V
  classical
  have hVGcommM : IsMulCommutative ↥VG := ⟨⟨hVGelem.1⟩⟩
  have hVG_ne_bot : VG ≠ ⊥ := by
    intro hbot
    apply hV_ne_bot
    rwa [hVG, Subgroup.map_eq_bot_iff, Subgroup.ker_subtype, le_bot_iff] at hbot
  have hKG_ne_botF : KG ≠ ⊥ := by
    intro hbot
    apply h313G
    rw [hbot, Subgroup.commutator_bot_left]
  have hKcommG : ∀ a ∈ KG, ∀ b ∈ KG, a * b = b * a := by
    intro a ha b hb
    exact congrArg Subtype.val (hKcomm ⟨a, ha⟩ ⟨b, hb⟩)
  -- `V_G ⊓ C_G(K_G) = ⊥` ((3.14) at the `G` level).
  have hVG_CKG_bot : VG ⊓ Subgroup.centralizer (KG : Set G) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxV, hxC⟩
    rw [hVG] at hxV
    obtain ⟨v, hv, rfl⟩ := hxV
    have hvC : v ∈ Subgroup.centralizer (K : Set ↥H) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have h2 := Subgroup.mem_centralizer_iff.mp hxC (H.subtype k) (by
        rw [hKG]
        exact ⟨k, hk, rfl⟩)
      exact Subtype.ext (by simpa using h2)
    have h3 : v ∈ V ⊓ Subgroup.centralizer (K : Set ↥H) := ⟨hv, hvC⟩
    rw [h314C, Subgroup.mem_bot] at h3
    rw [Subgroup.mem_bot, h3, map_one]
  -- `V_G ⊓ K_G = ⊥`.
  have hVG_KG_bot : VG ⊓ KG = ⊥ := by
    rw [hVG, hKG, ← Subgroup.map_inf _ _ H.subtype H.subtype_injective, hVK_inf,
      Subgroup.map_bot]
  -- `q`-th-power maps are injective on the elementary abelian `p`-group `V_G`.
  have hVG_qpow_inj : ∀ (a : ℕ) (x : ↥VG), x ^ q ^ a = 1 → x = 1 := by
    intro a x hx
    have h1 : orderOf x ∣ p := orderOf_dvd_of_pow_eq_one (hVGelem.2 x)
    have h2 : orderOf x ∣ q ^ a := orderOf_dvd_of_pow_eq_one hx
    have h4 : Nat.Coprime p (q ^ a) :=
      Nat.Coprime.pow_right a ((Nat.coprime_primes hp hq_prime).mpr (Ne.symm hq_ne_p))
    have h3 : orderOf x ∣ Nat.gcd p (q ^ a) := Nat.dvd_gcd h1 h2
    rw [Nat.Coprime] at h4
    rw [h4, Nat.dvd_one] at h3
    exact orderOf_eq_one_iff.mp h3
  -- ----- The family `{K₁, …, Kₙ}` and its fixed-point subgroups `Vᵢ` -----
  set Pfam : Subgroup G → Prop := fun Ki =>
    Ki ≤ KG ∧ Ki.relIndex KG = q ∧ VG ⊓ Subgroup.centralizer (Ki : Set G) ≠ ⊥ with hPfamdef
  set Vfam : {Ki : Subgroup G // Pfam Ki} → Subgroup G := fun i =>
    VG ⊓ Subgroup.centralizer (((i : Subgroup G) : Subgroup G) : Set G) with hVfamdef
  have hKi_le : ∀ i : {Ki : Subgroup G // Pfam Ki}, (i : Subgroup G) ≤ KG := fun i => i.2.1
  have hKi_rel : ∀ i : {Ki : Subgroup G // Pfam Ki}, ((i : Subgroup G)).relIndex KG = q :=
    fun i => i.2.2.1
  have hVfam_ne : ∀ i : {Ki : Subgroup G // Pfam Ki}, Vfam i ≠ ⊥ := fun i => i.2.2.2
  have hVfam_le : ∀ i : {Ki : Subgroup G // Pfam Ki}, Vfam i ≤ VG := fun i => inf_le_left
  -- all `Kᵢ` have the same order `|K_G| / q`
  obtain ⟨kK, hkK⟩ := hKGq.exists_card_eq
  have hkK_pos : 1 ≤ kK := by
    rcases Nat.eq_zero_or_pos kK with h0 | h1
    · exact absurd (Subgroup.eq_bot_of_card_eq _ (by rw [hkK, h0, pow_zero])) hKG_ne_botF
    · exact h1
  have hKi_card : ∀ i : {Ki : Subgroup G // Pfam Ki},
      Nat.card ↥((i : Subgroup G)) = q ^ (kK - 1) := by
    intro i
    have h0 := Subgroup.card_mul_index (((i : Subgroup G)).subgroupOf KG)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hKi_le i)).toEquiv] at h0
    have h1 : Nat.card ↥((i : Subgroup G)) * ((i : Subgroup G)).relIndex KG
        = Nat.card ↥KG := h0
    have h2 : q ^ (kK - 1) * q = q ^ kK := by
      rw [← pow_succ]
      congr 1
      omega
    rw [hKi_rel i, hkK, ← h2] at h1
    exact Nat.eq_of_mul_eq_mul_right hq_prime.pos h1
  -- distinct `Kᵢ`, `Kⱼ` generate `K_G` (maximality from prime relative index)
  have hKi_sup : ∀ i j : {Ki : Subgroup G // Pfam Ki}, i ≠ j →
      (i : Subgroup G) ⊔ (j : Subgroup G) = KG := by
    intro i j hij
    have hS_le : (i : Subgroup G) ⊔ (j : Subgroup G) ≤ KG := sup_le (hKi_le i) (hKi_le j)
    have h1 : ((i : Subgroup G)).relIndex ((i : Subgroup G) ⊔ (j : Subgroup G))
        * ((i : Subgroup G) ⊔ (j : Subgroup G)).relIndex KG = q := by
      rw [← hKi_rel i]
      exact Subgroup.relIndex_mul_relIndex _ _ _ le_sup_left hS_le
    have h2 : ((i : Subgroup G) ⊔ (j : Subgroup G)).relIndex KG = 1
        ∨ ((i : Subgroup G) ⊔ (j : Subgroup G)).relIndex KG = q :=
      hq_prime.eq_one_or_self_of_dvd _ (Dvd.intro_left _ h1)
    rcases h2 with h2 | h2
    · -- relative index 1: the join is everything
      have h3 : KG ≤ (i : Subgroup G) ⊔ (j : Subgroup G) := by
        rw [← Subgroup.subgroupOf_eq_top]
        rw [← Subgroup.index_eq_one]
        exact h2
      exact le_antisymm hS_le h3
    · -- relative index q: then `Kⱼ ≤ Kᵢ` and cards force `i = j`
      exfalso
      rw [h2] at h1
      have h3 : ((i : Subgroup G)).relIndex ((i : Subgroup G) ⊔ (j : Subgroup G)) = 1 := by
        have := Nat.eq_of_mul_eq_mul_right hq_prime.pos (h1.trans (one_mul q).symm)
        exact this
      have h4 : (i : Subgroup G) ⊔ (j : Subgroup G) ≤ (i : Subgroup G) := by
        rw [← Subgroup.subgroupOf_eq_top]
        rw [← Subgroup.index_eq_one]
        exact h3
      have h5 : (j : Subgroup G) ≤ (i : Subgroup G) := le_sup_right.trans h4
      have h6 : (j : Subgroup G) = (i : Subgroup G) :=
        Subgroup.eq_of_le_of_card_ge h5 (by rw [hKi_card i, hKi_card j])
      exact hij (Subtype.ext h6.symm)
  -- `Vᵢ ⊓ Vⱼ = ⊥` for `i ≠ j` (an element centralizing `Kᵢ` and `Kⱼ` centralizes `K_G`)
  have hVfam_disj : ∀ i j : {Ki : Subgroup G // Pfam Ki}, i ≠ j → Vfam i ⊓ Vfam j = ⊥ := by
    intro i j hij
    rw [eq_bot_iff]
    rintro x ⟨⟨hxV, hxCi⟩, -, hxCj⟩
    have hCi : (i : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G) := by
      intro k hk
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      rw [Set.mem_singleton_iff] at hs
      subst hs
      exact (Subgroup.mem_centralizer_iff.mp hxCi k hk).symm
    have hCj : (j : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G) := by
      intro k hk
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      rw [Set.mem_singleton_iff] at hs
      subst hs
      exact (Subgroup.mem_centralizer_iff.mp hxCj k hk).symm
    have hxCK : x ∈ Subgroup.centralizer (KG : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have h5 := Subgroup.mem_centralizer_iff.mp
        ((hKi_sup i j hij ▸ sup_le hCi hCj) hh) x (Set.mem_singleton x)
      exact h5.symm
    have h6 : x ∈ VG ⊓ Subgroup.centralizer (KG : Set G) := ⟨hxV, hxCK⟩
    rwa [hVG_CKG_bot] at h6
  -- ----- The averaging projections `eᵢ : V_G → Vᵢ` -----
  have hVfam_stable : ∀ i : {Ki : Subgroup G // Pfam Ki}, ∀ b ∈ KG, ∀ x ∈ Vfam i,
      b * x * b⁻¹ ∈ Vfam i := by
    intro i b hb x hx
    obtain ⟨hxV, hxC⟩ := hx
    refine Subgroup.mem_inf.mpr ⟨hVGnorm.conj_mem _ hxV _, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have hsb : s * b = b * s := hKcommG s (hKi_le i hs) b hb
    have hxs : s * x = x * s := Subgroup.mem_centralizer_iff.mp hxC s hs
    calc s * (b * x * b⁻¹) = (s * b) * x * b⁻¹ := by group
      _ = b * (s * x) * b⁻¹ := by rw [hsb]; group
      _ = b * (x * s) * b⁻¹ := by rw [hxs]
      _ = (b * x * b⁻¹) * (b * s * b⁻¹) := by group
      _ = (b * x * b⁻¹) * ((s * b) * b⁻¹) := by rw [← hsb]
      _ = (b * x * b⁻¹) * s := by group
  have instSubFT : ∀ X : Subgroup G, Fintype ↥X := fun _ => Fintype.ofFinite _
  set efam : {Ki : Subgroup G // Pfam Ki} → (↥VG →* ↥VG) := fun i =>
    avgConj (i : Subgroup G) VG with hefamdef
  have hefam_cent : ∀ (i : {Ki : Subgroup G // Pfam Ki}) (v : ↥VG),
      ((efam i v : ↥VG) : G) ∈ Subgroup.centralizer (((i : Subgroup G)) : Set G) := by
    intro i v
    simp only [hefamdef]
    exact avgConj_coe_mem_centralizer _ _ v
  have hefam_mem : ∀ (i j : {Ki : Subgroup G // Pfam Ki}) (v : ↥VG), (v : G) ∈ Vfam j →
      ((efam i v : ↥VG) : G) ∈ Vfam j := by
    intro i j v hv
    simp only [hefamdef]
    exact avgConj_coe_mem _ _ (fun b hb x hx => hVfam_stable j b (hKi_le i hb) x hx) hv
  have hefam_kill : ∀ (i j : {Ki : Subgroup G // Pfam Ki}), i ≠ j → ∀ v : ↥VG,
      (v : G) ∈ Vfam j → efam i v = 1 := by
    intro i j hij v hv
    have h1 : ((efam i v : ↥VG) : G) ∈ Vfam i :=
      Subgroup.mem_inf.mpr ⟨(efam i v).2, hefam_cent i v⟩
    have h3 : ((efam i v : ↥VG) : G) ∈ Vfam i ⊓ Vfam j :=
      Subgroup.mem_inf.mpr ⟨h1, hefam_mem i j v hv⟩
    rw [hVfam_disj i j hij, Subgroup.mem_bot] at h3
    refine Subtype.ext ?_
    rw [Subgroup.coe_one]
    exact h3
  have hefam_fix : ∀ (i : {Ki : Subgroup G // Pfam Ki}) (v : ↥VG), (v : G) ∈ Vfam i →
      efam i v = v ^ q ^ (kK - 1) := by
    intro i v hv
    simp only [hefamdef]
    rw [← hKi_card i]
    exact avgConj_apply_of_mem_centralizer _ _ (Subgroup.mem_inf.mp hv).2
  -- ----- Spanning: `⨆ᵢ Vᵢ = V_G` (**Prop 1.16(2)**, mmd L501) -----
  have hKGcommF : IsMulCommutative ↥KG := ⟨⟨hKcomm⟩⟩
  have hKG_le_NVG : KG ≤ Subgroup.normalizer (VG : Set G) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  set φV : ↥KG →* MulAut ↥VG :=
    VG.normalizerMonoidHom.comp (Subgroup.inclusion hKG_le_NVG) with hφVdef
  have hφV_val : ∀ (k : ↥KG) (v : ↥VG), ((φV k v : ↥VG) : G) = (k : G) * v * (k : G)⁻¹ :=
    fun _ _ => rfl
  have hKG_not_cyclic : ¬ IsCyclic ↥KG := by
    intro hcyc
    obtain ⟨g, hg⟩ := hcyc.exists_generator
    have h1 : Nat.card ↥KG = orderOf g := (orderOf_eq_card_of_forall_mem_zpowers hg).symm
    have h2 : orderOf g ∣ q := by
      rw [← hK_exp]
      exact Monoid.order_dvd_exponent g
    have h3 : Nat.card ↥KG ≤ q := h1 ▸ Nat.le_of_dvd hq_prime.pos h2
    have h4 : q < q ^ 2 := by
      have h5 := hq_prime.one_lt
      calc q = q * 1 := (mul_one q).symm
        _ < q * q := (Nat.mul_lt_mul_left hq_prime.pos).mpr h5
        _ = q ^ 2 := (sq q).symm
    omega
  have hcopKV : Nat.Coprime (Nat.card ↥KG) (Nat.card ↥VG) := by
    obtain ⟨b, hb⟩ := hVGelem.isPGroup.exists_card_eq
    rw [hkK, hb]
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes hq_prime hp).mpr hq_ne_p)
  have hspanRaw := OddOrder.BG.Ch1.S01.cocyclicFixedByClosure_eq_top_of_not_isCyclic
    φV hcopKV hKG_not_cyclic
  have hspan : (⨆ i : {Ki : Subgroup G // Pfam Ki}, (Vfam i).subgroupOf VG) = ⊤ := by
    rw [eq_top_iff, ← hspanRaw]
    change Subgroup.closure _ ≤ _
    rw [Subgroup.closure_le]
    rintro v ⟨Y, ⟨a, hYa⟩, hYfix⟩
    have hYnorm : Y.Normal := ⟨fun y hy g => by
      have h5 : g * y * g⁻¹ = y := by
        rw [hKcomm g y]
        group
      rw [h5]
      exact hy⟩
    -- `↥K_G ⧸ Y` is generated by `mk a` of order dividing `q`, so `[K_G : Y] ∈ {1, q}`
    have hYidx : Y.index = 1 ∨ Y.index = q := by
      have hgen : ∀ z : ↥KG ⧸ Y, z ∈ Subgroup.zpowers ((QuotientGroup.mk' Y) a) := by
        intro z
        obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Y z
        have hxmem : x ∈ ((Y : Set ↥KG) * (Subgroup.zpowers a : Set ↥KG)) := by
          rw [← Subgroup.normal_mul, hYa, Subgroup.coe_top]
          exact Set.mem_univ x
        rw [Set.mem_mul] at hxmem
        obtain ⟨y, hy, z', hz', hxeq⟩ := hxmem
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz'
        refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
        have hy1 : (QuotientGroup.mk' Y) y = 1 := (QuotientGroup.eq_one_iff y).mpr hy
        rw [← hxeq, map_mul, hy1, one_mul, map_zpow]
      have hcyc_card : Nat.card (↥KG ⧸ Y) = orderOf ((QuotientGroup.mk' Y) a) :=
        (orderOf_eq_card_of_forall_mem_zpowers hgen).symm
      have hdvd : orderOf ((QuotientGroup.mk' Y) a) ∣ q := by
        apply orderOf_dvd_of_pow_eq_one
        rw [← map_pow]
        have ha_q : a ^ q = 1 := by
          rw [← hK_exp]
          exact Monoid.pow_exponent_eq_one a
        rw [ha_q, map_one]
      rw [Subgroup.index_eq_card, hcyc_card]
      exact hq_prime.eq_one_or_self_of_dvd _ hdvd
    rcases hYidx with hY1 | hYq
    · -- `Y = ⊤`: `v` centralizes `K_G`, hence `v = 1`
      have hYtop : Y = ⊤ := Subgroup.index_eq_one.mp hY1
      have hvC : (v : G) ∈ Subgroup.centralizer (KG : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro g hg
        have h7 := hYfix ⟨g, hg⟩ (hYtop ▸ Subgroup.mem_top _)
        have h8 : g * (v : G) * g⁻¹ = (v : G) := by
          have h9 := congrArg Subtype.val h7
          rwa [hφV_val] at h9
        calc g * (v : G) = (g * (v : G) * g⁻¹) * g := by group
          _ = (v : G) * g := by rw [h8]
      have h9 : (v : G) ∈ VG ⊓ Subgroup.centralizer (KG : Set G) := ⟨v.2, hvC⟩
      rw [hVG_CKG_bot, Subgroup.mem_bot] at h9
      have h10 : v = 1 := Subtype.ext (by rw [Subgroup.coe_one]; exact h9)
      rw [h10]
      exact SetLike.mem_coe.mpr (Subgroup.one_mem _)
    · -- `[K_G : Y] = q`: `Y_G := Y.map subtype` is one of the `Kᵢ` (or its `Vᵢ` is `⊥`,
      -- in which case `v = 1` directly)
      set YG : Subgroup G := Y.map KG.subtype with hYGdef
      have hYG_le : YG ≤ KG := Subgroup.map_subtype_le Y
      have hYG_rel : YG.relIndex KG = q := by
        change ((Y.map KG.subtype).comap KG.subtype).index = q
        rw [Subgroup.comap_map_eq_self_of_injective KG.subtype_injective]
        exact hYq
      have hvfix : (v : G) ∈ Subgroup.centralizer (YG : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        rintro g ⟨y, hy, rfl⟩
        have h7 := hYfix y hy
        have h8 : (y : G) * (v : G) * (y : G)⁻¹ = (v : G) := by
          have h9 := congrArg Subtype.val h7
          rwa [hφV_val] at h9
        calc (KG.subtype y) * (v : G)
            = ((y : G) * (v : G) * (y : G)⁻¹) * (y : G) := by
              rw [Subgroup.coe_subtype]
              group
          _ = (v : G) * (KG.subtype y) := by rw [h8, Subgroup.coe_subtype]
      by_cases hVbot : VG ⊓ Subgroup.centralizer (YG : Set G) = ⊥
      · have h9 : (v : G) ∈ VG ⊓ Subgroup.centralizer (YG : Set G) := ⟨v.2, hvfix⟩
        rw [hVbot, Subgroup.mem_bot] at h9
        have h10 : v = 1 := Subtype.ext (by rw [Subgroup.coe_one]; exact h9)
        rw [h10]
        exact SetLike.mem_coe.mpr (Subgroup.one_mem _)
      · have hPYG : Pfam YG := ⟨hYG_le, hYG_rel, hVbot⟩
        have h10 : v ∈ (Vfam ⟨YG, hPYG⟩).subgroupOf VG := by
          rw [Subgroup.mem_subgroupOf]
          exact Subgroup.mem_inf.mpr ⟨v.2, hvfix⟩
        have h11 : ((Vfam ⟨YG, hPYG⟩).subgroupOf VG : Subgroup ↥VG)
            ≤ ⨆ i : {Ki : Subgroup G // Pfam Ki}, (Vfam i).subgroupOf VG :=
          le_iSup (fun i : {Ki : Subgroup G // Pfam Ki} => (Vfam i).subgroupOf VG)
            ⟨YG, hPYG⟩
        exact h11 h10
  -- ----- The conjugation action of `A = P_G·R₀` on `{K₁, …, Kₙ}`, and `PR`-transitivity -----
  have hι_fin : Finite {Ki : Subgroup G // Pfam Ki} := by
    have : Finite (Subgroup G) :=
      Finite.of_injective (fun X => (X : Set G)) SetLike.coe_injective
    exact Subtype.finite
  have := Fintype.ofFinite {Ki : Subgroup G // Pfam Ki}
  have hVGcommG : ∀ a ∈ VG, ∀ b ∈ VG, a * b = b * a := by
    intro a ha b hb
    exact congrArg Subtype.val (hVGelem.1 ⟨a, ha⟩ ⟨b, hb⟩)
  have hVG_conj_fix : ∀ a : ↥A, VG.map (MulAut.conj ((a : G))).toMonoidHom = VG :=
    fun a => map_conj_eq_self_of_mem_normalizer (by
      rw [Subgroup.normalizer_eq_top]
      exact Subgroup.mem_top _)
  have hPfam_conj : ∀ (a : ↥A) (X : Subgroup G), Pfam X →
      Pfam (X.map (MulAut.conj (a : G)).toMonoidHom) := by
    intro a X hPX
    simp only [hPfamdef] at hPX ⊢
    obtain ⟨hXle, hXrel, hXne⟩ := hPX
    have hKGfix : KG.map (MulAut.conj (a : G)).toMonoidHom = KG :=
      map_conj_eq_self_of_mem_normalizer (hA_le_N a.2)
    refine ⟨?_, ?_, ?_⟩
    · rw [← hKGfix]
      exact Subgroup.map_mono hXle
    · rw [← hKGfix, Subgroup.relIndex_map_map_of_injective X KG (MulEquiv.injective _)]
      exact hXrel
    · rw [centralizer_map_conj]
      intro hbot
      apply hXne
      have h7 : (VG ⊓ Subgroup.centralizer (X : Set G)).map (MulAut.conj (a : G)).toMonoidHom
          = (⊥ : Subgroup G).map (MulAut.conj (a : G)).toMonoidHom := by
        rw [Subgroup.map_bot, ← hbot,
          Subgroup.map_inf _ _ _ (MulEquiv.injective _), hVG_conj_fix a]
      exact Subgroup.map_injective (MulEquiv.injective _) h7
  let actF : MulAction ↥A {Ki : Subgroup G // Pfam Ki} :=
    conjSubtypeMulAction A Pfam hPfam_conj
  have hsmul_val : ∀ (a : ↥A) (i : {Ki : Subgroup G // Pfam Ki}),
      ((a • i : {Ki : Subgroup G // Pfam Ki}) : Subgroup G)
        = ((i : Subgroup G)).map (MulAut.conj (a : G)).toMonoidHom := fun _ _ => rfl
  have hVfam_smul : ∀ (a : ↥A) (i : {Ki : Subgroup G // Pfam Ki}),
      Vfam (a • i) = (Vfam i).map (MulAut.conj (a : G)).toMonoidHom := by
    intro a i
    simp only [hVfamdef]
    rw [hsmul_val a i]
    calc VG ⊓ Subgroup.centralizer
          ((((i : Subgroup G)).map (MulAut.conj (a : G)).toMonoidHom : Subgroup G) : Set G)
        = VG.map (MulAut.conj (a : G)).toMonoidHom
          ⊓ (Subgroup.centralizer (((i : Subgroup G)) : Set G)).map
              (MulAut.conj (a : G)).toMonoidHom := by
          rw [centralizer_map_conj, hVG_conj_fix a]
      _ = (VG ⊓ Subgroup.centralizer (((i : Subgroup G)) : Set G)).map
            (MulAut.conj (a : G)).toMonoidHom :=
          (Subgroup.map_inf _ _ _ (MulEquiv.injective _)).symm
  -- conjugation by `K_G` fixes each `Vᵢ` setwise
  have hVfam_conj_eq : ∀ (j : {Ki : Subgroup G // Pfam Ki}) (k : G), k ∈ KG →
      (Vfam j).map (MulAut.conj k).toMonoidHom = Vfam j := by
    intro j k hk
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hVfam_stable j k hk x hx
    · intro x hx
      refine ⟨k⁻¹ * x * k, ?_, by
        change k * (k⁻¹ * x * k) * k⁻¹ = x
        group⟩
      have h7 := hVfam_stable j k⁻¹ (KG.inv_mem hk) x hx
      rwa [inv_inv] at h7
  -- conjugation by `V_G` fixes each element of `V_G`
  have hVG_conj_pointwise : ∀ v ∈ VG, ∀ z ∈ VG, v * z * v⁻¹ = z := by
    intro v hv z hz
    rw [hVGcommG v hv z hz]
    group
  -- the sup of the `Vᵢ` over an orbit of the `A`-action is normal in `G`
  have horbitSup_normal : ∀ i₀ : {Ki : Subgroup G // Pfam Ki},
      Subgroup.normalizer
        (((⨆ j ∈ MulAction.orbit (↥A) i₀, Vfam j : Subgroup G)) : Set G) = ⊤ := by
    intro i₀
    set S : Subgroup G := ⨆ j ∈ MulAction.orbit (↥A) i₀, Vfam j with hSdef
    have hS_le_VG : S ≤ VG := iSup₂_le fun j _ => hVfam_le j
    rw [eq_top_iff, ← h323G]
    have hmapS : ∀ f : G →* G, S.map f = ⨆ j ∈ MulAction.orbit (↥A) i₀, (Vfam j).map f := by
      intro f
      rw [hSdef, Subgroup.map_iSup]
      exact iSup_congr fun j => Subgroup.map_iSup _ _
    -- elements of `A` permute the `Vᵢ` within the orbit
    have hApart : ∀ g : G, g ∈ A → g ∈ Subgroup.normalizer (S : Set G) := by
      intro g hgA
      apply mem_normalizer_of_map_conj_eq
      rw [hmapS]
      apply le_antisymm
      · refine iSup₂_le fun j hj => ?_
        rw [← hVfam_smul ⟨g, hgA⟩ j, hSdef]
        obtain ⟨b, hb⟩ := hj
        have hb' : b • i₀ = j := hb
        refine le_iSup₂ (f := fun j' (_ : j' ∈ MulAction.orbit (↥A) i₀) => Vfam j')
          ((⟨g, hgA⟩ : ↥A) • j) ⟨⟨g, hgA⟩ * b, ?_⟩
        change (⟨g, hgA⟩ * b : ↥A) • i₀ = (⟨g, hgA⟩ : ↥A) • j
        rw [mul_smul, hb']
      · rw [hSdef]
        refine iSup₂_le fun j hj => ?_
        have h7 : Vfam j = (Vfam ((⟨g, hgA⟩ : ↥A)⁻¹ • j)).map
            (MulAut.conj (g : G)).toMonoidHom := by
          rw [← hVfam_smul ⟨g, hgA⟩ ((⟨g, hgA⟩ : ↥A)⁻¹ • j), smul_inv_smul]
        rw [h7]
        obtain ⟨b, hb⟩ := hj
        have hb' : b • i₀ = j := hb
        refine le_iSup₂
          (f := fun j' (_ : j' ∈ MulAction.orbit (↥A) i₀) =>
            (Vfam j').map (MulAut.conj (g : G)).toMonoidHom)
          ((⟨g, hgA⟩ : ↥A)⁻¹ • j) ⟨(⟨g, hgA⟩ : ↥A)⁻¹ * b, ?_⟩
        change ((⟨g, hgA⟩ : ↥A)⁻¹ * b) • i₀ = (⟨g, hgA⟩ : ↥A)⁻¹ • j
        rw [mul_smul, hb']
    refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
    · -- `V_G` centralizes `S ≤ V_G`
      intro v hv
      rw [Subgroup.mem_normalizer_iff]
      intro z
      constructor
      · intro hz
        rw [hVG_conj_pointwise v hv z (hS_le_VG hz)]
        exact hz
      · intro hz
        have hzVG : z ∈ VG := by
          have h8 : v⁻¹ * (v * z * v⁻¹) * v = z := by group
          have h9 := hVGnorm.conj_mem _ (hS_le_VG hz) v⁻¹
          rw [inv_inv] at h9
          rw [← h8]
          exact h9
        rwa [hVG_conj_pointwise v hv z hzVG] at hz
    · -- `K_G` fixes each `Vᵢ` setwise
      intro k hk
      apply mem_normalizer_of_map_conj_eq
      rw [hmapS]
      refine le_antisymm (iSup₂_le fun j hj => ?_) ?_
      · rw [hVfam_conj_eq j k hk, hSdef]
        exact le_iSup₂ (f := fun j' (_ : j' ∈ MulAction.orbit (↥A) i₀) => Vfam j') j hj
      · rw [hSdef]
        refine iSup₂_le fun j hj => ?_
        rw [← hVfam_conj_eq j k hk]
        exact le_iSup₂
          (f := fun j' (_ : j' ∈ MulAction.orbit (↥A) i₀) =>
            (Vfam j').map (MulAut.conj k).toMonoidHom) j hj
    · -- `P_G ≤ A`
      intro g hg
      refine hApart g ?_
      rw [hAdef]
      exact Subgroup.mem_sup_left hg
    · -- `R₀ ≤ A`
      intro g hg
      refine hApart g ?_
      rw [hAdef]
      exact Subgroup.mem_sup_right hg
  -- `A` acts transitively on the family ((3.11): two disjoint orbit-sups cannot both be `≠ ⊥`)
  have htrans : ∀ i j : {Ki : Subgroup G // Pfam Ki}, j ∈ MulAction.orbit (↥A) i := by
    by_contra hcon
    push Not at hcon
    obtain ⟨i₀, j₀, hj₀⟩ := hcon
    set S₁ : Subgroup G := ⨆ j ∈ MulAction.orbit (↥A) i₀, Vfam j with hS₁def
    set S₂ : Subgroup G := ⨆ j ∈ MulAction.orbit (↥A) j₀, Vfam j with hS₂def
    have hS₁norm : S₁.Normal := Subgroup.normalizer_eq_top_iff.mp (horbitSup_normal i₀)
    have hS₂norm : S₂.Normal := Subgroup.normalizer_eq_top_iff.mp (horbitSup_normal j₀)
    -- the two orbits are disjoint
    have horb_disj : ∀ j, j ∈ MulAction.orbit (↥A) i₀ → j ∉ MulAction.orbit (↥A) j₀ := by
      intro j hj1 hj2
      apply hj₀
      obtain ⟨g, hg⟩ := hj1
      obtain ⟨g', hg'⟩ := hj2
      have hg2 : g • i₀ = j := hg
      have hg'2 : g' • j₀ = j := hg'
      refine ⟨g'⁻¹ * g, ?_⟩
      change (g'⁻¹ * g) • i₀ = j₀
      rw [mul_smul, hg2, ← hg'2, inv_smul_smul]
    -- disjointness of the sups via the averaging projections
    have hS₁S₂_bot : S₁ ⊓ S₂ = ⊥ := by
      set s₁ : Finset {Ki : Subgroup G // Pfam Ki} :=
        Finset.univ.filter (· ∈ MulAction.orbit (↥A) i₀) with hs₁def
      set s₂ : Finset {Ki : Subgroup G // Pfam Ki} :=
        Finset.univ.filter (· ∈ MulAction.orbit (↥A) j₀) with hs₂def
      have hmem₁ : ∀ j, j ∈ s₁ ↔ j ∈ MulAction.orbit (↥A) i₀ := by
        intro j
        rw [hs₁def, Finset.mem_filter]
        simp
      have hmem₂ : ∀ j, j ∈ s₂ ↔ j ∈ MulAction.orbit (↥A) j₀ := by
        intro j
        rw [hs₂def, Finset.mem_filter]
        simp
      have hst : Disjoint s₁ s₂ := by
        rw [Finset.disjoint_left]
        intro j hj1 hj2
        exact horb_disj j ((hmem₁ j).mp hj1) ((hmem₂ j).mp hj2)
      have hdisj := disjoint_biSup_biSup_of_proj
        (fun i : {Ki : Subgroup G // Pfam Ki} => (Vfam i).subgroupOf VG) efam
        (fun i v hv => hefam_fix i v (Subgroup.mem_subgroupOf.mp hv))
        (fun i j hij v hv => hefam_kill i j hij v (Subgroup.mem_subgroupOf.mp hv))
        (hVG_qpow_inj (kK - 1)) s₁ s₂ hst
      -- transport `Disjoint` along `map VG.subtype`
      have hSmap : ∀ (i₀' : {Ki : Subgroup G // Pfam Ki})
          (s : Finset {Ki : Subgroup G // Pfam Ki}),
          (∀ j, j ∈ s ↔ j ∈ MulAction.orbit (↥A) i₀') →
          (⨆ j ∈ MulAction.orbit (↥A) i₀', Vfam j : Subgroup G)
            = (⨆ j ∈ s, (Vfam j).subgroupOf VG).map VG.subtype := by
        intro i₀' s hmem
        have h8 : ((⨆ j ∈ s, (Vfam j).subgroupOf VG : Subgroup ↥VG)).map VG.subtype
            = ⨆ j ∈ s, ((Vfam j).subgroupOf VG).map VG.subtype := by
          rw [Subgroup.map_iSup]
          exact iSup_congr fun j => Subgroup.map_iSup _ _
        rw [h8]
        have h9 : ∀ j : {Ki : Subgroup G // Pfam Ki},
            ((Vfam j).subgroupOf VG).map VG.subtype = Vfam j := by
          intro j
          rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (hVfam_le j)]
        refine le_antisymm (iSup₂_le fun j hj => ?_) (iSup₂_le fun j hj => ?_)
        · rw [← h9 j]
          exact le_iSup₂
            (f := fun j' (_ : j' ∈ s) => ((Vfam j').subgroupOf VG).map VG.subtype) j
            ((hmem j).mpr hj)
        · rw [h9 j]
          exact le_iSup₂ (f := fun j' (_ : j' ∈ MulAction.orbit (↥A) i₀') => Vfam j') j
            ((hmem j).mp hj)
      rw [hS₁def, hS₂def, hSmap i₀ s₁ hmem₁, hSmap j₀ s₂ hmem₂,
        ← Subgroup.map_inf _ _ _ VG.subtype_injective, (disjoint_iff.mp hdisj),
        Subgroup.map_bot]
    -- both sups are nontrivial normal subgroups of `G` inside `H` — contradiction with (3.11)
    have hS₁_le_H : S₁ ≤ H :=
      (iSup₂_le fun j _ => hVfam_le j).trans hVG_le_H
    have hS₂_le_H : S₂ ≤ H :=
      (iSup₂_le fun j _ => hVfam_le j).trans hVG_le_H
    rcases h311 S₁ S₂ hS₁_le_H hS₂_le_H hS₁S₂_bot with h7 | h7
    · refine hVfam_ne i₀ (le_bot_iff.mp (le_trans ?_ (le_of_eq h7)))
      rw [hS₁def]
      exact le_iSup₂ (f := fun j' (_ : j' ∈ MulAction.orbit (↥A) i₀) => Vfam j') i₀
        (MulAction.mem_orbit_self i₀)
    · refine hVfam_ne j₀ (le_bot_iff.mp (le_trans ?_ (le_of_eq h7)))
      rw [hS₂def]
      exact le_iSup₂ (f := fun j' (_ : j' ∈ MulAction.orbit (↥A) j₀) => Vfam j') j₀
        (MulAction.mem_orbit_self j₀)
  -- ----- A generator `x` of `R₀`, and the fact that it moves some `Kᵢ` -----
  have hR₀_nontriv : Nontrivial ↥R₀ := by
    rw [← Finite.one_lt_card_iff_nontrivial, hr_card]
    exact hr_prime.one_lt
  obtain ⟨x₀, hx₀_ne⟩ := exists_ne (1 : ↥R₀)
  set xG : G := (x₀ : G) with hxGdef
  have hxR₀ : xG ∈ R₀ := x₀.2
  have hxG_ne : xG ≠ 1 := by
    intro h7
    exact hx₀_ne (Subtype.ext h7)
  have hxG_ord : orderOf xG = r := by
    have h1 : orderOf xG ∣ r := by
      rw [← hr_card]
      have h0 : orderOf xG = orderOf x₀ :=
        orderOf_injective R₀.subtype R₀.subtype_injective x₀
      rw [h0]
      exact orderOf_dvd_natCard x₀
    rcases (Nat.Prime.eq_one_or_self_of_dvd hr_prime _ h1) with h2 | h2
    · exact absurd (orderOf_eq_one_iff.mp h2) hxG_ne
    · exact h2
  have hzpow : Subgroup.zpowers xG = R₀ := by
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxR₀)
    rw [Nat.card_zpowers, hr_card, hxG_ord]
  have hxA_mem : xG ∈ A := by
    rw [hAdef]
    exact Subgroup.mem_sup_right hxR₀
  set xA : ↥A := ⟨xG, hxA_mem⟩ with hxAdef
  -- kernel of the permutation action
  set permF : ↥A →* Equiv.Perm {Ki : Subgroup G // Pfam Ki} :=
    MulAction.toPermHom (↥A) {Ki : Subgroup G // Pfam Ki} with hpermFdef
  have hperm_apply : ∀ (a : ↥A) (i : {Ki : Subgroup G // Pfam Ki}),
      permF a i = a • i := fun _ _ => rfl
  have hPG_le_A' : (P.map H.subtype : Subgroup G) ≤ A := by
    rw [hAdef]
    exact le_sup_left
  have hR₀_le_A' : R₀ ≤ A := by
    rw [hAdef]
    exact le_sup_right
  -- `K_G ⊓ C_G(V_G) = ⊥` ((3.10): a `K`-element centralizing `V` lies in `C_H(V) = V`)
  have hKG_CVG_bot : KG ⊓ Subgroup.centralizer (VG : Set G) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxK, hxC⟩
    rw [hKG] at hxK
    obtain ⟨k, hk, rfl⟩ := hxK
    have hkC : k ∈ Subgroup.centralizer ((V : Subgroup ↥H) : Set ↥H) := by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have h8 := Subgroup.mem_centralizer_iff.mp hxC (H.subtype w) (by
        rw [hVG]
        exact ⟨w, hw, rfl⟩)
      exact Subtype.ext (by simpa using h8)
    have h9 : k ∈ V ⊓ K := ⟨hCHV ▸ hkC, hk⟩
    rw [hVK_inf, Subgroup.mem_bot] at h9
    rw [Subgroup.mem_bot, h9, map_one]
  -- if `x` fixed every `Kᵢ`, then (3.21) forces `P` (hence all of `G`) to fix each `Vᵢ`,
  -- so each `Vᵢ` is normal; (3.11) then gives `n = 1`, contradicting `C_V(K) = 1`, `|K| > q²`
  have hnotallfix : ¬ ∀ i : {Ki : Subgroup G // Pfam Ki}, xA • i = i := by
    intro hallfix
    have hDnorm : (permF.ker).Normal := MonoidHom.normal_ker permF
    -- `R₀` (inside `A`) lies in the kernel
    have hR₀'_le_D : R₀.subgroupOf A ≤ permF.ker := by
      intro z hz
      have hzR₀ : (z : G) ∈ R₀ := Subgroup.mem_subgroupOf.mp hz
      rw [← hzpow] at hzR₀
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hzR₀
      have hzA : z = xA ^ k := by
        refine Subtype.ext ?_
        rw [← hk]
        rfl
      rw [MonoidHom.mem_ker, hzA, map_zpow]
      have hx1 : permF xA = 1 := by
        refine Equiv.ext fun i => ?_
        rw [hperm_apply, Equiv.Perm.one_apply]
        exact hallfix i
      rw [hx1, one_zpow]
    -- `P_G` (inside `A`) lies in the kernel: `P = [P, R₀] ⊆ [P, ker] ⊆ ker`
    have hPG'_le_D : (P.map H.subtype : Subgroup G).subgroupOf A ≤ permF.ker := by
      -- transport (3.21): `⁅P_G', R₀'⁆ = P_G'` inside `↥A`
      have hcommA : (⁅(P.map H.subtype : Subgroup G).subgroupOf A, R₀.subgroupOf A⁆
          : Subgroup ↥A) = (P.map H.subtype : Subgroup G).subgroupOf A := by
        apply Subgroup.map_injective (Subgroup.subtype_injective A)
        rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype,
          Subgroup.subgroupOf_map_subtype,
          inf_eq_left.mpr hPG_le_A', inf_eq_left.mpr hR₀_le_A', h321G]
      calc (P.map H.subtype : Subgroup G).subgroupOf A
          = ⁅(P.map H.subtype : Subgroup G).subgroupOf A, R₀.subgroupOf A⁆ := hcommA.symm
        _ ≤ ⁅(P.map H.subtype : Subgroup G).subgroupOf A, permF.ker⁆ :=
            Subgroup.commutator_mono le_rfl hR₀'_le_D
        _ ≤ permF.ker := Subgroup.commutator_le_right _ _
    -- hence the kernel is everything: every `a ∈ A` fixes every `i`
    have hD_top : permF.ker = ⊤ := by
      rw [eq_top_iff]
      have h7 : ((P.map H.subtype : Subgroup G) ⊔ R₀).subgroupOf A ≤ permF.ker := by
        rw [Subgroup.subgroupOf_sup hPG_le_A' hR₀_le_A']
        exact sup_le hPG'_le_D hR₀'_le_D
      rw [← hAdef, Subgroup.subgroupOf_self] at h7
      exact h7
    -- each `Vᵢ` is then normal in `G`
    have hVi_normal : ∀ i : {Ki : Subgroup G // Pfam Ki},
        Subgroup.normalizer ((Vfam i : Subgroup G) : Set G) = ⊤ := by
      intro i
      rw [eq_top_iff, ← h323G]
      have hApart : ∀ g : G, g ∈ A →
          g ∈ Subgroup.normalizer ((Vfam i : Subgroup G) : Set G) := by
        intro g hgA
        apply mem_normalizer_of_map_conj_eq
        rw [← hVfam_smul ⟨g, hgA⟩ i]
        have h8 : (⟨g, hgA⟩ : ↥A) • i = i := by
          have h9 : (⟨g, hgA⟩ : ↥A) ∈ permF.ker := by
            rw [hD_top]
            exact Subgroup.mem_top _
          rw [MonoidHom.mem_ker] at h9
          have h10 := congrArg (fun σ : Equiv.Perm {Ki : Subgroup G // Pfam Ki} => σ i) h9
          simpa [hperm_apply] using h10
        rw [h8]
      refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
      · intro v hv
        rw [Subgroup.mem_normalizer_iff]
        intro z
        constructor
        · intro hz
          rw [hVG_conj_pointwise v hv z (hVfam_le i hz)]
          exact hz
        · intro hz
          have hzVG : z ∈ VG := by
            have h8 : v⁻¹ * (v * z * v⁻¹) * v = z := by group
            have h9 := hVGnorm.conj_mem _ (hVfam_le i hz) v⁻¹
            rw [inv_inv] at h9
            rw [← h8]
            exact h9
          rwa [hVG_conj_pointwise v hv z hzVG] at hz
      · intro k hk
        exact mem_normalizer_of_map_conj_eq (hVfam_conj_eq i k hk)
      · intro g hg
        exact hApart g (hPG_le_A' hg)
      · intro g hg
        exact hApart g (hR₀_le_A' hg)
    -- (3.11): the family is then a singleton `{K₁}` with `V₁ = V_G`
    have hsub : Subsingleton {Ki : Subgroup G // Pfam Ki} := by
      refine ⟨fun i j => ?_⟩
      by_contra hij
      have := Subgroup.normalizer_eq_top_iff.mp (hVi_normal i)
      have := Subgroup.normalizer_eq_top_iff.mp (hVi_normal j)
      rcases h311 (Vfam i) (Vfam j) ((hVfam_le i).trans hVG_le_H)
        ((hVfam_le j).trans hVG_le_H) (hVfam_disj i j hij) with h7 | h7
      · exact hVfam_ne i h7
      · exact hVfam_ne j h7
    have hne_ι : Nonempty {Ki : Subgroup G // Pfam Ki} := by
      by_contra hempty
      rw [not_nonempty_iff] at hempty
      rw [iSup_of_empty] at hspan
      apply hVG_ne_bot
      rw [eq_bot_iff]
      intro v hv
      have h8 : (⟨v, hv⟩ : ↥VG) ∈ (⊥ : Subgroup ↥VG) := by
        rw [hspan]
        exact Subgroup.mem_top _
      rw [Subgroup.mem_bot] at h8
      rw [Subgroup.mem_bot]
      exact congrArg Subtype.val h8
    obtain ⟨i₀⟩ := hne_ι
    have hVfam_top : (Vfam i₀).subgroupOf VG = ⊤ := by
      rw [← hspan]
      apply le_antisymm (le_iSup _ i₀)
      refine iSup_le fun j => ?_
      rw [Subsingleton.elim j i₀]
    have hVG_le_C : VG ≤ Subgroup.centralizer (((i₀ : Subgroup G)) : Set G) := by
      intro w hw
      have h8 : (⟨w, hw⟩ : ↥VG) ∈ (Vfam i₀).subgroupOf VG := by
        rw [hVfam_top]
        exact Subgroup.mem_top _
      rw [Subgroup.mem_subgroupOf] at h8
      exact (Subgroup.mem_inf.mp h8).2
    have hKi₀_bot : (i₀ : Subgroup G) = ⊥ := by
      rw [eq_bot_iff]
      intro k hk
      have hkC : k ∈ Subgroup.centralizer (VG : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro w hwVG
        exact (Subgroup.mem_centralizer_iff.mp (hVG_le_C hwVG) k hk).symm
      have h9 : k ∈ KG ⊓ Subgroup.centralizer (VG : Set G) := ⟨hKi_le i₀ hk, hkC⟩
      rwa [hKG_CVG_bot] at h9
    have h10 := hKi_rel i₀
    rw [hKi₀_bot, Subgroup.relIndex_bot_left] at h10
    nlinarith [h337, h10, hq_prime.one_lt, sq q]
  obtain ⟨i₁, hi₁⟩ := not_forall.mp hnotallfix
  -- ----- The norm argument: `|Vⱼ| = p` and "every non-fixed index is in the `x`-orbit" -----
  set normR : ↥VG →* ↥VG := avgConj R₀ VG with hnormRdef
  -- on a non-fixed index, only `1 ∈ R₀` stabilizes
  have hfix_only : ∀ (j : {Ki : Subgroup G // Pfam Ki}), xA • j ≠ j →
      ∀ b : ↥A, (b : G) ∈ R₀ → b • j = j → (b : G) = 1 := by
    intro j hj b hbR₀ hbfix
    by_contra hbne
    have hbord : orderOf (b : G) = r := by
      have h1 : orderOf (b : G) ∣ r := by
        rw [← hr_card]
        have h0 : orderOf ((b : G)) = orderOf (⟨(b : G), hbR₀⟩ : ↥R₀) :=
          orderOf_injective R₀.subtype R₀.subtype_injective ⟨(b : G), hbR₀⟩
        rw [h0]
        exact orderOf_dvd_natCard _
      rcases Nat.Prime.eq_one_or_self_of_dvd hr_prime _ h1 with h2 | h2
      · exact absurd (orderOf_eq_one_iff.mp h2) hbne
      · exact h2
    have hzb : Subgroup.zpowers (b : G) = R₀ := by
      apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hbR₀)
      rw [Nat.card_zpowers, hr_card, hbord]
    have hxz : xG ∈ Subgroup.zpowers (b : G) := by
      rw [hzb]
      exact hxR₀
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hxz
    apply hj
    have hxAm : xA = b ^ m := by
      refine Subtype.ext ?_
      change xG = ((b ^ m : ↥A) : G)
      rw [← hm]
      rfl
    rw [hxAm]
    exact Subgroup.zpow_mem (MulAction.stabilizer (↥A) j) hbfix m
  -- `eⱼ ∘ norm` is the coprime power map on `Vⱼ`, for any non-fixed `j`
  have hnorm_proj : ∀ (j : {Ki : Subgroup G // Pfam Ki}), xA • j ≠ j →
      ∀ v : ↥VG, (v : G) ∈ Vfam j → efam j (normR v) = v ^ q ^ (kK - 1) := by
    intro j hj v hv
    have h1 : efam j (normR v) = ∏ b : ↥R₀, efam j (avgFactor R₀ VG v b) := by
      rw [show normR v = ∏ b : ↥R₀, avgFactor R₀ VG v b from avgConj_apply R₀ VG v,
        map_prod]
    rw [h1]
    have h2 : ∀ b : ↥R₀, b ≠ 1 → efam j (avgFactor R₀ VG v b) = 1 := by
      intro b hbne
      set bA : ↥A := ⟨(b : G), hR₀_le_A' b.2⟩ with hbAdef
      have hbA_ne : bA • j ≠ j := by
        intro hfixb
        apply hbne
        have h3 := hfix_only j hj bA b.2 hfixb
        exact Subtype.ext h3
      have h4 : ((avgFactor R₀ VG v b : ↥VG) : G) ∈ Vfam (bA • j) := by
        rw [hVfam_smul bA j]
        refine ⟨(v : G), hv, ?_⟩
        rw [avgFactor_coe]
        rfl
      exact hefam_kill j (bA • j) (Ne.symm hbA_ne) _ h4
    rw [Finset.prod_eq_single (1 : ↥R₀) (fun b _ hbne => h2 b hbne)
      (fun h => absurd (Finset.mem_univ _) h)]
    have h5 : avgFactor R₀ VG v (1 : ↥R₀) = v := by
      refine Subtype.ext ?_
      rw [avgFactor_coe]
      simp
    rw [h5]
    exact hefam_fix j v hv
  -- the norm is injective on `Vⱼ` (non-fixed `j`) and lands in `C_{V_G}(R₀)`
  have hnorm_inj : ∀ (j : {Ki : Subgroup G // Pfam Ki}), xA • j ≠ j →
      ∀ v w : ↥VG, (v : G) ∈ Vfam j → (w : G) ∈ Vfam j → normR v = normR w → v = w := by
    intro j hj v w hv hw heq
    have h1 : v ^ q ^ (kK - 1) = w ^ q ^ (kK - 1) := by
      rw [← hnorm_proj j hj v hv, ← hnorm_proj j hj w hw, heq]
    have h2 : (v⁻¹ * w) ^ q ^ (kK - 1) = 1 := by
      rw [mul_pow, inv_pow, h1, inv_mul_cancel]
    have h3 := hVG_qpow_inj (kK - 1) _ h2
    rwa [inv_mul_eq_one] at h3
  have hnorm_mem_C : ∀ v : ↥VG,
      ((normR v : ↥VG) : G) ∈ VG ⊓ Subgroup.centralizer (R₀ : Set G) := by
    intro v
    refine Subgroup.mem_inf.mpr ⟨(normR v).2, ?_⟩
    rw [hnormRdef]
    exact avgConj_coe_mem_centralizer _ _ v
  -- `|V_{i₁}| = p` ((3.19))
  have hVi₁_card : Nat.card ↥(Vfam i₁) = p := by
    have hle : Nat.card ↥(Vfam i₁) ≤ p := by
      rw [← h319]
      have hinj : Function.Injective (fun v : ↥(Vfam i₁) =>
          (⟨((normR ⟨(v : G), hVfam_le i₁ v.2⟩ : ↥VG) : G), hnorm_mem_C _⟩
            : ↥(VG ⊓ Subgroup.centralizer (R₀ : Set G)))) := by
        intro v w hvw
        have h0' := Subtype.ext_iff.mp hvw
        have h0 : ((normR ⟨(v : G), hVfam_le i₁ v.2⟩ : ↥VG) : G)
            = ((normR ⟨(w : G), hVfam_le i₁ w.2⟩ : ↥VG) : G) := h0'
        have h1 : normR ⟨(v : G), hVfam_le i₁ v.2⟩ = normR ⟨(w : G), hVfam_le i₁ w.2⟩ :=
          Subtype.ext h0
        have h2 := hnorm_inj i₁ hi₁ _ _ v.2 w.2 h1
        have h3' := Subtype.ext_iff.mp h2
        have h3 : (v : G) = (w : G) := h3'
        exact Subtype.ext h3
      exact Nat.card_le_card_of_injective _ hinj
    have hpg : IsPGroup p ↥(Vfam i₁) := fun g => ⟨1, by
      refine Subtype.ext ?_
      rw [pow_one]
      have h7 := hVGelem.2 ⟨(g : G), hVfam_le i₁ g.2⟩
      have h8 := congrArg Subtype.val h7
      simpa using h8⟩
    obtain ⟨c, hc⟩ := hpg.exists_card_eq
    have h2 : Nat.card ↥(Vfam i₁) ≠ 1 := fun h =>
      hVfam_ne i₁ (Subgroup.eq_bot_of_card_eq _ h)
    rw [hc] at hle h2 ⊢
    rcases c with _ | c'
    · rw [pow_zero] at h2
      exact absurd rfl h2
    · rcases c' with _ | c''
      · rw [pow_one]
      · exfalso
        have h3 : p ^ 2 ≤ p ^ (c'' + 1 + 1) := Nat.pow_le_pow_right hp.pos (by omega)
        have h4 : p < p ^ 2 := by nlinarith [hp.one_lt]
        omega
  -- by transitivity, `|Vⱼ| = p` for every `j`
  have hVfam_card : ∀ j : {Ki : Subgroup G // Pfam Ki}, Nat.card ↥(Vfam j) = p := by
    intro j
    obtain ⟨a, ha⟩ := htrans i₁ j
    rw [← ha, hVfam_smul]
    rw [← Nat.card_congr
      (Subgroup.equivMapOfInjective (Vfam i₁) _ (MulEquiv.injective _)).toEquiv]
    exact hVi₁_card
  -- ----- `x`-fixed indices: `Kⱼ = ⁅K_G, R₀⁆` (Aut of a prime-order group is abelian) -----
  have hKR_le_KG : (⁅KG, R₀⁆ : Subgroup G) ≤ KG := by
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    have h7 : g₂ ∈ Subgroup.normalizer (KG : Set G) := hA_le_N (hR₀_le_A' hg₂)
    have h8 : g₂ * g₁ * g₂⁻¹ ∈ KG := (Subgroup.mem_normalizer_iff.mp h7 g₁).mp hg₁
    have h9 : g₁ * (g₂ * g₁⁻¹ * g₂⁻¹) ∈ KG := by
      refine KG.mul_mem hg₁ ?_
      have h10 := KG.inv_mem h8
      simpa [mul_assoc] using h10
    have h11 : ⁅g₁, g₂⁆ = g₁ * (g₂ * g₁⁻¹ * g₂⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [h11]
    exact h9
  have hfix_eq : ∀ j : {Ki : Subgroup G // Pfam Ki}, xA • j = j →
      (j : Subgroup G) = (⁅KG, R₀⁆ : Subgroup G) := by
    intro j hjfix
    have : Fact p.Prime := ⟨hp⟩
    have hVj_cyc : IsCyclic ↥(Vfam j) := isCyclic_of_prime_card (hVfam_card j)
    have hKG_le_Nj : KG ≤ Subgroup.normalizer ((Vfam j : Subgroup G) : Set G) := fun k hk =>
      mem_normalizer_of_map_conj_eq (hVfam_conj_eq j k hk)
    have hR₀_le_Nj : R₀ ≤ Subgroup.normalizer ((Vfam j : Subgroup G) : Set G) := by
      intro g hg
      have hgA : g ∈ A := hR₀_le_A' hg
      have hsmulfix : (⟨g, hgA⟩ : ↥A) • j = j := by
        have hgz : g ∈ Subgroup.zpowers xG := by
          rw [hzpow]
          exact hg
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hgz
        have h7 : (⟨g, hgA⟩ : ↥A) = xA ^ k := by
          refine Subtype.ext ?_
          change g = ((xA ^ k : ↥A) : G)
          rw [← hk]
          rfl
        rw [h7]
        exact Subgroup.zpow_mem (MulAction.stabilizer (↥A) j) hjfix k
      apply mem_normalizer_of_map_conj_eq
      rw [← hVfam_smul ⟨g, hgA⟩ j, hsmulfix]
    -- `⁅K_G, R₀⁆ ≤ C_{K_G}(Vⱼ)`
    have hcomm_le : (⁅KG, R₀⁆ : Subgroup G)
        ≤ KG ⊓ Subgroup.centralizer ((Vfam j : Subgroup G) : Set G) := by
      refine le_inf hKR_le_KG ?_
      rw [Subgroup.commutator_le]
      intro g₁ hg₁ g₂ hg₂
      exact commutator_mem_centralizer_of_isCyclic (hKG_le_Nj hg₁) (hR₀_le_Nj hg₂)
    -- `C_{K_G}(Vⱼ) = Kⱼ` (it contains `Kⱼ`, is proper, and `Kⱼ` is maximal)
    have hC_eq : KG ⊓ Subgroup.centralizer ((Vfam j : Subgroup G) : Set G)
        = (j : Subgroup G) := by
      have hj_le : (j : Subgroup G)
          ≤ KG ⊓ Subgroup.centralizer ((Vfam j : Subgroup G) : Set G) := by
        refine le_inf (hKi_le j) ?_
        intro k hk
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        have h7 := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hw).2 k hk
        exact h7.symm
      have hC_ne : KG ⊓ Subgroup.centralizer ((Vfam j : Subgroup G) : Set G) ≠ KG := by
        intro heq
        have h7 : Vfam j ≤ VG ⊓ Subgroup.centralizer (KG : Set G) := by
          intro w hw
          refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hw).1, ?_⟩
          rw [Subgroup.mem_centralizer_iff]
          intro k hk
          have h8 : k ∈ KG ⊓ Subgroup.centralizer ((Vfam j : Subgroup G) : Set G) := by
            rw [heq]
            exact hk
          exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp h8).2 w hw).symm
        rw [hVG_CKG_bot, le_bot_iff] at h7
        exact hVfam_ne j h7
      set X : Subgroup G := KG ⊓ Subgroup.centralizer ((Vfam j : Subgroup G) : Set G)
        with hXdef
      have hX_le : X ≤ KG := inf_le_left
      have h1 : ((j : Subgroup G)).relIndex X * X.relIndex KG = q := by
        rw [← hKi_rel j]
        exact Subgroup.relIndex_mul_relIndex _ _ _ hj_le hX_le
      rcases hq_prime.eq_one_or_self_of_dvd _ (Dvd.intro_left _ h1) with h2 | h2
      · exfalso
        apply hC_ne
        have h3 : KG ≤ X := by
          rw [← Subgroup.subgroupOf_eq_top, ← Subgroup.index_eq_one]
          exact h2
        exact le_antisymm hX_le h3
      · rw [h2] at h1
        have h3 : ((j : Subgroup G)).relIndex X = 1 :=
          Nat.eq_of_mul_eq_mul_right hq_prime.pos (h1.trans (one_mul q).symm)
        have h4 : X ≤ (j : Subgroup G) := by
          rw [← Subgroup.subgroupOf_eq_top, ← Subgroup.index_eq_one]
          exact h3
        exact le_antisymm h4 hj_le
    -- conclude by cardinality: `⁅K_G,R₀⁆ ≤ Kⱼ`, both of index `q`
    have hKR_card : Nat.card ↥(⁅KG, R₀⁆ : Subgroup G) = q ^ (kK - 1) := by
      have h1 := Subgroup.card_mul_index ((⁅KG, R₀⁆ : Subgroup G).subgroupOf KG)
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKR_le_KG).toEquiv, hKRs_index,
        hkK] at h1
      have h2 : q ^ (kK - 1) * q = q ^ kK := by
        rw [← pow_succ]
        congr 1
        omega
      rw [← h2] at h1
      exact Nat.eq_of_mul_eq_mul_right hq_prime.pos h1
    have hle : (⁅KG, R₀⁆ : Subgroup G) ≤ (j : Subgroup G) := hC_eq ▸ hcomm_le
    have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [hKR_card, hKi_card j])
    exact heq.symm
  -- ----- Counting: norms fill `C_{V_G}(R₀)`, so non-fixed indices form one `R₀`-orbit -----
  have hnorm_surj : ∀ w : ↥VG, (w : G) ∈ VG ⊓ Subgroup.centralizer (R₀ : Set G) →
      ∃ v : ↥VG, (v : G) ∈ Vfam i₁ ∧ normR v = w := by
    have hfinj : Function.Injective (fun v : ↥(Vfam i₁) =>
        (⟨((normR ⟨(v : G), hVfam_le i₁ v.2⟩ : ↥VG) : G), hnorm_mem_C _⟩
          : ↥(VG ⊓ Subgroup.centralizer (R₀ : Set G)))) := by
      intro v w hvw
      have h0' := Subtype.ext_iff.mp hvw
      have h0 : ((normR ⟨(v : G), hVfam_le i₁ v.2⟩ : ↥VG) : G)
          = ((normR ⟨(w : G), hVfam_le i₁ w.2⟩ : ↥VG) : G) := h0'
      have h1 : normR ⟨(v : G), hVfam_le i₁ v.2⟩ = normR ⟨(w : G), hVfam_le i₁ w.2⟩ :=
        Subtype.ext h0
      have h2 := hnorm_inj i₁ hi₁ _ _ v.2 w.2 h1
      have h3' := Subtype.ext_iff.mp h2
      have h3 : (v : G) = (w : G) := h3'
      exact Subtype.ext h3
    have hfbij : Function.Bijective (fun v : ↥(Vfam i₁) =>
        (⟨((normR ⟨(v : G), hVfam_le i₁ v.2⟩ : ↥VG) : G), hnorm_mem_C _⟩
          : ↥(VG ⊓ Subgroup.centralizer (R₀ : Set G)))) := by
      rw [Nat.bijective_iff_injective_and_card]
      exact ⟨hfinj, by rw [hVi₁_card, h319]⟩
    intro w hw
    obtain ⟨v, hv⟩ := hfbij.2 ⟨(w : G), hw⟩
    refine ⟨⟨(v : G), hVfam_le i₁ v.2⟩, v.2, ?_⟩
    have h5' := Subtype.ext_iff.mp hv
    have h5 : ((normR ⟨(v : G), hVfam_le i₁ v.2⟩ : ↥VG) : G) = (w : G) := h5'
    exact Subtype.ext h5
  -- every non-fixed index lies in the `R₀`-orbit of `i₁`
  have hnonfix_in_orbit : ∀ j : {Ki : Subgroup G // Pfam Ki}, xA • j ≠ j →
      ∃ b : ↥A, (b : G) ∈ R₀ ∧ b • i₁ = j := by
    intro j hj
    by_contra hnotin
    push Not at hnotin
    rcases (Vfam j).bot_or_exists_ne_one with h1 | ⟨g, hg, hgne⟩
    · exact hVfam_ne j h1
    set vj : ↥VG := ⟨g, hVfam_le j hg⟩ with hvjdef
    have h2 : efam j (normR vj) = vj ^ q ^ (kK - 1) := hnorm_proj j hj vj hg
    have h3 : vj ^ q ^ (kK - 1) ≠ 1 := by
      intro h4
      apply hgne
      exact congrArg Subtype.val (hVG_qpow_inj (kK - 1) vj h4)
    obtain ⟨v, hv, hveq⟩ := hnorm_surj (normR vj) (hnorm_mem_C vj)
    have h6 : efam j (normR v) = 1 := by
      have h7 : efam j (normR v) = ∏ b : ↥R₀, efam j (avgFactor R₀ VG v b) := by
        rw [show normR v = ∏ b : ↥R₀, avgFactor R₀ VG v b from avgConj_apply R₀ VG v,
          map_prod]
      rw [h7]
      refine Finset.prod_eq_one fun b _ => ?_
      set bA : ↥A := ⟨(b : G), hR₀_le_A' b.2⟩ with hbAdef
      have h8 : ((avgFactor R₀ VG v b : ↥VG) : G) ∈ Vfam (bA • i₁) := by
        rw [hVfam_smul bA i₁]
        refine ⟨(v : G), hv, ?_⟩
        rw [avgFactor_coe]
        rfl
      exact hefam_kill j (bA • i₁) (fun h9 => hnotin bA b.2 h9.symm) _ h8
    rw [hveq] at h6
    rw [h6] at h2
    exact h3 h2.symm
  -- the `R₀`-orbit of `i₁` has exactly `r` elements (trivial stabilizer)
  have horbit_card : (MulAction.orbit (↥(R₀.subgroupOf A)) i₁).ncard = r := by
    rw [← Nat.card_coe_set_eq,
      Nat.card_congr (MulAction.orbitEquivQuotientStabilizer (↥(R₀.subgroupOf A)) i₁),
      ← Subgroup.index_eq_card]
    have hstab : MulAction.stabilizer (↥(R₀.subgroupOf A)) i₁ = ⊥ := by
      rw [eq_bot_iff]
      intro s hs
      rw [MulAction.mem_stabilizer_iff] at hs
      have h7 : ((s : ↥A) : G) = 1 :=
        hfix_only i₁ hi₁ (s : ↥A) (Subgroup.mem_subgroupOf.mp s.2) hs
      rw [Subgroup.mem_bot]
      exact Subtype.ext (Subtype.ext h7)
    rw [hstab, Subgroup.index_bot,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR₀_le_A').toEquiv]
    exact hr_card
  -- membership in the `R₀`-orbit, in the handy form
  have horbit_mem : ∀ j : {Ki : Subgroup G // Pfam Ki},
      j ∈ MulAction.orbit (↥(R₀.subgroupOf A)) i₁ ↔
        ∃ b : ↥A, (b : G) ∈ R₀ ∧ b • i₁ = j := by
    intro j
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨(s : ↥A), Subgroup.mem_subgroupOf.mp s.2, rfl⟩
    · rintro ⟨b, hb, rfl⟩
      exact ⟨⟨b, Subgroup.mem_subgroupOf.mpr hb⟩, rfl⟩
  -- ===== Final dichotomy: `n = r` (P fixes some `Vᵢ`) or `n = r + 1` (parity) =====
  by_cases hexfix : ∃ jstar : {Ki : Subgroup G // Pfam Ki}, xA • jstar = jstar
  · -- **`n = r + 1`**: even, yet it is the index of a stabilizer in the odd-order `A`
    obtain ⟨jstar, hjstar⟩ := hexfix
    have huniv : (Set.univ : Set {Ki : Subgroup G // Pfam Ki})
        = MulAction.orbit (↥(R₀.subgroupOf A)) i₁ ∪ {jstar} := by
      apply Set.eq_of_subset_of_subset
      · intro j _
        by_cases hjfix : xA • j = j
        · right
          rw [Set.mem_singleton_iff]
          exact Subtype.ext ((hfix_eq j hjfix).trans (hfix_eq jstar hjstar).symm)
        · left
          rw [horbit_mem j]
          exact hnonfix_in_orbit j hjfix
      · exact fun j _ => Set.mem_univ j
    have hdisj : Disjoint (MulAction.orbit (↥(R₀.subgroupOf A)) i₁)
        ({jstar} : Set {Ki : Subgroup G // Pfam Ki}) := by
      rw [Set.disjoint_singleton_right]
      intro hmem
      rw [horbit_mem jstar] at hmem
      obtain ⟨b, hbR₀, hbij⟩ := hmem
      have h7 : (b⁻¹ * xA * b) • i₁ = i₁ := by
        rw [mul_smul, mul_smul, hbij, hjstar, ← hbij, inv_smul_smul]
      have h8 : ((b⁻¹ * xA * b : ↥A) : G) ∈ R₀ :=
        R₀.mul_mem (R₀.mul_mem (R₀.inv_mem hbR₀) hxR₀) hbR₀
      have h9 := hfix_only i₁ hi₁ _ h8 h7
      apply hxG_ne
      have h10 : (b : G)⁻¹ * xG * (b : G) = 1 := h9
      calc xG = (b : G) * ((b : G)⁻¹ * xG * (b : G)) * (b : G)⁻¹ := by group
        _ = 1 := by rw [h10]; group
    have hn_card : Nat.card {Ki : Subgroup G // Pfam Ki} = r + 1 := by
      rw [← Set.ncard_univ, huniv,
        Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _), horbit_card,
        Set.ncard_singleton]
    have hr_odd : Odd r := by
      refine hodd.of_dvd_nat ?_
      rw [← hr_card]
      exact Subgroup.card_subgroup_dvd_card R₀
    have hn_dvd : Nat.card {Ki : Subgroup G // Pfam Ki} ∣ Nat.card G := by
      have huniv2 : MulAction.orbit (↥A) i₁ = Set.univ := by
        rw [Set.eq_univ_iff_forall]
        exact htrans i₁
      have h7 : Nat.card {Ki : Subgroup G // Pfam Ki}
          = (MulAction.stabilizer (↥A) i₁).index := by
        calc Nat.card {Ki : Subgroup G // Pfam Ki}
            = Nat.card ↥(Set.univ : Set {Ki : Subgroup G // Pfam Ki}) :=
              (Nat.card_congr (Equiv.Set.univ _)).symm
          _ = Nat.card ↥(MulAction.orbit (↥A) i₁) := by rw [huniv2]
          _ = Nat.card (↥A ⧸ MulAction.stabilizer (↥A) i₁) :=
              Nat.card_congr (MulAction.orbitEquivQuotientStabilizer (↥A) i₁)
          _ = (MulAction.stabilizer (↥A) i₁).index := (Subgroup.index_eq_card _).symm
      rw [h7]
      exact (Subgroup.index_dvd_card _).trans (Subgroup.card_subgroup_dvd_card A)
    have hn_odd : Odd (Nat.card {Ki : Subgroup G // Pfam Ki}) := hodd.of_dvd_nat hn_dvd
    rw [hn_card] at hn_odd
    exact (Nat.not_odd_iff_even.mpr (Odd.add_one hr_odd)) hn_odd
  · -- **`n = r`**: `p ∤ n`, so the `p`-group `P` fixes some `Vᵢ`; then `K = ⁅K,P⁆`
    -- centralizes that `Vᵢ` — against `C_V(K) = ⊥`
    push Not at hexfix
    have huniv : MulAction.orbit (↥(R₀.subgroupOf A)) i₁ = Set.univ := by
      rw [Set.eq_univ_iff_forall]
      intro j
      rw [horbit_mem j]
      exact hnonfix_in_orbit j (hexfix j)
    have hn_r : Nat.card {Ki : Subgroup G // Pfam Ki} = r := by
      rw [← Set.ncard_univ, ← huniv, horbit_card]
    have hp_ndvd_n : ¬ p ∣ Nat.card {Ki : Subgroup G // Pfam Ki} := by
      rw [hn_r]
      intro hdvd
      exact hpr ((Nat.prime_dvd_prime_iff_eq hp hr_prime).mp hdvd)
    have hPG'_p : IsPGroup p ↥((P.map H.subtype : Subgroup G).subgroupOf A) :=
      (hPp.map H.subtype).of_equiv (Subgroup.subgroupOfEquivOfLe hPG_le_A').symm
    obtain ⟨jP, hjP⟩ := hPG'_p.nonempty_fixed_point_of_prime_not_dvd_card
      {Ki : Subgroup G // Pfam Ki} hp_ndvd_n
    have hVjP_cyc : IsCyclic ↥(Vfam jP) := isCyclic_of_prime_card (hVfam_card jP)
    have hKG_le_NjP : KG ≤ Subgroup.normalizer ((Vfam jP : Subgroup G) : Set G) :=
      fun k hk => mem_normalizer_of_map_conj_eq (hVfam_conj_eq jP k hk)
    have hPG_le_NjP : (P.map H.subtype : Subgroup G)
        ≤ Subgroup.normalizer ((Vfam jP : Subgroup G) : Set G) := by
      intro g hg
      have hgA : g ∈ A := hPG_le_A' hg
      have hsfix : (⟨g, hgA⟩ : ↥A) • jP = jP :=
        hjP ⟨⟨g, hgA⟩, Subgroup.mem_subgroupOf.mpr hg⟩
      apply mem_normalizer_of_map_conj_eq
      rw [← hVfam_smul ⟨g, hgA⟩ jP, hsfix]
    have hcommKP_le : (⁅KG, (P.map H.subtype : Subgroup G)⁆ : Subgroup G)
        ≤ Subgroup.centralizer ((Vfam jP : Subgroup G) : Set G) := by
      rw [Subgroup.commutator_le]
      intro g₁ hg₁ g₂ hg₂
      exact commutator_mem_centralizer_of_isCyclic (hKG_le_NjP hg₁) (hPG_le_NjP hg₂)
    rw [h324] at hcommKP_le
    have h7 : Vfam jP ≤ VG ⊓ Subgroup.centralizer (KG : Set G) := by
      intro w hw
      refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hw).1, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      exact (Subgroup.mem_centralizer_iff.mp (hcommKP_le hk) w hw).symm
    rw [hVG_CKG_bot, le_bot_iff] at h7
    exact hVfam_ne jP h7

end OddOrder.BG.Ch1.S03f


