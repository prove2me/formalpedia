-- Prove2me | Definitions.Def_OddOrder_BG_Ch1_Preliminary_S03f_Endgame
-- name    : OddOrder_BG_Ch1_Preliminary_S03f_Endgame
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T06:08:43.323979+00:00
-- url     : https://prove2.me/theorems/e9714c33-fd1a-4364-9137-89a9208c0b76
-- title:
--   BG §3: Theorem 3.6, the (3.29)–(3.38) endgame
-- statement:
--   The terminal segment of the minimal-counterexample proof of Theorem 3.6 of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, §3, as a standalone lemma that uses no induction hypothesis, only the facts established up to (3.28). It covers (3.29) (faithful action on the Frattini quotient of the special group $K$), (3.30)–(3.31) (second use of Theorem 3.4) and the steps through (3.38).
--
--   The main declaration: `endgame_contradiction`.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch1_Preliminary/S03f_Endgame.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch1_Preliminary/S03f_Endgame.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S01b_Prop116
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S03_FrobeniusActions
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S03f_OrbitParity
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S03f_Prelim
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S03d_Thm34
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S03e_Thm35
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_PLengthTransfer
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_OperatorQuotientAction
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_OperatorMaschke
import Definitions.Def_OddOrder_GroupTheory_ZGroup

namespace OddOrder.BG.Ch1.S03f

open scoped commutatorElement Pointwise IsMulCommutative

open OddOrder.GroupTheory OddOrder.Isaacs.Ch04 OddOrder.BG.Ch1.OperatorQuotientAction

set_option maxHeartbeats 2400000 in
-- the `IsMulCommutative` scoped instances (priority 50) cycle with `CommMagma.to_isCommutative`;
-- failing class searches on `↥KG ⧸ commutator ↥KG` ((3.29)–(3.30)) must exhaust that branch,
-- which overflows the default 20000 budget (cf. `S03f_Thm36`)
set_option synthInstance.maxHeartbeats 400000 in
/-- **BG Theorem 3.6, the (3.29)–(3.38) endgame** (mmd L1090-L1196): the IH-free terminal
segment of the minimal-counterexample proof.  Against the phase A–D facts — `K` special `q`-group
with `⁅K,P⁆ = K` ((3.24)/(3.25)), `A = P·R₀` acting with `C_A(K) = ⊥` ((3.28)), `C_H(R₀)` a
`Z`-group, `|C_V(R₀)| = p` ((3.19)), `⁅P,R₀⁆ = P` ((3.21)) and `G = V·K·P·R₀` ((3.23)) — the
equations (3.29)–(3.37) force `K` elementary abelian of order `> q²`, and the orbit-parity
count (3.38) yields the contradiction. -/
theorem endgame_contradiction
    {G : Type*} [Group G] [Finite G] [Group.IsSolvable G]
    {p q r : ℕ} (hp : p.Prime) (hq_prime : q.Prime) (hr_prime : r.Prime)
    (hq_ne_p : q ≠ p) (hq_ne_r : q ≠ r) (hpr : p ≠ r) (hodd : Odd (Nat.card G))
    {H : Subgroup G} {V K P : Subgroup ↥H} {R₀ VG KG S₁ A : Subgroup G}
    (hVG : VG = V.map H.subtype) (hKG : KG = K.map H.subtype)
    [hVGnorm : VG.Normal]
    (hZ : OddOrder.GroupTheory.IsZGroup ↥(H ⊓ Subgroup.centralizer (R₀ : Set G)))
    (hVGelem : IsElementaryAbelian p ↥VG)
    (hV_ne_bot : V ≠ ⊥)
    (hVK_inf : V ⊓ K = ⊥)
    (h314C : V ⊓ Subgroup.centralizer (K : Set ↥H) = ⊥)
    (hCHV : Subgroup.centralizer ((V : Subgroup ↥H) : Set ↥H) = V)
    (hPp : IsPGroup p ↥P)
    (hr_card : Nat.card ↥R₀ = r)
    (hKGq : IsPGroup q ↥KG)
    (hK_special : IsSpecial q ↥KG)
    (hK_exp : Monoid.exponent ↥KG = q)
    (hAdef : A = (P.map H.subtype : Subgroup G) ⊔ R₀)
    (φA : ↥A →* MulAut ↥KG)
    (hφA_val : ∀ (a : ↥A) (k : ↥KG),
      ((φA a k : ↥KG) : G) = (a : G) * (k : G) * (a : G)⁻¹)
    (hAcard : Nat.card ↥A
      = Nat.card ↥(P.map H.subtype : Subgroup G) * Nat.card ↥R₀)
    (hA_le_N : A ≤ Subgroup.normalizer (KG : Set G))
    (h311 : ∀ (A' B' : Subgroup G) [A'.Normal] [B'.Normal], A' ≤ H → B' ≤ H →
      A' ⊓ B' = ⊥ → A' = ⊥ ∨ B' = ⊥)
    (h313G : (⁅KG, (P.map H.subtype : Subgroup G)⁆ : Subgroup G) ≠ ⊥)
    (h317 : ¬ (KG ≤ Subgroup.centralizer (R₀ : Set G)))
    (hKG_le_S₁ : KG ≤ S₁) (hR₀_le_S₁ : R₀ ≤ S₁)
    (hdisjKR : Disjoint KG R₀)
    (h318 : S₁ ⊓ Subgroup.centralizer (VG : Set G) = ⊥)
    (h319 : Nat.card ↥(VG ⊓ Subgroup.centralizer (R₀ : Set G)) = p)
    (h321G : (⁅(P.map H.subtype : Subgroup G), R₀⁆ : Subgroup G) = P.map H.subtype)
    (h322' : ∀ X : Subgroup G, X ≤ KG → X ≠ KG →
      R₀ ≤ Subgroup.normalizer (X : Set G) →
      (P.map H.subtype : Subgroup G) ≤ Subgroup.normalizer (X : Set G) →
      (⁅X, (P.map H.subtype : Subgroup G)⁆ : Subgroup G) = ⊥)
    (h323G : VG ⊔ KG ⊔ (P.map H.subtype) ⊔ R₀ = ⊤)
    (h324 : (⁅KG, (P.map H.subtype : Subgroup G)⁆ : Subgroup G) = KG)
    (h328 : A ⊓ Subgroup.centralizer (KG : Set G) = ⊥)
    (hR₀_le_NKG : R₀ ≤ Subgroup.normalizer (KG : Set G))
    (hPG_le_NKG : (P.map H.subtype : Subgroup G) ≤ Subgroup.normalizer (KG : Set G))
    (hR₀_le_NPG : R₀ ≤ Subgroup.normalizer ((P.map H.subtype : Subgroup G) : Set G))
    (hdisjPR : Disjoint (P.map H.subtype : Subgroup G) R₀) :
    False := by
    have : Fact p.Prime := ⟨hp⟩
    have hKG_le_H : KG ≤ H := hKG ▸ Subgroup.map_subtype_le K
    have : Fact q.Prime := ⟨hq_prime⟩
    have hq_ndvd_A : ¬ q ∣ Nat.card ↥A := by
      rw [hAcard]
      intro hdvd
      rcases (Nat.Prime.dvd_mul hq_prime).mp hdvd with h4 | h4
      · obtain ⟨k, hk⟩ := (hPp.map H.subtype).exists_card_eq
        rw [hk] at h4
        exact hq_ne_p
          ((Nat.prime_dvd_prime_iff_eq hq_prime hp).mp (hq_prime.dvd_of_dvd_pow h4))
      · rw [hr_card] at h4
        exact hq_ne_r ((Nat.prime_dvd_prime_iff_eq hq_prime hr_prime).mp h4)
    -- `K` special ⟹ `K' = Φ(K)` (in the elementary abelian branch both are `⊥`)
    have hK'Φ : commutator ↥KG = _root_.frattini ↥KG := by
      rcases hK_special.2 with hEA | ⟨hcomm, hfrat, _⟩
      · have hc : commutator ↥KG = ⊥ := by
          rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
          intro x _
          rw [Subgroup.mem_centralizer_iff]
          intro m _
          exact hEA.1 m x
        have hf : _root_.frattini ↥KG = ⊥ :=
          (OddOrder.BG.Ch1.S01.frattini_eq_bot_iff_isElementaryAbelian hKGq).mpr hEA
        rw [hc, hf]
      · rw [hcomm, hfrat]
    -- pin the `Normal` instance locally: with `IsMulCommutative (K/K')` in scope below, the
    -- bare search wanders into `Subgroup.normal_of_isMulCommutative` and times out
    have hK'norm : (commutator ↥KG).Normal := inferInstance
    have hK'_inv : OddOrder.Isaacs.Ch03.IsAInvariant φA (commutator ↥KG) :=
      OddOrder.Isaacs.Ch03.IsAInvariant.of_characteristic φA
    set φAQ : ↥A →* MulAut (↥KG ⧸ commutator ↥KG) :=
      OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom hK'_inv
      with hφAQ
    have h329 : ∀ a : ↥A,
        (∀ kq : ↥KG ⧸ commutator ↥KG, φAQ a kq = kq) → a = 1 := by
      intro a ha
      have ha1 : φAQ a = 1 := by
        ext kq
        exact ha kq
      have hcop : Nat.Coprime (orderOf (φA a)) q := by
        have h1 : orderOf (φA a) ∣ Nat.card ↥A :=
          (orderOf_map_dvd φA a).trans (orderOf_dvd_natCard a)
        exact (hq_prime.coprime_iff_not_dvd.mpr fun hdvd => hq_ndvd_A (hdvd.trans h1)).symm
      have htriv : ∀ z : ℤ, ∀ k : ↥KG,
          ∃ x ∈ _root_.frattini ↥KG, ((φA a) ^ z) k = k * x := by
        intro z k
        have h1 : φAQ (a ^ z) = 1 := by rw [map_zpow, ha1, one_zpow]
        have h2 : ((φA (a ^ z) k : ↥KG) : ↥KG ⧸ commutator ↥KG)
            = ((k : ↥KG) : ↥KG ⧸ commutator ↥KG) := by
          have h3 := DFunLike.congr_fun h1 ((k : ↥KG) : ↥KG ⧸ commutator ↥KG)
          rw [MulAut.one_apply, hφAQ,
            OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom_apply] at h3
          exact h3
        have h4 : k⁻¹ * (φA (a ^ z)) k ∈ commutator ↥KG := QuotientGroup.eq.mp h2.symm
        refine ⟨k⁻¹ * (φA (a ^ z)) k, hK'Φ ▸ h4, ?_⟩
        rw [← map_zpow]
        exact (mul_inv_cancel_left _ _).symm
      have hφA1 : φA a = 1 :=
        OddOrder.BG.Ch1.S01.mulAut_eq_one_of_coprime_orderOf_of_frattini hKGq (φA a)
          hcop htriv
      have haC : (a : G) ∈ Subgroup.centralizer (KG : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro m hm
        have h1 := DFunLike.congr_fun hφA1 ⟨m, hm⟩
        rw [MulAut.one_apply] at h1
        have h2 : (a : G) * m * (a : G)⁻¹ = m :=
          (hφA_val a ⟨m, hm⟩).symm.trans (congrArg Subtype.val h1)
        exact (mul_inv_eq_iff_eq_mul.mp h2).symm
      have habot : (a : G) ∈ A ⊓ Subgroup.centralizer (KG : Set G) := ⟨a.2, haC⟩
      rw [h328, Subgroup.mem_bot] at habot
      exact Subtype.ext habot
    -- ===== (3.30) `C_{K/K'}(R₀) ≠ 1`, i.e. `C_K(R₀) ⊄ K'` =====
    -- Otherwise `A = P·R₀` acts faithfully ((3.29)) on the `𝔽_q`-vector space `K/K'` with
    -- `C_{K/K'}(R₀) = 0`, so Theorem 3.4 (second use) makes `⁅R₀,P⁆ = ⊥`; but `⁅P,R₀⁆ = P`
    -- ((3.21)) then forces `P = ⊥`, contradicting `⁅K,P⁆ ≠ ⊥` ((3.13)).
    have hPG_le_A : (P.map H.subtype : Subgroup G) ≤ A := by
      rw [hAdef]; exact le_sup_left
    have hR₀_le_A : R₀ ≤ A := by
      rw [hAdef]; exact le_sup_right
    have hR₀cardA : Nat.card ↥(R₀.subgroupOf A) = r :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR₀_le_A).toEquiv).trans hr_card
    -- `K/K'` is abelian (shared by (3.30) and the Proposition 1.6(d) step at (3.32))
    have hQbar_mul_comm : ∀ a b : ↥KG ⧸ commutator ↥KG, a * b = b * a := by
      intro a b
      refine QuotientGroup.induction_on a fun x => ?_
      refine QuotientGroup.induction_on b fun y => ?_
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      have hc : (x * y)⁻¹ * (y * x) = ⁅y⁻¹, x⁻¹⁆ := by
        rw [commutatorElement_def, mul_inv_rev, inv_inv, inv_inv]
        exact (mul_assoc _ y x).symm
      rw [hc, commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    have h330 : ¬ ((KG ⊓ Subgroup.centralizer (R₀ : Set G)) ≤ ⁅KG, KG⁆) := by
      intro hsub
      -- `K/K'` as a `ZMod q`-module
      have hQbar_comm : IsMulCommutative (↥KG ⧸ commutator ↥KG) := ⟨⟨hQbar_mul_comm⟩⟩
      have hexpQ : ∀ g : ↥KG ⧸ commutator ↥KG, g ^ q = 1 := by
        intro g
        refine QuotientGroup.induction_on g fun k => ?_
        have hk : k ^ q = 1 := by
          rw [← hK_exp]
          exact Monoid.pow_exponent_eq_one k
        rw [← QuotientGroup.mk_pow, hk, QuotientGroup.mk_one]
      have hqsmul : ∀ x : Additive (↥KG ⧸ commutator ↥KG), (q : ℕ) • x = 0 := by
        intro x
        apply Additive.toMul.injective
        rw [toMul_nsmul, toMul_zero]
        exact hexpQ x.toMul
      have hQmod : Module (ZMod q) (Additive (↥KG ⧸ commutator ↥KG)) :=
        AddCommGroup.zmodModule hqsmul
      have : Module.Finite (ZMod q) (Additive (↥KG ⧸ commutator ↥KG)) :=
        Module.Finite.of_finite
      set ρ : Representation (ZMod q) ↥A (Additive (↥KG ⧸ commutator ↥KG)) :=
        (OddOrder.BG.Ch1_Preliminary.mulAutToEnd (↥KG ⧸ commutator ↥KG) q).comp φAQ
        with hρdef
      have hρ_apply : ∀ (g : ↥A) (x : Additive (↥KG ⧸ commutator ↥KG)),
          ρ g x = Additive.ofMul (φAQ g (Additive.toMul x)) := by
        intro g x
        rfl
      -- `P_G` is a normal Hall subgroup of `A` with complement `R₀`
      have hA_le_NPG : A ≤ Subgroup.normalizer
          ((P.map H.subtype : Subgroup G) : Set G) := by
        rw [hAdef]
        exact sup_le Subgroup.le_normalizer
          (fun _g hg => hR₀_le_NPG hg)
      have hPGnormA : (((P.map H.subtype).subgroupOf A) : Subgroup ↥A).Normal :=
        Subgroup.normal_subgroupOf_of_le_normalizer hA_le_NPG
      have hPGcardA : Nat.card ↥((P.map H.subtype).subgroupOf A)
          = Nat.card ↥(P.map H.subtype : Subgroup G) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPG_le_A).toEquiv
      have hcomplA : Subgroup.IsComplement'
          ((P.map H.subtype).subgroupOf A) (R₀.subgroupOf A) := by
        refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
        · refine disjoint_iff.mpr (eq_bot_iff.mpr fun x hx => ?_)
          rw [Subgroup.mem_inf] at hx
          simp only [Subgroup.mem_subgroupOf] at hx
          have hmem : (x : G) ∈ (P.map H.subtype : Subgroup G) ⊓ R₀ := ⟨hx.1, hx.2⟩
          rw [hdisjPR.eq_bot, Subgroup.mem_bot] at hmem
          rw [Subgroup.mem_bot]
          exact Subtype.ext (by simpa using hmem)
        · have hsup : (((P.map H.subtype).subgroupOf A) : Subgroup ↥A)
              ⊔ (R₀.subgroupOf A) = ⊤ := by
            rw [← Subgroup.subgroupOf_sup hPG_le_A hR₀_le_A, ← hAdef,
              Subgroup.subgroupOf_self]
          have hmul := Subgroup.normal_mul
            (((P.map H.subtype).subgroupOf A) : Subgroup ↥A) (R₀.subgroupOf A)
          rw [hsup, Subgroup.coe_top] at hmul
          exact hmul.symm
      have hHallA : Nat.Coprime (Nat.card ↥((P.map H.subtype).subgroupOf A))
          (Nat.card ↥(R₀.subgroupOf A)) := by
        rw [hPGcardA, hR₀cardA]
        obtain ⟨k, hk⟩ := (hPp.map H.subtype).exists_card_eq
        rw [hk]
        exact Nat.Coprime.pow_left k ((Nat.coprime_primes hp hr_prime).mpr hpr)
      have hodd_A : Odd (Nat.card ↥A) := by
        obtain ⟨m, hm⟩ := Subgroup.card_subgroup_dvd_card A
        rw [hm, Nat.odd_mul] at hodd
        exact hodd.1
      have hcharA : (Nat.card ↥A : ZMod q) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]
        exact hq_ndvd_A
      -- `C_{K/K'}(R₀) = 0`: a fixed vector lifts to `C_K(R₀)` (coprime action), lands in
      -- `K'` by `hsub`, hence dies in the quotient
      have hCV : ∀ v : Additive (↥KG ⧸ commutator ↥KG),
          (∀ rr : ↥(R₀.subgroupOf A), ρ ((rr : ↥A)) v = v) → v = 0 := by
        intro v hv
        obtain ⟨k, hk⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
        have hfix : ∀ rr : ↥(R₀.subgroupOf A), ∃ n ∈ commutator ↥KG,
            (φA.comp (R₀.subgroupOf A).subtype) rr k = k * n := by
          intro rr
          have h1 := hv rr
          rw [hρ_apply] at h1
          have h2 : φAQ (rr : ↥A) (Additive.toMul v) = Additive.toMul v := by
            have h3 := congrArg Additive.toMul h1
            rwa [toMul_ofMul] at h3
          rw [← hk, hφAQ,
            OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom_apply] at h2
          refine ⟨k⁻¹ * (φA (rr : ↥A)) k, QuotientGroup.eq.mp h2.symm, ?_⟩
          exact (mul_inv_cancel_left _ _).symm
        have hcopRK : Nat.Coprime (Nat.card ↥(R₀.subgroupOf A)) (Nat.card ↥KG) := by
          rw [hR₀cardA]
          obtain ⟨m, hm⟩ := hKGq.exists_card_eq
          rw [hm]
          exact Nat.Coprime.pow_right m
            ((Nat.coprime_primes hr_prime hq_prime).mpr (Ne.symm hq_ne_r))
        have hN_inv' : OddOrder.Isaacs.Ch03.IsAInvariant
            (φA.comp (R₀.subgroupOf A).subtype) (commutator ↥KG) :=
          OddOrder.Isaacs.Ch03.IsAInvariant.of_characteristic _
        obtain ⟨c, hc_fix, n, hn, hceq⟩ :=
          OddOrder.Isaacs.Ch04.coprime_fixedPoints_quotient hcopRK (Or.inr inferInstance)
            hN_inv' hfix
        -- `c ∈ C_K(R₀)`, so `c ∈ K'` by `hsub`; but `c ≡ k mod K'`, so `v = 0`
        have hcC : (c : G) ∈ KG ⊓ Subgroup.centralizer (R₀ : Set G) := by
          refine Subgroup.mem_inf.mpr
            ⟨c.2, Subgroup.mem_centralizer_iff.mpr fun m hm => ?_⟩
          have hmA : m ∈ A := hR₀_le_A hm
          have h5 := hc_fix ⟨⟨m, hmA⟩, Subgroup.mem_subgroupOf.mpr hm⟩
          have h6 : m * (c : G) * m⁻¹ = (c : G) :=
            (hφA_val ⟨m, hmA⟩ c).symm.trans (congrArg Subtype.val h5)
          exact mul_inv_eq_iff_eq_mul.mp h6
        have hcK' : c ∈ commutator ↥KG := by
          have h7 : (c : G) ∈ ⁅KG, KG⁆ := hsub hcC
          have hKGder : (commutator ↥KG).map KG.subtype = ⁅KG, KG⁆ := by
            rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
              Subgroup.range_subtype]
          have h8 : (c : G) ∈ (commutator ↥KG).map KG.subtype := hKGder.symm ▸ h7
          obtain ⟨c', hc', heq⟩ := h8
          rwa [show c' = c from Subtype.ext heq] at hc'
        have hmkc : ((k : ↥KG) : ↥KG ⧸ commutator ↥KG) = 1 := by
          have h9 : ((k : ↥KG) : ↥KG ⧸ commutator ↥KG)
              = ((c : ↥KG) : ↥KG ⧸ commutator ↥KG) := by
            rw [QuotientGroup.eq, hceq, inv_mul_cancel_left]
            exact hn
          rw [h9, QuotientGroup.eq_one_iff]
          exact hcK'
        rw [← ofMul_toMul v, ← hk, hmkc, ofMul_one]
      have hthm34 := S03d.thm34 ρ ((P.map H.subtype).subgroupOf A) (R₀.subgroupOf A)
        hcomplA hHallA ⟨r, hr_prime, hR₀cardA⟩ hodd_A hcharA hCV
      -- `⁅R₀,P⁆` acts trivially on `K/K'`, hence is trivial by (3.29)
      have hcomm_bot : (⁅R₀, (P.map H.subtype : Subgroup G)⁆ : Subgroup G) = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        have hsub2 : (⁅R₀, (P.map H.subtype : Subgroup G)⁆ : Subgroup G) ≤ A := by
          rw [Subgroup.commutator_le]
          intro g₁ hg₁ g₂ hg₂
          have h1 : g₁ ∈ A := hR₀_le_A hg₁
          have h2 : g₂ ∈ A := hPG_le_A hg₂
          rw [commutatorElement_def]
          exact A.mul_mem (A.mul_mem (A.mul_mem h1 h2) (A.inv_mem h1)) (A.inv_mem h2)
        have hxA : x ∈ A := hsub2 hx
        have hmapeq : (⁅(R₀.subgroupOf A : Subgroup ↥A), (P.map H.subtype).subgroupOf A⁆
            : Subgroup ↥A).map A.subtype = ⁅R₀, (P.map H.subtype : Subgroup G)⁆ := by
          rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype,
            Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hR₀_le_A,
            inf_eq_left.mpr hPG_le_A]
        have hx' : (⟨x, hxA⟩ : ↥A) ∈ (⁅(R₀.subgroupOf A : Subgroup ↥A),
            (P.map H.subtype).subgroupOf A⁆ : Subgroup ↥A) := by
          have hmem : x ∈ (⁅(R₀.subgroupOf A : Subgroup ↥A),
              (P.map H.subtype).subgroupOf A⁆ : Subgroup ↥A).map A.subtype :=
            hmapeq.symm ▸ hx
          obtain ⟨z, hz, hzx⟩ := hmem
          rwa [show z = ⟨x, hxA⟩ from Subtype.ext hzx] at hz
        have hρ1 : ρ ⟨x, hxA⟩ = 1 := hthm34 _ hx'
        have hone : (⟨x, hxA⟩ : ↥A) = 1 := by
          refine h329 _ fun kq => ?_
          have h1 := DFunLike.congr_fun hρ1 (Additive.ofMul kq)
          rw [hρ_apply, Module.End.one_apply] at h1
          exact Additive.ofMul.injective h1
        rw [Subgroup.mem_bot]
        have h10 := congrArg Subtype.val hone
        simpa using h10
      have hPGbot : (P.map H.subtype : Subgroup G) = ⊥ := by
        rw [← h321G, Subgroup.commutator_comm]
        exact hcomm_bot
      apply h313G
      rw [hPGbot, Subgroup.commutator_bot_right]
    -- ===== (3.31) `|C_K(R₀)| = q` and `C_K(R₀) ⊓ K' = ⊥` =====
    -- `C_K(R₀)` is a nontrivial ((3.30)) subgroup of exponent `q` ((3.26)) inside the
    -- `Z`-group `C_H(R₀)`, hence has order exactly `q`; being of prime order and not
    -- contained in `K'`, it meets `K'` trivially.
    have hCKR_ne_bot : KG ⊓ Subgroup.centralizer (R₀ : Set G) ≠ ⊥ := by
      intro hbot
      apply h330
      rw [hbot]
      exact bot_le
    have h331a : Nat.card ↥(KG ⊓ Subgroup.centralizer (R₀ : Set G)) = q := by
      refine card_eq_prime_of_le_isZGroup hZ
        (inf_le_inf_right _ hKG_le_H) hq_prime ?_ hCKR_ne_bot
      intro x hx
      obtain ⟨hxK, _⟩ := Subgroup.mem_inf.mp hx
      have h1 : (⟨x, hxK⟩ : ↥KG) ^ q = 1 := by
        rw [← hK_exp]
        exact Monoid.pow_exponent_eq_one _
      have h2 := congrArg Subtype.val h1
      rwa [Subgroup.coe_pow, Subgroup.coe_one] at h2
    have h331b : (KG ⊓ Subgroup.centralizer (R₀ : Set G)) ⊓ ⁅KG, KG⁆ = ⊥ := by
      by_contra hne
      have hdvd : Nat.card ↥((KG ⊓ Subgroup.centralizer (R₀ : Set G)) ⊓ ⁅KG, KG⁆) ∣ q :=
        h331a ▸ Subgroup.card_dvd_of_le inf_le_left
      rcases (Nat.dvd_prime hq_prime).mp hdvd with h1 | h1
      · exact hne (Subgroup.eq_bot_of_card_eq _ h1)
      · refine h330 ?_
        have heq : (KG ⊓ Subgroup.centralizer (R₀ : Set G)) ⊓ ⁅KG, KG⁆
            = KG ⊓ Subgroup.centralizer (R₀ : Set G) :=
          Subgroup.eq_of_le_of_card_ge inf_le_left (le_of_eq (h331a.trans h1.symm))
        exact heq ▸ inf_le_right
    -- ===== (3.32)+(3.33) `K ≠ ⁅K,R₀⁆` and `C_{⁅K,R₀⁆}(R₀) = ⊥` =====
    -- Proposition 1.6(d) on the abelian quotient `K/K'`: the `R₀`-fixed points and the
    -- action commutator intersect trivially, so `C_K(R₀) ∩ ⁅K,R₀⁆ ≤ K'`.  With (3.31) the
    -- intersection is then trivial; and `⁅K,R₀⁆ = K` would put the whole order-`q` group
    -- `C_K(R₀)` inside `K'`, contradicting (3.30).
    have hbridge : ∀ x ∈ (⁅KG, R₀⁆ : Subgroup G), ∃ hxK : x ∈ KG,
        ((⟨x, hxK⟩ : ↥KG) : ↥KG ⧸ commutator ↥KG) ∈
          OddOrder.Isaacs.Ch04.actionCommutator
            (φAQ.comp (R₀.subgroupOf A).subtype) := by
      intro x hx
      rw [Subgroup.commutator_def] at hx
      induction hx using Subgroup.closure_induction with
      | mem y hy =>
        obtain ⟨g₁, hg₁, g₂, hg₂, rfl⟩ := hy
        have hg₂A : g₂ ∈ A := hR₀_le_A hg₂
        have hyK : ⁅g₁, g₂⁆ ∈ KG := by
          rw [commutatorElement_def, mul_assoc g₁ g₂ g₁⁻¹, mul_assoc g₁]
          refine KG.mul_mem hg₁ ?_
          exact (Subgroup.mem_normalizer_iff.mp (hR₀_le_NKG hg₂) g₁⁻¹).mp (KG.inv_mem hg₁)
        refine ⟨hyK, Subgroup.subset_closure ?_⟩
        refine ⟨((⟨g₁, hg₁⟩ : ↥KG) : ↥KG ⧸ commutator ↥KG),
          ⟨⟨g₂, hg₂A⟩, Subgroup.mem_subgroupOf.mpr hg₂⟩, ?_⟩
        have hval : (⟨⁅g₁, g₂⁆, hyK⟩ : ↥KG)
            = ⟨g₁, hg₁⟩ * φA ⟨g₂, hg₂A⟩ (⟨g₁, hg₁⟩ : ↥KG)⁻¹ := by
          apply Subtype.ext
          have h1 : ((φA ⟨g₂, hg₂A⟩ ((⟨g₁, hg₁⟩ : ↥KG)⁻¹) : ↥KG) : G)
              = g₂ * g₁⁻¹ * g₂⁻¹ := hφA_val _ _
          change ⁅g₁, g₂⁆
            = ((⟨g₁, hg₁⟩ * φA ⟨g₂, hg₂A⟩ (⟨g₁, hg₁⟩ : ↥KG)⁻¹ : ↥KG) : G)
          rw [Subgroup.coe_mul, h1, commutatorElement_def,
            mul_assoc g₁ g₂ g₁⁻¹, mul_assoc g₁]
        rw [hval]
        rfl
      | one =>
        exact ⟨KG.one_mem, by
          rw [show (⟨(1 : G), KG.one_mem⟩ : ↥KG) = 1 from rfl, QuotientGroup.mk_one]
          exact Subgroup.one_mem _⟩
      | mul y z hy hz ihy ihz =>
        obtain ⟨hyK, hyAC⟩ := ihy
        obtain ⟨hzK, hzAC⟩ := ihz
        refine ⟨KG.mul_mem hyK hzK, ?_⟩
        rw [show (⟨y * z, KG.mul_mem hyK hzK⟩ : ↥KG) = ⟨y, hyK⟩ * ⟨z, hzK⟩ from rfl,
          QuotientGroup.mk_mul]
        exact Subgroup.mul_mem _ hyAC hzAC
      | inv y hy ihy =>
        obtain ⟨hyK, hyAC⟩ := ihy
        refine ⟨KG.inv_mem hyK, ?_⟩
        rw [show (⟨y⁻¹, KG.inv_mem hyK⟩ : ↥KG) = (⟨y, hyK⟩ : ↥KG)⁻¹ from rfl,
          QuotientGroup.mk_inv]
        exact Subgroup.inv_mem _ hyAC
    -- Proposition 1.6(d) core: `C_K(R₀) ∩ ⁅K,R₀⁆ ≤ K'`
    have hCcap : (KG ⊓ Subgroup.centralizer (R₀ : Set G)) ⊓ (⁅KG, R₀⁆ : Subgroup G)
        ≤ ⁅KG, KG⁆ := by
      let : CommGroup (↥KG ⧸ commutator ↥KG) :=
        { (inferInstance : Group (↥KG ⧸ commutator ↥KG)) with mul_comm := hQbar_mul_comm }
      have hCop16 : Nat.Coprime (Nat.card ↥(R₀.subgroupOf A))
          (Nat.card (↥KG ⧸ commutator ↥KG)) := by
        rw [hR₀cardA]
        have hdvd : Nat.card (↥KG ⧸ commutator ↥KG) ∣ Nat.card ↥KG :=
          ⟨Nat.card ↥(commutator ↥KG),
            Subgroup.card_eq_card_quotient_mul_card_subgroup (commutator ↥KG)⟩
        refine Nat.Coprime.coprime_dvd_right hdvd ?_
        obtain ⟨m, hm⟩ := hKGq.exists_card_eq
        rw [hm]
        exact Nat.Coprime.pow_right m
          ((Nat.coprime_primes hr_prime hq_prime).mpr (Ne.symm hq_ne_r))
      have hcompl16 :=
        OddOrder.BG.Ch1.S01.fixedPoints_isComplement_actionCommutator_of_abelian
          (φ := φAQ.comp (R₀.subgroupOf A).subtype) hCop16
      intro x hx
      obtain ⟨hxKC, hxKR⟩ := Subgroup.mem_inf.mp hx
      obtain ⟨hxKG, hxC⟩ := Subgroup.mem_inf.mp hxKC
      obtain ⟨hxK, hxAC⟩ := hbridge x hxKR
      have hxFP : ((⟨x, hxK⟩ : ↥KG) : ↥KG ⧸ commutator ↥KG)
          ∈ Subgroup.fixedPointsOfMulAut (φAQ.comp (R₀.subgroupOf A).subtype) := by
        rw [Subgroup.mem_fixedPointsOfMulAut]
        intro rr
        have h2 := Subgroup.mem_centralizer_iff.mp hxC ((rr : ↥A) : G)
          (Subgroup.mem_subgroupOf.mp rr.2)
        have h1 : φA (rr : ↥A) ⟨x, hxK⟩ = ⟨x, hxK⟩ := by
          apply Subtype.ext
          have h1val : ((φA (rr : ↥A) ⟨x, hxK⟩ : ↥KG) : G)
              = ((rr : ↥A) : G) * x * ((rr : ↥A) : G)⁻¹ := hφA_val _ _
          rw [h1val]
          exact mul_inv_eq_iff_eq_mul.mpr h2
        change ((φA (rr : ↥A) ⟨x, hxK⟩ : ↥KG) : ↥KG ⧸ commutator ↥KG)
          = ((⟨x, hxK⟩ : ↥KG) : ↥KG ⧸ commutator ↥KG)
        rw [h1]
      have h3 : ((⟨x, hxK⟩ : ↥KG) : ↥KG ⧸ commutator ↥KG) = 1 := by
        have h4 : ((⟨x, hxK⟩ : ↥KG) : ↥KG ⧸ commutator ↥KG)
            ∈ Subgroup.fixedPointsOfMulAut (φAQ.comp (R₀.subgroupOf A).subtype)
              ⊓ OddOrder.Isaacs.Ch04.actionCommutator
                (φAQ.comp (R₀.subgroupOf A).subtype) := ⟨hxFP, hxAC⟩
        rwa [hcompl16.disjoint.eq_bot, Subgroup.mem_bot] at h4
      have hxK' : (⟨x, hxK⟩ : ↥KG) ∈ commutator ↥KG := by
        rwa [QuotientGroup.eq_one_iff] at h3
      have hKGder : (commutator ↥KG).map KG.subtype = ⁅KG, KG⁆ := by
        rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
          Subgroup.range_subtype]
      exact hKGder ▸ ⟨⟨x, hxK⟩, hxK', rfl⟩
    -- **(3.32)** `⁅K,R₀⁆ ≠ K`
    have h332 : (⁅KG, R₀⁆ : Subgroup G) ≠ KG := by
      intro heq
      apply h330
      intro x hx
      refine hCcap (Subgroup.mem_inf.mpr ⟨hx, ?_⟩)
      rw [heq]
      exact (Subgroup.mem_inf.mp hx).1
    -- **(3.33)** `C_{⁅K,R₀⁆}(R₀) = ⊥`
    have h333 : (⁅KG, R₀⁆ : Subgroup G) ⊓ Subgroup.centralizer (R₀ : Set G) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨hxKR, hxC⟩ := Subgroup.mem_inf.mp hx
      obtain ⟨hxK, _⟩ := hbridge x hxKR
      have h1 : x ∈ (KG ⊓ Subgroup.centralizer (R₀ : Set G)) ⊓ ⁅KG, KG⁆ :=
        Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hxK, hxC⟩,
          hCcap (Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hxK, hxC⟩, hxKR⟩)⟩
      rwa [h331b] at h1
    -- ===== (3.34) `⁅K,R₀⁆` is abelian (Lemma 3.1 + **Theorem 3.5**) =====
    -- `T := ⁅K,R₀⁆·R₀` is a Frobenius group: the prime-order complement `R₀` acts without
    -- nontrivial fixed points on the kernel ((3.33)).  `T ≤ S₁` acts faithfully on `V`
    -- ((3.18)) and `dim C_V(R₀) = 1` ((3.19)), so Theorem 3.5 makes the derived subgroup
    -- of `⁅K,R₀⁆` act trivially on `V`, hence vanish.
    have hKR_le_KG : (⁅KG, R₀⁆ : Subgroup G) ≤ KG := by
      rw [Subgroup.commutator_le]
      intro g₁ hg₁ g₂ hg₂
      rw [commutatorElement_def, mul_assoc g₁ g₂ g₁⁻¹, mul_assoc g₁]
      exact KG.mul_mem hg₁
        ((Subgroup.mem_normalizer_iff.mp (hR₀_le_NKG hg₂) g₁⁻¹).mp (KG.inv_mem hg₁))
    set T : Subgroup G := (⁅KG, R₀⁆ : Subgroup G) ⊔ R₀ with hTdef
    have hKR_le_T : (⁅KG, R₀⁆ : Subgroup G) ≤ T := le_sup_left
    have hR₀_le_T : R₀ ≤ T := le_sup_right
    have hT_le_NKR : T ≤ Subgroup.normalizer ((⁅KG, R₀⁆ : Subgroup G) : Set G) := by
      rw [hTdef]
      exact sup_le Subgroup.le_normalizer
        (OddOrder.Isaacs.Ch04.subgroup_le_normalizer_commutator_self_right KG R₀)
    have hKRnormT : ((⁅KG, R₀⁆ : Subgroup G).subgroupOf T).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer hT_le_NKR
    have hT_le_S₁ : T ≤ S₁ := by
      rw [hTdef]
      exact sup_le (hKR_le_KG.trans hKG_le_S₁) hR₀_le_S₁
    have hdisjT : Disjoint (⁅KG, R₀⁆ : Subgroup G) R₀ := hdisjKR.mono_left hKR_le_KG
    have hR₀cardT : Nat.card ↥(R₀.subgroupOf T) = r :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR₀_le_T).toEquiv).trans hr_card
    have hcomplT : Subgroup.IsComplement'
        ((⁅KG, R₀⁆ : Subgroup G).subgroupOf T) (R₀.subgroupOf T) := by
      refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
      · refine disjoint_iff.mpr (eq_bot_iff.mpr fun x hx => ?_)
        rw [Subgroup.mem_inf] at hx
        simp only [Subgroup.mem_subgroupOf] at hx
        have hmem : (x : G) ∈ (⁅KG, R₀⁆ : Subgroup G) ⊓ R₀ := ⟨hx.1, hx.2⟩
        rw [hdisjT.eq_bot, Subgroup.mem_bot] at hmem
        rw [Subgroup.mem_bot]
        exact Subtype.ext (by simpa using hmem)
      · have hsup : (((⁅KG, R₀⁆ : Subgroup G).subgroupOf T) : Subgroup ↥T)
            ⊔ (R₀.subgroupOf T) = ⊤ := by
          rw [← Subgroup.subgroupOf_sup hKR_le_T hR₀_le_T, ← hTdef,
            Subgroup.subgroupOf_self]
        have hmul := Subgroup.normal_mul
          (((⁅KG, R₀⁆ : Subgroup G).subgroupOf T) : Subgroup ↥T) (R₀.subgroupOf T)
        rw [hsup, Subgroup.coe_top] at hmul
        exact hmul.symm
    have hKR_ne_bot : (⁅KG, R₀⁆ : Subgroup G) ≠ ⊥ := by
      intro hbot
      exact h317 (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot)
    have hKRT_ne_bot : ((⁅KG, R₀⁆ : Subgroup G).subgroupOf T) ≠ ⊥ := by
      intro hbot
      have h2 : (⁅KG, R₀⁆ : Subgroup G) ⊓ T = ⊥ := by
        rw [← Subgroup.subgroupOf_map_subtype, hbot, Subgroup.map_bot]
      rw [inf_eq_left.mpr hKR_le_T] at h2
      exact hKR_ne_bot h2
    have hFixT : ∀ k ∈ ((⁅KG, R₀⁆ : Subgroup G).subgroupOf T),
        (∀ s ∈ R₀.subgroupOf T, s * k * s⁻¹ = k) → k = 1 := by
      intro k hk hfix
      have hkKR : (k : G) ∈ (⁅KG, R₀⁆ : Subgroup G) := Subgroup.mem_subgroupOf.mp hk
      have hkC : (k : G) ∈ Subgroup.centralizer (R₀ : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro m hm
        have h1 := hfix ⟨m, hR₀_le_T hm⟩ (Subgroup.mem_subgroupOf.mpr hm)
        have h2 : m * (k : G) * m⁻¹ = (k : G) := congrArg Subtype.val h1
        exact mul_inv_eq_iff_eq_mul.mp h2
      have h3 : (k : G) ∈ (⁅KG, R₀⁆ : Subgroup G) ⊓ Subgroup.centralizer (R₀ : Set G) :=
        ⟨hkKR, hkC⟩
      rw [h333, Subgroup.mem_bot] at h3
      exact Subtype.ext h3
    have hrTprime : (Nat.card ↥(R₀.subgroupOf T)).Prime := by
      rw [hR₀cardT]
      exact hr_prime
    have hFrobT := S03d.isFrobeniusGroup_of_prime_complement_fixedFree
      hcomplT hrTprime hKRT_ne_bot hFixT
    -- the conjugation representation of `T` on the `𝔽_p`-space `V_G` ((3.19) pattern)
    have hVGcommT : IsMulCommutative ↥VG := ⟨⟨fun a b => hVGelem.1 a b⟩⟩
    have hpsmulT : ∀ x : Additive ↥VG, (p : ℕ) • x = 0 := by
      intro x
      apply Additive.toMul.injective
      rw [toMul_nsmul, toMul_zero]
      exact hVGelem.2 x.toMul
    have hVGmodT : Module (ZMod p) (Additive ↥VG) := AddCommGroup.zmodModule hpsmulT
    have : Module.Finite (ZMod p) (Additive ↥VG) := Module.Finite.of_finite
    set ρT : Representation (ZMod p) ↥T (Additive ↥VG) :=
      (OddOrder.BG.Ch1_Preliminary.mulAutToEnd ↥VG p).comp
        ((MulAut.conjNormal (G := G) (H := VG)).comp T.subtype) with hρT
    have hρT_apply : ∀ (g : ↥T) (x : Additive ↥VG),
        ρT g x = Additive.ofMul (MulAut.conjNormal (H := VG) (g : G) (Additive.toMul x)) := by
      intro g x
      rfl
    -- the `R₀`-invariants of `ρT` are exactly `C_{V_G}(R₀)`, of order `p` ((3.19)),
    -- hence one-dimensional
    have hmemiffT : ∀ v : Additive ↥VG,
        v ∈ Representation.invariants (ρT.comp (R₀.subgroupOf T).subtype)
          ↔ ((Additive.toMul v : ↥VG) : G) ∈ Subgroup.centralizer (R₀ : Set G) := by
      intro v
      rw [Representation.mem_invariants]
      constructor
      · intro hv
        rw [Subgroup.mem_centralizer_iff]
        intro m hm
        have h1 : Additive.ofMul (MulAut.conjNormal (H := VG) m (Additive.toMul v)) = v :=
          hv ⟨⟨m, hR₀_le_T hm⟩, Subgroup.mem_subgroupOf.mpr hm⟩
        have h2 := congrArg Additive.toMul h1
        rw [toMul_ofMul] at h2
        have h3 := congrArg Subtype.val h2
        rw [MulAut.conjNormal_apply] at h3
        exact mul_inv_eq_iff_eq_mul.mp h3
      · intro hc rr
        have h2 := Subgroup.mem_centralizer_iff.mp hc ((rr : ↥T) : G)
          (Subgroup.mem_subgroupOf.mp rr.2)
        change ρT ((rr : ↥T)) v = v
        rw [hρT_apply]
        apply Additive.toMul.injective
        rw [toMul_ofMul]
        apply Subtype.ext
        rw [MulAut.conjNormal_apply]
        exact mul_inv_eq_iff_eq_mul.mpr h2
    have hinv_card : Nat.card
        ↥(Representation.invariants (ρT.comp (R₀.subgroupOf T).subtype)) = p := by
      refine (Nat.card_congr ((Equiv.subtypeEquiv (Additive.toMul (α := ↥VG))
        (q := fun w : ↥VG => (w : G) ∈ Subgroup.centralizer (R₀ : Set G))
        fun v => hmemiffT v).trans ?_)).trans h319
      exact ⟨fun w => ⟨(w.1 : G), Subgroup.mem_inf.mpr ⟨w.1.2, w.2⟩⟩,
        fun z => ⟨⟨(z : G), (Subgroup.mem_inf.mp z.2).1⟩, (Subgroup.mem_inf.mp z.2).2⟩,
        fun w => by apply Subtype.ext; apply Subtype.ext; rfl,
        fun z => by apply Subtype.ext; rfl⟩
    have hCV1T : Module.finrank (ZMod p)
        ↥(Representation.invariants (ρT.comp (R₀.subgroupOf T).subtype)) = 1 := by
      have : Fintype ↥(Representation.invariants (ρT.comp (R₀.subgroupOf T).subtype)) :=
        Fintype.ofFinite _
      have h2 : Nat.card
          ↥(Representation.invariants (ρT.comp (R₀.subgroupOf T).subtype))
          = p ^ Module.finrank (ZMod p)
            ↥(Representation.invariants (ρT.comp (R₀.subgroupOf T).subtype)) := by
        rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod p), ZMod.card]
      rw [hinv_card] at h2
      have h3 : p ^ 1 = p ^ Module.finrank (ZMod p)
          ↥(Representation.invariants (ρT.comp (R₀.subgroupOf T).subtype)) := by
        rw [pow_one]
        exact h2
      exact (Nat.pow_right_injective hp.two_le h3).symm
    have hcharT : (Nat.card ↥T : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hdvd
      have hcardT : Nat.card ↥T
          = Nat.card ↥(⁅KG, R₀⁆ : Subgroup G) * Nat.card ↥R₀ := by
        rw [hTdef]
        exact card_sup_of_le_normalizer_of_disjoint
          (fun g hg =>
            OddOrder.Isaacs.Ch04.subgroup_le_normalizer_commutator_self_right KG R₀ hg)
          hdisjT
      rw [hcardT, hr_card] at hdvd
      rcases (Nat.Prime.dvd_mul hp).mp hdvd with h4 | h4
      · obtain ⟨m, hm⟩ := hKGq.exists_card_eq
        have h5 : p ∣ q ^ m := by
          rw [← hm]
          exact h4.trans (Subgroup.card_dvd_of_le hKR_le_KG)
        exact hq_ne_p
          ((Nat.prime_dvd_prime_iff_eq hp hq_prime).mp (hp.dvd_of_dvd_pow h5)).symm
      · exact hpr ((Nat.prime_dvd_prime_iff_eq hp hr_prime).mp h4)
    have hthm35 := S03e.thm35 ρT ((⁅KG, R₀⁆ : Subgroup G).subgroupOf T)
      (R₀.subgroupOf T) hFrobT inferInstance ⟨r, hr_prime, hR₀cardT⟩ hcharT hCV1T
    -- push the conclusion down to `G`: `⁅⁅K,R₀⁆,⁅K,R₀⁆⁆` centralises `V`, hence dies ((3.18))
    have h334 : (⁅(⁅KG, R₀⁆ : Subgroup G), (⁅KG, R₀⁆ : Subgroup G)⁆ : Subgroup G) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hsubT : (⁅(⁅KG, R₀⁆ : Subgroup G), (⁅KG, R₀⁆ : Subgroup G)⁆ : Subgroup G)
          ≤ T := by
        rw [Subgroup.commutator_le]
        intro g₁ hg₁ g₂ hg₂
        have h1 : g₁ ∈ T := hKR_le_T hg₁
        have h2 : g₂ ∈ T := hKR_le_T hg₂
        rw [commutatorElement_def]
        exact T.mul_mem (T.mul_mem (T.mul_mem h1 h2) (T.inv_mem h1)) (T.inv_mem h2)
      have hxT : x ∈ T := hsubT hx
      have hmapeqT : (⁅((⁅KG, R₀⁆ : Subgroup G).subgroupOf T : Subgroup ↥T),
          (⁅KG, R₀⁆ : Subgroup G).subgroupOf T⁆ : Subgroup ↥T).map T.subtype
          = ⁅(⁅KG, R₀⁆ : Subgroup G), (⁅KG, R₀⁆ : Subgroup G)⁆ := by
        rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype,
          inf_eq_left.mpr hKR_le_T]
      have hx' : (⟨x, hxT⟩ : ↥T) ∈ (⁅((⁅KG, R₀⁆ : Subgroup G).subgroupOf T : Subgroup ↥T),
          (⁅KG, R₀⁆ : Subgroup G).subgroupOf T⁆ : Subgroup ↥T) := by
        have hmem : x ∈ (⁅((⁅KG, R₀⁆ : Subgroup G).subgroupOf T : Subgroup ↥T),
            (⁅KG, R₀⁆ : Subgroup G).subgroupOf T⁆ : Subgroup ↥T).map T.subtype :=
          hmapeqT.symm ▸ hx
        obtain ⟨z, hz, hzx⟩ := hmem
        rwa [show z = ⟨x, hxT⟩ from Subtype.ext hzx] at hz
      have hρ1 : ρT ⟨x, hxT⟩ = 1 := hthm35 _ hx'
      have hxc : x ∈ Subgroup.centralizer (VG : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have hx1 := DFunLike.congr_fun hρ1 (Additive.ofMul (⟨y, hy⟩ : ↥VG))
        rw [hρT_apply, Module.End.one_apply] at hx1
        have hcoe := congrArg Subtype.val (Additive.ofMul.injective hx1)
        rw [MulAut.conjNormal_apply] at hcoe
        exact (mul_inv_eq_iff_eq_mul.mp hcoe).symm
      have hfin : x ∈ S₁ ⊓ Subgroup.centralizer (VG : Set G) := ⟨hT_le_S₁ hxT, hxc⟩
      rwa [h318] at hfin
    -- ===== (3.35) some `x ∈ P` moves `⁅K,R₀⁆` =====
    -- Otherwise `⁅K,R₀⁆` is a proper ((3.32)) `PR₀`-invariant subgroup of `K`, so `P`
    -- centralises it ((3.22)').  Its image in `K/K'` then lies in `C_{K/K'}(P)`, which is
    -- trivial: `K = ⁅K,P⁆` ((3.24)) makes the `P`-action commutator on `K/K'` everything,
    -- and Proposition 1.6(d) complements it against the fixed points.  Hence
    -- `⁅K,R₀⁆ ≤ K'`, so `R₀` acts trivially on `K/K'` and (3.29) kills `R₀` — absurd.
    -- (This route replaces BG's appeal to the second statement of (3.25) and Theorem 1.8.)
    have h335 : ∃ x ∈ (P.map H.subtype : Subgroup G),
        (⁅KG, R₀⁆ : Subgroup G).map (MulAut.conj x).toMonoidHom ≠ ⁅KG, R₀⁆ := by
      by_contra hcon
      push Not at hcon
      have hPG_le_NKR : (P.map H.subtype : Subgroup G)
          ≤ Subgroup.normalizer ((⁅KG, R₀⁆ : Subgroup G) : Set G) := fun x hx =>
        mem_normalizer_of_map_conj_eq (hcon x hx)
      -- `P` centralises `⁅K,R₀⁆` by the unconditional (3.22)
      have hKRP_bot : (⁅(⁅KG, R₀⁆ : Subgroup G), (P.map H.subtype : Subgroup G)⁆
          : Subgroup G) = ⊥ :=
        h322' _ hKR_le_KG h332
          (fun g hg =>
            OddOrder.Isaacs.Ch04.subgroup_le_normalizer_commutator_self_right KG R₀ hg)
          hPG_le_NKR
      -- the `P`-action commutator on `K/K'` is everything (`K = ⁅K,P⁆`, (3.24))
      have hbridgeP : ∀ x ∈ (⁅KG, (P.map H.subtype : Subgroup G)⁆ : Subgroup G),
          ∃ hxK : x ∈ KG,
          ((⟨x, hxK⟩ : ↥KG) : ↥KG ⧸ commutator ↥KG) ∈
            OddOrder.Isaacs.Ch04.actionCommutator
              (φAQ.comp ((P.map H.subtype).subgroupOf A).subtype) := by
        intro x hx
        rw [Subgroup.commutator_def] at hx
        induction hx using Subgroup.closure_induction with
        | mem y hy =>
          obtain ⟨g₁, hg₁, g₂, hg₂, rfl⟩ := hy
          have hg₂A : g₂ ∈ A := hPG_le_A hg₂
          have hyK : ⁅g₁, g₂⁆ ∈ KG := by
            rw [commutatorElement_def, mul_assoc g₁ g₂ g₁⁻¹, mul_assoc g₁]
            refine KG.mul_mem hg₁ ?_
            exact (Subgroup.mem_normalizer_iff.mp (hPG_le_NKG hg₂) g₁⁻¹).mp
              (KG.inv_mem hg₁)
          refine ⟨hyK, Subgroup.subset_closure ?_⟩
          refine ⟨((⟨g₁, hg₁⟩ : ↥KG) : ↥KG ⧸ commutator ↥KG),
            ⟨⟨g₂, hg₂A⟩, Subgroup.mem_subgroupOf.mpr hg₂⟩, ?_⟩
          have hval : (⟨⁅g₁, g₂⁆, hyK⟩ : ↥KG)
              = ⟨g₁, hg₁⟩ * φA ⟨g₂, hg₂A⟩ (⟨g₁, hg₁⟩ : ↥KG)⁻¹ := by
            apply Subtype.ext
            have h1 : ((φA ⟨g₂, hg₂A⟩ ((⟨g₁, hg₁⟩ : ↥KG)⁻¹) : ↥KG) : G)
                = g₂ * g₁⁻¹ * g₂⁻¹ := hφA_val _ _
            change ⁅g₁, g₂⁆
              = ((⟨g₁, hg₁⟩ * φA ⟨g₂, hg₂A⟩ (⟨g₁, hg₁⟩ : ↥KG)⁻¹ : ↥KG) : G)
            rw [Subgroup.coe_mul, h1, commutatorElement_def,
              mul_assoc g₁ g₂ g₁⁻¹, mul_assoc g₁]
          rw [hval]
          rfl
        | one =>
          exact ⟨KG.one_mem, by
            rw [show (⟨(1 : G), KG.one_mem⟩ : ↥KG) = 1 from rfl, QuotientGroup.mk_one]
            exact Subgroup.one_mem _⟩
        | mul y z hy hz ihy ihz =>
          obtain ⟨hyK, hyAC⟩ := ihy
          obtain ⟨hzK, hzAC⟩ := ihz
          refine ⟨KG.mul_mem hyK hzK, ?_⟩
          rw [show (⟨y * z, KG.mul_mem hyK hzK⟩ : ↥KG) = ⟨y, hyK⟩ * ⟨z, hzK⟩ from rfl,
            QuotientGroup.mk_mul]
          exact Subgroup.mul_mem _ hyAC hzAC
        | inv y hy ihy =>
          obtain ⟨hyK, hyAC⟩ := ihy
          refine ⟨KG.inv_mem hyK, ?_⟩
          rw [show (⟨y⁻¹, KG.inv_mem hyK⟩ : ↥KG) = (⟨y, hyK⟩ : ↥KG)⁻¹ from rfl,
            QuotientGroup.mk_inv]
          exact Subgroup.inv_mem _ hyAC
      have hACP_top : OddOrder.Isaacs.Ch04.actionCommutator
          (φAQ.comp ((P.map H.subtype).subgroupOf A).subtype) = ⊤ := by
        rw [eq_top_iff]
        intro kq _
        obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective kq
        have hkKR : (k : G) ∈ (⁅KG, (P.map H.subtype : Subgroup G)⁆ : Subgroup G) := by
          rw [h324]
          exact k.2
        obtain ⟨hxK, hAC⟩ := hbridgeP _ hkKR
        rwa [show (⟨(k : G), hxK⟩ : ↥KG) = k from Subtype.ext rfl] at hAC
      have hFPP_bot : Subgroup.fixedPointsOfMulAut
          (φAQ.comp ((P.map H.subtype).subgroupOf A).subtype) = ⊥ := by
        let : CommGroup (↥KG ⧸ commutator ↥KG) :=
          { (inferInstance : Group (↥KG ⧸ commutator ↥KG)) with
            mul_comm := hQbar_mul_comm }
        have hCopP : Nat.Coprime (Nat.card ↥((P.map H.subtype).subgroupOf A))
            (Nat.card (↥KG ⧸ commutator ↥KG)) := by
          have hdvd : Nat.card (↥KG ⧸ commutator ↥KG) ∣ Nat.card ↥KG :=
            ⟨Nat.card ↥(commutator ↥KG),
              Subgroup.card_eq_card_quotient_mul_card_subgroup (commutator ↥KG)⟩
          refine Nat.Coprime.coprime_dvd_right hdvd ?_
          have hPGcardA' : Nat.card ↥((P.map H.subtype).subgroupOf A)
              = Nat.card ↥(P.map H.subtype : Subgroup G) :=
            Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPG_le_A).toEquiv
          obtain ⟨m, hm⟩ := hKGq.exists_card_eq
          obtain ⟨k2, hk2⟩ := (hPp.map H.subtype).exists_card_eq
          rw [hm, hPGcardA', hk2]
          exact Nat.Coprime.pow_left k2 (Nat.Coprime.pow_right m
            ((Nat.coprime_primes hp hq_prime).mpr (Ne.symm hq_ne_p)))
        have hcomplP :=
          OddOrder.BG.Ch1.S01.fixedPoints_isComplement_actionCommutator_of_abelian
            (φ := φAQ.comp ((P.map H.subtype).subgroupOf A).subtype) hCopP
        rw [hACP_top] at hcomplP
        exact Subgroup.isComplement'_top_right.mp hcomplP
      -- `⁅K,R₀⁆` maps to `1` in `K/K'`
      have hKR_mk_one : ∀ x (_ : x ∈ (⁅KG, R₀⁆ : Subgroup G)) (hxK : x ∈ KG),
          ((⟨x, hxK⟩ : ↥KG) : ↥KG ⧸ commutator ↥KG) = 1 := by
        intro x hxKR hxK
        have hxcent : x ∈ Subgroup.centralizer
            ((P.map H.subtype : Subgroup G) : Set G) :=
          Subgroup.commutator_eq_bot_iff_le_centralizer.mp hKRP_bot hxKR
        have hxFPP : ((⟨x, hxK⟩ : ↥KG) : ↥KG ⧸ commutator ↥KG)
            ∈ Subgroup.fixedPointsOfMulAut
              (φAQ.comp ((P.map H.subtype).subgroupOf A).subtype) := by
          rw [Subgroup.mem_fixedPointsOfMulAut]
          intro pp
          have h2 := Subgroup.mem_centralizer_iff.mp hxcent ((pp : ↥A) : G)
            (Subgroup.mem_subgroupOf.mp pp.2)
          have h1 : φA (pp : ↥A) ⟨x, hxK⟩ = ⟨x, hxK⟩ := by
            apply Subtype.ext
            have h1val : ((φA (pp : ↥A) ⟨x, hxK⟩ : ↥KG) : G)
                = ((pp : ↥A) : G) * x * ((pp : ↥A) : G)⁻¹ := hφA_val _ _
            rw [h1val]
            exact mul_inv_eq_iff_eq_mul.mpr h2
          change ((φA (pp : ↥A) ⟨x, hxK⟩ : ↥KG) : ↥KG ⧸ commutator ↥KG)
            = ((⟨x, hxK⟩ : ↥KG) : ↥KG ⧸ commutator ↥KG)
          rw [h1]
        have h3 : ((⟨x, hxK⟩ : ↥KG) : ↥KG ⧸ commutator ↥KG) ∈ (⊥ : Subgroup _) := by
          rw [← hFPP_bot]
          exact hxFPP
        rwa [Subgroup.mem_bot] at h3
      -- `R₀` acts trivially on `K/K'`; (3.29) then forces `R₀ = ⊥`, absurd
      have hR₀bot : R₀ = ⊥ := by
        rw [eq_bot_iff]
        intro a ha
        rw [Subgroup.mem_bot]
        have haA : a ∈ A := hR₀_le_A ha
        have h1 : (⟨a, haA⟩ : ↥A) = 1 := by
          refine h329 _ fun kq => ?_
          obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective kq
          have hwmem : ((φA ⟨a, haA⟩ k * k⁻¹ : ↥KG) : G) ∈ (⁅KG, R₀⁆ : Subgroup G) := by
            have hval2 : ((φA ⟨a, haA⟩ k * k⁻¹ : ↥KG) : G) = ⁅a, (k : G)⁆ := by
              rw [Subgroup.coe_mul]
              have h4 : ((φA ⟨a, haA⟩ k : ↥KG) : G) = a * (k : G) * a⁻¹ := hφA_val _ _
              rw [h4, Subgroup.coe_inv, commutatorElement_def]
            rw [hval2, Subgroup.commutator_comm]
            exact Subgroup.commutator_mem_commutator ha k.2
          have hw_one : ((φA ⟨a, haA⟩ k * k⁻¹ : ↥KG) : ↥KG ⧸ commutator ↥KG) = 1 :=
            hKR_mk_one _ hwmem (φA ⟨a, haA⟩ k * k⁻¹ : ↥KG).2
          change ((φA ⟨a, haA⟩ k : ↥KG) : ↥KG ⧸ commutator ↥KG)
            = ((k : ↥KG) : ↥KG ⧸ commutator ↥KG)
          calc ((φA ⟨a, haA⟩ k : ↥KG) : ↥KG ⧸ commutator ↥KG)
              = (((φA ⟨a, haA⟩ k * k⁻¹) * k : ↥KG) : ↥KG ⧸ commutator ↥KG) := by
                rw [inv_mul_cancel_right]
            _ = ((φA ⟨a, haA⟩ k * k⁻¹ : ↥KG) : ↥KG ⧸ commutator ↥KG)
                * ((k : ↥KG) : ↥KG ⧸ commutator ↥KG) := by rw [QuotientGroup.mk_mul]
            _ = ((k : ↥KG) : ↥KG ⧸ commutator ↥KG) := by rw [hw_one, one_mul]
        exact congrArg Subtype.val h1
      rw [hR₀bot, Subgroup.card_bot] at hr_card
      exact hr_prime.one_lt.ne' hr_card.symm
    -- ===== (3.36) `K` is elementary abelian =====
    -- Step 1: `|K| = |⁅K,R₀⁆|·q`.  Proposition 1.6(a) (the general coprime form
    -- `K = C_K(R₀)·⁅K,R₀⁆`) with the two factors intersecting trivially ((3.33));
    -- `|C_K(R₀)| = q` by (3.31).
    obtain ⟨x, hxPG, hx_ne⟩ := h335
    set φAR : ↥(R₀.subgroupOf A) →* MulAut ↥KG := φA.comp (R₀.subgroupOf A).subtype
      with hφARdef
    have hcopRK36 : Nat.Coprime (Nat.card ↥(R₀.subgroupOf A)) (Nat.card ↥KG) := by
      rw [hR₀cardA]
      obtain ⟨m, hm⟩ := hKGq.exists_card_eq
      rw [hm]
      exact Nat.Coprime.pow_right m
        ((Nat.coprime_primes hr_prime hq_prime).mpr (Ne.symm hq_ne_r))
    have hsupK : Subgroup.fixedPointsOfMulAut φAR
        ⊔ OddOrder.Isaacs.Ch04.actionCommutator φAR = ⊤ :=
      OddOrder.Isaacs.Ch04.fixedPoints_sup_actionCommutator_eq_top hcopRK36
        (Or.inr inferInstance)
    -- the fixed points are `C_K(R₀)`
    have hFPval : Subgroup.fixedPointsOfMulAut φAR
        = (KG ⊓ Subgroup.centralizer (R₀ : Set G)).subgroupOf KG := by
      ext w
      rw [Subgroup.mem_fixedPointsOfMulAut, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      constructor
      · intro hw
        refine ⟨w.2, Subgroup.mem_centralizer_iff.mpr fun m hm => ?_⟩
        have hmA : m ∈ A := hR₀_le_A hm
        have h1 := hw ⟨⟨m, hmA⟩, Subgroup.mem_subgroupOf.mpr hm⟩
        have h2 : m * (w : G) * m⁻¹ = (w : G) :=
          (hφA_val ⟨m, hmA⟩ w).symm.trans (congrArg Subtype.val h1)
        exact mul_inv_eq_iff_eq_mul.mp h2
      · rintro ⟨-, hwC⟩
        intro rr
        have h2 := Subgroup.mem_centralizer_iff.mp hwC ((rr : ↥A) : G)
          (Subgroup.mem_subgroupOf.mp rr.2)
        apply Subtype.ext
        have h1val : ((φAR rr w : ↥KG) : G)
            = ((rr : ↥A) : G) * (w : G) * ((rr : ↥A) : G)⁻¹ := hφA_val _ _
        rw [h1val]
        exact mul_inv_eq_iff_eq_mul.mpr h2
    -- the action commutator is `⁅K,R₀⁆`
    have hbridgeK : ∀ y ∈ (⁅KG, R₀⁆ : Subgroup G), ∃ hyK : y ∈ KG,
        (⟨y, hyK⟩ : ↥KG) ∈ OddOrder.Isaacs.Ch04.actionCommutator φAR := by
      intro y hy
      rw [Subgroup.commutator_def] at hy
      induction hy using Subgroup.closure_induction with
      | mem z hz =>
        obtain ⟨g₁, hg₁, g₂, hg₂, rfl⟩ := hz
        have hg₂A : g₂ ∈ A := hR₀_le_A hg₂
        have hzK : ⁅g₁, g₂⁆ ∈ KG := by
          rw [commutatorElement_def, mul_assoc g₁ g₂ g₁⁻¹, mul_assoc g₁]
          refine KG.mul_mem hg₁ ?_
          exact (Subgroup.mem_normalizer_iff.mp (hR₀_le_NKG hg₂) g₁⁻¹).mp
            (KG.inv_mem hg₁)
        refine ⟨hzK, Subgroup.subset_closure ?_⟩
        refine ⟨⟨g₁, hg₁⟩, ⟨⟨g₂, hg₂A⟩, Subgroup.mem_subgroupOf.mpr hg₂⟩, ?_⟩
        apply Subtype.ext
        have h1 : ((φA ⟨g₂, hg₂A⟩ ((⟨g₁, hg₁⟩ : ↥KG)⁻¹) : ↥KG) : G)
            = g₂ * g₁⁻¹ * g₂⁻¹ := hφA_val _ _
        change ⁅g₁, g₂⁆
          = ((⟨g₁, hg₁⟩ * φA ⟨g₂, hg₂A⟩ (⟨g₁, hg₁⟩ : ↥KG)⁻¹ : ↥KG) : G)
        rw [Subgroup.coe_mul, h1, commutatorElement_def,
          mul_assoc g₁ g₂ g₁⁻¹, mul_assoc g₁]
      | one =>
        exact ⟨KG.one_mem, by
          rw [show (⟨(1 : G), KG.one_mem⟩ : ↥KG) = 1 from rfl]
          exact Subgroup.one_mem _⟩
      | mul y z hy hz ihy ihz =>
        obtain ⟨hyK, hyAC⟩ := ihy
        obtain ⟨hzK, hzAC⟩ := ihz
        refine ⟨KG.mul_mem hyK hzK, ?_⟩
        rw [show (⟨y * z, KG.mul_mem hyK hzK⟩ : ↥KG) = ⟨y, hyK⟩ * ⟨z, hzK⟩ from rfl]
        exact Subgroup.mul_mem _ hyAC hzAC
      | inv y hy ihy =>
        obtain ⟨hyK, hyAC⟩ := ihy
        refine ⟨KG.inv_mem hyK, ?_⟩
        rw [show (⟨y⁻¹, KG.inv_mem hyK⟩ : ↥KG) = (⟨y, hyK⟩ : ↥KG)⁻¹ from rfl]
        exact Subgroup.inv_mem _ hyAC
    have hACval : OddOrder.Isaacs.Ch04.actionCommutator φAR
        = (⁅KG, R₀⁆ : Subgroup G).subgroupOf KG := by
      apply le_antisymm
      · rw [OddOrder.Isaacs.Ch04.actionCommutator, Subgroup.closure_le]
        rintro _ ⟨g, rr, rfl⟩
        rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
        have hval : ((g * (φAR rr) g⁻¹ : ↥KG) : G)
            = ⁅(g : G), ((rr : ↥A) : G)⁆ := by
          have h1 : (((φAR rr) g⁻¹ : ↥KG) : G)
              = ((rr : ↥A) : G) * (g : G)⁻¹ * ((rr : ↥A) : G)⁻¹ := hφA_val _ _
          rw [Subgroup.coe_mul, h1, commutatorElement_def,
            mul_assoc (g : G) (((rr : ↥A) : G)) (g : G)⁻¹, mul_assoc (g : G)]
        rw [hval]
        exact Subgroup.commutator_mem_commutator g.2 (Subgroup.mem_subgroupOf.mp rr.2)
      · intro w hw
        obtain ⟨hxK, hin⟩ := hbridgeK (w : G) (Subgroup.mem_subgroupOf.mp hw)
        rwa [show (⟨(w : G), hxK⟩ : ↥KG) = w from Subtype.ext rfl] at hin
    rw [hFPval, hACval, sup_comm] at hsupK
    -- the two factors intersect trivially ((3.33))
    have hdisjCK : Disjoint ((⁅KG, R₀⁆ : Subgroup G).subgroupOf KG)
        ((KG ⊓ Subgroup.centralizer (R₀ : Set G)).subgroupOf KG) := by
      rw [disjoint_iff, eq_bot_iff]
      intro w hw
      rw [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at hw
      have h1 : (w : G) ∈ (⁅KG, R₀⁆ : Subgroup G) ⊓ Subgroup.centralizer (R₀ : Set G) :=
        ⟨hw.1, (Subgroup.mem_inf.mp hw.2).2⟩
      rw [h333, Subgroup.mem_bot] at h1
      rw [Subgroup.mem_bot]
      exact Subtype.ext h1
    -- `⁅K,R₀⁆ ⊴ K`
    have hKG_le_NKR : KG ≤ Subgroup.normalizer ((⁅KG, R₀⁆ : Subgroup G) : Set G) :=
      OddOrder.Isaacs.Ch04.subgroup_le_normalizer_commutator_self KG R₀
    have hKRsnorm : ((⁅KG, R₀⁆ : Subgroup G).subgroupOf KG).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer hKG_le_NKR
    -- `|K| = |⁅K,R₀⁆|·q`
    have hCs_card : Nat.card ↥((KG ⊓ Subgroup.centralizer (R₀ : Set G)).subgroupOf KG)
        = q :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv).trans h331a
    have hKRs_card : Nat.card ↥((⁅KG, R₀⁆ : Subgroup G).subgroupOf KG)
        = Nat.card ↥(⁅KG, R₀⁆ : Subgroup G) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKR_le_KG).toEquiv
    have hKGcard36 : Nat.card ↥KG
        = Nat.card ↥((⁅KG, R₀⁆ : Subgroup G).subgroupOf KG) * q := by
      have h2 := card_sup_of_le_normalizer_of_disjoint
        (A := (⁅KG, R₀⁆ : Subgroup G).subgroupOf KG)
        (B := (KG ⊓ Subgroup.centralizer (R₀ : Set G)).subgroupOf KG)
        (by
          intro g _
          rw [Subgroup.normalizer_eq_top]
          trivial)
        hdisjCK
      rw [hsupK, hCs_card] at h2
      calc Nat.card ↥KG = Nat.card ↥(⊤ : Subgroup ↥KG) :=
            (Nat.card_congr Subgroup.topEquiv.toEquiv).symm
        _ = _ := h2
    have hKRs_index : ((⁅KG, R₀⁆ : Subgroup G).subgroupOf KG).index = q := by
      have h3 := Subgroup.index_mul_card ((⁅KG, R₀⁆ : Subgroup G).subgroupOf KG)
      rw [hKGcard36, mul_comm (Nat.card ↥((⁅KG, R₀⁆ : Subgroup G).subgroupOf KG)) q]
        at h3
      have hpos : 0 < Nat.card ↥((⁅KG, R₀⁆ : Subgroup G).subgroupOf KG) := Nat.card_pos
      exact Nat.eq_of_mul_eq_mul_right hpos h3
    -- Step 2: the conjugate `⁅K,R₀⁆ˣ` is a second abelian normal subgroup of index `q`,
    -- distinct from `⁅K,R₀⁆` ((3.35)); together they generate `K` and their intersection
    -- is central, so `|K : Z(K)| ≤ q²`.
    set KRx : Subgroup G := (⁅KG, R₀⁆ : Subgroup G).map (MulAut.conj x).toMonoidHom
      with hKRxdef
    have hKRx_le_KG : KRx ≤ KG := by
      rw [hKRxdef]
      have h1 : (⁅KG, R₀⁆ : Subgroup G).map (MulAut.conj x).toMonoidHom
          ≤ KG.map (MulAut.conj x).toMonoidHom := Subgroup.map_mono hKR_le_KG
      rwa [map_conj_eq_self_of_mem_normalizer (hPG_le_NKG hxPG)] at h1
    have hKRx_card : Nat.card ↥KRx = Nat.card ↥(⁅KG, R₀⁆ : Subgroup G) := by
      rw [hKRxdef]
      exact Subgroup.card_map_of_injective (MulAut.conj x).injective
    have h334x : (⁅KRx, KRx⁆ : Subgroup G) = ⊥ := by
      rw [hKRxdef, ← Subgroup.map_commutator, h334, Subgroup.map_bot]
    -- composition law for conjugation maps
    have hcomp : ∀ a b : G,
        ((⁅KG, R₀⁆ : Subgroup G).map (MulAut.conj b).toMonoidHom).map
          (MulAut.conj a).toMonoidHom
        = (⁅KG, R₀⁆ : Subgroup G).map (MulAut.conj (a * b)).toMonoidHom := by
      intro a b
      rw [Subgroup.map_map]
      congr 1
      ext z
      simp [MulAut.conj_apply, mul_assoc]
    have hKG_le_NKRx : KG ≤ Subgroup.normalizer (KRx : Set G) := by
      intro g hg
      have hy : x⁻¹ * g * x ∈ KG := by
        refine (Subgroup.mem_normalizer_iff.mp (hPG_le_NKG hxPG) (x⁻¹ * g * x)).mpr ?_
        have h2 : x * (x⁻¹ * g * x) * x⁻¹ = g := by group
        rwa [h2]
      refine mem_normalizer_of_map_conj_eq ?_
      have hgx : g * x = x * (x⁻¹ * g * x) := by group
      calc KRx.map (MulAut.conj g).toMonoidHom
          = (⁅KG, R₀⁆ : Subgroup G).map (MulAut.conj (g * x)).toMonoidHom := by
            rw [hKRxdef, hcomp]
        _ = ((⁅KG, R₀⁆ : Subgroup G).map
              (MulAut.conj (x⁻¹ * g * x)).toMonoidHom).map (MulAut.conj x).toMonoidHom := by
            rw [hgx, hcomp]
        _ = (⁅KG, R₀⁆ : Subgroup G).map (MulAut.conj x).toMonoidHom := by
            rw [map_conj_eq_self_of_mem_normalizer (hKG_le_NKR hy)]
        _ = KRx := hKRxdef.symm
    have hKRxsnorm : (KRx.subgroupOf KG).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer hKG_le_NKRx
    have hKRxs_card : Nat.card ↥(KRx.subgroupOf KG)
        = Nat.card ↥(⁅KG, R₀⁆ : Subgroup G) :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKRx_le_KG).toEquiv).trans hKRx_card
    have hKRxs_index : (KRx.subgroupOf KG).index = q := by
      have h3 := Subgroup.index_mul_card (KRx.subgroupOf KG)
      rw [hKRxs_card, ← hKRs_card, hKGcard36,
        mul_comm (Nat.card ↥((⁅KG, R₀⁆ : Subgroup G).subgroupOf KG)) q] at h3
      exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h3
    have hKRs_ne : (⁅KG, R₀⁆ : Subgroup G).subgroupOf KG ≠ KRx.subgroupOf KG := by
      intro heq
      apply hx_ne
      have h1 := congrArg (fun S : Subgroup ↥KG => S.map KG.subtype) heq
      simp only [Subgroup.subgroupOf_map_subtype] at h1
      rw [inf_eq_left.mpr hKR_le_KG, inf_eq_left.mpr hKRx_le_KG] at h1
      exact h1.symm
    -- the two index-`q` normal subgroups generate `K`
    have hsupKK : ((⁅KG, R₀⁆ : Subgroup G).subgroupOf KG) ⊔ (KRx.subgroupOf KG) = ⊤ := by
      by_contra hne
      have hdvd : (((⁅KG, R₀⁆ : Subgroup G).subgroupOf KG) ⊔ (KRx.subgroupOf KG)).index
          ∣ q := by
        rw [← hKRs_index]
        exact Subgroup.index_dvd_of_le le_sup_left
      rcases (Nat.dvd_prime hq_prime).mp hdvd with h1 | h1
      · exact hne (Subgroup.index_eq_one.mp h1)
      · have h2 := Subgroup.index_mul_card (((⁅KG, R₀⁆ : Subgroup G).subgroupOf KG)
          ⊔ (KRx.subgroupOf KG))
        have h3 := Subgroup.index_mul_card ((⁅KG, R₀⁆ : Subgroup G).subgroupOf KG)
        rw [h1] at h2
        rw [hKRs_index] at h3
        have h4 : Nat.card ↥(((⁅KG, R₀⁆ : Subgroup G).subgroupOf KG)
            ⊔ (KRx.subgroupOf KG))
            = Nat.card ↥((⁅KG, R₀⁆ : Subgroup G).subgroupOf KG) :=
          Nat.eq_of_mul_eq_mul_left hq_prime.pos (h2.trans h3.symm)
        have h5 : (⁅KG, R₀⁆ : Subgroup G).subgroupOf KG
            = ((⁅KG, R₀⁆ : Subgroup G).subgroupOf KG) ⊔ (KRx.subgroupOf KG) :=
          Subgroup.eq_of_le_of_card_ge le_sup_left (le_of_eq h4)
        have h6 : KRx.subgroupOf KG ≤ (⁅KG, R₀⁆ : Subgroup G).subgroupOf KG := by
          rw [h5]
          exact le_sup_right
        have h7 : KRx.subgroupOf KG = (⁅KG, R₀⁆ : Subgroup G).subgroupOf KG :=
          Subgroup.eq_of_le_of_card_ge h6 (le_of_eq (hKRs_card.trans hKRxs_card.symm))
        exact hKRs_ne h7.symm
    -- their intersection is central in `K`
    have hZle : ((⁅KG, R₀⁆ : Subgroup G).subgroupOf KG) ⊓ (KRx.subgroupOf KG)
        ≤ Subgroup.center ↥KG := by
      intro z hz
      rw [Subgroup.mem_center_iff]
      intro k
      have hk : k ∈ ((⁅KG, R₀⁆ : Subgroup G).subgroupOf KG) ⊔ (KRx.subgroupOf KG) := by
        rw [hsupKK]
        trivial
      have hmul := Subgroup.normal_mul ((⁅KG, R₀⁆ : Subgroup G).subgroupOf KG)
        (KRx.subgroupOf KG)
      have hkset : k ∈ (((⁅KG, R₀⁆ : Subgroup G).subgroupOf KG : Subgroup ↥KG) : Set ↥KG)
          * ((KRx.subgroupOf KG : Subgroup ↥KG) : Set ↥KG) := by
        rw [← hmul]
        exact hk
      obtain ⟨k₁, hk₁, k₂, hk₂, hkeq⟩ := hkset
      simp only at hkeq
      have hcomm1 : (z : ↥KG) * k₁ = k₁ * z := by
        have h8 : ⁅(z : G), (k₁ : G)⁆ = 1 := by
          have h9 : ⁅(z : G), (k₁ : G)⁆ ∈ (⁅(⁅KG, R₀⁆ : Subgroup G),
              (⁅KG, R₀⁆ : Subgroup G)⁆ : Subgroup G) :=
            Subgroup.commutator_mem_commutator
              (Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp hz).1)
              (Subgroup.mem_subgroupOf.mp hk₁)
          rwa [h334, Subgroup.mem_bot] at h9
        exact Subtype.ext (commutatorElement_eq_one_iff_mul_comm.mp h8)
      have hcomm2 : (z : ↥KG) * k₂ = k₂ * z := by
        have h8 : ⁅(z : G), (k₂ : G)⁆ = 1 := by
          have h9 : ⁅(z : G), (k₂ : G)⁆ ∈ (⁅KRx, KRx⁆ : Subgroup G) :=
            Subgroup.commutator_mem_commutator
              (Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp hz).2)
              (Subgroup.mem_subgroupOf.mp hk₂)
          rwa [h334x, Subgroup.mem_bot] at h9
        exact Subtype.ext (commutatorElement_eq_one_iff_mul_comm.mp h8)
      calc k * z = (k₁ * k₂) * z := by rw [hkeq]
        _ = k₁ * (k₂ * z) := mul_assoc _ _ _
        _ = k₁ * (z * k₂) := by rw [← hcomm2]
        _ = (k₁ * z) * k₂ := (mul_assoc _ _ _).symm
        _ = (z * k₁) * k₂ := by rw [← hcomm1]
        _ = z * (k₁ * k₂) := mul_assoc _ _ _
        _ = z * k := by rw [hkeq]
    -- `|K : Z(K)| = qʲ` with `j ≤ 2`
    have hZind_le : (Subgroup.center ↥KG).index ≤ q * q := by
      have hpos : 0 < (((⁅KG, R₀⁆ : Subgroup G).subgroupOf KG)
          ⊓ (KRx.subgroupOf KG)).index := by
        refine Nat.pos_of_ne_zero fun h0 => ?_
        have h1 := Subgroup.index_mul_card (((⁅KG, R₀⁆ : Subgroup G).subgroupOf KG)
          ⊓ (KRx.subgroupOf KG))
        rw [h0, zero_mul] at h1
        exact Nat.card_pos.ne' h1.symm
      calc (Subgroup.center ↥KG).index
          ≤ (((⁅KG, R₀⁆ : Subgroup G).subgroupOf KG) ⊓ (KRx.subgroupOf KG)).index :=
            Nat.le_of_dvd hpos (Subgroup.index_dvd_of_le hZle)
        _ ≤ ((⁅KG, R₀⁆ : Subgroup G).subgroupOf KG).index * (KRx.subgroupOf KG).index :=
            Subgroup.index_inf_le
        _ = q * q := by rw [hKRs_index, hKRxs_index]
    obtain ⟨j, hjle2, hj⟩ : ∃ j ≤ 2, (Subgroup.center ↥KG).index = q ^ j := by
      obtain ⟨m, hm⟩ := hKGq.exists_card_eq
      obtain ⟨j, hjle, hj⟩ := (Nat.dvd_prime_pow hq_prime).mp
        (show (Subgroup.center ↥KG).index ∣ q ^ m by
          rw [← hm]
          exact Subgroup.index_dvd_card _)
      refine ⟨j, ?_, hj⟩
      by_contra hgt
      push Not at hgt
      have h1 : q ^ 3 ≤ q ^ j := Nat.pow_le_pow_right hq_prime.pos (by omega)
      have h2 : q * q < q ^ 3 := by
        have h3 : q * q = q ^ 2 := (pow_two q).symm
        have h4 : q ^ 2 < q ^ 3 := Nat.pow_lt_pow_right hq_prime.one_lt (by omega)
        omega
      rw [hj] at hZind_le
      omega
    -- the value `j = 2` is impossible: `PR₀` would act faithfully on the 2-dimensional
    -- `𝔽_q`-space `K/K'` and be abelian (**Theorem 2.6(a)**), contradicting (3.21)/(3.13)
    have hj2 : j = 2 → False := by
      intro hj2
      have hZne : Subgroup.center ↥KG ≠ ⊤ := by
        intro htop
        rw [htop, Subgroup.index_top, hj2] at hj
        have h3 : 2 ^ 2 ≤ q ^ 2 :=
          Nat.pow_le_pow_left (Nat.succ_le_of_lt hq_prime.one_lt) 2
        omega
      have hcomm_eq : commutator ↥KG = Subgroup.center ↥KG := by
        rcases hK_special.2 with hEA | ⟨hc, _, _⟩
        · exfalso
          apply hZne
          rw [eq_top_iff]
          intro a _
          rw [Subgroup.mem_center_iff]
          intro b
          exact hEA.1 b a
        · exact hc
      have hQcard : Nat.card (↥KG ⧸ commutator ↥KG) = q ^ 2 := by
        rw [← Subgroup.index_eq_card, hcomm_eq, hj, hj2]
      have hQbar_comm36 : IsMulCommutative (↥KG ⧸ commutator ↥KG) := ⟨⟨hQbar_mul_comm⟩⟩
      have hexpQ36 : ∀ g : ↥KG ⧸ commutator ↥KG, g ^ q = 1 := by
        intro g
        refine QuotientGroup.induction_on g fun k => ?_
        have hk : k ^ q = 1 := by
          rw [← hK_exp]
          exact Monoid.pow_exponent_eq_one k
        rw [← QuotientGroup.mk_pow, hk, QuotientGroup.mk_one]
      have hqsmul36 : ∀ v : Additive (↥KG ⧸ commutator ↥KG), (q : ℕ) • v = 0 := by
        intro v
        apply Additive.toMul.injective
        rw [toMul_nsmul, toMul_zero]
        exact hexpQ36 v.toMul
      have hQmod36 : Module (ZMod q) (Additive (↥KG ⧸ commutator ↥KG)) :=
        AddCommGroup.zmodModule hqsmul36
      have : Module.Finite (ZMod q) (Additive (↥KG ⧸ commutator ↥KG)) :=
        Module.Finite.of_finite
      have hdim2 : Module.finrank (ZMod q) (Additive (↥KG ⧸ commutator ↥KG)) = 2 := by
        have : Fintype (Additive (↥KG ⧸ commutator ↥KG)) := Fintype.ofFinite _
        have h2 : Nat.card (Additive (↥KG ⧸ commutator ↥KG))
            = q ^ Module.finrank (ZMod q) (Additive (↥KG ⧸ commutator ↥KG)) := by
          rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod q),
            ZMod.card]
        have h3 : Nat.card (Additive (↥KG ⧸ commutator ↥KG))
            = Nat.card (↥KG ⧸ commutator ↥KG) := rfl
        rw [h3, hQcard] at h2
        exact Nat.pow_right_injective hq_prime.two_le h2.symm
      set ρ2 : Representation (ZMod q) ↥A (Additive (↥KG ⧸ commutator ↥KG)) :=
        (OddOrder.BG.Ch1_Preliminary.mulAutToEnd (↥KG ⧸ commutator ↥KG) q).comp φAQ
        with hρ2
      have hρ2_apply : ∀ (g : ↥A) (v : Additive (↥KG ⧸ commutator ↥KG)),
          ρ2 g v = Additive.ofMul (φAQ g (Additive.toMul v)) := fun g v => rfl
      have hfaith2 : Function.Injective ρ2 := by
        intro a b hab
        have h1 : ρ2 (a * b⁻¹) = 1 := by
          rw [map_mul, hab, ← map_mul, mul_inv_cancel, map_one]
        have h2 : a * b⁻¹ = 1 := by
          refine h329 _ fun kq => ?_
          have h3 := DFunLike.congr_fun h1 (Additive.ofMul kq)
          rw [hρ2_apply, Module.End.one_apply] at h3
          exact Additive.ofMul.injective h3
        exact mul_inv_eq_one.mp h2
      have hodd_A36 : Odd (Nat.card ↥A) := by
        obtain ⟨m2, hm2⟩ := Subgroup.card_subgroup_dvd_card A
        rw [hm2, Nat.odd_mul] at hodd
        exact hodd.1
      have hchar36 : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ Nat.card ↥A → ¬ CharP (ZMod q) ℓ := by
        intro ℓ hℓ hdvd hcharP
        have hℓq : ℓ = q := CharP.eq (ZMod q) hcharP (ZMod.charP q)
        have hℓpr : ℓ = p ∨ ℓ = r := by
          have h3 : ℓ ∣ Nat.card ↥(P.map H.subtype : Subgroup G) * Nat.card ↥R₀ := by
            rw [← hAcard]
            exact hdvd
          rcases (Nat.Prime.dvd_mul hℓ).mp h3 with h4 | h4
          · left
            obtain ⟨k2, hk2⟩ := (hPp.map H.subtype).exists_card_eq
            rw [hk2] at h4
            exact (Nat.prime_dvd_prime_iff_eq hℓ hp).mp (hℓ.dvd_of_dvd_pow h4)
          · right
            rw [hr_card] at h4
            exact (Nat.prime_dvd_prime_iff_eq hℓ hr_prime).mp h4
        rcases hℓpr with h5 | h5
        · exact hq_ne_p (by rw [← hℓq]; exact h5)
        · exact hq_ne_r (by rw [← hℓq]; exact h5)
      have hAcomm := OddOrder.BG.Ch1.S02.odd_two_dim_abelian hodd_A36 hdim2 ρ2
        hfaith2 hchar36
      have hPGR₀bot : (⁅(P.map H.subtype : Subgroup G), R₀⁆ : Subgroup G) = ⊥ := by
        rw [eq_bot_iff, Subgroup.commutator_le]
        intro g₁ hg₁ g₂ hg₂
        have h6 := hAcomm.comm (⟨g₁, hPG_le_A hg₁⟩ : ↥A) ⟨g₂, hR₀_le_A hg₂⟩
        have h7 : g₁ * g₂ = g₂ * g₁ := congrArg Subtype.val h6
        rw [Subgroup.mem_bot]
        exact commutatorElement_eq_one_iff_mul_comm.mpr h7
      have hPGbot36 : (P.map H.subtype : Subgroup G) = ⊥ := h321G ▸ hPGR₀bot
      apply h313G
      rw [hPGbot36, Subgroup.commutator_bot_right]
    -- so `K/Z(K)` is cyclic and `K` is abelian, hence elementary abelian ((3.26))
    have hj01 : Nat.card (↥KG ⧸ Subgroup.center ↥KG) = q ^ j := by
      rw [← Subgroup.index_eq_card, hj]
    have hcyc : IsCyclic (↥KG ⧸ Subgroup.center ↥KG) := by
      rcases j with _ | _ | _ | j4
      · have : Subsingleton (↥KG ⧸ Subgroup.center ↥KG) := by
          rw [pow_zero] at hj01
          exact (Nat.card_eq_one_iff_unique.mp hj01).1
        exact isCyclic_of_subsingleton
      · rw [pow_one] at hj01
        exact isCyclic_of_prime_card hj01
      · exact absurd rfl (fun h => hj2 h)
      · exact absurd hjle2 (by omega)
    have hKcomm : ∀ a b : ↥KG, a * b = b * a := by
      exact (MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center
        (QuotientGroup.mk' (Subgroup.center ↥KG)) (by
          rw [QuotientGroup.ker_mk'])).is_comm.comm
    have h336 : (⁅KG, KG⁆ : Subgroup G) = ⊥ := by
      have hc : commutator ↥KG = ⊥ := by
        rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro a _
        rw [Subgroup.mem_centralizer_iff]
        intro b _
        exact hKcomm b a
      have hKGder36 : (commutator ↥KG).map KG.subtype = ⁅KG, KG⁆ := by
        rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
          Subgroup.range_subtype]
      rw [← hKGder36, hc, Subgroup.map_bot]
    have h336ea : OddOrder.GroupTheory.IsElementaryAbelian q ↥KG :=
      ⟨hKcomm, fun k => by rw [← hK_exp]; exact Monoid.pow_exponent_eq_one k⟩
    -- ===== (3.37) `|K| > q²` =====
    -- `A = PR₀` acts faithfully on `K` itself ((3.28)); were `|K| ≤ q²`, the elementary
    -- abelian `K` would be an `𝔽_q`-space of dimension ≤ 2 and `A` would be abelian in
    -- every case (dim 2: **Theorem 2.6(a)** again; dim 1: endomorphisms of a line commute;
    -- dim 0: `K = ⊥` contradicts (3.13)) — against (3.21)/(3.13).
    have h337 : q ^ 2 < Nat.card ↥KG := by
      by_contra hle
      push Not at hle
      have hKGcommM : IsMulCommutative ↥KG := ⟨⟨hKcomm⟩⟩
      have hqsmulK : ∀ v : Additive ↥KG, (q : ℕ) • v = 0 := by
        intro v
        apply Additive.toMul.injective
        rw [toMul_nsmul, toMul_zero]
        exact h336ea.2 v.toMul
      have hKmod : Module (ZMod q) (Additive ↥KG) := AddCommGroup.zmodModule hqsmulK
      have : Module.Finite (ZMod q) (Additive ↥KG) := Module.Finite.of_finite
      set ρ3 : Representation (ZMod q) ↥A (Additive ↥KG) :=
        (OddOrder.BG.Ch1_Preliminary.mulAutToEnd ↥KG q).comp φA with hρ3
      have hρ3_apply : ∀ (g : ↥A) (v : Additive ↥KG),
          ρ3 g v = Additive.ofMul (φA g (Additive.toMul v)) := fun g v => rfl
      -- faithfulness from (3.28)
      have hker3 : ∀ a : ↥A, ρ3 a = 1 → a = 1 := by
        intro a ha
        have haC : (a : G) ∈ Subgroup.centralizer (KG : Set G) := by
          rw [Subgroup.mem_centralizer_iff]
          intro m hm
          have h1 := DFunLike.congr_fun ha (Additive.ofMul (⟨m, hm⟩ : ↥KG))
          rw [hρ3_apply, Module.End.one_apply] at h1
          have h2 : (a : G) * m * (a : G)⁻¹ = m :=
            (hφA_val a ⟨m, hm⟩).symm.trans
              (congrArg Subtype.val (Additive.ofMul.injective h1))
          exact (mul_inv_eq_iff_eq_mul.mp h2).symm
        have habot : (a : G) ∈ A ⊓ Subgroup.centralizer (KG : Set G) := ⟨a.2, haC⟩
        rw [h328, Subgroup.mem_bot] at habot
        exact Subtype.ext habot
      have hKG_ne_bot37 : KG ≠ ⊥ := by
        intro hbot
        apply h313G
        rw [hbot, Subgroup.commutator_bot_left]
      -- `A` is abelian whatever the dimension (≤ 2) — contradiction with (3.21)/(3.13)
      have hAcomm37 : ∀ a b : ↥A, a * b = b * a := by
        have : Fintype (Additive ↥KG) := Fintype.ofFinite _
        have hcardK : Nat.card (Additive ↥KG)
            = q ^ Module.finrank (ZMod q) (Additive ↥KG) := by
          rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod q),
            ZMod.card]
        have hcardK' : Nat.card (Additive ↥KG) = Nat.card ↥KG := rfl
        have hfrle : Module.finrank (ZMod q) (Additive ↥KG) ≤ 2 := by
          by_contra hgt
          push Not at hgt
          have h1 : q ^ 3 ≤ q ^ Module.finrank (ZMod q) (Additive ↥KG) :=
            Nat.pow_le_pow_right hq_prime.pos (by omega)
          have h3 : q ^ 2 < q ^ 3 := Nat.pow_lt_pow_right hq_prime.one_lt (by omega)
          omega
        rcases hfr : Module.finrank (ZMod q) (Additive ↥KG) with _ | _ | _ | fr4
        · -- dim 0: `K = ⊥`
          exfalso
          rw [hfr, pow_zero] at hcardK
          exact hKG_ne_bot37 (Subgroup.eq_bot_of_card_eq _ (hcardK'.symm.trans hcardK))
        · -- dim 1: all endomorphisms of a line are scalars, hence commute
          intro a b
          have htriv := S03e.trivial_on_commutator_of_finrank_eq_one ρ3
            (by rw [hfr]) (⊤ : Subgroup ↥A)
          have h1 : ρ3 ⁅a, b⁆ = 1 := htriv _
            (Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b))
          have h2 : ⁅a, b⁆ = 1 := hker3 _ h1
          exact commutatorElement_eq_one_iff_mul_comm.mp h2
        · -- dim 2: Theorem 2.6(a)
          have hfaith3 : Function.Injective ρ3 := by
            intro a b hab
            have h1 : ρ3 (a * b⁻¹) = 1 := by
              rw [map_mul, hab, ← map_mul, mul_inv_cancel, map_one]
            exact mul_inv_eq_one.mp (hker3 _ h1)
          have hodd_A37 : Odd (Nat.card ↥A) := by
            obtain ⟨m2, hm2⟩ := Subgroup.card_subgroup_dvd_card A
            rw [hm2, Nat.odd_mul] at hodd
            exact hodd.1
          have hchar37 : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ Nat.card ↥A → ¬ CharP (ZMod q) ℓ := by
            intro ℓ hℓ hdvd hcharP
            have hℓq : ℓ = q := CharP.eq (ZMod q) hcharP (ZMod.charP q)
            have hℓpr : ℓ = p ∨ ℓ = r := by
              have h3 : ℓ ∣ Nat.card ↥(P.map H.subtype : Subgroup G) * Nat.card ↥R₀ := by
                rw [← hAcard]
                exact hdvd
              rcases (Nat.Prime.dvd_mul hℓ).mp h3 with h4 | h4
              · left
                obtain ⟨k2, hk2⟩ := (hPp.map H.subtype).exists_card_eq
                rw [hk2] at h4
                exact (Nat.prime_dvd_prime_iff_eq hℓ hp).mp (hℓ.dvd_of_dvd_pow h4)
              · right
                rw [hr_card] at h4
                exact (Nat.prime_dvd_prime_iff_eq hℓ hr_prime).mp h4
            rcases hℓpr with h5 | h5
            · exact hq_ne_p (by rw [← hℓq]; exact h5)
            · exact hq_ne_r (by rw [← hℓq]; exact h5)
          have hAcomm := OddOrder.BG.Ch1.S02.odd_two_dim_abelian hodd_A37
            (by rw [hfr]) ρ3 hfaith3 hchar37
          exact hAcomm.comm
        · exact absurd hfrle (by omega)
      have hPGR₀bot37 : (⁅(P.map H.subtype : Subgroup G), R₀⁆ : Subgroup G) = ⊥ := by
        rw [eq_bot_iff, Subgroup.commutator_le]
        intro g₁ hg₁ g₂ hg₂
        have h6 := hAcomm37 (⟨g₁, hPG_le_A hg₁⟩ : ↥A) ⟨g₂, hR₀_le_A hg₂⟩
        have h7 : g₁ * g₂ = g₂ * g₁ := congrArg Subtype.val h6
        rw [Subgroup.mem_bot]
        exact commutatorElement_eq_one_iff_mul_comm.mpr h7
      have hPGbot37 : (P.map H.subtype : Subgroup G) = ⊥ := h321G ▸ hPGR₀bot37
      apply h313G
      rw [hPGbot37, Subgroup.commutator_bot_right]
    -- ===== Phase F ((3.38)): the orbit-parity contradiction =====
    -- Split off to `S03f_OrbitParity.orbit_parity_contradiction` (it consumes no induction
    -- hypothesis — only the facts established above — and carries the whole counting argument).
    exact orbit_parity_contradiction hp hq_prime hr_prime hq_ne_p hpr hodd hVG hKG
      hVGelem hV_ne_bot hKcomm hK_exp hKGq h337 h314C hVK_inf hCHV hPp hr_card hAdef
      hA_le_N h311 h313G h319 h321G h323G h324 hKRs_index

end OddOrder.BG.Ch1.S03f


