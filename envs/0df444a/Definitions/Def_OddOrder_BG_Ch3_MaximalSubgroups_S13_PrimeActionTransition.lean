-- Prove2me | Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S13_PrimeActionTransition
-- name    : OddOrder_BG_Ch3_MaximalSubgroups_S13_PrimeActionTransition
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T08:59:41.214756+00:00
-- url     : https://prove2.me/theorems/a7e72957-d49b-48ea-9753-1366232152ff
-- title:
--   BG §13: Corollary 13.11 and Lemmas 13.12/13.13
-- statement:
--   Formalizes the end of §13 of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*: Corollary 13.11 and Lemmas 13.12 and 13.13. It also acts as the hub through which downstream files enter, importing the earlier §13 files (Lemmas 13.7/13.8, Theorems 13.9/13.10).
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 8 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch3_MaximalSubgroups/S13_PrimeActionTransition.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch3_MaximalSubgroups/S13_PrimeActionTransition.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S13_Theorem1310
import Mathlib.GroupTheory.NoncommCoprod

namespace OddOrder.BG.Ch3.S13

open OddOrder.GroupTheory

open OddOrder.Isaacs

open OddOrder.BG.Ch3.S12

open scoped Pointwise commutatorElement

variable {G : Type*} [Group G]

/-- In a finite cyclic group, a subgroup of prime order is unique: two subgroups of the same
prime order `q` coincide. (`H ⊔ K` is elementary abelian of exponent `q` and cyclic, hence of
order dividing `q`, forcing `H = H ⊔ K = K`.) Used for BG Cor 13.11(d). -/
theorem eq_of_card_eq_prime_of_isCyclic {A : Type*} [Group A] [Finite A] [IsCyclic A]
    {q : ℕ} (hq : q.Prime) {H K : Subgroup A}
    (hH : Nat.card ↥H = q) (hK : Nat.card ↥K = q) : H = K := by
  have : Fact q.Prime := ⟨hq⟩
  let : CommGroup A := IsCyclic.commGroup
  have hHel : H.IsElementaryAbelian q := Subgroup.IsElementaryAbelian.of_card_prime hH
  have hKel : K.IsElementaryAbelian q := Subgroup.IsElementaryAbelian.of_card_prime hK
  have hcent : H ≤ Subgroup.centralizer (K : Set A) := fun x _ =>
    Subgroup.mem_centralizer_iff.mpr (fun y _ => mul_comm y x)
  have hsupel : (H ⊔ K).IsElementaryAbelian q := hHel.sup_of_le_centralizer hKel hcent
  have : IsCyclic ↥(H ⊔ K) := inferInstance
  have hexp : Monoid.exponent ↥(H ⊔ K) ∣ q :=
    Monoid.exponent_dvd_of_forall_pow_eq_one (fun x => hsupel.2 x)
  have hcarddvd : Nat.card ↥(H ⊔ K) ∣ q := by rwa [IsCyclic.exponent_eq_card] at hexp
  have hcardle : Nat.card ↥(H ⊔ K) ≤ q := Nat.le_of_dvd hq.pos hcarddvd
  have hHK : H = H ⊔ K := Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hH]; exact hcardle)
  have hKK : K = H ⊔ K := Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [hK]; exact hcardle)
  exact hHK.trans hKK.symm

/-- `G`-level form of `eq_of_card_eq_prime_of_isCyclic`: two order-`q` subgroups of `G` both
contained in a cyclic subgroup `A` coincide. -/
theorem eq_of_card_eq_prime_of_le_isCyclic {A : Subgroup G} [Finite ↥A] (hAcyc : IsCyclic ↥A)
    {q : ℕ} (hq : q.Prime) {H K : Subgroup G} (hHA : H ≤ A) (hKA : K ≤ A)
    (hH : Nat.card ↥H = q) (hK : Nat.card ↥K = q) : H = K := by
  have := hAcyc
  have hH' : Nat.card ↥(H.subgroupOf A) = q := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHA).toEquiv]; exact hH
  have hK' : Nat.card ↥(K.subgroupOf A) = q := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKA).toEquiv]; exact hK
  have hEq : H.subgroupOf A = K.subgroupOf A := eq_of_card_eq_prime_of_isCyclic hq hH' hK'
  have hmap := congrArg (Subgroup.map A.subtype) hEq
  rwa [Subgroup.map_subgroupOf_eq_of_le hHA, Subgroup.map_subgroupOf_eq_of_le hKA] at hmap

/-- **BG Corollary 13.11** (mmd L3696; 結論は PDF p.103 から画像読みで復元): `E₃≠1` かつ `E₃` が
`M_σ` に regular 作用しないなら (a) `E₁≠1`; (b) `E=E₁E₃`; (c) `E` は `M_σ` に prime 作用;
(d) すべての `X∈ℰ¹(E)` は `E` で正規。 -/
theorem E3_not_regular_consequences [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) (hE3 : E₃ ≠ ⊥)
    (hreg : ¬ ActsRegularlyOn (S10.Msigma M) E₃) :
    E₁ ≠ ⊥ ∧ E = E₁ ⊔ E₃ ∧ ActsPrimeOn (S10.Msigma M) E ∧
    (∀ q : ℕ, q.Prime → ∀ X : Subgroup G, X ∈ elemAbelianOfRank G q 1 → X ≤ E →
      E ≤ Subgroup.normalizer (X : Set G)) := by
  classical
  have hE3prime : ActsPrimeOn (S10.Msigma M) E₃ := (cyclicSylow_actsPrime hG h).2
  -- From `¬reg` and `E₃` prime on `M_σ`: some `x ∈ E₃#` has `C_{M_σ}(x) ≠ 1`.
  have hxex : ∃ x ∈ E₃, x ≠ 1 ∧ S10.Msigma M ⊓ Subgroup.centralizer ({x} : Set G) ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    exact hreg (fun x hxE3 hx1 => by rw [fixedByElement_def]; exact hcon x hxE3 hx1)
  obtain ⟨x, hxE3, hxne, hxC⟩ := hxex
  -- `τ₂(M)` empty (`E₂ = ⊥`): an `A ∈ ℰ_p²(E)` with `p ∈ τ₂` would force `C_{M_σ}(x) = 1`.
  have hE2 : E₂ = ⊥ := by
    by_contra hE2ne
    obtain ⟨pp, hpp, hppdvd⟩ :=
      (Nat.card ↥E₂).exists_prime_and_dvd (fun hc => hE2ne (Subgroup.card_eq_one.mp hc))
    have : Fact pp.Prime := ⟨hpp⟩
    have hc2 : Nat.card ↥(E₂.subgroupOf E) = Nat.card ↥E₂ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₂_le).toEquiv
    have hppτ2 : pp ∈ tau2 M :=
      h.E₂_hall.1 pp (hc2 ▸ Nat.mem_primeFactors.mpr ⟨hpp, hppdvd, Nat.card_pos.ne'⟩)
    obtain ⟨A, hA, hAE⟩ := exists_elemAb_rank_two_le_E_of_tau2 hG h hppτ2
    exact hxC ((elemAb_normal_in_E_of_tau2 hG h hppτ2 hA hAE).2.2.2.1 x hxE3 hxne)
  -- (b) `E = E₁ ⊔ E₃` and (a) `E₁ ≠ ⊥`.
  have hEsup : E = E₁ ⊔ E₃ := by rw [h.eq_sup hG, hE2, sup_bot_eq]
  have hE1ne : E₁ ≠ ⊥ := h.E1_ne_bot_of_E2_eq_bot hG hE2
  -- Thm 13.10 contrapositive: every rank-1 `P ≤ E₁` centralizes `E₃`.
  have hAllCent : ∀ pp : ℕ, pp.Prime → ∀ P : Subgroup G, P ∈ elemAbelianOfRank G pp 1 → P ≤ E₁ →
      P ≤ Subgroup.centralizer (E₃ : Set G) := by
    intro pp hpp P hPmem hPE1
    by_contra hPnc
    exact hreg (E1_regular_on_E3_of_noncentralize hG h ⟨pp, hpp, P, hPmem, hPE1, hPnc⟩).2.1
  -- `E₁` does not act regularly on `E₃` (a rank-1 `P ≤ E₁` centralizes the nontrivial `E₃`).
  have hE1nreg : ¬ ActsRegularlyOn E₃ E₁ := by
    obtain ⟨pp, hpp, hppdvd⟩ :=
      (Nat.card ↥E₁).exists_prime_and_dvd (fun hc => hE1ne (Subgroup.card_eq_one.mp hc))
    have : Fact pp.Prime := ⟨hpp⟩
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' pp hppdvd
    have hPcard : Nat.card ↥(Subgroup.zpowers (g : G)) = pp := by
      rw [Nat.card_zpowers]; exact (orderOf_injective E₁.subtype E₁.subtype_injective g).trans hg
    have hPmem : Subgroup.zpowers (g : G) ∈ elemAbelianOfRank G pp 1 :=
      ⟨Subgroup.IsElementaryAbelian.of_card_prime hPcard, by rw [hPcard, pow_one]⟩
    have hPC : Subgroup.zpowers (g : G) ≤ Subgroup.centralizer (E₃ : Set G) :=
      hAllCent pp hpp _ hPmem (Subgroup.zpowers_le.mpr g.2)
    have hgne : g ≠ 1 := by intro hc; rw [hc, orderOf_one] at hg; exact hpp.ne_one hg.symm
    have hg1 : (g : G) ≠ 1 := fun hc => hgne (Subtype.ext (by simpa using hc))
    have hgCE3 : (g : G) ∈ Subgroup.centralizer (E₃ : Set G) := hPC (Subgroup.mem_zpowers _)
    have hE3sub : E₃ ≤ Subgroup.centralizer ({(g : G)} : Set G) := by
      intro e he; rw [Subgroup.mem_centralizer_iff]; intro u hu
      rw [Set.mem_singleton_iff.mp hu]
      exact (Subgroup.mem_centralizer_iff.mp hgCE3 e he).symm
    rw [ActsRegularlyOn]; push Not
    refine ⟨(g : G), g.2, hg1, ?_⟩
    rw [fixedByElement_def]
    intro hbot
    exact hE3 (le_bot_iff.mp (hbot ▸ le_inf le_rfl hE3sub))
  -- (c) `E` acts in a prime manner on `M_σ`.
  have hEprime : ActsPrimeOn (S10.Msigma M) E := hEsup ▸ E1E3_actsPrime hG h hE1ne hE1nreg
  refine ⟨hE1ne, hEsup, hEprime, ?_⟩
  -- (d) every prime-order `X ≤ E` is normal in `E`.
  intro q hqp X hXmem hXE
  have : Fact q.Prime := ⟨hqp⟩
  have hXcard : Nat.card ↥X = q := by simpa using hXmem.2
  have hEN3 : E ≤ Subgroup.normalizer ((E₃ : Subgroup G) : Set G) := h.E3_normal hG
  -- `|E₁|`, `|E₃|` are coprime (`τ₁ ∩ τ₃ = ∅`).
  have hcop13 : Nat.Coprime (Nat.card ↥E₁) (Nat.card ↥E₃) := by
    rw [Nat.coprime_iff_gcd_eq_one]
    by_contra hne
    obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd hne
    exact not_mem_tau3_of_mem_tau1
      (h.isPiGroup_tau1 r (Nat.mem_primeFactors.mpr
        ⟨hr, hrd.trans (Nat.gcd_dvd_left _ _), Nat.card_pos.ne'⟩))
      (h.isPiGroup_tau3 r (Nat.mem_primeFactors.mpr
        ⟨hr, hrd.trans (Nat.gcd_dvd_right _ _), Nat.card_pos.ne'⟩))
  by_cases hqE3 : q ∣ Nat.card ↥E₃
  · -- τ₃ case: `X ≤ E₃`, characteristic in the cyclic `E₃ ⊴ E`.
    have hqnE1 : ¬ q ∣ Nat.card ↥E₁ := by
      intro hd
      exact hqp.ne_one (Nat.dvd_one.mp (hcop13 ▸ Nat.dvd_gcd hd hqE3))
    have hcopXE1 : Nat.Coprime (Nat.card ↥X) (Nat.card ↥E₁) :=
      hXcard ▸ (hqp.coprime_iff_not_dvd.mpr hqnE1)
    have hXE3 : X ≤ E₃ :=
      le_of_le_sup_of_coprime_card (h.E₁_le.trans hEN3)
        (by rw [sup_comm, ← hEsup]; exact hXE) hcopXE1
    exact E_le_normalizer_of_le_E3 hG h hXE3
  · -- τ₁ case: `q ∣ |E₁|`; `X` equals the unique order-`q` subgroup of `E₁` modulo `E₃`.
    have : IsCyclic ↥E₁ := h.E1_isCyclic hG
    have : IsCyclic ↥E₃ := h.E3_isCyclic hG
    have hE1NE3 : E₁ ≤ Subgroup.normalizer (E₃ : Set G) := h.E₁_le.trans (h.E3_normal hG)
    -- `|E| = |E₁| * |E₃|`, so from `q ∣ |X| ∣ |E|` and `q ∤ |E₃|` we get `q ∣ |E₁|`.
    have hcardE : Nat.card ↥E = Nat.card ↥E₁ * Nat.card ↥E₃ := by
      rw [hEsup]
      exact card_sup_eq_mul_of_le_normalizer_of_disjoint hE1NE3
        (Subgroup.disjoint_of_coprime_natCard hcop13).eq_bot
    have hqE : q ∣ Nat.card ↥E := by
      have := Subgroup.card_dvd_of_le hXE; rwa [hXcard] at this
    have hqE1 : q ∣ Nat.card ↥E₁ := by
      rw [hcardE] at hqE
      exact (hqp.dvd_mul.mp hqE).resolve_right hqE3
    -- Build `P₀ = ⟨g⟩` of order `q` inside `E₁`, centralizing `E₃` (Thm 13.10 contrapositive).
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' q hqE1
    set P₀ : Subgroup G := Subgroup.zpowers (g : G) with hP₀def
    have hP₀card : Nat.card ↥P₀ = q := by
      rw [hP₀def, Nat.card_zpowers]
      exact (orderOf_injective E₁.subtype E₁.subtype_injective g).trans hg
    have hP₀E1 : P₀ ≤ E₁ := Subgroup.zpowers_le.mpr g.2
    have hP₀mem : P₀ ∈ elemAbelianOfRank G q 1 :=
      ⟨Subgroup.IsElementaryAbelian.of_card_prime hP₀card, by rw [hP₀card, pow_one]⟩
    have hP₀cent : P₀ ≤ Subgroup.centralizer (E₃ : Set G) := hAllCent q hqp P₀ hP₀mem hP₀E1
    have hP₀E : P₀ ≤ E := hP₀E1.trans h.E₁_le
    -- `E` normalizes `P₀`: `E₁` does (char in cyclic `E₁`), and `E₃` does (centralizes it).
    have hE1NP₀ : E₁ ≤ Subgroup.normalizer (P₀ : Set G) := by
      have : (P₀.subgroupOf E₁).Characteristic := Ch04.characteristic_of_subgroup_of_isCyclic _
      intro e he
      have hmem := OddOrder.BG.Ch1.S03f.mem_normalizer_map_subtype_of_characteristic (W := E₁)
        (C := P₀.subgroupOf E₁) (Subgroup.le_normalizer he)
      rwa [Subgroup.map_subgroupOf_eq_of_le hP₀E1] at hmem
    have hE3NP₀ : E₃ ≤ Subgroup.normalizer (P₀ : Set G) := by
      have hE3cP₀ : E₃ ≤ Subgroup.centralizer (P₀ : Set G) := by
        intro e he
        rw [Subgroup.mem_centralizer_iff]
        intro u hu
        exact (Subgroup.mem_centralizer_iff.mp (hP₀cent hu) e he).symm
      exact hE3cP₀.trans (Subgroup.centralizer_le_normalizer _)
    have hENP₀ : E ≤ Subgroup.normalizer (P₀ : Set G) :=
      hEsup ▸ sup_le hE1NP₀ hE3NP₀
    -- `D := P₀ ⊔ E₃` is cyclic (internal direct product of commuting coprime cyclics).
    set D : Subgroup G := P₀ ⊔ E₃ with hDdef
    have hcopP₀E3 : Nat.Coprime (Nat.card ↥P₀) (Nat.card ↥E₃) :=
      hP₀card ▸ (hqp.coprime_iff_not_dvd.mpr hqE3)
    have hP₀E3bot : P₀ ⊓ E₃ = ⊥ := (Subgroup.disjoint_of_coprime_natCard hcopP₀E3).eq_bot
    have hcomm : ∀ (m : ↥P₀) (n : ↥E₃), Commute (P₀.subtype m) (E₃.subtype n) := by
      intro m n
      change (m : G) * (n : G) = (n : G) * (m : G)
      exact (Subgroup.mem_centralizer_iff.mp (hP₀cent m.2) (n : G) n.2).symm
    have : IsCyclic ↥D := by
      have hinj : Function.Injective (MonoidHom.noncommCoprod P₀.subtype E₃.subtype hcomm) :=
        (MonoidHom.noncommCoprod_injective _ _ hcomm).mpr
          ⟨P₀.subtype_injective, E₃.subtype_injective, by
            rw [P₀.range_subtype, E₃.range_subtype]; exact disjoint_iff.mpr hP₀E3bot⟩
      have hrange : (MonoidHom.noncommCoprod P₀.subtype E₃.subtype hcomm).range = D := by
        rw [MonoidHom.noncommCoprod_range, P₀.range_subtype, E₃.range_subtype, hDdef]
      have hprodcyc : IsCyclic (↥P₀ × ↥E₃) :=
        Group.isCyclic_prod_iff.mpr ⟨inferInstance, inferInstance, hcopP₀E3⟩
      exact (((MonoidHom.ofInjective hinj).trans
        (MulEquiv.subgroupCongr hrange)).isCyclic).mp hprodcyc
    -- `E` normalizes `D` (normalizes both `P₀` and `E₃`).
    have hEND : E ≤ Subgroup.normalizer (D : Set G) := le_normalizer_sup hENP₀ hEN3
    -- `X ⊔ E₃ = P₀ ⊔ E₃ = D`, via the unique order-`q` subgroup of the cyclic quotient `E/E₃`.
    have hE₃subN : (E₃.subgroupOf E).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer h.E₃_le).mpr hEN3
    set mk : ↥E →* (↥E ⧸ E₃.subgroupOf E) := QuotientGroup.mk' (E₃.subgroupOf E) with hmkdef
    -- the quotient `↥E ⧸ E₃.subgroupOf E` is cyclic (surjective image of cyclic `↥E₁`).
    have hQcyc : IsCyclic (↥E ⧸ E₃.subgroupOf E) := by
      refine isCyclic_of_surjective (mk.comp (Subgroup.inclusion h.E₁_le)) ?_
      intro y
      induction y using QuotientGroup.induction_on with
      | _ e =>
        have hecoe : (e : G) ∈ (↑(E₁ ⊔ E₃) : Set G) := by
          rw [← hEsup]; exact e.2
        rw [Subgroup.coe_mul_of_left_le_normalizer_right E₁ E₃ hE1NE3] at hecoe
        obtain ⟨a, ha, b, hb, hab⟩ := hecoe
        rw [SetLike.mem_coe] at ha hb
        refine ⟨⟨a, ha⟩, ?_⟩
        rw [MonoidHom.comp_apply]
        change mk (Subgroup.inclusion h.E₁_le ⟨a, ha⟩) = mk e
        rw [hmkdef, QuotientGroup.mk'_eq_mk']
        refine ⟨⟨b, h.E₃_le hb⟩, ?_, ?_⟩
        · rw [Subgroup.mem_subgroupOf]; exact hb
        · apply Subtype.ext
          change a * b = (e : G)
          exact hab
    -- both `X` and `P₀` are disjoint from `E₃` (orders coprime), so inject into the quotient.
    have hcopXE3 : Nat.Coprime (Nat.card ↥X) (Nat.card ↥E₃) :=
      hXcard ▸ (hqp.coprime_iff_not_dvd.mpr hqE3)
    have hXE3bot : X ⊓ E₃ = ⊥ := (Subgroup.disjoint_of_coprime_natCard hcopXE3).eq_bot
    -- helper: card of the image of a subgroup `K ≤ E` disjoint from `E₃` equals `|K|`.
    have hcardmap : ∀ (K : Subgroup G), K ≤ E → K ⊓ E₃ = ⊥ →
        Nat.card ↥((K.subgroupOf E).map mk) = Nat.card ↥(K.subgroupOf E) := by
      intro K hKE hKbot
      have hkerbot : (E₃.subgroupOf E) ⊓ (K.subgroupOf E) = ⊥ := by
        rw [eq_bot_iff]
        intro z hz
        rw [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at hz
        have : (z : G) ∈ K ⊓ E₃ := Subgroup.mem_inf.mpr ⟨hz.2, hz.1⟩
        rw [hKbot, Subgroup.mem_bot] at this
        rw [Subgroup.mem_bot]
        exact Subtype.ext this
      have h1 : Nat.card ↥((K.subgroupOf E).map mk) = (E₃.subgroupOf E).relIndex (K.subgroupOf E) :=
          by
        rw [← Subgroup.relIndex_ker, hmkdef, QuotientGroup.ker_mk']
      rw [h1, Subgroup.relIndex,
        Subgroup.subgroupOf_eq_bot.mpr (disjoint_iff.mpr hkerbot), Subgroup.index_bot]
    have hcardXsub : Nat.card ↥(X.subgroupOf E) = q := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXE).toEquiv]; exact hXcard
    have hcardP₀sub : Nat.card ↥(P₀.subgroupOf E) = q := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP₀E).toEquiv]; exact hP₀card
    have hmapXcard : Nat.card ↥((X.subgroupOf E).map mk) = q := by
      rw [hcardmap X hXE hXE3bot, hcardXsub]
    have hmapP₀card : Nat.card ↥((P₀.subgroupOf E).map mk) = q := by
      rw [hcardmap P₀ hP₀E hP₀E3bot, hcardP₀sub]
    have hmapeq : (X.subgroupOf E).map mk = (P₀.subgroupOf E).map mk :=
      eq_of_card_eq_prime_of_isCyclic hqp hmapXcard hmapP₀card
    -- pull back: `X.subgroupOf E ⊔ ker = P₀.subgroupOf E ⊔ ker`, then map up to `X ⊔ E₃ = P₀ ⊔ E₃`.
    have hcomapeq := congrArg (Subgroup.comap mk) hmapeq
    rw [Subgroup.comap_map_eq, Subgroup.comap_map_eq, hmkdef, QuotientGroup.ker_mk'] at hcomapeq
    have hsupsub : (X ⊔ E₃).subgroupOf E = (P₀ ⊔ E₃).subgroupOf E := by
      rw [Subgroup.subgroupOf_sup hXE h.E₃_le, Subgroup.subgroupOf_sup hP₀E h.E₃_le]
      exact hcomapeq
    have hXsupE3 : X ⊔ E₃ = D := by
      have := congrArg (Subgroup.map E.subtype) hsupsub
      rwa [Subgroup.map_subgroupOf_eq_of_le (sup_le hXE h.E₃_le),
        Subgroup.map_subgroupOf_eq_of_le (sup_le hP₀E h.E₃_le), ← hDdef] at this
    -- `X ≤ D`, `X` characteristic in cyclic `D`, `E ≤ N(D)` ⟹ `E ≤ N(X)`.
    have hXD : X ≤ D := hXsupE3 ▸ le_sup_left
    have : (X.subgroupOf D).Characteristic := Ch04.characteristic_of_subgroup_of_isCyclic _
    intro e he
    have hmem := OddOrder.BG.Ch1.S03f.mem_normalizer_map_subtype_of_characteristic (W := D)
      (C := X.subgroupOf D) (hEND he)
    rwa [Subgroup.map_subgroupOf_eq_of_le hXD] at hmem

/-- Conjugation commutes with `centralizer`: `(C_G(S))^g = C_G(S^g)`. -/
private theorem conj_smul_centralizer (g : G) (S : Subgroup G) :
    MulAut.conj g • Subgroup.centralizer (S : Set G)
      = Subgroup.centralizer ((MulAut.conj g • S : Subgroup G) : Set G) :=
  Subgroup.map_centralizer_eq_of_bijective (S : Set G) (MulAut.conj g).toMonoidHom
    (MulAut.conj g).bijective

/-- **Hall conjugacy into the `τ₁`-piece**: given a `SubgroupESetup M E E₁ E₂ E₃` and a `p`-subgroup
`P ≤ E` with `p ∈ τ₁(M)`, some `E`-conjugate of `P` lands inside the `τ₁`-Hall piece `E₁`. (`↥E` is
solvable; `P.subgroupOf E` is a `τ₁(M)`-π-subgroup, contained in a Hall `τ₁`-subgroup of `↥E`, which
is `↥E`-conjugate to `E₁.subgroupOf E`.) Used to normalize `P` into `E₁` in Lemma 13.12. -/
private theorem exists_conj_le_tau1_piece [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ tau1 M) {P : Subgroup G} (hPp : IsPGroup p ↥P) (hPE : P ≤ E) :
    ∃ c ∈ E, MulAut.conj c • P ≤ E₁ := by
  classical
  have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups h.mem_maximal
  have : Group.IsSolvable ↥E :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective h.E_le)
  have hPEpi : Ch03.Subgroup.IsPiGroup (tau1 M) (P.subgroupOf E) := by
    intro s hs
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPE).toEquiv] at hs
    obtain ⟨n, hn⟩ := hPp.exists_card_eq
    rw [hn, Nat.mem_primeFactors] at hs
    exact ((Nat.prime_dvd_prime_iff_eq hs.1 Fact.out).mp (hs.1.dvd_of_dvd_pow hs.2.1)) ▸ hp
  obtain ⟨H, hH_hall, _, hPH⟩ :=
    OddOrder.BG.Ch1.S01.aInvariant_piSubgroup_le_aInvariant_hall
      (A := Unit) (φ := (1 : Unit →* MulAut ↥E))
      (by rw [Nat.card_unique]; exact Nat.coprime_one_left _) hPEpi (fun _ => one_smul _ _)
  set HG : Subgroup G := H.map E.subtype with hHGdef
  have hHG_le_E : HG ≤ E := Subgroup.map_subtype_le _
  have hHG_sub : HG.subgroupOf E = H := by
    rw [hHGdef, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective E.subtype_injective]
  have hHG_hall : Ch03.IsHallSubgroup (tau1 M) (HG.subgroupOf E) := hHG_sub ▸ hH_hall
  obtain ⟨w, hwE, hw⟩ :=
    Ch1.S06.exists_conj_eq_of_isHall_subgroupOf inferInstance hHG_le_E h.E₁_le hHG_hall h.E₁_hall
  refine ⟨w, hwE, ?_⟩
  have hPHG : P ≤ HG := by
    intro x hx
    rw [hHGdef]
    refine Subgroup.mem_map.mpr ⟨⟨x, hPE hx⟩, ?_, rfl⟩
    have hxsub : (⟨x, hPE hx⟩ : ↥E) ∈ P.subgroupOf E := Subgroup.mem_subgroupOf.mpr hx
    exact hHG_sub ▸ hPH hxsub
  calc MulAut.conj w • P ≤ MulAut.conj w • HG :=
        Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hPHG
    _ = E₁ := hw

/-- **BG Lemma 13.12** (mmd L3745): if `p ∈ τ₁(M)`, `P ∈ ℰ_p¹(E)`, `q ∈ τ₂(M)`, `A ∈ ℰ_q²(E)`,
and `C_A(P) ≠ 1`, then `C_{M_σ}(P) = 1`.

Proof (BG L3747): suppose `C_{M_σ}(P) ≠ 1`.  By Corollary 12.6(a),(e), `A ◁ E` and
`P ⊄ C_E(A)`, so `Y = C_A(P)` has order `q`.  By Theorem 13.4, `1 ⊂ C_{M_σ}(P) ⊆ C_{M_σ}(Y)`,
hence `𝓜(C_G(Y)) = {M}` by Corollary 12.6(c).  For `M* ∈ 𝓜(N_G(A))` we have `q ∈ σ(M*)` and
`p ∈ τ₁(M*) ∪ τ₂(M*)` by Lemma 12.11.  The case `p ∈ τ₂(M*)` gives `1 ⊂ C_G(P) ∩ M_σ ⊆ M* ∩ M_σ`,
contrary to Theorem 12.5(e); the case `p ∈ τ₁(M*)` gives `𝓜(C_G(Y)) = {M*}` by Lemma 13.6 for
`M*`, contradicting `𝓜(C_G(Y)) = {M}`.

Statement draft = Lane H (issue 2006, BG 原文逐条照合・S13 context build green); proof = Lane F. -/
theorem Msigma_centralizer_eq_bot_of_tau1_tau2 [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hp : p ∈ tau1 M) (hq : q ∈ tau2 M)
    {P A : Subgroup G} (hP : P ∈ elemAbelianOfRank G p 1) (hPE : P ≤ E)
    (hA : A ∈ elemAbelianOfRank G q 2) (hAE : A ≤ E)
    (hCAP : A ⊓ Subgroup.centralizer (P : Set G) ≠ ⊥) :
    S10.Msigma M ⊓ Subgroup.centralizer (P : Set G) = ⊥ := by
  classical
  -- By contradiction: assume `C_{M_σ}(P) ≠ 1`.
  rw [← not_ne_iff]
  intro hCPne
  -- Notation and basic facts.
  have hpσ : p ∉ S10.sigma M := hp.1
  have hqσ : q ∉ S10.sigma M := hq.1
  have hpne_q : p ≠ q := by
    rintro rfl
    have := tau1_pRank_eq_one hp; have := tau2_pRank_eq_two hq; omega
  have hAM : A ≤ M := hAE.trans h.E_le
  have hPM : P ≤ M := hPE.trans h.E_le
  have hPp : IsPGroup p ↥P := hP.1.isPGroup
  have hPne : P ≠ ⊥ := ne_bot_of_mem_elemAbelianOfRank_one hP
  have hAcard : Nat.card ↥A = q ^ 2 := hA.2
  have hAcomm : IsMulCommutative ↥A := ⟨⟨hA.1.comm⟩⟩
  have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups h.mem_maximal
  have : Group.IsSolvable ↥E :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective h.E_le)
  -- `M_σ ⊴ M`, used to conjugate `C_{M_σ}(·)` by elements of `M`.
  have hMnormMσ : M ≤ Subgroup.normalizer ((S10.Msigma M : Subgroup G) : Set G) :=
    le_normalizer_opiCoreInG _ _
  -- 12.6 bundle for `(M, q, A)`.
  have h126 := elemAb_normal_in_E_of_tau2 hG h hq hA hAE
  -- (1) `A ◁ E`.
  have hENA : E ≤ Subgroup.normalizer (A : Set G) := h126.1.1
  -- A conjugate of `P` (within `E`) lies inside the `τ₁`-Hall piece `E₁`.
  have hPconjE1 : ∃ c ∈ E, MulAut.conj c • P ≤ E₁ := exists_conj_le_tau1_piece hG h hp hPp hPE
  -- (2) `P ⊄ C_E(A)`, i.e. `¬ P ≤ C_G(A)`.
  have hPnotcA : ¬ P ≤ Subgroup.centralizer (A : Set G) := by
    intro hPcA
    obtain ⟨c, hcE, hPcE1⟩ := hPconjE1
    have hcM : c ∈ M := h.E_le hcE
    set Pc : Subgroup G := MulAut.conj c • P with hPcdef
    -- `P^c ≤ C_G(A)` (since `A^c = A` because `c ∈ E ≤ N(A)`).
    have hAc : MulAut.conj c • A = A := conj_smul_eq_self_of_mem_normalizer (hENA hcE)
    have hPcCA : Pc ≤ Subgroup.centralizer (A : Set G) := by
      have : MulAut.conj c • P ≤ MulAut.conj c • Subgroup.centralizer (A : Set G) :=
        Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hPcA
      rwa [conj_smul_centralizer, hAc, ← hPcdef] at this
    -- `P^c ≠ 1`, so there is `x ∈ (P^c)#`.
    have hPcne : Pc ≠ ⊥ := by
      rw [hPcdef]; intro hbot
      exact hPne (by simpa using congrArg (MulAut.conj c⁻¹ • ·) hbot)
    obtain ⟨x, hxPc, hxne⟩ := (Subgroup.bot_or_exists_ne_one Pc).resolve_left hPcne
    have hxE1 : x ∈ E₁ := hPcE1 hxPc
    have hxCA : x ∈ Subgroup.centralizer (A : Set G) := hPcCA hxPc
    -- 12.6(e): `C_{M_σ}({x}) = ⊥`.
    have hxbot : S10.Msigma M ⊓ Subgroup.centralizer ({x} : Set G) = ⊥ :=
      h126.2.2.2.2.1 x hxE1 hxCA hxne
    -- `C_{M_σ}(P^c) ≤ C_{M_σ}({x}) = ⊥`.
    have hCPcbot : S10.Msigma M ⊓ Subgroup.centralizer (Pc : Set G) = ⊥ :=
      le_bot_iff.mp (hxbot ▸ le_inf inf_le_left
        (inf_le_right.trans (Subgroup.centralizer_le
          (Set.singleton_subset_iff.mpr (SetLike.mem_coe.mpr hxPc)))))
    -- transport back: `C_{M_σ}(P) = conj c⁻¹ • C_{M_σ}(P^c) = ⊥`, contradicting `hCPne`.
    apply hCPne
    have hMσc : MulAut.conj c⁻¹ • S10.Msigma M = S10.Msigma M :=
      conj_smul_eq_self_of_mem_normalizer (hMnormMσ (M.inv_mem hcM))
    have hPcc : MulAut.conj c⁻¹ • Pc = P := by
      rw [hPcdef, ← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
    calc S10.Msigma M ⊓ Subgroup.centralizer (P : Set G)
        = (MulAut.conj c⁻¹ • S10.Msigma M) ⊓
            (MulAut.conj c⁻¹ • Subgroup.centralizer (Pc : Set G)) := by
          rw [hMσc, conj_smul_centralizer, hPcc]
      _ = MulAut.conj c⁻¹ • (S10.Msigma M ⊓ Subgroup.centralizer (Pc : Set G)) := by
          rw [Subgroup.smul_inf]
      _ = ⊥ := by rw [hCPcbot, Subgroup.smul_bot]
  -- (3) `Y := A ⊓ C_G(P)` has order `q` and is a line of `A` inside `C_E(P)`.
  set Y : Subgroup G := A ⊓ Subgroup.centralizer (P : Set G) with hYdef
  -- Coprime decomposition `A = C_A(P) × [A, P]` (`A` abelian, `P` acts coprimely).
  have hPNA : P ≤ Subgroup.normalizer (A : Set G) := hPE.trans hENA
  have hcopqp : Nat.Coprime q p :=
    (Nat.coprime_primes (Fact.out : q.Prime) (Fact.out : p.Prime)).mpr (Ne.symm hpne_q)
  have hcopAP : Nat.Coprime (Nat.card ↥A) (Nat.card ↥P) := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := p)).mp hPp
    rw [hAcard, hk]
    exact (hcopqp.pow_left 2).pow_right k
  obtain ⟨hYdisj, hYsup⟩ :=
    OddOrder.Isaacs.Ch05.fitting_coprime_abelian_decomp (P := A) (K := P) hPNA hcopAP
  -- rewrite `C_G(P) ⊓ A` as `Y = A ⊓ C_G(P)`.
  rw [inf_comm (Subgroup.centralizer (P : Set G)) A] at hYdisj hYsup
  rw [← hYdef] at hYdisj hYsup
  set W : Subgroup G := ⁅A, P⁆ with hWdef
  -- `[A, P] ≠ ⊥` exactly because `P` does not centralize `A`.
  have hWne : W ≠ ⊥ := by
    rw [hWdef, ne_eq, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro hAcP
    exact hPnotcA (Subgroup.le_centralizer_iff.mp hAcP)
  -- both `Y` and `W` are `q`-groups (subgroups of the elementary abelian `A`).
  have hYA : Y ≤ A := inf_le_left
  have hWA : W ≤ A := hYsup ▸ le_sup_right
  have hYq : IsPGroup q ↥Y := hA.1.isPGroup.to_le hYA
  have hWq : IsPGroup q ↥W := hA.1.isPGroup.to_le hWA
  -- `A` centralizes (hence normalizes) all its subgroups (it is abelian).
  have hYNW : Y ≤ Subgroup.normalizer (W : Set G) :=
    ((hYA.trans (le_centralizer_self_of_isElementaryAbelian hA.1)).trans
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hWA))).trans
      (Subgroup.centralizer_le_normalizer _)
  -- `|Y| * |W| = |Y ⊔ W| = |A| = q²`.
  have hYWcard : Nat.card ↥Y * Nat.card ↥W = q ^ 2 := by
    rw [← card_sup_eq_mul_of_le_normalizer_of_disjoint hYNW hYdisj, hYsup, hAcard]
  -- both factors are nontrivial: `Y ≠ ⊥` (`hCAP`) and `W ≠ ⊥` (`hWne`).
  have hYne : Y ≠ ⊥ := by rw [hYdef]; exact hCAP
  have hYcardq : q ∣ Nat.card ↥Y :=
    hYq.card_eq_or_dvd.resolve_left (fun h1 => hYne (Subgroup.card_eq_one.mp h1))
  have hWcardq : q ∣ Nat.card ↥W :=
    hWq.card_eq_or_dvd.resolve_left (fun h1 => hWne (Subgroup.card_eq_one.mp h1))
  -- from `|Y| * |W| = q²` with both divisible by `q`: `|Y| = q`.
  have hWcard : Nat.card ↥W = q := by
    obtain ⟨a, ha⟩ := hYcardq
    obtain ⟨b, hb⟩ := hWcardq
    have hqpos := (Fact.out : q.Prime).pos
    have hsq : q ^ 2 = q * q := sq q
    have key : q * q = q * (a * b * q) := by
      rw [← hsq, ← hYWcard, ha, hb]; ring
    have hab : a * b = 1 := by
      have h1 : q = a * b * q := Nat.eq_of_mul_eq_mul_left hqpos key
      nlinarith [h1, hqpos]
    have hb1 : b = 1 := Nat.eq_one_of_mul_eq_one_left hab
    rw [hb, hb1, mul_one]
  have hYcard : Nat.card ↥Y = q := by
    have hh := hYWcard
    rw [hWcard, sq] at hh
    exact Nat.eq_of_mul_eq_mul_right (Fact.out : q.Prime).pos hh
  have hYmem : Y ∈ elemAbelianOfRank G q 1 :=
    ⟨Subgroup.IsElementaryAbelian.of_card_prime hYcard, by rw [hYcard, pow_one]⟩
  have hYE : Y ≤ E := hYA.trans hAE
  have hYcP : Y ≤ Subgroup.centralizer (P : Set G) := inf_le_right
  -- (4) `𝓜(C_G(Y)) = {M}`.
  -- `q ∈ π(E)` (`Y ≤ E`, `|Y| = q`).
  have hqE : q ∈ (Nat.card ↥E).primeFactors := by
    refine Nat.mem_primeFactors.mpr ⟨Fact.out, ?_, Nat.card_pos.ne'⟩
    exact (hYcard ▸ Subgroup.card_dvd_of_le hYE)
  -- Theorem 13.4: `C_{M_σ}(P) ⊆ C_{M_σ}(Y)`.
  have h134 : S10.Msigma M ⊓ Subgroup.centralizer (P : Set G) ≤
      S10.Msigma M ⊓ Subgroup.centralizer (Y : Set G) :=
    centralizer_le_centralizer_of_tau1 hG h hp hqE hP hPE hYmem (le_inf hYE hYcP)
  have hCYne : S10.Msigma M ⊓ Subgroup.centralizer (Y : Set G) ≠ ⊥ := fun hbot =>
    hCPne (le_bot_iff.mp (hbot ▸ h134))
  -- Corollary 12.6(c): `𝓜(C_G(Y)) = {M}`.
  have hMY : maximalSubgroupsContaining (Subgroup.centralizer (Y : Set G)) = {M} :=
    h126.2.2.1 Y hYmem hYA hCYne
  -- (5) Pick `M* ∈ 𝓜(N_G(A))`; it is `≠ M` and contains `P`.
  have hAne : A ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥A = 1 := by rw [hbot]; exact Subgroup.card_bot
    rw [hAcard] at h1
    have hq1 : q ∣ 1 := h1 ▸ dvd_pow_self q (two_ne_zero)
    exact (Fact.out : q.Prime).one_lt.ne' (Nat.dvd_one.mp hq1)
  have hNAlt : Subgroup.normalizer (A : Set G) < ⊤ :=
    normalizer_lt_top_of_le_of_ne_bot hG h.mem_maximal hAM hAne
  obtain ⟨Mstar, hMstarCo, hNAMstar⟩ :=
    (eq_top_or_exists_le_coatom (Subgroup.normalizer (A : Set G))).resolve_left hNAlt.ne
  have hMstar : Mstar ∈ maximalSubgroupsContaining (Subgroup.normalizer (A : Set G)) :=
    mem_maximalSubgroupsContaining.mpr ⟨hMstarCo, hNAMstar⟩
  have hMstarMax : Mstar ∈ maximalSubgroups G := mem_maximalSubgroups.mpr hMstarCo
  -- `P ≤ N_G(A) ≤ M*` and `M* ≠ M` (12.6(b): `¬ N_G(A) ≤ M`).
  have hPMstar : P ≤ Mstar := ((hPE.trans hENA).trans hNAMstar)
  have hMstarneM : Mstar ≠ M := by
    rintro rfl
    exact h126.2.1.2.2 hNAMstar
  -- (6) Lemma 12.11: `q ∈ σ(M*)` and `p ∈ τ₁(M*) ∪ τ₂(M*)`.
  have htransfer := tau2_transfer_to_maximal hG h hq hA hAE hMstar
  have hqσstar : q ∈ S10.sigma Mstar := (htransfer.1 q Fact.out hq).1
  -- `p ∈ π(E/C_E(A))`: `C_E(A) ⊴ E` and the `p`-Sylow of `E` containing `P` is not in `C_E(A)`.
  have hENcA : E ≤
      Subgroup.normalizer ((E ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) : Set G) :=
    le_normalizer_inf Subgroup.le_normalizer (hENA.trans (normalizer_le_normalizer_centralizer A))
  have hCEAnorm : ((E ⊓ Subgroup.centralizer (A : Set G)).subgroupOf E).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr hENcA
  -- `P.subgroupOf E` is a `p`-group; take a Sylow `p`-subgroup `Sp ⊇ P` of `↥E`.
  have hPEpgroup : IsPGroup p ↥(P.subgroupOf E) :=
    hPp.of_equiv (Subgroup.subgroupOfEquivOfLe hPE).symm
  obtain ⟨Sp, hPSp⟩ := hPEpgroup.exists_le_sylow
  have hpidx : p ∈ (((E ⊓ Subgroup.centralizer (A : Set G)).subgroupOf E).index).primeFactors := by
    refine Nat.mem_primeFactors.mpr ⟨Fact.out, ?_, Subgroup.index_ne_zero_of_finite⟩
    refine prime_dvd_index_of_sylow_not_le_of_normal Sp (fun hSple => ?_)
    -- if the Sylow `Sp ⊆ C_E(A)`, then `P ⊆ C_G(A)`, contradicting step 2.
    have hPCA : P ≤ Subgroup.centralizer (A : Set G) := by
      intro x hx
      have hxE : (⟨x, hPE hx⟩ : ↥E) ∈ P.subgroupOf E := Subgroup.mem_subgroupOf.mpr hx
      have hxin := hSple (hPSp hxE)
      rw [Subgroup.mem_subgroupOf] at hxin
      exact (Subgroup.mem_inf.mp hxin).2
    exact hPnotcA hPCA
  have hpτstar : p ∈ tau1 Mstar ∪ tau2 Mstar := htransfer.2.1 p hpidx
  -- (7)–(8): split on `p ∈ τ₂(M*)` vs `p ∈ τ₁(M*)`.
  -- `A ≤ M*` (via `A ≤ N_G(A) ≤ M*`) and `A ≤ M*_σ` (`q ∈ σ(M*)`, `A` a `q`-group).
  have hAMstar : A ≤ Mstar := (Subgroup.le_normalizer).trans hNAMstar
  have hAMσstar : A ≤ S10.Msigma Mstar :=
    le_Msigma_of_mem_elemAbelianOfRank_of_mem_sigma hG hMstarMax Fact.out hqσstar hA hAMstar
  -- `1 ⊂ Y ≤ C_{M*_σ}(P)` (`Y ≤ A ≤ M*_σ` and `Y ≤ C_G(P)`).
  have hCMσstarP : S10.Msigma Mstar ⊓ Subgroup.centralizer (P : Set G) ≠ ⊥ := by
    refine fun hbot => hYne (le_bot_iff.mp (hbot ▸ ?_))
    exact le_inf (hYA.trans hAMσstar) hYcP
  -- `P` is a `σ(M*)'`-subgroup (`p ∉ σ(M*)` in both branches).
  have hP_pi : p ∉ S10.sigma Mstar → Subgroup.IsPiSubgroup ((S10.sigma Mstar)ᶜ) P := by
    intro hpσstar s hs
    obtain ⟨hsp, hsd, _⟩ := Nat.mem_primeFactors.mp hs
    obtain ⟨n, hn⟩ := hPp.exists_card_eq
    rw [hn] at hsd
    rwa [(Nat.prime_dvd_prime_iff_eq hsp Fact.out).mp (hsp.dvd_of_dvd_pow hsd)]
  rcases hpτstar with hpτ1star | hpτ2star
  · -- (8) `p ∈ τ₁(M*)`: contradiction with step 4 via Lemma 13.6 for `M*`.
    have hpσstar : p ∉ S10.sigma Mstar := hpτ1star.1
    -- complement `E* ⊇ P` of `M*_σ` in `M*`.
    obtain ⟨Es, Es1, Es2, Es3, hsetupS, hPEs, _⟩ :=
      exists_subgroupESetup_with_le hG hMstarMax hPMstar (hP_pi hpσstar)
    -- conjugate the setup so that `P` lies in its `τ₁`-Hall piece (Hall conjugacy in `↥E*`).
    obtain ⟨c, hcEs, hPcEs1⟩ := exists_conj_le_tau1_piece hG hsetupS hpτ1star hPp hPEs
    have hcMstar : c ∈ Mstar := hsetupS.E_le hcEs
    set hsetupS' := SubgroupESetup.conj' hsetupS (Mstar.inv_mem hcMstar) with hsetupS'def
    -- `P ≤ conj c⁻¹ • Es1` (the `τ₁`-piece of the conjugated setup).
    have hPEs1' : P ≤ MulAut.conj c⁻¹ • Es1 := by
      have h1 : MulAut.conj c⁻¹ • (MulAut.conj c • P) ≤ MulAut.conj c⁻¹ • Es1 :=
        Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hPcEs1
      rwa [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul] at h1
    -- a Sylow `q`-subgroup `S` of `M*_σ` (maximal `q`-subgroup of `M*_σ`).
    obtain ⟨S, hSMσstar, hSq, _, hScard⟩ := exists_einvariant_sylow_Msigma hG hsetupS q
    have hSmax : ∀ T : Subgroup G, T ≤ S10.Msigma Mstar → IsPGroup q ↥T → S ≤ T → S = T :=
      fun T hTM hTq hST => eq_of_le_of_isPGroup_card_eq_factorization hScard hTM hTq hST
    -- `Y ≤ M*_σ ⊓ C_G(P)`.
    have hYCstar : Y ≤ S10.Msigma Mstar ⊓ Subgroup.centralizer (P : Set G) :=
      le_inf (hYA.trans hAMσstar) hYcP
    -- Lemma 13.6 for `M*`: `𝓜(C_G(Y)) = {M*}`.
    have hMstarY : maximalSubgroupsContaining (Subgroup.centralizer (Y : Set G)) = {Mstar} :=
      (maximalContaining_eq_singleton_of_E1 hG hsetupS' hqσstar hPEs1' hPne hYmem hYCstar
        hSMσstar hSq hSmax).1
    -- contradiction with step 4 (`𝓜(C_G(Y)) = {M}`, `M* ≠ M`).
    rw [hMstarY] at hMY
    exact hMstarneM (Set.singleton_injective hMY)
  · -- (7) `p ∈ τ₂(M*)`: contradiction with Theorem 12.5(e) for the original `M`.
    have hpσstar : p ∉ S10.sigma Mstar := hpτ2star.1
    -- complement `E* ⊇ P` of `M*_σ` in `M*`, and a rank-2 `A* ∈ ℰ_p²(E*)`.
    obtain ⟨Es, Es1, Es2, Es3, hsetupS, hPEs, _⟩ :=
      exists_subgroupESetup_with_le hG hMstarMax hPMstar (hP_pi hpσstar)
    obtain ⟨As, hAsmem, hAsEs⟩ := exists_elemAb_rank_two_le_E_of_tau2 hG hsetupS hpτ2star
    -- 12.6(a)/M*: `ℰ_p¹(E*) = ℰ¹(A*)`, hence `P ≤ A*`.
    have hPAs : P ≤ As :=
      ((elemAb_normal_in_E_of_tau2 hG hsetupS hpτ2star hAsmem hAsEs).1.2 P hP).mp hPEs
    -- 12.6(c)/M*: `𝓜(C_G(P)) = {M*}`.
    have hMstarCP : maximalSubgroupsContaining (Subgroup.centralizer (P : Set G)) = {Mstar} :=
      (elemAb_normal_in_E_of_tau2 hG hsetupS hpτ2star hAsmem hAsEs).2.2.1 P hP hPAs hCMσstarP
    -- pick `z ∈ (M_σ ⊓ C_G(P))#`; then `z ∈ C_G(P) ≤ M*` and `z ∈ M_σ`, so `M_σ ⊓ M* ≠ ⊥`.
    obtain ⟨z, hzmem, hzne⟩ := (Subgroup.bot_or_exists_ne_one _).resolve_left hCPne
    obtain ⟨hzMσ, hzCP⟩ := Subgroup.mem_inf.mp hzmem
    have hCPlt : Subgroup.centralizer (P : Set G) < ⊤ :=
      lt_of_le_of_lt (Subgroup.centralizer_le_normalizer _)
        (normalizer_lt_top_of_le_of_ne_bot hG h.mem_maximal hPM hPne)
    obtain ⟨Mst', hco', hle'⟩ := (eq_top_or_exists_le_coatom _).resolve_left hCPlt.ne
    have hMst'mem : Mst' ∈ maximalSubgroupsContaining (Subgroup.centralizer (P : Set G)) :=
      mem_maximalSubgroupsContaining.mpr ⟨hco', hle'⟩
    have hMst'eq : Mst' = Mstar := by rw [hMstarCP] at hMst'mem; exact hMst'mem
    have hzMstar : z ∈ Mstar := hMst'eq ▸ hle' hzCP
    -- Theorem 12.5(e) for the original `(M, q, A)`: `M_σ ⊓ M* = ⊥` (since `M* ∈ ℳ(A)`, `M* ≠ M`).
    have h125e : S10.Msigma M ⊓ Mstar = ⊥ :=
      (Msigma_nilpotent_of_tau2 hG h.mem_maximal hq hA hAM).2.2.2.2.1 Mstar
        (mem_maximalSubgroupsContaining.mpr ⟨hMstarCo, hAMstar⟩) hMstarneM
    -- contradiction: `z ∈ M_σ ⊓ M* = ⊥` but `z ≠ 1`.
    exact hzne (by
      have : z ∈ S10.Msigma M ⊓ Mstar := Subgroup.mem_inf.mpr ⟨hzMσ, hzMstar⟩
      rwa [h125e, Subgroup.mem_bot] at this)

/-- From `ℳ(C_G(X)) = {M}` (and `X ≤ M`, `X ≠ ⊥`) conclude `C_G(X) ≤ M`: the centralizer is a
proper subgroup (its normalizer is `< ⊤`), so it lies in some coatom, which must be the unique `M`
containing it. Used twice in Lemma 13.13 (`C_G(Q) ≤ M`). -/
private theorem centralizer_le_M_of_maximalContaining_eq_singleton [Finite G]
    (hG : IsMinimalSimpleOdd G) {M X : Subgroup G} (hM : M ∈ maximalSubgroups G) (hXM : X ≤ M)
    (hXne : X ≠ ⊥)
    (hMX : maximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) = {M}) :
    Subgroup.centralizer (X : Set G) ≤ M := by
  have hCXlt : Subgroup.centralizer (X : Set G) < ⊤ :=
    lt_of_le_of_lt (Subgroup.centralizer_le_normalizer _)
      (normalizer_lt_top_of_le_of_ne_bot hG hM hXM hXne)
  obtain ⟨W, hWco, hWle⟩ := (eq_top_or_exists_le_coatom _).resolve_left hCXlt.ne
  have hWmem : W ∈ maximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) :=
    mem_maximalSubgroupsContaining.mpr ⟨hWco, hWle⟩
  rw [hMX, Set.mem_singleton_iff] at hWmem
  rw [hWmem] at hWle
  exact hWle

/-- **BG Lemma 13.13** (mmd L3765): if `p ∈ τ₁(M) ∪ τ₃(M)`, `P ∈ ℰ_p¹(E)`, and `C_{M_σ}(P) ≠ 1`,
then `p ∈ σ(M*)` for every `M* ∈ 𝓜(N_G(P))`.

Proof (BG L3767): by Lemma 12.2, `p ∈ σ(M*) ∪ τ₂(M*)`; suppose `p ∈ τ₂(M*)`.  Pick
`q ∈ π(C_{M_σ}(P))`, `Q ∈ ℰ_q¹(C_{M_σ}(P))`; by Theorem 13.9, `q ∉ σ(M*)`.  Let `E*` be a
complement of `M*_σ` in `M*` containing `PQ`, and `A ∈ ℰ_p²(E*)`; by Corollary 12.6(a), `A ◁ E*`
and `P ⊆ A`.  WLOG `P ≤ E₁` or `P ≤ E₃` (using Corollary 13.11 when `P ⊆ E₃`); Lemma 13.6 gives
`C_G(Q) ⊆ M`, so `A ⊄ C_{E*}(Q)` (as `r_p(M) = 1`), whence `q ∈ τ₁(M*)` by Corollary 12.10(c) and
`P = C_A(Q)`.  Lemma 13.12 for `M*` gives `C_{M*_σ}(Q) = 1`, and Corollary 12.9(c) then yields
`N_G(P) ⊄ M*`, contradicting `M* ∈ 𝓜(N_G(P))`.

Statement draft = Lane H (issue 2006); proof = Lane F (uses Lemma 13.12, 順序注意). -/
theorem mem_sigma_of_tau1_tau3_centralize [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    {p : ℕ} [Fact p.Prime] (hp : p ∈ tau1 M ∪ tau3 M)
    {P : Subgroup G} (hP : P ∈ elemAbelianOfRank G p 1) (hPE : P ≤ E)
    (hCP : S10.Msigma M ⊓ Subgroup.centralizer (P : Set G) ≠ ⊥)
    {Mstar : Subgroup G}
    (hMstar : Mstar ∈ maximalSubgroupsContaining (Subgroup.normalizer (P : Set G))) :
    p ∈ S10.sigma Mstar := by
  classical
  -- Unpack `M* ∈ ℳ(N_G(P))`.
  obtain ⟨hMstarCo, hNPMstar⟩ := mem_maximalSubgroupsContaining.mp hMstar
  have hMstarMax : Mstar ∈ maximalSubgroups G := mem_maximalSubgroups.mpr hMstarCo
  -- Basic facts about `P`.
  have hPp : IsPGroup p ↥P := hP.1.isPGroup
  have hPne : P ≠ ⊥ := ne_bot_of_mem_elemAbelianOfRank_one hP
  have hPM : P ≤ M := hPE.trans h.E_le
  have hpσ : p ∉ S10.sigma M := by
    rcases hp with h1 | h3
    · exact h1.1
    · exact h3.1
  have hpr1M : pRank ↥M p = 1 := by
    rcases hp with h1 | h3
    · exact tau1_pRank_eq_one h1
    · exact tau3_pRank_eq_one h3
  have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups h.mem_maximal
  have : Group.IsSolvable ↥E :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective h.E_le)
  -- `P ≤ N_G(P) ≤ M*`.
  have hPMstar : P ≤ Mstar := Subgroup.le_normalizer.trans hNPMstar
  -- (0) `M*` is not conjugate to `M` (Lemma 12.2(b), τ₁∪τ₃ form).
  have hMstarnc : ¬ ∃ g : G, MulAut.conj g • M = Mstar :=
    not_conj_of_mem_tau1_union_tau3_of_normalizer_le hG h.mem_maximal hp hPM hPne hPp hNPMstar
  have hMstarneM : Mstar ≠ M := by
    rintro rfl; exact hMstarnc ⟨1, by rw [map_one, one_smul]⟩
  -- `σ(M) ∩ σ(M*) = ∅` (Theorem 13.9).
  have hσdisj : Disjoint (S10.sigma M) (S10.sigma Mstar) :=
    sigma_disjoint_of_nonconjugate hG h.mem_maximal hMstarMax hMstarnc
  -- By contradiction: assume `p ∉ σ(M*)`; via Lemma 12.2(a) this gives `p ∈ τ₂(M*)`.
  by_contra hpσstar
  have hpτ2star : p ∈ tau2 Mstar :=
    (prime_mem_sigma_or_tau2 hG h.mem_maximal hPM hPne hPp hMstar).resolve_left hpσstar
  -- (0') Pick `q ∈ π(C_{M_σ}(P))`, build `Q ∈ ℰ_q¹(C_{M_σ}(P))`, `q ∈ σ(M)`, `q ∉ σ(M*)`, `q ≠ p`.
  set C : Subgroup G := S10.Msigma M ⊓ Subgroup.centralizer (P : Set G) with hCdef
  obtain ⟨q, hqp, hqdvd⟩ :=
    (Nat.card ↥C).exists_prime_and_dvd (fun hc => hCP (Subgroup.card_eq_one.mp hc))
  have : Fact q.Prime := ⟨hqp⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := ↥C) q hqdvd
  set Q : Subgroup G := Subgroup.zpowers (a : G) with hQdef
  have hQcard : Nat.card ↥Q = q := by
    rw [hQdef, Nat.card_zpowers]
    exact (orderOf_injective C.subtype C.subtype_injective a).trans ha
  have hQmem : Q ∈ elemAbelianOfRank G q 1 :=
    ⟨Subgroup.IsElementaryAbelian.of_card_prime hQcard, by rw [hQcard, pow_one]⟩
  have hQq : IsPGroup q ↥Q := hQmem.1.isPGroup
  have hQne : Q ≠ ⊥ := ne_bot_of_mem_elemAbelianOfRank_one hQmem
  -- `Q ≤ C = M_σ ⊓ C_G(P)`.
  have hQC : Q ≤ C := by
    rw [hQdef]; exact Subgroup.zpowers_le.mpr a.2
  have hQMσ : Q ≤ S10.Msigma M := hQC.trans inf_le_left
  have hQcP : Q ≤ Subgroup.centralizer (P : Set G) := hQC.trans inf_le_right
  -- `q ∈ σ(M)` (`Q ≤ M_σ`, `M_σ` is a `σ(M)`-group).
  have hqσ : q ∈ S10.sigma M :=
    S10.Msigma_isPiGroup M q (Nat.mem_primeFactors.mpr
      ⟨hqp, (hQcard ▸ Subgroup.card_dvd_of_le hQMσ), Nat.card_pos.ne'⟩)
  -- `q ∉ σ(M*)` (Theorem 13.9), so `q ≠ p` (`p ∉ σ(M)` but `q ∈ σ(M)`).
  have hqσstar : q ∉ S10.sigma Mstar := fun hh => hσdisj.ne_of_mem hqσ hh rfl
  have hpne_q : p ≠ q := fun hpq => hpσ (hpq ▸ hqσ)
  -- `P, Q ≤ M*` (`Q ≤ C_G(P) ≤ N_G(P) ≤ M*`).
  have hQMstar : Q ≤ Mstar :=
    (hQcP.trans ((Subgroup.centralizer_le_normalizer _).trans hNPMstar))
  -- `M_σ ⊴ M`, used to conjugate `C_{M_σ}(·)`.
  have hMnormMσ : M ≤ Subgroup.normalizer ((S10.Msigma M : Subgroup G) : Set G) :=
    le_normalizer_opiCoreInG _ _
  -- ===========================================================================
  -- Step 1: `C_G(Q) ≤ M`.  Case split on `p ∈ τ₃(M)` vs `p ∈ τ₁(M)`.
  -- ===========================================================================
  have hCGQ_le_M : Subgroup.centralizer (Q : Set G) ≤ M := by
    rcases hp with hpτ1 | hpτ3
    · -- τ₁ case: conjugate `P` into the `τ₁`-Hall piece `E₁` and apply Lemma 13.6.
      obtain ⟨e, heE, hPeE1⟩ := exists_conj_le_tau1_piece hG h hpτ1 hPp hPE
      have heM : e ∈ M := h.E_le heE
      set Pe : Subgroup G := MulAut.conj e • P with hPedef
      set Qe : Subgroup G := MulAut.conj e • Q with hQedef
      -- `Pe ≠ ⊥`, `Pe ∈ ℰ_p¹(E₁)`.
      have hPene : Pe ≠ ⊥ := by
        rw [hPedef]; intro hbot
        exact hPne (by simpa using congrArg (MulAut.conj e⁻¹ • ·) hbot)
      -- `Qe ∈ ℰ_q¹`.
      have hQemem : Qe ∈ elemAbelianOfRank G q 1 := conj_smul_mem_elemAbelianOfRank e hQmem
      -- `Qe ≤ C_{M_σ}(Pe)` (conjugating `Q ≤ C_{M_σ}(P)` by `e`, using `M_σ^e = M_σ`).
      have hMσe : MulAut.conj e • S10.Msigma M = S10.Msigma M :=
        conj_smul_eq_self_of_mem_normalizer (hMnormMσ heM)
      have hQeC : Qe ≤ S10.Msigma M ⊓ Subgroup.centralizer (Pe : Set G) := by
        have h1 : MulAut.conj e • Q ≤
            MulAut.conj e • (S10.Msigma M ⊓ Subgroup.centralizer (P : Set G)) :=
          Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr (le_inf hQMσ hQcP)
        rwa [Subgroup.smul_inf, hMσe, conj_smul_centralizer, ← hPedef, ← hQedef] at h1
      -- a Sylow `q`-subgroup `S` of `M_σ` containing `Qe`.
      obtain ⟨S, hSMσ, hSq, _, hScard⟩ := exists_einvariant_sylow_Msigma hG h q
      have hSmax : ∀ T : Subgroup G, T ≤ S10.Msigma M → IsPGroup q ↥T → S ≤ T → S = T :=
        fun T hTM hTq hST => eq_of_le_of_isPGroup_card_eq_factorization hScard hTM hTq hST
      -- Lemma 13.6 (for `M`, with line `Pe ≤ E₁`): `ℳ(C_G(Qe)) = {M}`.
      have hMQe : maximalSubgroupsContaining (Subgroup.centralizer (Qe : Set G)) = {M} :=
        (maximalContaining_eq_singleton_of_E1 hG h hqσ hPeE1 hPene hQemem hQeC hSMσ hSq hSmax).1
      -- `Qe ≤ M` (`Q ≤ M_σ ≤ M`, `e ∈ M`).
      have hQeM : Qe ≤ M := by
        rw [hQedef]
        calc MulAut.conj e • Q ≤ MulAut.conj e • M :=
              Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr (hQMσ.trans (S10.Msigma_le M))
          _ = M := conj_smul_eq_self_of_mem_normalizer (Subgroup.le_normalizer heM)
      -- `C_G(Qe) ≤ M`.  Then conjugate back by `e⁻¹` (using `M^e = M`).
      have hCGQe_le_M : Subgroup.centralizer (Qe : Set G) ≤ M :=
        centralizer_le_M_of_maximalContaining_eq_singleton hG h.mem_maximal hQeM
          (ne_bot_of_mem_elemAbelianOfRank_one hQemem) hMQe
      -- transport: `C_G(Q) = conj e⁻¹ • C_G(Qe) ≤ conj e⁻¹ • M = M`.
      have hMe : MulAut.conj e⁻¹ • M = M :=
        conj_smul_eq_self_of_mem_normalizer (Subgroup.le_normalizer (M.inv_mem heM))
      have hQecc : MulAut.conj e⁻¹ • Qe = Q := by
        rw [hQedef, ← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
      calc Subgroup.centralizer (Q : Set G)
          = MulAut.conj e⁻¹ • Subgroup.centralizer (Qe : Set G) := by
            rw [conj_smul_centralizer, hQecc]
        _ ≤ MulAut.conj e⁻¹ • M :=
            Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hCGQe_le_M
        _ = M := hMe
    · -- τ₃ case: `P ≤ E₃`, then Corollary 13.11 (E₃ non-regular) gives `E` prime on `M_σ`.
      -- `P ≤ E₃`: `P.subgroupOf E` is a `τ₃`-group, `E₃.subgroupOf E` a normal Hall `τ₃`-subgroup.
      have hPE3 : P ≤ E₃ := by
        have hEN3 : E ≤ Subgroup.normalizer ((E₃ : Subgroup G) : Set G) := h.E3_normal hG
        have hE3subN : (E₃.subgroupOf E).Normal :=
          (Subgroup.normal_subgroupOf_iff_le_normalizer h.E₃_le).mpr hEN3
        have hPEpi : Ch03.Subgroup.IsPiGroup (tau3 M) (P.subgroupOf E) := by
          intro s hs
          rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPE).toEquiv] at hs
          obtain ⟨n, hn⟩ := hPp.exists_card_eq
          rw [hn, Nat.mem_primeFactors] at hs
          exact ((Nat.prime_dvd_prime_iff_eq hs.1 Fact.out).mp (hs.1.dvd_of_dvd_pow hs.2.1)) ▸ hpτ3
        have hsub : P.subgroupOf E ≤ E₃.subgroupOf E :=
          isPiSubgroup_le_of_normal_isHall h.E₃_hall hPEpi
        intro x hx
        have hxE : (⟨x, hPE hx⟩ : ↥E) ∈ P.subgroupOf E := Subgroup.mem_subgroupOf.mpr hx
        have hxin := hsub hxE
        rw [Subgroup.mem_subgroupOf] at hxin
        exact hxin
      -- `E₃ ≠ ⊥` (contains `P ≠ ⊥`).
      have hE3ne : E₃ ≠ ⊥ := fun hbot => hPne (le_bot_iff.mp (hbot ▸ hPE3))
      -- `E₃` does not act regularly on `M_σ`: some `x ∈ P# ⊆ E₃#` has `C_{M_σ}(x) ≠ 1`
      -- (witnessed by `Q ≤ C_{M_σ}(P) ≤ C_{M_σ}(x)`).
      have hE3nonreg : ¬ ActsRegularlyOn (S10.Msigma M) E₃ := by
        obtain ⟨x, hxP, hxne⟩ := (Subgroup.bot_or_exists_ne_one P).resolve_left hPne
        intro hreg
        have hxE3 : x ∈ E₃ := hPE3 hxP
        have hbot : S10.Msigma M ⊓ Subgroup.centralizer ({x} : Set G) = ⊥ := by
          have := hreg x hxE3 hxne; rwa [fixedByElement_def] at this
        -- `Q ≤ M_σ ⊓ C_G(x)` (via `Q ≤ C_G(P)` and `x ∈ P`).
        apply hQne
        refine le_bot_iff.mp (hbot ▸ le_inf hQMσ ?_)
        refine hQcP.trans (Subgroup.centralizer_le ?_)
        intro y hy; rw [Set.mem_singleton_iff.mp hy]; exact SetLike.mem_coe.mpr hxP
      -- Corollary 13.11: `E₁ ≠ ⊥` and `E` acts in a prime manner on `M_σ`.
      obtain ⟨hE1ne, _hEsup, hEprime, _hEnormX⟩ :=
        E3_not_regular_consequences hG h hE3ne hE3nonreg
      -- `C_{M_σ}(P) = C_{M_σ}(E₁)` (`E` prime on `M_σ`: both equal `C_{M_σ}(E)`).
      have hE1neP : (E₁ : Subgroup G) ≠ ⊥ := hE1ne
      have hCPE : fixedBy (S10.Msigma M) P = fixedBy (S10.Msigma M) E :=
        fixedBy_eq_of_le_of_ne_bot hEprime (hPE3.trans h.E₃_le) hPne
      have hCE1E : fixedBy (S10.Msigma M) E₁ = fixedBy (S10.Msigma M) E :=
        fixedBy_eq_of_le_of_ne_bot hEprime h.E₁_le hE1neP
      -- So `Q ≤ C_{M_σ}(E₁)`.
      have hQCE1 : Q ≤ S10.Msigma M ⊓ Subgroup.centralizer (E₁ : Set G) := by
        have hQfix : Q ≤ fixedBy (S10.Msigma M) E₁ := by
          rw [hCE1E, ← hCPE, fixedBy_def]; exact le_inf hQMσ hQcP
        rwa [fixedBy_def] at hQfix
      -- Pick a prime-order subgroup `P' ∈ ℰ_r¹(E₁)`.
      obtain ⟨r, hrp, hrdvd⟩ :=
        (Nat.card ↥E₁).exists_prime_and_dvd (fun hc => hE1ne (Subgroup.card_eq_one.mp hc))
      have : Fact r.Prime := ⟨hrp⟩
      obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := ↥E₁) r hrdvd
      set P' : Subgroup G := Subgroup.zpowers (b : G) with hP'def
      have hP'card : Nat.card ↥P' = r := by
        rw [hP'def, Nat.card_zpowers]
        exact (orderOf_injective E₁.subtype E₁.subtype_injective b).trans hb
      have hP'E1 : P' ≤ E₁ := Subgroup.zpowers_le.mpr b.2
      have hP'mem : P' ∈ elemAbelianOfRank G r 1 :=
        ⟨Subgroup.IsElementaryAbelian.of_card_prime hP'card, by rw [hP'card, pow_one]⟩
      have hP'ne : P' ≠ ⊥ := ne_bot_of_mem_elemAbelianOfRank_one hP'mem
      -- `Q ≤ C_{M_σ}(P')` (since `Q ≤ C_{M_σ}(E₁) ≤ C_{M_σ}(P')`).
      have hQCP' : Q ≤ S10.Msigma M ⊓ Subgroup.centralizer (P' : Set G) :=
        le_inf hQMσ (hQCE1.trans (inf_le_right.trans
          (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hP'E1))))
      -- a Sylow `q`-subgroup `S` of `M_σ`.
      obtain ⟨S, hSMσ, hSq, _, hScard⟩ := exists_einvariant_sylow_Msigma hG h q
      have hSmax : ∀ T : Subgroup G, T ≤ S10.Msigma M → IsPGroup q ↥T → S ≤ T → S = T :=
        fun T hTM hTq hST => eq_of_le_of_isPGroup_card_eq_factorization hScard hTM hTq hST
      -- Lemma 13.6 (for `M`, line `P' ≤ E₁`): `ℳ(C_G(Q)) = {M}`, so `C_G(Q) ≤ M`.
      have hMQ : maximalSubgroupsContaining (Subgroup.centralizer (Q : Set G)) = {M} :=
        (maximalContaining_eq_singleton_of_E1 hG h hqσ hP'E1 hP'ne hQmem hQCP' hSMσ hSq hSmax).1
      exact centralizer_le_M_of_maximalContaining_eq_singleton hG h.mem_maximal
        (hQMσ.trans (S10.Msigma_le M)) hQne hMQ
  -- ===========================================================================
  -- Step 2: build `M*`'s setup with `E* ⊇ PQ`, `A ∈ ℰ_p²(E*)`, `P ≤ A`.
  -- ===========================================================================
  -- `P` and `Q` commute (`Q ≤ C_G(P)`), so `PQ := P ⊔ Q` is their internal direct product.
  have hPcQ : P ≤ Subgroup.centralizer (Q : Set G) := by
    intro x hx; rw [Subgroup.mem_centralizer_iff]; intro y hy
    exact (Subgroup.mem_centralizer_iff.mp (hQcP hy) x hx).symm
  set PQ : Subgroup G := P ⊔ Q with hPQdef
  have hPQMstar : PQ ≤ Mstar := sup_le hPMstar hQMstar
  -- `PQ` is a `σ(M*)'`-subgroup (its prime factors are `{p, q} ⊆ σ(M*)ᶜ`).
  have hPcardp : Nat.card ↥P = p := by rw [hP.2, pow_one]
  have hPQ_pi : Subgroup.IsPiSubgroup ((S10.sigma Mstar)ᶜ) PQ := by
    -- `P ⊓ Q = ⊥` (coprime orders `p ≠ q`), commuting ⟹ `|PQ| = |P| * |Q| = p * q`.
    have hPNQ : P ≤ Subgroup.normalizer (Q : Set G) :=
      hPcQ.trans (Subgroup.centralizer_le_normalizer _)
    have hcopPQ : Nat.Coprime (Nat.card ↥P) (Nat.card ↥Q) := by
      rw [hPcardp, hQcard]; exact (Nat.coprime_primes Fact.out Fact.out).mpr hpne_q
    have hPQinf : P ⊓ Q = ⊥ := (Subgroup.disjoint_of_coprime_natCard hcopPQ).eq_bot
    have hcardPQ : Nat.card ↥PQ = p * q := by
      rw [hPQdef, card_sup_eq_mul_of_le_normalizer_of_disjoint hPNQ hPQinf, hPcardp, hQcard]
    intro s hs
    rw [hcardPQ] at hs
    obtain ⟨hsp, hsd, _⟩ := Nat.mem_primeFactors.mp hs
    rcases (Nat.Prime.dvd_mul hsp).mp hsd with hsp' | hsq'
    · rw [(Nat.prime_dvd_prime_iff_eq hsp Fact.out).mp hsp']; exact hpσstar
    · rw [(Nat.prime_dvd_prime_iff_eq hsp Fact.out).mp hsq']; exact hqσstar
  -- complement `E* ⊇ PQ` of `M*_σ` in `M*`.
  obtain ⟨Es, Es1, Es2, Es3, hsetupS, hPQEs, _⟩ :=
    exists_subgroupESetup_with_le hG hMstarMax hPQMstar hPQ_pi
  have hPEs : P ≤ Es := le_sup_left.trans hPQEs
  have hQEs : Q ≤ Es := le_sup_right.trans hPQEs
  -- `A ∈ ℰ_p²(E*)` and `P ≤ A` (Cor 12.6(a)/M*).
  obtain ⟨A, hAmem, hAEs⟩ := exists_elemAb_rank_two_le_E_of_tau2 hG hsetupS hpτ2star
  have hPA : P ≤ A :=
    ((elemAb_normal_in_E_of_tau2 hG hsetupS hpτ2star hAmem hAEs).1.2 P hP).mp hPEs
  -- ===========================================================================
  -- Step 3: `⁅A, Q⁆ ≠ ⊥`.
  -- ===========================================================================
  have hAQne : ⁅A, Q⁆ ≠ ⊥ := by
    rw [ne_eq, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro hAcQ
    -- `A ≤ C_G(Q) ≤ M`, a rank-2 elem-ab `p`-subgroup of `M`, contra `r_p(M) = 1`.
    have hAM : A ≤ M := hAcQ.trans hCGQ_le_M
    have hcardA : Nat.card ↥(A.subgroupOf M) = p ^ 2 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAM).toEquiv]; exact hAmem.2
    have hAelM' : (A.subgroupOf M).IsElementaryAbelian p :=
      IsElementaryAbelian.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hAM).symm hAmem.1
    have h2le : 2 ≤ pRank ↥M p := by
      have := le_pRank (A.subgroupOf M) hAelM'
      rw [hcardA, Nat.log_pow (Fact.out : p.Prime).one_lt] at this
      exact this
    omega
  -- `Q ⊄ C_G(A)` follows: `Q ≤ C_G(A) ↔ A ≤ C_G(Q)`, which would give `⁅A, Q⁆ = ⊥`.
  have hQnotcA : ¬ Q ≤ Subgroup.centralizer (A : Set G) := by
    intro hQcA
    apply hAQne
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact Subgroup.le_centralizer_iff.mp hQcA
  -- ===========================================================================
  -- Step 4: endgame.  12.10(c) ⟹ `q ∈ τ₁(M*)`; `P = C_A(Q)`; 13.12/M* + 12.9(c) ⟹ ⊥.
  -- ===========================================================================
  -- 12.10(c)/M*: `∀ r ∈ π(E*/C_{E*}(A)), r ∈ τ₁(M*)`; show `q` is such an `r`.
  have h1210c := (nilpotent_sigmaComplement_abelian hG hsetupS).2.2.1 p Fact.out hpτ2star A hAmem
    hAEs
  have hqidx :
      q ∈ (((Es ⊓ Subgroup.centralizer (A : Set G)).subgroupOf Es).index).primeFactors := by
    refine Nat.mem_primeFactors.mpr ⟨Fact.out, ?_, Subgroup.index_ne_zero_of_finite⟩
    -- `Q.subgroupOf Es` is a `q`-group not contained in `C_{E*}(A)` (else `Q ≤ C_G(A)`).
    have hCEsAnorm : ((Es ⊓ Subgroup.centralizer (A : Set G)).subgroupOf Es).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr h1210c.2.1
    have hQEspg : IsPGroup q ↥(Q.subgroupOf Es) :=
      hQq.of_equiv (Subgroup.subgroupOfEquivOfLe hQEs).symm
    obtain ⟨Sq, hQSq⟩ := hQEspg.exists_le_sylow
    refine prime_dvd_index_of_sylow_not_le_of_normal Sq (fun hSqle => ?_)
    apply hQnotcA
    intro x hx
    have hxEs : (⟨x, hQEs hx⟩ : ↥Es) ∈ Q.subgroupOf Es := Subgroup.mem_subgroupOf.mpr hx
    have hxin := hSqle (hQSq hxEs)
    rw [Subgroup.mem_subgroupOf] at hxin
    exact (Subgroup.mem_inf.mp hxin).2
  have hqτ1star : q ∈ tau1 Mstar := h1210c.2.2 q hqidx
  -- `P = A ⊓ C_G(Q)` (`= C_A(Q)`).
  -- First `1 < P ≤ A ⊓ C_G(Q)`, then `|A ⊓ C_G(Q)| = p`, hence equality.
  set Y : Subgroup G := A ⊓ Subgroup.centralizer (Q : Set G) with hYdef
  have hPY : P ≤ Y := le_inf hPA hPcQ
  have hYne : Y ≠ ⊥ := fun hbot => hPne (le_bot_iff.mp (hbot ▸ hPY))
  -- Coprime decomposition `A = C_A(Q) × ⁅A, Q⁆` (`A` abelian, `Q` acts coprimely).
  have hAcomm : IsMulCommutative ↥A := ⟨⟨hAmem.1.comm⟩⟩
  have hQNA : Q ≤ Subgroup.normalizer (A : Set G) :=
    (hQEs.trans (elemAb_normal_in_E_of_tau2 hG hsetupS hpτ2star hAmem hAEs).1.1)
  have hcopAQ : Nat.Coprime (Nat.card ↥A) (Nat.card ↥Q) := by
    rw [hAmem.2, hQcard]
    exact Nat.Coprime.pow_left _ ((Nat.coprime_primes Fact.out Fact.out).mpr hpne_q)
  obtain ⟨hYdisj, hYsup⟩ :=
    OddOrder.Isaacs.Ch05.fitting_coprime_abelian_decomp (P := A) (K := Q) hQNA hcopAQ
  rw [inf_comm (Subgroup.centralizer (Q : Set G)) A] at hYdisj hYsup
  rw [← hYdef] at hYdisj hYsup
  -- abstract the commutator behind `W` (`set` avoids `whnf` runaway on the raw `⁅A,Q⁆` notation
  -- when used as a motive for `▸`; mirrors Lemma 13.12's `set W := ⁅A,P⁆`). `set` folds the
  -- occurrences of `⁅A,Q⁆` in `hYdisj`/`hYsup`/`hAQne` automatically.
  set W : Subgroup G := ⁅A, Q⁆ with hWdef
  -- both `Y` and `W` are `p`-groups inside the elementary abelian `A`.
  have hYA : Y ≤ A := inf_le_left
  have hWA : W ≤ A := hYsup ▸ le_sup_right
  have hYp : IsPGroup p ↥Y := hAmem.1.isPGroup.to_le hYA
  have hWp : IsPGroup p ↥W := hAmem.1.isPGroup.to_le hWA
  have hYNW : Y ≤ Subgroup.normalizer (W : Set G) :=
    ((hYA.trans (le_centralizer_self_of_isElementaryAbelian hAmem.1)).trans
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hWA))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hYWcard : Nat.card ↥Y * Nat.card ↥W = p ^ 2 := by
    rw [← card_sup_eq_mul_of_le_normalizer_of_disjoint hYNW hYdisj, hYsup, hAmem.2]
  have hYcardp : p ∣ Nat.card ↥Y :=
    hYp.card_eq_or_dvd.resolve_left (fun h1 => hYne (Subgroup.card_eq_one.mp h1))
  have hWcardp : p ∣ Nat.card ↥W :=
    hWp.card_eq_or_dvd.resolve_left (fun h1 => hAQne (Subgroup.card_eq_one.mp h1))
  -- from `|Y| * |W| = p²`, both divisible by `p`: `|Y| = p`.
  have hYcard : Nat.card ↥Y = p := by
    obtain ⟨c, hc⟩ := hYcardp
    obtain ⟨d, hd⟩ := hWcardp
    have hppos := (Fact.out : p.Prime).pos
    have key : p * p = p * (c * d * p) := by
      have hsq : p ^ 2 = p * p := sq p
      rw [← hsq, ← hYWcard, hc, hd]; ring
    have hcd : c * d = 1 := by
      have h1 : p = c * d * p := Nat.eq_of_mul_eq_mul_left hppos key
      nlinarith [h1, hppos]
    have hc1 : c = 1 := Nat.eq_one_of_mul_eq_one_right hcd
    rw [hc, hc1, mul_one]
  -- `P = Y` (both order `p`, `P ≤ Y`).
  have hPYeq : P = Y := Subgroup.eq_of_le_of_card_ge hPY (by rw [hYcard, hPcardp])
  -- 13.12/M* (roles renamed): `C_{M*_σ}(Q) = ⊥`.
  -- (`p := q ∈ τ₁(M*)`, `P := Q`, `q := p ∈ τ₂(M*)`, `A := A`, `C_A(Q) = Y ≠ ⊥`.)
  have hCMσstarQ : S10.Msigma Mstar ⊓ Subgroup.centralizer (Q : Set G) = ⊥ :=
    Msigma_centralizer_eq_bot_of_tau1_tau2 hG hsetupS (p := q) (q := p) hqτ1star hpτ2star
      hQmem hQEs hAmem hAEs (fun hb => hYne (hYdef.trans hb))
  -- 12.9(c)/M*: `¬ C_G(A ⊓ C_G(Q)) ≤ M*`, i.e. `¬ C_G(Y) ≤ M*`.
  have h129c := (commutator_decomp_of_tau1_action hG hsetupS hpτ2star hqτ1star hAmem hAEs
    hQmem hQEs hCMσstarQ hAQne).2.2.2.2
  -- But `C_G(A ⊓ C_G(Q)) = C_G(P) ≤ N_G(P) ≤ M*` (as `A ⊓ C_G(Q) = Y = P`).  Contradiction.
  -- (The goal's centralizer argument is the *set* `↑A ∩ ↑(C_G Q) = ↑(A ⊓ C_G Q) = ↑P`.)
  have hAQeqP : A ⊓ Subgroup.centralizer (Q : Set G) = P := hYdef.symm.trans hPYeq.symm
  have hsetP : (↑A ⊓ ↑(Subgroup.centralizer (Q : Set G)) : Set G) = (↑P : Set G) :=
    (Subgroup.coe_inf A (Subgroup.centralizer (Q : Set G))).symm.trans
      (congrArg (SetLike.coe) hAQeqP)
  apply h129c
  rw [hsetP]
  exact (Subgroup.centralizer_le_normalizer _).trans hNPMstar

end OddOrder.BG.Ch3.S13


