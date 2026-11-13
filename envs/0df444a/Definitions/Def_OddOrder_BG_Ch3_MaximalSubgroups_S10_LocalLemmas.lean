-- Prove2me | Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S10_LocalLemmas
-- name    : OddOrder_BG_Ch3_MaximalSubgroups_S10_LocalLemmas
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T07:11:31.269966+00:00
-- url     : https://prove2.me/theorems/8a95c294-0125-4fd0-9c8d-b83bfcccf907
-- title:
--   BG §10: local lemmas, Lemma 10.13 (rank-two elementary abelian structure)
-- statement:
--   Formalizes Lemma 10.13 of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, §10 (`nonabelian_pSubgroup_rankTwo_elemAbelian_structure`) with its helper lemmas, including transitivity of $GL_2(p)$-transvections. Proposition 10.11 and Lemma 10.12 are in the companion Core file.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 13 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch3_MaximalSubgroups/S10_LocalLemmas.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch3_MaximalSubgroups/S10_LocalLemmas.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S10_LocalLemmasCore

namespace OddOrder.BG.Ch3.S10

open OddOrder.GroupTheory

open OddOrder.Isaacs

open scoped Pointwise commutatorElement

variable {G : Type*} [Group G]

/-- Mutual commutation puts a subgroup inside the normalizer: if every element of `H`
commutes with every element of `K`, then `H ≤ N_G(K)`. -/
private theorem le_normalizer_of_forall_comm {H K : Subgroup G}
    (hHK : ∀ x ∈ H, ∀ y ∈ K, x * y = y * x) :
    H ≤ Subgroup.normalizer (K : Set G) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro k
  constructor
  · intro hk
    have : h * k * h⁻¹ = k := by rw [hHK h hh k hk]; group
    rwa [this]
  · intro hk
    have hc := hHK h hh _ hk
    have : k = h * k * h⁻¹ := by
      calc k = h⁻¹ * (h * k * h⁻¹) * h := by group
        _ = h⁻¹ * (h * (h * k * h⁻¹)) := by rw [hc]; group
        _ = h * k * h⁻¹ := by group
    rwa [← this] at hk

/-- Elementwise commutativity of the join of two elementwise-commutative subgroups that
centralize each other (stated on ambient elements to avoid subtype plumbing). -/
private theorem comm_sup_of_comm_of_comm {H K : Subgroup G}
    (hH : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x) (hK : ∀ x ∈ K, ∀ y ∈ K, x * y = y * x)
    (hHK : ∀ x ∈ H, ∀ y ∈ K, x * y = y * x) :
    ∀ x ∈ H ⊔ K, ∀ y ∈ H ⊔ K, x * y = y * x := by
  have hmul : ∀ g ∈ H ⊔ K, ∃ h ∈ H, ∃ k ∈ K, h * k = g := by
    intro g hg
    refine Set.mem_mul.mp ?_
    rw [(Subgroup.coe_mul_of_left_le_normalizer_right H K
      (le_normalizer_of_forall_comm hHK)).symm]
    exact hg
  intro x hx y hy
  obtain ⟨h₁, hh₁, k₁, hk₁, rfl⟩ := hmul x hx
  obtain ⟨h₂, hh₂, k₂, hk₂, rfl⟩ := hmul y hy
  calc h₁ * k₁ * (h₂ * k₂) = h₁ * h₂ * (k₁ * k₂) := by
        rw [mul_assoc, mul_assoc, ← mul_assoc k₁, ← hHK h₂ hh₂ k₁ hk₁, mul_assoc]
    _ = h₂ * h₁ * (k₂ * k₁) := by rw [hH h₁ hh₁ h₂ hh₂, hK k₁ hk₁ k₂ hk₂]
    _ = h₂ * k₂ * (h₁ * k₁) := by
        rw [mul_assoc, mul_assoc, ← mul_assoc h₁, hHK h₁ hh₁ k₂ hk₂, mul_assoc]

/-- Every elementary abelian `p`-subgroup of `C_G(A)` lies in the *maximal* elementary
abelian `A`: the join `A ⊔ E` is elementary abelian and contains `A`. This is the engine
behind BG's display (10.4) (`A = Ω₁(C_S(A))`, `r(C_S(A)) = 2`) in Lemma 10.13. -/
private theorem elemAbelian_le_of_le_centralizer [Finite G] {p : ℕ}
    {A : Subgroup G} (hAea : A.IsElementaryAbelian p)
    (hAmax : IsMaximalElementaryAbelian p A) {E : Subgroup G}
    (hEea : E.IsElementaryAbelian p) (hEC : E ≤ Subgroup.centralizer (A : Set G)) :
    E ≤ A := by
  have hA_le_CE : A ≤ Subgroup.centralizer (E : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact (Subgroup.mem_centralizer_iff.mp (hEC he) a ha).symm
  have hsup : (A ⊔ E).IsElementaryAbelian p := hAea.sup_of_le_centralizer hEea hA_le_CE
  have heq : A ⊔ E = A := hAmax.2 (A ⊔ E) hsup le_sup_left
  exact le_sup_right.trans heq.le

/-- An element of `C_G(A)` of order dividing `p` lies in the maximal elementary abelian `A`
(BG (10.4): `A = Ω₁(C_S(A))`, elementwise form). -/
private theorem mem_of_mem_centralizer_of_pow_eq_one [Finite G] {p : ℕ} [Fact p.Prime]
    {A : Subgroup G} (hAea : A.IsElementaryAbelian p)
    (hAmax : IsMaximalElementaryAbelian p A) {g : G}
    (hg : g ∈ Subgroup.centralizer (A : Set G)) (hgp : g ^ p = 1) : g ∈ A := by
  rcases eq_or_ne g 1 with rfl | hg1
  · exact A.one_mem
  · exact elemAbelian_le_of_le_centralizer hAea hAmax
      (Subgroup.IsElementaryAbelian.of_card_prime
        (by rw [Nat.card_zpowers, orderOf_eq_prime hgp hg1]))
      (Subgroup.zpowers_le.mpr hg) (Subgroup.mem_zpowers g)

/-- `Ω₁(Z(P)) ≤ A` for a maximal elementary abelian `A ≤ P`: elements of `Ω₁(Z(P))`
centralize `A` and have order dividing `p`. -/
private theorem omega1CenterInG_le_of_maximal [Finite G] {p : ℕ} [Fact p.Prime]
    {A P : Subgroup G} (hAea : A.IsElementaryAbelian p)
    (hAmax : IsMaximalElementaryAbelian p A) (hAP : A ≤ P) :
    omega1CenterInG P p ≤ A := by
  intro z hz
  obtain ⟨z', hz', rfl⟩ := Subgroup.mem_map.mp hz
  obtain ⟨hzc, hzp⟩ := mem_omega1OfAbelian.mp hz'
  refine mem_of_mem_centralizer_of_pow_eq_one hAea hAmax ?_ ?_
  · rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hzc ⟨a, hAP ha⟩)
  · calc (P.subtype z') ^ p = P.subtype (z' ^ p) := by rw [map_pow]
      _ = 1 := by rw [hzp, map_one]

/-- Two distinct subgroups of prime order intersect trivially. -/
private theorem inf_eq_bot_of_card_prime_of_ne [Finite G] {p : ℕ} [Fact p.Prime]
    {X Y : Subgroup G}
    (hX : Nat.card ↥X = p) (hY : Nat.card ↥Y = p) (hne : X ≠ Y) : X ⊓ Y = ⊥ := by
  by_contra hbot
  obtain ⟨g, hg, hg1⟩ := (Subgroup.bot_or_exists_ne_one (X ⊓ Y)).resolve_left hbot
  have hzleX : Subgroup.zpowers g ≤ X := Subgroup.zpowers_le.mpr hg.1
  have hzleY : Subgroup.zpowers g ≤ Y := Subgroup.zpowers_le.mpr hg.2
  have hcard : Nat.card ↥(Subgroup.zpowers g) = p := by
    have hdvd : Nat.card ↥(Subgroup.zpowers g) ∣ p := by
      rw [← hX]; exact Subgroup.card_dvd_of_le hzleX
    rcases (Nat.dvd_prime Fact.out).mp hdvd with h1 | h
    · exact absurd (Subgroup.card_eq_one.mp h1)
        (fun h => hg1 (Subgroup.zpowers_eq_bot.mp h))
    · exact h
  exact hne ((Subgroup.eq_of_le_of_card_ge hzleX (by rw [hX, hcard])).symm.trans
    (Subgroup.eq_of_le_of_card_ge hzleY (by rw [hY, hcard])))

/-- A subgroup of order `p²` is the join of any two of its distinct order-`p` subgroups. -/
private theorem eq_sup_of_card_prime_of_ne [Finite G] {p : ℕ} [Fact p.Prime]
    {A X Y : Subgroup G} (hAcard : Nat.card ↥A = p ^ 2) (hXA : X ≤ A) (hYA : Y ≤ A)
    (hX : Nat.card ↥X = p) (hY : Nat.card ↥Y = p) (hne : X ≠ Y) : X ⊔ Y = A := by
  have hsupA : X ⊔ Y ≤ A := sup_le hXA hYA
  have hdvd1 : p ∣ Nat.card ↥(X ⊔ Y) := by
    rw [← hX]; exact Subgroup.card_dvd_of_le le_sup_left
  have hdvd2 : Nat.card ↥(X ⊔ Y) ∣ p ^ 2 := by
    rw [← hAcard]; exact Subgroup.card_dvd_of_le hsupA
  obtain ⟨k, hk2, hkeq⟩ := (Nat.dvd_prime_pow Fact.out).mp hdvd2
  interval_cases k
  · rw [hkeq, pow_zero] at hdvd1
    exact absurd (Nat.dvd_one.mp hdvd1) (Fact.out : p.Prime).ne_one
  · exfalso
    have hXeq : X = X ⊔ Y :=
      Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hX, hkeq, pow_one])
    have hYX : Y ≤ X := hXeq ▸ le_sup_right
    exact hne (Subgroup.eq_of_le_of_card_ge hYX (by rw [hX, hY])).symm
  · exact Subgroup.eq_of_le_of_card_ge hsupA (by rw [hAcard, hkeq])

/-- **(10.6) producer, low-rank case** (`r(S) ≤ 2`): Corollary 10.7(b) makes the Sylow `S` a
central product `P₁ ∘ P₂` (`P₁` extraspecial of order `p³` and exponent `p`, `P₂` cyclic with
`Ω₁(P₂) = Z(P₁)`); exponent-`p` elements of `S` are trapped in `P₁`, so `A ≤ P₁` is
self-centralizing in `P₁` and `C_S(A) = A ⊔ P₂ = A₀ ⊔ P₂` is abelian, with
`Z₀ = Ω₁(Z(P)) = Z(P₁) = Ω₁(P₂) ≤ P₂` of order `p`. -/
private theorem centralizer_sylow_decomp_of_rank_le_two [Finite G]
    (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime] {A P A₀ : Subgroup G} (S : Sylow p G)
    (hAea : A.IsElementaryAbelian p) (hAcard : Nat.card ↥A = p ^ 2)
    (hAmax : IsMaximalElementaryAbelian p A) (hPp : IsPGroup p ↥P)
    (hPnonab : ¬ IsMulCommutative ↥P) (hAP : A ≤ P) (hPS : P ≤ (S : Subgroup G))
    (hA₀A : A₀ ≤ A) (hA₀card : Nat.card ↥A₀ = p) (hA₀ne : A₀ ≠ omega1CenterInG P p)
    (hrank : rank ↥(S : Subgroup G) ≤ 2) :
    ∃ Y : Subgroup G, Y ≤ (S : Subgroup G) ∧ IsCyclic ↥Y ∧ omega1CenterInG P p ≤ Y ∧
      A₀ ⊓ Y = ⊥ ∧ Subgroup.centralizer (A : Set G) ⊓ (S : Subgroup G) = A₀ ⊔ Y ∧
      (∀ c₁ ∈ Subgroup.centralizer (A : Set G) ⊓ (S : Subgroup G),
        ∀ c₂ ∈ Subgroup.centralizer (A : Set G) ⊓ (S : Subgroup G), c₁ * c₂ = c₂ * c₁) ∧
      Nat.card ↥(omega1CenterInG P p) = p := by
  classical
  have hA_le_S : A ≤ (S : Subgroup G) := hAP.trans hPS
  -- Corollary 10.7(b).
  rcases (sylow_structure hG S).2.1 hrank with hab |
    ⟨P₁, P₂, hP₁S, hP₂S, hP₁ex, hP₁card, hP₂cyc, hΩeq, hCP⟩
  · -- `S` abelian would make `P` abelian.
    refine absurd ⟨⟨fun a b => Subtype.ext ?_⟩⟩ hPnonab
    have h := congrArg Subtype.val
      (hab.is_comm.comm (⟨(a : G), hPS a.2⟩ : ↥(S : Subgroup G)) ⟨(b : G), hPS b.2⟩)
    simpa using h
  -- The two central factors commute elementwise.
  have hP₁P₂comm : ∀ x ∈ P₁, ∀ y ∈ P₂, x * y = y * x := by
    intro x hx y hy
    have h := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hCP.commutator_eq_bot hx
    exact (Subgroup.mem_centralizer_iff.mp h y hy).symm
  have hdecomp : ∀ s ∈ (S : Subgroup G), ∃ s₁ ∈ P₁, ∃ s₂ ∈ P₂, s₁ * s₂ = s := by
    intro s hs
    refine Set.mem_mul.mp ?_
    rw [(Subgroup.coe_mul_of_left_le_normalizer_right P₁ P₂
      (le_normalizer_of_forall_comm hP₁P₂comm)).symm, ← hCP.sup_eq]
    exact hs
  -- Exponent-`p` elements of `S` lie in `P₁` (`Ω₁(S) ≤ P₁`).
  have htrap : ∀ s ∈ (S : Subgroup G), s ^ p = 1 → s ∈ P₁ := by
    intro s hs hsp
    obtain ⟨s₁, hs₁, s₂, hs₂, rfl⟩ := hdecomp s hs
    have hcomm : Commute s₁ s₂ := hP₁P₂comm s₁ hs₁ s₂ hs₂
    have hs₁p : s₁ ^ p = 1 := congrArg Subtype.val (hP₁ex.pow_eq_one (⟨s₁, hs₁⟩ : ↥P₁))
    have hs₂p : s₂ ^ p = 1 := by
      have h := hsp
      rw [hcomm.mul_pow, hs₁p, one_mul] at h
      exact h
    have hs₂P₁ : s₂ ∈ P₁ := by
      have hmem : s₂ ∈ (Omega ↥P₂ p 1).map P₂.subtype :=
        ⟨⟨s₂, hs₂⟩, Omega.mem_of_pow_eq_one (by
          rw [pow_one]
          exact Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact hs₂p)), rfl⟩
      rw [hΩeq] at hmem
      exact Subgroup.map_subtype_le _ hmem
    exact P₁.mul_mem hs₁ hs₂P₁
  -- `A ≤ P₁`.
  have hA_le_P₁ : A ≤ P₁ := fun a ha => htrap a (hA_le_S ha)
    (congrArg Subtype.val (hAea.2 ⟨a, ha⟩))
  -- `C_{P₁}(A) = A` (the rank-two `A` is self-centralizing in the extraspecial `P₁`).
  have hCP₁A : Subgroup.centralizer (A : Set G) ⊓ P₁ = A := by
    have hA_le : A ≤ Subgroup.centralizer (A : Set G) ⊓ P₁ := by
      refine le_inf ?_ hA_le_P₁
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact congrArg Subtype.val (hAea.1 ⟨b, hb⟩ ⟨a, ha⟩)
    have hdvd : Nat.card ↥(Subgroup.centralizer (A : Set G) ⊓ P₁) ∣ p ^ 3 := by
      rw [← hP₁card]
      exact Subgroup.card_dvd_of_le inf_le_right
    obtain ⟨k, hk3, hkeq⟩ := (Nat.dvd_prime_pow Fact.out).mp hdvd
    have hp2le : p ^ 2 ≤ p ^ k := by
      rw [← hkeq, ← hAcard]
      exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hA_le)
    have hk2 : 2 ≤ k :=
      le_of_not_gt fun hlt =>
        absurd hp2le (not_le.mpr (Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt hlt))
    interval_cases k
    · exact (Subgroup.eq_of_le_of_card_ge hA_le (by rw [hAcard, hkeq])).symm
    · -- `|C_{P₁}(A)| = p³` would make `A` central in `P₁`, impossible (`|Z(P₁)| = p`).
      exfalso
      have hCeq : Subgroup.centralizer (A : Set G) ⊓ P₁ = P₁ :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hP₁card, hkeq])
      have hAcent : A.subgroupOf P₁ ≤ Subgroup.center ↥P₁ := by
        intro a ha
        rw [Subgroup.mem_center_iff]
        intro x
        have hx : (x : G) ∈ Subgroup.centralizer (A : Set G) := by
          have hx' : (x : G) ∈ Subgroup.centralizer (A : Set G) ⊓ P₁ := by
            rw [hCeq]; exact x.2
          exact hx'.1
        refine Subtype.ext ?_
        simp only [Subgroup.coe_mul]
        exact (Subgroup.mem_centralizer_iff.mp hx (a : G)
          (Subgroup.mem_subgroupOf.mp ha)).symm
      have hcard_le : p ^ 2 ∣ p := by
        rw [← hAcard, ← hP₁ex.isExtraspecial.center_card]
        calc Nat.card ↥A = Nat.card ↥(A.subgroupOf P₁) :=
              (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA_le_P₁).toEquiv).symm
          _ ∣ Nat.card ↥(Subgroup.center ↥P₁) := Subgroup.card_dvd_of_le hAcent
      have hp2 : p < p ^ 2 := by
        have h1 := (Fact.out : p.Prime).one_lt
        nlinarith
      exact absurd (Nat.le_of_dvd (Fact.out : p.Prime).pos hcard_le) (not_le.mpr hp2)
  -- `C_S(A) = A ⊔ P₂`.
  have hCSA : Subgroup.centralizer (A : Set G) ⊓ (S : Subgroup G) = A ⊔ P₂ := by
    apply le_antisymm
    · intro c hc
      obtain ⟨c₁, hc₁, c₂, hc₂, rfl⟩ := hdecomp c hc.2
      have hc₂C : c₂ ∈ Subgroup.centralizer (A : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro a ha
        exact hP₁P₂comm a (hA_le_P₁ ha) c₂ hc₂
      have hc₁C : c₁ ∈ Subgroup.centralizer (A : Set G) := by
        have heq : c₁ = c₁ * c₂ * c₂⁻¹ := by group
        rw [heq]
        exact Subgroup.mul_mem _ hc.1 (Subgroup.inv_mem _ hc₂C)
      have hc₁A : c₁ ∈ A := by
        have hmem : c₁ ∈ Subgroup.centralizer (A : Set G) ⊓ P₁ := ⟨hc₁C, hc₁⟩
        rwa [hCP₁A] at hmem
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hc₁A) (Subgroup.mem_sup_right hc₂)
    · refine sup_le (le_inf ?_ hA_le_S) (le_inf ?_ hP₂S)
      · intro a ha
        rw [Subgroup.mem_centralizer_iff]
        intro b hb
        exact congrArg Subtype.val (hAea.1 ⟨b, hb⟩ ⟨a, ha⟩)
      · intro y hy
        rw [Subgroup.mem_centralizer_iff]
        intro a ha
        exact hP₁P₂comm a (hA_le_P₁ ha) y hy
  -- `C_S(A)` is abelian.
  have hCab : ∀ c₁ ∈ Subgroup.centralizer (A : Set G) ⊓ (S : Subgroup G),
      ∀ c₂ ∈ Subgroup.centralizer (A : Set G) ⊓ (S : Subgroup G), c₁ * c₂ = c₂ * c₁ := by
    rw [hCSA]
    refine comm_sup_of_comm_of_comm
      (fun x hx y hy => congrArg Subtype.val (hAea.1 ⟨x, hx⟩ ⟨y, hy⟩))
      (fun x hx y hy => ?_)
      (fun x hx y hy => hP₁P₂comm x (hA_le_P₁ hx) y hy)
    have := hP₂cyc
    let : CommGroup ↥P₂ := IsCyclic.commGroup
    exact congrArg Subtype.val (mul_comm (⟨x, hx⟩ : ↥P₂) ⟨y, hy⟩)
  -- `Z₀ = Ω₁(Z(P))`: contained in `A`, nontrivial, proper in `A`, of order `p`.
  have hPnt : Nontrivial ↥P := by
    rcases subsingleton_or_nontrivial ↥P with hs | hn
    · exact absurd ⟨⟨fun a b => Subsingleton.elim _ _⟩⟩ hPnonab
    · exact hn
  obtain ⟨z, -, hzc, hz1, hzp⟩ :=
    exists_mem_omega1_center_of_normal_ne_bot hPp (N := ⊤) top_ne_bot
  have hzZ₀ : (z : G) ∈ omega1CenterInG P p :=
    Subgroup.mem_map.mpr ⟨z, mem_omega1OfAbelian.mpr ⟨hzc, hzp⟩, rfl⟩
  have hZ₀A : omega1CenterInG P p ≤ A := omega1CenterInG_le_of_maximal hAea hAmax hAP
  have hAne : A ≠ omega1CenterInG P p := by
    intro heq
    apply hPnonab
    have hPC : P ≤ Subgroup.centralizer (A : Set G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      rw [heq] at ha
      obtain ⟨z', hz', rfl⟩ := Subgroup.mem_map.mp ha
      exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp
        (mem_omega1OfAbelian.mp hz').1 ⟨x, hx⟩)).symm
    exact ⟨⟨fun a b => Subtype.ext
      (hCab _ ⟨hPC a.2, hPS a.2⟩ _ ⟨hPC b.2, hPS b.2⟩)⟩⟩
  have hZ₀card : Nat.card ↥(omega1CenterInG P p) = p := by
    have hdvd : Nat.card ↥(omega1CenterInG P p) ∣ p ^ 2 := by
      rw [← hAcard]
      exact Subgroup.card_dvd_of_le hZ₀A
    obtain ⟨k, hk2, hkeq⟩ := (Nat.dvd_prime_pow Fact.out).mp hdvd
    interval_cases k
    · exfalso
      have hsub : Subsingleton ↥(omega1CenterInG P p) :=
        (Nat.card_eq_one_iff_unique.mp (by rw [hkeq, pow_zero])).1
      have h1 := Subsingleton.elim (⟨(z : G), hzZ₀⟩ : ↥(omega1CenterInG P p))
        ⟨1, Subgroup.one_mem _⟩
      exact hz1 (OneMemClass.coe_eq_one.mp (congrArg Subtype.val h1))
    · rw [hkeq, pow_one]
    · exact absurd (Subgroup.eq_of_le_of_card_ge hZ₀A (by rw [hAcard, hkeq])).symm hAne
  -- `Z(P₁)` (mapped to `G`) is contained in `A`, then in `Z₀`; equality by cardinality.
  have hZP₁card : Nat.card ↥((Subgroup.center ↥P₁).map P₁.subtype) = p := by
    rw [Subgroup.card_map_of_injective P₁.subtype_injective]
    exact hP₁ex.isExtraspecial.center_card
  have hZP₁pow : ∀ w ∈ (Subgroup.center ↥P₁).map P₁.subtype, w ^ p = 1 := by
    intro w hw
    have h1 : (⟨w, hw⟩ : ↥((Subgroup.center ↥P₁).map P₁.subtype)) ^ p = 1 := by
      rw [← hZP₁card]
      exact pow_card_eq_one'
    have hcoe := congrArg Subtype.val h1
    rwa [SubmonoidClass.coe_pow, OneMemClass.coe_one] at hcoe
  have hZP₁_le_A : (Subgroup.center ↥P₁).map P₁.subtype ≤ A := by
    intro w hw
    refine mem_of_mem_centralizer_of_pow_eq_one hAea hAmax ?_ (hZP₁pow w hw)
    obtain ⟨w', hw', rfl⟩ := Subgroup.mem_map.mp hw
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hw' ⟨a, hA_le_P₁ ha⟩)
  have hZP₁_le_Z₀ : (Subgroup.center ↥P₁).map P₁.subtype ≤ omega1CenterInG P p := by
    intro w hw
    have hwA : w ∈ A := hZP₁_le_A hw
    have hwS : ∀ s ∈ (S : Subgroup G), s * w = w * s := by
      obtain ⟨w', hw', rfl⟩ := Subgroup.mem_map.mp hw
      intro s hs
      obtain ⟨s₁, hs₁, s₂, hs₂, rfl⟩ := hdecomp s hs
      have h₁ : s₁ * P₁.subtype w' = P₁.subtype w' * s₁ :=
        congrArg Subtype.val (Subgroup.mem_center_iff.mp hw' ⟨s₁, hs₁⟩)
      have h₂ : s₂ * P₁.subtype w' = P₁.subtype w' * s₂ :=
        (hP₁P₂comm (P₁.subtype w') (Subgroup.map_subtype_le _ ⟨w', hw', rfl⟩) s₂ hs₂).symm
      calc s₁ * s₂ * P₁.subtype w' = s₁ * (P₁.subtype w' * s₂) := by rw [mul_assoc, h₂]
        _ = P₁.subtype w' * (s₁ * s₂) := by rw [← mul_assoc, h₁, mul_assoc]
    refine Subgroup.mem_map.mpr ⟨⟨w, hAP hwA⟩, mem_omega1OfAbelian.mpr ⟨?_, ?_⟩, rfl⟩
    · rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hwS (g : G) (hPS g.2))
    · exact Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact hZP₁pow w hw)
  have hZ₀eq : omega1CenterInG P p = (Subgroup.center ↥P₁).map P₁.subtype :=
    (Subgroup.eq_of_le_of_card_ge hZP₁_le_Z₀ (by rw [hZ₀card, hZP₁card])).symm
  have hZ₀_le_P₂ : omega1CenterInG P p ≤ P₂ := by
    rw [hZ₀eq, ← hΩeq]
    exact Subgroup.map_subtype_le _
  -- Assemble with `Y = P₂`.
  refine ⟨P₂, hP₂S, hP₂cyc, hZ₀_le_P₂, ?_, ?_, hCab, hZ₀card⟩
  · -- `A₀ ⊓ P₂ = ⊥`: an exponent-`p` element of `P₂` lies in `Ω₁(P₂) = Z₀ ≠ A₀`.
    rw [eq_bot_iff]
    intro x hx
    have hxp : x ^ p = 1 := by
      have h1 : (⟨x, hx.1⟩ : ↥A₀) ^ p = 1 := by
        rw [← hA₀card]
        exact pow_card_eq_one'
      have hcoe := congrArg Subtype.val h1
      rwa [SubmonoidClass.coe_pow, OneMemClass.coe_one] at hcoe
    have hxZ₀ : x ∈ omega1CenterInG P p := by
      rw [hZ₀eq, ← hΩeq]
      exact ⟨⟨x, hx.2⟩, Omega.mem_of_pow_eq_one (by
        rw [pow_one]
        exact Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact hxp)), rfl⟩
    have hmem : x ∈ A₀ ⊓ omega1CenterInG P p := ⟨hx.1, hxZ₀⟩
    rwa [inf_eq_bot_of_card_prime_of_ne hA₀card hZ₀card hA₀ne] at hmem
  · -- `C_S(A) = A₀ ⊔ P₂` via `A = A₀ ⊔ Z₀` and `Z₀ ≤ P₂`.
    rw [hCSA, ← eq_sup_of_card_prime_of_ne hAcard hA₀A hZ₀A hA₀card hZ₀card hA₀ne,
      sup_assoc, sup_eq_right.mpr hZ₀_le_P₂]

/-- Bridge: the `↥S`-level centralizer of `L.subgroupOf S` is the `subgroupOf`-image of the
ambient `C_G(L) ⊓ S`. -/
private theorem centralizer_subgroupOf_inf_eq {S L : Subgroup G} (hLS : L ≤ S) :
    Subgroup.centralizer ((L.subgroupOf S : Subgroup ↥S) : Set ↥S)
      = (Subgroup.centralizer (L : Set G) ⊓ S).subgroupOf S := by
  ext m
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  constructor
  · intro hc
    refine ⟨fun h hh => ?_, m.2⟩
    simpa using congrArg Subtype.val (hc ⟨h, hLS hh⟩ (Subgroup.mem_subgroupOf.mpr hh))
  · intro hc h hh
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact hc.1 (h : G) (Subgroup.mem_subgroupOf.mp hh)

/-- **(10.6) producer, high-rank case** (`r_p(S) ≥ 3`): `S` is narrow with maximal elementary
abelian witness `A` (BG (10.4)), and BG Theorem 5.3(d) (`narrow_centralizer_decomp`) splits
`C_S(L) = L × C_T(L)` for each order-`p` line `L ≤ A` other than `Z₁ = Ω₁(Z(S))`; since
`C_S(L) = C_S(A)` (as `A = L ⊔ Z₁` with `Z₁` central in `S`) this gives the abelian
decomposition `C_S(A) = A₀ ⊔ Y`, and `Z₀ = Ω₁(Z(P)) = Z₁` has order `p`. -/
private theorem centralizer_sylow_decomp_of_three_le_rank [Finite G]
    (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime] {A P A₀ : Subgroup G} (S : Sylow p G)
    (hAea : A.IsElementaryAbelian p) (hAcard : Nat.card ↥A = p ^ 2)
    (hAmax : IsMaximalElementaryAbelian p A) (hPp : IsPGroup p ↥P)
    (hPnonab : ¬ IsMulCommutative ↥P) (hAP : A ≤ P) (hPS : P ≤ (S : Subgroup G))
    (hA₀A : A₀ ≤ A) (hA₀card : Nat.card ↥A₀ = p) (hA₀ne : A₀ ≠ omega1CenterInG P p)
    (h3 : 3 ≤ pRank ↥(S : Subgroup G) p) :
    ∃ Y : Subgroup G, Y ≤ (S : Subgroup G) ∧ IsCyclic ↥Y ∧ omega1CenterInG P p ≤ Y ∧
      A₀ ⊓ Y = ⊥ ∧ Subgroup.centralizer (A : Set G) ⊓ (S : Subgroup G) = A₀ ⊔ Y ∧
      (∀ c₁ ∈ Subgroup.centralizer (A : Set G) ⊓ (S : Subgroup G),
        ∀ c₂ ∈ Subgroup.centralizer (A : Set G) ⊓ (S : Subgroup G), c₁ * c₂ = c₂ * c₁) ∧
      Nat.card ↥(omega1CenterInG P p) = p := by
  classical
  have hA_le_S : A ≤ (S : Subgroup G) := hAP.trans hPS
  have hp_odd : Odd p := hG.odd.of_dvd_nat
    ((show p ∣ Nat.card ↥A by rw [hAcard]; exact dvd_pow_self p two_ne_zero).trans
      (Subgroup.card_subgroup_dvd_card A))
  have hApow : ∀ g ∈ A, g ^ p = 1 := by
    intro g hg
    have h := congrArg Subtype.val (hAea.2 ⟨g, hg⟩)
    rwa [SubmonoidClass.coe_pow, OneMemClass.coe_one] at h
  -- `↥S`-level data for `A`: maximality is inherited.
  have hA'card : Nat.card ↥(A.subgroupOf (S : Subgroup G)) = p ^ 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA_le_S).toEquiv]
    exact hAcard
  have hA'ea : (A.subgroupOf (S : Subgroup G)).IsElementaryAbelian p :=
    IsElementaryAbelian.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hA_le_S).symm hAea
  have hA'max : IsMaximalElementaryAbelian p (A.subgroupOf (S : Subgroup G)) := by
    refine ⟨hA'ea, ?_⟩
    intro F hFea hAF
    have hFmap : F.map (S : Subgroup G).subtype = A :=
      hAmax.2 _ (hFea.map (S : Subgroup G).subtype_injective) (by
        rw [← Subgroup.map_subgroupOf_eq_of_le hA_le_S]
        exact Subgroup.map_mono hAF)
    calc F = (F.map (S : Subgroup G).subtype).subgroupOf (S : Subgroup G) := by
          rw [Subgroup.subgroupOf,
            Subgroup.comap_map_eq_self_of_injective (S : Subgroup G).subtype_injective]
      _ = A.subgroupOf (S : Subgroup G) := by rw [hFmap]
  have hnarrow : IsNarrow p ↥(S : Subgroup G) :=
    (Ch1.S05.narrow_iff_exists_maximalElementaryAbelian_card_prime_sq hp_odd S.isPGroup' h3).mpr
      ⟨A.subgroupOf (S : Subgroup G), hA'card, hA'max⟩
  -- BG (10.4): `r(C_S(A)) ≤ 2`, first at the ambient level, then at the `↥S` level.
  have hrank2G : pRank ↥(Subgroup.centralizer (A : Set G) ⊓ (S : Subgroup G)) p ≤ 2 := by
    rw [pRank_le_iff]
    intro E hEea
    have hEmap_le_A :
        E.map (Subgroup.centralizer (A : Set G) ⊓ (S : Subgroup G)).subtype ≤ A :=
      elemAbelian_le_of_le_centralizer hAea hAmax
        (hEea.map (Subgroup.centralizer (A : Set G) ⊓ (S : Subgroup G)).subtype_injective)
        ((Subgroup.map_subtype_le _).trans inf_le_left)
    have hlog : Nat.log p (Nat.card ↥E) ≤ Nat.log p (Nat.card ↥A) := by
      apply Nat.log_mono_right
      have hEcard : Nat.card
          ↥(E.map (Subgroup.centralizer (A : Set G) ⊓ (S : Subgroup G)).subtype)
          = Nat.card ↥E :=
        Subgroup.card_map_of_injective
          (Subgroup.centralizer (A : Set G) ⊓ (S : Subgroup G)).subtype_injective
      rw [← hEcard]
      exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hEmap_le_A)
    rwa [hAcard, Nat.log_pow (Fact.out : p.Prime).one_lt] at hlog
  have hrank2' : pRank ↥(Subgroup.centralizer
      ((A.subgroupOf (S : Subgroup G) : Subgroup ↥(S : Subgroup G)) :
        Set ↥(S : Subgroup G))) p ≤ 2 := by
    rw [centralizer_subgroupOf_inf_eq hA_le_S]
    exact le_trans
      (pRank_le_of_injective
        (f := (Subgroup.subgroupOfEquivOfLe
          (inf_le_right : Subgroup.centralizer (A : Set G) ⊓ (S : Subgroup G)
            ≤ (S : Subgroup G))).toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe _).injective)
      hrank2G
  -- `Z₁ = Ω₁(Z(S))`: contained in `A`, of order exactly `p`.
  have hZ₁A : omega1CenterInG (S : Subgroup G) p ≤ A :=
    omega1CenterInG_le_of_maximal hAea hAmax hA_le_S
  have hZ₁S_comm : ∀ z ∈ omega1CenterInG (S : Subgroup G) p,
      ∀ s ∈ (S : Subgroup G), z * s = s * z := by
    intro z hz s hs
    obtain ⟨z', hz', rfl⟩ := Subgroup.mem_map.mp hz
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp
      (mem_omega1OfAbelian.mp hz').1 ⟨s, hs⟩)).symm
  have hSnt : Nontrivial ↥(S : Subgroup G) := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    calc 1 < p ^ 2 := Nat.one_lt_pow two_ne_zero (Fact.out : p.Prime).one_lt
      _ = Nat.card ↥A := hAcard.symm
      _ ≤ Nat.card ↥(S : Subgroup G) :=
          Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hA_le_S)
  obtain ⟨zS, -, hzSc, hzS1, hzSp⟩ :=
    exists_mem_omega1_center_of_normal_ne_bot S.isPGroup' (N := ⊤) top_ne_bot
  have hzSZ₁ : (zS : G) ∈ omega1CenterInG (S : Subgroup G) p :=
    Subgroup.mem_map.mpr ⟨zS, mem_omega1OfAbelian.mpr ⟨hzSc, hzSp⟩, rfl⟩
  have hZ₁ne_A : omega1CenterInG (S : Subgroup G) p ≠ A := by
    intro heq
    have hSC : (S : Subgroup G) ≤ Subgroup.centralizer (A : Set G) := by
      intro s hs
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      rw [← heq] at ha
      exact hZ₁S_comm a ha s hs
    have hCS : Subgroup.centralizer (A : Set G) ⊓ (S : Subgroup G) = (S : Subgroup G) :=
      inf_eq_right.mpr hSC
    rw [hCS] at hrank2G
    omega
  have hZ₁card : Nat.card ↥(omega1CenterInG (S : Subgroup G) p) = p := by
    have hdvd : Nat.card ↥(omega1CenterInG (S : Subgroup G) p) ∣ p ^ 2 := by
      rw [← hAcard]
      exact Subgroup.card_dvd_of_le hZ₁A
    obtain ⟨k, hk2, hkeq⟩ := (Nat.dvd_prime_pow Fact.out).mp hdvd
    interval_cases k
    · exfalso
      have hsub : Subsingleton ↥(omega1CenterInG (S : Subgroup G) p) :=
        (Nat.card_eq_one_iff_unique.mp (by rw [hkeq, pow_zero])).1
      have h1 := Subsingleton.elim
        (⟨(zS : G), hzSZ₁⟩ : ↥(omega1CenterInG (S : Subgroup G) p)) ⟨1, Subgroup.one_mem _⟩
      exact hzS1 (OneMemClass.coe_eq_one.mp (congrArg Subtype.val h1))
    · rw [hkeq, pow_one]
    · exact absurd (Subgroup.eq_of_le_of_card_ge hZ₁A (by rw [hAcard, hkeq])) hZ₁ne_A
  -- Sub-producer: the Theorem 5.3(d) decomposition for any line `L ≤ A` other than `Z₁`.
  have key : ∀ L : Subgroup G, L ≤ A → Nat.card ↥L = p →
      L ≠ omega1CenterInG (S : Subgroup G) p →
      ∃ Y : Subgroup G, Y ≤ (S : Subgroup G) ∧ IsCyclic ↥Y ∧
        omega1CenterInG (S : Subgroup G) p ≤ Y ∧ L ⊓ Y = ⊥ ∧
        Subgroup.centralizer (A : Set G) ⊓ (S : Subgroup G) = L ⊔ Y ∧
        (∀ l ∈ L, ∀ y ∈ Y, l * y = y * l) := by
    intro L hLA hLcard hLne
    have hL_le_S : L ≤ (S : Subgroup G) := hLA.trans hA_le_S
    have hLZcomm : ∀ x ∈ L, ∀ y ∈ omega1CenterInG (S : Subgroup G) p, x * y = y * x :=
      fun x hx y hy => (hZ₁S_comm y hy x (hL_le_S hx)).symm
    -- `C_S(A) = C_S(L)` (`A = L ⊔ Z₁` with `Z₁` central).
    have hCLA : Subgroup.centralizer (A : Set G) ⊓ (S : Subgroup G)
        = Subgroup.centralizer (L : Set G) ⊓ (S : Subgroup G) := by
      apply le_antisymm
      · exact inf_le_inf_right _ (Subgroup.centralizer_le (fun x hx => hLA hx))
      · intro c hc
        refine Subgroup.mem_inf.mpr ⟨?_, hc.2⟩
        rw [Subgroup.mem_centralizer_iff]
        intro a ha
        have haLZ : a ∈ (↑L * ↑(omega1CenterInG (S : Subgroup G) p) : Set G) := by
          rw [(Subgroup.coe_mul_of_left_le_normalizer_right L _
            (le_normalizer_of_forall_comm hLZcomm)).symm,
            eq_sup_of_card_prime_of_ne hAcard hLA hZ₁A hLcard hZ₁card hLne]
          exact ha
        obtain ⟨l, hl, z, hz, rfl⟩ := Set.mem_mul.mp haLZ
        have hcl : l * c = c * l := Subgroup.mem_centralizer_iff.mp hc.1 l hl
        have hcz : z * c = c * z := hZ₁S_comm z hz c hc.2
        calc l * z * c = l * (c * z) := by rw [mul_assoc, hcz]
          _ = c * (l * z) := by rw [← mul_assoc, hcl, mul_assoc]
    -- the `↥S`-level inputs for Theorem 5.3(d)
    have hL'card : Nat.card ↥(L.subgroupOf (S : Subgroup G)) = p := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hL_le_S).toEquiv]
      exact hLcard
    have hrankL : pRank ↥(Subgroup.centralizer
        ((L.subgroupOf (S : Subgroup G) : Subgroup ↥(S : Subgroup G)) :
          Set ↥(S : Subgroup G))) p ≤ 2 := by
      rw [centralizer_subgroupOf_inf_eq hL_le_S, ← hCLA,
        ← centralizer_subgroupOf_inf_eq hA_le_S]
      exact hrank2'
    obtain ⟨hYcyc, -, hLT, hCdecomp⟩ :=
      Ch1.S05.narrow_centralizer_decomp hp_odd S.isPGroup' h3 hnarrow
        (L.subgroupOf (S : Subgroup G)) hL'card hrankL
    refine ⟨(Subgroup.centralizer
        ((L.subgroupOf (S : Subgroup G) : Subgroup ↥(S : Subgroup G)) :
          Set ↥(S : Subgroup G)) ⊓
      Subgroup.centralizer
        ((omega1UpperCentralTwo ↥(S : Subgroup G) p : Subgroup ↥(S : Subgroup G)) :
          Set ↥(S : Subgroup G))).map (S : Subgroup G).subtype,
      Subgroup.map_subtype_le _, ?_, ?_, ?_, ?_, ?_⟩
    · -- cyclic
      have := hYcyc
      exact isCyclic_of_surjective _
        (Subgroup.equivMapOfInjective _ _ (S : Subgroup G).subtype_injective).surjective
    · -- `Z₁ ≤ Y`
      intro z hz
      have hzS : z ∈ (S : Subgroup G) := omega1CenterInG_le (S : Subgroup G) p hz
      refine Subgroup.mem_map.mpr ⟨⟨z, hzS⟩, Subgroup.mem_inf.mpr ⟨?_, ?_⟩, rfl⟩
      · rw [Subgroup.mem_centralizer_iff]
        intro h hh
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        exact (hZ₁S_comm z hz (h : G) h.2).symm
      · rw [Subgroup.mem_centralizer_iff]
        intro h hh
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        exact (hZ₁S_comm z hz (h : G) h.2).symm
    · -- `L ⊓ Y = ⊥`
      rw [eq_bot_iff]
      intro x hx
      have hxS : x ∈ (S : Subgroup G) := hL_le_S hx.1
      have hxY := hx.2
      obtain ⟨y', hy', hyeq⟩ := Subgroup.mem_map.mp hxY
      have hy'x : y' = ⟨x, hxS⟩ := Subtype.ext hyeq
      rw [hy'x] at hy'
      have hbot : (⟨x, hxS⟩ : ↥(S : Subgroup G)) ∈
          (⊥ : Subgroup ↥(S : Subgroup G)) := by
        rw [← hLT]
        exact ⟨Subgroup.mem_subgroupOf.mpr hx.1, hy'.2⟩
      rw [Subgroup.mem_bot] at hbot
      rw [Subgroup.mem_bot]
      simpa using congrArg Subtype.val hbot
    · -- `C_G(A) ⊓ S = L ⊔ Y`
      have hmapL : (Subgroup.centralizer
            ((L.subgroupOf (S : Subgroup G) : Subgroup ↥(S : Subgroup G)) :
              Set ↥(S : Subgroup G))).map (S : Subgroup G).subtype
          = Subgroup.centralizer (L : Set G) ⊓ (S : Subgroup G) := by
        rw [centralizer_subgroupOf_inf_eq hL_le_S,
          Subgroup.map_subgroupOf_eq_of_le inf_le_right]
      have hmap := congrArg (Subgroup.map (S : Subgroup G).subtype) hCdecomp
      rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hL_le_S, hmapL] at hmap
      rw [hCLA, hmap]
    · -- elements of `Y` centralize `L`
      intro l hl y hy
      obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.mp hy
      have hcomm := Subgroup.mem_centralizer_iff.mp hy'.1
        (⟨l, hL_le_S hl⟩ : ↥(S : Subgroup G)) (Subgroup.mem_subgroupOf.mpr hl)
      have hcoe := congrArg Subtype.val hcomm
      simpa using hcoe
  -- `Z₀ = Ω₁(Z(P))`: order `p` and equal to `Z₁`.
  obtain ⟨L₀g, hL₀A, hL₀Z₁⟩ : ∃ a ∈ A, a ∉ omega1CenterInG (S : Subgroup G) p := by
    by_contra h
    push Not at h
    exact hZ₁ne_A (le_antisymm hZ₁A h)
  have hL₀ne1 : L₀g ≠ 1 := fun h => hL₀Z₁ (by rw [h]; exact Subgroup.one_mem _)
  have hL₀card : Nat.card ↥(Subgroup.zpowers L₀g) = p := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (hApow L₀g hL₀A) hL₀ne1
  have hL₀ne : Subgroup.zpowers L₀g ≠ omega1CenterInG (S : Subgroup G) p := by
    intro h
    exact hL₀Z₁ (h ▸ Subgroup.mem_zpowers L₀g)
  obtain ⟨Y₀, hY₀S, hY₀cyc, hY₀Z₁, hL₀Y₀, hC₀, hL₀Y₀comm⟩ :=
    key (Subgroup.zpowers L₀g) (Subgroup.zpowers_le.mpr hL₀A) hL₀card hL₀ne
  -- `C_S(A)` is abelian (from the generic-line decomposition).
  have hCab : ∀ c₁ ∈ Subgroup.centralizer (A : Set G) ⊓ (S : Subgroup G),
      ∀ c₂ ∈ Subgroup.centralizer (A : Set G) ⊓ (S : Subgroup G), c₁ * c₂ = c₂ * c₁ := by
    rw [hC₀]
    refine comm_sup_of_comm_of_comm (fun x hx y hy => ?_) (fun x hx y hy => ?_) hL₀Y₀comm
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact Commute.zpow_zpow_self L₀g i j
    · have := hY₀cyc
      let : CommGroup ↥Y₀ := IsCyclic.commGroup
      exact congrArg Subtype.val (mul_comm (⟨x, hx⟩ : ↥Y₀) ⟨y, hy⟩)
  -- (10.5): `A ≠ Z₀`, hence `|Z₀| = p` and `Z₀ = Z₁`.
  have hPnt : Nontrivial ↥P := by
    rcases subsingleton_or_nontrivial ↥P with hs | hn
    · exact absurd ⟨⟨fun a b => Subsingleton.elim _ _⟩⟩ hPnonab
    · exact hn
  obtain ⟨zP, -, hzPc, hzP1, hzPp⟩ :=
    exists_mem_omega1_center_of_normal_ne_bot hPp (N := ⊤) top_ne_bot
  have hzPZ₀ : (zP : G) ∈ omega1CenterInG P p :=
    Subgroup.mem_map.mpr ⟨zP, mem_omega1OfAbelian.mpr ⟨hzPc, hzPp⟩, rfl⟩
  have hZ₀A : omega1CenterInG P p ≤ A := omega1CenterInG_le_of_maximal hAea hAmax hAP
  have hAne : A ≠ omega1CenterInG P p := by
    intro heq
    apply hPnonab
    have hPC : P ≤ Subgroup.centralizer (A : Set G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      rw [heq] at ha
      obtain ⟨z', hz', rfl⟩ := Subgroup.mem_map.mp ha
      exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp
        (mem_omega1OfAbelian.mp hz').1 ⟨x, hx⟩)).symm
    exact ⟨⟨fun a b => Subtype.ext
      (hCab _ ⟨hPC a.2, hPS a.2⟩ _ ⟨hPC b.2, hPS b.2⟩)⟩⟩
  have hZ₀card : Nat.card ↥(omega1CenterInG P p) = p := by
    have hdvd : Nat.card ↥(omega1CenterInG P p) ∣ p ^ 2 := by
      rw [← hAcard]
      exact Subgroup.card_dvd_of_le hZ₀A
    obtain ⟨k, hk2, hkeq⟩ := (Nat.dvd_prime_pow Fact.out).mp hdvd
    interval_cases k
    · exfalso
      have hsub : Subsingleton ↥(omega1CenterInG P p) :=
        (Nat.card_eq_one_iff_unique.mp (by rw [hkeq, pow_zero])).1
      have h1 := Subsingleton.elim (⟨(zP : G), hzPZ₀⟩ : ↥(omega1CenterInG P p))
        ⟨1, Subgroup.one_mem _⟩
      exact hzP1 (OneMemClass.coe_eq_one.mp (congrArg Subtype.val h1))
    · rw [hkeq, pow_one]
    · exact absurd (Subgroup.eq_of_le_of_card_ge hZ₀A (by rw [hAcard, hkeq])).symm hAne
  have hZ₁_le_Z₀ : omega1CenterInG (S : Subgroup G) p ≤ omega1CenterInG P p := by
    intro z hz
    have hzA : z ∈ A := hZ₁A hz
    refine Subgroup.mem_map.mpr ⟨⟨z, hAP hzA⟩, mem_omega1OfAbelian.mpr ⟨?_, ?_⟩, rfl⟩
    · rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      exact (hZ₁S_comm z hz (g : G) (hPS g.2)).symm
    · exact Subtype.ext (by
        rw [SubmonoidClass.coe_pow, OneMemClass.coe_one]
        exact pow_eq_one_of_mem_omega1CenterInG hz)
  have hZ₀Z₁ : omega1CenterInG P p = omega1CenterInG (S : Subgroup G) p :=
    (Subgroup.eq_of_le_of_card_ge hZ₁_le_Z₀ (by rw [hZ₁card, hZ₀card])).symm
  -- final assembly with `L = A₀`
  obtain ⟨Y, hYS, hYcyc, hYZ₁, hA₀Y, hCY, hA₀Ycomm⟩ :=
    key A₀ hA₀A hA₀card (by rw [← hZ₀Z₁]; exact hA₀ne)
  refine ⟨Y, hYS, hYcyc, by rw [hZ₀Z₁]; exact hYZ₁, hA₀Y, hCY, ?_, hZ₀card⟩
  rw [hCY]
  refine comm_sup_of_comm_of_comm (fun x hx y hy => ?_) (fun x hx y hy => ?_) hA₀Ycomm
  · exact congrArg Subtype.val (hAea.1 ⟨x, hA₀A hx⟩ ⟨y, hA₀A hy⟩)
  · have := hYcyc
    let : CommGroup ↥Y := IsCyclic.commGroup
    exact congrArg Subtype.val (mul_comm (⟨x, hx⟩ : ↥Y) ⟨y, hy⟩)

/-- Generator of a subgroup of prime order. -/
private theorem exists_zpowers_eq_of_card_prime [Finite G] {p : ℕ} [Fact p.Prime]
    {X : Subgroup G} (hX : Nat.card ↥X = p) :
    ∃ a : G, a ∈ X ∧ orderOf a = p ∧ Subgroup.zpowers a = X := by
  have h1 : 1 < Nat.card ↥X := by rw [hX]; exact (Fact.out : p.Prime).one_lt
  have : Nontrivial ↥X := Finite.one_lt_card_iff_nontrivial.mp h1
  obtain ⟨a, ha1⟩ := exists_ne (1 : ↥X)
  have hane : (a : G) ≠ 1 := fun h => ha1 (Subtype.ext h)
  have hord_dvd : orderOf (a : G) ∣ p := by
    rw [← hX]
    exact Subgroup.orderOf_dvd_natCard X a.2
  have hord : orderOf (a : G) = p :=
    ((Nat.dvd_prime Fact.out).mp hord_dvd).resolve_left
      (fun h => hane (orderOf_eq_one_iff.mp h))
  refine ⟨a, a.2, hord, ?_⟩
  exact Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr a.2)
    (by rw [hX, Nat.card_zpowers, hord])

/-- **GL₂(p)-transvection transitivity, multiplicative form** (core of Lemma 10.13(c)):
if the `p`-element `x` normalizes the rank-two elementary abelian `A` and centralizes the
order-`p` subgroup `Z₀ ≤ A` but not all of `A`, then the powers of `x` conjugate any order-`p`
subgroup `X ≤ A` other than `Z₀` onto any other such `Y`.

In coordinates `A = ⟨a⟩ × ⟨z₀⟩` (`a` a generator of `X`): conjugation by `x` fixes `z₀` and
sends `a ↦ a^{i₀} z₀^{j₀}`; iterating to `x^{orderOf x} = 1` forces `i₀ ≡ 1 (mod p)` (Fermat),
and `j₀ ≢ 0` since `x ∉ C_G(A)`, so `x^k a x^{-k} = a z₀^{k j₀}` sweeps through all lines
`⟨a^m z₀^s⟩ ≠ ⟨z₀⟩` as `k` runs (solve `k j₀ m ≡ s (mod p)` in the field `ZMod p`). -/
private theorem exists_conj_pow_eq_of_fixes_line [Finite G] {p : ℕ} [Fact p.Prime]
    {A Z₀ : Subgroup G} (hAea : A.IsElementaryAbelian p) (hAcard : Nat.card ↥A = p ^ 2)
    {x : G} (hxN : x ∈ Subgroup.normalizer (A : Set G)) {e : ℕ} (hxord : orderOf x = p ^ e)
    (hZ₀A : Z₀ ≤ A) (hZ₀card : Nat.card ↥Z₀ = p)
    (hxZ₀ : ∀ z ∈ Z₀, x * z = z * x)
    (hxnC : ¬ ∀ a ∈ A, x * a = a * x)
    {X Y : Subgroup G} (hXA : X ≤ A) (hXcard : Nat.card ↥X = p) (hXne : X ≠ Z₀)
    (hYA : Y ≤ A) (hYcard : Nat.card ↥Y = p) (hYne : Y ≠ Z₀) :
    ∃ k : ℕ, MulAut.conj (x ^ k) • X = Y := by
  classical
  obtain ⟨a, haX, haord, haz⟩ := exists_zpowers_eq_of_card_prime hXcard
  obtain ⟨z₀, hz₀Z, hz₀ord, hz₀z⟩ := exists_zpowers_eq_of_card_prime hZ₀card
  obtain ⟨b, hbY, hbord, hbz⟩ := exists_zpowers_eq_of_card_prime hYcard
  have haA : a ∈ A := hXA haX
  have hz₀A : z₀ ∈ A := hZ₀A hz₀Z
  have hbA : b ∈ A := hYA hbY
  have hAcomm : ∀ g ∈ A, ∀ h ∈ A, g * h = h * g := fun g hg h hh =>
    congrArg Subtype.val (hAea.1 ⟨g, hg⟩ ⟨h, hh⟩)
  have hcomm_az : Commute a z₀ := hAcomm a haA z₀ hz₀A
  -- coordinates along `A = X ⊔ Z₀`
  have hXZsup : X ⊔ Z₀ = A :=
    eq_sup_of_card_prime_of_ne hAcard hXA hZ₀A hXcard hZ₀card hXne
  have hcoord : ∀ g ∈ A, ∃ i j : ℤ, g = a ^ i * z₀ ^ j := by
    intro g hg
    have hmem : g ∈ (↑X * ↑Z₀ : Set G) := by
      rw [(Subgroup.coe_mul_of_left_le_normalizer_right X Z₀
        (le_normalizer_of_forall_comm (fun u hu v hv =>
          hAcomm u (hXA hu) v (hZ₀A hv)))).symm, hXZsup]
      exact hg
    obtain ⟨u, hu, v, hv, rfl⟩ := Set.mem_mul.mp hmem
    rw [← haz] at hu
    rw [← hz₀z] at hv
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    exact ⟨i, j, rfl⟩
  -- coordinate separation: `a^i z₀^j = 1` forces `p ∣ i` and `p ∣ j`
  have hsep : ∀ i j : ℤ, a ^ i * z₀ ^ j = 1 → (p : ℤ) ∣ i ∧ (p : ℤ) ∣ j := by
    intro i j hij
    have hzj_eq : a ^ i = (z₀ ^ j)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one]
      exact hij
    have hai : a ^ i ∈ X ⊓ Z₀ := by
      constructor
      · rw [← haz]
        exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers a) i
      · rw [hzj_eq, ← hz₀z]
        exact Subgroup.inv_mem _ (Subgroup.zpow_mem _ (Subgroup.mem_zpowers z₀) j)
    rw [inf_eq_bot_of_card_prime_of_ne hXcard hZ₀card hXne, Subgroup.mem_bot] at hai
    have hzj : z₀ ^ j = 1 := by
      have h := hij
      rw [hai, one_mul] at h
      exact h
    constructor
    · rw [← haord]
      exact orderOf_dvd_iff_zpow_eq_one.mpr hai
    · rw [← hz₀ord]
      exact orderOf_dvd_iff_zpow_eq_one.mpr hzj
  -- conjugation by `x` in coordinates
  have hxa_mem : x * a * x⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hxN a).mp haA
  obtain ⟨i₀, j₀, hxa⟩ := hcoord _ hxa_mem
  have hxz : ∀ j : ℤ, x * z₀ ^ j * x⁻¹ = z₀ ^ j := by
    intro j
    have hc : Commute x (z₀ ^ j) := (show Commute x z₀ from hxZ₀ z₀ hz₀Z).zpow_right j
    rw [hc.eq]
    group
  -- iterate to `x^{orderOf x} = 1`: the `X`-coordinate of `x^k a x^{-k}` is `i₀^k`
  have hiter : ∀ k : ℕ, ∃ jk : ℤ, x ^ k * a * (x ^ k)⁻¹ = a ^ (i₀ ^ k) * z₀ ^ jk := by
    intro k
    induction k with
    | zero => exact ⟨0, by simp⟩
    | succ n ih =>
      obtain ⟨jn, hjn⟩ := ih
      refine ⟨j₀ * i₀ ^ n + jn, ?_⟩
      have h1 : x ^ (n + 1) * a * (x ^ (n + 1))⁻¹
          = x * (x ^ n * a * (x ^ n)⁻¹) * x⁻¹ := by
        rw [pow_succ']
        group
      have h2 : x * (a ^ i₀ ^ n * z₀ ^ jn) * x⁻¹
          = (x * a * x⁻¹) ^ (i₀ ^ n) * (x * z₀ ^ jn * x⁻¹) := by
        rw [conj_zpow]
        group
      have h3 : (a ^ i₀ * z₀ ^ j₀) ^ i₀ ^ n
          = a ^ (i₀ ^ (n + 1)) * z₀ ^ (j₀ * i₀ ^ n) := by
        rw [((hcomm_az.zpow_zpow i₀ j₀)).mul_zpow, ← zpow_mul, ← zpow_mul]
        congr 2
        rw [pow_succ]
        ring
      rw [h1, hjn, h2, hxz jn, hxa, h3, mul_assoc, ← zpow_add]
  obtain ⟨jN, hjN⟩ := hiter (orderOf x)
  rw [pow_orderOf_eq_one x] at hjN
  have hjN' : a = a ^ (i₀ ^ orderOf x) * z₀ ^ jN := by
    have h := hjN
    rw [one_mul, inv_one, mul_one] at h
    exact h
  -- Fermat: `i₀ ≡ 1 (mod p)`
  have hsep1 : (p : ℤ) ∣ (i₀ ^ orderOf x - 1) ∧ (p : ℤ) ∣ jN := by
    apply hsep
    have hswap : a⁻¹ * z₀ ^ jN = z₀ ^ jN * a⁻¹ := ((hcomm_az.zpow_right jN).inv_left).eq
    calc a ^ (i₀ ^ orderOf x - 1) * z₀ ^ jN
        = a ^ (i₀ ^ orderOf x) * a⁻¹ * z₀ ^ jN := by
          rw [zpow_sub, zpow_one]
      _ = a ^ (i₀ ^ orderOf x) * z₀ ^ jN * a⁻¹ := by
          rw [mul_assoc, hswap, mul_assoc]
      _ = a * a⁻¹ := by rw [← hjN']
      _ = 1 := mul_inv_cancel a
  have hi₀ : (p : ℤ) ∣ (i₀ - 1) := by
    have hcast : ((i₀ ^ orderOf x - 1 : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hsep1.1
    push_cast at hcast
    rw [sub_eq_zero, hxord] at hcast
    have hfermat : ∀ m : ℕ, ((i₀ : ZMod p)) ^ (p ^ m) = (i₀ : ZMod p) := by
      intro m
      induction m with
      | zero => simp
      | succ n ih => rw [pow_succ, pow_mul, ih, ZMod.pow_card]
    rw [hfermat e] at hcast
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [sub_eq_zero]
    exact hcast
  have hxa' : x * a * x⁻¹ = a * z₀ ^ j₀ := by
    have ha_i₀ : a ^ i₀ = a := by
      have h := (zpow_eq_zpow_iff_modEq (x := a) (m := i₀) (n := 1)).mpr (by
        rw [haord]
        exact (Int.modEq_iff_dvd.mpr hi₀).symm)
      simpa using h
    rw [hxa, ha_i₀]
  -- `j₀ ≢ 0 (mod p)`, else `x` would centralize `A`
  have hj₀ : ¬ (p : ℤ) ∣ j₀ := by
    intro hdvd
    apply hxnC
    have hza : z₀ ^ j₀ = 1 :=
      orderOf_dvd_iff_zpow_eq_one.mp (by rw [hz₀ord]; exact hdvd)
    have hcomm_xa : Commute x a := by
      have h := hxa'
      rw [hza, mul_one] at h
      calc x * a = x * a * x⁻¹ * x := by group
        _ = a * x := by rw [h]
    intro g hg
    obtain ⟨i, j, rfl⟩ := hcoord g hg
    exact ((hcomm_xa.zpow_right i).mul_right
      ((show Commute x z₀ from hxZ₀ z₀ hz₀Z).zpow_right j)).eq
  -- with `i₀ = 1`: `x^k a x^{-k} = a z₀^{k j₀}`
  have hiter' : ∀ k : ℕ, x ^ k * a * (x ^ k)⁻¹ = a * z₀ ^ ((k : ℤ) * j₀) := by
    intro k
    induction k with
    | zero => simp
    | succ n ih =>
      have h1 : x ^ (n + 1) * a * (x ^ (n + 1))⁻¹
          = x * (x ^ n * a * (x ^ n)⁻¹) * x⁻¹ := by
        rw [pow_succ']
        group
      have h2 : x * (a * z₀ ^ ((n : ℤ) * j₀)) * x⁻¹
          = (x * a * x⁻¹) * (x * z₀ ^ ((n : ℤ) * j₀) * x⁻¹) := by group
      rw [h1, ih, h2, hxz, hxa', mul_assoc, ← zpow_add]
      congr 2
      push_cast
      ring
  -- coordinates of the target generator: `b = a^m z₀^s` with `p ∤ m`
  obtain ⟨m, sb, hbeq⟩ := hcoord b hbA
  have hm : ¬ (p : ℤ) ∣ m := by
    intro hdvd
    have ham : a ^ m = 1 :=
      orderOf_dvd_iff_zpow_eq_one.mp (by rw [haord]; exact hdvd)
    have hbZ : b ∈ Z₀ := by
      rw [hbeq, ham, one_mul, ← hz₀z]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers z₀) sb
    apply hYne
    rw [← hbz]
    exact Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hbZ)
      (by rw [hZ₀card, Nat.card_zpowers, hbord])
  -- solve `k j₀ m ≡ s (mod p)` in the field `ZMod p`
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  set u : ZMod p := (j₀ : ZMod p) * (m : ZMod p) with hu
  have hu0 : u ≠ 0 := by
    rw [hu]
    exact mul_ne_zero
      (fun h => hj₀ ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h))
      (fun h => hm ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h))
  refine ⟨((sb : ZMod p) * u⁻¹).val, ?_⟩
  set k : ℕ := ((sb : ZMod p) * u⁻¹).val with hk
  have hsolve : (p : ℤ) ∣ ((k : ℤ) * j₀ * m - sb) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [sub_eq_zero]
    have hkcast : ((k : ℕ) : ZMod p) = (sb : ZMod p) * u⁻¹ := by
      rw [hk, ZMod.natCast_val, ZMod.cast_id]
    rw [hkcast, mul_assoc, ← hu, inv_mul_cancel_right₀ hu0]
  -- conclude: `conj (x^k) • X = ⟨a z₀^{k j₀}⟩ = Y`
  have hconj : MulAut.conj (x ^ k) • X = Subgroup.zpowers (x ^ k * a * (x ^ k)⁻¹) := by
    rw [← haz, conjSmul_eq_map, MonoidHom.map_zpowers]
    rfl
  rw [hconj, hiter' k]
  have htA : a * z₀ ^ ((k : ℤ) * j₀) ∈ A :=
    A.mul_mem haA (hZ₀A (by rw [← hz₀z]; exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers z₀) _))
  have hbmem : b ∈ Subgroup.zpowers (a * z₀ ^ ((k : ℤ) * j₀)) := by
    have hpow : (a * z₀ ^ ((k : ℤ) * j₀)) ^ m = b := by
      rw [(hcomm_az.zpow_right ((k : ℤ) * j₀)).mul_zpow, ← zpow_mul, hbeq]
      congr 1
      rw [zpow_eq_zpow_iff_modEq, hz₀ord]
      refine (Int.modEq_iff_dvd.mpr ?_).symm
      exact hsolve
    rw [← hpow]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) m
  have htne : a * z₀ ^ ((k : ℤ) * j₀) ≠ 1 := by
    intro h
    have := (hsep 1 ((k : ℤ) * j₀) (by rw [zpow_one]; exact h)).1
    have h1 := Int.le_of_dvd one_pos this
    have h2 := (Fact.out : p.Prime).one_lt
    omega
  have htpow : (a * z₀ ^ ((k : ℤ) * j₀)) ^ p = 1 := by
    have h := congrArg Subtype.val (hAea.2 ⟨_, htA⟩)
    rwa [SubmonoidClass.coe_pow, OneMemClass.coe_one] at h
  have hzc : Nat.card ↥(Subgroup.zpowers (a * z₀ ^ ((k : ℤ) * j₀))) = p := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime htpow htne
  rw [← hbz]
  exact (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hbmem)
    (by rw [hzc, Nat.card_zpowers, hbord])).symm

/-- **BG Lemma 10.13** (mmd MISSING_PAGE, PDF p.79): `p ∈ π(G)`,
`A ∈ ℰ_p²(G) ∩ ℰ_p*(G)`, and `P` is a nonabelian `p`-subgroup of `G` containing
`A`. Let `Z₀ = Ω₁(Z(P))` and let `A₀ ∈ ℰ¹(A)` with `A₀ ≠ Z₀`. Then
(a) `Z₀ ∈ ℰ¹(A)`; (b) `C_P(A) = A₀ × Z` for a cyclic subgroup `Z` containing
`Z₀`; and (c) `N_P(A)` acts transitively by conjugation on `ℰ¹(A) - {Z₀}`.

Here `Z₀` is `omega1CenterInG P p`, `C_P(A)` is
`Subgroup.centralizer (A : Set G) ⊓ P`, and the internal product in (b) is encoded by
trivial intersection plus equality with the join, following the existing `IsNarrow` convention. -/
theorem nonabelian_pSubgroup_rankTwo_elemAbelian_structure [Finite G]
    (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime]
    (hpG : p ∈ (Nat.card G).primeFactors)
    {A P A₀ : Subgroup G} (hA : A ∈ elemAbelianOfRank G p 2)
    (hAmax : IsMaximalElementaryAbelian p A) (hPp : IsPGroup p ↥P)
    (hPnonab : ¬ IsMulCommutative ↥P) (hAP : A ≤ P)
    (hA₀ : elemAbelianOfRankIn p 1 A A₀) (hA₀ne : A₀ ≠ omega1CenterInG P p) :
    elemAbelianOfRankIn p 1 A (omega1CenterInG P p) ∧
    (∃ Z : Subgroup G, Z ≤ P ∧ IsCyclic ↥Z ∧ omega1CenterInG P p ≤ Z ∧
      A₀ ⊓ Z = ⊥ ∧ Subgroup.centralizer (A : Set G) ⊓ P = A₀ ⊔ Z) ∧
    (∀ X Y : Subgroup G, elemAbelianOfRankIn p 1 A X → X ≠ omega1CenterInG P p →
      elemAbelianOfRankIn p 1 A Y → Y ≠ omega1CenterInG P p →
        ∃ n ∈ Subgroup.normalizer (A : Set G) ⊓ P, MulAut.conj n • X = Y) := by
  classical
  obtain ⟨hAea, hAcard⟩ := hA
  obtain ⟨⟨hA₀ea, hA₀card'⟩, hA₀A⟩ := hA₀
  have hA₀card : Nat.card ↥A₀ = p := by rw [hA₀card', pow_one]
  have hApow : ∀ g ∈ A, g ^ p = 1 := by
    intro g hg
    have h := congrArg Subtype.val (hAea.2 ⟨g, hg⟩)
    rwa [SubmonoidClass.coe_pow, OneMemClass.coe_one] at h
  -- a Sylow `p`-subgroup `S ⊇ P` and the (10.6) decomposition `C_S(A) = A₀ ⊔ Y`
  obtain ⟨S, hPS⟩ := hPp.exists_le_sylow
  obtain ⟨Ydec, hYS, hYcyc, hZ₀Y, hA₀Y, hCeq, hCab, hZ₀card⟩ :
      ∃ Y : Subgroup G, Y ≤ (S : Subgroup G) ∧ IsCyclic ↥Y ∧ omega1CenterInG P p ≤ Y ∧
        A₀ ⊓ Y = ⊥ ∧ Subgroup.centralizer (A : Set G) ⊓ (S : Subgroup G) = A₀ ⊔ Y ∧
        (∀ c₁ ∈ Subgroup.centralizer (A : Set G) ⊓ (S : Subgroup G),
          ∀ c₂ ∈ Subgroup.centralizer (A : Set G) ⊓ (S : Subgroup G), c₁ * c₂ = c₂ * c₁) ∧
        Nat.card ↥(omega1CenterInG P p) = p := by
    rcases Nat.lt_or_ge (pRank ↥(S : Subgroup G) p) 3 with h2 | h3
    · refine centralizer_sylow_decomp_of_rank_le_two hG S hAea hAcard hAmax hPp hPnonab
        hAP hPS hA₀A hA₀card hA₀ne ?_
      rw [rank_le_iff]
      intro q hq
      have : Fact q.Prime := ⟨hq⟩
      rcases eq_or_ne q p with rfl | hqp
      · omega
      · rw [pRank_le_iff]
        intro E hEea
        obtain ⟨k, hk⟩ := hEea.isPGroup.exists_card_eq
        have hk0 : k = 0 := by
          by_contra hk0
          have hq_dvd : q ∣ Nat.card ↥(S : Subgroup G) := by
            refine dvd_trans ?_ (Subgroup.card_subgroup_dvd_card E)
            rw [hk]
            exact dvd_pow_self q hk0
          obtain ⟨m', hm'⟩ := S.isPGroup'.exists_card_eq
          rw [hm'] at hq_dvd
          exact hqp ((Nat.prime_dvd_prime_iff_eq hq Fact.out).mp
            (hq.dvd_of_dvd_pow hq_dvd))
        rw [hk, hk0, pow_zero, Nat.log_one_right]
        omega
    · exact centralizer_sylow_decomp_of_three_le_rank hG S hAea hAcard hAmax hPp hPnonab
        hAP hPS hA₀A hA₀card hA₀ne (by omega)
  -- (b): `C_P(A) = A₀ ⊔ (Y ⊓ P)` by the Dedekind argument
  have hA₀P : A₀ ≤ P := hA₀A.trans hAP
  have hA₀comm_Y : ∀ u ∈ A₀, ∀ v ∈ Ydec, u * v = v * u := by
    intro u hu v hv
    refine hCab u ?_ v ?_
    · rw [hCeq]; exact Subgroup.mem_sup_left hu
    · rw [hCeq]; exact Subgroup.mem_sup_right hv
  have hCP : Subgroup.centralizer (A : Set G) ⊓ P = A₀ ⊔ (Ydec ⊓ P) := by
    apply le_antisymm
    · intro c hc
      have hcS : c ∈ A₀ ⊔ Ydec := by
        rw [← hCeq]
        exact ⟨hc.1, hPS hc.2⟩
      have hmem : c ∈ (↑A₀ * ↑Ydec : Set G) := by
        rw [(Subgroup.coe_mul_of_left_le_normalizer_right A₀ Ydec
          (le_normalizer_of_forall_comm hA₀comm_Y)).symm]
        exact hcS
      obtain ⟨a₀, ha₀, y, hy, rfl⟩ := Set.mem_mul.mp hmem
      have hyP : y ∈ P := by
        have heq : y = a₀⁻¹ * (a₀ * y) := by group
        rw [heq]
        exact P.mul_mem (P.inv_mem (hA₀P ha₀)) hc.2
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ha₀)
        (Subgroup.mem_sup_right ⟨hy, hyP⟩)
    · refine sup_le (le_inf ?_ hA₀P) (le_inf ?_ inf_le_right)
      · intro u hu
        rw [Subgroup.mem_centralizer_iff]
        intro g hg
        exact congrArg Subtype.val (hAea.1 ⟨g, hg⟩ ⟨u, hA₀A hu⟩)
      · intro v hv
        have hv' : v ∈ A₀ ⊔ Ydec := Subgroup.mem_sup_right hv.1
        rw [← hCeq] at hv'
        exact hv'.1
  refine ⟨⟨⟨?_, ?_⟩, omega1CenterInG_le_of_maximal hAea hAmax hAP⟩,
    ⟨Ydec ⊓ P, inf_le_right, ?_, le_inf hZ₀Y (omega1CenterInG_le P p), ?_, hCP⟩, ?_⟩
  · -- (a) elementary abelian
    exact omega1OfAbelian_isElementaryAbelian.map P.subtype_injective
  · -- (a) cardinality
    rw [pow_one]
    exact hZ₀card
  · -- (b) cyclicity of `Z = Y ⊓ P`
    have := hYcyc
    exact Subgroup.isCyclic_of_le inf_le_left
  · -- (b) `A₀ ⊓ Z = ⊥`
    rw [eq_bot_iff, ← hA₀Y]
    exact inf_le_inf_left A₀ inf_le_left
  -- (c): a non-centralizing element of `N_P(A)` exists, and its powers act transitively.
  intro X Yl hX hXne hYl hYlne
  have hCPab : ∀ c₁ ∈ Subgroup.centralizer (A : Set G) ⊓ P,
      ∀ c₂ ∈ Subgroup.centralizer (A : Set G) ⊓ P, c₁ * c₂ = c₂ * c₁ := by
    intro c₁ h₁ c₂ h₂
    exact hCab c₁ ⟨h₁.1, hPS h₁.2⟩ c₂ ⟨h₂.1, hPS h₂.2⟩
  have hCPlt : (Subgroup.centralizer (A : Set G) ⊓ P).subgroupOf P < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    have hPle : P ≤ Subgroup.centralizer (A : Set G) ⊓ P :=
      Subgroup.subgroupOf_eq_top.mp htop
    exact hPnonab ⟨⟨fun a b => Subtype.ext (hCPab _ (hPle a.2) _ (hPle b.2))⟩⟩
  have : Group.IsNilpotent ↥P := hPp.isNilpotent
  have hgrow := Group.normalizerCondition_of_isNilpotent (G := ↥P)
    ((Subgroup.centralizer (A : Set G) ⊓ P).subgroupOf P) hCPlt
  obtain ⟨w, hwN, hwC⟩ := SetLike.exists_of_lt hgrow
  -- `A` is exactly the set of exponent-`p` elements of `C_P(A)`
  have hAset : ∀ g : G, g ∈ A ↔ (g ∈ Subgroup.centralizer (A : Set G) ⊓ P ∧ g ^ p = 1) := by
    intro g
    constructor
    · intro hg
      refine ⟨Subgroup.mem_inf.mpr ⟨?_, hAP hg⟩, hApow g hg⟩
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact congrArg Subtype.val (hAea.1 ⟨h, hh⟩ ⟨g, hg⟩)
    · rintro ⟨hg, hgp⟩
      exact mem_of_mem_centralizer_of_pow_eq_one hAea hAmax hg.1 hgp
  -- conjugation by normalizer elements of `C' = C_P(A).subgroupOf P` preserves `C_P(A)`
  have hconjC : ∀ w' : ↥P, w' ∈ Subgroup.normalizer
      (((Subgroup.centralizer (A : Set G) ⊓ P).subgroupOf P : Subgroup ↥P) : Set ↥P) →
      ∀ g ∈ Subgroup.centralizer (A : Set G) ⊓ P,
      (w' : G) * g * (w' : G)⁻¹ ∈ Subgroup.centralizer (A : Set G) ⊓ P := by
    intro w' hw' g hg
    have hg' : (⟨g, hg.2⟩ : ↥P) ∈ (Subgroup.centralizer (A : Set G) ⊓ P).subgroupOf P :=
      Subgroup.mem_subgroupOf.mpr hg
    have h2 := (Subgroup.mem_normalizer_iff.mp hw' ⟨g, hg.2⟩).mp hg'
    rw [Subgroup.mem_subgroupOf] at h2
    simpa using h2
  have hwgN : (w : G) ∈ Subgroup.normalizer (A : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      obtain ⟨hh1, hh2⟩ := (hAset h).mp hh
      refine (hAset _).mpr ⟨hconjC w hwN h hh1, ?_⟩
      rw [conj_pow, hh2, mul_one, mul_inv_cancel]
    · intro hh
      obtain ⟨hh1, hh2⟩ := (hAset _).mp hh
      have h3 := hconjC w⁻¹ (Subgroup.inv_mem _ hwN) _ hh1
      have h4 : ((w⁻¹ : ↥P) : G) * ((w : G) * h * (w : G)⁻¹) * ((w⁻¹ : ↥P) : G)⁻¹ = h := by
        push_cast
        group
      rw [h4] at h3
      refine (hAset _).mpr ⟨h3, ?_⟩
      have h5 : ((w : G) * h * (w : G)⁻¹) ^ p = 1 := hh2
      rw [conj_pow] at h5
      have h6 : h ^ p = (w : G)⁻¹ * 1 * (w : G) := by
        rw [← h5]
        group
      simpa using h6
  have hwgnC : ¬ ∀ a ∈ A, (w : G) * a = a * (w : G) := by
    intro hc
    apply hwC
    refine Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨?_, w.2⟩)
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact (hc h hh).symm
  have hwgZ₀ : ∀ z ∈ omega1CenterInG P p, (w : G) * z = z * (w : G) := by
    intro z hz
    obtain ⟨z', hz', rfl⟩ := Subgroup.mem_map.mp hz
    simpa using congrArg Subtype.val (Subgroup.mem_center_iff.mp
      (mem_omega1OfAbelian.mp hz').1 w)
  obtain ⟨e, he⟩ := IsPGroup.iff_orderOf.mp hPp w
  have hword : orderOf (w : G) = p ^ e := by
    rw [← he]
    exact orderOf_injective P.subtype P.subtype_injective w
  obtain ⟨k, hk⟩ := exists_conj_pow_eq_of_fixes_line hAea hAcard hwgN hword
    (omega1CenterInG_le_of_maximal hAea hAmax hAP) hZ₀card hwgZ₀ hwgnC
    hX.2 (by have := hX.1.2; rwa [pow_one] at this) hXne
    hYl.2 (by have := hYl.1.2; rwa [pow_one] at this) hYlne
  exact ⟨(w : G) ^ k, ⟨Subgroup.pow_mem _ hwgN k, P.pow_mem w.2 k⟩, hk⟩

end OddOrder.BG.Ch3.S10


