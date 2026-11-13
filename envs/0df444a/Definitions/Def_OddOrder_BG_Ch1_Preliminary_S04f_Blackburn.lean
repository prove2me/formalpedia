-- Prove2me | Definitions.Def_OddOrder_BG_Ch1_Preliminary_S04f_Blackburn
-- name    : OddOrder_BG_Ch1_Preliminary_S04f_Blackburn
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T06:10:58.987901+00:00
-- url     : https://prove2.me/theorems/eb9cf239-8295-40d3-8d2e-f68bd1ebcf6f
-- title:
--   BG §4F: Blackburn's theorem (tail)
-- statement:
--   The final part of the Bender–Glauberman §4F development on Blackburn's theorem. The bundle consists of lemmas only.
--
--   The bundle also proves 23 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch1_Preliminary/S04f_Blackburn.lean

/-
Copyright (c) 2026 Yawara ISHIDA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch1_Preliminary/S04f_Blackburn.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S04f_Omega1
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S04f_BlackburnNoncentral

open scoped Pointwise commutatorElement

namespace OddOrder.BG.Ch1.S04

open OddOrder.GroupTheory

open OddOrder.Isaacs.Ch03 (IsAInvariant)

open OddOrder.Isaacs.Ch03.IsAInvariant
  (quotientMulAutHom quotientMulAutHom_apply)

open OddOrder.BG.Ch1_Preliminary (isAInvariant_map_subtype_of_restrict
  isAInvariant_subgroupOf_restrict)

section BlackburnClassification

/-- If an elementary abelian subgroup `T` is centralized by an element `x` of
order dividing `p`, then `T ⊔ ⟨x⟩` is elementary abelian. -/
private theorem isElementaryAbelian_sup_zpowers_of_centralizes
    {R : Type*} [Group R] {p : ℕ} {T : Subgroup R} [T.Normal]
    (hT_elem : T.IsElementaryAbelian p) {x : R} (hxp : x ^ p = 1)
    (hx_cent : ∀ t ∈ T, t * x = x * t) :
    (T ⊔ Subgroup.zpowers x).IsElementaryAbelian p := by
  let X : Subgroup R := Subgroup.zpowers x
  let E : Subgroup R := T ⊔ X
  have hE_mul : (↑E : Set R) = (↑T : Set R) * (↑X : Set R) := by
    dsimp [E, X]
    exact Subgroup.normal_mul T (Subgroup.zpowers x)
  have hX_comm : ∀ u ∈ X, ∀ v ∈ X, u * v = v * u := by
    intro u hu v hv
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    exact (Commute.zpow_zpow_self x i j).eq
  have hT_X_comm : ∀ t ∈ T, ∀ u ∈ X, t * u = u * t := by
    intro t ht u hu
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    exact ((show Commute t x from hx_cent t ht).zpow_right i).eq
  refine ⟨?_, ?_⟩
  · intro a b
    have haE : (a : R) ∈ (↑T : Set R) * (↑X : Set R) := by
      rw [← hE_mul]
      exact a.2
    have hbE : (b : R) ∈ (↑T : Set R) * (↑X : Set R) := by
      rw [← hE_mul]
      exact b.2
    obtain ⟨t₁, ht₁, u₁, hu₁, ha⟩ := haE
    obtain ⟨t₂, ht₂, u₂, hu₂, hb⟩ := hbE
    apply Subtype.ext
    change (a : R) * (b : R) = (b : R) * (a : R)
    rw [← ha, ← hb]
    have ht₁t₂ : t₁ * t₂ = t₂ * t₁ :=
      congrArg Subtype.val (hT_elem.comm ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩)
    have hu₁u₂ : u₁ * u₂ = u₂ * u₁ := hX_comm u₁ hu₁ u₂ hu₂
    have hu₁t₂ : u₁ * t₂ = t₂ * u₁ := (hT_X_comm t₂ ht₂ u₁ hu₁).symm
    have ht₁u₂ : t₁ * u₂ = u₂ * t₁ := hT_X_comm t₁ ht₁ u₂ hu₂
    calc
      t₁ * u₁ * (t₂ * u₂) = t₁ * t₂ * (u₁ * u₂) := by
        rw [show t₁ * u₁ * (t₂ * u₂) = t₁ * (u₁ * t₂) * u₂ by group,
          hu₁t₂]
        group
      _ = t₂ * t₁ * (u₂ * u₁) := by rw [ht₁t₂, hu₁u₂]
      _ = t₂ * u₂ * (t₁ * u₁) := by
        rw [show t₂ * u₂ * (t₁ * u₁) = t₂ * (u₂ * t₁) * u₁ by group,
          ← ht₁u₂]
        group
  · intro a
    have haE : (a : R) ∈ (↑T : Set R) * (↑X : Set R) := by
      rw [← hE_mul]
      exact a.2
    obtain ⟨t, ht, u, hu, ha⟩ := haE
    apply Subtype.ext
    change (a : R) ^ p = 1
    rw [← ha]
    have htu : Commute t u := hT_X_comm t ht u hu
    rw [htu.mul_pow]
    have ht_pow : t ^ p = 1 := congrArg Subtype.val (hT_elem.pow_eq_one ⟨t, ht⟩)
    have hu_pow : u ^ p = 1 := by
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
      rw [← zpow_natCast (x ^ i) p, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
        hxp, one_zpow]
    rw [ht_pow, hu_pow, mul_one]

/-- Blackburn 4.16 Case B-2: every order-`p` element of `D = C_R(T)`
already lies in `T = [Ω₁(R), R]`.  Otherwise `T ⊔ ⟨x⟩` would be elementary
abelian of order `p³`, contradicting `pRank R p ≤ 2`. -/
private theorem blackburn_noncentral_order_p_mem_commutator
    {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]
    (hrank : pRank R p ≤ 2)
    (hT_facts :
      let S : Subgroup R := Omega R p 1
      let T : Subgroup R := ⁅S, (⊤ : Subgroup R)⁆
      (Subgroup.center S).map S.subtype < T ∧ T < S ∧ Nat.card T = p ^ 2)
    (hT_elem :
      let S : Subgroup R := Omega R p 1
      let T : Subgroup R := ⁅S, (⊤ : Subgroup R)⁆
      T.IsElementaryAbelian p) :
    let S : Subgroup R := Omega R p 1
    let T : Subgroup R := ⁅S, (⊤ : Subgroup R)⁆
    let D : Subgroup R := Subgroup.centralizer (T : Set R)
    ∀ x : R, x ∈ D → x ^ p = 1 → x ∈ T := by
  dsimp at hT_facts hT_elem ⊢
  let S : Subgroup R := Omega R p 1
  let T : Subgroup R := ⁅S, (⊤ : Subgroup R)⁆
  let D : Subgroup R := Subgroup.centralizer (T : Set R)
  intro x hxD hxp
  by_contra hxT
  let X : Subgroup R := Subgroup.zpowers x
  have hp : p.Prime := Fact.out
  have hT_normal : T.Normal := by
    dsimp [T]
    exact Subgroup.commutator_normal S (⊤ : Subgroup R)
  have hx_ne : x ≠ 1 := by
    intro hx
    exact hxT (hx ▸ T.one_mem)
  have hx_order : orderOf x = p := orderOf_eq_prime hxp hx_ne
  have hX_card : Nat.card X = p := by
    rw [show X = Subgroup.zpowers x from rfl, Nat.card_zpowers, hx_order]
  have hTX_card_dvd : Nat.card (T ⊓ X : Subgroup R) ∣ p := by
    have hsub_dvd := Subgroup.card_subgroup_dvd_card ((T ⊓ X).subgroupOf X)
    have hsub_card : Nat.card ((T ⊓ X).subgroupOf X) = Nat.card (T ⊓ X : Subgroup R) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (inf_le_right : T ⊓ X ≤ X)).toEquiv
    rwa [hsub_card, hX_card] at hsub_dvd
  have hTX_card : Nat.card (T ⊓ X : Subgroup R) = 1 := by
    rcases (Nat.dvd_prime hp).mp hTX_card_dvd with hcard | hcard
    · exact hcard
    · have hTX_eq_X : T ⊓ X = X := by
        apply Subgroup.eq_of_le_of_card_ge inf_le_right
        rw [hX_card, hcard]
      have hx_mem_TX : x ∈ T ⊓ X := by
        rw [hTX_eq_X]
        exact Subgroup.mem_zpowers x
      exact False.elim (hxT hx_mem_TX.1)
  have hTX_bot : T ⊓ X = ⊥ := Subgroup.eq_bot_of_card_eq _ hTX_card
  have hXT_bot : X ⊓ T = ⊥ := by rw [inf_comm, hTX_bot]
  have hsup_card : Nat.card (T ⊔ X : Subgroup R) = p ^ 3 := by
    have hcard_XT : Nat.card (X ⊔ T : Subgroup R) = Nat.card X * Nat.card T :=
      OddOrder.BG.Ch1.S01.card_sup_eq_card_mul_card_of_disjoint_normal
        (T := X) (M := T) hXT_bot
    calc
      Nat.card (T ⊔ X : Subgroup R) = Nat.card (X ⊔ T : Subgroup R) := by rw [sup_comm]
      _ = Nat.card X * Nat.card T := hcard_XT
      _ = p * p ^ 2 := by rw [hX_card, hT_facts.2.2]
      _ = p ^ 3 := by ring
  have hx_cent : ∀ t ∈ T, t * x = x * t := by
    rw [Subgroup.mem_centralizer_iff] at hxD
    intro t ht
    exact hxD t ht
  have hsup_elem : (T ⊔ X).IsElementaryAbelian p :=
    isElementaryAbelian_sup_zpowers_of_centralizes hT_elem hxp hx_cent
  have hprank_ge : 3 ≤ pRank R p :=
    pow_le_card_of_le_pRank (T ⊔ X : Subgroup R) hsup_elem hsup_card
  have : (3 : ℕ) ≤ 2 := hprank_ge.trans hrank
  omega

/-- Blackburn 4.16 Case B-2: `Ω₁(D)` maps onto `T`, where
`D = C_R(T)` and `T = [Ω₁(R), R]`. -/
private theorem blackburn_noncentral_omega1_centralizer_eq_commutator
    {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]
    (hrank : pRank R p ≤ 2)
    (hT_facts :
      let S : Subgroup R := Omega R p 1
      let T : Subgroup R := ⁅S, (⊤ : Subgroup R)⁆
      (Subgroup.center S).map S.subtype < T ∧ T < S ∧ Nat.card T = p ^ 2)
    (hT_elem :
      let S : Subgroup R := Omega R p 1
      let T : Subgroup R := ⁅S, (⊤ : Subgroup R)⁆
      T.IsElementaryAbelian p) :
    let S : Subgroup R := Omega R p 1
    let T : Subgroup R := ⁅S, (⊤ : Subgroup R)⁆
    let D : Subgroup R := Subgroup.centralizer (T : Set R)
    (Omega D p 1).map D.subtype = T := by
  dsimp at hT_facts hT_elem ⊢
  let S : Subgroup R := Omega R p 1
  let T : Subgroup R := ⁅S, (⊤ : Subgroup R)⁆
  let D : Subgroup R := Subgroup.centralizer (T : Set R)
  have hrelations := blackburn_noncentral_centralizer_relations hT_facts hT_elem
  have hT_le_D : T ≤ D := hrelations.2.1
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    change Subgroup.closure {d : D | d ^ (p ^ 1) = 1} ≤ Subgroup.comap D.subtype T
    rw [Subgroup.closure_le]
    intro d hd
    change (d : R) ∈ T
    have hd_pow_D : d ^ p = 1 := by simpa [pow_one] using hd
    have hd_pow_R : (d : R) ^ p = 1 := congrArg Subtype.val hd_pow_D
    exact blackburn_noncentral_order_p_mem_commutator hrank hT_facts hT_elem
      (d : R) d.2 hd_pow_R
  · intro t htT
    refine ⟨⟨t, hT_le_D htT⟩, ?_, rfl⟩
    refine Omega.mem_of_pow_eq_one ?_
    rw [pow_one]
    apply Subtype.ext
    change t ^ p = 1
    exact congrArg (fun u : T => (u : R)) (hT_elem.pow_eq_one ⟨t, htT⟩)

/-- Blackburn 4.16 Case B-2: a Maschke complement `X/C` in
`D/C = C_R(T)/C_R(S)` is cyclic.  The key point is that every order-`p`
generator of `Ω₁(X)` lies in `Ω₁(D)=T`; its quotient image lies in both the
`X/C` and `TC/C` summands, hence is trivial and the generator lies in `C`.
Since `Ω₁(C)` has order `p`, the rank-one cyclicity criterion applies to `X`. -/
private theorem blackburn_noncentral_centralizer_complement_isCyclic
    {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]
    (hp_odd : Odd p) (hR : IsPGroup p R)
    (hΩ_extraspecial : IsExtraspecial p (Omega R p 1))
    (hT_facts :
      let S : Subgroup R := Omega R p 1
      let T : Subgroup R := ⁅S, (⊤ : Subgroup R)⁆
      (Subgroup.center S).map S.subtype < T ∧ T < S ∧ Nat.card T = p ^ 2)
    (hT_elem :
      let S : Subgroup R := Omega R p 1
      let T : Subgroup R := ⁅S, (⊤ : Subgroup R)⁆
      T.IsElementaryAbelian p)
    (hΩD_eq_T :
      let S : Subgroup R := Omega R p 1
      let T : Subgroup R := ⁅S, (⊤ : Subgroup R)⁆
      let D : Subgroup R := Subgroup.centralizer (T : Set R)
      (Omega D p 1).map D.subtype = T)
    (hΩC_eq_center :
      let S : Subgroup R := Omega R p 1
      let C : Subgroup R := Subgroup.centralizer (S : Set R)
      (Omega C p 1).map C.subtype = (Subgroup.center S).map S.subtype)
    {X : Subgroup (Subgroup.centralizer ((⁅Omega R p 1, (⊤ : Subgroup R)⁆ : Subgroup R) : Set R))}
    (hX_inf_T :
      let S : Subgroup R := Omega R p 1
      let T : Subgroup R := ⁅S, (⊤ : Subgroup R)⁆
      let C : Subgroup R := Subgroup.centralizer (S : Set R)
      let D : Subgroup R := Subgroup.centralizer (T : Set R)
      let hCD_normal : (C.subgroupOf D).Normal :=
        (blackburn_noncentral_centralizer_normalities (R := R) (p := p)).2.2
      letI : (C.subgroupOf D).Normal := hCD_normal
      X.map (QuotientGroup.mk' (C.subgroupOf D)) ⊓
          (T.subgroupOf D).map (QuotientGroup.mk' (C.subgroupOf D)) = ⊥) :
    IsCyclic X := by
  dsimp at hT_facts hT_elem hΩD_eq_T hΩC_eq_center hX_inf_T ⊢
  let S : Subgroup R := Omega R p 1
  let T : Subgroup R := ⁅S, (⊤ : Subgroup R)⁆
  let C : Subgroup R := Subgroup.centralizer (S : Set R)
  let D : Subgroup R := Subgroup.centralizer (T : Set R)
  have hrelations := blackburn_noncentral_centralizer_relations hT_facts hT_elem
  have hT_le_D : T ≤ D := hrelations.2.1
  have hCD_norms := blackburn_noncentral_centralizer_normalities (R := R) (p := p)
  have hCD_normal : (C.subgroupOf D).Normal := hCD_norms.2.2
  let q : D →* D ⧸ C.subgroupOf D := QuotientGroup.mk' (C.subgroupOf D)
  let f : X →* R := D.subtype.comp X.subtype
  have hf_inj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    exact D.subtype_injective hab
  have hΩX_map_le : (Omega X p 1).map f ≤ (Omega C p 1).map C.subtype := by
    rw [Subgroup.map_le_iff_le_comap]
    change Subgroup.closure {x : X | x ^ (p ^ 1) = 1} ≤
      Subgroup.comap f ((Omega C p 1).map C.subtype)
    rw [Subgroup.closure_le]
    intro x hxpow
    change f x ∈ (Omega C p 1).map C.subtype
    have hxpow_X : (x : X) ^ p = 1 := by simpa [pow_one] using hxpow
    have hxpow_D : (x : D) ^ p = 1 := congrArg Subtype.val hxpow_X
    have hxΩD : (x : D) ∈ Omega D p 1 := by
      refine Omega.mem_of_pow_eq_one ?_
      rw [pow_one]
      exact hxpow_D
    have hxT : ((x : D) : R) ∈ T := by
      have hxmap : ((x : D) : R) ∈ (Omega D p 1).map D.subtype :=
        ⟨(x : D), hxΩD, rfl⟩
      rwa [hΩD_eq_T] at hxmap
    have hxTsub : (x : D) ∈ T.subgroupOf D := by
      rw [Subgroup.mem_subgroupOf]
      exact hxT
    have hxXmap : q (x : D) ∈ X.map q := ⟨(x : D), x.property, rfl⟩
    have hxTmap : q (x : D) ∈ (T.subgroupOf D).map q :=
      ⟨(x : D), hxTsub, rfl⟩
    have hxq_one : q (x : D) = 1 := by
      have hxinf : q (x : D) ∈ X.map q ⊓ (T.subgroupOf D).map q := ⟨hxXmap, hxTmap⟩
      rw [hX_inf_T, Subgroup.mem_bot] at hxinf
      exact hxinf
    have hxC : (x : D) ∈ C.subgroupOf D := (QuotientGroup.eq_one_iff (x : D)).mp hxq_one
    refine ⟨⟨((x : D) : R), Subgroup.mem_subgroupOf.mp hxC⟩, ?_, ?_⟩
    · refine Omega.mem_of_pow_eq_one ?_
      rw [pow_one]
      apply Subtype.ext
      change ((x : D) : R) ^ p = 1
      exact congrArg Subtype.val hxpow_D
    · rfl
  have hΩC_map_card : Nat.card ((Omega C p 1).map C.subtype) = p := by
    rw [hΩC_eq_center, Subgroup.card_map_of_injective S.subtype_injective,
      hΩ_extraspecial.center_card]
  have hΩX_card_le : Nat.card (Omega X p 1) ≤ p := by
    have hΩX_map_card : Nat.card ((Omega X p 1).map f) = Nat.card (Omega X p 1) :=
      Subgroup.card_map_of_injective (K := Omega X p 1) hf_inj
    calc
      Nat.card (Omega X p 1) = Nat.card ((Omega X p 1).map f) := hΩX_map_card.symm
      _ ≤ Nat.card ((Omega C p 1).map C.subtype) := Subgroup.card_le_of_le hΩX_map_le
      _ = p := hΩC_map_card
  have hD_pg : IsPGroup p D := hR.to_subgroup D
  have hX_pg : IsPGroup p X := hD_pg.to_subgroup X
  exact isCyclic_of_card_omega1_le_prime hX_pg hp_odd hΩX_card_le

/-- Blackburn 4.16 Case B-2 quotient sizes: from `Z(S) < T < S`,
`|S| = p³`, `|T| = p²`, and `|Z(S)| = p`, both `S/T` and `T/S'`
have order `p`.  The second quotient uses `S' = Z(S)` from extraspeciality,
transported into the ambient group by `S.subtype`. -/
private theorem blackburn_noncentral_commutator_quotient_cards
    {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]
    (hΩ_card : Nat.card (Omega R p 1) = p ^ 3)
    (hΩ_extraspecial : IsExtraspecial p (Omega R p 1))
    (hT_facts :
      let S : Subgroup R := Omega R p 1
      let T : Subgroup R := ⁅S, (⊤ : Subgroup R)⁆
      (Subgroup.center S).map S.subtype < T ∧ T < S ∧ Nat.card T = p ^ 2) :
    let S : Subgroup R := Omega R p 1
    let T : Subgroup R := ⁅S, (⊤ : Subgroup R)⁆
    let Z : Subgroup R := (Subgroup.center S).map S.subtype
    Nat.card (S ⧸ T.subgroupOf S) = p ∧ Nat.card (T ⧸ Z.subgroupOf T) = p := by
  dsimp at hT_facts ⊢
  let S : Subgroup R := Omega R p 1
  let T : Subgroup R := ⁅S, (⊤ : Subgroup R)⁆
  let Z : Subgroup R := (Subgroup.center S).map S.subtype
  have hp : p.Prime := Fact.out
  have hZ_lt_T : Z < T := hT_facts.1
  have hT_lt_S : T < S := hT_facts.2.1
  have hT_card : Nat.card T = p ^ 2 := hT_facts.2.2
  have hZ_le_T : Z ≤ T := hZ_lt_T.le
  have hT_le_S : T ≤ S := hT_lt_S.le
  have hTsub_card : Nat.card (T.subgroupOf S) = Nat.card T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT_le_S).toEquiv
  have hS_lagrange : Nat.card S =
      Nat.card (S ⧸ T.subgroupOf S) * Nat.card (T.subgroupOf S) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (T.subgroupOf S)
  have hS_quot_card : Nat.card (S ⧸ T.subgroupOf S) = p := by
    have hmul : Nat.card (S ⧸ T.subgroupOf S) * p ^ 2 = p * p ^ 2 := by
      calc
        Nat.card (S ⧸ T.subgroupOf S) * p ^ 2
            = Nat.card (S ⧸ T.subgroupOf S) * Nat.card (T.subgroupOf S) := by
              rw [hTsub_card, hT_card]
        _ = Nat.card S := hS_lagrange.symm
        _ = p ^ 3 := hΩ_card
        _ = p * p ^ 2 := by ring
    exact Nat.eq_of_mul_eq_mul_right (Nat.pow_pos hp.pos : 0 < p ^ 2) hmul
  have hZ_card : Nat.card Z = p := by
    dsimp [Z]
    rw [Subgroup.card_map_of_injective S.subtype_injective, hΩ_extraspecial.center_card]
  have hZsub_card : Nat.card (Z.subgroupOf T) = Nat.card Z :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZ_le_T).toEquiv
  have hT_lagrange : Nat.card T =
      Nat.card (T ⧸ Z.subgroupOf T) * Nat.card (Z.subgroupOf T) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (Z.subgroupOf T)
  have hT_quot_card : Nat.card (T ⧸ Z.subgroupOf T) = p := by
    have hmul : Nat.card (T ⧸ Z.subgroupOf T) * p = p * p := by
      calc
        Nat.card (T ⧸ Z.subgroupOf T) * p
            = Nat.card (T ⧸ Z.subgroupOf T) * Nat.card (Z.subgroupOf T) := by
              rw [hZsub_card, hZ_card]
        _ = Nat.card T := hT_lagrange.symm
        _ = p ^ 2 := hT_card
        _ = p * p := by ring
    exact Nat.eq_of_mul_eq_mul_right hp.pos hmul
  exact ⟨hS_quot_card, hT_quot_card⟩

/-- Normality support for Blackburn 4.16 Case B-2.  `T = [S,R]` is
normal in `R`, hence `T.subgroupOf S` is normal in `S`; since `T` is elementary
abelian, the embedded center `S' = Z(S)` is normal inside `T`. -/
private theorem blackburn_noncentral_commutator_normalities
    {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]
    (hT_elem :
      let S : Subgroup R := Omega R p 1
      let T : Subgroup R := ⁅S, (⊤ : Subgroup R)⁆
      T.IsElementaryAbelian p) :
    let S : Subgroup R := Omega R p 1
    let T : Subgroup R := ⁅S, (⊤ : Subgroup R)⁆
    let Z : Subgroup R := (Subgroup.center S).map S.subtype
    T.Normal ∧ (T.subgroupOf S).Normal ∧ (Z.subgroupOf T).Normal := by
  dsimp at hT_elem ⊢
  let S : Subgroup R := Omega R p 1
  let T : Subgroup R := ⁅S, (⊤ : Subgroup R)⁆
  let Z : Subgroup R := (Subgroup.center S).map S.subtype
  have hS_normal : S.Normal := by dsimp [S]; infer_instance
  have hT_normal : T.Normal := by
    dsimp [T]
    exact Subgroup.commutator_normal S (⊤ : Subgroup R)
  have hT_sub_S_normal : (T.subgroupOf S).Normal := hT_normal.subgroupOf S
  have hT_comm_inst : IsMulCommutative T := ⟨⟨hT_elem.1⟩⟩
  have hZ_sub_T_normal : (Z.subgroupOf T).Normal :=
    Subgroup.normal_of_isMulCommutative (Z.subgroupOf T)
  exact ⟨hT_normal, hT_sub_S_normal, hZ_sub_T_normal⟩

/-- Blackburn 4.16 Case B-2: if `y ∈ S \ T` and `z ∈ T \ Z(S)`, then the
second commutator `[y,z]` is a nontrivial element of `Z(S) = S'`.

Indeed, if `y` centralized `z`, then the cyclic image of `y` generates the prime
order quotient `S/T`; together with the abelianity of `T`, every element of `S`
would centralize `z`, forcing `z ∈ Z(S)`. -/
private theorem blackburn_noncentral_second_commutator_mem_center_and_ne_one
    {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]
    (hΩ_extraspecial : IsExtraspecial p (Omega R p 1))
    (hT_facts :
      let S : Subgroup R := Omega R p 1
      let T : Subgroup R := ⁅S, (⊤ : Subgroup R)⁆
      (Subgroup.center S).map S.subtype < T ∧ T < S ∧ Nat.card T = p ^ 2)
    (hT_elem :
      let S : Subgroup R := Omega R p 1
      let T : Subgroup R := ⁅S, (⊤ : Subgroup R)⁆
      T.IsElementaryAbelian p)
    (hT_quot_cards :
      let S : Subgroup R := Omega R p 1
      let T : Subgroup R := ⁅S, (⊤ : Subgroup R)⁆
      let Z : Subgroup R := (Subgroup.center S).map S.subtype
      Nat.card (S ⧸ T.subgroupOf S) = p ∧ Nat.card (T ⧸ Z.subgroupOf T) = p)
    {y z : R}
    (hyS : y ∈ Omega R p 1)
    (hyT : y ∉ ⁅Omega R p 1, (⊤ : Subgroup R)⁆)
    (hzT : z ∈ ⁅Omega R p 1, (⊤ : Subgroup R)⁆)
    (hzZ : z ∉ (Subgroup.center (Omega R p 1)).map (Omega R p 1).subtype) :
    let S : Subgroup R := Omega R p 1
    let Z : Subgroup R := (Subgroup.center S).map S.subtype
    ⁅y, z⁆ ∈ Z ∧ ⁅y, z⁆ ≠ 1 := by
  dsimp at hT_facts hT_elem hT_quot_cards hyS hyT hzT hzZ ⊢
  let S : Subgroup R := Omega R p 1
  let T : Subgroup R := ⁅S, (⊤ : Subgroup R)⁆
  let Z : Subgroup R := (Subgroup.center S).map S.subtype
  have hT_le_S : T ≤ S := hT_facts.2.1.le
  have hZ_eq_comm : Z = ⁅S, S⁆ := by
    dsimp [S, Z]
    rw [← hΩ_extraspecial.commutator_eq_center, Subgroup.map_subtype_commutator]
  have hmemZ : ⁅y, z⁆ ∈ Z := by
    rw [hZ_eq_comm]
    exact Subgroup.commutator_mem_commutator hyS (hT_le_S hzT)
  refine ⟨hmemZ, ?_⟩
  intro hyz_one
  have hyz_comm : Commute y z := commutatorElement_eq_one_iff_commute.mp hyz_one
  have hnorms := blackburn_noncentral_commutator_normalities hT_elem
  have hTsub_normal : (T.subgroupOf S).Normal := by
    simpa [S, T, Z] using hnorms.2.1
  let Tsub : Subgroup S := T.subgroupOf S
  let yS : S := ⟨y, hyS⟩
  let qy : S ⧸ Tsub := QuotientGroup.mk' Tsub yS
  have hqy_ne : qy ≠ 1 := by
    intro hqy
    have hyTsub : yS ∈ Tsub := (QuotientGroup.eq_one_iff yS).mp hqy
    exact hyT (Subgroup.mem_subgroupOf.mp hyTsub)
  have hquot_card : Nat.card (S ⧸ Tsub) = p := by
    simpa [S, T, Z, Tsub] using hT_quot_cards.1
  have hqy_top : Subgroup.zpowers qy = ⊤ :=
    zpowers_eq_top_of_prime_card hquot_card hqy_ne
  have hz_center : z ∈ Z := by
    refine ⟨⟨z, hT_le_S hzT⟩, ?_, rfl⟩
    change (⟨z, hT_le_S hzT⟩ : S) ∈ Subgroup.center S
    rw [Subgroup.mem_center_iff]
    intro sS
    have hs_mem : (QuotientGroup.mk' Tsub sS : S ⧸ Tsub) ∈ Subgroup.zpowers qy := by
      rw [hqy_top]
      exact Subgroup.mem_top _
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hs_mem
    have hquot_eq : QuotientGroup.mk' Tsub sS = QuotientGroup.mk' Tsub (yS ^ n) := by
      simpa [qy] using hn.symm
    have hdivT : sS * (yS ^ n)⁻¹ ∈ Tsub := by
      have hdiv : sS / (yS ^ n) ∈ Tsub :=
        (QuotientGroup.eq_iff_div_mem.mp hquot_eq)
      simpa [div_eq_mul_inv] using hdiv
    have htT : ((sS * (yS ^ n)⁻¹ : S) : R) ∈ T :=
      Subgroup.mem_subgroupOf.mp hdivT
    have ht_comm : Commute (((sS * (yS ^ n)⁻¹ : S) : R)) z := by
      exact congrArg Subtype.val
        (hT_elem.comm ⟨((sS * (yS ^ n)⁻¹ : S) : R), htT⟩ ⟨z, hzT⟩)
    have hyn_comm : Commute (((yS ^ n : S) : R)) z := by
      simpa [yS] using hyz_comm.zpow_left n
    have hs_decomp : (sS : R) = ((sS * (yS ^ n)⁻¹ : S) : R) * ((yS ^ n : S) : R) := by
      change (sS : R) = (sS : R) * (((yS ^ n : S) : R))⁻¹ * ((yS ^ n : S) : R)
      group
    have hs_comm : Commute (sS : R) z := by
      rw [hs_decomp]
      exact ht_comm.mul_left hyn_comm
    apply Subtype.ext
    exact hs_comm.eq
  exact hzZ hz_center

/-- If `G` is generated by a normal subgroup `S` and a subgroup `X`, and the
commutators `[S,S]` and `[X,S]` vanish modulo a normal subgroup `Z`, while `X`
is abelian, then `G/Z` is abelian.  This is the group-theoretic bridge used in
Blackburn 4.16 Case B-2 to turn a hypothetical trivial action of the cyclic
complement on `S/S'` into centralization of `S/S'` by all of `R`. -/
private theorem quotient_commutative_of_sup_commutators_le
    {G : Type*} [Group G] {S X Z : Subgroup G} [S.Normal] [Z.Normal]
    (hSX : S ⊔ X = ⊤)
    (hSS : ⁅S, S⁆ ≤ Z) (hXS : ⁅X, S⁆ ≤ Z)
    (hX_comm : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) :
    IsMulCommutative (G ⧸ Z) := by
  let q : G →* G ⧸ Z := QuotientGroup.mk' Z
  refine ⟨⟨fun a b => ?_⟩⟩
  obtain ⟨r, rfl⟩ := QuotientGroup.mk'_surjective Z a
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective Z b
  have hr_top : r ∈ S ⊔ X := by
    rw [hSX]
    exact Subgroup.mem_top r
  have hu_top : u ∈ S ⊔ X := by
    rw [hSX]
    exact Subgroup.mem_top u
  obtain ⟨s₁, hs₁, x₁, hx₁, hr⟩ :=
    (Subgroup.mem_sup_of_normal_left (s := S) (t := X) (x := r)).mp hr_top
  obtain ⟨s₂, hs₂, x₂, hx₂, hu⟩ :=
    (Subgroup.mem_sup_of_normal_left (s := S) (t := X) (x := u)).mp hu_top
  have hss : Commute (q s₁) (q s₂) := by
    rw [← commutatorElement_eq_one_iff_commute, ← map_commutatorElement]
    change QuotientGroup.mk' Z ⁅s₁, s₂⁆ = 1
    exact (QuotientGroup.eq_one_iff ⁅s₁, s₂⁆).mpr
      (hSS (Subgroup.commutator_mem_commutator hs₁ hs₂))
  have hxs : Commute (q x₁) (q s₂) := by
    rw [← commutatorElement_eq_one_iff_commute, ← map_commutatorElement]
    change QuotientGroup.mk' Z ⁅x₁, s₂⁆ = 1
    exact (QuotientGroup.eq_one_iff ⁅x₁, s₂⁆).mpr
      (hXS (Subgroup.commutator_mem_commutator hx₁ hs₂))
  have hsx : Commute (q s₁) (q x₂) := by
    rw [← commutatorElement_eq_one_iff_commute, ← map_commutatorElement]
    change QuotientGroup.mk' Z ⁅s₁, x₂⁆ = 1
    have hx₂s₁ : ⁅x₂, s₁⁆ ∈ Z := hXS (Subgroup.commutator_mem_commutator hx₂ hs₁)
    have hs₁x₂ : ⁅s₁, x₂⁆ ∈ Z := by
      rw [← commutatorElement_inv x₂ s₁]
      exact Z.inv_mem hx₂s₁
    exact (QuotientGroup.eq_one_iff ⁅s₁, x₂⁆).mpr hs₁x₂
  have hxx : Commute (q x₁) (q x₂) := by
    change q x₁ * q x₂ = q x₂ * q x₁
    simpa [q] using congrArg q (hX_comm x₁ hx₁ x₂ hx₂)
  calc
    q r * q u = (q s₁ * q x₁) * (q s₂ * q x₂) := by
      rw [← hr, ← hu]
      simp [q]
    _ = (q s₂ * q x₂) * (q s₁ * q x₁) :=
      ((hss.mul_left hxs).mul_right (hsx.mul_left hxx)).eq
    _ = q u * q r := by
      rw [← hr, ← hu]
      simp [q]

/-- If the cyclic subgroup generated by `x` does not centralize `S` modulo `Z`,
then the generator itself has a noncentral commutator with some element of `S`.
This turns the Blackburn B-2 complement action from a subgroup statement into
one generator-level witness. -/
private theorem exists_commutator_generator_not_mem_of_zpowers_commutator_not_le
    {G : Type*} [Group G] {S Z : Subgroup G} [Z.Normal] {x : G}
    (hnot : ¬ ⁅Subgroup.zpowers x, S⁆ ≤ Z) :
    ∃ y : G, y ∈ S ∧ ⁅x, y⁆ ∉ Z := by
  by_contra hnone
  apply hnot
  rw [Subgroup.commutator_le]
  intro u hu s hs
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
  have hxs_mem : ⁅x, s⁆ ∈ Z := by
    by_contra hxs_not
    exact hnone ⟨s, hs, hxs_not⟩
  let q : G →* G ⧸ Z := QuotientGroup.mk' Z
  have hxs_comm : Commute (q x) (q s) := by
    rw [← commutatorElement_eq_one_iff_commute, ← map_commutatorElement]
    change QuotientGroup.mk' Z ⁅x, s⁆ = 1
    exact (QuotientGroup.eq_one_iff ⁅x, s⁆).mpr hxs_mem
  have hxpow_comm : Commute (q (x ^ n)) (q s) := by
    simpa [q] using hxs_comm.zpow_left n
  apply (QuotientGroup.eq_one_iff ⁅x ^ n, s⁆).mp
  change QuotientGroup.mk' Z ⁅x ^ n, s⁆ = 1
  rw [map_commutatorElement]
  exact commutatorElement_eq_one_iff_commute.mpr hxpow_comm

/-- Blackburn 4.16 Case B-2: if `R = S D`, where `D = C_R(T)` is
`A`-invariant and normal, then `[R,A]=R` forces some operator to move `S`
nontrivially modulo `T`.  Otherwise every action commutator of an element
`s * d` lies in `D`, so `[R,A] ≤ D`, contradicting `D ≠ R`. -/
private theorem exists_operator_moving_omega1_mod_commutator
    {R : Type*} [Group R] {p : ℕ} [Fact p.Prime]
    {A : Type*} [Group A] {φ : A →* MulAut R}
    {S T D : Subgroup R} [D.Normal]
    (hT_le_D : T ≤ D) (hSD_top : S ⊔ D = ⊤)
    (hD_inv : IsAInvariant φ D)
    (hD_ne_top : D ≠ ⊤)
    (hRA : OddOrder.Isaacs.Ch04.actionCommutator φ = ⊤) :
    ∃ a : A, ∃ s : R, s ∈ S ∧ (φ a) s * s⁻¹ ∉ T := by
  by_contra hnone
  have hS_action_le_T : ∀ a : A, ∀ s : R, s ∈ S → (φ a) s * s⁻¹ ∈ T := by
    intro a s hs
    by_contra hsT
    exact hnone ⟨a, s, hs, hsT⟩
  have hcomm_le_D : OddOrder.Isaacs.Ch04.actionCommutator φ ≤ D := by
    rw [OddOrder.Isaacs.Ch04.actionCommutator_le_iff]
    intro a g
    have hg_top : g ∈ S ⊔ D := by
      rw [hSD_top]
      exact Subgroup.mem_top g
    obtain ⟨s, hsS, d, hdD, hsd⟩ :=
      (Subgroup.mem_sup_of_normal_right (s := S) (t := D) (x := g)).mp hg_top
    subst g
    have hs_part : (φ a) s * s⁻¹ ∈ D := hT_le_D (hS_action_le_T a s hsS)
    have hd_part : (φ a) d * d⁻¹ ∈ D :=
      D.mul_mem (hD_inv.smul_mem a hdD) (D.inv_mem hdD)
    have hconj_part : s * ((φ a) d * d⁻¹) * s⁻¹ ∈ D :=
      (inferInstance : D.Normal).conj_mem _ hd_part s
    have hfactor : (φ a) (s * d) * (s * d)⁻¹ =
        ((φ a) s * s⁻¹) * (s * ((φ a) d * d⁻¹) * s⁻¹) := by
      rw [map_mul]
      group
    rw [hfactor]
    exact D.mul_mem hs_part hconj_part
  have htop_le_D : (⊤ : Subgroup R) ≤ D := by
    rw [← hRA]
    exact hcomm_le_D
  have hD_top : D = ⊤ := by
    apply eq_top_iff.mpr
    intro g hg
    exact htop_le_D hg
  exact hD_ne_top hD_top

/-- Blackburn 4.16 Case B-2: the cyclic Maschke complement cannot centralize
`S/S'`.  If `[X,S] ≤ S'`, then the quotient by `S' = Z(S)` is abelian because
`R = S X`, `S/S'` is abelian, and `X` is cyclic.  Hence `[S,R] ≤ S'`,
contradicting the noncentral branch. -/
private theorem blackburn_noncentral_complement_commutator_not_le_center
    {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]
    (hΩ_extraspecial : IsExtraspecial p (Omega R p 1))
    (hnot : ¬ ⁅(Omega R p 1 : Subgroup R), (⊤ : Subgroup R)⁆ ≤
      (Subgroup.center (Omega R p 1)).map (Omega R p 1).subtype)
    {X : Subgroup R}
    (hSX_top :
      let S : Subgroup R := Omega R p 1
      S ⊔ X = ⊤)
    (hX_comm : IsMulCommutative X) :
    let S : Subgroup R := Omega R p 1
    let Z : Subgroup R := (Subgroup.center S).map S.subtype
    ¬ ⁅X, S⁆ ≤ Z := by
  dsimp at hSX_top ⊢
  let S : Subgroup R := Omega R p 1
  let Z : Subgroup R := (Subgroup.center S).map S.subtype
  have hS_normal : S.Normal := by
    dsimp [S]
    infer_instance
  have hZ_eq_comm : Z = ⁅S, S⁆ := by
    dsimp [S, Z]
    rw [← hΩ_extraspecial.commutator_eq_center, Subgroup.map_subtype_commutator]
  have hZ_normal : Z.Normal := by
    rw [hZ_eq_comm]
    infer_instance
  intro hXS
  apply hnot
  change ⁅S, (⊤ : Subgroup R)⁆ ≤ Z
  have hSS : ⁅S, S⁆ ≤ Z := by
    rw [← hZ_eq_comm]
  have hX_comm' : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x := by
    intro x hx y hy
    exact congrArg Subtype.val (hX_comm.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hquot_comm : IsMulCommutative (R ⧸ Z) :=
    quotient_commutative_of_sup_commutators_le hSX_top hSS hXS hX_comm'
  have hcomm_le_Z : _root_.commutator R ≤ Z :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := Z)).mp hquot_comm
  rw [_root_.commutator_def] at hcomm_le_Z
  exact (Subgroup.commutator_mono (show S ≤ (⊤ : Subgroup R) from le_top) le_top).trans hcomm_le_Z

/-- An automorphism of a cyclic group is the identity if it fixes a generator. -/
private theorem mulAut_eq_one_of_zpowers_eq_top_of_apply_eq
    {G : Type*} [Group G] {g : G} {σ : MulAut G}
    (hgen : Subgroup.zpowers g = ⊤) (hσg : σ g = g) :
    σ = 1 := by
  ext u
  have hu : u ∈ Subgroup.zpowers g := by
    rw [hgen]
    exact Subgroup.mem_top u
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
  simp [map_zpow, hσg]

/-- A commutator that lies in the quotient kernel gives commuting quotient images. -/
private theorem commute_quotient_of_commutator_mem
    {G : Type*} [Group G] {N : Subgroup G} [N.Normal] {x y : G}
    (hxy : ⁅x, y⁆ ∈ N) :
    Commute (QuotientGroup.mk' N x) (QuotientGroup.mk' N y) := by
  rw [← commutatorElement_eq_one_iff_commute, ← map_commutatorElement]
  exact (QuotientGroup.eq_one_iff ⁅x, y⁆).mpr hxy

/-- A right-hand error factor commuting with the left entry and the retained right
entry does not change the commutator. -/
private theorem commutatorElement_mul_right_eq_of_commute
    {G : Type*} [Group G] {x t y : G}
    (hxt : Commute x t) (hyt : Commute y t) :
    ⁅x, t * y⁆ = ⁅x, y⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  have ht_comm : Commute t (x * y * x⁻¹ * y⁻¹) := by
    have htx : Commute t x := hxt.symm
    have hty : Commute t y := hyt.symm
    have htx_inv : Commute t x⁻¹ := by
      simpa using htx.zpow_right (-1 : ℤ)
    have hty_inv : Commute t y⁻¹ := by
      simpa using hty.zpow_right (-1 : ℤ)
    exact (((htx.mul_right hty).mul_right htx_inv).mul_right hty_inv)
  calc
    x * (t * y) * x⁻¹ * (t * y)⁻¹
        = x * t * y * x⁻¹ * (y⁻¹ * t⁻¹) := by
          rw [mul_inv_rev]
          group
    _ = t * x * y * x⁻¹ * (y⁻¹ * t⁻¹) := by rw [hxt.eq]
    _ = t * (x * y * x⁻¹ * y⁻¹) * t⁻¹ := by group
    _ = x * y * x⁻¹ * y⁻¹ := ht_comm.mul_inv_cancel

/-- A left-hand error factor commuting with the right entry does not change the
commutator when the retained commutator is central. -/
private theorem commutatorElement_mul_left_eq_of_commute_right_of_central
    {G : Type*} [Group G] {t x y : G}
    (hty : Commute t y) (hcen : ⁅x, y⁆ ∈ Subgroup.center G) :
    ⁅t * x, y⁆ = ⁅x, y⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  have ht_comm : Commute t (x * y * x⁻¹ * y⁻¹) := by
    simpa [commute_iff_eq, commutatorElement_def] using Subgroup.mem_center_iff.mp hcen t
  calc
    (t * x) * y * (t * x)⁻¹ * y⁻¹
        = t * x * y * (x⁻¹ * t⁻¹) * y⁻¹ := by
          rw [mul_inv_rev]
    _ = t * x * y * x⁻¹ * t⁻¹ * y⁻¹ := by group
    _ = t * x * y * x⁻¹ * (t⁻¹ * y⁻¹) := by group
    _ = t * x * y * x⁻¹ * (y⁻¹ * t⁻¹) := by rw [hty.inv_inv.eq]
    _ = t * (x * y * x⁻¹ * y⁻¹) * t⁻¹ := by group
    _ = x * y * x⁻¹ * y⁻¹ := ht_comm.mul_inv_cancel

/-- If `[x,y]` is central, inverting the left entry inverts the commutator. -/
private theorem commutatorElement_inv_left_of_central
    {G : Type*} [Group G] {x y : G}
    (hz : ⁅x, y⁆ ∈ Subgroup.center G) :
    ⁅x⁻¹, y⁆ = ⁅x, y⁆⁻¹ := by
  let c : G := ⁅x, y⁆
  have hc : c ∈ Subgroup.center G := by simpa [c] using hz
  have hxy : x * y = c * y * x := by
    dsimp [c]
    rw [commutatorElement_def]
    group
  have hyx : y * x = c⁻¹ * x * y := by
    calc
      y * x = c⁻¹ * (c * (y * x)) := by group
      _ = c⁻¹ * (c * y * x) := by group
      _ = c⁻¹ * (x * y) := by rw [hxy]
      _ = c⁻¹ * x * y := by group
  have hc_inv : c⁻¹ ∈ Subgroup.center G := (Subgroup.center G).inv_mem hc
  have hxc : x⁻¹ * c⁻¹ = c⁻¹ * x⁻¹ := Subgroup.mem_center_iff.mp hc_inv x⁻¹
  change ⁅x⁻¹, y⁆ = c⁻¹
  rw [commutatorElement_def]
  rw [inv_inv]
  change x⁻¹ * y * x * y⁻¹ = c⁻¹
  rw [show x⁻¹ * y * x * y⁻¹ = x⁻¹ * (y * x) * y⁻¹ by group, hyx]
  calc
    x⁻¹ * (c⁻¹ * x * y) * y⁻¹ = (x⁻¹ * c⁻¹) * x * (y * y⁻¹) := by group
    _ = (c⁻¹ * x⁻¹) * x * (y * y⁻¹) := by rw [hxc]
    _ = c⁻¹ := by group

/-- If `[x,y]` is central, inverting the right entry inverts the commutator. -/
private theorem commutatorElement_inv_right_of_central
    {G : Type*} [Group G] {x y : G}
    (hz : ⁅x, y⁆ ∈ Subgroup.center G) :
    ⁅x, y⁻¹⁆ = ⁅x, y⁆⁻¹ := by
  have hz' : ⁅y, x⁆ ∈ Subgroup.center G := by
    rw [← commutatorElement_inv]
    exact (Subgroup.center G).inv_mem hz
  have hleft := commutatorElement_inv_left_of_central hz'
  rw [← commutatorElement_inv (y⁻¹) x, hleft, commutatorElement_inv]

/-- Integer-exponent version of BG Lemma 4.2(a), left slot.

Public because Appendix E consumes it: BG's `(E.12)` computes with the eigenvalues `rᵢ`,
which are *integers*, so the natural-exponent form
`commutatorElement_pow_left_of_central` is not enough there. -/
theorem commutatorElement_zpow_left_of_central
    {G : Type*} [Group G] {x y : G}
    (hz : ⁅x, y⁆ ∈ Subgroup.center G) (n : ℤ) :
    ⁅x ^ n, y⁆ = ⁅x, y⁆ ^ n := by
  obtain ⟨m, rfl | rfl⟩ := n.eq_nat_or_neg
  · simpa [zpow_natCast] using commutatorElement_pow_left_of_central hz m
  · have hzm : ⁅x ^ m, y⁆ ∈ Subgroup.center G := by
      rw [commutatorElement_pow_left_of_central hz m]
      exact (Subgroup.center G).pow_mem hz m
    rw [zpow_neg, zpow_natCast, commutatorElement_inv_left_of_central hzm,
      commutatorElement_pow_left_of_central hz m, zpow_neg, zpow_natCast]

/-- Integer-exponent version of BG Lemma 4.2(a), right slot.

Public for the same reason as the left-slot form: BG's `(E.12)` needs integer exponents. -/
theorem commutatorElement_zpow_right_of_central
    {G : Type*} [Group G] {x y : G}
    (hz : ⁅x, y⁆ ∈ Subgroup.center G) (n : ℤ) :
    ⁅x, y ^ n⁆ = ⁅x, y⁆ ^ n := by
  obtain ⟨m, rfl | rfl⟩ := n.eq_nat_or_neg
  · simpa [zpow_natCast] using commutatorElement_pow_right_of_central hz m
  · have hzm : ⁅x, y ^ m⁆ ∈ Subgroup.center G := by
      rw [commutatorElement_pow_right_of_central hz m]
      exact (Subgroup.center G).pow_mem hz m
    rw [zpow_neg, zpow_natCast, commutatorElement_inv_right_of_central hzm,
      commutatorElement_pow_right_of_central hz m, zpow_neg, zpow_natCast]

/-- In a cyclic subgroup generated by an element of order `p`, equality of integer
powers is equality of the corresponding `ZMod p` coordinates.

Public because Appendix E's `(E.12)` reads its eigenvalue congruence
`rᵢ ≡ rᵢ₋₁ r (mod p)` off exactly this bridge, applied to a generator of the
order-`p` chain section `Hᵢ/Hᵢ₊₁`. -/
theorem zmod_eq_of_zpow_eq_of_order_prime
    {G : Type*} [Group G] {p : ℕ} [Fact p.Prime] {g : G}
    (hg : orderOf g = p) {m n : ℤ} (h : g ^ m = g ^ n) :
    (m : ZMod p) = (n : ZMod p) := by
  rw [ZMod.intCast_eq_intCast_iff]
  rwa [← hg, ← zpow_eq_zpow_iff_modEq]

/-- The converse coordinate bridge for an element of order `p`. -/
private theorem zpow_eq_of_zmod_eq_order_prime
    {G : Type*} [Group G] {p : ℕ} [Fact p.Prime] {g : G}
    (hg : orderOf g = p) {m n : ℤ} (h : (m : ZMod p) = (n : ZMod p)) :
    g ^ m = g ^ n := by
  rw [zpow_eq_zpow_iff_modEq, hg, ← ZMod.intCast_eq_intCast_iff]
  exact h

/-- The final congruence contradiction in Blackburn 4.16 Case B-2.

BG obtains `jk ≡ i` and `ij ≡ k`, with `i ≠ 0`, while the odd-order action gives
`j² ≠ 1`.  The two congruences imply `i * j² = i`, hence `j² = 1` in `ZMod p`. -/
private theorem blackburn_zmod_congruence_contradiction
    {p : ℕ} [Fact p.Prime] {i j k : ZMod p}
    (hi : i ≠ 0) (hj : j ^ 2 ≠ 1)
    (hjk : j * k = i) (hij : i * j = k) : False := by
  have hpow : i * j ^ 2 = i := by
    calc
      i * j ^ 2 = (i * j) * j := by ring
      _ = k * j := by rw [hij]
      _ = j * k := by rw [mul_comm]
      _ = i := hjk
  have hzero : i * (j ^ 2 - 1) = 0 := by
    rw [mul_sub, hpow, mul_one, sub_self]
  rcases mul_eq_zero.mp hzero with hi_zero | hj_zero
  · exact hi hi_zero
  · exact hj (sub_eq_zero.mp hj_zero)

/-- **BG Theorem 4.16** (Blackburn rank-two classification).

Let `p` be an odd prime, `R` a nonidentity finite `p`-group, and `A` a
`p'`-group of automorphisms of `R`.  If `r(R) ≤ 2`, `[R,A]=R`, and `|A|` is odd,
then `p > 3` and either `R` is abelian, or `R` is a central product
`R₁ ∘ R₂` where `R₁` is nonabelian of order `p^3` and exponent `p`, `R₂` is
cyclic, and `Ω₁(R₂)=R₁'`.

In Lean, because `R` is a `p`-group, BG's rank hypothesis `r(R) ≤ 2` is represented
as `pRank R p ≤ 2`; see the §4C comments above `scn3_empty_of_pRank_le_two`.
The proof splits into the small-`Ω₁` abelian branch and the large nonabelian
`S = Ω₁(R)` branch. In the latter branch the Blackburn B-2 computation produces
scalars `i,j,k` on `X`, `S/T`, and `T/Z`; the congruences `ij=k` and `jk=i`
contradict the odd-order action condition `j^2 ≠ 1`. -/
theorem blackburnRankTwoClassification
    {R : Type*} [Group R] [Finite R] [Nontrivial R]
    {p : ℕ} [Fact p.Prime] (hp_odd : Odd p) (hR : IsPGroup p R)
    {A : Type*} [Group A] [Finite A] {φ : A →* MulAut R}
    (hcop : Nat.Coprime (Nat.card A) (Nat.card R))
    (hrank : pRank R p ≤ 2)
    (hRA : OddOrder.Isaacs.Ch04.actionCommutator φ = ⊤)
    (hAodd : Odd (Nat.card A)) :
    3 < p ∧ (IsMulCommutative R ∨ BlackburnCentralProductCase p R) := by
  have hp3 : 3 < p := three_lt_of_odd_coprime_actionCommutator_top_rank_le_two
    hp_odd hR hcop hrank hRA hAodd
  refine ⟨hp3, ?_⟩
  by_cases hΩ : Nat.card (Omega R p 1) ≤ p ^ 2
  · exact Or.inl (isMulCommutative_of_omega1_card_le_prime_sq_blackburn
      hp_odd hR hp3 hcop hΩ hRA)
  obtain ⟨hΩ_card, hΩ_pow⟩ := omega1_large_card_eq_prime_cube_and_pow_eq_one hR hp3 hrank hΩ
  have hΩ_noncomm : ¬ IsMulCommutative (Omega R p 1) :=
    omega1_large_not_isMulCommutative hrank hΩ_card hΩ_pow
  have hΩ_exp : Monoid.exponent (Omega R p 1) = p :=
    exponent_eq_prime_of_card_prime_cube_and_pow_eq_one hΩ_card hΩ_pow
  have hΩ_center_card : Nat.card (Subgroup.center (Omega R p 1)) = p :=
    center_card_eq_prime_of_noncomm_card_prime_cube hΩ_card hΩ_noncomm
  have hΩ_extraspecial : IsExtraspecial p (Omega R p 1) :=
    isExtraspecial_of_noncomm_card_prime_cube_exp_prime hΩ_card hΩ_noncomm hΩ_exp
  by_cases hSR : ⁅(Omega R p 1 : Subgroup R), (⊤ : Subgroup R)⁆ ≤
      (Subgroup.center (Omega R p 1)).map (Omega R p 1).subtype
  · exact Or.inr (blackburnCentralProductCase_of_omega1_commutator_le_center
      hp_odd hR hΩ_card hΩ_pow hΩ_noncomm hΩ_exp hΩ_extraspecial hSR)
  · have hT_facts := blackburn_noncentral_commutator_facts hR hΩ_card hΩ_extraspecial hSR
    have hT_elem := blackburn_noncentral_commutator_isElementaryAbelian hΩ_pow hT_facts
    have hT_quot_cards :=
      blackburn_noncentral_commutator_quotient_cards hΩ_card hΩ_extraspecial hT_facts
    have hRT_centralizer_card :=
      blackburn_noncentral_centralizer_quotient_card_eq_prime hR hT_facts hT_elem
    have hSC_top :=
      blackburn_noncentral_omega1_sup_centralizer_eq_top hR hT_facts hT_elem
    have hCDT_relations := blackburn_noncentral_centralizer_relations hT_facts hT_elem
    have hΩD_eq_T :=
      blackburn_noncentral_omega1_centralizer_eq_commutator hrank hT_facts hT_elem
    have hTC_image :=
      blackburn_noncentral_commutator_image_relations hT_facts hT_elem hT_quot_cards
    obtain ⟨hΩC_eq_center, hC_cyclic, hΩC_eq_comm⟩ :=
      blackburn_omega1_centralizer_eq_center_cyclic_and_commutator
        hp_odd hR hΩ_pow hΩ_extraspecial
    have hCD_norms := blackburn_noncentral_centralizer_normalities (R := R) (p := p)
    have hT_norms := blackburn_noncentral_commutator_normalities hT_elem
    have hD_quot_ab :=
      blackburn_noncentral_centralizer_quotient_commutative hT_facts hT_elem
    obtain ⟨X, hC_le_X, hX_inv, hX_omega, hX_inf_T, hX_sup_T⟩ :=
      blackburn_noncentral_exists_centralizer_quotient_complement
        (φ := φ) hcop hT_facts hT_elem hD_quot_ab
    have hX_cyclic :=
      blackburn_noncentral_centralizer_complement_isCyclic
        hp_odd hR hΩ_extraspecial hT_facts hT_elem hΩD_eq_T hΩC_eq_center hX_inf_T
    have hSX_top :=
      blackburn_noncentral_omega1_sup_centralizer_complement_eq_top
        hR hT_facts hT_elem hC_le_X hX_sup_T
    let S : Subgroup R := Omega R p 1
    let T : Subgroup R := ⁅S, (⊤ : Subgroup R)⁆
    let C : Subgroup R := Subgroup.centralizer (S : Set R)
    let D : Subgroup R := Subgroup.centralizer (T : Set R)
    obtain ⟨xX, hxX_gen⟩ := isCyclic_iff_exists_zpowers_eq_top.mp hX_cyclic
    let x : R := ((xX : X) : D)
    have hX_map_eq_zpowers : X.map D.subtype = Subgroup.zpowers x := by
      apply le_antisymm
      · rintro r ⟨d, hdX, rfl⟩
        have hd_top : (⟨d, hdX⟩ : X) ∈ (⊤ : Subgroup X) := Subgroup.mem_top _
        rw [← hxX_gen] at hd_top
        obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hd_top
        rw [Subgroup.mem_zpowers_iff]
        refine ⟨n, ?_⟩
        simpa [x] using congrArg (fun u : X => ((u : D) : R)) hn
      · intro r hr
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hr
        refine ⟨(xX : D) ^ n, zpow_mem xX.2 n, ?_⟩
        simp [x]
    let Z : Subgroup R := (Subgroup.center S).map S.subtype
    have hSX_top' : S ⊔ X.map D.subtype = ⊤ := by
      simpa [S, T, D] using hSX_top
    have hSX_zpowers_top : S ⊔ Subgroup.zpowers x = ⊤ := by
      simpa [hX_map_eq_zpowers] using hSX_top'
    have hXmap_comm : IsMulCommutative (X.map D.subtype) := by
      rw [hX_map_eq_zpowers]
      infer_instance
    have hX_comm_not_le_Z : ¬ ⁅X.map D.subtype, S⁆ ≤ Z := by
      simpa [S, Z] using
        (blackburn_noncentral_complement_commutator_not_le_center
          (R := R) (p := p) (X := X.map D.subtype)
          hΩ_extraspecial hSR (by simpa [S] using hSX_top') hXmap_comm)
    have hxS_comm_not_le_Z : ¬ ⁅Subgroup.zpowers x, S⁆ ≤ Z := by
      simpa [hX_map_eq_zpowers] using hX_comm_not_le_Z
    have hS_normal : S.Normal := by
      dsimp [S]
      infer_instance
    have hZ_eq_comm : Z = ⁅S, S⁆ := by
      dsimp [S, Z]
      rw [← hΩ_extraspecial.commutator_eq_center, Subgroup.map_subtype_commutator]
    have hZ_normal : Z.Normal := by
      rw [hZ_eq_comm]
      infer_instance
    obtain ⟨y, hyS, hxyZ⟩ :=
      exists_commutator_generator_not_mem_of_zpowers_commutator_not_le
        (S := S) (Z := Z) (x := x) hxS_comm_not_le_Z
    have hxD : x ∈ D := by
      dsimp [x]
      exact ((xX : X) : D).2
    have hy_not_T : y ∉ T := by
      intro hyT
      have hcent := (Subgroup.mem_centralizer_iff.mp hxD) y hyT
      have hcomm_one : ⁅x, y⁆ = 1 := by
        exact commutatorElement_eq_one_iff_commute.mpr
          (show Commute x y from hcent.symm)
      exact hxyZ (by rw [hcomm_one]; exact Z.one_mem)
    have hxyT : ⁅x, y⁆ ∈ T := by
      dsimp [T]
      have hmem : ⁅x, y⁆ ∈ ⁅(⊤ : Subgroup R), S⁆ :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top x) hyS
      rwa [Subgroup.commutator_comm] at hmem
    have hD_ne_top : D ≠ ⊤ := by
      intro hD_top
      have hS_le_D : S ≤ D := by
        intro s hs
        rw [hD_top]
        exact Subgroup.mem_top s
      exact (blackburn_noncentral_omega1_not_le_centralizer (R := R) (p := p) hT_facts)
        (by simpa [S, T, D] using hS_le_D)
    have hT_le_D : T ≤ D := by
      simpa [S, T, D, Z] using hCDT_relations.2.1
    have hD_inv : IsAInvariant φ D := by
      simpa [S, T, D] using
        (blackburn_noncentral_operator_invariances (p := p) (φ := φ)).2.2.2
    obtain ⟨a, s0, hs0S, hs0T⟩ :=
      exists_operator_moving_omega1_mod_commutator
        (R := R) (p := p) (φ := φ) (S := S) (T := T) (D := D) hT_le_D
        (by simpa [S, T, D] using hSC_top) hD_inv hD_ne_top hRA
    let z : R := ⁅x, y⁆
    have hzT : z ∈ T := by
      simpa [z] using hxyT
    have hzZ : z ∉ Z := by
      simpa [z] using hxyZ
    obtain ⟨hywZ, hyw_ne⟩ :=
      blackburn_noncentral_second_commutator_mem_center_and_ne_one
        (R := R) (p := p) hΩ_extraspecial hT_facts hT_elem hT_quot_cards
        (y := y) (z := z) (by simpa [S] using hyS)
        (by simpa [S, T] using hy_not_T)
        (by simpa [S, T, z] using hzT)
        (by simpa [S, Z, z] using hzZ)
    let w : R := ⁅y, z⁆
    have hwZ : w ∈ Z := by
      simpa [S, Z, w] using hywZ
    have hw_ne : w ≠ 1 := by
      simpa [w] using hyw_ne
    have hC_le_D : C ≤ D := by
      simpa [S, T, C, D, Z] using hCDT_relations.1
    have hTC_eq_Z : T ⊓ C = Z := by
      simpa [S, T, C, D, Z] using hCDT_relations.2.2
    have hCsub_le_X : C.subgroupOf D ≤ X := by
      simpa [S, T, C, D] using hC_le_X
    have hZ_le_zpowers : Z ≤ Subgroup.zpowers x := by
      intro r hrZ
      have hrC : r ∈ C := by
        have hrTC : r ∈ T ⊓ C := by
          rw [hTC_eq_Z]
          exact hrZ
        exact hrTC.2
      have hrD : r ∈ D := hC_le_D hrC
      have hrCsub : (⟨r, hrD⟩ : D) ∈ C.subgroupOf D := by
        exact hrC
      have hrXmap : r ∈ X.map D.subtype :=
        ⟨⟨r, hrD⟩, hCsub_le_X hrCsub, rfl⟩
      simpa [hX_map_eq_zpowers] using hrXmap
    have hw_zpowers : w ∈ Subgroup.zpowers x := hZ_le_zpowers hwZ
    obtain ⟨mW, hmW⟩ := Subgroup.mem_zpowers_iff.mp hw_zpowers
    have hZ_le_S : Z ≤ S := by
      dsimp [Z]
      exact Subgroup.map_subtype_le _
    have hwS : w ∈ S := hZ_le_S hwZ
    have hwp : w ^ p = 1 := by
      have hwpS := hΩ_pow ⟨w, hwS⟩
      exact congrArg Subtype.val hwpS
    have hw_order : orderOf w = p := orderOf_eq_prime hwp hw_ne
    have hX_inv' : IsAInvariant hD_inv.restrict X := by
      simpa [S, T, D] using hX_inv
    have hφx_Xmap : (φ a) x ∈ X.map D.subtype := by
      refine ⟨(hD_inv.restrict a) (xX : D), hX_inv'.smul_mem a xX.2, ?_⟩
      simp [x, IsAInvariant.restrict_apply_val]
    obtain ⟨iℤ, hiℤ_eq⟩ :=
      Subgroup.mem_zpowers_iff.mp (by simpa [hX_map_eq_zpowers] using hφx_Xmap)
    have hφx_eq : (φ a) x = x ^ iℤ := hiℤ_eq.symm
    have hInv := blackburn_noncentral_operator_invariances (R := R) (p := p) (φ := φ)
    have hS_inv : IsAInvariant φ S := by
      simpa [S, T, C, D] using hInv.1
    have hT_inv : IsAInvariant φ T := by
      simpa [S, T, C, D] using hInv.2.1
    have hZ_inv : IsAInvariant φ Z := by
      rw [hZ_eq_comm]
      exact hS_inv.commutator hS_inv
    let Tsub : Subgroup S := T.subgroupOf S
    have hTsub_normal : Tsub.Normal := by
      simpa [S, T, Z, Tsub] using hT_norms.2.1
    let yS : S := ⟨y, hyS⟩
    let qy : S ⧸ Tsub := QuotientGroup.mk' Tsub yS
    have hqy_ne : qy ≠ 1 := by
      intro hqy
      have hyTsub : yS ∈ Tsub := (QuotientGroup.eq_one_iff yS).mp hqy
      exact hy_not_T (Subgroup.mem_subgroupOf.mp hyTsub)
    have hST_card : Nat.card (S ⧸ Tsub) = p := by
      simpa [S, T, Z, Tsub] using hT_quot_cards.1
    have hqy_top : Subgroup.zpowers qy = ⊤ :=
      zpowers_eq_top_of_prime_card hST_card hqy_ne
    let φyS : S := ⟨(φ a) y, hS_inv.smul_mem a hyS⟩
    have hφy_mem : (QuotientGroup.mk' Tsub φyS : S ⧸ Tsub) ∈ Subgroup.zpowers qy := by
      rw [hqy_top]
      exact Subgroup.mem_top _
    obtain ⟨jℤ, hjℤ_eq⟩ := Subgroup.mem_zpowers_iff.mp hφy_mem
    have hφy_quot_eq : (QuotientGroup.mk' Tsub φyS : S ⧸ Tsub) = qy ^ jℤ :=
      hjℤ_eq.symm
    let Zsub : Subgroup T := Z.subgroupOf T
    have hZsub_normal : Zsub.Normal := by
      simpa [S, T, Z, Zsub] using hT_norms.2.2
    let zT : T := ⟨z, hzT⟩
    let qz : T ⧸ Zsub := QuotientGroup.mk' Zsub zT
    have hqz_ne : qz ≠ 1 := by
      intro hqz
      have hzZsub : zT ∈ Zsub := (QuotientGroup.eq_one_iff zT).mp hqz
      exact hzZ (Subgroup.mem_subgroupOf.mp hzZsub)
    have hTZ_card : Nat.card (T ⧸ Zsub) = p := by
      simpa [S, T, Z, Zsub] using hT_quot_cards.2
    have hqz_top : Subgroup.zpowers qz = ⊤ :=
      zpowers_eq_top_of_prime_card hTZ_card hqz_ne
    let φzT : T := ⟨(φ a) z, hT_inv.smul_mem a hzT⟩
    have hφz_mem : (QuotientGroup.mk' Zsub φzT : T ⧸ Zsub) ∈ Subgroup.zpowers qz := by
      rw [hqz_top]
      exact Subgroup.mem_top _
    obtain ⟨kℤ, hkℤ_eq⟩ := Subgroup.mem_zpowers_iff.mp hφz_mem
    have hφz_quot_eq : (QuotientGroup.mk' Zsub φzT : T ⧸ Zsub) = qz ^ kℤ :=
      hkℤ_eq.symm
    have hφw_i : (φ a) w = w ^ iℤ := by
      calc
        (φ a) w = (φ a) (x ^ mW) := by rw [hmW]
        _ = ((φ a) x) ^ mW := by rw [map_zpow]
        _ = (x ^ iℤ) ^ mW := by rw [hφx_eq]
        _ = x ^ (iℤ * mW) := by rw [zpow_mul]
        _ = x ^ (mW * iℤ) := by rw [mul_comm]
        _ = (x ^ mW) ^ iℤ := by rw [zpow_mul]
        _ = w ^ iℤ := by rw [hmW]
    have hi_ne_zero : (iℤ : ZMod p) ≠ 0 := by
      intro hi0
      have hwi_one : w ^ iℤ = 1 := by
        have hzero : ((iℤ : ℤ) : ZMod p) = ((0 : ℤ) : ZMod p) := by
          simpa using hi0
        have hpow :=
          zpow_eq_of_zmod_eq_order_prime hw_order (m := iℤ) (n := 0) hzero
        simpa using hpow
      have hφw_one : (φ a) w = 1 := by
        rw [hφw_i, hwi_one]
      have hφw_eq : (φ a) w = (φ a) 1 := by
        simpa using hφw_one
      exact hw_ne ((φ a).injective hφw_eq)
    have hφy_mod_T : (φ a) y * (y ^ jℤ)⁻¹ ∈ T := by
      have hqy_pow : qy ^ jℤ = QuotientGroup.mk' Tsub (yS ^ jℤ) := by
        dsimp [qy]
      have hquot_eq :
          (QuotientGroup.mk' Tsub φyS : S ⧸ Tsub) =
            QuotientGroup.mk' Tsub (yS ^ jℤ) := by
        rw [hφy_quot_eq, hqy_pow]
      have hdiv : φyS / (yS ^ jℤ) ∈ Tsub :=
        QuotientGroup.eq_iff_div_mem.mp hquot_eq
      have hdivR : ((φ a) y) * ((y ^ jℤ)⁻¹) ∈ T := by
        simpa [div_eq_mul_inv, φyS, yS] using Subgroup.mem_subgroupOf.mp hdiv
      simpa using hdivR
    have hφz_mod_Z : (φ a) z * (z ^ kℤ)⁻¹ ∈ Z := by
      have hqz_pow : qz ^ kℤ = QuotientGroup.mk' Zsub (zT ^ kℤ) := by
        dsimp [qz]
      have hquot_eq :
          (QuotientGroup.mk' Zsub φzT : T ⧸ Zsub) =
            QuotientGroup.mk' Zsub (zT ^ kℤ) := by
        rw [hφz_quot_eq, hqz_pow]
      have hdiv : φzT / (zT ^ kℤ) ∈ Zsub :=
        QuotientGroup.eq_iff_div_mem.mp hquot_eq
      have hdivR : ((φ a) z) * ((z ^ kℤ)⁻¹) ∈ Z := by
        simpa [div_eq_mul_inv, φzT, zT] using Subgroup.mem_subgroupOf.mp hdiv
      simpa using hdivR
    have hTsub_inv : IsAInvariant hS_inv.restrict Tsub :=
      isAInvariant_subgroupOf_restrict hS_inv hT_inv
    let φST : A →* MulAut (S ⧸ Tsub) := quotientMulAutHom hTsub_inv
    have hφST_qy : (φST a) qy = qy ^ jℤ := by
      have hres : (hS_inv.restrict a) yS = φyS :=
        Subtype.ext (IsAInvariant.restrict_apply_val hS_inv a yS)
      simpa [φST, qy, hres] using hφy_quot_eq
    have hφST_ne_one : φST a ≠ 1 := by
      intro htriv
      let s0S : S := ⟨s0, hs0S⟩
      let φs0S : S := ⟨(φ a) s0, hS_inv.smul_mem a hs0S⟩
      have hquot_s0 :
          (QuotientGroup.mk' Tsub φs0S : S ⧸ Tsub) =
            QuotientGroup.mk' Tsub s0S := by
        have happ := congrArg
          (fun σ : MulAut (S ⧸ Tsub) => σ (QuotientGroup.mk' Tsub s0S)) htriv
        have hres : (hS_inv.restrict a) s0S = φs0S :=
          Subtype.ext (IsAInvariant.restrict_apply_val hS_inv a s0S)
        simpa [φST, hres] using happ
      have hdiv : φs0S / s0S ∈ Tsub := QuotientGroup.eq_iff_div_mem.mp hquot_s0
      exact hs0T (by
        simpa [div_eq_mul_inv, s0S, φs0S] using Subgroup.mem_subgroupOf.mp hdiv)
    have hqy_pow_p : qy ^ p = 1 := by
      simpa [hST_card] using (pow_card_eq_one' (G := S ⧸ Tsub) (x := qy))
    have hqy_order : orderOf qy = p := orderOf_eq_prime hqy_pow_p hqy_ne
    have hj_ne_one : (jℤ : ZMod p) ≠ 1 := by
      intro hj_one
      have hpow_one : qy ^ jℤ = qy := by
        have hcoord : ((jℤ : ℤ) : ZMod p) = ((1 : ℤ) : ZMod p) := by
          simpa using hj_one
        have hpow :=
          zpow_eq_of_zmod_eq_order_prime hqy_order (m := jℤ) (n := 1) hcoord
        simpa using hpow
      have hfix : (φST a) qy = qy := by
        rw [hφST_qy, hpow_one]
      exact hφST_ne_one (mulAut_eq_one_of_zpowers_eq_top_of_apply_eq hqy_top hfix)
    have hj_sq_ne_one : ((jℤ : ZMod p) ^ 2) ≠ 1 := by
      intro hj_sq
      have hsq_fix : ((φST a) ^ 2) qy = qy := by
        calc
          ((φST a) ^ 2) qy = (φST a) ((φST a) qy) := by simp [pow_two]
          _ = (φST a) (qy ^ jℤ) := by rw [hφST_qy]
          _ = ((φST a) qy) ^ jℤ := by rw [map_zpow]
          _ = (qy ^ jℤ) ^ jℤ := by rw [hφST_qy]
          _ = qy ^ (jℤ * jℤ) := by rw [zpow_mul]
          _ = qy ^ (1 : ℤ) := by
            have hcoord : (((jℤ * jℤ : ℤ) : ZMod p) = ((1 : ℤ) : ZMod p)) := by
              simpa [pow_two] using hj_sq
            exact zpow_eq_of_zmod_eq_order_prime hqy_order
              (m := jℤ * jℤ) (n := 1) hcoord
          _ = qy := by simp
      have hsq_one : (φST a) ^ 2 = 1 :=
        mulAut_eq_one_of_zpowers_eq_top_of_apply_eq hqy_top hsq_fix
      have horder_two : orderOf (φST a) = 2 := by
        exact orderOf_eq_prime (by simpa [pow_two] using hsq_one) hφST_ne_one
      have htwo_dvd_A : 2 ∣ Nat.card A := by
        have horder_dvd_a : orderOf (φST a) ∣ orderOf a := orderOf_map_dvd φST a
        have ha_dvd_card : orderOf a ∣ Nat.card A := orderOf_dvd_natCard a
        simpa [horder_two] using horder_dvd_a.trans ha_dvd_card
      exact (Nat.not_even_iff_odd.mpr hAodd) (even_iff_two_dvd.mpr htwo_dvd_A)
    have hT_le_S : T ≤ S := by
      simpa [S, T, Z] using hT_facts.2.1.le
    have hqz_pow_p : qz ^ p = 1 := by
      simpa [hTZ_card] using (pow_card_eq_one' (G := T ⧸ Zsub) (x := qz))
    have hqz_order : orderOf qz = p := orderOf_eq_prime hqz_pow_p hqz_ne
    let qRZ : R →* R ⧸ Z := QuotientGroup.mk' Z
    have hz_center_q : qRZ z ∈ Subgroup.center (R ⧸ Z) := by
      rw [Subgroup.mem_center_iff]
      intro u
      obtain ⟨r, rfl⟩ := QuotientGroup.mk'_surjective Z u
      have hr_top : r ∈ S ⊔ Subgroup.zpowers x := by
        rw [hSX_zpowers_top]
        exact Subgroup.mem_top r
      obtain ⟨s, hsS, xn, hxn, hr⟩ :=
        (Subgroup.mem_sup_of_normal_left (s := S) (t := Subgroup.zpowers x) (x := r)).mp
          hr_top
      have hsz : Commute (qRZ s) (qRZ z) := by
        have hzsZ : ⁅z, s⁆ ∈ Z := by
          rw [hZ_eq_comm]
          exact Subgroup.commutator_mem_commutator (hT_le_S hzT) hsS
        exact (commute_quotient_of_commutator_mem hzsZ).symm
      have hxnz : Commute (qRZ xn) (qRZ z) := by
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxn
        have hzx : Commute z x := Subgroup.mem_centralizer_iff.mp hxD z hzT
        exact ((hzx.zpow_right n).map qRZ).symm
      change Commute (qRZ r) (qRZ z)
      rw [← hr]
      simpa [qRZ] using hsz.mul_left hxnz
    let tY : R := (φ a) y * (y ^ jℤ)⁻¹
    have htYT : tY ∈ T := by
      simpa [tY] using hφy_mod_T
    have hφy_decomp : (φ a) y = tY * y ^ jℤ := by
      dsimp [tY]
      group
    let cZ : R := (φ a) z * (z ^ kℤ)⁻¹
    have hcZZ : cZ ∈ Z := by
      simpa [cZ] using hφz_mod_Z
    have hφz_decomp : (φ a) z = cZ * z ^ kℤ := by
      dsimp [cZ]
      group
    have hφz_mod_Z_ij : (φ a) z * (z ^ (iℤ * jℤ))⁻¹ ∈ Z := by
      have hxpow_t_comm : Commute (qRZ (x ^ iℤ)) (qRZ tY) := by
        have hxt : Commute (x ^ iℤ) tY := by
          have htx : Commute tY x := Subgroup.mem_centralizer_iff.mp hxD tY htYT
          exact htx.symm.zpow_left iℤ
        exact hxt.map qRZ
      have hyj_t_comm : Commute (qRZ (y ^ jℤ)) (qRZ tY) := by
        have hcomm_mem : ⁅y ^ jℤ, tY⁆ ∈ Z := by
          rw [hZ_eq_comm]
          exact Subgroup.commutator_mem_commutator (zpow_mem hyS jℤ)
            (hT_le_S htYT)
        exact commute_quotient_of_commutator_mem hcomm_mem
      have hxy_q_eq : ⁅qRZ x, qRZ y⁆ = qRZ z := by
        change ⁅qRZ x, qRZ y⁆ = qRZ ⁅x, y⁆
        exact (map_commutatorElement (f := qRZ) (g₁ := x) (g₂ := y)).symm
      have hxy_q_center : ⁅qRZ x, qRZ y⁆ ∈ Subgroup.center (R ⧸ Z) := by
        rw [hxy_q_eq]
        exact hz_center_q
      have hxy_pow_q :
          ⁅(qRZ x) ^ iℤ, (qRZ y) ^ jℤ⁆ = (qRZ z) ^ (iℤ * jℤ) := by
        have hleft_center : ⁅(qRZ x) ^ iℤ, qRZ y⁆ ∈ Subgroup.center (R ⧸ Z) := by
          rw [commutatorElement_zpow_left_of_central hxy_q_center iℤ]
          exact (Subgroup.center (R ⧸ Z)).zpow_mem hxy_q_center iℤ
        calc
          ⁅(qRZ x) ^ iℤ, (qRZ y) ^ jℤ⁆
              = ⁅(qRZ x) ^ iℤ, qRZ y⁆ ^ jℤ := by
                rw [commutatorElement_zpow_right_of_central hleft_center jℤ]
          _ = (⁅qRZ x, qRZ y⁆ ^ iℤ) ^ jℤ := by
                rw [commutatorElement_zpow_left_of_central hxy_q_center iℤ]
          _ = ⁅qRZ x, qRZ y⁆ ^ (iℤ * jℤ) := by rw [zpow_mul]
          _ = (qRZ z) ^ (iℤ * jℤ) := by rw [hxy_q_eq]
      have hφz_qcalc : qRZ ((φ a) z) = (qRZ z) ^ (iℤ * jℤ) := by
        calc
          qRZ ((φ a) z) = qRZ (⁅(φ a) x, (φ a) y⁆) := by
            dsimp [z]
            rw [map_commutatorElement]
          _ = ⁅qRZ ((φ a) x), qRZ ((φ a) y)⁆ := by
            rw [map_commutatorElement]
          _ = ⁅qRZ (x ^ iℤ), qRZ (tY * y ^ jℤ)⁆ := by
            rw [hφx_eq, hφy_decomp]
          _ = ⁅qRZ (x ^ iℤ), qRZ tY * qRZ (y ^ jℤ)⁆ := by
            simp [qRZ]
          _ = ⁅qRZ (x ^ iℤ), qRZ (y ^ jℤ)⁆ := by
            exact commutatorElement_mul_right_eq_of_commute hxpow_t_comm hyj_t_comm
          _ = (qRZ z) ^ (iℤ * jℤ) := by
            simpa [map_zpow] using hxy_pow_q
      have hquot : qRZ ((φ a) z) = qRZ (z ^ (iℤ * jℤ)) := by
        simpa [map_zpow] using hφz_qcalc
      simpa [div_eq_mul_inv] using QuotientGroup.eq_iff_div_mem.mp hquot
    have hφz_quot_eq_ij :
        (QuotientGroup.mk' Zsub φzT : T ⧸ Zsub) = qz ^ (iℤ * jℤ) := by
      have hqz_pow :
          qz ^ (iℤ * jℤ) = QuotientGroup.mk' Zsub (zT ^ (iℤ * jℤ)) := by
        dsimp [qz]
      rw [hqz_pow]
      apply QuotientGroup.eq_iff_div_mem.mpr
      change ((φzT / zT ^ (iℤ * jℤ) : T) : R) ∈ Z
      simpa [div_eq_mul_inv, φzT, zT] using hφz_mod_Z_ij
    have hij : (iℤ : ZMod p) * (jℤ : ZMod p) = (kℤ : ZMod p) := by
      have hpows : qz ^ kℤ = qz ^ (iℤ * jℤ) := by
        rw [← hφz_quot_eq, hφz_quot_eq_ij]
      have hcoord := zmod_eq_of_zpow_eq_of_order_prime hqz_order hpows
      simpa [Int.cast_mul] using hcoord.symm
    have memZ_centerS : ∀ {u : R} (huS : u ∈ S), u ∈ Z →
        (⟨u, huS⟩ : S) ∈ Subgroup.center S := by
      intro u huS huZ
      dsimp [Z] at huZ
      rcases huZ with ⟨uS, huS_center, hu_eq⟩
      have hEq : (⟨u, huS⟩ : S) = uS := by
        ext
        simpa using hu_eq.symm
      simpa [hEq] using huS_center
    have hw_center_S : (⟨w, hwS⟩ : S) ∈ Subgroup.center S :=
      memZ_centerS hwS hwZ
    have hw_center : w ∈ Subgroup.center R := by
      rw [Subgroup.mem_center_iff]
      intro r
      have hr_top : r ∈ S ⊔ Subgroup.zpowers x := by
        rw [hSX_zpowers_top]
        exact Subgroup.mem_top r
      obtain ⟨s, hsS, xn, hxn, hr⟩ :=
        (Subgroup.mem_sup_of_normal_left (s := S) (t := Subgroup.zpowers x) (x := r)).mp
          hr_top
      have hsw : Commute s w := by
        exact congrArg Subtype.val
          (Subgroup.mem_center_iff.mp hw_center_S ⟨s, hsS⟩)
      have hxnw : Commute xn w := by
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxn
        simpa [hmW] using (Commute.zpow_zpow_self (a := x) (m := n) (n := mW))
      change Commute r w
      rw [← hr]
      simpa using hsw.mul_left hxnw
    have hcZS : cZ ∈ S := hZ_le_S hcZZ
    have hcZ_center_S : (⟨cZ, hcZS⟩ : S) ∈ Subgroup.center S :=
      memZ_centerS hcZS hcZZ
    have htyS : tY ∈ S := hT_le_S htYT
    have hyjS : y ^ jℤ ∈ S := zpow_mem hyS jℤ
    have hzkT : z ^ kℤ ∈ T := zpow_mem hzT kℤ
    have hzkS : z ^ kℤ ∈ S := hT_le_S hzkT
    have hleft_cZ_comm : Commute (tY * y ^ jℤ) cZ := by
      have hleftS : tY * y ^ jℤ ∈ S := S.mul_mem htyS hyjS
      have hcomm : Commute (tY * y ^ jℤ) cZ := by
        exact congrArg Subtype.val
          (Subgroup.mem_center_iff.mp hcZ_center_S ⟨tY * y ^ jℤ, hleftS⟩)
      exact hcomm
    have hzk_cZ_comm : Commute (z ^ kℤ) cZ := by
      have hcomm : Commute (z ^ kℤ) cZ := by
        exact congrArg Subtype.val
          (Subgroup.mem_center_iff.mp hcZ_center_S ⟨z ^ kℤ, hzkS⟩)
      exact hcomm
    have htY_zk_comm : Commute tY (z ^ kℤ) := by
      exact congrArg Subtype.val (hT_elem.comm ⟨tY, htYT⟩ ⟨z ^ kℤ, hzkT⟩)
    have hyz_center : ⁅y, z⁆ ∈ Subgroup.center R := by
      simpa [w] using hw_center
    have hyj_zk_eq : ⁅y ^ jℤ, z ^ kℤ⁆ = w ^ (jℤ * kℤ) := by
      have hleft_center : ⁅y ^ jℤ, z⁆ ∈ Subgroup.center R := by
        rw [commutatorElement_zpow_left_of_central hyz_center jℤ]
        exact (Subgroup.center R).zpow_mem hyz_center jℤ
      calc
        ⁅y ^ jℤ, z ^ kℤ⁆ = ⁅y ^ jℤ, z⁆ ^ kℤ := by
          rw [commutatorElement_zpow_right_of_central hleft_center kℤ]
        _ = (⁅y, z⁆ ^ jℤ) ^ kℤ := by
          rw [commutatorElement_zpow_left_of_central hyz_center jℤ]
        _ = ⁅y, z⁆ ^ (jℤ * kℤ) := by rw [zpow_mul]
        _ = w ^ (jℤ * kℤ) := by rfl
    have hyj_zk_center : ⁅y ^ jℤ, z ^ kℤ⁆ ∈ Subgroup.center R := by
      rw [hyj_zk_eq]
      exact (Subgroup.center R).zpow_mem hw_center (jℤ * kℤ)
    have hφw_jk : (φ a) w = w ^ (jℤ * kℤ) := by
      calc
        (φ a) w = ⁅(φ a) y, (φ a) z⁆ := by
          dsimp [w]
          rw [map_commutatorElement]
        _ = ⁅tY * y ^ jℤ, cZ * z ^ kℤ⁆ := by
          rw [hφy_decomp, hφz_decomp]
        _ = ⁅tY * y ^ jℤ, z ^ kℤ⁆ := by
          exact commutatorElement_mul_right_eq_of_commute hleft_cZ_comm hzk_cZ_comm
        _ = ⁅y ^ jℤ, z ^ kℤ⁆ := by
          exact commutatorElement_mul_left_eq_of_commute_right_of_central
            htY_zk_comm hyj_zk_center
        _ = w ^ (jℤ * kℤ) := hyj_zk_eq
    have hjk : (jℤ : ZMod p) * (kℤ : ZMod p) = (iℤ : ZMod p) := by
      have hpows : w ^ iℤ = w ^ (jℤ * kℤ) := by
        rw [← hφw_i, hφw_jk]
      have hcoord := zmod_eq_of_zpow_eq_of_order_prime hw_order hpows
      simpa [Int.cast_mul] using hcoord.symm
    exact False.elim (blackburn_zmod_congruence_contradiction
      (p := p) (i := (iℤ : ZMod p)) (j := (jℤ : ZMod p)) (k := (kℤ : ZMod p))
      hi_ne_zero hj_sq_ne_one hjk hij)

end BlackburnClassification

end OddOrder.BG.Ch1.S04


