-- Prove2me | Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S12_Lemma1218
-- name    : OddOrder_BG_Ch3_MaximalSubgroups_S12_Lemma1218
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T07:21:00.728705+00:00
-- url     : https://prove2.me/theorems/63fd04ec-4a20-4182-9cd5-014d943e1fb3
-- title:
--   BG §12: Lemma 12.18, $\tau_1$-elements against $M_\alpha$
-- statement:
--   Formalizes Lemma 12.18 of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, §12: for $p\in\tau_1(M)$, $P\in\mathcal{E}_p^1(M)$ and a nontrivial $P$-invariant $q$-subgroup $Q$ of $M$ with $C_Q(P)=1$ and $\mathcal{M}(N_G(Q))\ne\{M\}$: (a) $M_\alpha\ne 1$ and $q\notin\alpha(M)$ give $C_{M_\alpha}(P)\ne 1$ and $C_{M_\alpha}(PQ)=1$; (b) if $Q$ is Sylow then $\alpha(M)=\beta(M)$.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 10 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch3_MaximalSubgroups/S12_Lemma1218.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch3_MaximalSubgroups/S12_Lemma1218.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S12_E

namespace OddOrder.BG.Ch3.S12

open OddOrder.GroupTheory

open OddOrder.Isaacs

open OddOrder.BG.Ch1.S06 (actionCommutator_conj_map_subtype fixedPointsOfMulAut_conj_map_subtype)

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **BB4 — degenerate case of BG Theorem 10.2(d)**: if `M_α = 1` then `M'` is nilpotent.
By `S10.derived_quotient_Malpha_le_fitting`, `(M/M_α)' ≤ F(M/M_α)` unconditionally; with
`M_α = 1` the quotient is by `⊥`, so `M' ≤ F(M)`-type nilpotency transports back to `↥M`
along `QuotientGroup.quotientBot`. Used contrapositively in Lemma 12.18(b) to produce
`M_α ≠ 1` from the non-nilpotence of `M'`. -/
theorem isNilpotent_derived_of_Malpha_eq_bot [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) (hα : S10.Malpha M = ⊥) :
    Group.IsNilpotent ↥(derivedInG M) := by
  classical
  have h102 := S10.derived_quotient_Malpha_le_fitting hG hM
  -- the quotient is by `⊥`, so it is isomorphic to `↥M` itself.
  have hbot : (S10.Malpha M).subgroupOf M = ⊥ := by rw [hα, Subgroup.bot_subgroupOf]
  have e2 : (↥M ⧸ (S10.Malpha M).subgroupOf M) ≃* ↥M :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  -- the commutator of the quotient is nilpotent: subgroup of the nilpotent Fitting subgroup.
  have hnil1 : Group.IsNilpotent ↥(commutator (↥M ⧸ (S10.Malpha M).subgroupOf M)) :=
    Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe h102)
  have hcomm_eq :
      (commutator (↥M ⧸ (S10.Malpha M).subgroupOf M)).map e2.toMonoidHom = commutator ↥M := by
    rw [_root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ e2.surjective, ← _root_.commutator_def]
  have hnil2 : Group.IsNilpotent ↥(commutator ↥M) := by
    rw [← hcomm_eq]
    exact Group.nilpotent_of_mulEquiv (Subgroup.equivMapOfInjective _ _ e2.injective)
  -- `derivedInG M = (commutator ↥M).map M.subtype`.
  exact Group.nilpotent_of_mulEquiv (Subgroup.equivMapOfInjective _ _ M.subtype_injective)

section Helpers

/-- In a finite group, two subgroups of common prime order `r` lying in a common cyclic
subgroup `C` coincide: each equals `⟨g^(|C|/r)⟩` for a generator `g` of `C`. This is the
`Ω₁`-bookkeeping engine of Lemma 12.18(a): it identifies `⟨z⟩ = C_{R₁}(P)` inside the cyclic
group `C_R(P)` without a general `Ω₁` operator. -/
private theorem eq_of_card_eq_of_le_of_isCyclic [Finite G] {C A B : Subgroup G}
    (hC : IsCyclic ↥C) (hA : A ≤ C) (hB : B ≤ C) {r : ℕ} (hr : r.Prime)
    (hcardA : Nat.card ↥A = r) (hcardB : Nat.card ↥B = r) : A = B := by
  classical
  obtain ⟨g, hg⟩ := hC.exists_generator
  have hn : orderOf g = Nat.card ↥C := orderOf_eq_card_of_forall_mem_zpowers hg
  have hnpos : 0 < Nat.card ↥C := Nat.card_pos
  have hrn : r ∣ Nat.card ↥C := by
    rw [← hcardA]
    calc Nat.card ↥A
        = Nat.card ↥(A.subgroupOf C) :=
          (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv).symm
      _ ∣ Nat.card ↥C := Subgroup.card_subgroup_dvd_card _
  -- any subgroup of `↥C` of order `r` equals `zpowers (g ^ (|C| / r))`.
  have key : ∀ D : Subgroup ↥C, Nat.card ↥D = r →
      D = Subgroup.zpowers (g ^ (Nat.card ↥C / r)) := by
    intro D hD
    have : Nontrivial ↥D := by
      apply Finite.one_lt_card_iff_nontrivial.mp
      rw [hD]; exact hr.one_lt
    obtain ⟨a0, ha0⟩ := exists_ne (1 : ↥D)
    have ha1 : (a0 : ↥C) ≠ 1 := fun h => ha0 (Subtype.ext h)
    have hor : orderOf (a0 : ↥C) = r := by
      have hdvd : orderOf (a0 : ↥C) ∣ r := hD ▸ Subgroup.orderOf_dvd_natCard D a0.2
      rcases (Nat.dvd_prime hr).mp hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) ha1
      · exact h
    have hzD : Subgroup.zpowers (a0 : ↥C) = D :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr a0.2)
        (by rw [Nat.card_zpowers, hor, hD])
    obtain ⟨i, hi⟩ :=
      Submonoid.mem_powers_iff (a0 : ↥C) g |>.mp (mem_powers_iff_mem_zpowers.mpr (hg _))
    have hoi : orderOf g / (orderOf g).gcd i = r := by rw [← orderOf_pow, hi, hor]
    have hgcd_dvd : (orderOf g).gcd i ∣ orderOf g := Nat.gcd_dvd_left _ _
    have hgcd_eq : (orderOf g).gcd i = Nat.card ↥C / r := by
      have hmul : (orderOf g).gcd i * r = orderOf g := by
        rw [← hoi, Nat.mul_div_cancel' hgcd_dvd]
      have h := Nat.div_eq_of_eq_mul_left hr.pos hmul.symm
      rw [← h, hn]
    have hdvd_i : Nat.card ↥C / r ∣ i := hgcd_eq ▸ Nat.gcd_dvd_right (orderOf g) i
    have hle : D ≤ Subgroup.zpowers (g ^ (Nat.card ↥C / r)) := by
      rw [← hzD, Subgroup.zpowers_le, ← hi]
      obtain ⟨k, hk⟩ := hdvd_i
      rw [hk, pow_mul]
      exact Subgroup.npow_mem_zpowers _ k
    have hcard_z : Nat.card ↥(Subgroup.zpowers (g ^ (Nat.card ↥C / r))) = r := by
      rw [Nat.card_zpowers, orderOf_pow, hn, Nat.gcd_eq_right (Nat.div_dvd_of_dvd hrn),
        Nat.div_div_self hrn hnpos.ne']
    exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq (hcard_z.trans hD.symm))
  have hA' : Nat.card ↥(A.subgroupOf C) = r := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv]; exact hcardA
  have hB' : Nat.card ↥(B.subgroupOf C) = r := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB).toEquiv]; exact hcardB
  have h := (key _ hA').trans (key _ hB').symm
  have hmap := congrArg (Subgroup.map C.subtype) h
  rwa [Subgroup.map_subgroupOf_eq_of_le hA, Subgroup.map_subgroupOf_eq_of_le hB] at hmap

/-- Variant of `inf_centralizer_sup_eq_bot_of_le_normalizer` retaining the second factor:
if `P` normalizes `Q` and `R`, `Q` normalizes `R`, `Q ⊓ R = ⊥`, and `C_Q(P) = 1`, then every
`P`-central element of `Q ⊔ R` lies in `R` (its `Q`-component is trivial). Computes
`C_{Q⊔N}(P) ≤ C_N(P)` and `C_{Q⊔N}(Q-side)` decompositions in Lemma 12.18(a). -/
private theorem inf_centralizer_sup_le_inf_of_le_normalizer {G : Type*} [Group G]
    {P Q R : Subgroup G} (hPQ : P ≤ Subgroup.normalizer (Q : Set G))
    (hPR : P ≤ Subgroup.normalizer (R : Set G)) (hQR : Q ≤ Subgroup.normalizer (R : Set G))
    (hdisj : Q ⊓ R = ⊥) (hCQ : Q ⊓ Subgroup.centralizer (P : Set G) = ⊥) :
    (Q ⊔ R) ⊓ Subgroup.centralizer (P : Set G) ≤
      R ⊓ Subgroup.centralizer (P : Set G) := by
  intro g hg
  rw [Subgroup.mem_inf] at hg
  obtain ⟨hgQR, hgC⟩ := hg
  rw [Subgroup.mem_centralizer_iff] at hgC
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right Q R hQR,
    Set.mem_mul] at hgQR
  obtain ⟨u, hu, v, hv, rfl⟩ := hgQR
  have key : ∀ a ∈ P, a * u * a⁻¹ = u ∧ a * v * a⁻¹ = v := by
    intro a ha
    have hau : a * u * a⁻¹ ∈ Q := (Subgroup.mem_set_normalizer_iff.mp (hPQ ha) u).mp hu
    have hav : a * v * a⁻¹ ∈ R := (Subgroup.mem_set_normalizer_iff.mp (hPR ha) v).mp hv
    have hcomm : a * (u * v) = (u * v) * a := hgC a ha
    have hconj : (a * u * a⁻¹) * (a * v * a⁻¹) = u * v := by
      have h1 : a * (u * v) * a⁻¹ = u * v := by rw [hcomm]; group
      calc (a * u * a⁻¹) * (a * v * a⁻¹) = a * (u * v) * a⁻¹ := by group
        _ = u * v := h1
    have hwQ : u⁻¹ * (a * u * a⁻¹) ∈ Q := Q.mul_mem (Q.inv_mem hu) hau
    have hwR : u⁻¹ * (a * u * a⁻¹) ∈ R := by
      have h2 : a * u * a⁻¹ = u * v * (a * v * a⁻¹)⁻¹ := by
        rw [eq_comm, mul_inv_eq_iff_eq_mul]; exact hconj.symm
      have heq : u⁻¹ * (a * u * a⁻¹) = v * (a * v * a⁻¹)⁻¹ := by rw [h2]; group
      rw [heq]; exact R.mul_mem hv (R.inv_mem hav)
    have hw1 : u⁻¹ * (a * u * a⁻¹) = 1 := by
      have hmem : u⁻¹ * (a * u * a⁻¹) ∈ Q ⊓ R := ⟨hwQ, hwR⟩
      rwa [hdisj, Subgroup.mem_bot] at hmem
    have hu_fix : a * u * a⁻¹ = u := by rw [inv_mul_eq_one] at hw1; exact hw1.symm
    refine ⟨hu_fix, ?_⟩
    rw [hu_fix] at hconj
    exact mul_left_cancel hconj
  have huC : u ∈ Subgroup.centralizer (P : Set G) := by
    rw [Subgroup.mem_centralizer_iff]; intro a ha
    have h := (key a ha).1; rwa [mul_inv_eq_iff_eq_mul] at h
  have hvC : v ∈ Subgroup.centralizer (P : Set G) := by
    rw [Subgroup.mem_centralizer_iff]; intro a ha
    have h := (key a ha).2; rwa [mul_inv_eq_iff_eq_mul] at h
  have hu1 : u = 1 := by
    have hmem : u ∈ Q ⊓ Subgroup.centralizer (P : Set G) := ⟨hu, huC⟩
    rwa [hCQ, Subgroup.mem_bot] at hmem
  rw [hu1, one_mul]
  exact ⟨hv, hvC⟩

/-- A subgroup normalizing both `A` and `B` normalizes `A ⊓ B`.
(Public: shared with `S12_ExceptionalBridge` for Lemma 12.3.) -/
theorem le_normalizer_inf {G : Type*} [Group G] {H A B : Subgroup G}
    (hA : H ≤ Subgroup.normalizer (A : Set G)) (hB : H ≤ Subgroup.normalizer (B : Set G)) :
    H ≤ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have hxA := Subgroup.mem_normalizer_iff.mp (hA hx) h
  have hxB := Subgroup.mem_normalizer_iff.mp (hB hx) h
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨hxA.mp h1, hxB.mp h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨hxA.mpr h1, hxB.mpr h2⟩

/-- The normalizer of `Q` normalizes the centralizer of `Q`.
(Public: shared with `S12_Theorem127`.) -/
theorem normalizer_le_normalizer_centralizer {G : Type*} [Group G] (Q : Subgroup G) :
    Subgroup.normalizer (Q : Set G) ≤
      Subgroup.normalizer ((Subgroup.centralizer (Q : Set G) : Subgroup G) : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro c
  constructor
  · intro hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro y hy
    have hy' : x⁻¹ * y * x ∈ Q := (Subgroup.mem_normalizer_iff''.mp hx y).mp hy
    have hcomm := hc _ hy'
    calc y * (x * c * x⁻¹) = x * ((x⁻¹ * y * x) * c) * x⁻¹ := by group
      _ = x * (c * (x⁻¹ * y * x)) * x⁻¹ := by rw [hcomm]
      _ = (x * c * x⁻¹) * y := by group
  · intro hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro y hy
    have hy' : x * y * x⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hx y).mp hy
    have hcomm := hc _ hy'
    have h2 : x * (y * c) * x⁻¹ = x * (c * y) * x⁻¹ := by
      calc x * (y * c) * x⁻¹ = (x * y * x⁻¹) * (x * c * x⁻¹) := by group
        _ = (x * c * x⁻¹) * (x * y * x⁻¹) := hcomm
        _ = x * (c * y) * x⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h2)

/-- The normalizer of `K` normalizes the normalizer of `K`. -/
private theorem normalizer_le_normalizer_normalizer {G : Type*} [Group G] (K : Subgroup G) :
    Subgroup.normalizer (K : Set G) ≤
      Subgroup.normalizer ((Subgroup.normalizer (K : Set G) : Subgroup G) : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro n
  constructor
  · intro hn
    rw [Subgroup.mem_normalizer_iff] at hn ⊢
    intro k
    constructor
    · intro hk
      have h1 : x⁻¹ * k * x ∈ K := (Subgroup.mem_normalizer_iff''.mp hx k).mp hk
      have h2 : n * (x⁻¹ * k * x) * n⁻¹ ∈ K := (hn _).mp h1
      have h3 : x * (n * (x⁻¹ * k * x) * n⁻¹) * x⁻¹ ∈ K :=
        (Subgroup.mem_normalizer_iff.mp hx _).mp h2
      convert h3 using 1
      group
    · intro hk
      have h1 : x⁻¹ * ((x * n * x⁻¹) * k * (x * n * x⁻¹)⁻¹) * x ∈ K :=
        (Subgroup.mem_normalizer_iff''.mp hx _).mp hk
      have h1' : n * (x⁻¹ * k * x) * n⁻¹ ∈ K := by convert h1 using 1; group
      have h2 : x⁻¹ * k * x ∈ K := (hn _).mpr h1'
      exact (Subgroup.mem_normalizer_iff''.mp hx k).mpr h2
  · intro hn
    rw [Subgroup.mem_normalizer_iff] at hn ⊢
    intro k
    constructor
    · intro hk
      have h1 : x * k * x⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hx k).mp hk
      have h2 : (x * n * x⁻¹) * (x * k * x⁻¹) * (x * n * x⁻¹)⁻¹ ∈ K := (hn _).mp h1
      have h2' : x * (n * k * n⁻¹) * x⁻¹ ∈ K := by convert h2 using 1; group
      exact (Subgroup.mem_normalizer_iff.mp hx _).mpr h2'
    · intro hk
      have h1 : x * (n * k * n⁻¹) * x⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hx _).mp hk
      have h1' : (x * n * x⁻¹) * (x * k * x⁻¹) * (x * n * x⁻¹)⁻¹ ∈ K := by
        convert h1 using 1; group
      have h2 : x * k * x⁻¹ ∈ K := (hn _).mpr h1'
      exact (Subgroup.mem_normalizer_iff.mp hx k).mpr h2

/-- A nontrivial subgroup `S` of a cyclic group `C` consisting of elements of order dividing a
prime `r` (here: `S ≤ R₁` with `Monoid.exponent ↥R₁ = r`) has order exactly `r`. Computes
`|C_{R₁}(P)| = |C_{R₁}(Q)| = r` in Lemma 12.18(a) — the displayed equation `(12.7)`. -/
private theorem card_eq_prime_of_le_exponent_prime [Finite G] {S R₁ C : Subgroup G}
    (hC : IsCyclic ↥C) (hSC : S ≤ C) (hSR₁ : S ≤ R₁) {r : ℕ} (hr : r.Prime)
    (hexp : Monoid.exponent ↥R₁ = r) (hSne : S ≠ ⊥) : Nat.card ↥S = r := by
  have := hC
  have hcyc : IsCyclic ↥S := Subgroup.isCyclic_of_le hSC
  obtain ⟨g₀, hg₀⟩ := hcyc.exists_generator
  have hor_card : orderOf g₀ = Nat.card ↥S := orderOf_eq_card_of_forall_mem_zpowers hg₀
  have hdvd_r : orderOf g₀ ∣ r := by
    have hmem : (g₀ : G) ∈ R₁ := hSR₁ g₀.2
    have h1 : orderOf (⟨(g₀ : G), hmem⟩ : ↥R₁) ∣ r := hexp ▸ Monoid.order_dvd_exponent _
    have h2 : orderOf ((g₀ : G)) = orderOf ((⟨(g₀ : G), hmem⟩ : ↥R₁)) :=
      orderOf_injective R₁.subtype R₁.subtype_injective ⟨(g₀ : G), hmem⟩
    have h3 : orderOf (g₀ : G) = orderOf g₀ :=
      orderOf_injective S.subtype S.subtype_injective g₀
    rwa [← h2, h3] at h1
  rcases (Nat.dvd_prime hr).mp hdvd_r with h1 | hr_eq
  · exfalso
    apply hSne
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg₀ ⟨x, hx⟩)
    have hg₀1 : g₀ = 1 := orderOf_eq_one_iff.mp h1
    rw [Subgroup.mem_bot]
    have hx1 : (⟨x, hx⟩ : ↥S) = 1 := by rw [← hk, hg₀1, one_zpow]
    exact congrArg Subtype.val hx1
  · rw [← hor_card]; exact hr_eq

/-- **Theorem 3.7 contradiction step of Lemma 12.18(a)** (shared by both conjuncts; extracted
from the first conjunct `tau1_Malpha_centralizer_P_ne_bot`). If `P` of prime order `p`
normalizes the `q`-group `Q ≠ 1` and the `r`-group `R₁` (`p, q, r` pairwise distinct), `Q`
normalizes but does not centralize `R₁`, and `C_Q(P) = 1`, then `C_{R₁}(P) ≠ 1`: otherwise
`P` acts fixed-point-freely on `Q ⊔ R₁`, so Theorem 3.7 makes `Q ⊔ R₁` nilpotent, and
coprimality of orders would force `Q` to centralize `R₁`. -/
private theorem inf_centralizer_ne_bot_of_not_le_centralizer [Finite G]
    {p q r : ℕ} [Fact p.Prime] [Fact q.Prime] [Fact r.Prime]
    (hqp : q ≠ p) (hrp : r ≠ p) (hqr : q ≠ r)
    {P Q R₁ : Subgroup G} (hsolv : Group.IsSolvable ↥((Q ⊔ R₁) ⊔ P))
    (hPp : IsPGroup p ↥P) (hPcard : Nat.card ↥P = p)
    (hQq : IsPGroup q ↥Q) (hR₁r : IsPGroup r ↥R₁) (hQne : Q ≠ ⊥)
    (hQinv : P ≤ Subgroup.normalizer (Q : Set G))
    (hPnormR₁ : P ≤ Subgroup.normalizer (R₁ : Set G))
    (hQnormR₁ : Q ≤ Subgroup.normalizer (R₁ : Set G))
    (hCQP : Q ⊓ Subgroup.centralizer (P : Set G) = ⊥)
    (hQncR₁ : ¬ Q ≤ Subgroup.centralizer (R₁ : Set G)) :
    R₁ ⊓ Subgroup.centralizer (P : Set G) ≠ ⊥ := by
  classical
  have hPne : P ≠ ⊥ := by
    intro h; rw [h, Subgroup.card_bot] at hPcard
    have := (Fact.out : p.Prime).one_lt; omega
  have hQR₁disj : Q ⊓ R₁ = ⊥ := by
    apply OddOrder.BG.Ch1.S01.inf_eq_bot_of_pGroup_coprime hQq
    obtain ⟨k, hk⟩ := hR₁r.exists_card_eq
    rw [hk]; exact ((Nat.coprime_primes Fact.out Fact.out).mpr hqr.symm).pow_left k
  -- `QR₁` is not nilpotent (`Q` does not centralize `R₁`, but coprime orders would commute).
  have hQR₁nn : ¬ Group.IsNilpotent ↥(Q ⊔ R₁) := by
    intro hnil
    apply hQncR₁
    intro x hxQ
    rw [Subgroup.mem_centralizer_iff]
    intro y hyR₁
    have hx' : x ∈ Q ⊔ R₁ := Subgroup.mem_sup_left hxQ
    have hy' : y ∈ Q ⊔ R₁ := Subgroup.mem_sup_right hyR₁
    have hoxq : ∃ a, orderOf x = q ^ a := by
      obtain ⟨a, ha⟩ := IsPGroup.iff_orderOf.mp hQq ⟨x, hxQ⟩
      exact ⟨a, by rw [← ha]; exact orderOf_injective Q.subtype Q.subtype_injective ⟨x, hxQ⟩⟩
    have hoyr : ∃ b, orderOf y = r ^ b := by
      obtain ⟨b, hb⟩ := IsPGroup.iff_orderOf.mp hR₁r ⟨y, hyR₁⟩
      exact ⟨b, by rw [← hb]; exact orderOf_injective R₁.subtype R₁.subtype_injective ⟨y, hyR₁⟩⟩
    have hcop : Nat.Coprime (orderOf (⟨x, hx'⟩ : ↥(Q ⊔ R₁)))
        (orderOf (⟨y, hy'⟩ : ↥(Q ⊔ R₁))) := by
      have hxo : orderOf (⟨x, hx'⟩ : ↥(Q ⊔ R₁)) = orderOf x :=
        (orderOf_injective (Q ⊔ R₁).subtype (Q ⊔ R₁).subtype_injective ⟨x, hx'⟩).symm
      have hyo : orderOf (⟨y, hy'⟩ : ↥(Q ⊔ R₁)) = orderOf y :=
        (orderOf_injective (Q ⊔ R₁).subtype (Q ⊔ R₁).subtype_injective ⟨y, hy'⟩).symm
      rw [hxo, hyo]
      obtain ⟨a, ha⟩ := hoxq; obtain ⟨b, hb⟩ := hoyr
      rw [ha, hb]
      exact (((Nat.coprime_primes Fact.out Fact.out).mpr hqr).pow_left a).pow_right b
    have hcomm := OddOrder.GroupTheory.commute_of_coprime_orderOf_of_isNilpotent hcop
    have hxy : x * y = y * x := by simpa using congrArg Subtype.val hcomm
    exact hxy.symm
  -- `C_{R₁}(P) ≠ 1` (else Theorem 3.7 makes `QR₁` nilpotent).
  intro hCR₁P
  apply hQR₁nn
  have hFPFbot : (Q ⊔ R₁) ⊓ Subgroup.centralizer (P : Set G) = ⊥ :=
    inf_centralizer_sup_eq_bot_of_le_normalizer hQinv hPnormR₁ hQnormR₁ hQR₁disj hCQP hCR₁P
  have hQR₁card : Nat.card ↥(Q ⊔ R₁) = Nat.card ↥Q * Nat.card ↥R₁ :=
    card_sup_eq_mul_of_le_normalizer_of_disjoint hQnormR₁ hQR₁disj
  have hQR₁cop : (Nat.card ↥(Q ⊔ R₁)).Coprime p := by
    rw [hQR₁card]
    have h1 : (Nat.card ↥Q).Coprime p := by
      obtain ⟨k, hk⟩ := hQq.exists_card_eq
      rw [hk]; exact ((Nat.coprime_primes Fact.out Fact.out).mpr hqp).pow_left k
    have h2 : (Nat.card ↥R₁).Coprime p := by
      obtain ⟨k, hk⟩ := hR₁r.exists_card_eq
      rw [hk]; exact ((Nat.coprime_primes Fact.out Fact.out).mpr hrp).pow_left k
    exact Nat.coprime_comm.mp
      (Nat.Coprime.mul_right (Nat.coprime_comm.mp h1) (Nat.coprime_comm.mp h2))
  refine OddOrder.BG.Ch1.S03c.isNilpotent_of_normalizing_primeOrder_fixedPointFree
    (N := Q ⊔ R₁) (R := P) ?_ ?_ ?_ hPne ⟨p, Fact.out, hPcard⟩ ?_
  · exact (le_inf hQinv hPnormR₁).trans
      (Subgroup.normalizer_inf_normalizer_le_normalizer_sup Q R₁)
  · rw [disjoint_iff, inf_comm]
    exact OddOrder.BG.Ch1.S01.inf_eq_bot_of_pGroup_coprime hPp hQR₁cop
  · exact fun h => hQne (le_bot_iff.mp (le_sup_left.trans h.le))
  · intro a haP ha1 n hn hn1 hfix
    have hcomm_an : Commute a n := mul_inv_eq_iff_eq_mul.mp hfix
    have hzpa : Subgroup.zpowers a = P := by
      have hle : Subgroup.zpowers a ≤ P := by rw [Subgroup.zpowers_le]; exact haP
      have horder : orderOf a = p := by
        have hdvd : orderOf a ∣ p := hPcard ▸ Subgroup.orderOf_dvd_natCard P haP
        rcases (Nat.dvd_prime Fact.out).mp hdvd with h | h
        · exact absurd (orderOf_eq_one_iff.mp h) ha1
        · exact h
      have hcard : Nat.card ↥(Subgroup.zpowers a) = Nat.card ↥P := by
        rw [Nat.card_zpowers, horder, hPcard]
      exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)
    have hnC : n ∈ Subgroup.centralizer (P : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hbP
      rw [← hzpa] at hbP
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hbP
      exact (hcomm_an.zpow_left k).eq
    have hmem : n ∈ (Q ⊔ R₁) ⊓ Subgroup.centralizer (P : Set G) := ⟨hn, hnC⟩
    rw [hFPFbot, Subgroup.mem_bot] at hmem
    exact hn1 hmem

end Helpers

/-- **BG Lemma 12.18(a), second conclusion** (mmd L3502-3506): under the hypotheses of Lemma
12.18 with `q ∉ α(M)`, the centralizer `C_{M_α}(PQ)` is trivial. By contradiction: a `P ⊔ Q`-
central element `z ∈ M_α` of prime order `r` (necessarily `r ∈ α(M)`) lies in a `PQ`-invariant
Sylow `r`-subgroup `R` of `M_α` of rank `≥ 3`. The Thompson subgroup `R₁` (Theorem 1.13) gives
`C_{R₁}(P)` of order exactly `r` inside the cyclic `C_R(P)` — equation `(12.7)` — whence
`⟨z⟩ = C_{R₁}(P) = C_{R₁}(Q) = R₀` by uniqueness of the order-`r` subgroup of a cyclic group.
For `N := N_{R₁}(R₀) ⊋ R₀`, the quotient `QN/R₀` (inside the ambient `(Q ⊔ N ⊔ P)/R₀`) admits
the order-`p` group `P` with fixed-point-free action (`C_N(P) = R₀ = C_N(Q)`), so Theorem 3.7
makes it nilpotent; coprimality then forces `Q` to centralize `N/R₀ ≠ 1`, whose fixed points
pull back to `C_N(Q) = R₀` — a contradiction. -/
theorem tau1_Malpha_centralizer_PQ_eq_bot [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hqp : q ≠ p) (hp : p ∈ tau1 M) {P : Subgroup G} (hP : P ∈ elemAbelianOfRank G p 1)
    (hPM : P ≤ M) {Q : Subgroup G} (hQM : Q ≤ M) (hQne : Q ≠ ⊥) (hQq : IsPGroup q ↥Q)
    (hQinv : P ≤ Subgroup.normalizer (Q : Set G))
    (hCQP : Q ⊓ Subgroup.centralizer (P : Set G) = ⊥)
    (hMNQ : maximalSubgroupsContaining (Subgroup.normalizer (Q : Set G)) ≠ {M})
    (hqα : q ∉ S10.alpha M) :
    S10.Malpha M ⊓ Subgroup.centralizer ((P ⊔ Q : Subgroup G) : Set G) = ⊥ := by
  classical
  have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  by_contra hcon
  -- `P` facts (as in the first conjunct).
  obtain ⟨hPea, hPcard1⟩ := mem_elemAbelianOfRank.mp hP
  have hPp : IsPGroup p ↥P := hPea.isPGroup
  have hPcard : Nat.card ↥P = p := by rw [hPcard1, pow_one]
  have hPne : P ≠ ⊥ := by
    intro h; rw [h, Subgroup.card_bot] at hPcard
    have := (Fact.out : p.Prime).one_lt; omega
  have hpα : p ∉ S10.alpha M := by
    intro hpa; have h3 := ((S10.mem_alpha_iff M p).mp hpa).2; rw [hp.2.2] at h3; omega
  have hPpi : Subgroup.IsPiSubgroup (S10.alpha M)ᶜ P := by
    intro s hs; rw [hPcard, (Fact.out : p.Prime).primeFactors, Finset.mem_singleton] at hs
    exact hs ▸ hpα
  have hQpi : Subgroup.IsPiSubgroup (S10.alpha M)ᶜ Q := by
    intro s hs
    obtain ⟨k, hk⟩ := hQq.exists_card_eq
    rw [hk] at hs
    have hsp := Nat.prime_of_mem_primeFactors hs
    have hsq : s = q :=
      (Nat.prime_dvd_prime_iff_eq hsp Fact.out).mp
        (hsp.dvd_of_dvd_pow (Nat.dvd_of_mem_primeFactors hs))
    exact hsq ▸ hqα
  -- `(12.6)` and `(12.5)`.
  have h126 : rank ↥(Subgroup.centralizer (P : Set G) ⊓ S10.Malpha M) ≤ 1 :=
    rank_centralizer_Malpha_le_one_of_not_uniqueMaximal hG hM hPM hPne hPpi
      (maximalSubgroupsContaining_normalizer_ne_singleton_of_mem_tau1 hG hM hp hPM hPne hPp)
  have h125 : rank ↥(Subgroup.centralizer (Q : Set G) ⊓ S10.Malpha M) ≤ 1 :=
    rank_centralizer_Malpha_le_one_of_not_uniqueMaximal hG hM hQM hQne hQpi hMNQ
  -- `X := P ⊔ Q` is an `α(M)'`-subgroup of `M`.
  have hXM : (P ⊔ Q : Subgroup G) ≤ M := sup_le hPM hQM
  have hPQdisj : P ⊓ Q = ⊥ := by
    apply OddOrder.BG.Ch1.S01.inf_eq_bot_of_pGroup_coprime hPp
    obtain ⟨k, hk⟩ := hQq.exists_card_eq
    rw [hk]; exact ((Nat.coprime_primes Fact.out Fact.out).mpr hqp).pow_left k
  have hXcard : Nat.card ↥(P ⊔ Q) = Nat.card ↥P * Nat.card ↥Q :=
    card_sup_eq_mul_of_le_normalizer_of_disjoint hQinv hPQdisj
  have hXpi : Subgroup.IsPiSubgroup (S10.alpha M)ᶜ (P ⊔ Q) := by
    intro s hs
    rw [hXcard, Nat.primeFactors_mul Nat.card_pos.ne' Nat.card_pos.ne'] at hs
    rcases Finset.mem_union.mp hs with h | h
    · exact hPpi s h
    · exact hQpi s h
  -- the prime `r` and the central element `z` (Step B of the skeleton).
  have hCzne : Nat.card
      ↥(S10.Malpha M ⊓ Subgroup.centralizer ((P ⊔ Q : Subgroup G) : Set G)) ≠ 1 := by
    intro h; exact hcon (Subgroup.card_eq_one.mp h)
  obtain ⟨r, hrp', hrdvd⟩ := Nat.exists_prime_and_dvd hCzne
  have : Fact r.Prime := ⟨hrp'⟩
  have hrα : r ∈ S10.alpha M := by
    apply S10.Malpha_isPiGroup M r
    refine Nat.mem_primeFactors.mpr ⟨hrp', ?_, Nat.card_pos.ne'⟩
    exact hrdvd.trans (Subgroup.card_dvd_of_le inf_le_left)
  have hqr : q ≠ r := fun h => hqα (h ▸ hrα)
  have hrp_ne : r ≠ p := fun h => hpα (h ▸ hrα)
  have hr2 : r ≠ 2 := by
    rintro rfl
    have hodd := hG.odd
    rw [Nat.odd_iff] at hodd
    obtain ⟨c, hc⟩ := hrdvd.trans
      ((Subgroup.card_subgroup_dvd_card (S10.Malpha M ⊓ _)))
    omega
  have hr_odd : Odd r := hrp'.odd_of_ne_two hr2
  obtain ⟨z0, hz0⟩ := exists_prime_orderOf_dvd_card' (G :=
    ↥(S10.Malpha M ⊓ Subgroup.centralizer ((P ⊔ Q : Subgroup G) : Set G))) r hrdvd
  set z : G := (z0 : G) with hz_def
  have hz_ord : orderOf z = r := by
    have h : orderOf z = orderOf z0 :=
      (orderOf_injective (S10.Malpha M ⊓ Subgroup.centralizer
        ((P ⊔ Q : Subgroup G) : Set G)).subtype (Subgroup.subtype_injective _) z0)
    rw [h, hz0]
  have hzMa : z ∈ S10.Malpha M := z0.2.1
  have hzCX : z ∈ Subgroup.centralizer ((P ⊔ Q : Subgroup G) : Set G) := z0.2.2
  have hz1 : z ≠ 1 := by
    intro h; rw [h, orderOf_one] at hz_ord; exact hrp'.one_lt.ne' hz_ord.symm
  have hzCP : z ∈ Subgroup.centralizer (P : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_left) hzCX
  have hzCQ : z ∈ Subgroup.centralizer (Q : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_right) hzCX
  -- `⟨z⟩` is a `PQ`-invariant `r`-subgroup of `M_α`.
  have hzpMa : Subgroup.zpowers z ≤ S10.Malpha M := Subgroup.zpowers_le.mpr hzMa
  have hz_zp_card : Nat.card ↥(Subgroup.zpowers z) = r := by
    rw [Nat.card_zpowers, hz_ord]
  have hzp_r : IsPGroup r ↥(Subgroup.zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [hz_zp_card, pow_one])
  have hzpinv : (P ⊔ Q : Subgroup G) ≤
      Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G) := by
    intro x hx
    have hcomm : Commute x z := Subgroup.mem_centralizer_iff.mp hzCX x hx
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      have h1 : x * z ^ k = z ^ k * x := (hcomm.zpow_right k).eq
      have h2 : x * z ^ k * x⁻¹ = z ^ k := by rw [h1]; group
      rw [h2]; exact hh
    · intro hh
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hh
      have h1 : x⁻¹ * z ^ k * x = z ^ k := by
        have := (hcomm.inv_left.zpow_right k).eq
        rw [this]; group
      have h2 : h = z ^ k := by
        have h3 : h = x⁻¹ * (z ^ k) * x := by rw [hk]; group
        rw [h3, h1]
      rw [h2]
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩
  -- `R` = a `PQ`-invariant Sylow `r`-subgroup of `M_α` with `r(R) ≥ 3` containing `z`.
  obtain ⟨R, hRMa, hRr, hXnormR, hRrank, hzR⟩ :=
    exists_invariant_sylow_Malpha_rank_three hG hM hrα hXM hXpi hzpMa hzp_r hzpinv
  have hPnormR : P ≤ Subgroup.normalizer (R : Set G) := le_sup_left.trans hXnormR
  have hQnormR : Q ≤ Subgroup.normalizer (R : Set G) := le_sup_right.trans hXnormR
  have hRMle : R ≤ M := hRMa.trans (S10.Malpha_le M)
  have hzRmem : z ∈ R := hzR (Subgroup.mem_zpowers z)
  -- `Q` does not centralize `R`.
  have hQncR : ¬ Q ≤ Subgroup.centralizer (R : Set G) := by
    intro hQcR
    have hRleCQ : R ≤ Subgroup.centralizer (Q : Set G) ⊓ S10.Malpha M := by
      refine le_inf (fun x hxR => ?_) hRMa
      rw [Subgroup.mem_centralizer_iff]
      intro y hyQ
      have hy := hQcR hyQ
      rw [Subgroup.mem_centralizer_iff] at hy
      exact (hy x hxR).symm
    have hrk : (3 : ℕ) ≤ rank ↥(Subgroup.centralizer (Q : Set G) ⊓ S10.Malpha M) :=
      le_trans hRrank (rank_le_of_injective (Subgroup.inclusion_injective hRleCQ))
    omega
  have hRne : R ≠ ⊥ := fun h => hz1 (Subgroup.mem_bot.mp (h ▸ hzRmem))
  -- `C_R(P)` and `C_R(Q)` are cyclic (`(12.6)`, `(12.5)`).
  have hCRP_cyclic : IsCyclic ↥(R ⊓ Subgroup.centralizer (P : Set G)) := by
    refine S10.isCyclic_of_pRank_le_one (hRr.to_le inf_le_left) hr_odd ?_
    have hle : R ⊓ Subgroup.centralizer (P : Set G) ≤
        Subgroup.centralizer (P : Set G) ⊓ S10.Malpha M :=
      le_inf inf_le_right (inf_le_left.trans hRMa)
    calc pRank ↥(R ⊓ Subgroup.centralizer (P : Set G)) r
        ≤ rank ↥(R ⊓ Subgroup.centralizer (P : Set G)) := pRank_le_rank r
      _ ≤ rank ↥(Subgroup.centralizer (P : Set G) ⊓ S10.Malpha M) :=
          rank_le_of_injective (Subgroup.inclusion_injective hle)
      _ ≤ 1 := h126
  have hCRQ_cyclic : IsCyclic ↥(R ⊓ Subgroup.centralizer (Q : Set G)) := by
    refine S10.isCyclic_of_pRank_le_one (hRr.to_le inf_le_left) hr_odd ?_
    have hle : R ⊓ Subgroup.centralizer (Q : Set G) ≤
        Subgroup.centralizer (Q : Set G) ⊓ S10.Malpha M :=
      le_inf inf_le_right (inf_le_left.trans hRMa)
    calc pRank ↥(R ⊓ Subgroup.centralizer (Q : Set G)) r
        ≤ rank ↥(R ⊓ Subgroup.centralizer (Q : Set G)) := pRank_le_rank r
      _ ≤ rank ↥(Subgroup.centralizer (Q : Set G) ⊓ S10.Malpha M) :=
          rank_le_of_injective (Subgroup.inclusion_injective hle)
      _ ≤ 1 := h125
  -- `R₁` = Thompson characteristic subgroup of `R`.
  obtain ⟨R₁, hR₁R, hR₁char, hR₁exp, hQncR₁⟩ :=
    exists_charSubgroup_exponent_not_centralized hG.odd hqr hRr hRne hQq hQnormR hQncR
  have : (R₁.subgroupOf R).Characteristic := hR₁char
  have hR₁r : IsPGroup r ↥R₁ := hRr.to_le hR₁R
  have hR₁M : R₁ ≤ M := hR₁R.trans hRMle
  have hNRle : Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (R₁ : Set G) := by
    have h := OddOrder.BG.AppB.normalizer_le_normalizer_map_of_characteristic
      (K := R) (W := R₁.subgroupOf R)
    rwa [Subgroup.map_subgroupOf_eq_of_le hR₁R] at h
  have hPnormR₁ : P ≤ Subgroup.normalizer (R₁ : Set G) := hPnormR.trans hNRle
  have hQnormR₁ : Q ≤ Subgroup.normalizer (R₁ : Set G) := hQnormR.trans hNRle
  have hQR₁disj : Q ⊓ R₁ = ⊥ := by
    apply OddOrder.BG.Ch1.S01.inf_eq_bot_of_pGroup_coprime hQq
    obtain ⟨k, hk⟩ := hR₁r.exists_card_eq
    rw [hk]; exact ((Nat.coprime_primes Fact.out Fact.out).mpr hqr.symm).pow_left k
  -- `C_{R₁}(P) ≠ 1` (the Theorem 3.7 step, via the extracted helper).
  have hYM37 : (Q ⊔ R₁) ⊔ P ≤ M := sup_le (sup_le hQM hR₁M) hPM
  have hsolvY37 : Group.IsSolvable ↥((Q ⊔ R₁) ⊔ P) :=
    Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hYM37).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hYM37).surjective
  have hCR₁Pne : R₁ ⊓ Subgroup.centralizer (P : Set G) ≠ ⊥ :=
    inf_centralizer_ne_bot_of_not_le_centralizer hqp hrp_ne hqr hsolvY37 hPp hPcard hQq hR₁r
      hQne hQinv hPnormR₁ hQnormR₁ hCQP hQncR₁
  -- `(12.7)`: `|C_{R₁}(P)| = r`, so `⟨z⟩ = C_{R₁}(P)` inside the cyclic `C_R(P)`.
  have hCR₁P_le : R₁ ⊓ Subgroup.centralizer (P : Set G) ≤
      R ⊓ Subgroup.centralizer (P : Set G) := inf_le_inf_right _ hR₁R
  have hCR₁P_card : Nat.card ↥(R₁ ⊓ Subgroup.centralizer (P : Set G)) = r :=
    card_eq_prime_of_le_exponent_prime hCRP_cyclic hCR₁P_le inf_le_left hrp' hR₁exp hCR₁Pne
  have hzeq : Subgroup.zpowers z = R₁ ⊓ Subgroup.centralizer (P : Set G) :=
    eq_of_card_eq_of_le_of_isCyclic hCRP_cyclic
      (le_inf (Subgroup.zpowers_le.mpr hzRmem) (Subgroup.zpowers_le.mpr hzCP))
      hCR₁P_le hrp' hz_zp_card hCR₁P_card
  have hzR₁mem : z ∈ R₁ :=
    (Subgroup.mem_inf.mp (hzeq ▸ Subgroup.mem_zpowers z)).1
  -- `R₀ := C_{R₁}(Q) = ⟨z⟩ = C_{R₁}(P)`.
  set R₀ : Subgroup G := R₁ ⊓ Subgroup.centralizer (Q : Set G) with hR₀_def
  have hzR₀le : Subgroup.zpowers z ≤ R₀ :=
    le_inf (Subgroup.zpowers_le.mpr hzR₁mem) (Subgroup.zpowers_le.mpr hzCQ)
  have hR₀ne : R₀ ≠ ⊥ := by
    intro h
    apply hz1
    have := hzR₀le (Subgroup.mem_zpowers z)
    rwa [h, Subgroup.mem_bot] at this
  have hR₀card : Nat.card ↥R₀ = r :=
    card_eq_prime_of_le_exponent_prime hCRQ_cyclic (inf_le_inf_right _ hR₁R) inf_le_left
      hrp' hR₁exp hR₀ne
  have hR₀eq_z : R₀ = Subgroup.zpowers z :=
    (Subgroup.eq_of_le_of_card_ge hzR₀le (le_of_eq (hR₀card.trans hz_zp_card.symm))).symm
  have hCR₁P_eq_R₀ : R₁ ⊓ Subgroup.centralizer (P : Set G) = R₀ := by
    rw [hR₀eq_z, ← hzeq]
  -- `R₀ < R₁` and `N := N_{R₁}(R₀) ⊋ R₀`.
  have hR₀lt : R₀ < R₁ := by
    refine lt_of_le_of_ne inf_le_left ?_
    intro heq
    apply hQncR₁
    have hR₁CQ : R₁ ≤ Subgroup.centralizer (Q : Set G) := by
      conv_lhs => rw [← heq]
      exact inf_le_right
    exact Subgroup.le_centralizer_iff.mp hR₁CQ
  set N : Subgroup G := R₁ ⊓ Subgroup.normalizer (R₀ : Set G) with hN_def
  have hR₀ltN : R₀ < N := OddOrder.BG.Ch2.S08.lt_inf_normalizer_of_isPGroup_lt hR₁r hR₀lt
  have hNleR₁ : N ≤ R₁ := inf_le_left
  have hR₀leN : R₀ ≤ N := hR₀ltN.le
  have hNr : IsPGroup r ↥N := hR₁r.to_le hNleR₁
  have hNM : N ≤ M := hNleR₁.trans hR₁M
  -- normalizer bookkeeping: `P, Q ≤ N_G(R₀)` and `P, Q ≤ N_G(N)`.
  have hPnormR₀ : P ≤ Subgroup.normalizer (R₀ : Set G) :=
    le_normalizer_inf hPnormR₁ (hQinv.trans (normalizer_le_normalizer_centralizer Q))
  have hQnormR₀ : Q ≤ Subgroup.normalizer (R₀ : Set G) :=
    le_normalizer_inf hQnormR₁
      (Subgroup.le_normalizer.trans (normalizer_le_normalizer_centralizer Q))
  have hPnormN : P ≤ Subgroup.normalizer (N : Set G) :=
    le_normalizer_inf hPnormR₁ (hPnormR₀.trans (normalizer_le_normalizer_normalizer R₀))
  have hQnormN : Q ≤ Subgroup.normalizer (N : Set G) :=
    le_normalizer_inf hQnormR₁ (hQnormR₀.trans (normalizer_le_normalizer_normalizer R₀))
  -- `C_N(Q) = R₀ = C_N(P)`.
  have hCNQ : N ⊓ Subgroup.centralizer (Q : Set G) = R₀ := by
    apply le_antisymm
    · exact inf_le_inf_right _ hNleR₁
    · exact le_inf hR₀leN inf_le_right
  have hCNP : N ⊓ Subgroup.centralizer (P : Set G) = R₀ := by
    apply le_antisymm
    · calc N ⊓ Subgroup.centralizer (P : Set G)
          ≤ R₁ ⊓ Subgroup.centralizer (P : Set G) := inf_le_inf_right _ hNleR₁
        _ = R₀ := hCR₁P_eq_R₀
    · refine le_inf hR₀leN ?_
      rw [hR₀eq_z]
      exact Subgroup.zpowers_le.mpr hzCP
  have hQNdisj : Q ⊓ N = ⊥ := by
    rw [eq_bot_iff]
    calc Q ⊓ N ≤ Q ⊓ R₁ := inf_le_inf_left _ hNleR₁
      _ = ⊥ := hQR₁disj
  -- the ambient group `H := (Q ⊔ N) ⊔ P` and the quotient by `R₀`.
  set Y : Subgroup G := Q ⊔ N with hY_def
  have hYM : Y ≤ M := sup_le hQM hNM
  have hPnormY : P ≤ Subgroup.normalizer (Y : Set G) :=
    (le_inf hQinv hPnormN).trans (Subgroup.normalizer_inf_normalizer_le_normalizer_sup Q N)
  have hYnormR₀ : Y ≤ Subgroup.normalizer (R₀ : Set G) := sup_le hQnormR₀ inf_le_right
  have hYcard : Nat.card ↥Y = Nat.card ↥Q * Nat.card ↥N :=
    card_sup_eq_mul_of_le_normalizer_of_disjoint hQnormN hQNdisj
  have hYcop_p : (Nat.card ↥Y).Coprime p := by
    rw [hYcard]
    have h1 : (Nat.card ↥Q).Coprime p := by
      obtain ⟨k, hk⟩ := hQq.exists_card_eq
      rw [hk]; exact ((Nat.coprime_primes Fact.out Fact.out).mpr hqp).pow_left k
    have h2 : (Nat.card ↥N).Coprime p := by
      obtain ⟨k, hk⟩ := hNr.exists_card_eq
      rw [hk]; exact ((Nat.coprime_primes Fact.out Fact.out).mpr hrp_ne).pow_left k
    exact Nat.coprime_comm.mp
      (Nat.Coprime.mul_right (Nat.coprime_comm.mp h1) (Nat.coprime_comm.mp h2))
  set Hgrp : Subgroup G := Y ⊔ P with hHgrp_def
  have hHM : Hgrp ≤ M := sup_le hYM hPM
  have hsolvH : Group.IsSolvable ↥Hgrp :=
    Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hHM).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hHM).surjective
  have hsolvYgrp : Group.IsSolvable ↥Y :=
    Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hYM).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hYM).surjective
  have hsolvN : Group.IsSolvable ↥N :=
    Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hNM).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hNM).surjective
  have hHnormR₀ : Hgrp ≤ Subgroup.normalizer (R₀ : Set G) := sup_le hYnormR₀ hPnormR₀
  have hR₀H : R₀ ≤ Hgrp := (hR₀leN.trans le_sup_right).trans le_sup_left
  have hR₀nH : (R₀.subgroupOf Hgrp).Normal := by
    constructor
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hHnormR₀ g.2) _).mp hn
  set π : ↥Hgrp →* ↥Hgrp ⧸ R₀.subgroupOf Hgrp :=
    QuotientGroup.mk' (R₀.subgroupOf Hgrp) with hπ_def
  have : Group.IsSolvable (↥Hgrp ⧸ R₀.subgroupOf Hgrp) :=
    Group.isSolvable_of_surjective (f := π) (QuotientGroup.mk'_surjective _)
  set N' : Subgroup (↥Hgrp ⧸ R₀.subgroupOf Hgrp) := (Y.subgroupOf Hgrp).map π with hN'_def
  set R' : Subgroup (↥Hgrp ⧸ R₀.subgroupOf Hgrp) := (P.subgroupOf Hgrp).map π with hR'_def
  -- cardinalities: `|R'| = p`, `p ∤ |N'|`.
  have hN'card_dvd : Nat.card ↥N' ∣ Nat.card ↥Y :=
    ((Y.subgroupOf Hgrp).card_map_dvd π).trans
      (dvd_of_eq (Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv))
  have hN'cop_p : (Nat.card ↥N').Coprime p := Nat.Coprime.coprime_dvd_left hN'card_dvd hYcop_p
  have hPR₀disj : P ⊓ R₀ = ⊥ := by
    apply OddOrder.BG.Ch1.S01.inf_eq_bot_of_pGroup_coprime hPp
    rw [hR₀card]
    exact (Nat.coprime_primes Fact.out Fact.out).mpr hrp_ne
  have hR'card : Nat.card ↥R' = p := by
    set f : ↥(P.subgroupOf Hgrp) →* ↥Hgrp ⧸ R₀.subgroupOf Hgrp :=
      π.comp (P.subgroupOf Hgrp).subtype with hf_def
    have hf_inj : Function.Injective f := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro x hx
      rw [MonoidHom.mem_ker] at hx
      have hker : (x : ↥Hgrp) ∈ R₀.subgroupOf Hgrp := by
        have h1 : (x : ↥Hgrp) ∈ (QuotientGroup.mk' (R₀.subgroupOf Hgrp)).ker :=
          MonoidHom.mem_ker.mpr hx
        rwa [QuotientGroup.ker_mk'] at h1
      rw [Subgroup.mem_subgroupOf] at hker
      have hxP : ((x : ↥Hgrp) : G) ∈ P := by
        have := x.2; rwa [Subgroup.mem_subgroupOf] at this
      have hmem : ((x : ↥Hgrp) : G) ∈ P ⊓ R₀ := ⟨hxP, hker⟩
      rw [hPR₀disj, Subgroup.mem_bot] at hmem
      rw [Subgroup.mem_bot]
      exact Subtype.ext (Subtype.ext hmem)
    have hR'_eq_range : R' = f.range := by
      rw [hR'_def, hf_def, MonoidHom.range_comp, Subgroup.range_subtype]
    rw [hR'_eq_range]
    calc Nat.card ↥f.range = Nat.card ↥(P.subgroupOf Hgrp) :=
          (Nat.card_congr (MonoidHom.ofInjective hf_inj).toEquiv).symm
      _ = Nat.card ↥P := Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
      _ = p := hPcard
  have hR'p : IsPGroup p ↥R' := IsPGroup.of_card (n := 1) (by rw [hR'card, pow_one])
  have hdisj' : Disjoint N' R' := by
    rw [disjoint_iff, inf_comm]
    exact OddOrder.BG.Ch1.S01.inf_eq_bot_of_pGroup_coprime hR'p hN'cop_p
  -- nontriviality witnesses.
  obtain ⟨n₀, hn₀N, hn₀R₀⟩ := SetLike.exists_of_lt hR₀ltN
  have hn₀Y : n₀ ∈ Y := Subgroup.mem_sup_right hn₀N
  have hn₀H : n₀ ∈ Hgrp := Subgroup.mem_sup_left hn₀Y
  have hN'ne : N' ≠ ⊥ := by
    intro h
    have hmem : π ⟨n₀, hn₀H⟩ ∈ N' :=
      Subgroup.mem_map_of_mem _ (by rwa [Subgroup.mem_subgroupOf])
    rw [h, Subgroup.mem_bot] at hmem
    have h1 : (⟨n₀, hn₀H⟩ : ↥Hgrp) ∈ (QuotientGroup.mk' (R₀.subgroupOf Hgrp)).ker :=
      MonoidHom.mem_ker.mpr hmem
    rw [QuotientGroup.ker_mk', Subgroup.mem_subgroupOf] at h1
    exact hn₀R₀ h1
  have hR'ne : R' ≠ ⊥ := by
    intro h; rw [h, Subgroup.card_bot] at hR'card
    have := (Fact.out : p.Prime).one_lt; omega
  -- `R'` normalizes `N'`.
  have hR'norm : R' ≤ Subgroup.normalizer (N' : Set (↥Hgrp ⧸ R₀.subgroupOf Hgrp)) := by
    rintro x' hx'
    obtain ⟨xt, hxt, rfl⟩ := Subgroup.mem_map.mp hx'
    have hxtP : ((xt : ↥Hgrp) : G) ∈ P := by
      have := hxt; rwa [Subgroup.mem_subgroupOf] at this
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      obtain ⟨nt, hnt, rfl⟩ := Subgroup.mem_map.mp hh
      have heq : π xt * π nt * (π xt)⁻¹ = π (xt * nt * xt⁻¹) := by
        rw [map_mul, map_mul, map_inv]
      rw [heq]
      apply Subgroup.mem_map_of_mem
      rw [Subgroup.mem_subgroupOf] at hnt ⊢
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
      exact (Subgroup.mem_normalizer_iff.mp (hPnormY hxtP) _).mp hnt
    · intro hh
      obtain ⟨mt, hmt, hmteq⟩ := Subgroup.mem_map.mp hh
      have h_eq : h = π (xt⁻¹ * mt * xt) := by
        rw [map_mul, map_mul, map_inv, hmteq]
        group
      rw [h_eq]
      apply Subgroup.mem_map_of_mem
      rw [Subgroup.mem_subgroupOf] at hmt ⊢
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
      exact (Subgroup.mem_normalizer_iff''.mp (hPnormY hxtP) _).mp hmt
  -- conjugation action of `↥P` on `↥Y` and `Q`-side action on `↥N` (templates from BB3).
  let actP : MulDistribMulAction ↥P ↥Y :=
    MulDistribMulAction.compHom (M := ↥(Subgroup.normalizer (Y : Set G))) ↥Y
      (Subgroup.inclusion hPnormY)
  set φP : ↥P →* MulAut ↥Y := MulDistribMulAction.toMulAut ↥P ↥Y with hφP
  have hφP_coe : ∀ (a : ↥P) (x : ↥Y), (Y.subtype ((φP a) x)) = (↑a) * (Y.subtype x) * (↑a)⁻¹ :=
    fun _ _ => rfl
  have hR₀nY : (R₀.subgroupOf Y).Normal := by
    constructor
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hYnormR₀ g.2) _).mp hn
  have hR₀inv_P : Ch03.IsAInvariant φP (R₀.subgroupOf Y) := by
    rw [Ch03.isAInvariant_iff_smul_mem]
    intro a g hg
    rw [Subgroup.mem_subgroupOf] at hg ⊢
    have hcoe : ((φP a) g : G) = (↑a) * (g : G) * (↑a)⁻¹ := hφP_coe a g
    rw [hcoe]
    exact (Subgroup.mem_normalizer_iff.mp (hPnormR₀ a.2) _).mp hg
  have hCopP : Nat.Coprime (Nat.card ↥P) (Nat.card ↥Y) := by
    rw [hPcard]; exact Nat.coprime_comm.mp hYcop_p
  -- fixed-point-freeness of the `R'`-action on `N'` via coprime coset-fixed points.
  have hFPF : ∀ x' ∈ R', x' ≠ 1 → ∀ n' ∈ N', n' ≠ 1 → x' * n' * x'⁻¹ ≠ n' := by
    intro x' hx' hx'1 n' hn' hn'1 hfix
    -- `n'` is centralized by all of `R' = ⟨x'⟩`.
    have hzp_x' : Subgroup.zpowers x' = R' := by
      have hle : Subgroup.zpowers x' ≤ R' := Subgroup.zpowers_le.mpr hx'
      have horder : orderOf x' = p := by
        have hdvd : orderOf x' ∣ p := hR'card ▸ Subgroup.orderOf_dvd_natCard R' hx'
        rcases (Nat.dvd_prime Fact.out).mp hdvd with h | h
        · exact absurd (orderOf_eq_one_iff.mp h) hx'1
        · exact h
      have hcard : Nat.card ↥(Subgroup.zpowers x') = Nat.card ↥R' := by
        rw [Nat.card_zpowers, horder, hR'card]
      exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)
    have hn'C : ∀ y' ∈ R', y' * n' * y'⁻¹ = n' := by
      intro y' hy'
      rw [← hzp_x'] at hy'
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy'
      have hcomm : Commute x' n' := mul_inv_eq_iff_eq_mul.mp hfix
      have h1 : x' ^ k * n' = n' * x' ^ k := (hcomm.zpow_left k).eq
      rw [h1]; group
    obtain ⟨nt, hnt, rfl⟩ := Subgroup.mem_map.mp hn'
    have hntY : ((nt : ↥Hgrp) : G) ∈ Y := by
      have := hnt; rwa [Subgroup.mem_subgroupOf] at this
    set nY : ↥Y := ⟨((nt : ↥Hgrp) : G), hntY⟩ with hnY_def
    have hg_fix : ∀ a : ↥P, ∃ m ∈ R₀.subgroupOf Y, (φP a) nY = nY * m := by
      intro a
      have haH : (a : G) ∈ Hgrp := Subgroup.mem_sup_right a.2
      have haP' : (⟨(a : G), haH⟩ : ↥Hgrp) ∈ P.subgroupOf Hgrp := by
        rw [Subgroup.mem_subgroupOf]; exact a.2
      have hπa : π ⟨(a : G), haH⟩ ∈ R' := Subgroup.mem_map_of_mem _ haP'
      have hfix_a := hn'C _ hπa
      have h1 : π (⟨(a : G), haH⟩ * nt * ⟨(a : G), haH⟩⁻¹ * nt⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hfix_a, mul_inv_cancel]
      have hker : ((⟨(a : G), haH⟩ * nt * ⟨(a : G), haH⟩⁻¹ * nt⁻¹ : ↥Hgrp) : G) ∈ R₀ := by
        have h2 : (⟨(a : G), haH⟩ * nt * ⟨(a : G), haH⟩⁻¹ * nt⁻¹ : ↥Hgrp) ∈
            (QuotientGroup.mk' (R₀.subgroupOf Hgrp)).ker := MonoidHom.mem_ker.mpr h1
        rw [QuotientGroup.ker_mk', Subgroup.mem_subgroupOf] at h2
        exact h2
      have hkerG : (a : G) * (nY : G) * (a : G)⁻¹ * (nY : G)⁻¹ ∈ R₀ := by
        simpa only [Subgroup.coe_mul, InvMemClass.coe_inv] using hker
      refine ⟨nY⁻¹ * (φP a) nY, ?_, (mul_inv_cancel_left _ _).symm⟩
      rw [Subgroup.mem_subgroupOf]
      have hval : ((nY⁻¹ * (φP a) nY : ↥Y) : G) =
          (nY : G)⁻¹ * ((a : G) * (nY : G) * (a : G)⁻¹) := by
        simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
        congr 1
      rw [hval]
      have hrw : (nY : G)⁻¹ * ((a : G) * (nY : G) * (a : G)⁻¹) =
          (nY : G)⁻¹ * ((a : G) * (nY : G) * (a : G)⁻¹ * (nY : G)⁻¹) * (nY : G) := by group
      rw [hrw]
      exact (Subgroup.mem_normalizer_iff''.mp (hYnormR₀ hntY) _).mp hkerG
    obtain ⟨c, hc_fix, m, hm, hc_eq⟩ :=
      OddOrder.Isaacs.Ch04.coprime_fixedPoints_quotient (φ := φP) hCopP
        (Or.inr inferInstance) hR₀inv_P hg_fix
    have hcC : (c : G) ∈ Subgroup.centralizer (P : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a haP
      have hfixc := hc_fix ⟨a, haP⟩
      have hG_eq : a * (c : G) * a⁻¹ = (c : G) := by
        have hcoe := hφP_coe ⟨a, haP⟩ c
        rw [hfixc] at hcoe
        exact hcoe.symm
      exact mul_inv_eq_iff_eq_mul.mp hG_eq
    have hcR₀ : (c : G) ∈ R₀ := by
      have hmem : (c : G) ∈ Y ⊓ Subgroup.centralizer (P : Set G) := ⟨c.2, hcC⟩
      have hdecomp := inf_centralizer_sup_le_inf_of_le_normalizer hQinv hPnormN hQnormN
        hQNdisj hCQP hmem
      rw [hCNP] at hdecomp
      exact hdecomp
    have hm' : ((m : ↥Y) : G) ∈ R₀ := by
      have := hm; rwa [Subgroup.mem_subgroupOf] at this
    have hnY_R₀ : (nY : G) ∈ R₀ := by
      have hY_eq : (nY : G) = (c : G) * ((m : ↥Y) : G)⁻¹ := by
        rw [hc_eq]
        simp only [Subgroup.coe_mul]
        group
      rw [hY_eq]
      exact R₀.mul_mem hcR₀ (R₀.inv_mem hm')
    apply hn'1
    have h1 : nt ∈ (QuotientGroup.mk' (R₀.subgroupOf Hgrp)).ker := by
      rw [QuotientGroup.ker_mk', Subgroup.mem_subgroupOf]
      exact hnY_R₀
    exact MonoidHom.mem_ker.mp h1
  -- Theorem 3.7: `N' = QN/R₀` is nilpotent.
  have hsolvN'R' : Group.IsSolvable ↥(N' ⊔ R') := inferInstance
  have hnil : Group.IsNilpotent ↥N' :=
    OddOrder.BG.Ch1.S03c.isNilpotent_of_normalizing_primeOrder_fixedPointFree
      (N := N') (R := R') hR'norm hdisj' hN'ne hR'ne ⟨p, Fact.out, hR'card⟩ hFPF
  -- coprimality in the nilpotent `N'` forces `Q` to centralize `N/R₀`, whose fixed points
  -- pull back to `C_N(Q) = R₀`: contradiction with `n₀ ∉ R₀`.
  apply hn₀R₀
  let actQ : MulDistribMulAction ↥Q ↥N :=
    MulDistribMulAction.compHom (M := ↥(Subgroup.normalizer (N : Set G))) ↥N
      (Subgroup.inclusion hQnormN)
  set φQ : ↥Q →* MulAut ↥N := MulDistribMulAction.toMulAut ↥Q ↥N with hφQ
  have hφQ_coe : ∀ (a : ↥Q) (x : ↥N), (N.subtype ((φQ a) x)) = (↑a) * (N.subtype x) * (↑a)⁻¹ :=
    fun _ _ => rfl
  have hNnormR₀ : N ≤ Subgroup.normalizer (R₀ : Set G) := inf_le_right
  have hR₀nN : (R₀.subgroupOf N).Normal := by
    constructor
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hNnormR₀ g.2) _).mp hn
  have hR₀inv_Q : Ch03.IsAInvariant φQ (R₀.subgroupOf N) := by
    rw [Ch03.isAInvariant_iff_smul_mem]
    intro a g hg
    rw [Subgroup.mem_subgroupOf] at hg ⊢
    have hcoe : ((φQ a) g : G) = (↑a) * (g : G) * (↑a)⁻¹ := hφQ_coe a g
    rw [hcoe]
    exact (Subgroup.mem_normalizer_iff.mp (hQnormR₀ a.2) _).mp hg
  have hCopQ : Nat.Coprime (Nat.card ↥Q) (Nat.card ↥N) := by
    obtain ⟨k, hk⟩ := hQq.exists_card_eq
    obtain ⟨l, hl⟩ := hNr.exists_card_eq
    rw [hk, hl]
    exact (((Nat.coprime_primes Fact.out Fact.out).mpr hqr).pow_left k).pow_right l
  have hg_fixQ : ∀ u : ↥Q, ∃ m ∈ R₀.subgroupOf N, (φQ u) ⟨n₀, hn₀N⟩ = ⟨n₀, hn₀N⟩ * m := by
    intro u
    have huY : (u : G) ∈ Y := Subgroup.mem_sup_left u.2
    have huH : (u : G) ∈ Hgrp := Subgroup.mem_sup_left huY
    have hπu_N' : π ⟨(u : G), huH⟩ ∈ N' :=
      Subgroup.mem_map_of_mem _ (by rw [Subgroup.mem_subgroupOf]; exact huY)
    have hπn₀_N' : π ⟨n₀, hn₀H⟩ ∈ N' :=
      Subgroup.mem_map_of_mem _ (by rw [Subgroup.mem_subgroupOf]; exact hn₀Y)
    -- coprime orders in the nilpotent `N'` force the images to commute.
    have hcommN' : Commute (π ⟨(u : G), huH⟩) (π ⟨n₀, hn₀H⟩) := by
      have hou : ∃ a, orderOf (π ⟨(u : G), huH⟩) = q ^ a := by
        have h1 : orderOf (⟨(u : G), huH⟩ : ↥Hgrp) = orderOf (u : G) :=
          (orderOf_injective Hgrp.subtype Hgrp.subtype_injective ⟨(u : G), huH⟩).symm
        have h2 : orderOf (u : G) = orderOf u :=
          orderOf_injective Q.subtype Q.subtype_injective u
        obtain ⟨a, ha⟩ := IsPGroup.iff_orderOf.mp hQq u
        obtain ⟨b, hb, hdvd⟩ := (Nat.dvd_prime_pow Fact.out).mp
          (((orderOf_map_dvd π _).trans (dvd_of_eq (h1.trans (h2.trans ha)))))
        exact ⟨b, hdvd⟩
      have hon : ∃ b, orderOf (π ⟨n₀, hn₀H⟩) = r ^ b := by
        have h1 : orderOf (⟨n₀, hn₀H⟩ : ↥Hgrp) = orderOf n₀ :=
          (orderOf_injective Hgrp.subtype Hgrp.subtype_injective ⟨n₀, hn₀H⟩).symm
        have h2 : orderOf (⟨n₀, hn₀N⟩ : ↥N) = orderOf n₀ :=
          (orderOf_injective N.subtype N.subtype_injective ⟨n₀, hn₀N⟩).symm
        obtain ⟨a, ha⟩ := IsPGroup.iff_orderOf.mp hNr ⟨n₀, hn₀N⟩
        obtain ⟨b, hb, hdvd⟩ := (Nat.dvd_prime_pow Fact.out).mp
          ((orderOf_map_dvd π _).trans (dvd_of_eq (h1.trans (h2.symm.trans ha))))
        exact ⟨b, hdvd⟩
      have hu' : π ⟨(u : G), huH⟩ ∈ N' ⊔ R' := Subgroup.mem_sup_left hπu_N'
      have hn' : π ⟨n₀, hn₀H⟩ ∈ N' ⊔ R' := Subgroup.mem_sup_left hπn₀_N'
      -- work inside the nilpotent subgroup `N'`.
      have hcop : Nat.Coprime (orderOf (⟨π ⟨(u : G), huH⟩, hπu_N'⟩ : ↥N'))
          (orderOf (⟨π ⟨n₀, hn₀H⟩, hπn₀_N'⟩ : ↥N')) := by
        have hxo : orderOf (⟨π ⟨(u : G), huH⟩, hπu_N'⟩ : ↥N') = orderOf (π ⟨(u : G), huH⟩) :=
          (orderOf_injective N'.subtype N'.subtype_injective
            ⟨π ⟨(u : G), huH⟩, hπu_N'⟩).symm
        have hyo : orderOf (⟨π ⟨n₀, hn₀H⟩, hπn₀_N'⟩ : ↥N') = orderOf (π ⟨n₀, hn₀H⟩) :=
          (orderOf_injective N'.subtype N'.subtype_injective
            ⟨π ⟨n₀, hn₀H⟩, hπn₀_N'⟩).symm
        rw [hxo, hyo]
        obtain ⟨a, ha⟩ := hou; obtain ⟨b, hb⟩ := hon
        rw [ha, hb]
        exact (((Nat.coprime_primes Fact.out Fact.out).mpr hqr).pow_left a).pow_right b
      have := hnil
      have hcomm := OddOrder.GroupTheory.commute_of_coprime_orderOf_of_isNilpotent hcop
      have hxy := congrArg Subtype.val hcomm
      simpa [commute_iff_eq] using hxy
    have h1 : π (⟨(u : G), huH⟩ * ⟨n₀, hn₀H⟩ * ⟨(u : G), huH⟩⁻¹ * ⟨n₀, hn₀H⟩⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]
      have hc : π ⟨(u : G), huH⟩ * π ⟨n₀, hn₀H⟩ = π ⟨n₀, hn₀H⟩ * π ⟨(u : G), huH⟩ :=
        hcommN'.eq
      rw [hc]
      group
    have hker : ((⟨(u : G), huH⟩ * ⟨n₀, hn₀H⟩ * ⟨(u : G), huH⟩⁻¹ * ⟨n₀, hn₀H⟩⁻¹ :
        ↥Hgrp) : G) ∈ R₀ := by
      have h2 : (⟨(u : G), huH⟩ * ⟨n₀, hn₀H⟩ * ⟨(u : G), huH⟩⁻¹ * ⟨n₀, hn₀H⟩⁻¹ : ↥Hgrp) ∈
          (QuotientGroup.mk' (R₀.subgroupOf Hgrp)).ker := MonoidHom.mem_ker.mpr h1
      rw [QuotientGroup.ker_mk', Subgroup.mem_subgroupOf] at h2
      exact h2
    have hkerG : (u : G) * n₀ * (u : G)⁻¹ * n₀⁻¹ ∈ R₀ := by
      simpa only [Subgroup.coe_mul, InvMemClass.coe_inv] using hker
    refine ⟨(⟨n₀, hn₀N⟩ : ↥N)⁻¹ * (φQ u) ⟨n₀, hn₀N⟩, ?_, (mul_inv_cancel_left _ _).symm⟩
    rw [Subgroup.mem_subgroupOf]
    have hval : (((⟨n₀, hn₀N⟩ : ↥N)⁻¹ * (φQ u) ⟨n₀, hn₀N⟩ : ↥N) : G) =
        n₀⁻¹ * ((u : G) * n₀ * (u : G)⁻¹) := by
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
      congr 1
    rw [hval]
    have hrw : n₀⁻¹ * ((u : G) * n₀ * (u : G)⁻¹) =
        n₀⁻¹ * ((u : G) * n₀ * (u : G)⁻¹ * n₀⁻¹) * n₀ := by group
    rw [hrw]
    have hn₀normR₀ : n₀ ∈ Subgroup.normalizer (R₀ : Set G) := hNnormR₀ hn₀N
    exact (Subgroup.mem_normalizer_iff''.mp hn₀normR₀ _).mp hkerG
  obtain ⟨c, hc_fix, m, hm, hc_eq⟩ :=
    OddOrder.Isaacs.Ch04.coprime_fixedPoints_quotient (φ := φQ) hCopQ
      (Or.inr inferInstance) hR₀inv_Q hg_fixQ
  have hcC : (c : G) ∈ Subgroup.centralizer (Q : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a haQ
    have hfixc := hc_fix ⟨a, haQ⟩
    have hG_eq : a * (c : G) * a⁻¹ = (c : G) := by
      have hcoe := hφQ_coe ⟨a, haQ⟩ c
      rw [hfixc] at hcoe
      exact hcoe.symm
    exact mul_inv_eq_iff_eq_mul.mp hG_eq
  have hcR₀ : (c : G) ∈ R₀ := by
    have hmem : (c : G) ∈ N ⊓ Subgroup.centralizer (Q : Set G) := ⟨c.2, hcC⟩
    rwa [hCNQ] at hmem
  have hm' : ((m : ↥N) : G) ∈ R₀ := by
    have := hm; rwa [Subgroup.mem_subgroupOf] at this
  have hn₀_eq : n₀ = (c : G) * ((m : ↥N) : G)⁻¹ := by
    have h := congrArg (N.subtype) hc_eq
    rw [map_mul] at h
    have h2 : (c : G) = n₀ * ((m : ↥N) : G) := h
    rw [h2]
    group
  rw [hn₀_eq]
  exact R₀.mul_mem hcR₀ (R₀.inv_mem hm')

/-- **BG Lemma 12.18** (mmd L3454): `p ∈ τ₁(M)`, `P ∈ ℰ_p¹(M)`, `q ∈ p'`, `Q` を `M` の非自明
`P`-不変 `q`-部分群で `C_Q(P)=1`, `ℳ(N_G(Q))≠{M}` とすると
(a) `M_α≠1` かつ `q∉α(M)` なら `C_{M_α}(P)≠1` かつ `C_{M_α}(PQ)=1`;
(b) `Q` が `M` の Sylow `q` なら `α(M)=β(M)` で (a) の状況が成立。 -/
theorem tau1_Malpha_interaction [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hqp : q ≠ p) (hp : p ∈ tau1 M) {P : Subgroup G} (hP : P ∈ elemAbelianOfRank G p 1)
    (hPM : P ≤ M) {Q : Subgroup G} (hQM : Q ≤ M) (hQne : Q ≠ ⊥) (hQq : IsPGroup q ↥Q)
    (hQinv : P ≤ Subgroup.normalizer (Q : Set G))
    (hCQP : Q ⊓ Subgroup.centralizer (P : Set G) = ⊥)
    (hMNQ : maximalSubgroupsContaining (Subgroup.normalizer (Q : Set G)) ≠ {M}) :
    (S10.Malpha M ≠ ⊥ → q ∉ S10.alpha M →
      S10.Malpha M ⊓ Subgroup.centralizer (P : Set G) ≠ ⊥ ∧
      S10.Malpha M ⊓ Subgroup.centralizer ((P ⊔ Q : Subgroup G) : Set G) = ⊥) ∧
    ((∀ T : Subgroup G, T ≤ M → IsPGroup q ↥T → Q ≤ T → Q = T) →
      S10.alpha M = S10.beta M ∧ S10.Malpha M ≠ ⊥ ∧ q ∉ S10.alpha M ∧
      S10.Malpha M ⊓ Subgroup.centralizer (P : Set G) ≠ ⊥ ∧
      S10.Malpha M ⊓ Subgroup.centralizer ((P ⊔ Q : Subgroup G) : Set G) = ⊥) := by
  classical
  have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  have hMcoatom : IsCoatom M := mem_maximalSubgroups.mp hM
  obtain ⟨hPea, hPcard1⟩ := mem_elemAbelianOfRank.mp hP
  have hPp : IsPGroup p ↥P := hPea.isPGroup
  have hPcard : Nat.card ↥P = p := by rw [hPcard1, pow_one]
  refine ⟨fun hαne hqα =>
    ⟨tau1_Malpha_centralizer_P_ne_bot hG hM hqp hp hP hPM hQM hQne hQq hQinv hCQP hMNQ hαne hqα,
     tau1_Malpha_centralizer_PQ_eq_bot hG hM hqp hp hP hPM hQM hQne hQq hQinv hCQP hMNQ hqα⟩,
    ?_⟩
  intro hQsyl
  -- `N_G(Q) < ⊤`; if `M ≤ N_G(Q)` then `N_G(Q) = M` and `ℳ(N_G(Q)) = {M}`, contradiction.
  have hNQne_top : Subgroup.normalizer (Q : Set G) ≠ ⊤ := by
    intro htop
    have : Q.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases hG.simple.eq_bot_or_eq_top_of_normal Q inferInstance with h | h
    · exact hQne h
    · exact hMcoatom.1 (top_le_iff.mp (h ▸ hQM))
  have hnotMleNQ : ¬ M ≤ Subgroup.normalizer (Q : Set G) := by
    intro hle
    apply hMNQ
    have hNQM : Subgroup.normalizer (Q : Set G) = M := by
      by_contra hne
      exact hNQne_top (hMcoatom.2 _ (lt_of_le_of_ne hle (Ne.symm hne)))
    rw [hNQM]
    ext L
    simp only [Set.mem_singleton_iff]
    constructor
    · rintro ⟨hLco, hML⟩
      by_contra hne
      exact hLco.1 (hMcoatom.2 L (lt_of_le_of_ne hML (Ne.symm hne)))
    · intro hLM
      rw [hLM]
      exact ⟨hMcoatom, le_refl M⟩
  -- Step 1: `Q ≤ M'` — the coprime fixed-point-free action of `P` gives `Q = [Q, P]`.
  have hQM' : Q ≤ derivedInG M := by
    have : Group.IsSolvable ↥Q :=
      Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hQM).toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hQM).surjective
    have hfix_bot : Subgroup.fixedPointsOfMulAut
        ((Subgroup.normalizerMonoidHom Q).comp (Subgroup.inclusion hQinv)) = ⊥ := by
      have h2 : (Subgroup.fixedPointsOfMulAut
          ((Subgroup.normalizerMonoidHom Q).comp (Subgroup.inclusion hQinv))).map Q.subtype
          = ⊥ := by
        rw [fixedPointsOfMulAut_conj_map_subtype hQinv, inf_comm]; exact hCQP
      exact ((Subgroup.fixedPointsOfMulAut
        ((Subgroup.normalizerMonoidHom Q).comp
          (Subgroup.inclusion hQinv))).map_eq_bot_iff_of_injective
        Q.subtype_injective).mp h2
    have hcop : Nat.Coprime (Nat.card ↥P) (Nat.card ↥Q) := by
      obtain ⟨k, hk⟩ := hQq.exists_card_eq
      rw [hPcard, hk]
      exact ((Nat.coprime_primes Fact.out Fact.out).mpr (Ne.symm hqp)).pow_right k
    have htop : Ch04.actionCommutator
        ((Subgroup.normalizerMonoidHom Q).comp (Subgroup.inclusion hQinv)) = ⊤ := by
      have h := Ch04.fixedPoints_sup_actionCommutator_eq_top
        (φ := (Subgroup.normalizerMonoidHom Q).comp (Subgroup.inclusion hQinv)) hcop
        (Or.inr inferInstance)
      rwa [hfix_bot, bot_sup_eq] at h
    have hAC := actionCommutator_conj_map_subtype hQinv
    rw [htop] at hAC
    have hQeq : Q = ⁅Q, P⁆ := by
      rw [← hAC, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    calc Q = ⁅Q, P⁆ := hQeq
      _ ≤ ⁅M, M⁆ := Subgroup.commutator_mono hQM hPM
      _ = derivedInG M := (Subgroup.map_subtype_commutator M).symm
  -- Steps 2-3: `Q ⋪ M`, so `M'` is not nilpotent (its Sylow `q` would be characteristic).
  have hM'le : derivedInG M ≤ M := Subgroup.map_subtype_le _
  have hM'nn : ¬ Group.IsNilpotent ↥(derivedInG M) := by
    intro hnil
    apply hnotMleNQ
    have hQ₀pgrp : IsPGroup q ↥(Q.subgroupOf (derivedInG M)) :=
      hQq.of_equiv (Subgroup.subgroupOfEquivOfLe hQM').symm
    have hmax : ∀ {T : Subgroup ↥(derivedInG M)}, IsPGroup q ↥T →
        Q.subgroupOf (derivedInG M) ≤ T → T = Q.subgroupOf (derivedInG M) := by
      intro T hT hle
      have hTmap_le : T.map (derivedInG M).subtype ≤ M :=
        (Subgroup.map_subtype_le T).trans hM'le
      have hTq : IsPGroup q ↥(T.map (derivedInG M).subtype) := hT.map _
      have hQle : Q ≤ T.map (derivedInG M).subtype := by
        conv_lhs => rw [← Subgroup.map_subgroupOf_eq_of_le hQM']
        exact Subgroup.map_mono hle
      have hTeq := hQsyl _ hTmap_le hTq hQle
      apply Subgroup.map_injective (derivedInG M).subtype_injective
      rw [Subgroup.map_subgroupOf_eq_of_le hQM', ← hTeq]
    let S : Sylow q ↥(derivedInG M) := ⟨Q.subgroupOf (derivedInG M), hQ₀pgrp, hmax⟩
    have htfae := (Group.isNilpotent_of_finite_tfae (G := ↥(derivedInG M))).out 0 3
    have hnormal : (Q.subgroupOf (derivedInG M)).Normal := htfae.mp hnil q ⟨Fact.out⟩ S
    have hchar : (Q.subgroupOf (derivedInG M)).Characteristic :=
      Sylow.characteristic_of_normal S hnormal
    have hNle : Subgroup.normalizer (derivedInG M : Set G) ≤
        Subgroup.normalizer (Q : Set G) := by
      have h := OddOrder.BG.AppB.normalizer_le_normalizer_map_of_characteristic
        (K := derivedInG M) (W := Q.subgroupOf (derivedInG M))
      rwa [Subgroup.map_subgroupOf_eq_of_le hQM'] at h
    exact (S10.le_normalizer_derivedInG M).trans hNle
  -- Step 4: `M_α ≠ 1` (BB4 contrapositive).
  have hαne : S10.Malpha M ≠ ⊥ := fun h => hM'nn (isNilpotent_derived_of_Malpha_eq_bot hG hM h)
  -- Step 5: `q ∉ α(M)` (else `r(Q) ≥ 3` makes `N_G(Q)` uniquely maximal — Theorem 9.6).
  have hqα : q ∉ S10.alpha M := by
    intro hqa
    apply hMNQ
    have h3 : 3 ≤ pRank ↥M q := ((S10.mem_alpha_iff M q).mp hqa).2
    have hQM_pgrp : IsPGroup q ↥(Q.subgroupOf M) :=
      hQq.of_equiv (Subgroup.subgroupOfEquivOfLe hQM).symm
    have hmaxM : ∀ {T : Subgroup ↥M}, IsPGroup q ↥T → Q.subgroupOf M ≤ T →
        T = Q.subgroupOf M := by
      intro T hT hle
      have hTmap_le : T.map M.subtype ≤ M := Subgroup.map_subtype_le T
      have hTq : IsPGroup q ↥(T.map M.subtype) := hT.map _
      have hQle : Q ≤ T.map M.subtype := by
        conv_lhs => rw [← Subgroup.map_subgroupOf_eq_of_le hQM]
        exact Subgroup.map_mono hle
      have hTeq := hQsyl _ hTmap_le hTq hQle
      apply Subgroup.map_injective M.subtype_injective
      rw [Subgroup.map_subgroupOf_eq_of_le hQM, ← hTeq]
    let S : Sylow q ↥M := ⟨Q.subgroupOf M, hQM_pgrp, hmaxM⟩
    have hrank3 : 3 ≤ rank ↥Q := by
      have e : ↥(Q.subgroupOf M) ≃* ↥Q := Subgroup.subgroupOfEquivOfLe hQM
      calc (3 : ℕ) ≤ pRank ↥M q := h3
        _ = pRank ↥(S : Subgroup ↥M) q := (pRank_sylow_eq S).symm
        _ ≤ pRank ↥Q q := pRank_le_of_injective (f := e.toMonoidHom) e.injective
        _ ≤ rank ↥Q := pRank_le_rank q
    have hQlt : Q < ⊤ := lt_of_le_of_lt hQM hMcoatom.lt_top
    have hUQ := OddOrder.BG.Ch2.S09.uniquenessTheorem hG hQlt (by omega) (Or.inl hrank3)
    have hUNQ : IsUniquelyMaximal (Subgroup.normalizer (Q : Set G)) :=
      hUQ.of_le_of_lt_top Subgroup.le_normalizer (lt_top_iff_ne_top.mpr hNQne_top)
    have huniq : hUNQ.uniqueMaximalSubgroup = M :=
      (hUQ.eq_uniqueMaximalSubgroup_of_isCoatom_of_le hUNQ.uniqueMaximalSubgroup_isCoatom
          (Subgroup.le_normalizer.trans hUNQ.le_uniqueMaximalSubgroup)).trans
        (hUQ.eq_uniqueMaximalSubgroup_of_isCoatom_of_le hMcoatom hQM).symm
    exact hUNQ.maximalSubgroupsContaining_eq_singleton.trans (by rw [huniq])
  -- Step 6: `α(M) = β(M)` (a prime `r ∈ α − β` would put `C_M(Q) ∈ 𝒰` by Corollary 10.9(a)(2)).
  have hαβ : S10.alpha M = S10.beta M := by
    apply Set.Subset.antisymm
    · intro r hra
      by_contra hrb
      have : Fact r.Prime :=
        ⟨Nat.prime_of_mem_primeFactors ((S10.mem_alpha_iff M r).mp hra).1⟩
      have hrq : r ≠ q := fun h => hqα (h ▸ hra)
      have hqβ : q ∉ S10.beta M := fun h => hqα (S10.beta_subset_alpha M h)
      have h109 :=
        (S10.beta_complement_centralizes hG hM hrq hrb hqβ hQM hQq (Or.inl hQM')).2 hra
      apply hMNQ
      have hCN : Subgroup.centralizer (Q : Set G) ⊓ M ≤ Subgroup.normalizer (Q : Set G) :=
        inf_le_left.trans (Subgroup.centralizer_le_normalizer _)
      have hUNQ : IsUniquelyMaximal (Subgroup.normalizer (Q : Set G)) :=
        h109.of_le_of_lt_top hCN (lt_top_iff_ne_top.mpr hNQne_top)
      have huniq : hUNQ.uniqueMaximalSubgroup = M :=
        (h109.eq_uniqueMaximalSubgroup_of_isCoatom_of_le hUNQ.uniqueMaximalSubgroup_isCoatom
            (hCN.trans hUNQ.le_uniqueMaximalSubgroup)).trans
          (h109.eq_uniqueMaximalSubgroup_of_isCoatom_of_le hMcoatom inf_le_right).symm
      exact hUNQ.maximalSubgroupsContaining_eq_singleton.trans (by rw [huniq])
    · exact S10.beta_subset_alpha M
  exact ⟨hαβ, hαne, hqα,
    tau1_Malpha_centralizer_P_ne_bot hG hM hqp hp hP hPM hQM hQne hQq hQinv hCQP hMNQ hαne hqα,
    tau1_Malpha_centralizer_PQ_eq_bot hG hM hqp hp hP hPM hQM hQne hQq hQinv hCQP hMNQ hqα⟩

end OddOrder.BG.Ch3.S12


