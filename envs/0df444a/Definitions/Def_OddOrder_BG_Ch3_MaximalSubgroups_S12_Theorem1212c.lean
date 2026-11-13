-- Prove2me | Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S12_Theorem1212c
-- name    : OddOrder_BG_Ch3_MaximalSubgroups_S12_Theorem1212c
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T08:07:51.579763+00:00
-- url     : https://prove2.me/theorems/d604649c-73cc-4e88-a571-c8ba31343f57
-- title:
--   BG §12: Theorem 12.12, three-case assembly
-- statement:
--   The final assembly of Theorem 12.12 of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, §12, under the hypothesis that every $(\tau_1(M)\cup\tau_3(M))$-element $e\in E^\#$ has $C_{M_\sigma}(e)=1$. The conclusion `FrobFactConclusion` (an abelian normal $A_0$, and a complement $E_0$ giving a Frobenius group $E_0M_\sigma$) is proved by three cases, the first being $\tau_2(M)=\emptyset$ ($E=E_1E_3$).
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 9 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch3_MaximalSubgroups/S12_Theorem1212c.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch3_MaximalSubgroups/S12_Theorem1212c.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S12_Theorem1212b

namespace OddOrder.BG.Ch3.S12

open OddOrder.GroupTheory

open OddOrder.Isaacs

open OddOrder.Isaacs.Ch06

open scoped Pointwise

open scoped IsMulCommutative

variable {G : Type*} [Group G]

/-- A `π`-subgroup `N` is contained in any **normal** Hall `π`-subgroup `H`. (Companion to
`Subgroup.IsPiGroup.normal_le_hall`, which assumes the *small* subgroup normal; here the *Hall*
one is normal and `N` is arbitrary.) `H ⊔ N = HN` is a `π`-group (its order divides `|H|·|N|`), so
Hall maximality forces `H ⊔ N = H`. -/
theorem isPiSubgroup_le_of_normal_isHall [Finite G] {π : Set ℕ} {H N : Subgroup G} [H.Normal]
    (hH : Ch03.IsHallSubgroup π H) (hN : Ch03.Subgroup.IsPiGroup π N) : N ≤ H := by
  have hSup_pi : Ch03.Subgroup.IsPiGroup π (H ⊔ N : Subgroup G) := by
    intro q hq
    rw [Nat.mem_primeFactors] at hq
    obtain ⟨hq_prime, hq_dvd, _⟩ := hq
    have h_card_eq : Nat.card ↥(H ⊔ N : Subgroup G) * Nat.card ↥(H ⊓ N : Subgroup G)
        = Nat.card ↥H * Nat.card ↥N := by
      have h_hk := Subgroup.card_HK_mul_card_inf_eq_card_mul_card H N
      rwa [show (↑H * ↑N : Set G) = ↑(H ⊔ N : Subgroup G) from
        (Subgroup.normal_mul H N).symm] at h_hk
    have h_dvd_prod : q ∣ Nat.card ↥H * Nat.card ↥N := by
      rw [← h_card_eq]; exact hq_dvd.mul_right _
    rcases hq_prime.dvd_mul.mp h_dvd_prod with hH_dvd | hN_dvd
    · exact hH.1 q (Nat.mem_primeFactors.mpr ⟨hq_prime, hH_dvd, Nat.card_pos.ne'⟩)
    · exact hN q (Nat.mem_primeFactors.mpr ⟨hq_prime, hN_dvd, Nat.card_pos.ne'⟩)
  have h_card_dvd : Nat.card ↥(H ⊔ N : Subgroup G) ∣ Nat.card ↥H :=
    hH.card_dvd_of_isPiGroup hSup_pi
  have h_card_eq : Nat.card ↥(H ⊔ N : Subgroup G) = Nat.card ↥H :=
    Nat.le_antisymm (Nat.le_of_dvd Nat.card_pos h_card_dvd)
      (Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective le_sup_left))
  have h_sup_eq : (H ⊔ N : Subgroup G) = H :=
    (Subgroup.eq_of_le_of_card_ge le_sup_left h_card_eq.le).symm
  intro x hx
  have hx_sup : x ∈ (H ⊔ N : Subgroup G) := Subgroup.mem_sup_right hx
  rwa [h_sup_eq] at hx_sup

/-- If `H` normalizes each `Z p` (`p ∈ T`), it normalizes their join `T.sup Z`. -/
theorem le_normalizer_finsetSup [Finite G] {H : Subgroup G} (T : Finset ℕ) (Z : ℕ → Subgroup G)
    (h : ∀ p ∈ T, H ≤ Subgroup.normalizer (Z p : Set G)) :
    H ≤ Subgroup.normalizer ((T.sup Z : Subgroup G) : Set G) := by
  classical
  induction T using Finset.induction with
  | empty =>
    rw [Finset.sup_empty]
    intro x _
    apply Subgroup.mem_normalizer_fintype
    intro n hn
    rw [Subgroup.coe_bot, Set.mem_singleton_iff] at hn ⊢
    subst hn; group
  | insert q T' hq ih =>
    rw [Finset.sup_insert]
    refine (le_inf (h q (Finset.mem_insert_self q T'))
      (ih (fun p hp => h p (Finset.mem_insert_of_mem hp)))).trans ?_
    exact Subgroup.normalizer_inf_normalizer_le_normalizer_sup _ _

/-- **Internal direct product, cardinality**: for a `Finset` `T` of primes and `Z p` a `p`-group
normalized by `H ≥ Z p`, `|T.sup Z| = ∏_{p ∈ T} |Z p|`. By `Finset.induction`, splitting off one
prime `q`: `Z q` normalizes (via `H`) the rest `T'.sup Z`, and their orders are coprime
(`|Z q|` a `q`-power, `|T'.sup Z| = ∏` a product of `p`-powers with `p ≠ q`), so
`card_sup_eq_mul_of_le_normalizer_of_disjoint` applies. -/
theorem card_finsetSup_eq_prod [Finite G] {H : Subgroup G} (T : Finset ℕ) (Z : ℕ → Subgroup G)
    (hTp : ∀ p ∈ T, p.Prime) (hZH : ∀ p ∈ T, Z p ≤ H)
    (hZnorm : ∀ p ∈ T, H ≤ Subgroup.normalizer (Z p : Set G))
    (hZpg : ∀ p ∈ T, IsPGroup p ↥(Z p)) :
    Nat.card ↥(T.sup Z) = ∏ p ∈ T, Nat.card ↥(Z p) := by
  classical
  induction T using Finset.induction with
  | empty => simp
  | insert q T' hq ih =>
    have hqmem : q ∈ insert q T' := Finset.mem_insert_self q T'
    have hsubT' : ∀ {p}, p ∈ T' → p ∈ insert q T' := fun hp => Finset.mem_insert_of_mem hp
    have : Fact q.Prime := ⟨hTp q hqmem⟩
    have hcardT' : Nat.card ↥(T'.sup Z) = ∏ p ∈ T', Nat.card ↥(Z p) :=
      ih (fun p hp => hTp p (hsubT' hp)) (fun p hp => hZH p (hsubT' hp))
        (fun p hp => hZnorm p (hsubT' hp)) (fun p hp => hZpg p (hsubT' hp))
    -- `Z q` normalizes the join of the rest.
    have hqN : Z q ≤ Subgroup.normalizer ((T'.sup Z : Subgroup G) : Set G) :=
      (hZH q hqmem).trans (le_normalizer_finsetSup T' Z (fun p hp => hZnorm p (hsubT' hp)))
    -- coprimality of orders.
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp (hZpg q hqmem)
    have hcop : Nat.Coprime (Nat.card ↥(Z q)) (Nat.card ↥(T'.sup Z : Subgroup G)) := by
      rw [hm, hcardT']
      refine Nat.Coprime.pow_left _ (Nat.Coprime.prod_right fun p hp => ?_)
      have : Fact p.Prime := ⟨hTp p (hsubT' hp)⟩
      obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp (hZpg p (hsubT' hp))
      rw [hk]
      exact Nat.Coprime.pow_right _
        ((Nat.coprime_primes (hTp q hqmem) (hTp p (hsubT' hp))).mpr (fun he => hq (he ▸ hp)))
    have hdisj : Z q ⊓ (T'.sup Z : Subgroup G) = ⊥ :=
      (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
    rw [Finset.sup_insert, card_sup_eq_mul_of_le_normalizer_of_disjoint hqN hdisj, hcardT',
      Finset.prod_insert hq]

/-- **Internal direct product, components**: an element `a ∈ T.sup Z` of prime order `r ∈ T` lies
in `Z r`. Indeed `Z r ⊴ T.sup Z` (normalized via `H`), and `[T.sup Z : Z r] = ∏_{p ≠ r} |Z p|` is
coprime to `r` (cardinality `card_finsetSup_eq_prod`), so the image of `a` in the quotient has
order dividing both `r` and an `r'`-number, hence is trivial: `a ∈ Z r`. -/
theorem mem_Z_of_orderOf_prime_mem [Finite G] {H : Subgroup G} (T : Finset ℕ) (Z : ℕ → Subgroup G)
    (hTp : ∀ p ∈ T, p.Prime) (hZH : ∀ p ∈ T, Z p ≤ H)
    (hZnorm : ∀ p ∈ T, H ≤ Subgroup.normalizer (Z p : Set G))
    (hZpg : ∀ p ∈ T, IsPGroup p ↥(Z p))
    {r : ℕ} (hr : r ∈ T) {a : G} (ha : a ∈ T.sup Z) (har : orderOf a = r) :
    a ∈ Z r := by
  classical
  have : Fact r.Prime := ⟨hTp r hr⟩
  have hZrle : Z r ≤ T.sup Z := Finset.le_sup hr
  have hnorm : (T.sup Z : Subgroup G) ≤ Subgroup.normalizer (Z r : Set G) :=
    (Finset.sup_le hZH).trans (hZnorm r hr)
  set K' : Subgroup ↥(T.sup Z) := (Z r).subgroupOf (T.sup Z) with hK'
  have : K'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hZrle).mpr hnorm
  set a' : ↥(T.sup Z) := ⟨a, ha⟩ with ha'
  have hord_a' : orderOf a' = r := (Subgroup.orderOf_coe a').symm.trans har
  -- `[T.sup Z : Z r] = ∏_{p ∈ T.erase r} |Z p|`, coprime to `r`.
  have hcofactor : Nat.card (↥(T.sup Z) ⧸ K') = ∏ p ∈ T.erase r, Nat.card ↥(Z p) := by
    have hK'card : Nat.card ↥K' = Nat.card ↥(Z r) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZrle).toEquiv
    have hlag := Subgroup.card_eq_card_quotient_mul_card_subgroup K'
    rw [hK'card, card_finsetSup_eq_prod T Z hTp hZH hZnorm hZpg,
      ← Finset.mul_prod_erase T (fun p => Nat.card ↥(Z p)) hr, mul_comm] at hlag
    exact (Nat.eq_of_mul_eq_mul_right Nat.card_pos hlag.symm)
  have hcop : Nat.Coprime r (∏ p ∈ T.erase r, Nat.card ↥(Z p)) := by
    refine Nat.Coprime.prod_right fun p hp => ?_
    have hpT : p ∈ T := Finset.mem_of_mem_erase hp
    have : Fact p.Prime := ⟨hTp p hpT⟩
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp (hZpg p hpT)
    rw [hk]
    exact Nat.Coprime.pow_right _
      ((Nat.coprime_primes (hTp r hr) (hTp p hpT)).mpr (Finset.ne_of_mem_erase hp).symm)
  -- the image of `a` in the quotient is trivial.
  have hdvdr : orderOf (QuotientGroup.mk' K' a') ∣ r :=
    hord_a' ▸ orderOf_map_dvd (QuotientGroup.mk' K') a'
  have hdvdc : orderOf (QuotientGroup.mk' K' a') ∣ ∏ p ∈ T.erase r, Nat.card ↥(Z p) :=
    hcofactor ▸ orderOf_dvd_natCard _
  have hone : orderOf (QuotientGroup.mk' K' a') = 1 :=
    Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd hdvdr hdvdc)
  have : a' ∈ K' := QuotientGroup.eq_one_iff _ |>.mp (orderOf_eq_one_iff.mp hone)
  exact Subgroup.mem_subgroupOf.mp this

/-- **Per-prime `Z_p` extraction** for the abelian-Sylow case (`p ∈ τ₂(M)`). Combining
`exists_elemAb_rank_two_le_E_of_tau2`, the Sylow extension `A ≤ S`, the abelianness `habel`, the
Lemma 12.8(c) chain (`sylow_chain_of_abelianSylow`, giving `S ≤ E`), and the per-prime capstone
`exists_cyclic_Enormal_regular_of_abelianSylow`, we obtain a cyclic `p`-subgroup `Z ≤ E`,
normalized by `E`, of the same exponent as a Sylow `p`-subgroup `S ≤ E`, acting regularly on
`M_σ`. (`Z ⊴ E` follows from `E ≤ N_G(Z)`; the `Z_p` for distinct `p ∈ τ₂(M)` will assemble into
an internal direct product `∏ Z_p ≤ E`.) -/
theorem exists_regular_cyclic_of_mem_tau2 [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ tau2 M)
    (habel : ∀ S : Sylow p G, IsMulCommutative ↥(S : Subgroup G))
    (hreg : ∀ e ∈ E, e ≠ 1 → (∀ r ∈ (orderOf e).primeFactors, r ∈ tau1 M ∪ tau3 M) →
      S10.Msigma M ⊓ Subgroup.centralizer ({e} : Set G) = ⊥) :
    ∃ Z : Subgroup G, Z ≤ E ∧ IsCyclic ↥Z ∧ Z ≠ ⊥ ∧ IsPGroup p ↥Z ∧
      E ≤ Subgroup.normalizer (Z : Set G) ∧
      (∃ S : Sylow p G, (S : Subgroup G) ≤ E ∧
        Monoid.exponent ↥Z = Monoid.exponent ↥(S : Subgroup G)) ∧
      ∀ z ∈ Z, z ≠ 1 → S10.Msigma M ⊓ Subgroup.centralizer ({z} : Set G) = ⊥ := by
  obtain ⟨A, hA, hAE⟩ := exists_elemAb_rank_two_le_E_of_tau2 hG h hp
  obtain ⟨S, hAS⟩ := hA.1.isPGroup.exists_le_sylow
  have hSab : IsMulCommutative ↥(S : Subgroup G) := habel S
  have hSE : (S : Subgroup G) ≤ E :=
    (le_centralizer_of_le_of_le hSab le_rfl hAS).trans (centralizer_le_E_of_tau2 hG h hp hA hAE).1
  have hSM : (S : Subgroup G) ≤ M := hSE.trans h.E_le
  obtain ⟨Z, hZS, hZcyc, hZne, hZN, hZexp, hZreg⟩ :=
    exists_cyclic_Enormal_regular_of_abelianSylow hG h hp hA hAE hAS hSM hSab hreg
  exact ⟨Z, hZS.trans hSE, hZcyc, hZne, S.isPGroup'.to_le hZS, hZN, ⟨S, hSE, hZexp⟩, hZreg⟩

/-- **BG Theorem 12.12, Case 3, part (a)** (mmd L3345 "Obviously `A₀ = E₂` satisfies (a)"):
in the abelian-Sylow regime, `A₀ = E₂` is an abelian normal subgroup of `E` (Lemma 12.8(a)) with
`C_E(x) ⊆ E₂` for every `x ∈ M_σ#`. The containment holds because `C_E(x)` is a `τ₂(M)`-group:
any prime `q ∣ |C_E(x)|` with `q ∈ τ₁(M) ∪ τ₃(M)` would give an element `a ∈ E#` of order `q`
centralizing `x`, so `x ∈ M_σ ⊓ C_G(a) = 1` by `hreg`, contradiction; hence `q ∈ τ₂(M)`, and the
`τ₂`-subgroup `C_E(x)` lies in the normal Hall `τ₂`-subgroup `E₂`. -/
theorem frobFact_partA_of_abelianSylow [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    (hτ2 : ∃ p ∈ (Nat.card ↥E).primeFactors, p ∈ tau2 M)
    (habel : ∀ q, q ∈ (Nat.card ↥E).primeFactors → q ∈ tau2 M →
      ∀ S : Sylow q G, IsMulCommutative ↥(S : Subgroup G))
    (hreg : ∀ e ∈ E, e ≠ 1 → (∀ r ∈ (orderOf e).primeFactors, r ∈ tau1 M ∪ tau3 M) →
      S10.Msigma M ⊓ Subgroup.centralizer ({e} : Set G) = ⊥) :
    ∃ A₀ : Subgroup G, A₀ ≤ E ∧ IsMulCommutative ↥A₀ ∧
      E ≤ Subgroup.normalizer ((A₀ : Subgroup G) : Set G) ∧
      ∀ x ∈ S10.Msigma M, x ≠ 1 → E ⊓ Subgroup.centralizer ({x} : Set G) ≤ A₀ := by
  classical
  obtain ⟨p, hpE, hp⟩ := hτ2
  have : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hpE⟩
  obtain ⟨A, hA, hAE⟩ := exists_elemAb_rank_two_le_E_of_tau2 hG h hp
  obtain ⟨S, hAS⟩ := hA.1.isPGroup.exists_le_sylow
  have hSab : IsMulCommutative ↥(S : Subgroup G) := habel p hpE hp S
  obtain ⟨⟨hE₂ab, hE₂norm⟩, _⟩ := E2_abelian_of_abelianSylow hG h hp hA hAE S hAS hSab
  refine ⟨E₂, h.E₂_le, hE₂ab, hE₂norm, ?_⟩
  intro x hxMσ hxne
  -- `C_E(x) = E ⊓ C_G(x)` is a `τ₂`-subgroup of `E`; the normal Hall `τ₂`-subgroup `E₂` contains
  -- it.
  have : ((E₂).subgroupOf E).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.E₂_le).mpr hE₂norm
  have hpi : Ch03.Subgroup.IsPiGroup (tau2 M)
      ((E ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf E) := by
    intro q hq
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv] at hq
    obtain ⟨hqp, hqd, _⟩ := Nat.mem_primeFactors.mp hq
    have : Fact q.Prime := ⟨hqp⟩
    have hqE : q ∈ (Nat.card ↥E).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hqp, hqd.trans (Subgroup.card_dvd_of_le inf_le_left),
        Nat.card_pos.ne'⟩
    by_contra hqnτ2
    obtain ⟨a, ha_ord⟩ := exists_prime_orderOf_dvd_card' (G := ↥(E ⊓ Subgroup.centralizer
      ({x} : Set G))) q hqd
    have haE : (a : G) ∈ E := (Subgroup.mem_inf.mp a.2).1
    have haCx : (a : G) ∈ Subgroup.centralizer ({x} : Set G) := (Subgroup.mem_inf.mp a.2).2
    have hane : (a : G) ≠ 1 := by
      intro hc
      rw [← Subgroup.orderOf_coe, hc, orderOf_one] at ha_ord
      exact hqp.ne_one ha_ord.symm
    have ha_ordG : orderOf (a : G) = q := by rw [Subgroup.orderOf_coe]; exact ha_ord
    have hq13 : q ∈ tau1 M ∪ tau3 M := by
      rcases h.mem_tau_union_of_mem_primeFactors hG hqE with (h1 | h2) | h3
      · exact Or.inl h1
      · exact absurd h2 hqnτ2
      · exact Or.inr h3
    have hreg_a : S10.Msigma M ⊓ Subgroup.centralizer ({(a : G)} : Set G) = ⊥ := by
      refine hreg (a : G) haE hane ?_
      intro r hr
      rw [ha_ordG, hqp.primeFactors, Finset.mem_singleton] at hr
      rwa [hr]
    have hxmem : x ∈ S10.Msigma M ⊓ Subgroup.centralizer ({(a : G)} : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨hxMσ, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro m hm
      rw [Set.mem_singleton_iff] at hm; subst hm
      exact (Subgroup.mem_centralizer_iff.mp haCx x (Set.mem_singleton x)).symm
    rw [hreg_a, Subgroup.mem_bot] at hxmem
    exact hxne hxmem
  have hle := isPiSubgroup_le_of_normal_isHall (H := (E₂).subgroupOf E)
    (N := (E ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf E) h.E₂_hall hpi
  intro y hy
  have hyE : y ∈ E := (Subgroup.mem_inf.mp hy).1
  have : (⟨y, hyE⟩ : ↥E) ∈ (E₂).subgroupOf E := hle (Subgroup.mem_subgroupOf.mpr hy)
  exact Subgroup.mem_subgroupOf.mp this

/-- **The `τ₂`-product `ZZ = ∏_{p ∈ τ₂(M)} Z_p`** for the abelian-Sylow case. Choosing for each
prime `p ∈ τ₂(M) ∩ π(E)` a regular cyclic `Z_p` (`exists_regular_cyclic_of_mem_tau2`), their join
`ZZ` is: `≤ E`, nontrivial, normalized by `E`, a `τ₂(M)`-group, **regular on `M_σ`** (every
nonidentity element — by `inf_centralizer_eq_bot_of_forall_prime_order` reducing to prime order,
then `mem_Z_of_orderOf_prime_mem` placing it in some regular `Z_r`), and it realizes the `τ₂`-part
of `exp(E)` (`v_r(exp E) ≤ v_r(exp ZZ)` for `r ∈ τ₂(M)`, since `exp(Z_r) = exp(Sylow_r E)` divides
`exp ZZ`). -/
theorem exists_tau2_product [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    (hτ2 : ∃ p ∈ (Nat.card ↥E).primeFactors, p ∈ tau2 M)
    (habel : ∀ q, q ∈ (Nat.card ↥E).primeFactors → q ∈ tau2 M →
      ∀ S : Sylow q G, IsMulCommutative ↥(S : Subgroup G))
    (hreg : ∀ e ∈ E, e ≠ 1 → (∀ r ∈ (orderOf e).primeFactors, r ∈ tau1 M ∪ tau3 M) →
      S10.Msigma M ⊓ Subgroup.centralizer ({e} : Set G) = ⊥) :
    ∃ ZZ : Subgroup G, ZZ ≤ E ∧ ZZ ≠ ⊥ ∧ E ≤ Subgroup.normalizer (ZZ : Set G) ∧
      Ch03.Subgroup.IsPiGroup (tau2 M) ZZ ∧
      (∀ a ∈ ZZ, a ≠ 1 → S10.Msigma M ⊓ Subgroup.centralizer ({a} : Set G) = ⊥) ∧
      (∀ r ∈ tau2 M,
        (Monoid.exponent ↥E).factorization r ≤ (Monoid.exponent ↥ZZ).factorization r) := by
  classical
  set T : Finset ℕ := (Nat.card ↥E).primeFactors.filter (· ∈ tau2 M) with hTdef
  have hTp : ∀ p ∈ T, p.Prime := fun p hp =>
    Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
  have hTτ2 : ∀ p ∈ T, p ∈ tau2 M := fun p hp => (Finset.mem_filter.mp hp).2
  have hTpf : ∀ p ∈ T, p ∈ (Nat.card ↥E).primeFactors := fun p hp => (Finset.mem_filter.mp hp).1
  have hex : ∀ p ∈ T, ∃ Z : Subgroup G, Z ≤ E ∧ IsCyclic ↥Z ∧ Z ≠ ⊥ ∧ IsPGroup p ↥Z ∧
      E ≤ Subgroup.normalizer (Z : Set G) ∧
      (∃ S : Sylow p G, (S : Subgroup G) ≤ E ∧
        Monoid.exponent ↥Z = Monoid.exponent ↥(S : Subgroup G)) ∧
      ∀ z ∈ Z, z ≠ 1 → S10.Msigma M ⊓ Subgroup.centralizer ({z} : Set G) = ⊥ := by
    intro p hp
    have : Fact p.Prime := ⟨hTp p hp⟩
    exact exists_regular_cyclic_of_mem_tau2 hG h (hTτ2 p hp) (habel p (hTpf p hp) (hTτ2 p hp)) hreg
  choose! Zf hZfE hZfcyc hZfne hZfpg hZfN hZfSyl hZfreg using hex
  set ZZ : Subgroup G := T.sup Zf with hZZdef
  have hZZE : ZZ ≤ E := Finset.sup_le hZfE
  have hZZN : E ≤ Subgroup.normalizer (ZZ : Set G) := le_normalizer_finsetSup T Zf hZfN
  obtain ⟨p₀, hp₀E, hp₀τ2⟩ := hτ2
  have hp₀T : p₀ ∈ T := by rw [hTdef, Finset.mem_filter]; exact ⟨hp₀E, hp₀τ2⟩
  have hZZne : ZZ ≠ ⊥ := fun hbot => hZfne p₀ hp₀T (le_bot_iff.mp (hbot ▸ Finset.le_sup hp₀T))
  have hZZcard : Nat.card ↥ZZ = ∏ p ∈ T, Nat.card ↥(Zf p) :=
    card_finsetSup_eq_prod T Zf hTp hZfE hZfN hZfpg
  -- the prime divisors of `|ZZ|` are exactly the primes of `T`, all in `τ₂(M)`.
  have hprimeT : ∀ {q : ℕ}, q.Prime → q ∣ Nat.card ↥ZZ → q ∈ T := by
    intro q hqp hqd
    rw [hZZcard] at hqd
    obtain ⟨p, hpT, hqdp⟩ := (Nat.Prime.prime hqp).exists_mem_finset_dvd hqd
    have : Fact p.Prime := ⟨hTp p hpT⟩
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp (hZfpg p hpT)
    rw [hk] at hqdp
    rwa [(Nat.prime_dvd_prime_iff_eq hqp (hTp p hpT)).mp (hqp.dvd_of_dvd_pow hqdp)]
  have hZZpi : Ch03.Subgroup.IsPiGroup (tau2 M) ZZ := by
    intro q hq
    obtain ⟨hqp, hqd, _⟩ := Nat.mem_primeFactors.mp hq
    exact hTτ2 _ (hprimeT hqp hqd)
  have hZZreg : ∀ a ∈ ZZ, a ≠ 1 → S10.Msigma M ⊓ Subgroup.centralizer ({a} : Set G) = ⊥ := by
    refine inf_centralizer_eq_bot_of_forall_prime_order ?_
    intro a haZZ harp
    have hrdvd : orderOf a ∣ Nat.card ↥ZZ := ZZ.orderOf_dvd_natCard haZZ
    have hrT : orderOf a ∈ T := hprimeT harp hrdvd
    have haZf : a ∈ Zf (orderOf a) :=
      mem_Z_of_orderOf_prime_mem T Zf hTp hZfE hZfN hZfpg hrT haZZ rfl
    exact hZfreg (orderOf a) hrT a haZf
      (fun hc => by rw [hc, orderOf_one] at harp; exact harp.ne_one rfl)
  refine ⟨ZZ, hZZE, hZZne, hZZN, hZZpi, hZZreg, ?_⟩
  intro r hrτ2
  by_cases hrp : r.Prime
  · by_cases hrE : r ∈ (Nat.card ↥E).primeFactors
    · have hrT : r ∈ T := by rw [hTdef, Finset.mem_filter]; exact ⟨hrE, hrτ2⟩
      have : Fact r.Prime := ⟨hrp⟩
      obtain ⟨S, hSE, hexpZS⟩ := hZfSyl r hrT
      have hScard : Nat.card ↥((S : Subgroup G).subgroupOf E) =
          r ^ (Nat.card ↥E).factorization r := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSE).toEquiv, S.card_eq_multiplicity]
        congr 1
        refine Nat.le_antisymm ?_
          ((Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr
            (Subgroup.card_subgroup_dvd_card E) r)
        rw [← Nat.Prime.pow_dvd_iff_le_factorization hrp Nat.card_pos.ne', ← S.card_eq_multiplicity]
        exact Subgroup.card_dvd_of_le hSE
      have h1 := factorization_exponent_le_of_sylow hSE hScard
      have hexp_ne : Monoid.exponent ↥ZZ ≠ 0 := fun hz =>
        Nat.card_pos.ne' (Nat.eq_zero_of_zero_dvd (hz ▸ Group.exponent_dvd_nat_card))
      have hexpZ_ne : Monoid.exponent ↥(Zf r) ≠ 0 := fun hz =>
        Nat.card_pos.ne' (Nat.eq_zero_of_zero_dvd (hz ▸ Group.exponent_dvd_nat_card))
      have hdvd : Monoid.exponent ↥(Zf r) ∣ Monoid.exponent ↥ZZ :=
        Monoid.exponent_dvd_of_monoidHom (Subgroup.inclusion (Finset.le_sup hrT))
          (Subgroup.inclusion_injective _)
      calc (Monoid.exponent ↥E).factorization r
          ≤ (Monoid.exponent ↥(S : Subgroup G)).factorization r := h1
        _ = (Monoid.exponent ↥(Zf r)).factorization r := by rw [hexpZS]
        _ ≤ (Monoid.exponent ↥ZZ).factorization r :=
            (Finsupp.le_def.mp ((Nat.factorization_le_iff_dvd hexpZ_ne hexp_ne).mpr hdvd)) r
    · have hr0 : (Monoid.exponent ↥E).factorization r = 0 := by
        rw [Nat.factorization_eq_zero_iff]
        refine Or.inr (Or.inl fun hdvd => hrE ?_)
        exact Nat.mem_primeFactors.mpr ⟨hrp, hdvd.trans Group.exponent_dvd_nat_card,
          Nat.card_pos.ne'⟩
      omega
  · rw [Nat.factorization_eq_zero_of_not_prime _ hrp]; omega

/-- **BG Theorem 12.12, Case 3** (mmd L3344-3373): in the abelian-Sylow regime, with `τ₂(M)`
nonempty, the conclusion `FrobFactConclusion M E` holds. Here `A₀ = E₂` (abelian normal Hall
`τ₂`-subgroup of `E`, by Lemma 12.8(a)), and `E₀ = E₁E₃ · ∏_{p ∈ τ₂} Z_p`, where each `Z_p` is a
cyclic normal subgroup of `E` of the same exponent as a Sylow `p`-subgroup `S_p ≤ E` and acting
regularly on `M_σ` (`exists_cyclic_Enormal_regular_of_abelianSylow`).

`habel` provides that every Sylow `p`-subgroup of `G` (for `p ∈ τ₂(M)` dividing `|E|`) is abelian;
`hτ2` witnesses the nonemptiness of `τ₂(M) ∩ π(E)`.

`E₀ = ZZ ⊔ K`, where `ZZ` (`exists_tau2_product`) is the `τ₂`-product (regular, realizing the
`τ₂`-part of `exp E`) and `K` is a Hall `τ₂(M)'`-subgroup of `E` (realizing the `τ₂'`-part). The
regularity of `E₀` reduces (`inf_centralizer_eq_bot_of_forall_prime_order`) to prime-order `a`:
a `τ₂`-element lies in `ZZ` (its image in `E₀/ZZ`, a `τ₂'`-group, is trivial) hence is regular,
while a `(τ₁∪τ₃)`-element uses `hreg`. -/
theorem frobFact_of_abelianSylow [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    (hτ2 : ∃ p ∈ (Nat.card ↥E).primeFactors, p ∈ tau2 M)
    (habel : ∀ q, q ∈ (Nat.card ↥E).primeFactors → q ∈ tau2 M →
      ∀ S : Sylow q G, IsMulCommutative ↥(S : Subgroup G))
    (hreg : ∀ e ∈ E, e ≠ 1 → (∀ r ∈ (orderOf e).primeFactors, r ∈ tau1 M ∪ tau3 M) →
      S10.Msigma M ⊓ Subgroup.centralizer ({e} : Set G) = ⊥) :
    FrobFactConclusion M E := by
  classical
  obtain ⟨ZZ, hZZE, hZZne, hZZN, hZZpi, hZZreg, hZZexp⟩ := exists_tau2_product hG h hτ2 habel hreg
  have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups h.mem_maximal
  have : Group.IsSolvable ↥E :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective h.E_le)
  -- `K` = a Hall `τ₂(M)'`-subgroup of `E`.
  obtain ⟨K', hK'hall⟩ := Ch03.hall_E_exists (G := ↥E) ((tau2 M)ᶜ)
  set K : Subgroup G := K'.map E.subtype with hKdef
  have hKE : K ≤ E := Subgroup.map_subtype_le _
  have hKcard : Nat.card ↥K = Nat.card ↥K' :=
    Subgroup.card_map_of_injective E.subtype_injective
  have hKpi : ∀ p ∈ (Nat.card ↥K).primeFactors, p ∉ tau2 M := by
    intro p hp; rw [hKcard] at hp; exact hK'hall.1 p hp
  -- `ZZ ⊓ K = ⊥` by coprimality (`ZZ` a `τ₂`-group, `K` a `τ₂'`-group).
  have hcop : Nat.Coprime (Nat.card ↥ZZ) (Nat.card ↥K) :=
    Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl Nat.card_pos.ne' Nat.card_pos.ne' hZZpi hKpi
  have hZZKdisj : ZZ ⊓ K = ⊥ := (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
  -- `E₀ = ZZ ⊔ K`.
  set E₀ : Subgroup G := ZZ ⊔ K with hE₀def
  have hE₀E : E₀ ≤ E := sup_le hZZE hKE
  have hKNZZ : K ≤ Subgroup.normalizer (ZZ : Set G) := hKE.trans hZZN
  have hE₀card : Nat.card ↥E₀ = Nat.card ↥ZZ * Nat.card ↥K := by
    rw [hE₀def, sup_comm,
      card_sup_eq_mul_of_le_normalizer_of_disjoint hKNZZ (by rw [inf_comm]; exact hZZKdisj),
      Nat.mul_comm]
  have hZZE₀ : ZZ ≤ E₀ := le_sup_left
  have hE₀NZZ : E₀ ≤ Subgroup.normalizer (ZZ : Set G) := hE₀E.trans hZZN
  have : (ZZ.subgroupOf E₀).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hZZE₀).mpr hE₀NZZ
  have hE₀ne : E₀ ≠ ⊥ := fun hbot => hZZne (le_bot_iff.mp (hbot ▸ hZZE₀))
  -- **Part (b) regularity**: every nonidentity element of `E₀` is regular on `M_σ`.
  have hE₀reg : ∀ a ∈ E₀, a ≠ 1 → S10.Msigma M ⊓ Subgroup.centralizer ({a} : Set G) = ⊥ := by
    refine inf_centralizer_eq_bot_of_forall_prime_order ?_
    intro a haE₀ harp
    have hane : a ≠ 1 := fun hc => by rw [hc, orderOf_one] at harp; exact harp.ne_one rfl
    have haE : a ∈ E := hE₀E haE₀
    by_cases hrτ2 : orderOf a ∈ tau2 M
    · -- `a`'s image in `E₀ / ZZ` (a `τ₂'`-group) is trivial, so `a ∈ ZZ`.
      have hquotcard : Nat.card (↥E₀ ⧸ ZZ.subgroupOf E₀) = Nat.card ↥K := by
        have hlag := Subgroup.card_eq_card_quotient_mul_card_subgroup (ZZ.subgroupOf E₀)
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZZE₀).toEquiv, hE₀card] at hlag
        exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (hlag.symm.trans (Nat.mul_comm _ _))
      set a' : ↥E₀ := ⟨a, haE₀⟩ with ha'
      have hcopK : Nat.Coprime (orderOf a) (Nat.card ↥K) :=
        (Nat.Prime.coprime_iff_not_dvd harp).mpr fun hd =>
          hKpi (orderOf a) (Nat.mem_primeFactors.mpr ⟨harp, hd, Nat.card_pos.ne'⟩) hrτ2
      have hone : orderOf (QuotientGroup.mk' (ZZ.subgroupOf E₀) a') = 1 := by
        have hdr : orderOf (QuotientGroup.mk' (ZZ.subgroupOf E₀) a') ∣ orderOf a :=
          ((Subgroup.orderOf_coe a').symm ▸ orderOf_map_dvd (QuotientGroup.mk' _) a')
        have hdK : orderOf (QuotientGroup.mk' (ZZ.subgroupOf E₀) a') ∣ Nat.card ↥K :=
          hquotcard ▸ orderOf_dvd_natCard _
        exact Nat.dvd_one.mp (hcopK ▸ Nat.dvd_gcd hdr hdK)
      have haZZ : a ∈ ZZ :=
        Subgroup.mem_subgroupOf.mp (QuotientGroup.eq_one_iff _ |>.mp (orderOf_eq_one_iff.mp hone))
      exact hZZreg a haZZ hane
    · -- `orderOf a ∈ τ₁(M) ∪ τ₃(M)`: `hreg` applies directly.
      refine hreg a haE hane fun s hs => ?_
      rw [harp.primeFactors, Finset.mem_singleton] at hs
      subst hs
      have hsE : orderOf a ∈ (Nat.card ↥E).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨harp, E.orderOf_dvd_natCard haE, Nat.card_pos.ne'⟩
      rcases h.mem_tau_union_of_mem_primeFactors hG hsE with (h1 | h2) | h3
      · exact Or.inl h1
      · exact absurd h2 hrτ2
      · exact Or.inr h3
  -- **Part (b) exponent**: `exp(E₀) = exp(E)`.
  have hexp : Monoid.exponent ↥E₀ = Monoid.exponent ↥E := by
    refine exponent_eq_of_forall_factorization_le hE₀E fun r hrp => ?_
    have : Fact r.Prime := ⟨hrp⟩
    by_cases hrτ2 : r ∈ tau2 M
    · -- `τ₂`-part realized inside `ZZ`.
      obtain ⟨g, hg⟩ := hrp.exists_orderOf_eq_pow_factorization_exponent ↥ZZ
      refine ⟨Subgroup.inclusion hZZE₀ g, ?_⟩
      rw [orderOf_injective (Subgroup.inclusion hZZE₀) (Subgroup.inclusion_injective _) g, hg,
        Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, Nat.Prime.factorization_self hrp,
        mul_one]
      exact hZZexp r hrτ2
    · -- `τ₂'`-part realized inside `K ⊇ Sylow_r(E)`.
      have hKr : (Nat.card ↥K).factorization r = (Nat.card ↥E).factorization r := by
        have hmul := Subgroup.card_mul_index K'
        have hidx : (K'.index).factorization r = 0 := by
          rw [Nat.factorization_eq_zero_iff]
          exact Or.inr (Or.inl fun hd => hK'hall.2 r
            (Nat.mem_primeFactors.mpr ⟨hrp, hd, Subgroup.index_ne_zero_of_finite⟩) hrτ2)
        have := congrArg (fun n => n.factorization r) hmul
        simp only [Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite,
          Finsupp.add_apply, hidx, add_zero] at this
        rw [hKcard]; exact this
      set P : Sylow r ↥K := default with hP
      have hPcard : Nat.card ↥((P : Subgroup ↥K).map K.subtype) =
          r ^ (Nat.card ↥E).factorization r := by
        rw [Subgroup.card_map_of_injective K.subtype_injective, P.card_eq_multiplicity, hKr]
      have hPE : (P : Subgroup ↥K).map K.subtype ≤ E := (Subgroup.map_subtype_le _).trans hKE
      have hPcard' : Nat.card ↥(((P : Subgroup ↥K).map K.subtype).subgroupOf E) =
          r ^ (Nat.card ↥E).factorization r := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPE).toEquiv, hPcard]
      have h1 := factorization_exponent_le_of_sylow hPE hPcard'
      obtain ⟨g, hg⟩ := hrp.exists_orderOf_eq_pow_factorization_exponent
        ↥((P : Subgroup ↥K).map K.subtype)
      have hPE₀ : (P : Subgroup ↥K).map K.subtype ≤ E₀ :=
        (Subgroup.map_subtype_le _).trans le_sup_right
      refine ⟨Subgroup.inclusion hPE₀ g, ?_⟩
      rw [orderOf_injective (Subgroup.inclusion hPE₀) (Subgroup.inclusion_injective _) g, hg,
        Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, Nat.Prime.factorization_self hrp,
        mul_one]
      exact h1
  -- **Part (a)** and assembly.
  obtain ⟨A₀, hA₀⟩ := frobFact_partA_of_abelianSylow hG h hτ2 habel hreg
  exact ⟨⟨A₀, hA₀⟩, E₀, hE₀E, hexp, isFrobeniusGroup_of_regular hG h hE₀E hE₀ne hE₀reg⟩

/-- **BG Theorem 12.12** (mmd L3336): suppose `C_{M_σ}(e) = 1` for every
`(τ₁(M) ∪ τ₃(M))`-element `e ∈ E#`. Then
(a) `E` contains an abelian normal subgroup `A₀` with `C_E(x) ⊆ A₀` for all `x ∈ M_σ#`, and
(b) `E` contains a subgroup `E₀` of the same exponent as `E` such that `E₀ M_σ` is a Frobenius
group with Frobenius kernel `M_σ`.

(Scaffold moved here from `S12_E.lean`.) Proof by the three-case split described in the file
header. The case selector is whether some `τ₂(M)`-prime dividing `|E|` has a nonabelian Sylow
`p`-subgroup in `G`. -/
theorem frobenius_factorization_of_regular [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    (hreg : ∀ e ∈ E, e ≠ 1 → (∀ r ∈ (orderOf e).primeFactors, r ∈ tau1 M ∪ tau3 M) →
      S10.Msigma M ⊓ Subgroup.centralizer ({e} : Set G) = ⊥) :
    FrobFactConclusion M E := by
  by_cases hnonab : ∃ p ∈ (Nat.card ↥E).primeFactors, p ∈ tau2 M ∧
      ∃ S : Sylow p G, ¬ IsMulCommutative ↥(S : Subgroup G)
  · -- **Case 2**: a `τ₂`-prime with a nonabelian Sylow.
    obtain ⟨p, hpE, hp, hS⟩ := hnonab
    have : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hpE⟩
    obtain ⟨A, hA, hAE⟩ := exists_elemAb_rank_two_le_E_of_tau2 hG h hp
    exact frobFact_of_nonabelianSylow hG h hp hA hAE hS hreg
  · -- No `τ₂`-prime has a nonabelian Sylow: all relevant Sylows are abelian.
    have habel : ∀ q, q ∈ (Nat.card ↥E).primeFactors → q ∈ tau2 M →
        ∀ S : Sylow q G, IsMulCommutative ↥(S : Subgroup G) := by
      intro q hqE hq S
      by_contra hc
      exact hnonab ⟨q, hqE, hq, S, hc⟩
    by_cases hτ2 : ∃ p ∈ (Nat.card ↥E).primeFactors, p ∈ tau2 M
    · -- **Case 3**: `τ₂(M) ≠ ∅`, abelian Sylows.
      exact frobFact_of_abelianSylow hG h hτ2 habel hreg
    · -- **Case 1**: no `τ₂`-prime divides `|E|`, so `E = E₁E₃` and `hreg` is unconditional.
      refine frobFact_of_regular_all hG h (h.E_ne_bot hG) ?_
      intro e heE hene
      refine hreg e heE hene ?_
      intro r hr
      obtain ⟨hrp, hrd, _⟩ := Nat.mem_primeFactors.mp hr
      have hrE : r ∈ (Nat.card ↥E).primeFactors := by
        exact Nat.mem_primeFactors.mpr ⟨hrp, hrd.trans (E.orderOf_dvd_natCard heE),
            Nat.card_pos.ne'⟩
      have hru : r ∈ tau1 M ∪ tau2 M ∪ tau3 M :=
        h.mem_tau_union_of_mem_primeFactors hG hrE
      have hrnτ2 : r ∉ tau2 M := fun hr2 => hτ2 ⟨r, hrE, hr2⟩
      rcases hru with (h1 | h2) | h3
      · exact Or.inl h1
      · exact absurd h2 hrnτ2
      · exact Or.inr h3

end OddOrder.BG.Ch3.S12


