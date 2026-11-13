-- Prove2me | Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S12_Theorem1212b
-- name    : OddOrder_BG_Ch3_MaximalSubgroups_S12_Theorem1212b
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T08:05:10.067382+00:00
-- url     : https://prove2.me/theorems/3adbc9c1-964e-4aed-8c6d-003685550041
-- title:
--   BG §12: Theorem 12.12, Case 3 (abelian Sylow $p$), building blocks
-- statement:
--   Building blocks for Case 3 of Theorem 12.12 of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, §12: the Sylow $p$-subgroup of $G$ is abelian and $\tau_2(M)\ne\emptyset$. Under the setting of Lemma 12.8, $A_0=E_2$ satisfies (a), and for (b) one builds a cyclic $N_G(S)$-invariant subgroup $Z\le S$ with $\exp(Z)=\exp(S)$ and $C_{M_\sigma}(\Omega_1(Z))=1$. The file assembles the parts of this case from the bottom up.
--
--   Main declarations: `conjActionHom`; `exists_cyclic_Enormal_regular_of_CES_eq`.
--
--   The bundle also proves 25 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch3_MaximalSubgroups/S12_Theorem1212b.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch3_MaximalSubgroups/S12_Theorem1212b.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S12_Theorem1212
import Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S12_ExceptionalBridge

namespace OddOrder.BG.Ch3.S12

open OddOrder.GroupTheory

open OddOrder.Isaacs

open OddOrder.Isaacs.Ch06

open scoped Pointwise

open scoped IsMulCommutative

variable {G : Type*} [Group G]

/-- The maximality predicate making `S` a Sylow `p`-subgroup *of `M`* as well: any `p`-subgroup
`R` of `M` containing `S` equals `S`. Holds because `S` is already a Sylow `p`-subgroup of `G`. -/
theorem sylow_maximal_in_M_of_le {p : ℕ} [Fact p.Prime] {M : Subgroup G} [Finite G]
    {S : Sylow p G} (_hSM : (S : Subgroup G) ≤ M) :
    ∀ R : Subgroup G, (S : Subgroup G) ≤ R → R ≤ M → IsPGroup p ↥R → R = (S : Subgroup G) := by
  intro R hSR _ hRpg
  refine (Subgroup.eq_of_le_of_card_ge hSR ?_).symm
  obtain ⟨k, hk⟩ := hRpg.exists_card_eq
  rw [S.card_eq_multiplicity, hk]
  refine Nat.pow_le_pow_right (Fact.out : p.Prime).pos ?_
  rw [← Nat.Prime.pow_dvd_iff_le_factorization Fact.out Nat.card_pos.ne', ← hk]
  exact Subgroup.card_subgroup_dvd_card R

/-- **Theorem 12.12, Case 3 key fact** (BG L3345-3347): since `p ∉ σ(M)` gives `N_G(S) ⊄ M`,
every `N_G(S)`-invariant line `L ≤ S` automatically satisfies `C_{M_σ}(L) = 1`. Indeed `L ≤ A`
(`= Ω₁(S)`, all order-`p` elements), so if `M_σ ⊓ C_G(L) ≠ 1` then Corollary 12.6(c) makes `M`
the unique maximal over `C_G(L)`, forcing `N_G(L) ⊆ M` and hence `N_G(S) ≤ N_G(L) ⊆ M`,
contradicting `N_G(S) ⊄ M`. -/
theorem inf_centralizer_line_eq_bot_of_invariant [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ tau2 M) {A : Subgroup G} (hA : A ∈ elemAbelianOfRank G p 2) (hAE : A ≤ E)
    {S : Sylow p G} (hAS : A ≤ (S : Subgroup G)) (hSM : (S : Subgroup G) ≤ M)
    {L : Subgroup G} (hL : L ∈ elemAbelianOfRank G p 1) (hLS : L ≤ (S : Subgroup G))
    (hLinv : Subgroup.normalizer ((S : Subgroup G) : Set G) ≤
      Subgroup.normalizer (L : Set G)) :
    S10.Msigma M ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
  classical
  have hAM : A ≤ M := hAE.trans h.E_le
  -- `Ω₁(S) = A` and `N_G(S) ⊄ M` (Theorem 12.5(b) packaging).
  obtain ⟨hΩ, hNS_not_le⟩ := omega1_eq_of_tau2 hG h.mem_maximal hp hA hAM
    S.isPGroup' hAS hSM (sylow_maximal_in_M_of_le hSM)
  -- the line `L ≤ A`: its order-`p` elements lie in `Ω₁(S) = A`.
  have hLA : L ≤ A := by
    rw [hΩ]
    intro g hg
    rw [Subgroup.mem_map]
    have hgS : (g : G) ∈ (S : Subgroup G) := hLS hg
    refine ⟨⟨g, hgS⟩, ?_, rfl⟩
    apply Omega.mem_of_pow_eq_one
    have hgp : (g : G) ^ p = 1 := by
      have h1 := congrArg (Subtype.val : ↥L → G) (hL.1.pow_eq_one ⟨g, hg⟩)
      simpa using h1
    exact Subtype.ext (by simpa using hgp)
  by_contra hne
  -- Corollary 12.6(c): `M` is the unique maximal subgroup over `C_G(L)`.
  have hsingle : maximalSubgroupsContaining (Subgroup.centralizer (L : Set G)) = {M} :=
    maximalContaining_centralizer_line_eq_singleton hG h hp hA hAE hL hLA hne
  -- hence `N_G(L) ⊆ M`.
  have hLne : L ≠ ⊥ := ne_bot_of_mem_elemAbelianOfRank_one hL
  have hNL_lt : Subgroup.normalizer (L : Set G) < ⊤ :=
    normalizer_lt_top_of_le_of_ne_bot hG h.mem_maximal (hLA.trans hAM) hLne
  have hNL_le_M : Subgroup.normalizer (L : Set G) ≤ M := by
    obtain ⟨Mst, hco, hle⟩ := (eq_top_or_exists_le_coatom _).resolve_left hNL_lt.ne
    have hmem : Mst ∈ maximalSubgroupsContaining (Subgroup.centralizer (L : Set G)) :=
      mem_maximalSubgroupsContaining.mpr
        ⟨hco, (Subgroup.centralizer_le_normalizer _).trans hle⟩
    rw [hsingle, Set.mem_singleton_iff] at hmem
    exact hmem ▸ hle
  exact hNS_not_le (hLinv.trans hNL_le_M)

/-- In a finite cyclic `p`-group, a subgroup `L` of order `p` is contained in `⟨a⟩` for every
nonidentity `a` (it is the unique minimal subgroup `Ω₁`). Working in a generator `g`: writing
`a = g^k`, `x = g^s` for `x ∈ L`, one has `gcd(N,k)·ord(a) = N = gcd(N,s)·p`, so `p ∣ ord(a)`
(`a` a nonidentity `p`-element) gives `gcd(N,k) ∣ gcd(N,s) ∣ s`, whence `x = g^s ∈ ⟨g^k⟩ = ⟨a⟩`
by Bézout. -/
theorem line_le_zpowers_in_cyclic {C : Type*} [Group C] [Finite C] [IsCyclic C]
    {p : ℕ} [Fact p.Prime] (hCp : IsPGroup p C) {L : Subgroup C} (hLcard : Nat.card ↥L = p)
    {a : C} (ha1 : a ≠ 1) : L ≤ Subgroup.zpowers a := by
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := C)
  obtain ⟨ka, hka⟩ : ∃ ka : ℕ, g ^ ka = a :=
    (Submonoid.mem_powers_iff a g).mp (mem_powers_iff_mem_zpowers.mpr (hg a))
  -- `p ∣ orderOf a` (a nonidentity `p`-element).
  have hpa : p ∣ orderOf a := by
    obtain ⟨n, hn⟩ := hCp a
    obtain ⟨i, _, hi⟩ := (Nat.dvd_prime_pow Fact.out).mp (orderOf_dvd_of_pow_eq_one hn)
    rcases Nat.eq_zero_or_pos i with rfl | hipos
    · rw [pow_zero] at hi; exact absurd (orderOf_eq_one_iff.mp hi) ha1
    · rw [hi]; exact dvd_pow_self p hipos.ne'
  intro x hxL
  rcases eq_or_ne x 1 with rfl | hx1
  · exact one_mem _
  obtain ⟨sx, hsx⟩ : ∃ sx : ℕ, g ^ sx = x :=
    (Submonoid.mem_powers_iff x g).mp (mem_powers_iff_mem_zpowers.mpr (hg x))
  -- `orderOf x = p`.
  have hxord : orderOf x = p := by
    have h1 : orderOf x ∣ p := by
      have h2 : orderOf (⟨x, hxL⟩ : ↥L) ∣ Nat.card ↥L := orderOf_dvd_natCard _
      rwa [Subgroup.orderOf_mk, hLcard] at h2
    rcases (Fact.out : p.Prime).eq_one_or_self_of_dvd _ h1 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hx1
    · exact h
  -- `gcd(N,ka) ∣ sx`, where `N = orderOf g`.
  have hga : Nat.gcd (orderOf g) ka ∣ orderOf g := Nat.gcd_dvd_left _ _
  have hgs : Nat.gcd (orderOf g) sx ∣ orderOf g := Nat.gcd_dvd_left _ _
  have ea : Nat.gcd (orderOf g) ka * orderOf a = orderOf g := by
    rw [← hka, orderOf_pow]; exact Nat.mul_div_cancel' hga
  have ex : Nat.gcd (orderOf g) sx * p = orderOf g := by
    rw [← hxord, ← hsx, orderOf_pow]; exact Nat.mul_div_cancel' hgs
  obtain ⟨t, ht⟩ := hpa
  have hcancel : Nat.gcd (orderOf g) ka * t = Nat.gcd (orderOf g) sx := by
    have heq : Nat.gcd (orderOf g) ka * t * p = Nat.gcd (orderOf g) sx * p := by
      rw [mul_assoc, mul_comm t p, ← ht, ea, ex]
    exact Nat.eq_of_mul_eq_mul_right (Fact.out : p.Prime).pos heq
  have hdvd : Nat.gcd (orderOf g) ka ∣ sx := by
    have h1 : Nat.gcd (orderOf g) ka ∣ Nat.gcd (orderOf g) sx := ⟨t, hcancel.symm⟩
    exact dvd_trans h1 (Nat.gcd_dvd_right (orderOf g) sx)
  -- `x = g^sx ∈ ⟨g^ka⟩ = ⟨a⟩` via Bézout.
  rw [← hsx, ← hka, Subgroup.mem_zpowers_iff]
  obtain ⟨w, hw⟩ := hdvd
  refine ⟨Int.gcdA ka (orderOf g) * w, ?_⟩
  have hbez : (Nat.gcd ka (orderOf g) : ℤ)
      = (ka : ℤ) * Int.gcdA ka (orderOf g) + (orderOf g : ℤ) * Int.gcdB ka (orderOf g) :=
    Int.gcd_eq_gcd_ab ka (orderOf g)
  rw [← zpow_natCast g ka, ← zpow_mul, ← zpow_natCast g sx, zpow_eq_zpow_iff_modEq,
    Int.modEq_iff_dvd]
  have hrw : (sx : ℤ) - (ka : ℤ) * (Int.gcdA ka (orderOf g) * w)
      = (orderOf g : ℤ) * (Int.gcdB ka (orderOf g) * w) := by
    have hsxz : (sx : ℤ) = (Nat.gcd ka (orderOf g) : ℤ) * (w : ℤ) := by
      rw [Nat.gcd_comm]; exact_mod_cast hw
    rw [hsxz, hbez]; ring
  rw [hrw]
  exact dvd_mul_right _ _

/-- **Regularity transfer from the line to the whole cyclic group**: if `N` meets the centralizer
of an order-`p` line `L ≤ Z` (cyclic `p`-group) trivially, then it meets `C_G(a)` trivially for
every `a ∈ Z#`. Each such `a` has `L ≤ ⟨a⟩` (unique minimal subgroup), so `C_G(a) ≤ C_G(L)`. -/
theorem inf_centralizer_eq_bot_of_line_le_cyclic [Finite G] {Z L N : Subgroup G} {p : ℕ}
    [Fact p.Prime] (hZp : IsPGroup p ↥Z) [IsCyclic ↥Z] (hLZ : L ≤ Z) (hLcard : Nat.card ↥L = p)
    (hNL : N ⊓ Subgroup.centralizer (L : Set G) = ⊥) :
    ∀ a ∈ Z, a ≠ 1 → N ⊓ Subgroup.centralizer ({a} : Set G) = ⊥ := by
  intro a ha ha1
  -- `L ≤ ⟨a⟩` via the unique-minimal-subgroup lemma, transported from `↥Z` to `G`.
  have hLza : L ≤ Subgroup.zpowers a := by
    have hcard' : Nat.card ↥(L.subgroupOf Z) = p := by
      rw [← hLcard]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLZ).toEquiv
    have hane : (⟨a, ha⟩ : ↥Z) ≠ 1 := by
      intro hcon; exact ha1 (by simpa using congrArg Subtype.val hcon)
    have key := line_le_zpowers_in_cyclic (C := ↥Z) hZp hcard' hane
    have h1 := Subgroup.map_mono (f := Z.subtype) key
    rwa [Subgroup.map_subgroupOf_eq_of_le hLZ, MonoidHom.map_zpowers] at h1
  -- `C_G(a) = C_G(⟨a⟩) ≤ C_G(L)`.
  have hCle : Subgroup.centralizer ({a} : Set G) ≤ Subgroup.centralizer (L : Set G) := by
    rw [← centralizer_zpowers_eq_singleton]
    exact Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hLza)
  rw [← le_bot_iff, ← hNL]
  exact le_inf inf_le_left (inf_le_right.trans hCle)

/-- The conjugation action homomorphism `↥Q →* MulAut ↥S` of a subgroup `Q ≤ N_G(S)` on `S`
(restriction of `Subgroup.normalizerMonoidHom S` along `Q ↪ N_G(S)`). -/
def conjActionHom {S Q : Subgroup G} (hQN : Q ≤ Subgroup.normalizer (S : Set G)) :
    ↥Q →* MulAut ↥S :=
  (Subgroup.normalizerMonoidHom S).comp (Subgroup.inclusion hQN)

/-- The kernel of the conjugation action `conjActionHom` is `C_Q(S) = C_G(S) ⊓ Q`
(the elements of `Q` centralizing `S`), via `Subgroup.normalizerMonoidHom_ker`. -/
theorem conjActionHom_ker {S Q : Subgroup G} (hQN : Q ≤ Subgroup.normalizer (S : Set G)) :
    (conjActionHom hQN).ker = (Subgroup.centralizer (S : Set G)).subgroupOf Q := by
  ext a
  simp only [conjActionHom, MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_subgroupOf]
  rw [← MonoidHom.mem_ker, Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf]
  rfl

/-- **φ̄ quotient action wrapper** (Theorem 12.12, Case 3 main branch, BG L3360-3366): a `q`-group
`Q ≤ N_G(S)` acting on the (`p`-group, `p ≠ q`) `S ≠ 1` by conjugation, fixed-point-freely outside
its kernel `C_Q(S)` — i.e. every `x ∈ Q` with `x ∉ C_G(S)` has `S ⊓ C_G(x) = 1` — has cyclic
quotient `Q ⧸ C_Q(S)`. The lifted conjugation hom `φ̄ : Q ⧸ ker → MulAut S` is fixed-point-free
(its `actionFixedBy` of a nonidentity coset is `C_S(x) = 1`), so Proposition 3.9
(`isCyclic_of_coprime_fpf_pgroup_action`) applies. -/
theorem isCyclic_quotient_of_conjugation_fpf [Finite G]
    {S Q : Subgroup G} {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hQN : Q ≤ Subgroup.normalizer (S : Set G))
    (hSp : IsPGroup p ↥S) (hQq : IsPGroup q ↥Q) (hSne : S ≠ ⊥)
    (hq_odd : Odd q) (hpq : p ≠ q)
    (hfpf : ∀ x ∈ Q, x ∉ Subgroup.centralizer (S : Set G) →
      (S : Subgroup G) ⊓ Subgroup.centralizer ({x} : Set G) = ⊥) :
    IsCyclic (↥Q ⧸ (conjActionHom hQN).ker) := by
  classical
  have : Nontrivial ↥S := (Subgroup.nontrivial_iff_ne_bot S).mpr hSne
  have hRq : IsPGroup q (↥Q ⧸ (conjActionHom hQN).ker) := hQq.to_quotient _
  -- coprimality of `|Q/ker|` (a `q`-power) and `|S|` (a `p`-power), `p ≠ q`.
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card (p := q)).mp hRq
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := p)).mp hSp
  have hcop : Nat.Coprime (Nat.card (↥Q ⧸ (conjActionHom hQN).ker)) (Nat.card ↥S) := by
    rw [hm, hn]
    exact ((Nat.coprime_primes (Fact.out : q.Prime) (Fact.out : p.Prime)).mpr
      (Ne.symm hpq)).pow m n
  -- apply Proposition 3.9 to the lifted conjugation hom.
  refine isCyclic_of_coprime_fpf_pgroup_action hRq hq_odd hcop
    (QuotientGroup.kerLift (conjActionHom hQN)) ?_
  intro ā hā
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective ā
  -- `a ∉ ker`, i.e. `(a:G) ∉ C_G(S)`.
  have ha_ker : a ∉ (conjActionHom hQN).ker := fun hmem =>
    hā ((QuotientGroup.eq_one_iff a).mpr hmem)
  have ha_cent : (a : G) ∉ Subgroup.centralizer (S : Set G) := by
    rw [conjActionHom_ker, Subgroup.mem_subgroupOf] at ha_ker; exact ha_ker
  -- the fixed subgroup of the coset `mk a` is `⊥` (regularity of `x` on `S`).
  rw [eq_bot_iff]
  intro s hs
  rw [mem_actionFixedBy, QuotientGroup.kerLift_mk] at hs
  have hsval : (a : G) * (s : G) * (a : G)⁻¹ = (s : G) := congrArg Subtype.val hs
  have hcomm : (a : G) * (s : G) = (s : G) * (a : G) := mul_inv_eq_iff_eq_mul.mp hsval
  have hmem : (s : G) ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ({(a : G)} : Set G) := by
    rw [Subgroup.mem_inf]
    refine ⟨s.2, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro y hy
    rw [Set.mem_singleton_iff] at hy; subst hy
    exact hcomm
  rw [hfpf (a : G) a.2 ha_cent, Subgroup.mem_bot] at hmem
  rw [Subgroup.mem_bot]
  exact Subtype.ext hmem

/-- In a finite abelian `p`-group `T` (`p` odd) of `p`-rank `≤ 2`, a subgroup `T₀` disjoint from a
*nontrivial* subgroup `T₁` is cyclic. If `T₀` were noncyclic it would contain an elementary abelian
`B₀ ≤ T₀` of order `p²`; with an order-`p` element `y ∈ T₁`, the join `B₀ ⊔ ⟨y⟩` (disjoint since
`T₀ ⊓ T₁ = ⊥`) is elementary abelian of order `p³`, forcing `pRank T ≥ 3`, a contradiction.
Used in Theorem 12.12 Case 3 for `S = C_S(X) × [S,X]`: both factors are cyclic since `r(S) = 2`. -/
theorem isCyclic_of_inf_eq_bot_of_pRank_le_two {T : Type*} [CommGroup T] [Finite T] {p : ℕ}
    [Fact p.Prime] (hTp : IsPGroup p T) (hodd : Odd p) (hrank : pRank T p ≤ 2)
    {T₀ T₁ : Subgroup T} (hdisj : T₀ ⊓ T₁ = ⊥) (hT₁ : T₁ ≠ ⊥) :
    IsCyclic ↥T₀ := by
  classical
  by_contra hnc
  -- noncyclic `T₀` contains an elementary abelian `B₀` of order `p²`.
  obtain ⟨B₀, hB₀ea, hB₀card⟩ :=
    OddOrder.BG.Ch1.S04.exists_isElementaryAbelian_card_prime_sq_of_not_isCyclic
      (hTp.to_subgroup T₀) hodd hnc
  set B : Subgroup T := B₀.map T₀.subtype with hB_def
  have hBea : B.IsElementaryAbelian p :=
    Subgroup.IsElementaryAbelian.map T₀.subtype_injective hB₀ea
  have hBT₀ : B ≤ T₀ := Subgroup.map_subtype_le B₀
  have hBcard : Nat.card ↥B = p ^ 2 := by
    rw [hB_def, ← hB₀card]
    exact Nat.card_congr
      (Subgroup.equivMapOfInjective B₀ T₀.subtype T₀.subtype_injective).symm.toEquiv
  -- an order-`p` element `y ∈ T₁`.
  have : Nontrivial ↥T₁ := (Subgroup.nontrivial_iff_ne_bot T₁).mpr hT₁
  have hp_dvd : p ∣ Nat.card ↥T₁ := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := p)).mp (hTp.to_subgroup T₁)
    have h1lt : 1 < Nat.card ↥T₁ := Finite.one_lt_card
    have hk0 : k ≠ 0 := by rintro rfl; rw [pow_zero] at hk; omega
    rw [hk]; exact dvd_pow_self p hk0
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hp_dvd
  set y : T := T₁.subtype x with hy_def
  have hyT₁ : y ∈ T₁ := x.2
  have hyord : orderOf y = p := by
    rw [hy_def, orderOf_injective T₁.subtype T₁.subtype_injective x]; exact hx
  -- `⟨y⟩` is elementary abelian of order `p`.
  have hZcard : Nat.card ↥(Subgroup.zpowers y) = p := by rw [Nat.card_zpowers]; exact hyord
  have hZea : (Subgroup.zpowers y).IsElementaryAbelian p :=
    Subgroup.IsElementaryAbelian.of_card_prime hZcard
  have hZT₁ : Subgroup.zpowers y ≤ T₁ := by rw [Subgroup.zpowers_le]; exact hyT₁
  -- `B ⊓ ⟨y⟩ = ⊥` (both inside the disjoint `T₀`, `T₁`).
  have hBZ_disj : B ⊓ Subgroup.zpowers y = ⊥ := by
    rw [← le_bot_iff, ← hdisj]
    exact le_inf (inf_le_left.trans hBT₀) (inf_le_right.trans hZT₁)
  -- `B ⊔ ⟨y⟩` is elementary abelian of order `p³`, so `pRank T ≥ 3`.
  have hcent : B ≤ Subgroup.centralizer (Subgroup.zpowers y : Set T) :=
    fun b _ => Subgroup.mem_centralizer_iff.mpr (fun g _ => mul_comm g b)
  have hsupea : (B ⊔ Subgroup.zpowers y).IsElementaryAbelian p :=
    isElementaryAbelian_sup_of_le_centralizer hBea hZea hcent
  have hsupcard : Nat.card ↥(B ⊔ Subgroup.zpowers y) = p ^ 3 := by
    rw [OddOrder.BG.Ch1.S01.card_sup_eq_card_mul_card_of_disjoint_normal hBZ_disj, hBcard, hZcard]
    ring
  have hle := le_pRank (B ⊔ Subgroup.zpowers y) hsupea
  rw [hsupcard, Nat.log_pow (Fact.out : p.Prime).one_lt] at hle
  omega

/-- In a finite abelian group `T` that is the internal product `T₀ ⊔ T₁ = ⊤` of two subgroups, if
`exp(T₁) ∣ exp(T₀)` then `exp(T) = exp(T₀)`. Every `g ∈ T` factors as `g = a·b` (`a ∈ T₀`,
`b ∈ T₁`, commuting), and `ord(g) ∣ lcm(ord a, ord b) ∣ exp(T₀)`. Used in Theorem 12.12 Case 3
with `T = S`, `T₀ = Z` the larger of the two cyclic factors `C_S(X), [S,X]` (the larger has the
bigger order, hence absorbs the exponent), giving `exp(Z) = exp(S)`. -/
theorem exponent_eq_of_sup_eq_top_of_exponent_dvd {T : Type*} [CommGroup T] [Finite T]
    {T₀ T₁ : Subgroup T} (hsup : T₀ ⊔ T₁ = ⊤)
    (hexp : Monoid.exponent ↥T₁ ∣ Monoid.exponent ↥T₀) :
    Monoid.exponent T = Monoid.exponent ↥T₀ := by
  classical
  refine dvd_antisymm ?_ (Monoid.exponent_dvd_of_monoidHom T₀.subtype T₀.subtype_injective)
  rw [Monoid.exponent_dvd]
  intro g
  have hg : g ∈ T₀ ⊔ T₁ := by rw [hsup]; exact Subgroup.mem_top g
  obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup.mp hg
  subst hab
  refine ((Commute.all a b).orderOf_mul_dvd_lcm).trans (Nat.lcm_dvd ?_ ?_)
  · have h := Monoid.order_dvd_exponent (⟨a, ha⟩ : ↥T₀)
    rwa [Subgroup.orderOf_mk] at h
  · have h := Monoid.order_dvd_exponent (⟨b, hb⟩ : ↥T₁)
    rw [Subgroup.orderOf_mk] at h
    exact h.trans hexp

/-- Cast of `isCyclic_of_inf_eq_bot_of_pRank_le_two` to two subgroups `S₀, S₁` of `G` sitting
inside an abelian `p`-group `S` of `p`-rank `≤ 2`: if `S₀ ⊓ S₁ = ⊥` and `S₁ ≠ ⊥`, then `S₀` is
cyclic. (Works inside the ambient type `↥S`, using `subgroupOf` and `subgroupOfEquivOfLe`.) -/
theorem isCyclic_of_le_of_inf_eq_bot_of_pRank_le_two {S S₀ S₁ : Subgroup G} {p : ℕ}
    [Fact p.Prime] [Finite G] [IsMulCommutative ↥S] (hSp : IsPGroup p ↥S) (hodd : Odd p)
    (hrank : pRank ↥S p ≤ 2) (hS₀S : S₀ ≤ S) (hS₁S : S₁ ≤ S)
    (hdisj : S₀ ⊓ S₁ = ⊥) (hS₁ne : S₁ ≠ ⊥) : IsCyclic ↥S₀ := by
  have key : IsCyclic ↥(S₀.subgroupOf S) := by
    refine isCyclic_of_inf_eq_bot_of_pRank_le_two hSp hodd hrank
      (T₀ := S₀.subgroupOf S) (T₁ := S₁.subgroupOf S) ?_ ?_
    · refine le_bot_iff.mp ?_
      intro x hx
      rw [Subgroup.mem_inf] at hx
      have hmem : (x : G) ∈ S₀ ⊓ S₁ :=
        ⟨Subgroup.mem_subgroupOf.mp hx.1, Subgroup.mem_subgroupOf.mp hx.2⟩
      rw [hdisj, Subgroup.mem_bot] at hmem
      exact Subgroup.mem_bot.mpr (Subtype.ext hmem)
    · exact fun heq =>
        hS₁ne (disjoint_self.mp ((Subgroup.subgroupOf_eq_bot.mp heq).mono_right hS₁S))
  exact isCyclic_of_surjective _ (Subgroup.subgroupOfEquivOfLe hS₀S).surjective

/-- Cast of `exponent_eq_of_sup_eq_top_of_exponent_dvd` to subgroups `S₀, S₁ ≤ S` of `G` with
`S₀ ⊔ S₁ = S`: if `exp(S₁) ∣ exp(S₀)` then `exp(S₀) = exp(S)`. -/
theorem exponent_eq_of_le_of_sup_eq_of_exponent_dvd {S S₀ S₁ : Subgroup G} [IsMulCommutative ↥S]
    [Finite G] (hS₀S : S₀ ≤ S) (hS₁S : S₁ ≤ S) (hsup : S₀ ⊔ S₁ = S)
    (hexp : Monoid.exponent ↥S₁ ∣ Monoid.exponent ↥S₀) :
    Monoid.exponent ↥S₀ = Monoid.exponent ↥S := by
  have e₀ : Monoid.exponent ↥(S₀.subgroupOf S) = Monoid.exponent ↥S₀ :=
    Monoid.exponent_eq_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hS₀S)
  have e₁ : Monoid.exponent ↥(S₁.subgroupOf S) = Monoid.exponent ↥S₁ :=
    Monoid.exponent_eq_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hS₁S)
  have htop : S₀.subgroupOf S ⊔ S₁.subgroupOf S = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hS₀S hS₁S, hsup, Subgroup.subgroupOf_self]
  have key := exponent_eq_of_sup_eq_top_of_exponent_dvd htop (by rw [e₀, e₁]; exact hexp)
  rw [e₀] at key
  exact key.symm

/-- **Theorem 12.12, Case 3, the per-`Z` payoff** (BG L3354-3357): every `N_G(S)`-invariant
nonidentity cyclic subgroup `Z ≤ S` satisfies `C_{M_σ}(z) = 1` for all `z ∈ Z#`. Its order-`p`
subgroup `L = Ω₁(Z)` is a line (`Ω₁` of cyclic `Z` has order `p` since `↥Z` is abelian of class
`≤ 2`), is `N_G(S)`-invariant (characteristic in `Z`, via `normalizer_le_normalizer_map_of_-`
`characteristic`), so the key fact gives `M_σ ⊓ C_G(L) = 1`, and the cyclic bridge spreads this
to every `z ∈ Z#`. -/
theorem inf_centralizer_eq_bot_of_invariant_cyclic [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ tau2 M) {A : Subgroup G} (hA : A ∈ elemAbelianOfRank G p 2) (hAE : A ≤ E)
    {S : Sylow p G} (hAS : A ≤ (S : Subgroup G)) (hSM : (S : Subgroup G) ≤ M)
    {Z : Subgroup G} [IsCyclic ↥Z] (hZS : Z ≤ (S : Subgroup G)) (hZne : Z ≠ ⊥)
    (hZinv : Subgroup.normalizer ((S : Subgroup G) : Set G) ≤
      Subgroup.normalizer (Z : Set G)) :
    ∀ z ∈ Z, z ≠ 1 → S10.Msigma M ⊓ Subgroup.centralizer ({z} : Set G) = ⊥ := by
  classical
  have hodd : Odd p := hG.odd.of_dvd_nat
    (dvd_trans (hA.2 ▸ dvd_pow_self p (two_ne_zero)) (Subgroup.card_subgroup_dvd_card A))
  have hZp : IsPGroup p ↥Z := S.isPGroup'.to_le hZS
  have : Nontrivial ↥Z := (Subgroup.nontrivial_iff_ne_bot Z).mpr hZne
  -- `↥Z` is abelian (cyclic), so class `≤ 2`.
  have hcl : _root_.commutator ↥Z ≤ Subgroup.center ↥Z := by rw [commutator_eq_bot]; exact bot_le
  -- a `p`-torsion element makes `Ω₁(↥Z)` nontrivial.
  have hpZ : p ∣ Nat.card ↥Z := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := p)).mp hZp
    have h1lt : 1 < Nat.card ↥Z := Finite.one_lt_card
    have hk0 : k ≠ 0 := by rintro rfl; rw [pow_zero] at hk; omega
    rw [hk]; exact dvd_pow_self p hk0
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hpZ
  have hxne : x ≠ 1 := by
    intro hx1; rw [hx1, orderOf_one] at hx; exact absurd hx.symm (Fact.out : p.Prime).ne_one
  have hxO : x ∈ Omega ↥Z p 1 :=
    Omega.mem_of_pow_eq_one (by rw [pow_one]; exact hx ▸ pow_orderOf_eq_one x)
  have hOnt : Nontrivial ↥(Omega ↥Z p 1) := by
    rw [Subgroup.nontrivial_iff_ne_bot]
    intro hbot; rw [hbot, Subgroup.mem_bot] at hxO; exact hxne hxO
  have hOcard : Nat.card ↥(Omega ↥Z p 1) = p := by
    rw [← IsCyclic.exponent_eq_card]; exact Omega.exponent_eq_of_class_le_two hodd hcl
  -- `L = Ω₁(Z)` as a subgroup of `G`: a line `≤ Z ≤ S`, `N_G(S)`-invariant.
  set L : Subgroup G := (Omega ↥Z p 1).map Z.subtype with hL_def
  have hLcard : Nat.card ↥L = p := by
    rw [hL_def, Subgroup.card_map_of_injective Z.subtype_injective]; exact hOcard
  have hLZ : L ≤ Z := hL_def ▸ Subgroup.map_subtype_le _
  have hLS : L ≤ (S : Subgroup G) := hLZ.trans hZS
  have hL1 : L ∈ elemAbelianOfRank G p 1 :=
    ⟨Subgroup.IsElementaryAbelian.of_card_prime hLcard, by rw [hLcard, pow_one]⟩
  have hLinv : Subgroup.normalizer ((S : Subgroup G) : Set G) ≤
      Subgroup.normalizer (L : Set G) := by
    rw [hL_def]
    exact hZinv.trans AppB.normalizer_le_normalizer_map_of_characteristic
  have hkey := inf_centralizer_line_eq_bot_of_invariant hG h hp hA hAE hAS hSM hL1 hLS hLinv
  exact inf_centralizer_eq_bot_of_line_le_cyclic hZp hLZ hLcard hkey

/-- **Theorem 12.12, Case 3, the `Z`-construction** (BG L3367-3373): in the abelian-Sylow regime,
a subgroup `X ≤ N_G(S)` (coprime to `S`) with `1 ⊊ C_S(X) ⊊ S` produces the required cyclic
subgroup `Z`. Indeed `S = S₀ × S₁` with `S₀ = C_S(X)`, `S₁ = [S, X]`
(`fitting_coprime_abelian_decomp`), both cyclic (rank 2) and `N_G(S)`-invariant (Lemma 12.8(f)).
Taking `Z` to be the larger of `S₀, S₁` (by order) gives a cyclic `N_G(S)`-invariant `Z ≤ S` of
the same exponent as `S` (the larger cyclic `p`-factor absorbs the exponent) acting regularly on
`M_σ` (`inf_centralizer_eq_bot_of_invariant_cyclic`). -/
theorem exists_invariant_cyclic_sameExponent_regular [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ tau2 M) {A : Subgroup G} (hA : A ∈ elemAbelianOfRank G p 2) (hAE : A ≤ E)
    {S : Sylow p G} (hAS : A ≤ (S : Subgroup G)) (hSM : (S : Subgroup G) ≤ M)
    (hSab : IsMulCommutative ↥(S : Subgroup G))
    {X : Subgroup G} (hXN : X ≤ Subgroup.normalizer ((S : Subgroup G) : Set G))
    (hcop : Nat.Coprime (Nat.card ↥(S : Subgroup G)) (Nat.card ↥X))
    (hS0ne : (S : Subgroup G) ⊓ Subgroup.centralizer (X : Set G) ≠ ⊥)
    (hSltS : (S : Subgroup G) ⊓ Subgroup.centralizer (X : Set G) ≠ (S : Subgroup G)) :
    ∃ Z : Subgroup G, Z ≤ (S : Subgroup G) ∧ IsCyclic ↥Z ∧ Z ≠ ⊥ ∧
      Subgroup.normalizer ((S : Subgroup G) : Set G) ≤ Subgroup.normalizer (Z : Set G) ∧
      Monoid.exponent ↥Z = Monoid.exponent ↥(S : Subgroup G) ∧
      ∀ z ∈ Z, z ≠ 1 → S10.Msigma M ⊓ Subgroup.centralizer ({z} : Set G) = ⊥ := by
  classical
  have := hSab
  have hodd : Odd p := hG.odd.of_dvd_nat
    (dvd_trans (hA.2 ▸ dvd_pow_self p (two_ne_zero)) (Subgroup.card_subgroup_dvd_card A))
  have hSp : IsPGroup p ↥(S : Subgroup G) := S.isPGroup'
  have hrank : pRank ↥(S : Subgroup G) p ≤ 2 :=
    (pRank_le_of_injective (Subgroup.inclusion_injective hSM)).trans (le_of_eq (tau2_pRank_eq_two
        hp))
  -- decomposition `S = S₀ × S₁`, `S₀ = C_S(X)`, `S₁ = [S, X]`.
  obtain ⟨hdisj, hsup⟩ :=
    OddOrder.Isaacs.Ch05.fitting_coprime_abelian_decomp (P := (S : Subgroup G)) (K := X) hXN hcop
  set S₀ : Subgroup G := Subgroup.centralizer (X : Set G) ⊓ (S : Subgroup G) with hS₀def
  set S₁ : Subgroup G := ⁅(S : Subgroup G), X⁆ with hS₁def
  have hS₀S : S₀ ≤ (S : Subgroup G) := inf_le_right
  have hS₁S : S₁ ≤ (S : Subgroup G) := hsup ▸ le_sup_right
  -- both factors nontrivial.
  have hS₀ne : S₀ ≠ ⊥ := by rw [hS₀def, inf_comm]; exact hS0ne
  have hS₁ne : S₁ ≠ ⊥ := fun hbot => hSltS (by
    rw [inf_comm, ← hS₀def, ← hsup, hbot, sup_bot_eq])
  -- both factors cyclic (rank 2).
  have hS₀cyc : IsCyclic ↥S₀ :=
    isCyclic_of_le_of_inf_eq_bot_of_pRank_le_two hSp hodd hrank hS₀S hS₁S hdisj hS₁ne
  have hS₁cyc : IsCyclic ↥S₁ :=
    isCyclic_of_le_of_inf_eq_bot_of_pRank_le_two hSp hodd hrank hS₁S hS₀S
      (by rw [inf_comm]; exact hdisj) hS₀ne
  -- both factors `N_G(S)`-invariant (Lemma 12.8(f)).
  obtain ⟨h128f0, h128f1⟩ := relative_normality_of_abelianSylow hG h hp hA hAE hAS hSab X hXN
  have hS₀inv : Subgroup.normalizer ((S : Subgroup G) : Set G) ≤ Subgroup.normalizer (S₀ : Set G) :=
      by
    rw [hS₀def, inf_comm]; exact h128f0
  have hS₁inv : Subgroup.normalizer ((S : Subgroup G) : Set G) ≤ Subgroup.normalizer (S₁ : Set G) :=
    h128f1
  -- exponent divisibility from the `p`-power orders.
  have := hS₀cyc; have := hS₁cyc
  have hexpdvd : ∀ {T₀ T₁ : Subgroup G}, IsCyclic ↥T₀ → IsCyclic ↥T₁ → T₀ ≤ (S : Subgroup G) →
      T₁ ≤ (S : Subgroup G) → Nat.card ↥T₁ ≤ Nat.card ↥T₀ →
      Monoid.exponent ↥T₁ ∣ Monoid.exponent ↥T₀ := by
    intro T₀ T₁ hc0 hc1 h0 h1 hle
    have := hc0; have := hc1
    rw [IsCyclic.exponent_eq_card, IsCyclic.exponent_eq_card]
    obtain ⟨a, ha⟩ := (IsPGroup.iff_card (p := p)).mp (hSp.to_le h0)
    obtain ⟨b, hb⟩ := (IsPGroup.iff_card (p := p)).mp (hSp.to_le h1)
    rw [ha, hb]; rw [ha, hb] at hle
    exact pow_dvd_pow p ((Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp hle)
  -- `Z` = the larger factor.
  rcases le_total (Nat.card ↥S₁) (Nat.card ↥S₀) with hle | hle
  · refine ⟨S₀, hS₀S, hS₀cyc, hS₀ne, hS₀inv, ?_, ?_⟩
    · exact exponent_eq_of_le_of_sup_eq_of_exponent_dvd hS₀S hS₁S hsup
        (hexpdvd hS₀cyc hS₁cyc hS₀S hS₁S hle)
    · exact inf_centralizer_eq_bot_of_invariant_cyclic hG h hp hA hAE hAS hSM hS₀S hS₀ne hS₀inv
  · refine ⟨S₁, hS₁S, hS₁cyc, hS₁ne, hS₁inv, ?_, ?_⟩
    · exact exponent_eq_of_le_of_sup_eq_of_exponent_dvd hS₁S hS₀S (sup_comm S₀ S₁ ▸ hsup)
        (hexpdvd hS₁cyc hS₀cyc hS₁S hS₀S hle)
    · exact inf_centralizer_eq_bot_of_invariant_cyclic hG h hp hA hAE hAS hSM hS₁S hS₁ne hS₁inv

/-- **Theorem 12.12, Case 3 setup**: in the abelian-Sylow regime `E ≤ N_G(S)`. By the Sylow chain
(`sylow_chain_of_abelianSylow`) `S ≤ F(E)`, and `S` is the Sylow `p`-subgroup of the nilpotent
`F(E)`, hence normal and characteristic in `F(E)`; since `E` normalizes its Fitting subgroup,
`E ≤ N_G(F(E)) ≤ N_G(S)`. In particular every Sylow subgroup of `E` lies in `N_G(S)`. -/
theorem E_le_normalizer_sylow_of_abelianSylow [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ tau2 M) {A : Subgroup G} (hA : A ∈ elemAbelianOfRank G p 2) (hAE : A ≤ E)
    {S : Sylow p G} (hAS : A ≤ (S : Subgroup G)) (hSab : IsMulCommutative ↥(S : Subgroup G)) :
    E ≤ Subgroup.normalizer ((S : Subgroup G) : Set G) := by
  classical
  have hchain := sylow_chain_of_abelianSylow hG h hp hA hAE hAS hSab
  have hSFE : (S : Subgroup G) ≤ Ch2.S08.fittingInG E := hchain.1.trans hchain.2.1
  have : Group.IsNilpotent ↥(Ch2.S08.fittingInG E) := Ch2.S08.fittingInG_isNilpotent E
  set SF : Sylow p ↥(Ch2.S08.fittingInG E) := S.subtype hSFE with hSFdef
  have hSF_norm : (SF : Subgroup ↥(Ch2.S08.fittingInG E)).Normal := by
    have htfae := (Group.isNilpotent_of_finite_tfae (G := ↥(Ch2.S08.fittingInG E))).out 0 3
    exact htfae.mp inferInstance p ⟨Fact.out⟩ SF
  have : (SF : Subgroup ↥(Ch2.S08.fittingInG E)).Characteristic :=
    Sylow.characteristic_of_normal SF hSF_norm
  have hmap : (SF : Subgroup ↥(Ch2.S08.fittingInG E)).map (Ch2.S08.fittingInG E).subtype
      = (S : Subgroup G) := by
    rw [hSFdef, Sylow.coe_subtype, Subgroup.map_subgroupOf_eq_of_le hSFE]
  have hNFE_le : Subgroup.normalizer ((Ch2.S08.fittingInG E : Subgroup G) : Set G) ≤
      Subgroup.normalizer ((S : Subgroup G) : Set G) := by
    have hchar := OddOrder.BG.AppB.normalizer_le_normalizer_map_of_characteristic
      (K := Ch2.S08.fittingInG E) (W := (SF : Subgroup ↥(Ch2.S08.fittingInG E)))
    rwa [hmap] at hchar
  have hE_NFE : E ≤ Subgroup.normalizer ((Ch2.S08.fittingInG E : Subgroup G) : Set G) :=
    fun e he => Ch2.S08.mem_normalizer_fittingInG_of_mem he
  exact hE_NFE.trans hNFE_le

/-- **BG Proposition 1.6(e)** (mmd L424): if `S` is an abelian `p`-group, `Q` acts coprimely
on `S` (`Q ≤ N_G(S)`), and `Q` centralizes `Ω₁(S)` (all elements of `S` of order dividing `p`),
then `Q` centralizes `S`. Via the coprime decomposition `S = C_S(Q) × [S, Q]`
(`fitting_coprime_abelian_decomp`): if `[S, Q] ≠ 1` it is a nontrivial `p`-subgroup of `S`, so
it contains an order-`p` element, which lies in `Ω₁(S) ⊆ C_S(Q)`, contradicting
`C_S(Q) ⊓ [S, Q] = 1`. -/
theorem centralizer_le_of_omega1_le_centralizer [Finite G] {S Q : Subgroup G} {p : ℕ}
    [Fact p.Prime] (hSab : IsMulCommutative ↥S) (hSp : IsPGroup p ↥S)
    (hQN : Q ≤ Subgroup.normalizer (S : Set G))
    (hcop : Nat.Coprime (Nat.card ↥S) (Nat.card ↥Q))
    (hO : (Omega ↥S p 1).map S.subtype ≤ Subgroup.centralizer (Q : Set G)) :
    (S : Subgroup G) ≤ Subgroup.centralizer (Q : Set G) := by
  classical
  obtain ⟨hdisj, hsup⟩ :=
    OddOrder.Isaacs.Ch05.fitting_coprime_abelian_decomp (P := S) (K := Q) hQN hcop
  -- It suffices to show `[S, Q] = ⊥`, for then `S = C_S(Q) ⊆ C(Q)`.
  have hcomm_le_S : (⁅(S : Subgroup G), Q⁆ : Subgroup G) ≤ S := le_sup_right.trans (le_of_eq hsup)
  have hcomm_bot : (⁅(S : Subgroup G), Q⁆ : Subgroup G) = ⊥ := by
    by_contra hne
    have : Nontrivial ↥(⁅(S : Subgroup G), Q⁆ : Subgroup G) :=
      (Subgroup.nontrivial_iff_ne_bot _).mpr hne
    have hcomm_pg : IsPGroup p ↥(⁅(S : Subgroup G), Q⁆ : Subgroup G) := hSp.to_le hcomm_le_S
    -- a nonidentity order-`p` element of `[S, Q]`
    have hpdvd : p ∣ Nat.card ↥(⁅(S : Subgroup G), Q⁆ : Subgroup G) := by
      obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := p)).mp hcomm_pg
      have h1lt : 1 < Nat.card ↥(⁅(S : Subgroup G), Q⁆ : Subgroup G) := Finite.one_lt_card
      have hk0 : k ≠ 0 := by rintro rfl; rw [pow_zero] at hk; omega
      rw [hk]; exact dvd_pow_self p hk0
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' p hpdvd
    set x : G := (y : G) with hxdef
    have hxC : x ∈ (⁅(S : Subgroup G), Q⁆ : Subgroup G) := y.2
    have hyne : y ≠ 1 := by
      intro h; rw [h, orderOf_one] at hy; exact (Fact.out : p.Prime).ne_one hy.symm
    have hxne : x ≠ 1 := by rw [hxdef, Ne, OneMemClass.coe_eq_one]; exact hyne
    have hyp : y ^ p = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
    have hxp : x ^ p = 1 := by
      rw [hxdef, ← SubmonoidClass.coe_pow, hyp, OneMemClass.coe_one]
    have hxS : x ∈ (S : Subgroup G) := hcomm_le_S hxC
    have hsubpow : (⟨x, hxS⟩ : ↥(S : Subgroup G)) ^ p = 1 := by
      apply Subtype.ext; rw [SubmonoidClass.coe_pow, OneMemClass.coe_one]; exact hxp
    -- `x ∈ Ω₁(S)`, hence `x ∈ C(Q)`.
    have hxOmega : x ∈ (Omega ↥S p 1).map S.subtype :=
      ⟨⟨x, hxS⟩, Omega.mem_of_pow_eq_one (by rw [pow_one]; exact hsubpow), rfl⟩
    have hxCQ : x ∈ Subgroup.centralizer (Q : Set G) := hO hxOmega
    -- `x ∈ (C(Q) ⊓ S) ⊓ [S, Q] = ⊥`.
    have : x ∈ ((Subgroup.centralizer (Q : Set G) ⊓ S) ⊓ ⁅(S : Subgroup G), Q⁆ : Subgroup G) :=
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hxCQ, hxS⟩, hxC⟩
    rw [hdisj, Subgroup.mem_bot] at this
    exact hxne this
  rw [hcomm_bot, sup_bot_eq] at hsup
  calc (S : Subgroup G) = Subgroup.centralizer (Q : Set G) ⊓ S := hsup.symm
    _ ≤ Subgroup.centralizer (Q : Set G) := inf_le_left

/-- In a finite cyclic `q`-group `C` (`q` odd), the order-`q` subgroup `Ω₁(C)` is contained in
*every* nontrivial subgroup `H` (it is the unique minimal subgroup). Indeed `|Ω₁(C)| = q` (cyclic
exponent) and, picking a nonidentity `h ∈ H`, `Ω₁(C) ≤ ⟨h⟩ ≤ H` by `line_le_zpowers_in_cyclic`. -/
theorem omega_le_of_ne_bot_in_cyclic {C : Type*} [Group C] [Finite C] [IsCyclic C] {q : ℕ}
    [Fact q.Prime] (hCq : IsPGroup q C) (hodd : Odd q) {H : Subgroup C} (hH : H ≠ ⊥) :
    Omega C q 1 ≤ H := by
  classical
  have : Nontrivial ↥H := (Subgroup.nontrivial_iff_ne_bot H).mpr hH
  obtain ⟨h, hhne⟩ := exists_ne (1 : ↥H)
  have hhH : (h : C) ∈ H := h.2
  have hh1 : (h : C) ≠ 1 := fun hc => hhne (Subtype.ext hc)
  have : Nontrivial C := ⟨(h : C), 1, hh1⟩
  have hcl : _root_.commutator C ≤ Subgroup.center C := by rw [commutator_eq_bot]; exact bot_le
  have hqC : q ∣ Nat.card C := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := q)).mp hCq
    have h1lt : 1 < Nat.card C := Finite.one_lt_card
    have hk0 : k ≠ 0 := by rintro rfl; rw [pow_zero] at hk; omega
    rw [hk]; exact dvd_pow_self q hk0
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' q hqC
  have hxne : x ≠ 1 := by
    intro hx1; rw [hx1, orderOf_one] at hx; exact absurd hx.symm (Fact.out : q.Prime).ne_one
  have hxO : x ∈ Omega C q 1 :=
    Omega.mem_of_pow_eq_one (by rw [pow_one]; exact hx ▸ pow_orderOf_eq_one x)
  have : Nontrivial ↥(Omega C q 1) := by
    rw [Subgroup.nontrivial_iff_ne_bot]
    intro hbot; rw [hbot, Subgroup.mem_bot] at hxO; exact hxne hxO
  have hOcard : Nat.card ↥(Omega C q 1) = q := by
    rw [← IsCyclic.exponent_eq_card]; exact Omega.exponent_eq_of_class_le_two hodd hcl
  exact (line_le_zpowers_in_cyclic hCq hOcard hh1).trans (Subgroup.zpowers_le.mpr hhH)

/-- **Theorem 12.12, Case 3, the `r(Q) = 1` side** (BG L3363-3365): if a finite `q`-group `Q`
(`q` odd) has cyclic quotient `Q ⧸ Q₀` and `Q₀ ⊊ Q₁ ≤ Q` with `Q₁` cyclic, then `pRank Q q ≤ 1`.
Since `Q ⧸ Q₀` is cyclic, `Ω₁(Q ⧸ Q₀) ≤ Q₁ ⧸ Q₀` (the unique minimal subgroup lies in the
nontrivial `Q₁ ⧸ Q₀`), so `Ω₁(Q) ≤ Q₁`; every elementary abelian `B ≤ Q` lies in `Ω₁(Q) ≤ Q₁`
(cyclic), hence is cyclic of order `≤ q`. -/
theorem pRank_le_one_of_cyclic_quotient {Q : Type*} [Group Q] [Finite Q] {q : ℕ}
    [Fact q.Prime] {Q₀ Q₁ : Subgroup Q} [Q₀.Normal] (hQq : IsPGroup q Q) (hodd : Odd q)
    (hcyc : IsCyclic (Q ⧸ Q₀)) (h0lt1 : Q₀ < Q₁) (hQ₁cyc : IsCyclic ↥Q₁) :
    pRank Q q ≤ 1 := by
  classical
  set f := QuotientGroup.mk' Q₀ with hf
  -- `Ω₁(Q) ≤ Q₁`.
  have hOmegaQ₁ : Omega Q q 1 ≤ Q₁ := by
    rw [Omega, Subgroup.closure_le]
    intro g hg
    have hgq : g ^ q = 1 := by simpa only [Set.mem_ofPred_eq, pow_one] using hg
    have hmapne : Q₁.map f ≠ ⊥ := by
      intro hbot
      rw [Subgroup.map_eq_bot_iff, hf, QuotientGroup.ker_mk'] at hbot
      exact h0lt1.ne (le_antisymm h0lt1.le hbot)
    have hgbar : f g ∈ Omega (Q ⧸ Q₀) q 1 :=
      Omega.mem_of_pow_eq_one (by rw [pow_one, ← map_pow, hgq, map_one])
    have hmem : f g ∈ Q₁.map f :=
      omega_le_of_ne_bot_in_cyclic (hQq.to_quotient Q₀) hodd hmapne hgbar
    have hcm : (Q₁.map f).comap f = Q₁ :=
      Subgroup.comap_map_eq_self (by rw [hf, QuotientGroup.ker_mk']; exact h0lt1.le)
    rw [← hcm]; exact Subgroup.mem_comap.mpr hmem
  -- `pRank Q ≤ 1`.
  rw [pRank_le_iff]
  intro B hB
  have hBOmega : B ≤ Omega Q q 1 := fun b hb => Omega.mem_of_pow_eq_one (by
    rw [pow_one]
    have h1 := congrArg (Subtype.val : ↥B → Q) (hB.pow_eq_one ⟨b, hb⟩)
    simpa using h1)
  have hBQ₁ : B ≤ Q₁ := hBOmega.trans hOmegaQ₁
  have : IsCyclic ↥B := Subgroup.isCyclic_of_le hBQ₁
  have hBexp : Monoid.exponent ↥B ∣ q := by
    rw [Monoid.exponent_dvd]; intro b; exact orderOf_dvd_of_pow_eq_one (hB.pow_eq_one b)
  have hBle : Nat.card ↥B ≤ q :=
    Nat.le_of_dvd (Fact.out : q.Prime).pos (by rw [← IsCyclic.exponent_eq_card]; exact hBexp)
  have hq2 : q < q ^ 2 := by rw [pow_two]; nlinarith [(Fact.out : q.Prime).one_lt]
  have hlt2 : Nat.log q (Nat.card ↥B) < 2 :=
    Nat.log_lt_of_lt_pow' two_ne_zero (lt_of_le_of_lt hBle hq2)
  omega

/-- Two Sylow `p`-subgroups, one normalizing the other, coincide: if `S ≤ N_G(P)` with `P`, `S`
both Sylow `p`-subgroups of `G`, then `S = P`. Indeed `P` is a normal (hence unique) Sylow
`p`-subgroup of `N_G(P)`, so the `p`-subgroup `S ≤ N_G(P)` lands inside it, and equal orders
force equality. -/
theorem sylow_eq_of_le_normalizer {p : ℕ} [Fact p.Prime] [Finite G]
    (P S : Sylow p G) (hSle : (S : Subgroup G) ≤ Subgroup.normalizer ((P : Subgroup G) : Set G)) :
    (S : Subgroup G) = (P : Subgroup G) := by
  classical
  have hPN : (P : Subgroup G) ≤ Subgroup.normalizer ((P : Subgroup G) : Set G) :=
    Subgroup.le_normalizer
  have : Unique (Sylow p ↥(Subgroup.normalizer ((P : Subgroup G) : Set G))) :=
    Sylow.unique_of_normal (P.subtype hPN) (by
      rw [Sylow.coe_subtype]; exact Subgroup.normal_in_normalizer)
  have heq : S.subtype hSle = P.subtype hPN := Subsingleton.elim _ _
  have hcoe : (S : Subgroup G).subgroupOf (Subgroup.normalizer ((P : Subgroup G) : Set G))
      = (P : Subgroup G).subgroupOf (Subgroup.normalizer ((P : Subgroup G) : Set G)) := by
    have h : ((S.subtype hSle : Sylow p ↥(Subgroup.normalizer ((P : Subgroup G) : Set G))) :
          Subgroup ↥(Subgroup.normalizer ((P : Subgroup G) : Set G)))
        = (P.subtype hPN : Subgroup ↥(Subgroup.normalizer ((P : Subgroup G) : Set G))) := by
      rw [heq]
    rwa [Sylow.coe_subtype, Sylow.coe_subtype] at h
  calc (S : Subgroup G)
      = Subgroup.map (Subgroup.normalizer ((P : Subgroup G) : Set G)).subtype
          ((S : Subgroup G).subgroupOf (Subgroup.normalizer ((P : Subgroup G) : Set G))) :=
        (Subgroup.map_subgroupOf_eq_of_le hSle).symm
    _ = Subgroup.map (Subgroup.normalizer ((P : Subgroup G) : Set G)).subtype
          ((P : Subgroup G).subgroupOf (Subgroup.normalizer ((P : Subgroup G) : Set G))) := by
        rw [hcoe]
    _ = (P : Subgroup G) := Subgroup.map_subgroupOf_eq_of_le hPN

/-- **Theorem 12.12, Case 3, the `r_q = 2` side** (BG L3364): in the abelian-Sylow regime, if
`q ∣ [E : C_E(A)]` and `q ∣ |C_E(A)|`, then `r_q(N_G(S)) = 2`. By Lemma 12.11(c) the maximal
`M* ∈ ℳ(N_G(A))` has `q ∈ τ₂(M*)` and contains a Sylow `p`-subgroup `P` of `G` normal in `M*`.
Since `S ≤ N_G(S) = N_G(A) ≤ M* ≤ N_G(P)` and both `S, P` are Sylow `p`-subgroups, `S = P`, hence
`M* ≤ N_G(S)`; with `N_G(S) ≤ M*` this gives `M* = N_G(S)`, so
`pRank (N_G(S)) q = pRank M* q = 2`. -/
theorem pRank_normalizer_eq_two_of_index_card [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ tau2 M) {A : Subgroup G} (hA : A ∈ elemAbelianOfRank G p 2) (hAE : A ≤ E)
    {S : Sylow p G} (hAS : A ≤ (S : Subgroup G)) (hSab : IsMulCommutative ↥(S : Subgroup G))
    {q : ℕ}
    (hqi : q ∈ (((E ⊓ Subgroup.centralizer (A : Set G)).subgroupOf E).index).primeFactors)
    (hqc : q ∈ (Nat.card ↥(E ⊓ Subgroup.centralizer (A : Set G))).primeFactors) :
    pRank ↥(Subgroup.normalizer ((S : Subgroup G) : Set G)) q = 2 := by
  classical
  have hAM : A ≤ M := hAE.trans h.E_le
  have hAne : A ≠ ⊥ := by
    intro hbot; have hcard := hA.2
    rw [hbot, Subgroup.card_bot] at hcard
    exact (Nat.one_lt_pow two_ne_zero (Fact.out : p.Prime).one_lt).ne' hcard.symm
  -- `N_G(A) = N_G(S)` (Lemma 12.8(d)).
  have hNAS : Subgroup.normalizer (A : Set G) = Subgroup.normalizer ((S : Subgroup G) : Set G) :=
    (normalizer_chain_of_abelianSylow hG h hp hA hAE hAS hSab).1
  -- choose `M* ∈ ℳ(N_G(A))`.
  obtain ⟨Mstar, hco, hle⟩ := (eq_top_or_exists_le_coatom _).resolve_left
    (normalizer_lt_top_of_le_of_ne_bot hG h.mem_maximal hAM hAne).ne
  have hMstar_mem : Mstar ∈ maximalSubgroupsContaining (Subgroup.normalizer (A : Set G)) :=
    mem_maximalSubgroupsContaining.mpr ⟨hco, hle⟩
  -- Lemma 12.11(c).
  obtain ⟨hqτ₂, ⟨P, hP_norm⟩, -⟩ :=
    (tau2_transfer_to_maximal hG h hp hA hAE hMstar_mem).2.2 q hqi hqc
  -- `S ≤ M* ≤ N_G(P)`, so `S = P`.
  have hSMstar : (S : Subgroup G) ≤ Mstar :=
    (hNAS ▸ (Subgroup.le_normalizer : (S : Subgroup G) ≤ _)).trans hle
  have hSeqP : (S : Subgroup G) = (P : Subgroup G) :=
    sylow_eq_of_le_normalizer P S (hSMstar.trans hP_norm)
  -- `M* = N_G(S)`.
  have hMstar_eq : Mstar = Subgroup.normalizer ((S : Subgroup G) : Set G) :=
    le_antisymm (by rw [hSeqP]; exact hP_norm) (hNAS ▸ hle)
  rw [← hMstar_eq]; exact tau2_pRank_eq_two hqτ₂

/-- If `H` is a normal subgroup not containing the Sylow `q`-subgroup `P`, then `q ∣ [K : H]`.
(The image of `P` in `K ⧸ H` is a `q`-subgroup whose order divides `[K : H]`; if `q ∤ [K : H]`
this order is `1`, forcing `P ≤ H`.) -/
theorem prime_dvd_index_of_sylow_not_le_of_normal {K : Type*} [Group K] [Finite K] {q : ℕ}
    [Fact q.Prime] (P : Sylow q K) {H : Subgroup K} [H.Normal] (hPH : ¬ (P : Subgroup K) ≤ H) :
    q ∣ H.index := by
  classical
  by_contra hq
  apply hPH
  intro x hxP
  have hPg : IsPGroup q ↥((P : Subgroup K).map (QuotientGroup.mk' H)) :=
    P.isPGroup'.map (QuotientGroup.mk' H)
  have hdvd : Nat.card ↥((P : Subgroup K).map (QuotientGroup.mk' H)) ∣ H.index := by
    rw [Subgroup.index_eq_card]; exact Subgroup.card_subgroup_dvd_card _
  have hcard1 : Nat.card ↥((P : Subgroup K).map (QuotientGroup.mk' H)) = 1 := by
    obtain ⟨k, hk⟩ := hPg.exists_card_eq
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rwa [pow_zero] at hk
    · exact absurd ((dvd_pow_self q hk0.ne').trans (hk ▸ hdvd)) hq
  have hmaptriv : (P : Subgroup K).map (QuotientGroup.mk' H) = ⊥ := Subgroup.card_eq_one.mp hcard1
  have hx1 : (QuotientGroup.mk' H) x = 1 := by
    have hmem : (QuotientGroup.mk' H) x ∈ (P : Subgroup K).map (QuotientGroup.mk' H) :=
      Subgroup.mem_map_of_mem _ hxP
    rw [hmaptriv, Subgroup.mem_bot] at hmem; exact hmem
  rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx1

/-- **Theorem 12.12, Case 3 front-half setup** (BG L3359-3361): in the abelian-Sylow regime with
the regularity hypothesis, if `C_E(S) ≠ E` then there is a prime `q ≠ p` and a Sylow
`q`-subgroup `Q₁` of `E` that is cyclic, lies in `τ₁(M)`, does **not** centralize `S`, and with
`q ∈ π(E/C_E(A)) ∩ π(C_E(A))`. (`q ∈ π(E/C_E(S))`, Prop 1.6(e) gives `Q₁ ⊄ C_E(A)`, Cor 12.10(c)
gives `q ∈ τ₁(M)` and `Q₁` cyclic, and a central `q`-line in `E₁` gives `q ∣ |C_E(A)|`.) -/
theorem exists_sylow_tau1_cyclic_notCentralizing [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ tau2 M) {A : Subgroup G} (hA : A ∈ elemAbelianOfRank G p 2) (hAE : A ≤ E)
    {S : Sylow p G} (hAS : A ≤ (S : Subgroup G)) (hSM : (S : Subgroup G) ≤ M)
    (hSab : IsMulCommutative ↥(S : Subgroup G))
    (hreg : ∀ e ∈ E, e ≠ 1 → (∀ r ∈ (orderOf e).primeFactors, r ∈ tau1 M ∪ tau3 M) →
      S10.Msigma M ⊓ Subgroup.centralizer ({e} : Set G) = ⊥)
    (hCES : Subgroup.centralizer ((S : Subgroup G) : Set G) ⊓ E ≠ E) :
    ∃ q : ℕ, ∃ Q₁ : Subgroup G, q.Prime ∧ q ≠ p ∧ IsPGroup q ↥Q₁ ∧ Q₁ ≤ E ∧
      (∀ R : Subgroup G, Q₁ ≤ R → R ≤ E → IsPGroup q ↥R → R = Q₁) ∧
      IsCyclic ↥Q₁ ∧
      ¬ ((Q₁ : Subgroup G) ≤ Subgroup.centralizer ((S : Subgroup G) : Set G)) ∧
      q ∈ (((E ⊓ Subgroup.centralizer (A : Set G)).subgroupOf E).index).primeFactors ∧
      q ∈ (Nat.card ↥(E ⊓ Subgroup.centralizer (A : Set G))).primeFactors := by
  classical
  have hAM : A ≤ M := hAE.trans h.E_le
  -- `S ≤ E` and `A = Ω₁(S)`.
  have hSE : (S : Subgroup G) ≤ E :=
    (le_centralizer_of_le_of_le hSab le_rfl hAS).trans (centralizer_le_E_of_tau2 hG h hp hA hAE).1
  have hAom : A = (Omega ↥(S : Subgroup G) p 1).map (S : Subgroup G).subtype :=
    (omega1_eq_of_tau2 hG h.mem_maximal hp hA hAM S.isPGroup' hAS hSM
      (sylow_maximal_in_M_of_le hSM)).1
  -- `C_E(A) ⊴ E` (Corollary 12.10(c)).
  have hCEAnorm : E ≤ Subgroup.normalizer ((E ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) : Set
      G) :=
    ((nilpotent_sigmaComplement_abelian hG h).2.2.1 p (Fact.out : p.Prime) hp A hA hAE).2.1
  have hCEA_norm : ((E ⊓ Subgroup.centralizer (A : Set G)).subgroupOf E).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr hCEAnorm
  -- choose `q ∈ π(E/C_E(S))` and a Sylow `q`-subgroup `Q₁` of `E`.
  have hHne : (Subgroup.centralizer ((S : Subgroup G) : Set G) ⊓ E).subgroupOf E ≠ ⊤ := by
    rw [ne_eq, Subgroup.subgroupOf_eq_top]; intro hle; exact hCES (le_antisymm inf_le_right hle)
  obtain ⟨q, hq_prime, hq_dvd⟩ := Nat.exists_prime_and_dvd
    (fun hi => hHne (Subgroup.index_eq_one.mp hi))
  have : Fact q.Prime := ⟨hq_prime⟩
  obtain ⟨Q₁'⟩ : Nonempty (Sylow q ↥E) := inferInstance
  set Q₁ : Subgroup G := (Q₁' : Subgroup ↥E).map E.subtype with hQ₁def
  have hQ₁E : Q₁ ≤ E := by rw [hQ₁def]; exact Subgroup.map_subtype_le _
  have hQ₁pg : IsPGroup q ↥Q₁ := by rw [hQ₁def]; exact Q₁'.isPGroup'.map E.subtype
  -- `Q₁` is a Sylow `q`-subgroup of `E`.
  have hQ₁maxE : ∀ R : Subgroup G, Q₁ ≤ R → R ≤ E → IsPGroup q ↥R → R = Q₁ := by
    intro R hQ₁R hRE hRpg
    have hRsubpg : IsPGroup q ↥(R.subgroupOf E) := by
      apply (IsPGroup.iff_card).mpr
      obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hRpg
      exact ⟨k, by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRE).toEquiv, hk]⟩
    have hQ₁'R : Q₁' ≤ R.subgroupOf E :=
      Subgroup.map_le_iff_le_comap.mp (by rw [← hQ₁def]; exact hQ₁R)
    have heq : R.subgroupOf E = (Q₁' : Subgroup ↥E) := Q₁'.3 hRsubpg hQ₁'R
    calc R = (R.subgroupOf E).map E.subtype := (Subgroup.map_subgroupOf_eq_of_le hRE).symm
      _ = Q₁ := by rw [heq, hQ₁def]
  -- `Q₁ ⊄ C(S)`, i.e. `C_S(Q₁) ⊊ S`.
  have hQ₁ncS : ¬ ((Q₁ : Subgroup G) ≤ Subgroup.centralizer ((S : Subgroup G) : Set G)) := by
    have hnle : ¬ (Q₁' ≤ (Subgroup.centralizer ((S:Subgroup G):Set G) ⊓ E).subgroupOf E) :=
      sylow_not_le_of_prime_dvd_index Q₁' hq_dvd
    intro hcon
    exact hnle (Subgroup.map_le_iff_le_comap.mp (by rw [← hQ₁def]; exact le_inf hcon hQ₁E))
  -- `q ≠ p` (a Sylow `p` of `E`, namely `S`, lies in `C_E(S)`).
  have hqp : q ≠ p := by
    rintro rfl
    have hSsub : (S.subtype hSE : Subgroup ↥E) ≤
        (Subgroup.centralizer ((S:Subgroup G):Set G) ⊓ E).subgroupOf E := by
      rw [Sylow.coe_subtype]
      exact Subgroup.comap_mono (le_inf (le_centralizer_of_le_of_le hSab le_rfl le_rfl) hSE)
    exact sylow_not_le_of_prime_dvd_index (S.subtype hSE) hq_dvd hSsub
  -- `Q₁ ⊄ C_E(A)` (Prop 1.6(e) contrapositive), hence `q ∣ [E : C_E(A)]` (`C_E(A) ⊴ E`).
  have hQ₁NS : (Q₁ : Subgroup G) ≤ Subgroup.normalizer ((S : Subgroup G) : Set G) :=
    hQ₁E.trans (E_le_normalizer_sylow_of_abelianSylow hG h hp hA hAE hAS hSab)
  have hcopSQ₁ : Nat.Coprime (Nat.card ↥(S : Subgroup G)) (Nat.card ↥Q₁) := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := p)).mp S.isPGroup'
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card (p := q)).mp hQ₁pg
    rw [hn, hm]
    exact ((Nat.coprime_primes (Fact.out : p.Prime) hq_prime).mpr (Ne.symm hqp)).pow n m
  have hQ₁ncA : ¬ ((Q₁ : Subgroup G) ≤ Subgroup.centralizer (A : Set G)) := by
    intro hcon
    refine hQ₁ncS (le_centralizer_swap ?_)
    exact centralizer_le_of_omega1_le_centralizer hSab S.isPGroup' hQ₁NS hcopSQ₁
      (hAom ▸ le_centralizer_swap hcon)
  have hQ₁'ncA : ¬ (Q₁' ≤ (E ⊓ Subgroup.centralizer (A : Set G)).subgroupOf E) := by
    intro hcon
    have hmap : Q₁ ≤ E ⊓ Subgroup.centralizer (A : Set G) := by
      rw [hQ₁def]; exact Subgroup.map_le_iff_le_comap.mpr hcon
    exact hQ₁ncA (hmap.trans inf_le_right)
  have hqidvd : q ∣ ((E ⊓ Subgroup.centralizer (A : Set G)).subgroupOf E).index :=
    prime_dvd_index_of_sylow_not_le_of_normal Q₁' hQ₁'ncA
  have hqi : q ∈ (((E ⊓ Subgroup.centralizer (A : Set G)).subgroupOf E).index).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hq_prime, hqidvd, Subgroup.index_ne_zero_of_finite⟩
  -- `q ∈ τ₁(M)` (Cor 12.10(c)), and `Q₁` cyclic.
  have hqτ₁ : q ∈ tau1 M :=
    ((nilpotent_sigmaComplement_abelian hG h).2.2.1 p (Fact.out : p.Prime) hp A hA hAE).2.2 q hqi
  have hqodd : Odd q := hG.odd.of_dvd_nat
    ((hqidvd.trans (Subgroup.index_dvd_card _)).trans (Subgroup.card_subgroup_dvd_card E))
  have hQ₁cyc : IsCyclic ↥Q₁ := by
    refine S10.isCyclic_of_pRank_le_one hQ₁pg hqodd ?_
    have h1 : pRank ↥Q₁ q ≤ pRank ↥M q :=
      pRank_le_of_injective (f := Subgroup.inclusion (hQ₁E.trans h.E_le))
        (Subgroup.inclusion_injective _)
    rwa [tau1_pRank_eq_one hqτ₁] at h1
  -- `q ∣ |C_E(A)|` via a central `τ₁`-line `X'` in `E₁` (Lemma 12.8(e)).
  have hqcard_E : q ∣ Nat.card ↥E := hqidvd.trans (Subgroup.index_dvd_card _)
  have hq_notidx : ¬ q ∣ (E₁.subgroupOf E).index := fun hd =>
    (h.E₁_hall.index_no_pi q
      (Nat.mem_primeFactors.mpr ⟨hq_prime, hd, Subgroup.index_ne_zero_of_finite⟩)) hqτ₁
  have hqE₁ : q ∣ Nat.card ↥E₁ := by
    have hcard := Subgroup.card_mul_index (E₁.subgroupOf E)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₁_le).toEquiv] at hcard
    rcases (hq_prime.dvd_mul).mp (hcard ▸ hqcard_E) with h' | h'
    · exact h'
    · exact absurd h' hq_notidx
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' q hqE₁
  have hg'E₁ : (g : G) ∈ E₁ := g.2
  have hg'ord : orderOf (g : G) = q := by
    rw [← hg]; exact orderOf_injective E₁.subtype E₁.subtype_injective g
  have hg'ne : (g : G) ≠ 1 := by
    intro h1; rw [h1, orderOf_one] at hg'ord; exact hq_prime.ne_one hg'ord.symm
  set X' : Subgroup G := Subgroup.zpowers (g : G) with hX'def
  have hX'E₁ : X' ≤ E₁ := by rw [hX'def, Subgroup.zpowers_le]; exact hg'E₁
  have hX'card : Nat.card ↥X' = q := by rw [hX'def, Nat.card_zpowers, hg'ord]
  have hX'mem : X' ∈ elemAbelianOfRank G q 1 :=
    ⟨Subgroup.IsElementaryAbelian.of_card_prime hX'card, by rw [pow_one]; exact hX'card⟩
  have hMσCX' : S10.Msigma M ⊓ Subgroup.centralizer (X' : Set G) = ⊥ := by
    rw [hX'def, centralizer_zpowers_eq_singleton]
    refine hreg (g : G) (h.E₁_le hg'E₁) hg'ne (fun r hr => ?_)
    rw [hg'ord, hq_prime.primeFactors, Finset.mem_singleton] at hr
    rw [hr]; exact Set.mem_union_left _ hqτ₁
  obtain ⟨-, hEcent⟩ := central_line_of_abelianSylow hG h hp hA hAE hAS hSab X'
    ⟨q, hq_prime, hX'mem⟩ hX'E₁ hMσCX'
  have hX'CEA : X' ≤ E ⊓ Subgroup.centralizer (A : Set G) :=
    le_inf (hX'E₁.trans h.E₁_le) (le_centralizer_swap (hAE.trans hEcent))
  have hqc : q ∈ (Nat.card ↥(E ⊓ Subgroup.centralizer (A : Set G))).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hq_prime, hX'card ▸ Subgroup.card_dvd_of_le hX'CEA, Nat.card_pos.ne'⟩
  exact ⟨q, Q₁, hq_prime, hqp, hQ₁pg, hQ₁E, hQ₁maxE, hQ₁cyc, hQ₁ncS, hqi, hqc⟩

/-- **Theorem 12.12, Case 3 front-half** (BG L3359-3370): in the abelian-Sylow regime with the
regularity hypothesis, if `C_E(S) ≠ E` then some `X ≤ N_G(S)` (a `q`-subgroup) has
`1 ⊊ C_S(X) ⊊ S`. If not, the Sylow `q`-subgroup `Q` of `N_G(S)` containing `Q₁` would act
regularly on `S` modulo `C_Q(S)`, making `Q ⧸ C_Q(S)` cyclic and `pRank Q q ≤ 1`; but
`pRank Q q = r_q(N_G(S)) = 2`, a contradiction. This `X` feeds
`exists_invariant_cyclic_sameExponent_regular`. -/
theorem exists_partial_centralizer_of_abelianSylow [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ tau2 M) {A : Subgroup G} (hA : A ∈ elemAbelianOfRank G p 2) (hAE : A ≤ E)
    {S : Sylow p G} (hAS : A ≤ (S : Subgroup G)) (hSM : (S : Subgroup G) ≤ M)
    (hSab : IsMulCommutative ↥(S : Subgroup G))
    (hreg : ∀ e ∈ E, e ≠ 1 → (∀ r ∈ (orderOf e).primeFactors, r ∈ tau1 M ∪ tau3 M) →
      S10.Msigma M ⊓ Subgroup.centralizer ({e} : Set G) = ⊥)
    (hCES : Subgroup.centralizer ((S : Subgroup G) : Set G) ⊓ E ≠ E) :
    ∃ X : Subgroup G, X ≤ Subgroup.normalizer ((S : Subgroup G) : Set G) ∧
      Nat.Coprime (Nat.card ↥(S : Subgroup G)) (Nat.card ↥X) ∧
      (S : Subgroup G) ⊓ Subgroup.centralizer (X : Set G) ≠ ⊥ ∧
      (S : Subgroup G) ⊓ Subgroup.centralizer (X : Set G) ≠ (S : Subgroup G) := by
  classical
  obtain ⟨q, Q₁, hq_prime, hqp, hQ₁pg, hQ₁E, hQ₁maxE, hQ₁cyc, hQ₁ncS, hqi, hqc⟩ :=
    exists_sylow_tau1_cyclic_notCentralizing hG h hp hA hAE hAS hSM hSab hreg hCES
  have : Fact q.Prime := ⟨hq_prime⟩
  have hpG : p ∣ Nat.card G :=
    (hA.2 ▸ dvd_pow_self p two_ne_zero).trans (Subgroup.card_subgroup_dvd_card A)
  have hqodd : Odd q := hG.odd.of_dvd_nat
    ((Nat.dvd_of_mem_primeFactors hqc).trans (Subgroup.card_subgroup_dvd_card _))
  have hSne : (S : Subgroup G) ≠ ⊥ := Sylow.ne_bot_of_dvd_card S hpG
  have hCSE : Subgroup.centralizer ((S : Subgroup G) : Set G) ≤ E :=
    (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hAS)).trans
      (centralizer_le_E_of_tau2 hG h hp hA hAE).1
  set NS : Subgroup G := Subgroup.normalizer ((S : Subgroup G) : Set G) with hNSdef
  have hENS : E ≤ NS := E_le_normalizer_sylow_of_abelianSylow hG h hp hA hAE hAS hSab
  have hQ₁NS : Q₁ ≤ NS := hQ₁E.trans hENS
  -- a Sylow `q`-subgroup `Q` of `N_G(S)` containing `Q₁`.
  have hQ₁subNS_pg : IsPGroup q ↥(Q₁.subgroupOf NS) := by
    apply (IsPGroup.iff_card).mpr
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hQ₁pg
    exact ⟨k, by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ₁NS).toEquiv, hk]⟩
  obtain ⟨Q', hQ₁Q'⟩ := hQ₁subNS_pg.exists_le_sylow
  set Q : Subgroup G := (Q' : Subgroup ↥NS).map NS.subtype with hQdef
  have hQNS : Q ≤ NS := by rw [hQdef]; exact Subgroup.map_subtype_le _
  have hQpg : IsPGroup q ↥Q := by rw [hQdef]; exact Q'.isPGroup'.map NS.subtype
  have hQ₁Q : Q₁ ≤ Q := by
    rw [hQdef, ← Subgroup.map_subgroupOf_eq_of_le hQ₁NS]; exact Subgroup.map_mono hQ₁Q'
  -- `pRank Q q = 2` (Sylow of `N_G(S)`, the `r_q = 2` lemma).
  have hpR2 : pRank ↥Q q = 2 := by
    have e := Subgroup.equivMapOfInjective (Q' : Subgroup ↥NS) NS.subtype NS.subtype_injective
    have hmapeq : pRank ↥Q q = pRank ↥(Q' : Subgroup ↥NS) q :=
      le_antisymm (pRank_le_of_injective (f := e.symm.toMonoidHom) e.symm.injective)
        (pRank_le_of_injective (f := e.toMonoidHom) e.injective)
    rw [hmapeq, pRank_sylow_eq Q']
    exact pRank_normalizer_eq_two_of_index_card hG h hp hA hAE hAS hSab hqi hqc
  -- `E ⊓ Q = Q₁` (`Q₁` is the Sylow `q` of `E` inside `Q`).
  have hEQ : E ⊓ Q = Q₁ :=
    hQ₁maxE (E ⊓ Q) (le_inf hQ₁E hQ₁Q) inf_le_left (hQpg.to_le inf_le_right)
  by_contra hcon
  push Not at hcon
  -- regularity of `Q` on `S` modulo `C_G(S)`.
  have hreg' : ∀ x ∈ Q, x ∉ Subgroup.centralizer ((S : Subgroup G) : Set G) →
      (S : Subgroup G) ⊓ Subgroup.centralizer ({x} : Set G) = ⊥ := by
    intro x hxQ hxnc
    by_contra hne
    have hxNS : Subgroup.zpowers x ≤ NS := Subgroup.zpowers_le.mpr (hQNS hxQ)
    have hcopx : Nat.Coprime (Nat.card ↥(S : Subgroup G)) (Nat.card ↥(Subgroup.zpowers x)) := by
      obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := p)).mp S.isPGroup'
      obtain ⟨m, hm⟩ := (IsPGroup.iff_card (p := q)).mp
        (hQpg.to_le (Subgroup.zpowers_le.mpr hxQ))
      rw [hn, hm]
      exact ((Nat.coprime_primes (Fact.out : p.Prime) hq_prime).mpr (Ne.symm hqp)).pow n m
    have hSC : (S : Subgroup G) ⊓ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G)
        = (S : Subgroup G) :=
      hcon (Subgroup.zpowers x) hxNS hcopx
        (by rw [centralizer_zpowers_eq_singleton]; exact hne)
    rw [centralizer_zpowers_eq_singleton] at hSC
    apply hxnc
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact (Subgroup.mem_centralizer_iff.mp (hSC.ge hs).2 x (Set.mem_singleton x)).symm
  -- `Q ⧸ C_Q(S)` cyclic (Prop 3.9 via the φ̄ wrapper).
  have hcyc : IsCyclic (↥Q ⧸ (conjActionHom hQNS).ker) :=
    isCyclic_quotient_of_conjugation_fpf hQNS S.isPGroup' hQpg hSne hqodd (Ne.symm hqp) hreg'
  -- `C_Q(S) ⊊ Q₁` inside `Q`.
  have hker_lt : (conjActionHom hQNS).ker < Q₁.subgroupOf Q := by
    rw [conjActionHom_ker]
    refine lt_of_le_of_ne ?_ ?_
    · intro y hy
      have hyC : (y : G) ∈ Subgroup.centralizer ((S : Subgroup G) : Set G) :=
        (Subgroup.mem_subgroupOf).mp hy
      have hyQ₁ : (y : G) ∈ Q₁ := by
        have hmem : (y : G) ∈ E ⊓ Q := ⟨hCSE hyC, y.2⟩
        rwa [hEQ] at hmem
      exact (Subgroup.mem_subgroupOf).mpr hyQ₁
    · intro heq
      apply hQ₁ncS
      intro x hxQ₁
      have hxmem : (⟨x, hQ₁Q hxQ₁⟩ : ↥Q) ∈ Q₁.subgroupOf Q :=
        (Subgroup.mem_subgroupOf).mpr hxQ₁
      rw [← heq, Subgroup.mem_subgroupOf] at hxmem
      exact hxmem
  have hQ₁subQ_cyc : IsCyclic ↥(Q₁.subgroupOf Q) :=
    isCyclic_of_surjective _ (Subgroup.subgroupOfEquivOfLe hQ₁Q).symm.surjective
  have hpR1 : pRank ↥Q q ≤ 1 :=
    pRank_le_one_of_cyclic_quotient hQpg hqodd hcyc hker_lt hQ₁subQ_cyc
  rw [hpR2] at hpR1
  omega

/-- A subgroup of order `p` is generated by any of its nonidentity elements. -/
theorem exists_generator_of_card_prime [Finite G] {p : ℕ} [Fact p.Prime] {L : Subgroup G}
    (hLp : Nat.card ↥L = p) : ∃ w : G, orderOf w = p ∧ Subgroup.zpowers w = L := by
  have : Nontrivial ↥L := (Subgroup.nontrivial_iff_ne_bot L).mpr (by
    intro hbot; rw [hbot, Subgroup.card_bot] at hLp; exact (Fact.out : p.Prime).ne_one hLp.symm)
  obtain ⟨w, hw⟩ := exists_ne (1 : ↥L)
  have hwL : (w : G) ∈ L := w.2
  have hwne : (w : G) ≠ 1 := fun hc => hw (Subtype.ext (by rw [hc]; rfl))
  have hord : orderOf (w : G) = p := by
    have hd : orderOf (w : G) ∣ p := by
      have h1 : orderOf (w : G) = orderOf w := orderOf_injective L.subtype L.subtype_injective w
      rw [h1, ← hLp]; exact orderOf_dvd_natCard w
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hd with h1 | hp'
    · exact absurd (orderOf_eq_one_iff.mp h1) hwne
    · exact hp'
  exact ⟨(w : G), hord, Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hwL)
    (by rw [Nat.card_zpowers, hord]; exact hLp.le)⟩

set_option maxHeartbeats 1000000 in
-- raised heartbeat budget for the heavy elaboration below
/-- **Theorem 12.12, Case 3, the `C_E(S) = E` branch** (BG L3349-3358): in the abelian-Sylow
regime with the regularity hypothesis, if `C_E(S) = E` then `S` has a cyclic subgroup `Z` of
exponent `exp(S)`, normalized by `E`, acting regularly on `M_σ`. (Construction avoiding the
`S = Y × Z` decomposition: take a good line `L = ⟨w⟩ ≤ ℧^{a-1}(S)` with `C_{M_σ}(L) = 1` — if
`℧^{a-1}(S) = A`, Theorem 12.5(f); else `℧^{a-1}(S)` is a characteristic line, the key fact — and
write `w = s^{p^{a-1}}` with `orderOf s = p^a = exp(S)`, `Z = ⟨s⟩`.) -/
theorem exists_cyclic_Enormal_regular_of_CES_eq [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ tau2 M) {A : Subgroup G} (hA : A ∈ elemAbelianOfRank G p 2) (hAE : A ≤ E)
    {S : Sylow p G} (hAS : A ≤ (S : Subgroup G)) (hSM : (S : Subgroup G) ≤ M)
    (hSab : IsMulCommutative ↥(S : Subgroup G))
    (_hreg : ∀ e ∈ E, e ≠ 1 → (∀ r ∈ (orderOf e).primeFactors, r ∈ tau1 M ∪ tau3 M) →
      S10.Msigma M ⊓ Subgroup.centralizer ({e} : Set G) = ⊥)
    (hCES : Subgroup.centralizer ((S : Subgroup G) : Set G) ⊓ E = E) :
    ∃ Z : Subgroup G, Z ≤ (S : Subgroup G) ∧ IsCyclic ↥Z ∧ Z ≠ ⊥ ∧
      E ≤ Subgroup.normalizer (Z : Set G) ∧
      Monoid.exponent ↥Z = Monoid.exponent ↥(S : Subgroup G) ∧
      ∀ z ∈ Z, z ≠ 1 → S10.Msigma M ⊓ Subgroup.centralizer ({z} : Set G) = ⊥ := by
  classical
  have := hSab
  have hAM : A ≤ M := hAE.trans h.E_le
  have hEC : E ≤ Subgroup.centralizer ((S : Subgroup G) : Set G) := by
    rw [← hCES]; exact inf_le_left
  have hAom : A = (Omega ↥(S : Subgroup G) p 1).map (S : Subgroup G).subtype :=
    (omega1_eq_of_tau2 hG h.mem_maximal hp hA hAM S.isPGroup' hAS hSM
      (sylow_maximal_in_M_of_le hSM)).1
  obtain ⟨a, ha⟩ : ∃ a, Monoid.exponent ↥(S : Subgroup G) = p ^ a := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp S.isPGroup'
    obtain ⟨b, _, hb⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp
      (hn ▸ Group.exponent_dvd_nat_card)
    exact ⟨b, hb⟩
  have hpG : p ∣ Nat.card G :=
    (hA.2 ▸ dvd_pow_self p two_ne_zero).trans (Subgroup.card_subgroup_dvd_card A)
  have hSne : (S : Subgroup G) ≠ ⊥ := Sylow.ne_bot_of_dvd_card S hpG
  have : Nontrivial ↥(S : Subgroup G) := (Subgroup.nontrivial_iff_ne_bot _).mpr hSne
  have ha1 : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with rfl | hpos
    · exfalso
      obtain ⟨s, hs⟩ := exists_ne (1 : ↥(S : Subgroup G))
      have hd : orderOf s ∣ Monoid.exponent ↥(S : Subgroup G) := Monoid.order_dvd_exponent s
      rw [ha, pow_zero, Nat.dvd_one, orderOf_eq_one_iff] at hd
      exact hs hd
    · exact hpos
  set UG : Subgroup G := (Agemo ↥(S : Subgroup G) p (a - 1)).map (S : Subgroup G).subtype
    with hUGdef
  have hAgemo_le_Omega : Agemo ↥(S : Subgroup G) p (a - 1) ≤ Omega ↥(S : Subgroup G) p 1 := by
    rw [Agemo, Subgroup.closure_le]
    rintro g ⟨x, rfl⟩
    refine Omega.mem_of_pow_eq_one ?_
    calc (x ^ p ^ (a - 1)) ^ p ^ 1
        = x ^ (p ^ (a - 1) * p ^ 1) := (pow_mul x _ _).symm
      _ = x ^ p ^ a := by rw [← pow_add, Nat.sub_add_cancel ha1]
      _ = 1 := by rw [← ha]; exact Monoid.pow_exponent_eq_one x
  have hUG_le_A : UG ≤ A := by rw [hUGdef, hAom]; exact Subgroup.map_mono hAgemo_le_Omega
  have hUGS : UG ≤ (S : Subgroup G) := hUG_le_A.trans hAS
  have hUG_ne : UG ≠ ⊥ := by
    rw [hUGdef, ne_eq, Subgroup.map_eq_bot_iff_of_injective _ (S : Subgroup G).subtype_injective]
    intro hAgemo_bot
    have hall : ∀ x : ↥(S : Subgroup G), x ^ (p ^ (a - 1)) = 1 := fun x => by
      have hx := Agemo.mem_of_eq_pow (p := p) (n := a - 1) x
      rw [hAgemo_bot, Subgroup.mem_bot] at hx; exact hx
    have hdvd : Monoid.exponent ↥(S : Subgroup G) ∣ p ^ (a - 1) :=
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hall
    rw [ha] at hdvd
    have hle := Nat.le_of_dvd (pow_pos (Fact.out : p.Prime).pos _) hdvd
    have hlt : p ^ (a - 1) < p ^ a := Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt (by omega)
    omega
  -- A good line `wG`-generated, contained in `℧^{a-1}(S)`.
  obtain ⟨wG, hwG_ord, hwG_good, hwG_mem⟩ :
      ∃ wG : G, orderOf wG = p ∧
        S10.Msigma M ⊓ Subgroup.centralizer ((Subgroup.zpowers wG : Subgroup G) : Set G) = ⊥ ∧
        wG ∈ UG := by
    by_cases hUGA : A ≤ UG
    · obtain ⟨A₁, hA₁mem, hA₁A, hA₁good⟩ :=
        (Msigma_nilpotent_of_tau2 hG h.mem_maximal hp hA hAM).2.2.2.2.2
      have hA₁card : Nat.card ↥A₁ = p := by rw [hA₁mem.2, pow_one]
      obtain ⟨w, hword, hwgen⟩ := exists_generator_of_card_prime hA₁card
      refine ⟨w, hword, by rw [hwgen]; exact hA₁good, hUGA (hA₁A ?_)⟩
      rw [← hwgen]; exact Subgroup.mem_zpowers w
    · have hUGltA : UG < A := lt_of_le_of_ne hUG_le_A (fun he => hUGA he.ge)
      have hdvd : Nat.card ↥UG ∣ p ^ 2 := by rw [← hA.2]; exact Subgroup.card_dvd_of_le hUG_le_A
      have hne1 : Nat.card ↥UG ≠ 1 := by rw [Ne, Subgroup.card_eq_one]; exact hUG_ne
      have hne2 : Nat.card ↥UG ≠ p ^ 2 := fun hc2 =>
        (ne_of_lt hUGltA) (Subgroup.eq_of_le_of_card_ge hUG_le_A (by rw [hc2, hA.2]))
      have hUGcard : Nat.card ↥UG = p := by
        obtain ⟨c, hc_le, hc⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hdvd
        interval_cases c
        · rw [pow_zero] at hc; exact absurd hc hne1
        · rw [pow_one] at hc; exact hc
        · exact absurd hc hne2
      have hUGmem : UG ∈ elemAbelianOfRank G p 1 :=
        ⟨Subgroup.IsElementaryAbelian.of_card_prime hUGcard, by rw [pow_one]; exact hUGcard⟩
      have hUGinv : Subgroup.normalizer ((S : Subgroup G) : Set G) ≤
          Subgroup.normalizer (UG : Set G) := by
        rw [hUGdef]
        exact OddOrder.BG.AppB.normalizer_le_normalizer_map_of_characteristic
          (K := (S : Subgroup G)) (W := Agemo ↥(S : Subgroup G) p (a - 1))
      have hgood : S10.Msigma M ⊓ Subgroup.centralizer (UG : Set G) = ⊥ :=
        inf_centralizer_line_eq_bot_of_invariant hG h hp hA hAE hAS hSM hUGmem hUGS hUGinv
      obtain ⟨w, hword, hwgen⟩ := exists_generator_of_card_prime hUGcard
      refine ⟨w, hword, by rw [hwgen]; exact hgood, ?_⟩
      rw [← hwgen]; exact Subgroup.mem_zpowers w
  -- extract `s` with `s^{p^{a-1}} = wG`, `orderOf s = p^a = exp(S)`.
  rw [hUGdef] at hwG_mem
  obtain ⟨y', hy'mem, hy'eq⟩ := hwG_mem
  obtain ⟨t, ht⟩ := mem_agemo_iff_of_comm.mp
    (show y' ∈ Agemo ↥(S : Subgroup G) p (a - 1) from hy'mem)
  set s : G := (t : G) with hsdef
  have hsw : s ^ (p ^ (a - 1)) = wG := by
    rw [hsdef, ← hy'eq, ht]; exact (SubmonoidClass.coe_pow t _).symm
  have hsS : s ∈ (S : Subgroup G) := by rw [hsdef]; exact t.2
  have hsord : orderOf s = p ^ a := by
    have hsexp : orderOf s ∣ p ^ a := by
      rw [← ha, hsdef]
      exact (orderOf_injective (S : Subgroup G).subtype (S : Subgroup G).subtype_injective t) ▸
        Monoid.order_dvd_exponent t
    have hnd : ¬ orderOf s ∣ p ^ (a - 1) := by
      intro hd
      have hwG1 : wG = 1 := by rw [← hsw]; exact orderOf_dvd_iff_pow_eq_one.mp hd
      rw [hwG1, orderOf_one] at hwG_ord
      exact (Fact.out : p.Prime).ne_one hwG_ord.symm
    obtain ⟨c, hc_le, hc⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hsexp
    rw [hc]; congr 1
    by_contra hca
    rw [hc] at hnd
    exact hnd (pow_dvd_pow p (by omega))
  -- `Z = ⟨s⟩`.
  have hsne : s ≠ 1 := by
    intro h1; rw [h1, orderOf_one] at hsord
    exact (Nat.one_lt_pow (by omega) (Fact.out : p.Prime).one_lt).ne hsord
  have hZS : Subgroup.zpowers s ≤ (S : Subgroup G) := Subgroup.zpowers_le.mpr hsS
  have hLZ : (Subgroup.zpowers wG : Subgroup G) ≤ Subgroup.zpowers s := by
    rw [← hsw]
    exact Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ (Subgroup.mem_zpowers s) _)
  refine ⟨Subgroup.zpowers s, hZS, inferInstance, (Subgroup.zpowers_eq_bot.not.mpr hsne), ?_, ?_,
      ?_⟩
  · -- `E ≤ N_G(⟨s⟩)`: `E ≤ C(S) ≤ C({s}) = C(⟨s⟩) ≤ N(⟨s⟩)`.
    have hEC' : E ≤ Subgroup.centralizer ({s} : Set G) :=
      hEC.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hsS))
    rw [← centralizer_zpowers_eq_singleton] at hEC'
    exact hEC'.trans (Subgroup.centralizer_le_normalizer _)
  · -- `exp(⟨s⟩) = exp(S)`.
    rw [IsCyclic.exponent_eq_card, Nat.card_zpowers, hsord, ha]
  · -- regularity, via the back-half line-to-cyclic lemma.
    exact inf_centralizer_eq_bot_of_line_le_cyclic (S.isPGroup'.to_le hZS) hLZ
      (by rw [Nat.card_zpowers, hwG_ord]) hwG_good

/-- **Regular cyclic line in an abelian Sylow `p`-subgroup**
(`exists_cyclic_Enormal_regular_of_CES_eq`
with the two hypotheses used *only* for the `E ≤ N_G(Z)` conclusion removed).  In
`exists_cyclic_Enormal_regular_of_CES_eq` the regularity input `hreg` is never used in the
`C_E(S)=E` branch, and `hCES` is used solely to derive `E ≤ C_G(S)` (`hEC`) for `E ≤ N_G(Z)`.
Dropping both and that conclusion yields: for a maximal `M`, `p ∈ τ₂(M)`, `A ∈ ℰ_p²(G)` inside an
abelian Sylow `p`-subgroup `S ≤ M` (with `A ≤ E`), there is a cyclic `Z ≤ S` of exponent `exp S`
acting regularly on `M_σ`.  Used by the type-`P` case of BG Lemma 15.1(e), where `S = Sylow_p(U)`
and `C_E(S)=E` fails for the full `σ`-complement `E = KU` (and `hreg` is false there, since
`κ(M) ⊆ τ₁(M) ∪ τ₃(M)`). -/
theorem exists_regular_cyclic_in_abelianSylow_tau2 [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ tau2 M) {A : Subgroup G} (hA : A ∈ elemAbelianOfRank G p 2) (hAE : A ≤ E)
    {S : Sylow p G} (hAS : A ≤ (S : Subgroup G)) (hSM : (S : Subgroup G) ≤ M)
    (hSab : IsMulCommutative ↥(S : Subgroup G)) :
    ∃ Z : Subgroup G, Z ≤ (S : Subgroup G) ∧ IsCyclic ↥Z ∧ Z ≠ ⊥ ∧
      Monoid.exponent ↥Z = Monoid.exponent ↥(S : Subgroup G) ∧
      ∀ z ∈ Z, z ≠ 1 → S10.Msigma M ⊓ Subgroup.centralizer ({z} : Set G) = ⊥ := by
  classical
  have := hSab
  have hAM : A ≤ M := hAE.trans h.E_le
  have hAom : A = (Omega ↥(S : Subgroup G) p 1).map (S : Subgroup G).subtype :=
    (omega1_eq_of_tau2 hG h.mem_maximal hp hA hAM S.isPGroup' hAS hSM
      (sylow_maximal_in_M_of_le hSM)).1
  obtain ⟨a, ha⟩ : ∃ a, Monoid.exponent ↥(S : Subgroup G) = p ^ a := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp S.isPGroup'
    obtain ⟨b, _, hb⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp
      (hn ▸ Group.exponent_dvd_nat_card)
    exact ⟨b, hb⟩
  have hpG : p ∣ Nat.card G :=
    (hA.2 ▸ dvd_pow_self p two_ne_zero).trans (Subgroup.card_subgroup_dvd_card A)
  have hSne : (S : Subgroup G) ≠ ⊥ := Sylow.ne_bot_of_dvd_card S hpG
  have : Nontrivial ↥(S : Subgroup G) := (Subgroup.nontrivial_iff_ne_bot _).mpr hSne
  have ha1 : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with rfl | hpos
    · exfalso
      obtain ⟨s, hs⟩ := exists_ne (1 : ↥(S : Subgroup G))
      have hd : orderOf s ∣ Monoid.exponent ↥(S : Subgroup G) := Monoid.order_dvd_exponent s
      rw [ha, pow_zero, Nat.dvd_one, orderOf_eq_one_iff] at hd
      exact hs hd
    · exact hpos
  set UG : Subgroup G := (Agemo ↥(S : Subgroup G) p (a - 1)).map (S : Subgroup G).subtype
    with hUGdef
  have hAgemo_le_Omega : Agemo ↥(S : Subgroup G) p (a - 1) ≤ Omega ↥(S : Subgroup G) p 1 := by
    rw [Agemo, Subgroup.closure_le]
    rintro g ⟨x, rfl⟩
    refine Omega.mem_of_pow_eq_one ?_
    calc (x ^ p ^ (a - 1)) ^ p ^ 1
        = x ^ (p ^ (a - 1) * p ^ 1) := (pow_mul x _ _).symm
      _ = x ^ p ^ a := by rw [← pow_add, Nat.sub_add_cancel ha1]
      _ = 1 := by rw [← ha]; exact Monoid.pow_exponent_eq_one x
  have hUG_le_A : UG ≤ A := by rw [hUGdef, hAom]; exact Subgroup.map_mono hAgemo_le_Omega
  have hUGS : UG ≤ (S : Subgroup G) := hUG_le_A.trans hAS
  have hUG_ne : UG ≠ ⊥ := by
    rw [hUGdef, ne_eq, Subgroup.map_eq_bot_iff_of_injective _ (S : Subgroup G).subtype_injective]
    intro hAgemo_bot
    have hall : ∀ x : ↥(S : Subgroup G), x ^ (p ^ (a - 1)) = 1 := fun x => by
      have hx := Agemo.mem_of_eq_pow (p := p) (n := a - 1) x
      rw [hAgemo_bot, Subgroup.mem_bot] at hx; exact hx
    have hdvd : Monoid.exponent ↥(S : Subgroup G) ∣ p ^ (a - 1) :=
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hall
    rw [ha] at hdvd
    have hle := Nat.le_of_dvd (pow_pos (Fact.out : p.Prime).pos _) hdvd
    have hlt : p ^ (a - 1) < p ^ a := Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt (by omega)
    omega
  obtain ⟨wG, hwG_ord, hwG_good, hwG_mem⟩ :
      ∃ wG : G, orderOf wG = p ∧
        S10.Msigma M ⊓ Subgroup.centralizer ((Subgroup.zpowers wG : Subgroup G) : Set G) = ⊥ ∧
        wG ∈ UG := by
    by_cases hUGA : A ≤ UG
    · obtain ⟨A₁, hA₁mem, hA₁A, hA₁good⟩ :=
        (Msigma_nilpotent_of_tau2 hG h.mem_maximal hp hA hAM).2.2.2.2.2
      have hA₁card : Nat.card ↥A₁ = p := by rw [hA₁mem.2, pow_one]
      obtain ⟨w, hword, hwgen⟩ := exists_generator_of_card_prime hA₁card
      refine ⟨w, hword, by rw [hwgen]; exact hA₁good, hUGA (hA₁A ?_)⟩
      rw [← hwgen]; exact Subgroup.mem_zpowers w
    · have hUGltA : UG < A := lt_of_le_of_ne hUG_le_A (fun he => hUGA he.ge)
      have hdvd : Nat.card ↥UG ∣ p ^ 2 := by rw [← hA.2]; exact Subgroup.card_dvd_of_le hUG_le_A
      have hne1 : Nat.card ↥UG ≠ 1 := by rw [Ne, Subgroup.card_eq_one]; exact hUG_ne
      have hne2 : Nat.card ↥UG ≠ p ^ 2 := fun hc2 =>
        (ne_of_lt hUGltA) (Subgroup.eq_of_le_of_card_ge hUG_le_A (by rw [hc2, hA.2]))
      have hUGcard : Nat.card ↥UG = p := by
        obtain ⟨c, hc_le, hc⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hdvd
        interval_cases c
        · rw [pow_zero] at hc; exact absurd hc hne1
        · rw [pow_one] at hc; exact hc
        · exact absurd hc hne2
      have hUGmem : UG ∈ elemAbelianOfRank G p 1 :=
        ⟨Subgroup.IsElementaryAbelian.of_card_prime hUGcard, by rw [pow_one]; exact hUGcard⟩
      have hUGinv : Subgroup.normalizer ((S : Subgroup G) : Set G) ≤
          Subgroup.normalizer (UG : Set G) := by
        rw [hUGdef]
        exact OddOrder.BG.AppB.normalizer_le_normalizer_map_of_characteristic
          (K := (S : Subgroup G)) (W := Agemo ↥(S : Subgroup G) p (a - 1))
      have hgood : S10.Msigma M ⊓ Subgroup.centralizer (UG : Set G) = ⊥ :=
        inf_centralizer_line_eq_bot_of_invariant hG h hp hA hAE hAS hSM hUGmem hUGS hUGinv
      obtain ⟨w, hword, hwgen⟩ := exists_generator_of_card_prime hUGcard
      refine ⟨w, hword, by rw [hwgen]; exact hgood, ?_⟩
      rw [← hwgen]; exact Subgroup.mem_zpowers w
  rw [hUGdef] at hwG_mem
  obtain ⟨y', hy'mem, hy'eq⟩ := hwG_mem
  obtain ⟨t, ht⟩ := mem_agemo_iff_of_comm.mp
    (show y' ∈ Agemo ↥(S : Subgroup G) p (a - 1) from hy'mem)
  set s : G := (t : G) with hsdef
  have hsw : s ^ (p ^ (a - 1)) = wG := by
    rw [hsdef, ← hy'eq, ht]; exact (SubmonoidClass.coe_pow t _).symm
  have hsS : s ∈ (S : Subgroup G) := by rw [hsdef]; exact t.2
  have hsord : orderOf s = p ^ a := by
    have hsexp : orderOf s ∣ p ^ a := by
      rw [← ha, hsdef]
      exact (orderOf_injective (S : Subgroup G).subtype (S : Subgroup G).subtype_injective t) ▸
        Monoid.order_dvd_exponent t
    have hnd : ¬ orderOf s ∣ p ^ (a - 1) := by
      intro hd
      have hwG1 : wG = 1 := by rw [← hsw]; exact orderOf_dvd_iff_pow_eq_one.mp hd
      rw [hwG1, orderOf_one] at hwG_ord
      exact (Fact.out : p.Prime).ne_one hwG_ord.symm
    obtain ⟨c, hc_le, hc⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hsexp
    rw [hc]; congr 1
    by_contra hca
    rw [hc] at hnd
    exact hnd (pow_dvd_pow p (by omega))
  have hsne : s ≠ 1 := by
    intro h1; rw [h1, orderOf_one] at hsord
    exact (Nat.one_lt_pow (by omega) (Fact.out : p.Prime).one_lt).ne hsord
  have hZS : Subgroup.zpowers s ≤ (S : Subgroup G) := Subgroup.zpowers_le.mpr hsS
  have hLZ : (Subgroup.zpowers wG : Subgroup G) ≤ Subgroup.zpowers s := by
    rw [← hsw]
    exact Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ (Subgroup.mem_zpowers s) _)
  refine ⟨Subgroup.zpowers s, hZS, inferInstance, (Subgroup.zpowers_eq_bot.not.mpr hsne), ?_, ?_⟩
  · rw [IsCyclic.exponent_eq_card, Nat.card_zpowers, hsord, ha]
  · exact inf_centralizer_eq_bot_of_line_le_cyclic (S.isPGroup'.to_le hZS) hLZ
      (by rw [Nat.card_zpowers, hwG_ord]) hwG_good

/-- **Theorem 12.12, Case 3, per-prime `Z`-construction** (both branches): in the abelian-Sylow
regime with the regularity hypothesis, `S` has a cyclic subgroup `Z` of exponent `exp(S)`,
normalized by `E`, acting regularly on `M_σ`. (Splits on `C_E(S) = E`: the `= E` branch uses the
agemo construction, the `≠ E` branch produces `X` (front-half) then the invariant `Z` (back-half).
In both cases `E ≤ N_G(Z)`.) -/
theorem exists_cyclic_Enormal_regular_of_abelianSylow [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ tau2 M) {A : Subgroup G} (hA : A ∈ elemAbelianOfRank G p 2) (hAE : A ≤ E)
    {S : Sylow p G} (hAS : A ≤ (S : Subgroup G)) (hSM : (S : Subgroup G) ≤ M)
    (hSab : IsMulCommutative ↥(S : Subgroup G))
    (hreg : ∀ e ∈ E, e ≠ 1 → (∀ r ∈ (orderOf e).primeFactors, r ∈ tau1 M ∪ tau3 M) →
      S10.Msigma M ⊓ Subgroup.centralizer ({e} : Set G) = ⊥) :
    ∃ Z : Subgroup G, Z ≤ (S : Subgroup G) ∧ IsCyclic ↥Z ∧ Z ≠ ⊥ ∧
      E ≤ Subgroup.normalizer (Z : Set G) ∧
      Monoid.exponent ↥Z = Monoid.exponent ↥(S : Subgroup G) ∧
      ∀ z ∈ Z, z ≠ 1 → S10.Msigma M ⊓ Subgroup.centralizer ({z} : Set G) = ⊥ := by
  by_cases hCES : Subgroup.centralizer ((S : Subgroup G) : Set G) ⊓ E = E
  · exact exists_cyclic_Enormal_regular_of_CES_eq hG h hp hA hAE hAS hSM hSab hreg hCES
  · obtain ⟨X, hXN, hcop, hne, hltS⟩ :=
      exists_partial_centralizer_of_abelianSylow hG h hp hA hAE hAS hSM hSab hreg hCES
    obtain ⟨Z, hZS, hZcyc, hZne, hZNinv, hZexp, hZreg⟩ :=
      exists_invariant_cyclic_sameExponent_regular hG h hp hA hAE hAS hSM hSab hXN hcop hne hltS
    have hENS : E ≤ Subgroup.normalizer ((S : Subgroup G) : Set G) :=
      E_le_normalizer_sylow_of_abelianSylow hG h hp hA hAE hAS hSab
    exact ⟨Z, hZS, hZcyc, hZne, hENS.trans hZNinv, hZexp, hZreg⟩

/-- If every prime-order element of `H` acts fixed-point-freely on `N` (`N ⊓ C(h) = ⊥`), then so
does every nonidentity element. (For `h ∈ H#`, a prime-order power `h^(|h|/r)` is fixed-point-free
and `C(h) ⊆ C(h^(|h|/r))`.) The reduction underlying "`E₀` is a Frobenius complement". -/
theorem inf_centralizer_eq_bot_of_forall_prime_order [Finite G] {H N : Subgroup G}
    (hpr : ∀ h ∈ H, (orderOf h).Prime → N ⊓ Subgroup.centralizer ({h} : Set G) = ⊥) :
    ∀ h ∈ H, h ≠ 1 → N ⊓ Subgroup.centralizer ({h} : Set G) = ⊥ := by
  intro h hhH hne
  have hn : orderOf h ≠ 0 := (orderOf_pos h).ne'
  have hn1 : orderOf h ≠ 1 := fun hc => hne (orderOf_eq_one_iff.mp hc)
  obtain ⟨r, hr_prime, hr_dvd⟩ := Nat.exists_prime_and_dvd hn1
  have hk_ord : orderOf (h ^ (orderOf h / r)) = r := orderOf_pow_orderOf_div hn hr_dvd
  have hk_good : N ⊓ Subgroup.centralizer ({h ^ (orderOf h / r)} : Set G) = ⊥ :=
    hpr (h ^ (orderOf h / r)) (H.pow_mem hhH _) (by rw [hk_ord]; exact hr_prime)
  have hCsub : Subgroup.centralizer ({h} : Set G) ≤
      Subgroup.centralizer ({h ^ (orderOf h / r)} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro y hy
    rw [Set.mem_singleton_iff] at hy; subst hy
    exact (Commute.pow_left (hx h rfl) _)
  rw [eq_bot_iff, ← hk_good]
  exact inf_le_inf_left N hCsub

end OddOrder.BG.Ch3.S12


