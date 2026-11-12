-- Prove2me | Definitions.Def_OddOrder_BG_Ch1_Preliminary_S04c_Prop411
-- name    : OddOrder_BG_Ch1_Preliminary_S04c_Prop411
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:53:49.727028+00:00
-- url     : https://prove2.me/theorems/5ce2f6c3-e80d-47e6-88f6-dec26994f696
-- title:
--   BG §4: Proposition 4.11 (Huppert)
-- statement:
--   Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, §4, Proposition 4.11 (Huppert, *Endliche Gruppen I*, Satz III.11.6): for a prime $p>3$ and a finite $p$-group $R$ with $|\Omega_1(R)|\le p^2$, $R$ is metacyclic. The proof is by induction on $|R|$ using Lemmas 4.9, 4.5(b), 4.2 and 4.1.
--
--   The bundle consists of lemmas only, including `exists_metacyclic_lift_of_isMetacyclic_quotient_center_prime` (equation (4.7): lift a metacyclic quotient $R/\langle z\rangle$ back to $R$) and two micro-helpers for central $z$.
--
--   The bundle also proves 9 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch1_Preliminary/S04c_Prop411.lean

/-
Copyright (c) 2026 Yawara ISHIDA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch1_Preliminary/S04c_Prop411.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S04_PGroupsSmallRank

open scoped commutatorElement

namespace OddOrder.BG.Ch1.S04

open OddOrder.GroupTheory

variable {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]

/-- **In a finite `p`-group, a normal subgroup of order `p` is central.**

A nontrivial normal subgroup of a finite `p`-group meets the centre
(`IsPGroup.normal_inf_center_nontrivial`); since `|N| = p` is prime, the nontrivial
subgroup `N ⊓ Z(R)` of `N` must be all of `N`, so `N ≤ Z(R)`.

(BG §4 Prop 4.11 の step 6 で `⟨a,z⟩/⟨aᵖ,z⟩` (位数 `p` の normal) が中心に入ることに使う。) -/
theorem le_center_of_card_eq_prime_of_normal (hR : IsPGroup p R)
    {N : Subgroup R} [N.Normal] (hN : Nat.card N = p) : N ≤ Subgroup.center R := by
  have hp : p.Prime := Fact.out
  have hNnt : Nontrivial N :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hN]; exact hp.one_lt)
  have hmeet : Nontrivial ((N ⊓ Subgroup.center R : Subgroup R)) :=
    OddOrder.Isaacs.Ch01.IsPGroup.normal_inf_center_nontrivial hR hNnt
  have hle : (N ⊓ Subgroup.center R : Subgroup R) ≤ N := inf_le_left
  have hcard_dvd : Nat.card (N ⊓ Subgroup.center R : Subgroup R) ∣ Nat.card N :=
    Subgroup.card_dvd_of_le hle
  have hcard_ne_one : Nat.card (N ⊓ Subgroup.center R : Subgroup R) ≠ 1 :=
    (Finite.one_lt_card_iff_nontrivial.mpr hmeet).ne'
  have hcard_eq : Nat.card (N ⊓ Subgroup.center R : Subgroup R) = p := by
    rcases (Nat.dvd_prime hp).mp (hN ▸ hcard_dvd) with h1 | hp'
    · exact absurd h1 hcard_ne_one
    · exact hp'
  have heq : (N ⊓ Subgroup.center R : Subgroup R) = N :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcard_eq, hN])
  calc N = (N ⊓ Subgroup.center R : Subgroup R) := heq.symm
    _ ≤ Subgroup.center R := inf_le_right

/-- For an abelian finite `p`-group `R`, `|R / Φ(R)| ≤ |Ω₁(R)|`.

The `p`-th power map `φ : x ↦ xᵖ` is a homomorphism (abelian) with `ker φ = Ω₁(R)` (the
`p`-torsion) and `range φ ≤ Φ(R)` (each `xᵖ ∈ Φ(R)`). The first isomorphism theorem gives
`(range φ).index = |ker φ| = |Ω₁(R)|`, and `range φ ≤ Φ(R)` gives `|R/Φ(R)| ≤ (range φ).index`.

(BG §4 Prop 4.11 abelian base case で `|Ω₁(R)| ≤ p²` から `|R/Φ(R)| ≤ p²`、ゆえ rank ≤ 2 を出すのに使う。) -/
theorem card_quotient_frattini_le_card_omega1_of_comm (hR : IsPGroup p R)
    (hcomm : ∀ x y : R, x * y = y * x) :
    Nat.card (R ⧸ frattini R) ≤ Nat.card (Omega R p 1) := by
  let : CommGroup R := { (inferInstance : Group R) with mul_comm := hcomm }
  -- `φ : x ↦ xᵖ`, a homomorphism since `R` is abelian.
  let φ : R →* R :=
    { toFun := fun x => x ^ p
      map_one' := one_pow p
      map_mul' := fun a b => mul_pow a b p }
  -- `ker φ = Ω₁(R)`.
  have hker : φ.ker = Omega R p 1 := by
    apply le_antisymm
    · intro x hx
      exact Omega.mem_of_pow_eq_one (by rw [pow_one]; exact hx)
    · rw [Omega, Subgroup.closure_le]
      rintro x hx
      rw [SetLike.mem_coe, MonoidHom.mem_ker]
      change x ^ p = 1
      simpa using hx
  -- `range φ ≤ Φ(R)`: each `xᵖ ∈ Φ(R)`.
  have hrange_le : φ.range ≤ frattini R := by
    rintro _ ⟨x, rfl⟩
    exact OddOrder.GroupTheory.IsPGroup.pow_mem_frattini hR x
  -- `(range φ).index = |ker φ|` (first isomorphism + `index_mul_card`).
  have hidx : (φ.range).index = Nat.card φ.ker := by
    have hcong : Nat.card (R ⧸ φ.ker) = Nat.card φ.range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
    have hre : Nat.card φ.range = φ.ker.index := hcong.symm
    have e1 : (φ.range).index * Nat.card φ.range = Nat.card R := φ.range.index_mul_card
    have e2 : φ.ker.index * Nat.card φ.ker = Nat.card R := φ.ker.index_mul_card
    have hkpos : 0 < φ.ker.index := Nat.card_pos
    rw [hre] at e1
    have hcancel : φ.ker.index * (φ.range).index = φ.ker.index * Nat.card φ.ker := by
      rw [mul_comm φ.ker.index (φ.range).index, e1, ← e2]
    exact Nat.eq_of_mul_eq_mul_left hkpos hcancel
  -- `|R/Φ| = Φ.index ∣ (range φ).index`, and both positive ⇒ `≤`.
  have hdvd : (frattini R).index ∣ (φ.range).index := Subgroup.index_dvd_of_le hrange_le
  have hrpos : 0 < (φ.range).index := Nat.card_pos
  calc Nat.card (R ⧸ frattini R) = (frattini R).index := rfl
    _ ≤ (φ.range).index := Nat.le_of_dvd hrpos hdvd
    _ = Nat.card φ.ker := hidx
    _ = Nat.card (Omega R p 1) := by rw [hker]

/-- **A finite `p`-group of order `≤ p²` is generated by at most two elements.**

If `Q` is cyclic, one generator suffices. Otherwise `|Q| = p²` (a `p`-group of order `≤ p²`
that is not cyclic cannot have order `1` or `p`); picking `g₁ ≠ 1` and `g₂ ∉ ⟨g₁⟩` gives
`⟨g₁, g₂⟩ ⊋ ⟨g₁⟩`, forcing `|⟨g₁, g₂⟩| = p² = |Q|`, so `⟨g₁, g₂⟩ = Q`. -/
theorem exists_generators_le_two_of_isPGroup_of_card_le_prime_sq {Q : Type*} [Group Q] [Finite Q]
    (hQpg : IsPGroup p Q) (hQ : Nat.card Q ≤ p ^ 2) :
    ∃ T : Finset Q, T.card ≤ 2 ∧ Subgroup.closure (↑T : Set Q) = ⊤ := by
  classical
  have hp : p.Prime := Fact.out
  by_cases hcyc : IsCyclic Q
  · -- cyclic: a single generator.
    obtain ⟨g, hg⟩ := hcyc.exists_generator
    refine ⟨{g}, by simp, ?_⟩
    rw [Finset.coe_singleton, ← Subgroup.zpowers_eq_closure]
    exact top_unique fun x _ => hg x
  · -- not cyclic ⇒ `|Q| = p²`.
    obtain ⟨k, hk⟩ := hQpg.exists_card_eq
    have hk2 : k = 2 := by
      have hkle : k ≤ 2 := by
        have h := hQ; rw [hk] at h; exact (Nat.pow_le_pow_iff_right hp.one_lt).mp h
      interval_cases k
      · refine absurd ?_ hcyc
        have h1 : Nat.card Q = 1 := by rw [hk]; simp
        have : Subsingleton Q := (Nat.card_eq_one_iff_unique.mp h1).1
        exact ⟨⟨1, fun x => Subgroup.mem_zpowers_iff.mpr ⟨0, Subsingleton.elim _ _⟩⟩⟩
      · exact absurd (isCyclic_of_prime_card (p := p) (by rw [hk, pow_one])) hcyc
      · rfl
    rw [hk2] at hk
    have : Nontrivial Q := by
      rw [← Finite.one_lt_card_iff_nontrivial, hk]
      exact Nat.one_lt_pow (by norm_num) hp.one_lt
    obtain ⟨g₁, hg₁⟩ := exists_ne (1 : Q)
    have hcardz : Nat.card (Subgroup.zpowers g₁) = orderOf g₁ := Nat.card_zpowers g₁
    have hord_dvd : orderOf g₁ ∣ p ^ 2 := by
      rw [← hcardz, ← hk]; exact Subgroup.card_subgroup_dvd_card _
    have hord_ne1 : orderOf g₁ ≠ 1 := by simpa [orderOf_eq_one_iff] using hg₁
    -- `⟨g₁⟩ = ⊤` would make `Q` cyclic; so `⟨g₁⟩ ≠ ⊤`.
    have hz_ne_top : Subgroup.zpowers g₁ ≠ ⊤ := by
      intro htop
      apply hcyc
      refine ⟨⟨g₁, fun x => ?_⟩⟩
      have hx : x ∈ (⊤ : Subgroup Q) := Subgroup.mem_top x
      rwa [← htop] at hx
    -- hence `orderOf g₁ = p` (divides `p²`, `≠ 1`, `≠ p²`).
    have hordp : orderOf g₁ = p := by
      rcases (Nat.dvd_prime_pow hp).mp hord_dvd with ⟨j, hj_le, hje⟩
      interval_cases j
      · simp only [pow_zero] at hje; exact absurd hje hord_ne1
      · rw [hje, pow_one]
      · have hcardeq : Nat.card (Subgroup.zpowers g₁) = Nat.card Q := by rw [hcardz, hje, hk]
        exact absurd (Subgroup.eq_top_of_card_eq (H := Subgroup.zpowers g₁) hcardeq) hz_ne_top
    obtain ⟨g₂, hg₂⟩ : ∃ x, x ∉ Subgroup.zpowers g₁ := by
      by_contra h; push Not at h
      exact hz_ne_top (top_unique fun x _ => h x)
    refine ⟨{g₁, g₂}, le_trans (Finset.card_insert_le _ _) (by simp), ?_⟩
    -- `K := ⟨g₁,g₂⟩` contains `⟨g₁⟩` (order `p`) and `g₂ ∉ ⟨g₁⟩`, so `|K| ≠ p`; `|K| ∣ p²` and
    -- `p ∣ |K|` then force `|K| = p² = |Q|`, hence `K = ⊤`.
    have hg₁K : g₁ ∈ Subgroup.closure (↑({g₁, g₂} : Finset Q) : Set Q) :=
      Subgroup.subset_closure (by simp)
    have hg₂K : g₂ ∈ Subgroup.closure (↑({g₁, g₂} : Finset Q) : Set Q) :=
      Subgroup.subset_closure (by simp)
    set K : Subgroup Q := Subgroup.closure (↑({g₁, g₂} : Finset Q) : Set Q) with hK
    have hzle : Subgroup.zpowers g₁ ≤ K := by rw [Subgroup.zpowers_le]; exact hg₁K
    have hKdvd : Nat.card K ∣ p ^ 2 := by rw [← hk]; exact Subgroup.card_subgroup_dvd_card _
    have hp_dvd_K : p ∣ Nat.card K := by
      have h := Subgroup.card_dvd_of_le hzle; rwa [hcardz, hordp] at h
    have hKne_p : Nat.card K ≠ p := by
      intro hKp
      have hcard_le : Nat.card K ≤ Nat.card (Subgroup.zpowers g₁) :=
        le_of_eq (by rw [hKp, hcardz, hordp])
      have heq : Subgroup.zpowers g₁ = K := Subgroup.eq_of_le_of_card_ge hzle hcard_le
      exact hg₂ (by rw [heq]; exact hg₂K)
    have hKeq : Nat.card K = p ^ 2 := by
      rcases (Nat.dvd_prime_pow hp).mp hKdvd with ⟨j, hj_le, hje⟩
      interval_cases j
      · rw [hje, pow_zero] at hp_dvd_K; exact absurd (Nat.dvd_one.mp hp_dvd_K) hp.ne_one
      · rw [pow_one] at hje; exact absurd hje hKne_p
      · exact hje
    have hKcardeq : Nat.card K = Nat.card Q := by rw [hKeq, hk]
    exact Subgroup.eq_top_of_card_eq (H := K) hKcardeq

/-- **Burnside basis (rank ≤ 2 form)**: a finite `p`-group `R` with `|R/Φ(R)| ≤ p²` is
generated by at most two elements.

Apply `exists_generators_le_two_of_isPGroup_of_card_le_prime_sq` to the (elementary abelian)
quotient `R/Φ(R)` to get `≤2` generators of `R/Φ(R)`, lift them to `R`, and use that `Φ(R)` is
non-generating (`frattini_nongenerating`). -/
theorem exists_generators_le_two_of_card_quotient_frattini_le_prime_sq
    (hR : IsPGroup p R) (hQ : Nat.card (R ⧸ frattini R) ≤ p ^ 2) :
    ∃ T : Finset R, T.card ≤ 2 ∧ Subgroup.closure (↑T : Set R) = ⊤ := by
  classical
  obtain ⟨U, hUcard, hUgen⟩ :=
    exists_generators_le_two_of_isPGroup_of_card_le_prime_sq (hR.to_quotient (frattini R)) hQ
  -- preimage section `f` of `mk'`.
  let f : (R ⧸ frattini R) → R := fun u => (QuotientGroup.mk'_surjective (frattini R) u).choose
  have hfspec : ∀ u, QuotientGroup.mk' (frattini R) (f u) = u :=
    fun u => (QuotientGroup.mk'_surjective (frattini R) u).choose_spec
  refine ⟨U.image f, le_trans Finset.card_image_le hUcard, ?_⟩
  -- the image of `closure (U.image f)` in `R/Φ` is `closure U = ⊤`.
  have hmap : (Subgroup.closure (↑(U.image f) : Set R)).map (QuotientGroup.mk' (frattini R)) = ⊤ :=
      by
    rw [MonoidHom.map_closure]
    have himg : (QuotientGroup.mk' (frattini R)) '' (↑(U.image f) : Set R) = (↑U : Set _) := by
      rw [Finset.coe_image, Set.image_image]
      ext u
      simp only [Set.mem_image, Finset.mem_coe]
      exact ⟨fun ⟨v, hv, hvu⟩ => by rw [← hvu, hfspec]; exact hv,
             fun hu => ⟨u, hu, hfspec u⟩⟩
    rw [himg]; exact hUgen
  -- hence `closure (U.image f) ⊔ Φ(R) = ⊤`, so by `frattini_nongenerating`, `= ⊤`.
  have hsup : Subgroup.closure (↑(U.image f) : Set R) ⊔ frattini R = ⊤ := by
    have hcm := Subgroup.comap_map_eq (f := QuotientGroup.mk' (frattini R))
      (Subgroup.closure (↑(U.image f) : Set R))
    rw [hmap, Subgroup.comap_top, QuotientGroup.ker_mk'] at hcm
    exact hcm.symm
  exact frattini_nongenerating hsup

/-- **BG Prop 4.11, abelian base case**: an abelian finite `p`-group with `|Ω₁(R)| ≤ p²` is
metacyclic.

`|R/Φ(R)| ≤ |Ω₁(R)| ≤ p²` (`card_quotient_frattini_le_card_omega1_of_comm`), so `R` is generated
by `≤ 2` elements (`exists_generators_le_two_of_card_quotient_frattini_le_prime_sq`). If `R` is
cyclic it is metacyclic; otherwise `R = ⟨a, b⟩` and `⟨a⟩` is a cyclic normal subgroup (abelian)
with `R/⟨a⟩ = ⟨b̄⟩` cyclic. -/
theorem isMetacyclic_of_omega1_card_le_prime_sq_of_comm (hR : IsPGroup p R)
    (hcomm : ∀ x y : R, x * y = y * x) (hΩ : Nat.card (Omega R p 1) ≤ p ^ 2) :
    OddOrder.GroupTheory.IsMetacyclic R := by
  classical
  let : CommGroup R := { (inferInstance : Group R) with mul_comm := hcomm }
  have hQ : Nat.card (R ⧸ frattini R) ≤ p ^ 2 :=
    le_trans (card_quotient_frattini_le_card_omega1_of_comm hR hcomm) hΩ
  obtain ⟨T, hTcard, hTgen⟩ := exists_generators_le_two_of_card_quotient_frattini_le_prime_sq hR hQ
  by_cases hcyc : IsCyclic R
  · exact OddOrder.GroupTheory.IsMetacyclic.of_isCyclic
  · -- not cyclic ⇒ `T.card = 2` (`≤ 1` generators would make `R` cyclic).
    have hT2 : T.card = 2 := by
      by_contra hne
      apply hcyc
      have hcard1 : T.card ≤ 1 := by omega
      obtain ⟨a, ha⟩ := Finset.card_le_one_iff_subset_singleton.mp hcard1
      have hle : Subgroup.closure (↑T : Set R) ≤ Subgroup.zpowers a := by
        rw [Subgroup.closure_le]
        intro x hx
        have hx' : x ∈ ({a} : Finset R) := ha (Finset.mem_coe.mp hx)
        rw [Finset.mem_singleton] at hx'; subst hx'
        exact Subgroup.mem_zpowers _
      rw [hTgen] at hle
      have htop : Subgroup.zpowers a = ⊤ := top_le_iff.mp hle
      refine ⟨⟨a, fun x => ?_⟩⟩
      have hx : x ∈ (⊤ : Subgroup R) := Subgroup.mem_top x
      rwa [← htop] at hx
    obtain ⟨a, b, hab, hTab⟩ := Finset.card_eq_two.mp hT2
    rw [hTab, Finset.coe_pair] at hTgen
    refine ⟨Subgroup.zpowers a, inferInstance, inferInstance, ?_⟩
    -- `R/⟨a⟩` is cyclic, generated by `mk b`.
    have hmkb_top :
        Subgroup.zpowers (QuotientGroup.mk' (Subgroup.zpowers a) b) = ⊤ := by
      have h1 : (Subgroup.closure ({a, b} : Set R)).map
          (QuotientGroup.mk' (Subgroup.zpowers a)) = ⊤ := by
        rw [hTgen, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
      rw [MonoidHom.map_closure, Set.image_pair] at h1
      have hmka : QuotientGroup.mk' (Subgroup.zpowers a) a = 1 := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]; exact Subgroup.mem_zpowers a
      rw [hmka] at h1
      have hle : Subgroup.closure
            ({1, QuotientGroup.mk' (Subgroup.zpowers a) b} : Set (R ⧸ Subgroup.zpowers a))
          ≤ Subgroup.zpowers (QuotientGroup.mk' (Subgroup.zpowers a) b) := by
        rw [Subgroup.closure_le]
        intro y hy
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with rfl | rfl
        · exact one_mem _
        · exact Subgroup.mem_zpowers _
      rw [h1] at hle
      exact top_le_iff.mp hle
    refine ⟨⟨QuotientGroup.mk' (Subgroup.zpowers a) b, fun x => ?_⟩⟩
    have hx : x ∈ (⊤ : Subgroup (R ⧸ Subgroup.zpowers a)) := Subgroup.mem_top x
    rwa [← hmkb_top] at hx

omit [Finite R] in
omit [Fact (Nat.Prime p)] in
/-- **BG Prop 4.11, equation (4.7)**: lift a metacyclic quotient `R/⟨z⟩` back to `R`.

Let `R` be a finite `p`-group, `z ∈ Z(R)` of order `p` (so `T := ⟨z⟩` is normal), and suppose
`R ⧸ T` is metacyclic. Then there exist `a, b ∈ R` with, writing `K := ⟨a, z⟩`:

* `(i)`  `K ◁ R`               (`⟨a, z⟩` is normal);
* `(ii)` `R' ⊆ K`              (the commutator subgroup lies in `⟨a, z⟩`);
* `(iii)` `R = ⟨a, b, z⟩`;
* `(iv)` `K / T` is cyclic      (`⟨a, z⟩/⟨z⟩` is cyclic; used by step 6 of Prop 4.11);
* `(v)`  `R / K` is cyclic      (used by step 8 of Prop 4.11).

Unpacking `IsMetacyclic (R ⧸ T)` gives a cyclic normal `N ◁ R/T` with `(R/T)/N` cyclic. Lifting
a generator of `N` along `mk' T` gives `a` with `N = ⟨mk a⟩`; set `K := comap (mk' T) N`. Then
`K ◁ R` (`Normal.comap`), `T ≤ K` (`le_comap_mk'`), `K.map (mk' T) = N`
(`map_comap_eq_self_of_surjective`); and `(ii)` follows from `(R/T)/N` abelian, `(iv)` from
the first isomorphism theorem `K/(T.subgroupOf K) ≃ K.map (mk' T) = N`, `(v)` from Noether's
third isomorphism theorem `(R/T)/N ≃ R/K`. Lifting a generator of `(R/T)/N` twice gives `b`,
whence `R = ⟨a, b, z⟩`. Finally `K = ⟨a, z⟩` is verified by `ext`.

The conclusion is packaged with `K := ⟨a, z⟩` bound existentially together with its `Normal`
instance, so that the cyclic quotients `K/T` and `R/K` are well-formed group quotients; the
defining equation `K = ⟨a, z⟩` is part of the conclusion, so no content of `(4.7)` is lost.

The hypothesis `(Subgroup.zpowers z).Normal` is the typeclass prerequisite for the quotient
`R ⧸ ⟨z⟩` to be a group; it is a direct consequence of `z ∈ Z(R)` (which the caller, the
induction body of Prop 4.11, has at hand) and is *not* hoisted hard content.

This is the `(4.7)` step of the non-abelian induction of Prop 4.11 (mmd L1560-1564). -/
theorem exists_metacyclic_lift_of_isMetacyclic_quotient_center_prime (_hR : IsPGroup p R)
    {z : R} [(Subgroup.zpowers z).Normal] (hz : z ∈ Subgroup.center R) (hzp : orderOf z = p)
    (hmeta : OddOrder.GroupTheory.IsMetacyclic (R ⧸ Subgroup.zpowers z)) :
    ∃ (a b : R) (K : Subgroup R), ∃ _ : K.Normal,
      K = Subgroup.closure ({a, z} : Set R) ∧
      _root_.commutator R ≤ K ∧
      Subgroup.closure ({a, b, z} : Set R) = ⊤ ∧
      IsCyclic (K ⧸ (Subgroup.zpowers z).subgroupOf K) ∧
      IsCyclic (R ⧸ K) := by
  classical
  set T : Subgroup R := Subgroup.zpowers z with hT
  -- ⟨STEP 1⟩ Unpack `IsMetacyclic (R ⧸ T)`.
  obtain ⟨N, hNnorm, hNcyc, hQcyc⟩ := hmeta
  have := hNnorm; have := hNcyc; have := hQcyc
  -- ⟨STEP 2⟩ A generator `ngen` of `N`, lifted to `a ∈ R`; so `N = ⟨mk' T a⟩`.
  obtain ⟨ngen, hngen⟩ := hNcyc.exists_generator
  obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective T ngen
  have haN : QuotientGroup.mk' T a ∈ N := ha ▸ ngen.2
  have hNeq : N = Subgroup.zpowers (QuotientGroup.mk' T a) := by
    apply le_antisymm
    · -- every `x ∈ N` is a power of the generator `ngen`, hence of `mk' T a = ↑ngen`.
      intro x hx
      obtain ⟨k, hk⟩ := (Subgroup.mem_zpowers_iff).mp (hngen ⟨x, hx⟩)
      rw [Subgroup.mem_zpowers_iff]
      refine ⟨k, ?_⟩
      -- `(mk' T a)^k = (N.subtype ngen)^k = N.subtype (ngen^k) = N.subtype ⟨x,hx⟩ = x`.
      have hsub : N.subtype (ngen ^ k) = x := by rw [hk]; rfl
      rwa [map_zpow, Subgroup.coe_subtype, ← ha] at hsub
    · rw [Subgroup.zpowers_le]; exact haN
  -- ⟨STEP 3⟩ `K := comap (mk' T) N`; normal, contains `T`, and maps onto `N`.
  set K : Subgroup R := N.comap (QuotientGroup.mk' T) with hK
  have hKnorm : K.Normal := hNnorm.comap _
  have hTleK : T ≤ K := QuotientGroup.le_comap_mk' T N
  have hKmap : K.map (QuotientGroup.mk' T) = N :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective T) N
  -- ⟨STEP 4 = (ii)⟩ `commutator R ≤ K`.
  have hcommQ : _root_.commutator (R ⧸ T) ≤ N :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mp inferInstance
  have hcommR : _root_.commutator R ≤ K := by
    rw [hK, ← Subgroup.map_le_iff_le_comap]
    calc (_root_.commutator R).map (QuotientGroup.mk' T)
        = _root_.commutator (R ⧸ T) := by
          rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
              Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective T)]
      _ ≤ N := hcommQ
  -- ⟨STEP 5 = (iii)⟩ `R = ⟨a, b, z⟩`, with `b` a two-step lift of a generator of `(R/T)/N`.
  obtain ⟨qgen, hqgen⟩ := hQcyc.exists_generator
  obtain ⟨bq, hbq⟩ := QuotientGroup.mk'_surjective N qgen
  obtain ⟨b, hb⟩ := QuotientGroup.mk'_surjective T bq
  -- (a) `closure {mk' T a, mk' T b} = ⊤` in `R ⧸ T`.
  have hmkclosure :
      Subgroup.closure ({QuotientGroup.mk' T a, QuotientGroup.mk' T b} : Set (R ⧸ T)) = ⊤ := by
    set C : Subgroup (R ⧸ T) :=
      Subgroup.closure ({QuotientGroup.mk' T a, QuotientGroup.mk' T b} : Set (R ⧸ T)) with hC
    -- `mk' T a ∈ N`, so `N = ⟨mk' T a⟩ ≤ C`.
    have hNleC : N ≤ C := by
      rw [hNeq, Subgroup.zpowers_le, hC]
      exact Subgroup.subset_closure (by simp)
    -- The image of `C` under `mk' N` is `⊤` (it contains the generator `qgen` of `(R/T)/N`).
    have hmapN : C.map (QuotientGroup.mk' N) = ⊤ := by
      rw [hC, MonoidHom.map_closure, Set.image_pair]
      -- `mk' N (mk' T a) = 1` (since `mk' T a ∈ N`), `mk' N (mk' T b) = qgen`.
      have hmka1 : QuotientGroup.mk' N (QuotientGroup.mk' T a) = 1 := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]; exact haN
      have hmkbq : QuotientGroup.mk' N (QuotientGroup.mk' T b) = qgen := by
        rw [hb, hbq]
      rw [hmka1, hmkbq]
      -- `closure {1, qgen} ⊇ zpowers qgen = ⊤`.
      refine top_le_iff.mp (le_trans (fun y _ => hqgen y) ?_)
      rw [Subgroup.zpowers_le]
      exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    -- `C ⊔ N = comap (mk' N) (map (mk' N) C) = comap ⊤ = ⊤`, and `N ≤ C`, so `C = ⊤`.
    have hsupN : C ⊔ N = ⊤ := by
      have hcm := Subgroup.comap_map_eq (f := QuotientGroup.mk' N) C
      rw [hmapN, Subgroup.comap_top, QuotientGroup.ker_mk'] at hcm
      exact hcm.symm
    rw [sup_eq_left.mpr hNleC] at hsupN
    rw [hC] at hsupN; exact hsupN
  -- (b) Lift to `R`: `closure {a, b, z} = ⊤`.
  have hiii : Subgroup.closure ({a, b, z} : Set R) = ⊤ := by
    have hmap3 : (Subgroup.closure ({a, b, z} : Set R)).map (QuotientGroup.mk' T) = ⊤ := by
      rw [MonoidHom.map_closure, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]
      have hmkz : QuotientGroup.mk' T z = 1 := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hT]; exact Subgroup.mem_zpowers z
      rw [hmkz]
      refine top_le_iff.mp ?_
      rw [← hmkclosure]
      apply Subgroup.closure_mono
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
      tauto
    have hsup : Subgroup.closure ({a, b, z} : Set R) ⊔ T = ⊤ := by
      have hcm := Subgroup.comap_map_eq (f := QuotientGroup.mk' T)
        (Subgroup.closure ({a, b, z} : Set R))
      rw [hmap3, Subgroup.comap_top, QuotientGroup.ker_mk'] at hcm; exact hcm.symm
    have hzin : z ∈ Subgroup.closure ({a, b, z} : Set R) := Subgroup.subset_closure (by simp)
    have hTin : T ≤ Subgroup.closure ({a, b, z} : Set R) := by
      rw [hT, Subgroup.zpowers_le]; exact hzin
    rw [sup_eq_left.mpr hTin] at hsup; exact hsup
  -- ⟨STEP 6 = (iv)⟩ `K / (T.subgroupOf K)` is cyclic (`≅ K.map (mk' T) = N`).
  have hiv : IsCyclic (K ⧸ (T.subgroupOf K)) := by
    -- `φ := mk' T ∘ K.subtype : K →* R/T`, with `range φ = K.map (mk' T) = N` and
    -- `ker φ = T.subgroupOf K`.
    set φ : K →* (R ⧸ T) := (QuotientGroup.mk' T).comp K.subtype with hφ
    have hrange : φ.range = N := by
      rw [hφ, MonoidHom.range_comp, Subgroup.range_subtype]; exact hKmap
    have hkereq : φ.ker = T.subgroupOf K := by
      rw [hφ, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']; rfl
    have : IsCyclic ↥φ.range := by rw [hrange]; exact hNcyc
    have : IsCyclic (K ⧸ φ.ker) :=
      isCyclic_of_surjective (QuotientGroup.quotientKerEquivRange φ).symm.toMonoidHom
        (QuotientGroup.quotientKerEquivRange φ).symm.surjective
    have : (T.subgroupOf K).Normal := (inferInstance : T.Normal).subgroupOf K
    -- transport `IsCyclic (K ⧸ φ.ker)` along the equality `φ.ker = T.subgroupOf K`.
    exact isCyclic_of_surjective (QuotientGroup.quotientMulEquivOfEq hkereq).toMonoidHom
      (QuotientGroup.quotientMulEquivOfEq hkereq).surjective
  -- ⟨STEP 7 = (v)⟩ `R / K` is cyclic (`≅ (R/T)/N`).
  have hv : IsCyclic (R ⧸ K) := by
    -- `(R/T)/N ≃ (R/T)/(K.map (mk' T)) ≃ R/K`, and the first is cyclic.
    have e : ((R ⧸ T) ⧸ N) ≃* (R ⧸ K) :=
      (QuotientGroup.quotientMulEquivOfEq hKmap.symm).trans
        (QuotientGroup.quotientQuotientEquivQuotient T K hTleK)
    exact isCyclic_of_surjective e e.surjective
  -- ⟨STEP 8⟩ Identify `K = closure {a, z}` by `ext`.
  have hKeq : K = Subgroup.closure ({a, z} : Set R) := by
    apply le_antisymm
    · -- `x ∈ K = comap (mk' T) N ⟹ mk' T x ∈ N = ⟨mk' T a⟩ ⟹ x ∈ ⟨a, z⟩`.
      intro x hx
      rw [hK, Subgroup.mem_comap, hNeq, Subgroup.mem_zpowers_iff] at hx
      obtain ⟨k, hk⟩ := hx
      -- `mk' T x = (mk' T a)^k = mk' T (a^k)`, so `x * (a^k)⁻¹ ∈ ker (mk' T) = T = ⟨z⟩`.
      have hxa : QuotientGroup.mk' T (x * (a ^ k)⁻¹) = 1 := by
        rw [map_mul, map_inv, map_zpow, hk, mul_inv_cancel]
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hT,
        Subgroup.mem_zpowers_iff] at hxa
      obtain ⟨m, hm⟩ := hxa
      -- `x = z^m * a^k ∈ ⟨a, z⟩`.
      have hzmem : z ∈ Subgroup.closure ({a, z} : Set R) :=
        Subgroup.subset_closure (by simp)
      have hamem : a ∈ Subgroup.closure ({a, z} : Set R) :=
        Subgroup.subset_closure (by simp)
      have hxeq : x = z ^ m * a ^ k := by
        rw [hm]; group
      rw [hxeq]
      exact mul_mem ((Subgroup.closure ({a, z} : Set R)).zpow_mem hzmem m)
        ((Subgroup.closure ({a, z} : Set R)).zpow_mem hamem k)
    · -- `a, z ∈ K`.
      rw [Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · rw [SetLike.mem_coe, hK, Subgroup.mem_comap]; exact haN
      · rw [SetLike.mem_coe]; exact hTleK (by rw [hT]; exact Subgroup.mem_zpowers _)
  exact ⟨a, b, K, hKnorm, hKeq, hcommR, hiii, hiv, hv⟩

/-- **BG Prop 4.11, step 8** (mmd L1584-1586): a finite `p`-group `R` (`p` odd) with
`|Ω₁(R)| ≤ p²` whose commutator subgroup `R'` is cyclic is metacyclic.

This is the closing step of the non-abelian induction of Prop 4.11, stated as a clean
stand-alone lemma (the `a, b, z` setup of the induction is not needed). The general form
subsumes the abelian case (`R' = ⊥` is cyclic), so it faithfully captures the BG argument
without weakening the conclusion.

Proof (following BG): if `R` is cyclic it is metacyclic. Otherwise let `S` be a cyclic
subgroup maximal subject to `R' ⊆ S` (exists by finiteness, with witness `R'` itself,
which is cyclic by hypothesis). Since `R' ⊆ S`, `S ⊴ R`, and `S ≠ R` as `R` is not cyclic.
For *any* `S₁` with `S ≤ S₁` and `|S₁/S| = p` (i.e. `S₁ = comap (mk' S) P̄` for an order-`p`
subgroup `P̄ ≤ R/S`): `S₁` is not cyclic (else `S = S₁` by maximality, contradicting
`S.relIndex S₁ = p ≠ 1`), so by Lemma 4.5(b) `|Ω₁(S₁)| = p²`. Pushing `Ω₁(↥S₁)` into `R` and
squeezing against `|Ω₁(R)| ≤ p²` gives `Ω₁(S₁) = Ω₁(R)` (so `|Ω₁(R)| = p²`), hence
`Ω₁(R) ≤ S₁` and `S₁ = S ⊔ Ω₁(R)` (a tower-`relIndex` computation, using `Ω₁(R) ⊄ S`). As
`S ⊔ Ω₁(R)` does not depend on `P̄`, every order-`p` subgroup of `R/S` is
`(S ⊔ Ω₁(R)).map (mk' S)`, so `R/S` has a unique subgroup of order `p` and is cyclic
(`isCyclic_of_subgroups_card_prime_unique_of_odd`). Then `⟨S, R/S⟩` witnesses metacyclicity. -/
theorem isMetacyclic_of_isCyclic_commutator_of_card_omega1_le
    (hR : IsPGroup p R) (hp_odd : Odd p)
    (hΩ : Nat.card (Omega R p 1) ≤ p ^ 2)
    (hcyc : IsCyclic (_root_.commutator R)) :
    OddOrder.GroupTheory.IsMetacyclic R := by
  classical
  have hp : p.Prime := Fact.out
  -- ⟨STEP 0⟩ If `R` is cyclic, it is metacyclic; otherwise work with `hRcyc : ¬ IsCyclic R`.
  by_cases hRcyc : IsCyclic R
  · have := hRcyc
    exact OddOrder.GroupTheory.IsMetacyclic.of_isCyclic
  -- ⟨STEP 1⟩ Maximal cyclic `S` subject to `R' ⊆ S`, from finiteness (witness = `R'`).
  obtain ⟨S, hSsub, hSmax⟩ :=
    Finite.exists_le_maximal
      (p := fun H : Subgroup R => IsCyclic ↥H ∧ _root_.commutator R ≤ H) ⟨hcyc, le_refl _⟩
  have hScyc : IsCyclic ↥S := hSmax.1.1
  have hRprime_le : _root_.commutator R ≤ S := hSmax.1.2
  have := hScyc
  -- ⟨STEP 2⟩ `S ⊴ R` (since `R' ⊆ S`) and `S ≠ ⊤` (since `R` is not cyclic).
  have hSnorm : S.Normal := OddOrder.Isaacs.Ch06.normal_of_commutator_le hRprime_le
  have := hSnorm
  -- `R/S` is a `p`-group.
  have hQpg : IsPGroup p (R ⧸ S) := hR.to_quotient S
  -- ⟨STEP 5⟩ Uniqueness of order-`p` subgroups of `R/S` ⇒ `R/S` cyclic.
  have hRScyc : IsCyclic (R ⧸ S) := by
    refine OddOrder.Isaacs.Ch06.isCyclic_of_subgroups_card_prime_unique_of_odd hQpg hp_odd ?_
    -- For each order-`p` subgroup `P̄ ≤ R/S`, its preimage `S₁ = comap (mk' S) P̄` equals
    -- the fixed subgroup `S ⊔ Ω₁(R)`; hence `P̄ = (S ⊔ Ω₁(R)).map (mk' S)` for every `P̄`.
    have key : ∀ P : Subgroup (R ⧸ S), Nat.card P = p →
        Subgroup.comap (QuotientGroup.mk' S) P = S ⊔ Omega R p 1 := by
      intro P hP
      set S₁ : Subgroup R := Subgroup.comap (QuotientGroup.mk' S) P with hS₁_def
      have hS_le_S₁ : S ≤ S₁ := QuotientGroup.le_comap_mk' S P
      have hS₁pg : IsPGroup p S₁ := hR.to_subgroup S₁
      -- (5b) `S.relIndex S₁ = p`.
      have hSrel : S.relIndex S₁ = p := by
        have hker : S = (QuotientGroup.mk' S).ker := (QuotientGroup.ker_mk' S).symm
        rw [hker, Subgroup.relIndex_ker, hS₁_def,
          Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective S)]
        exact hP
      -- (5c) `S₁` is not cyclic: else maximality forces `S = S₁`, but `relIndex = p ≠ 1`.
      have hS₁nc : ¬ IsCyclic ↥S₁ := by
        intro hS₁cyc
        have hle : S₁ ≤ S := hSmax.2 ⟨hS₁cyc, hRprime_le.trans hS_le_S₁⟩ hS_le_S₁
        have hSeqS₁ : S = S₁ := le_antisymm hS_le_S₁ hle
        rw [← hSeqS₁, Subgroup.relIndex_self] at hSrel
        exact hp.one_lt.ne' hSrel.symm
      -- (5d) `S.subgroupOf S₁` is cyclic (`≅ ↥S`) of index `p`; apply Lemma 4.5(b) to `↥S₁`.
      have hSsub_cyc : IsCyclic ↥(S.subgroupOf S₁) :=
        isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hS_le_S₁).symm.toMonoidHom
          (Subgroup.subgroupOfEquivOfLe hS_le_S₁).symm.surjective
      have hSsub_idx : (S.subgroupOf S₁).index = p := hSrel
      obtain ⟨_hΩS₁_ea, hΩS₁_card⟩ :=
        isElementaryAbelian_omega1_of_isCyclic_index_prime hS₁pg hp_odd hS₁nc hSsub_cyc hSsub_idx
      -- (5e) `(Ω₁ ↥S₁).map S₁.subtype ≤ Ω₁(R)` and has order `p²`; squeeze with `hΩ` ⇒ equal.
      have hΩmap_le : (Omega (↥S₁) p 1).map S₁.subtype ≤ Omega R p 1 := by
        rw [Subgroup.map_le_iff_le_comap, Omega, Subgroup.closure_le]
        rintro ⟨g, hgS₁⟩ (hg : (⟨g, hgS₁⟩ : ↥S₁) ^ (p ^ 1) = 1)
        change (⟨g, hgS₁⟩ : ↥S₁) ∈ Subgroup.comap S₁.subtype (Omega R p 1)
        rw [Subgroup.mem_comap]
        refine Omega.mem_of_pow_eq_one ?_
        rw [pow_one]
        have hval := congrArg (Subgroup.subtype S₁) hg
        rw [map_pow, pow_one, map_one] at hval
        simpa using hval
      have hΩmap_card : Nat.card ((Omega (↥S₁) p 1).map S₁.subtype) = p ^ 2 := by
        rw [Subgroup.card_map_of_injective S₁.subtype_injective, hΩS₁_card]
      have hΩeq : (Omega (↥S₁) p 1).map S₁.subtype = Omega R p 1 :=
        Subgroup.eq_of_le_of_card_ge hΩmap_le (by rw [hΩmap_card]; exact hΩ)
      -- `|Ω₁(R)| = p²` (consequence of the squeeze) and `Ω₁(R) ≤ S₁`.
      have hΩR_card : Nat.card (Omega R p 1) = p ^ 2 := by rw [← hΩeq, hΩmap_card]
      have hΩR_le_S₁ : Omega R p 1 ≤ S₁ := by rw [← hΩeq]; exact Subgroup.map_subtype_le _
      -- `Ω₁(R)` is elementary abelian (image of the e.a. `Ω₁ ↥S₁`), so every element is
      -- `p`-torsion.
      have hΩR_ea : (Omega R p 1).IsElementaryAbelian p :=
        hΩeq ▸ _hΩS₁_ea.map S₁.subtype_injective
      have hΩR_pow : ∀ g : R, g ∈ Omega R p 1 → g ^ p = 1 := by
        intro g hg
        have := hΩR_ea.pow_eq_one ⟨g, hg⟩
        simpa using congrArg (Subtype.val) this
      -- `Ω₁(R) ⊄ S`: else `Ω₁(R) ≤ (Ω₁ ↥S).map subtype`, forcing `p² = |Ω₁(R)| ≤ |Ω₁ ↥S| = p`.
      have hΩR_not_le_S : ¬ Omega R p 1 ≤ S := by
        intro hle
        -- `S` is nontrivial (it contains the nontrivial `Ω₁(R)`, of order `p²`).
        have hS_nt : Nontrivial ↥S := by
          rw [← Finite.one_lt_card_iff_nontrivial]
          have h1 : Nat.card (Omega R p 1) ≤ Nat.card ↥S := Subgroup.card_le_of_le hle
          have h2 : 1 < Nat.card (Omega R p 1) := by
            rw [hΩR_card]; exact Nat.one_lt_pow (by norm_num) hp.one_lt
          omega
        -- each generator of `Ω₁(R)` lies in `(Ω₁ ↥S).map S.subtype`.
        have hΩR_le_ΩS : Omega R p 1 ≤ (Omega (↥S) p 1).map S.subtype := by
          intro x hx
          have hxS : x ∈ S := hle hx
          rw [Subgroup.mem_map]
          refine ⟨⟨x, hxS⟩, ?_, rfl⟩
          refine Omega.mem_of_pow_eq_one ?_
          rw [pow_one]
          ext
          rw [SubmonoidClass.coe_pow, Subgroup.coe_mk, OneMemClass.coe_one]
          exact hΩR_pow x hx
        have hΩS_card : Nat.card (Omega ↥S p 1) = p :=
          card_omega1_eq_prime_of_isCyclic (hR.to_subgroup S)
        have hΩSmap_card : Nat.card ((Omega ↥S p 1).map S.subtype) = p := by
          rw [Subgroup.card_map_of_injective S.subtype_injective, hΩS_card]
        have hle_card : Nat.card (Omega R p 1) ≤ p := by
          calc Nat.card (Omega R p 1)
              ≤ Nat.card ((Omega ↥S p 1).map S.subtype) := Subgroup.card_le_of_le hΩR_le_ΩS
            _ = p := hΩSmap_card
        rw [hΩR_card] at hle_card
        -- `p² ≤ p` is false for `p ≥ 2`.
        nlinarith [hp.two_le]
      -- (5f) `S₁ = S ⊔ Ω₁(R)` via a tower `relIndex` computation.
      have hSup_le : S ⊔ Omega R p 1 ≤ S₁ := sup_le hS_le_S₁ hΩR_le_S₁
      have hS_le_sup : S ≤ S ⊔ Omega R p 1 := le_sup_left
      have htower : S.relIndex (S ⊔ Omega R p 1) * (S ⊔ Omega R p 1).relIndex S₁ = p := by
        rw [Subgroup.relIndex_mul_relIndex S (S ⊔ Omega R p 1) S₁ hS_le_sup hSup_le]; exact hSrel
      have hfirst_ne_one : S.relIndex (S ⊔ Omega R p 1) ≠ 1 := by
        rw [Ne, Subgroup.relIndex_eq_one]
        intro hle
        exact hΩR_not_le_S (le_trans le_sup_right hle)
      have hsecond_eq_one : (S ⊔ Omega R p 1).relIndex S₁ = 1 := by
        -- `a * b = p` prime with `a ≠ 1` forces `a = p`, hence `b = 1`.
        set a := S.relIndex (S ⊔ Omega R p 1)
        set b := (S ⊔ Omega R p 1).relIndex S₁
        have hadvd : a ∣ p := Dvd.intro_left b (by rw [mul_comm]; exact htower)
        have ha_eq_p : a = p := (hp.eq_one_or_self_of_dvd a hadvd).resolve_left hfirst_ne_one
        rw [ha_eq_p] at htower
        have hp_pos : 0 < p := hp.pos
        have : p * b = p * 1 := by rw [mul_one]; exact htower
        exact Nat.eq_of_mul_eq_mul_left hp_pos this
      have hge : S₁ ≤ S ⊔ Omega R p 1 := Subgroup.relIndex_eq_one.mp hsecond_eq_one
      exact le_antisymm hge hSup_le
    -- Close uniqueness: both order-`p` subgroups map back to the same `comap`.
    intro P Q hP hQ
    have hPc := key P hP
    have hQc := key Q hQ
    have hPm : (Subgroup.comap (QuotientGroup.mk' S) P).map (QuotientGroup.mk' S) = P :=
      Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective S) P
    have hQm : (Subgroup.comap (QuotientGroup.mk' S) Q).map (QuotientGroup.mk' S) = Q :=
      Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective S) Q
    rw [← hPm, ← hQm, hPc, hQc]
  -- ⟨STEP 7⟩ `⟨S, R/S⟩` witnesses metacyclicity.
  exact ⟨S, hSnorm, hScyc, hRScyc⟩

omit [Finite R] in
/-- **Prop 4.11 micro-helper**: with `z` central, every element of `⟨a, z⟩` is `a ^ k * z ^ m`
for some `k, m : ℤ` (the subgroup generated by `a` and a central `z` is "abelian on `a, z`"). -/
private theorem exists_zpow_mul_zpow_of_mem_closure_pair_central {a z : R}
    (hz_center : z ∈ Subgroup.center R) {x : R} (hx : x ∈ Subgroup.closure ({a, z} : Set R)) :
    ∃ (k m : ℤ), x = a ^ k * z ^ m := by
  have hcz : Commute a z := Subgroup.mem_center_iff.mp hz_center a
  refine Subgroup.closure_induction
    (p := fun x _ => ∃ (k m : ℤ), x = a ^ k * z ^ m) ?_ ?_ ?_ ?_ hx
  · rintro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact ⟨1, 0, by simp⟩
    · exact ⟨0, 1, by simp⟩
  · exact ⟨0, 0, by simp⟩
  · rintro x y _ _ ⟨k₁, m₁, rfl⟩ ⟨k₂, m₂, rfl⟩
    have hcomm : Commute (z ^ m₁) (a ^ k₂) := (hcz.symm.zpow_left m₁).zpow_right k₂
    refine ⟨k₁ + k₂, m₁ + m₂, ?_⟩
    calc a ^ k₁ * z ^ m₁ * (a ^ k₂ * z ^ m₂)
        = a ^ k₁ * (z ^ m₁ * a ^ k₂) * z ^ m₂ := by group
      _ = a ^ k₁ * (a ^ k₂ * z ^ m₁) * z ^ m₂ := by rw [hcomm.eq]
      _ = a ^ (k₁ + k₂) * z ^ (m₁ + m₂) := by rw [zpow_add, zpow_add]; group
  · rintro x _ ⟨k, m, rfl⟩
    have hc2 : Commute (a ^ k) (z ^ m) := (hcz.zpow_left k).zpow_right m
    refine ⟨-k, -m, ?_⟩
    rw [mul_inv_rev, hc2.symm.inv_left.inv_right.eq, zpow_neg, zpow_neg]

omit [Finite R] in
omit [Fact (Nat.Prime p)] in
/-- **Prop 4.11 micro-helper**: with `z` central of order `p`, `(a ^ k * z ^ m) ^ p = a ^ (k*p)`
(the `z` part dies since `z ^ p = 1`). -/
private theorem zpow_mul_zpow_pow_of_central {a z : R} (hz_center : z ∈ Subgroup.center R)
    (hzp : orderOf z = p) (k m : ℤ) : (a ^ k * z ^ m) ^ p = a ^ (k * (p : ℤ)) := by
  have hcz : Commute a z := Subgroup.mem_center_iff.mp hz_center a
  have hc2 : Commute (a ^ k) (z ^ m) := (hcz.zpow_left k).zpow_right m
  have hzp1 : z ^ p = 1 := by rw [← hzp]; exact pow_orderOf_eq_one z
  have hzmp : (z ^ m) ^ p = 1 := by
    rw [← zpow_natCast (z ^ m) p, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hzp1, one_zpow]
  rw [hc2.mul_pow, hzmp, mul_one, ← zpow_natCast (a ^ k) p, ← zpow_mul]

/-- **Prop 4.11 micro-helper (STEP 2)**: extract a central element `z` of order `p` lying in a
nontrivial normal subgroup `V` of a finite `p`-group `R`.

`V` is normal and nontrivial, so `V ⊓ Z(R) ≠ 1` (`normal_inf_center_nontrivial`); Cauchy
(`exists_prime_orderOf_dvd_card'`) gives an element of order `p` in `V ⊓ Z(R)`. -/
private theorem exists_central_orderOf_eq_prime_mem_of_normal (hR : IsPGroup p R)
    {V : Subgroup R} [V.Normal] (hV : Nontrivial V) :
    ∃ z : R, z ∈ V ∧ z ∈ Subgroup.center R ∧ orderOf z = p := by
  have hp : p.Prime := Fact.out
  have hinf_nt : Nontrivial ((V ⊓ Subgroup.center R : Subgroup R)) :=
    OddOrder.Isaacs.Ch01.IsPGroup.normal_inf_center_nontrivial hR hV
  have hpg_inf : IsPGroup p (V ⊓ Subgroup.center R : Subgroup R) := hR.to_subgroup _
  have hpdvd : p ∣ Nat.card (V ⊓ Subgroup.center R : Subgroup R) := by
    rcases hpg_inf.card_eq_or_dvd with h1 | hd
    · exact absurd (Finite.card_le_one_iff_subsingleton.mp h1.le)
        (not_subsingleton_iff_nontrivial.mpr hinf_nt)
    · exact hd
  obtain ⟨g, hg⟩ :=
    exists_prime_orderOf_dvd_card' (G := (V ⊓ Subgroup.center R : Subgroup R)) p hpdvd
  exact ⟨(g : R), g.2.1, g.2.2, by rw [Subgroup.orderOf_coe, hg]⟩

/-- **Prop 4.11 micro-helper (STEP 4 + STEP 5)**: the `(4.7)` lift together with the
commutator equation `[a, b] = a^(i·p)·z^j`.

Given a finite non-abelian `p`-group `R` with a central `z` of order `p` such that `R/⟨z⟩` is
metacyclic, the `(4.7)` lift `exists_metacyclic_lift_of_isMetacyclic_quotient_center_prime`
produces `a, b, K = ⟨a, z⟩` with `K ◁ R`, `R' ≤ K`, `R = ⟨a,b,z⟩`, `K/⟨z⟩` and `R/K` cyclic.
Since `R` is non-abelian, `R/⟨z⟩` is not cyclic (Lemma 4.1), so `K/⟨z⟩ ≠ 1`; then
`W := ⟨aᵖ, z⟩ ◁ R` has `|K/W| = p`, and `K/W ≤ Z(R/W)` by Lemma δ
(`le_center_of_card_eq_prime_of_normal`), giving `[a, b] ∈ W`, i.e. `[a, b] = a^(i·p)·z^j`.

This packages STEP 5 of the non-abelian induction (mmd L1564) and feeds both closing branches. -/
private theorem exists_lift_commutator_eq_of_isMetacyclic_quotient_center_prime
    (hR : IsPGroup p R) {z : R} [(Subgroup.zpowers z).Normal] (hz : z ∈ Subgroup.center R)
    (hzp : orderOf z = p) (hnc : ¬ ∀ x y : R, x * y = y * x)
    (hmeta : OddOrder.GroupTheory.IsMetacyclic (R ⧸ Subgroup.zpowers z)) :
    ∃ (a b : R) (K : Subgroup R), ∃ _ : K.Normal,
      K = Subgroup.closure ({a, z} : Set R) ∧
      _root_.commutator R ≤ K ∧
      Subgroup.closure ({a, b, z} : Set R) = ⊤ ∧
      IsCyclic (K ⧸ (Subgroup.zpowers z).subgroupOf K) ∧
      IsCyclic (R ⧸ K) ∧
      ∃ (i j : ℤ), a⁻¹ * b⁻¹ * a * b = a ^ (i * (p : ℤ)) * z ^ j := by
  classical
  have hp : p.Prime := Fact.out
  set Z : Subgroup R := Subgroup.zpowers z with hZ_def
  -- ⟨STEP 4⟩ The `(4.7)` lift.
  obtain ⟨a, b, K, hKnorm, hKeq, hRp_le_K, hgen, hKTcyc, hRKcyc⟩ :=
    exists_metacyclic_lift_of_isMetacyclic_quotient_center_prime hR hz hzp hmeta
  have := hKnorm
  refine ⟨a, b, K, hKnorm, hKeq, hRp_le_K, hgen, hKTcyc, hRKcyc, ?_⟩
  -- ⟨STEP 5a⟩ `R/Z` is not cyclic (else `R/Z(R)` cyclic ⇒ `R` abelian, Lemma 4.1).
  have hZ_le_center : Z ≤ Subgroup.center R := by rw [hZ_def, Subgroup.zpowers_le]; exact hz
  have hRZ_ncyc : ¬ IsCyclic (R ⧸ Z) := by
    intro hcyc
    have := hcyc
    apply hnc
    intro x y
    exact (MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center
      (QuotientGroup.mk' Z)
      (le_trans (le_of_eq (QuotientGroup.ker_mk' Z)) hZ_le_center)).is_comm.comm x y
  -- ⟨STEP 5b⟩ `mk'Z a ≠ 1` (i.e. `a ∉ Z`): else `K = ⟨a,z⟩ = Z`, so `R/Z ≅ R/K` cyclic,
  -- contradicting `R/Z` non-cyclic.
  have haZ_ne : QuotientGroup.mk' Z a ≠ 1 := by
    intro hmk1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmk1
    -- `a ∈ Z`, so `K = closure{a, z} = Z`.
    have hzZ : z ∈ Z := by rw [hZ_def]; exact Subgroup.mem_zpowers z
    have hKeqZ : K = Z := by
      rw [hKeq]
      apply le_antisymm
      · rw [Subgroup.closure_le]
        intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl
        · exact hmk1
        · exact hzZ
      · rw [hZ_def, Subgroup.zpowers_le]; exact Subgroup.subset_closure (by simp)
    apply hRZ_ncyc
    -- transport `IsCyclic (R ⧸ K)` along `K = Z`.
    have := hRKcyc
    exact isCyclic_of_surjective (QuotientGroup.quotientMulEquivOfEq hKeqZ).toMonoidHom
      (QuotientGroup.quotientMulEquivOfEq hKeqZ).surjective
  have haK : a ∈ K := hKeq ▸ Subgroup.subset_closure (by simp)
  -- ⟨STEP 5c⟩ `W := ⟨aᵖ, z⟩ ◁ R`. Conjugates of generators stay in `W`: `g aᵖ g⁻¹ = (gag⁻¹)ᵖ`,
  -- and `gag⁻¹ ∈ K = ⟨a,z⟩` (K normal) is `a^k z^m`, so `(gag⁻¹)ᵖ = a^{kp} ∈ ⟨aᵖ⟩`.
  have hpow : ∀ g : R, (g * a * g⁻¹) ^ p ∈ Subgroup.zpowers (a ^ p) := by
    intro g
    have hmem : g * a * g⁻¹ ∈ K := hKnorm.conj_mem a haK g
    obtain ⟨k, m, heq⟩ :=
      exists_zpow_mul_zpow_of_mem_closure_pair_central hz (hKeq ▸ hmem)
    rw [heq, zpow_mul_zpow_pow_of_central hz hzp k m]
    -- `a ^ (k * p) = (a ^ p) ^ k ∈ ⟨aᵖ⟩`.
    have hap : a ^ (k * (p : ℤ)) = (a ^ p) ^ k := by
      rw [mul_comm, zpow_mul, zpow_natCast]
    rw [hap]
    exact zpow_mem (Subgroup.mem_zpowers (a ^ p)) k
  set W : Subgroup R := Subgroup.closure ({a ^ p, z} : Set R) with hW_def
  have hapW : a ^ p ∈ W := Subgroup.subset_closure (by simp)
  have hzW : z ∈ W := Subgroup.subset_closure (by simp)
  have hW_normal : W.Normal := by
    refine ⟨fun n hn g => ?_⟩
    induction hn using Subgroup.closure_induction with
    | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · rw [show g * a ^ p * g⁻¹ = (g * a * g⁻¹) ^ p by rw [conj_pow]]
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hpow g)
        rw [← hk]; exact zpow_mem hapW k
      · rw [Subgroup.mem_center_iff.mp hz g, mul_assoc, mul_inv_cancel, mul_one]; exact hzW
    | one => simp
    | mul x y _ _ hx hy =>
        rw [show g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) by group]; exact W.mul_mem hx hy
    | inv x _ hx => rw [show g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ by group]; exact W.inv_mem hx
  have := hW_normal
  -- ⟨STEP 5d⟩ `a ∉ W`: else `a = (aᵖ)^k z^m ⇒ a^{1-pk} ∈ Z ⇒ (mk'Z a)^{1-pk} = 1`,
  -- so `orderOf (mk'Z a) ∣ 1 - pk`; but `p ∣ orderOf (mk'Z a)` forces `p ∣ 1`, contradiction.
  have haW : a ∉ W := by
    intro haWmem
    -- `W = ⟨aᵖ, z⟩`, so by the standard form (`aᵖ` and `z` commute, `z` central) `a = (aᵖ)^k z^m`.
    obtain ⟨k, m, heq⟩ :=
      exists_zpow_mul_zpow_of_mem_closure_pair_central (a := a ^ p) hz haWmem
    -- `a^{1 - pk} = z^m ∈ Z`.
    have hcz : Commute a z := Subgroup.mem_center_iff.mp hz a
    have ha_in_Z : a ^ (1 - (p : ℤ) * k) ∈ Z := by
      have h1 : a = a ^ ((p : ℤ) * k) * z ^ m := by
        rw [← zpow_natCast a p, ← zpow_mul] at heq; exact heq
      -- from `a = a^{pk} z^m`: `z^m = a^{-pk} a = a^{1-pk}`.
      have h2 : z ^ m = a ^ (1 - (p : ℤ) * k) := by
        have h5 : z ^ m = (a ^ ((p : ℤ) * k))⁻¹ * a := by
          apply mul_left_cancel (a := a ^ ((p : ℤ) * k))
          rw [mul_inv_cancel_left, ← h1]
        rw [h5, ← zpow_neg, show (1 : ℤ) - (p : ℤ) * k = -((p : ℤ) * k) + 1 by ring,
          zpow_add, zpow_one]
      rw [← h2, hZ_def]; exact zpow_mem (Subgroup.mem_zpowers z) m
    -- `(mk'Z a)^{1 - pk} = 1`, so `orderOf (mk'Z a) ∣ 1 - pk`.
    have hord_dvd : (orderOf (QuotientGroup.mk' Z a) : ℤ) ∣ (1 - (p : ℤ) * k) := by
      rw [orderOf_dvd_iff_zpow_eq_one, ← map_zpow, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff]
      exact ha_in_Z
    -- `p ∣ orderOf (mk'Z a)` (nontrivial p-group element).
    have hp_dvd_ord : (p : ℤ) ∣ (orderOf (QuotientGroup.mk' Z a) : ℤ) := by
      have hQpg : IsPGroup p (R ⧸ Z) := hR.to_quotient Z
      obtain ⟨t, ht⟩ := (IsPGroup.iff_orderOf.mp hQpg) (QuotientGroup.mk' Z a)
      have ht_pos : 0 < t := by
        rcases Nat.eq_zero_or_pos t with h0 | hpos
        · rw [h0, pow_zero] at ht
          exact absurd (orderOf_eq_one_iff.mp ht) haZ_ne
        · exact hpos
      have : (p : ℤ) ∣ ((p ^ t : ℕ) : ℤ) := by
        rw [Nat.cast_pow]; exact dvd_pow_self _ ht_pos.ne'
      rwa [← ht] at this
    -- `p ∣ (1 - pk)` and `p ∣ pk` ⇒ `p ∣ 1`, contradiction.
    have hp_dvd_one : (p : ℤ) ∣ 1 := by
      have hd1 : (p : ℤ) ∣ (1 - (p : ℤ) * k) := dvd_trans hp_dvd_ord hord_dvd
      have hd2 : (p : ℤ) ∣ (p : ℤ) * k := Dvd.intro k rfl
      have := dvd_add hd1 hd2
      simpa using this
    have hle : (p : ℤ) ≤ 1 := Int.le_of_dvd one_pos hp_dvd_one
    have hle' : p ≤ 1 := by exact_mod_cast hle
    have := hp.one_lt
    omega
  -- ⟨STEP 5e⟩ `K.map (mk'W) = ⟨mk'W a⟩` is cyclic of order `p`.
  -- `mk'W z = 1` (since `z ∈ W`), so the image of `K = ⟨a, z⟩` is `⟨mk'W a⟩`.
  have hmkWz : QuotientGroup.mk' W z = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]; exact hzW
  have hKmapeq : K.map (QuotientGroup.mk' W) = Subgroup.zpowers (QuotientGroup.mk' W a) := by
    rw [hKeq, MonoidHom.map_closure, Set.image_pair, hmkWz]
    apply le_antisymm
    · rw [Subgroup.closure_le]
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · exact Subgroup.mem_zpowers _
      · exact one_mem _
    · rw [Subgroup.zpowers_le]; exact Subgroup.subset_closure (by simp)
  -- `orderOf (mk'W a) = p`: `(mk'W a)^p = mk'W (aᵖ) = 1` (a^p ∈ W) and `mk'W a ≠ 1` (a ∉ W).
  have hmkWa_pow : (QuotientGroup.mk' W a) ^ p = 1 := by
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]; exact hapW
  have hmkWa_ne : QuotientGroup.mk' W a ≠ 1 := by
    rw [QuotientGroup.mk'_apply, Ne, QuotientGroup.eq_one_iff]; exact haW
  have hord : orderOf (QuotientGroup.mk' W a) = p := by
    have hd : orderOf (QuotientGroup.mk' W a) ∣ p := orderOf_dvd_of_pow_eq_one hmkWa_pow
    have hne1 : orderOf (QuotientGroup.mk' W a) ≠ 1 := by
      rw [Ne, orderOf_eq_one_iff]; exact hmkWa_ne
    exact (Nat.dvd_prime hp).mp hd |>.resolve_left hne1
  have hKWcard : Nat.card (K.map (QuotientGroup.mk' W)) = p := by
    rw [hKmapeq, Nat.card_zpowers, hord]
  -- ⟨STEP 5f⟩ `K.map (mk'W) ≤ Z(R/W)` (Lemma δ), so `[a, b] ∈ W`.
  have hKW_central : K.map (QuotientGroup.mk' W) ≤ Subgroup.center (R ⧸ W) :=
    le_center_of_card_eq_prime_of_normal (hR.to_quotient W) hKWcard
  have hcomm_mem_W : a⁻¹ * b⁻¹ * a * b ∈ W := by
    -- `mk'W a ∈ K.map (mk'W) ≤ Z(R/W)`, so it commutes with `mk'W b`; hence `mk'W (a⁻¹b⁻¹ab) = 1`.
    have hmkWa_mem : QuotientGroup.mk' W a ∈ K.map (QuotientGroup.mk' W) :=
      Subgroup.mem_map_of_mem _ haK
    have hmkWa_center : QuotientGroup.mk' W a ∈ Subgroup.center (R ⧸ W) := hKW_central hmkWa_mem
    have hcomm : Commute (QuotientGroup.mk' W a) (QuotientGroup.mk' W b) :=
      (Subgroup.mem_center_iff.mp hmkWa_center (QuotientGroup.mk' W b)).symm
    have h0 : QuotientGroup.mk' W (a⁻¹ * b⁻¹ * a * b) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]
      set A := QuotientGroup.mk' W a
      set B := QuotientGroup.mk' W b
      have h1 : A⁻¹ * B⁻¹ * A * B = A⁻¹ * (B⁻¹ * A) * B := by group
      rw [h1, hcomm.symm.inv_left.eq]; group
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h0
  -- ⟨STEP 5g⟩ standard form `a⁻¹b⁻¹ab = (aᵖ)^i z^j = a^{ip}z^j` from membership in `W = ⟨aᵖ, z⟩`.
  obtain ⟨i, j, hij⟩ :=
    exists_zpow_mul_zpow_of_mem_closure_pair_central (a := a ^ p) hz hcomm_mem_W
  refine ⟨i, j, ?_⟩
  rw [hij, ← zpow_natCast a p, ← zpow_mul, mul_comm (p : ℤ) i]

/-- **BG Proposition 4.11** (Huppert, *Endliche Gruppen I*, Satz III.11.6).
A finite `p`-group `R` with `p > 3` and `|Ω₁(R)| ≤ p²` is metacyclic.

Strong induction on `|R|`. If `R` is abelian, the abelian base case
(`isMetacyclic_of_omega1_card_le_prime_sq_of_comm`) closes it. Otherwise `R' = [R, R] ≠ ⊥`,
so `R' ⊓ Z(R) ≠ 1`; pick a central `z` of order `p` inside `R'` (and inside `℧¹(R')` when the
latter is nontrivial). With `T := ⟨z⟩`, Lemma 4.9 gives `|Ω₁(R/T)| ≤ p²`, so by induction `R/T`
is metacyclic; the `(4.7)` lift produces `a, b` with `K := ⟨a, z⟩ ◁ R`, `R' ≤ K`, `R = ⟨a,b,z⟩`,
`K/T` and `R/K` cyclic. Since `R` is non-abelian, `R/T` is not cyclic (else `R/Z(R)` cyclic ⇒ `R`
abelian, Lemma 4.1), so `[a,b] ∈ ⟨aᵖ, z⟩` (order-`p` quotient `K/⟨aᵖ,z⟩` is central, Lemma δ).
Then:
* if `℧¹(R') ≠ 1`: `z ∈ ℧¹(R') ⊆ ℧¹(K) ⊆ ⟨a⟩`, so `K = ⟨a⟩` is cyclic normal with `R/K` cyclic
  ⇒ `R` metacyclic;
* if `℧¹(R') = 1`: `R'` has exponent `p`, and Lemma 4.2 gives `[a,b] ∈ Z(R)`, so `R' = ⟨[a,b]⟩`
  is cyclic; step 8 (`isMetacyclic_of_isCyclic_commutator_of_card_omega1_le`) closes it.

mmd `references/bg/local-analysis.mmd` L1554-1586. -/
theorem isMetacyclic_of_omega1_card_le_prime_sq (hR : IsPGroup p R) (hp3 : 3 < p)
    (hΩ : Nat.card (Omega R p 1) ≤ p ^ 2) : OddOrder.GroupTheory.IsMetacyclic R := by
  classical
  have hp : p.Prime := Fact.out
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  -- Strong induction on `|R|`, packaged in a (type-polymorphic) motive.
  let motive : ℕ → Prop := fun n =>
    ∀ {R' : Type _} [Group R'] [Finite R'], IsPGroup p R' →
      Nat.card (Omega R' p 1) ≤ p ^ 2 → Nat.card R' = n →
      OddOrder.GroupTheory.IsMetacyclic R'
  refine (Nat.strongRecOn (motive := motive) (Nat.card R) ?_) hR hΩ rfl
  clear hR hΩ
  intro n ih R' _ _ hR' hΩ' hcard
  -- ⟨STEP 1⟩ abelian case.
  by_cases hab : ∀ x y : R', x * y = y * x
  · exact isMetacyclic_of_omega1_card_le_prime_sq_of_comm hR' hab hΩ'
  -- ⟨STEP 2⟩ pick a central `z` of order `p` inside `R' = [R', R']` (and inside `℧¹(R')` if `≠1`).
  set Rp : Subgroup R' := _root_.commutator R' with hRp
  have hRp_ne : Rp ≠ ⊥ := by
    rw [hRp]
    intro hc
    exact hab (fun x y => ((commutator_eq_bot_iff R').mp hc).is_comm.comm x y)
  have hRp_nt : Nontrivial Rp := (Subgroup.nontrivial_iff_ne_bot Rp).mpr hRp_ne
  have hRp_normal : Rp.Normal := by rw [hRp]; infer_instance
  -- `℧¹(R') = (Agemo Rp p 1).map Rp.subtype`, pushed into `R'`; characteristic in `Rp ◁ R'`,
  -- hence normal in `R'`.
  set U₀ : Subgroup R' := (Agemo Rp p 1).map Rp.subtype with hU₀
  have hU₀_normal : U₀.Normal := by rw [hU₀]; infer_instance
  have hU₀_le : U₀ ≤ Rp := by rw [hU₀]; exact Subgroup.map_subtype_le _
  -- Branch on `℧¹(R') = ⊥`; this drives both the choice of `z` and the closing step.
  by_cases h𝒰 : U₀ = ⊥
  -- ============================================================
  -- BRANCH `℧¹(R') = ⊥`  (STEP 7): `z ∈ R' ⊓ Z(R')`.
  -- ============================================================
  · -- ⟨STEP 2⟩ extract a central `z` of order `p` in `Rp = R'`.
    obtain ⟨z, hzRp, hz_center, hzp⟩ :=
      exists_central_orderOf_eq_prime_mem_of_normal hR' (V := Rp) hRp_nt
    set Z : Subgroup R' := Subgroup.zpowers z with hZ_def
    have hZ_le_center : Z ≤ Subgroup.center R' := by
      rw [hZ_def, Subgroup.zpowers_le]; exact hz_center
    have hZ_normal : Z.Normal := by
      constructor; intro nn hnn g'
      have := Subgroup.mem_center_iff.mp (hZ_le_center hnn) g'
      rw [this, mul_assoc, mul_inv_cancel, mul_one]; exact hnn
    -- ⟨STEP 3⟩ Lemma 4.9 + IH ⇒ `R'/Z` metacyclic.
    have hΩZ : Nat.card (Omega (R' ⧸ Z) p 1) ≤ p ^ 2 :=
      card_omega1_quotient_le_prime_sq hR' hp3 hΩ' Z
    have hZcard : Nat.card Z = p := by rw [hZ_def, Nat.card_zpowers, hzp]
    have hRZ_lt : Nat.card (R' ⧸ Z) < n := by
      rw [← hcard, ← Z.index_eq_card]
      have hmul := Z.card_mul_index
      have hZpos : 1 < Nat.card Z := by rw [hZcard]; exact hp.one_lt
      calc Z.index = Nat.card R' / Nat.card Z := by
              rw [← hmul, Nat.mul_div_cancel_left _ Nat.card_pos]
        _ < Nat.card R' := Nat.div_lt_self Nat.card_pos hZpos
    have hmeta : OddOrder.GroupTheory.IsMetacyclic (R' ⧸ Z) :=
      ih (Nat.card (R' ⧸ Z)) hRZ_lt (hR'.to_quotient Z) hΩZ rfl
    -- ⟨STEP 4 + STEP 5⟩ the `(4.7)` lift and `a⁻¹b⁻¹ab = a^{ip}z^j`.
    obtain ⟨a, b, K, hKnorm, hKeq, hRp_le_K, hgen, _hKTcyc, hRKcyc, i, j, hij⟩ :=
      exists_lift_commutator_eq_of_isMetacyclic_quotient_center_prime hR' hz_center hzp hab hmeta
    -- ⟨STEP 7⟩ `℧¹(R') = ⊥` ⇒ `Rp = R'` has exponent `p`.
    have hRp_exp : ∀ x : R', x ∈ Rp → x ^ p = 1 := by
      intro x hx
      have hmem : (⟨x, hx⟩ : ↥Rp) ^ (p ^ 1) ∈ Agemo Rp p 1 :=
        Agemo.mem_of_eq_pow (G := ↥Rp) ⟨x, hx⟩
      have hmap : Rp.subtype ((⟨x, hx⟩ : ↥Rp) ^ (p ^ 1)) ∈ U₀ :=
        hU₀ ▸ Subgroup.mem_map_of_mem _ hmem
      rw [h𝒰, Subgroup.mem_bot] at hmap
      have : x ^ (p ^ 1) = 1 := by
        rw [map_pow, Subgroup.coe_subtype] at hmap; simpa using hmap
      rwa [pow_one] at this
    set c : R' := a⁻¹ * b⁻¹ * a * b with hc_def
    -- `c = a⁻¹b⁻¹ab ∈ commutator R' = Rp`, so `c ^ p = 1`.
    have hc_mem_Rp : c ∈ Rp := by
      rw [hRp, hc_def]
      have : ⁅a⁻¹, b⁻¹⁆ ∈ _root_.commutator R' :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top a⁻¹) (Subgroup.mem_top b⁻¹)
      rwa [commutatorElement_def, inv_inv, inv_inv] at this
    have hcp : c ^ p = 1 := hRp_exp c hc_mem_Rp
    have hbz : Commute b z := Subgroup.mem_center_iff.mp hz_center b
    have hcz : Commute a z := Subgroup.mem_center_iff.mp hz_center a
    -- (A) `Commute a c`; (B) `c^{ip}=1`; (D) `b⁻¹ a b = a c`; closing `b⁻¹ c b = c`.
    have hca : Commute a c := by
      rw [hij]
      exact ((Commute.refl a).zpow_right _).mul_right (hcz.zpow_right j)
    have hcip : c ^ (i * (p : ℤ)) = 1 := by
      rw [mul_comm i, zpow_mul, zpow_natCast, hcp, one_zpow]
    -- `Commute b c` (BG's `[a,b]^b = [a,b]`).
    have hcb : Commute b c := by
      have hzb : Commute (z ^ j) b := (hbz.symm.zpow_left j)
      have hc1 : b⁻¹ * z ^ j * b = z ^ j := by rw [mul_assoc, hzb.eq]; group
      have hc2 : (b⁻¹ * a * b) ^ (i * (p : ℤ)) = b⁻¹ * a ^ (i * (p : ℤ)) * b := by
        have := @conj_zpow R' _ (i * (p : ℤ)) b⁻¹ a; simpa using this
      have hac : b⁻¹ * a * b = a * c := by rw [hc_def]; group
      have hconj : b⁻¹ * c * b = c := by
        conv_lhs => rw [hij]
        rw [show b⁻¹ * (a ^ (i * (p : ℤ)) * z ^ j) * b
              = (b⁻¹ * a ^ (i * (p : ℤ)) * b) * (b⁻¹ * z ^ j * b) by group, hc1, ← hc2,
          hac, hca.mul_zpow, hcip, mul_one, ← hij]
      have e : b * (b⁻¹ * c * b) = b * c := by rw [hconj]
      rw [← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul] at e
      exact e.symm
    -- `c ∈ Z(R')`: it commutes with the generators `a, b, z`, and `R' = ⟨a, b, z⟩`.
    have hc_center : c ∈ Subgroup.center R' := by
      rw [Subgroup.mem_center_iff]
      intro w
      have hw : w ∈ Subgroup.closure ({a, b, z} : Set R') := by rw [hgen]; exact Subgroup.mem_top w
      -- every generator commutes with `c`.
      have hwc : w ∈ Subgroup.centralizer ({c} : Set R') := by
        have hgen_le : Subgroup.closure ({a, b, z} : Set R') ≤ Subgroup.centralizer {c} := by
          rw [Subgroup.closure_le]
          intro y hy
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
          rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
          rcases hy with rfl | rfl | rfl
          · exact hca.eq
          · exact hcb.eq
          · exact (Subgroup.mem_center_iff.mp hz_center c).symm
        exact hgen_le hw
      rw [Subgroup.mem_centralizer_singleton_iff] at hwc
      exact hwc
    -- `commutator R' = ⟨c⟩` is cyclic.
    have hcyc_comm : IsCyclic (_root_.commutator R') := by
      have hcomm_eq : _root_.commutator R' = Subgroup.zpowers c := by
        apply le_antisymm
        · -- `R'/⟨c⟩` is abelian (generators `a, b, z` commute mod `⟨c⟩`), so `R' ≤ ⟨c⟩`.
          have hZc_normal : (Subgroup.zpowers c).Normal := by
            constructor; intro nn hnn g'
            have := Subgroup.mem_center_iff.mp (Subgroup.zpowers_le.mpr hc_center hnn) g'
            rw [this, mul_assoc, mul_inv_cancel, mul_one]; exact hnn
          rw [← Subgroup.Normal.quotient_commutative_iff_commutator_le]
          have htop : Subgroup.closure
              ({QuotientGroup.mk' (Subgroup.zpowers c) a, QuotientGroup.mk' (Subgroup.zpowers c) b,
                QuotientGroup.mk' (Subgroup.zpowers c) z} : Set (R' ⧸ Subgroup.zpowers c)) = ⊤ := by
            have h1 : (Subgroup.closure ({a, b, z} : Set R')).map (QuotientGroup.mk'
                (Subgroup.zpowers c)) = ⊤ := by
              rw [hgen, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
            rw [MonoidHom.map_closure] at h1
            rw [← h1]; congr 1
            rw [Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]
          -- `[a,b] = c ∈ ⟨c⟩` (so `mk a, mk b` commute); `z` is central; hence all generators
          -- commute.
          have hmkc : QuotientGroup.mk' (Subgroup.zpowers c) c = 1 := by
            rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]; exact Subgroup.mem_zpowers c
          have hab_q : Commute (QuotientGroup.mk' (Subgroup.zpowers c) a)
              (QuotientGroup.mk' (Subgroup.zpowers c) b) := by
            have : QuotientGroup.mk' (Subgroup.zpowers c) (a⁻¹ * b⁻¹ * a * b) = 1 := by
              rw [← hc_def]; exact hmkc
            rw [map_mul, map_mul, map_mul, map_inv, map_inv] at this
            -- `ā⁻¹ b̄⁻¹ ā b̄ = 1 ⇒ Commute ā b̄`.
            have heq : QuotientGroup.mk' (Subgroup.zpowers c) b * QuotientGroup.mk'
                (Subgroup.zpowers c) a
                = QuotientGroup.mk' (Subgroup.zpowers c) a * QuotientGroup.mk' (Subgroup.zpowers c)
                    b := by
              set A := QuotientGroup.mk' (Subgroup.zpowers c) a
              set B := QuotientGroup.mk' (Subgroup.zpowers c) b
              have h2 : A * (A⁻¹ * B⁻¹ * A * B) = A := by rw [this, mul_one]
              rw [show A * (A⁻¹ * B⁻¹ * A * B) = B⁻¹ * A * B by group] at h2
              have h3 : B * (B⁻¹ * A * B) = B * A := by rw [h2]
              rw [← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul] at h3
              exact h3.symm
            exact heq.symm
          have haz_q : Commute (QuotientGroup.mk' (Subgroup.zpowers c) a)
              (QuotientGroup.mk' (Subgroup.zpowers c) z) := by
            have : Commute a z := hcz
            exact (this.map (QuotientGroup.mk' (Subgroup.zpowers c)))
          have hbz_q : Commute (QuotientGroup.mk' (Subgroup.zpowers c) b)
              (QuotientGroup.mk' (Subgroup.zpowers c) z) := by
            have : Commute b z := hbz
            exact (this.map (QuotientGroup.mk' (Subgroup.zpowers c)))
          have hcomm_top : IsMulCommutative (Subgroup.closure
              ({QuotientGroup.mk' (Subgroup.zpowers c) a, QuotientGroup.mk' (Subgroup.zpowers c) b,
                QuotientGroup.mk' (Subgroup.zpowers c) z} : Set (R' ⧸ Subgroup.zpowers c))) := by
            refine Subgroup.isMulCommutative_closure ?_
            intro x hx y hy
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
            rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
              first
                | rfl
                | exact hab_q.eq | exact hab_q.symm.eq
                | exact haz_q.eq | exact haz_q.symm.eq
                | exact hbz_q.eq | exact hbz_q.symm.eq
          rw [htop] at hcomm_top
          exact ⟨⟨fun x y => by
            have := hcomm_top.is_comm.comm (⟨x, Subgroup.mem_top x⟩ : (⊤ : Subgroup (R' ⧸
                Subgroup.zpowers c)))
              ⟨y, Subgroup.mem_top y⟩
            exact Subtype.ext_iff.mp this⟩⟩
        · rw [Subgroup.zpowers_le, hc_def]
          have : ⁅a⁻¹, b⁻¹⁆ ∈ _root_.commutator R' :=
            Subgroup.commutator_mem_commutator (Subgroup.mem_top a⁻¹) (Subgroup.mem_top b⁻¹)
          rwa [commutatorElement_def, inv_inv, inv_inv] at this
      rw [hcomm_eq]; infer_instance
    -- ⟨STEP 8⟩ `R'` has cyclic commutator ⇒ metacyclic (helper γ).
    exact isMetacyclic_of_isCyclic_commutator_of_card_omega1_le hR' hodd hΩ' hcyc_comm
  -- ============================================================
  -- BRANCH `℧¹(R') ≠ ⊥`  (STEP 6): `z ∈ ℧¹(R') ⊓ Z(R')`.
  -- ============================================================
  · -- ⟨STEP 2⟩ extract a central `z` of order `p` in `U₀ = ℧¹(R') ≤ Rp`.
    have hU₀_nt : Nontrivial U₀ := (Subgroup.nontrivial_iff_ne_bot U₀).mpr h𝒰
    obtain ⟨z, hzU₀, hz_center, hzp⟩ :=
      exists_central_orderOf_eq_prime_mem_of_normal hR' (V := U₀) hU₀_nt
    have hzRp : z ∈ Rp := hU₀_le hzU₀
    set Z : Subgroup R' := Subgroup.zpowers z with hZ_def
    have hZ_le_center : Z ≤ Subgroup.center R' := by
      rw [hZ_def, Subgroup.zpowers_le]; exact hz_center
    have hZ_normal : Z.Normal := by
      constructor; intro nn hnn g'
      have := Subgroup.mem_center_iff.mp (hZ_le_center hnn) g'
      rw [this, mul_assoc, mul_inv_cancel, mul_one]; exact hnn
    -- ⟨STEP 3⟩ Lemma 4.9 + IH ⇒ `R'/Z` metacyclic.
    have hΩZ : Nat.card (Omega (R' ⧸ Z) p 1) ≤ p ^ 2 :=
      card_omega1_quotient_le_prime_sq hR' hp3 hΩ' Z
    have hZcard : Nat.card Z = p := by rw [hZ_def, Nat.card_zpowers, hzp]
    have hRZ_lt : Nat.card (R' ⧸ Z) < n := by
      rw [← hcard, ← Z.index_eq_card]
      have hmul := Z.card_mul_index
      have hZpos : 1 < Nat.card Z := by rw [hZcard]; exact hp.one_lt
      calc Z.index = Nat.card R' / Nat.card Z := by
              rw [← hmul, Nat.mul_div_cancel_left _ Nat.card_pos]
        _ < Nat.card R' := Nat.div_lt_self Nat.card_pos hZpos
    have hmeta : OddOrder.GroupTheory.IsMetacyclic (R' ⧸ Z) :=
      ih (Nat.card (R' ⧸ Z)) hRZ_lt (hR'.to_quotient Z) hΩZ rfl
    -- ⟨STEP 4 + STEP 5⟩ the `(4.7)` lift (the commutator equation is not needed here).
    obtain ⟨a, b, K, hKnorm, hKeq, hRp_le_K, _hgen, hKTcyc, hRKcyc, _i, _j, _hij⟩ :=
      exists_lift_commutator_eq_of_isMetacyclic_quotient_center_prime hR' hz_center hzp hab hmeta
    -- ⟨STEP 6⟩ `z ∈ ℧¹(R') ⊆ ⟨a⟩`, so `K = ⟨a⟩` is cyclic.
    -- Every `x ∈ Rp ⊆ K = ⟨a, z⟩` is `a^k z^m`, so `x^p = a^{kp} ∈ ⟨a⟩`; hence `U₀ ≤ ⟨a⟩`.
    have hU₀_le_zpa : U₀ ≤ Subgroup.zpowers a := by
      rw [hU₀, Subgroup.map_le_iff_le_comap, Agemo, Subgroup.closure_le]
      rintro w ⟨g, rfl⟩
      simp only [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.coe_subtype]
      -- `(g : R')^(p^1) = a^{kp} ∈ ⟨a⟩` where `g ∈ ↥Rp ⊆ K`.
      have hgRp : (g : R') ∈ _root_.commutator R' := hRp ▸ g.2
      have hgK : (g : R') ∈ K := hRp_le_K hgRp
      obtain ⟨k, m, hkm⟩ :=
        exists_zpow_mul_zpow_of_mem_closure_pair_central hz_center (hKeq ▸ hgK)
      change ((g : R') ^ (p ^ 1)) ∈ Subgroup.zpowers a
      rw [pow_one, hkm, zpow_mul_zpow_pow_of_central hz_center hzp k m]
      exact zpow_mem (Subgroup.mem_zpowers a) (k * (p : ℤ))
    have hz_in_a : z ∈ Subgroup.zpowers a := hU₀_le_zpa hzU₀
    -- `K = closure{a, z} = ⟨a⟩`.
    have hK_eq_zpa : K = Subgroup.zpowers a := by
      rw [hKeq]
      apply le_antisymm
      · rw [Subgroup.closure_le]
        intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl
        · exact Subgroup.mem_zpowers _
        · exact hz_in_a
      · rw [Subgroup.zpowers_le]; exact Subgroup.subset_closure (by simp)
    have hKcyc : IsCyclic K := by rw [hK_eq_zpa]; infer_instance
    -- `⟨K, R/K⟩` witnesses metacyclicity.
    exact ⟨K, hKnorm, hKcyc, hRKcyc⟩

end OddOrder.BG.Ch1.S04


