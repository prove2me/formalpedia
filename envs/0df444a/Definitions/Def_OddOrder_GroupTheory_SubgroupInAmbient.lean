-- Prove2me | Definitions.Def_OddOrder_GroupTheory_SubgroupInAmbient
-- name    : OddOrder_GroupTheory_SubgroupInAmbient
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:04:33.264693+00:00
-- url     : https://prove2.me/theorems/f84cbcc9-0906-43e3-8ffa-74810b3f5444
-- title:
--   Subgroup constructions realized in the ambient group
-- statement:
--   A shared module for two constructions needed by both Bender–Glauberman (Chapters II–IV) and Peterfalvi (Sections 10–16), realized as subgroups of the ambient group $G$ rather than of $H$. It is the single canonical home for what were previously duplicated definitions.
--
--   Main definitions: `derivedInG` (the derived subgroup $H'$ of a subgroup $H$, mapped into $G$), `opiCoreInG` (the $\pi$-core $O_\pi(H)$ mapped into $G$), and a lemma that $H\sqcup C$ is normal when $H\trianglelefteq G$, $C\trianglelefteq U$ and $G=H\sqcup U$.
--
--   The bundle also proves 18 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/SubgroupInAmbient.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/SubgroupInAmbient.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Isaacs_Ch03_SplitExtensions_Main
import Definitions.Def_OddOrder_GroupTheory_OpResidual

namespace OddOrder.GroupTheory

open OddOrder.Isaacs

variable {G : Type*} [Group G]

/-- **`H'` in `G`**: the derived subgroup `commutator ↥H` of a subgroup `H`,
mapped back into the ambient group `G` via `H.subtype`. -/
def derivedInG (H : Subgroup G) : Subgroup G :=
  (commutator ↥H).map H.subtype

/-- **`O_π(H)` in `G`**: the `π`-core of the subgroup `H` (largest normal
`π`-subgroup of `↥H`), mapped back into the ambient group `G` via `H.subtype`.
`opiCoreInG {p} H = O_p(H)` and `opiCoreInG {p}ᶜ H = O_{p'}(H)`, both in `G`. -/
def opiCoreInG (π : Set ℕ) (H : Subgroup G) : Subgroup G :=
  (Ch03.oPiCore π ↥H).map H.subtype

/-- `O_π(H) ≤ H` in the ambient group. -/
theorem opiCoreInG_le (π : Set ℕ) (H : Subgroup G) : opiCoreInG π H ≤ H :=
  Subgroup.map_subtype_le _

/-- The order of `opiCoreInG π H` agrees with the order of the `π`-core of `↥H`. -/
theorem card_opiCoreInG (π : Set ℕ) (H : Subgroup G) :
    Nat.card ↥(opiCoreInG π H) = Nat.card ↥(Ch03.oPiCore π ↥H) :=
  (Nat.card_congr (Subgroup.equivMapOfInjective _ H.subtype
    H.subtype_injective).toEquiv).symm

/-- `opiCoreInG π H` is a `π`-subgroup (ambient form of `oPiCore.isPiGroup`). -/
theorem isPiSubgroup_opiCoreInG [Finite G] (π : Set ℕ) (H : Subgroup G) :
    Subgroup.IsPiSubgroup π (opiCoreInG π H) := by
  intro r hr
  rw [card_opiCoreInG] at hr
  exact Ch03.oPiCore.isPiGroup π r hr

/-- A subgroup of a pi-subgroup which is also a pi-complement subgroup is trivial. -/
theorem eq_bot_of_le_of_isPiSubgroup_of_isPiSubgroup_compl [Finite G] {π : Set ℕ}
    {H N : Subgroup G} (hNH : N ≤ H) (hHpi : Subgroup.IsPiSubgroup π H)
    (hNpic : Subgroup.IsPiSubgroup πᶜ N) :
    N = ⊥ := by
  apply Subgroup.card_eq_one.mp
  have hEmpty : (Nat.card ↥N).primeFactors = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro r hr
    have hrH : r ∈ (Nat.card ↥H).primeFactors :=
      Nat.mem_primeFactors.mpr
        ⟨(Nat.mem_primeFactors.mp hr).1,
          (Nat.mem_primeFactors.mp hr).2.1.trans (Subgroup.card_dvd_of_le hNH),
          Nat.card_pos.ne'⟩
    have hr_not_pi : r ∉ π := by
      simpa using hNpic r hr
    exact hr_not_pi (hHpi r hrH)
  rcases Nat.primeFactors_eq_empty.mp hEmpty with hzero | hone
  · exact False.elim (Nat.card_pos.ne' hzero)
  · exact hone

/-- A `π`-subgroup and a `π`-complement subgroup intersect trivially. -/
theorem inf_eq_bot_of_isPiSubgroup_of_isPiSubgroup_compl [Finite G] {π : Set ℕ}
    {H K : Subgroup G} (hHpi : Subgroup.IsPiSubgroup π H)
    (hKpi : Subgroup.IsPiSubgroup πᶜ K) :
    H ⊓ K = ⊥ := by
  refine eq_bot_of_le_of_isPiSubgroup_of_isPiSubgroup_compl inf_le_left hHpi ?_
  intro r hr
  exact hKpi r
    (Nat.primeFactors_mono (Subgroup.card_dvd_of_le inf_le_right) Nat.card_pos.ne' hr)

/-- If H is a pi-subgroup, then its ambient pi-complement core is trivial. -/
theorem opiCoreInG_compl_eq_bot_of_isPiSubgroup [Finite G] {π : Set ℕ} {H : Subgroup G}
    (hHpi : Subgroup.IsPiSubgroup π H) :
    opiCoreInG πᶜ H = ⊥ :=
  eq_bot_of_le_of_isPiSubgroup_of_isPiSubgroup_compl
    (opiCoreInG_le πᶜ H) hHpi (isPiSubgroup_opiCoreInG πᶜ H)

/-- The orders of a pi-subgroup and a pi-complement subgroup are coprime. -/
theorem coprime_card_of_isPiSubgroup_of_isPiSubgroup_compl [Finite G]
    {π : Set ℕ} {H K : Subgroup G} (hHpi : Subgroup.IsPiSubgroup π H)
    (hKpi : Subgroup.IsPiSubgroup πᶜ K) :
    Nat.Coprime (Nat.card ↥H) (Nat.card ↥K) :=
  OddOrder.Isaacs.Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl
    (π := π) Nat.card_pos.ne' Nat.card_pos.ne' hHpi hKpi

/-- If an element lies in a pi-subgroup and its cyclic subgroup is a pi-complement
subgroup, then the element is trivial. -/
theorem eq_one_of_mem_of_isPiSubgroup_of_zpowers_isPiSubgroup_compl [Finite G]
    {π : Set ℕ} {H : Subgroup G} (hHpi : Subgroup.IsPiSubgroup π H)
    {x : G} (hxH : x ∈ H) (hxpi : Subgroup.IsPiSubgroup πᶜ (Subgroup.zpowers x)) :
    x = 1 := by
  have hZle : Subgroup.zpowers x ≤ H := Subgroup.zpowers_le.mpr hxH
  have hZbot : Subgroup.zpowers x = ⊥ :=
    eq_bot_of_le_of_isPiSubgroup_of_isPiSubgroup_compl hZle hHpi hxpi
  have hxZ : x ∈ Subgroup.zpowers x := Subgroup.mem_zpowers x
  rw [hZbot] at hxZ
  exact Subgroup.mem_bot.mp hxZ

/-- A finite subgroup is a pi-subgroup if every element whose cyclic subgroup is a
pi-complement subgroup is trivial. -/
theorem isPiSubgroup_of_forall_zpowers_isPiSubgroup_compl_eq_one [Finite G]
    {π : Set ℕ} {H : Subgroup G}
    (htriv : ∀ x : G, x ∈ H → Subgroup.IsPiSubgroup πᶜ (Subgroup.zpowers x) → x = 1) :
    Subgroup.IsPiSubgroup π H := by
  intro q hq
  by_contra hq_not_pi
  have : Fact q.Prime := ⟨Nat.prime_of_mem_primeFactors hq⟩
  obtain ⟨x, hx_order⟩ :=
    exists_prime_orderOf_dvd_card' (G := ↥H) q (Nat.mem_primeFactors.mp hq).2.1
  have hxH : (x : G) ∈ H := x.2
  have hZpi : Subgroup.IsPiSubgroup πᶜ (Subgroup.zpowers (x : G)) := by
    intro r hr
    have hZcard : Nat.card ↥(Subgroup.zpowers (x : G)) = q := by
      rw [Nat.card_zpowers]
      exact (orderOf_injective H.subtype (Subgroup.subtype_injective H) x).trans hx_order
    have hrq : r = q := by
      rw [hZcard, Nat.Prime.primeFactors (Fact.out : q.Prime), Finset.mem_singleton] at hr
      exact hr
    rw [hrq]
    simpa using hq_not_pi
  have hx_one : (x : G) = 1 := htriv (x : G) hxH hZpi
  have hx_sub_one : x = 1 := Subtype.ext hx_one
  have hq_one : q = 1 := by
    rw [← hx_order, hx_sub_one, orderOf_one]
  exact (Fact.out : q.Prime).ne_one hq_one

/-- A q-group is a singleton pi-subgroup (`isPiSubgroup_of_isPGroup_of_mem` at `π = {q}`;
kept as a named corollary for its 19 call sites, issue 9130). -/
theorem isPiSubgroup_singleton_of_isPGroup [Finite G] {q : ℕ} [Fact q.Prime]
    {H : Subgroup G} (hH : IsPGroup q ↥H) : Subgroup.IsPiSubgroup {q} H :=
  Subgroup.isPiSubgroup_of_isPGroup_of_mem hH rfl

/-- A `{q}`-subgroup is a `q`-group. -/
theorem isPGroup_of_isPiSubgroup_singleton [Finite G] {q : ℕ} [Fact q.Prime]
    {H : Subgroup G} (hH : Subgroup.IsPiSubgroup {q} H) : IsPGroup q ↥H :=
  IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne'
    (fun {d} hd hdvd => Set.mem_singleton_iff.mp
      (hH d (Nat.mem_primeFactors.mpr ⟨hd, hdvd, Nat.card_pos.ne'⟩))))

/-- `O_q(H)` in the ambient group is a `q`-group. -/
theorem isPGroup_opiCoreInG_singleton [Finite G] {q : ℕ} [Fact q.Prime]
    (H : Subgroup G) : IsPGroup q ↥(opiCoreInG ({q} : Set ℕ) H) :=
  isPGroup_of_isPiSubgroup_singleton (isPiSubgroup_opiCoreInG ({q} : Set ℕ) H)

/-- If `N ≤ H` is normal in `H` and is a `π`-subgroup, then it lies in the
ambient realization of `O_π(H)`. -/
theorem le_opiCoreInG_of_normal_of_isPiSubgroup {π : Set ℕ} {H N : Subgroup G}
    (hNH : N ≤ H) (hNnorm : (N.subgroupOf H).Normal)
    (hNpi : Subgroup.IsPiSubgroup π N) :
    N ≤ opiCoreInG π H := by
  have := hNnorm
  have hNpi_sub : Ch03.Subgroup.IsPiGroup π (N.subgroupOf H) := by
    intro r hr
    refine hNpi r ?_
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNH).toEquiv] at hr
  calc N = (N.subgroupOf H).map H.subtype :=
      (Subgroup.map_subgroupOf_eq_of_le hNH).symm
    _ ≤ (Ch03.oPiCore π ↥H).map H.subtype :=
        Subgroup.map_mono (Ch03.Subgroup.IsPiGroup.le_oPiCore hNpi_sub)
    _ = opiCoreInG π H := rfl

/-- **`H` normalizes `O_π(H)`** (in the ambient group): the `π`-core is characteristic
in `↥H`, so conjugation by an element of `H` (which restricts to an automorphism of
`↥H`) fixes its image in `G`. -/
theorem le_normalizer_opiCoreInG (π : Set ℕ) (H : Subgroup G) :
    H ≤ Subgroup.normalizer (opiCoreInG π H) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have hfix := Subgroup.characteristic_iff_comap_eq.mp
    (Ch03.oPiCore.characteristic π ↥H) (MulAut.conj (⟨x, hx⟩ : ↥H))
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨MulAut.conj (⟨x, hx⟩ : ↥H) z, ?_, rfl⟩
    have h1 : z ∈ (Ch03.oPiCore π ↥H).comap
        (MulAut.conj (⟨x, hx⟩ : ↥H)).toMonoidHom := by
      rw [hfix]
      exact hz
    exact Subgroup.mem_comap.mp h1
  · intro hy
    obtain ⟨z, hz, hz_eq⟩ := hy
    have hy_mem : y ∈ H := by
      have hyH : x * y * x⁻¹ ∈ H := hz_eq ▸ z.2
      have h1 : x⁻¹ * (x * y * x⁻¹) * x = y := by group
      rw [← h1]
      exact H.mul_mem (H.mul_mem (H.inv_mem hx) hyH) hx
    have hzy : z = MulAut.conj (⟨x, hx⟩ : ↥H) (⟨y, hy_mem⟩ : ↥H) := by
      apply Subtype.ext
      simpa [MulAut.conj_apply] using hz_eq
    have h2 : (⟨y, hy_mem⟩ : ↥H) ∈ (Ch03.oPiCore π ↥H).comap
        (MulAut.conj (⟨x, hx⟩ : ↥H)).toMonoidHom := by
      rw [Subgroup.mem_comap]
      rw [hzy] at hz
      exact hz
    rw [hfix] at h2
    exact ⟨⟨y, hy_mem⟩, h2, rfl⟩

/-- Any subgroup normalizing `H` also normalizes the ambient realization of `O_π(H)`. -/
theorem le_normalizer_opiCoreInG_of_le_normalizer (π : Set ℕ) {A H : Subgroup G}
    (hAH : A ≤ Subgroup.normalizer (H : Set G)) :
    A ≤ Subgroup.normalizer (opiCoreInG π H) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have hxH : x ∈ Subgroup.normalizer (H : Set G) := hAH hx
  let ψ : MulAut ↥H := H.normalizerMonoidHom ⟨x, hxH⟩
  have hfix := Subgroup.characteristic_iff_comap_eq.mp
    (Ch03.oPiCore.characteristic π ↥H) ψ
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨ψ z, ?_, ?_⟩
    · have hzCore : z ∈ (Ch03.oPiCore π ↥H).comap ψ.toMonoidHom := by
        rw [hfix]
        exact hz
      exact Subgroup.mem_comap.mp hzCore
    · change ↑(ψ z) = x * ↑z * x⁻¹
      rfl
  · intro hy
    obtain ⟨z, hz, hz_eq⟩ := hy
    have hyH : y ∈ H :=
      (Subgroup.mem_normalizer_iff.mp hxH y).mpr (hz_eq ▸ z.2)
    have hzy : z = (MulEquiv.toMonoidHom ψ) ⟨y, hyH⟩ := by
      apply Subtype.ext
      change (z : G) = x * y * x⁻¹
      exact hz_eq
    have hyCore : (⟨y, hyH⟩ : ↥H) ∈ (Ch03.oPiCore π ↥H).comap ψ.toMonoidHom := by
      rw [Subgroup.mem_comap]
      rw [← hzy]
      exact hz
    rw [hfix] at hyCore
    exact ⟨⟨y, hyH⟩, hyCore, rfl⟩

/-- If `H` is normal in the ambient group, then the ambient realization of `O_π(H)`
is normal as well. -/
theorem opiCoreInG_normal (π : Set ℕ) {H : Subgroup G} [H.Normal] :
    (opiCoreInG π H).Normal := by
  rw [← Subgroup.normalizer_eq_top_iff]
  apply eq_top_iff.mpr
  have htop_le_norm_H : (⊤ : Subgroup G) ≤ Subgroup.normalizer (H : Set G) := by
    rw [Subgroup.normalizer_eq_top]
  exact le_normalizer_opiCoreInG_of_le_normalizer π htop_le_norm_H

/-- **A self-normalizing `p`-subgroup of a Sylow overgroup is the whole Sylow.**
If a subgroup `P ≤ Q` of a Sylow `p`-subgroup `Q` of `G` has the property that every element of `Q`
normalizing `P` already lies in `P` (`P.normalizer ⊓ Q ≤ P`), then `P = Q`.

This is the normalizer-growth half of Sylow theory: `Q` is a `p`-group, hence nilpotent, hence
satisfies the normalizer condition; the hypothesis says `P.subgroupOf Q` is self-normalizing in
`↥Q` (via `subgroupOf_normalizer_eq`), and a self-normalizing subgroup of a group with the
normalizer condition is the whole group, so `P.subgroupOf Q = ⊤`, i.e. `Q ≤ P`.

The intended use: a `p`-subgroup `P` with `N_G(P) = L` such that every `p`-element of `L` lies in
`P` (e.g. `P` the unique normal Sylow `p`-subgroup of `L`) is itself Sylow in `G` — take a Sylow
overgroup `Q ⊇ P`, and `N_G(P) ⊓ Q = L ⊓ Q ≤ P` because `Q`-elements are `p`-elements. -/
theorem sylow_coe_eq_of_normalizer_inf_le [Finite G] {p : ℕ} [Fact p.Prime]
    {Q : Sylow p G} {P : Subgroup G} (hPQ : P ≤ (Q : Subgroup G))
    (hle : Subgroup.normalizer P ⊓ (Q : Subgroup G) ≤ P) :
    (Q : Subgroup G) = P := by
  have : Group.IsNilpotent ↥(Q : Subgroup G) := Q.isPGroup'.isNilpotent
  have hnc : NormalizerCondition ↥(Q : Subgroup G) := Group.normalizerCondition_of_isNilpotent
  -- `P.subgroupOf Q` is self-normalizing in `↥Q`.
  have hself : Subgroup.normalizer (P.subgroupOf (Q : Subgroup G)) =
      P.subgroupOf (Q : Subgroup G) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hPQ]
    refine le_antisymm (fun x hx => ?_) (fun x hx => ?_) <;>
      rw [Subgroup.mem_subgroupOf] at hx ⊢
    · exact hle ⟨hx, x.2⟩
    · exact P.le_normalizer hx
  have htop : P.subgroupOf (Q : Subgroup G) = ⊤ :=
    (normalizerCondition_iff_only_full_group_self_normalizing.mp hnc) _ hself
  exact le_antisymm (Subgroup.subgroupOf_eq_top.mp htop) hPQ

open Subgroup in
/-- **`H ⊔ C` is normal when `H ◁ G`, `C ◁ U`, and `G = H ⊔ U`.**  In a group generated by a normal
subgroup `H` and a subgroup `U` (`H ⊔ U = ⊤`), the join `H ⊔ C` of `H` with any `U`-normal subgroup
`C ≤ U` is normal in `G`.  This is the standard "`H ⋊ C ◁ H ⋊ U`" fact:

* `H` normalizes `H ⊔ C`: for `h ∈ H`, `c ∈ C`, `h c h⁻¹ = [h,c]·c` with `[h,c] ∈ H` (`H ◁ G`), so
  `h c h⁻¹ ∈ H·C`;
* `U` normalizes `H ⊔ C`: for `u ∈ U`, `u H u⁻¹ = H` (`H ◁ G`) and `u C u⁻¹ = C` (`C ◁ U`).

Since `H ⊔ U = ⊤`, all of `G` normalizes `H ⊔ C`.  This is the (9.9.a) normality `HC ◁ HU`, with
`C = C_U(H̄)` the kernel of the `U`-action on the chief factor (automatically `◁ U`). -/
theorem sup_normal_of_normal_left_of_normal_subgroupOf {H U C : Subgroup G} [hH : H.Normal]
    (hCU : C ≤ U) [hC : (C.subgroupOf U).Normal] (hsup : H ⊔ U = ⊤) :
    (H ⊔ C).Normal := by
  -- `C ◁ U`, read as a conjugation fact in `G`.
  have hConjU : ∀ u ∈ U, ∀ c ∈ C, u * c * u⁻¹ ∈ C := by
    intro u hu c hc
    have hmem : (⟨c, hCU hc⟩ : ↥U) ∈ C.subgroupOf U := by rw [Subgroup.mem_subgroupOf]; exact hc
    have hconj := hC.conj_mem ⟨c, hCU hc⟩ hmem ⟨u, hu⟩
    rw [Subgroup.mem_subgroupOf] at hconj
    simpa using hconj
  -- Conjugating `c ∈ C` by `h ∈ H` lands in `H ⊔ C` (`= [h,c]·c`, `[h,c] ∈ H` as `H ◁ G`).
  have hConjH : ∀ h ∈ H, ∀ c ∈ C, h * c * h⁻¹ ∈ H ⊔ C := by
    intro h hh c hc
    have hcomm : h * c * h⁻¹ * c⁻¹ ∈ H := by
      have h2 : h * (c * h⁻¹ * c⁻¹) ∈ H := mul_mem hh (hH.conj_mem h⁻¹ (inv_mem hh) c)
      rwa [show h * (c * h⁻¹ * c⁻¹) = h * c * h⁻¹ * c⁻¹ by group] at h2
    rw [show h * c * h⁻¹ = (h * c * h⁻¹ * c⁻¹) * c by group]
    exact mul_mem (Subgroup.mem_sup_left hcomm) (Subgroup.mem_sup_right hc)
  rw [← normalizer_eq_top_iff, eq_top_iff, ← hsup, sup_le_iff]
  refine ⟨fun h hh => ?_, fun u hu => ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    have key : ∀ h ∈ H, ∀ n ∈ H ⊔ C, h * n * h⁻¹ ∈ H ⊔ C := by
      intro h hh n hn
      rw [Subgroup.mem_sup_of_normal_left] at hn
      obtain ⟨a, ha, b, hb, rfl⟩ := hn
      rw [show h * (a * b) * h⁻¹ = (h * a * h⁻¹) * (h * b * h⁻¹) by group]
      exact mul_mem (Subgroup.mem_sup_left (hH.conj_mem a ha h)) (hConjH h hh b hb)
    intro n
    refine ⟨key h hh n, fun hn => ?_⟩
    have := key h⁻¹ (inv_mem hh) _ hn
    rwa [show h⁻¹ * (h * n * h⁻¹) * h⁻¹⁻¹ = n by group] at this
  · rw [Subgroup.mem_normalizer_iff]
    have key : ∀ u ∈ U, ∀ n ∈ H ⊔ C, u * n * u⁻¹ ∈ H ⊔ C := by
      intro u hu n hn
      rw [Subgroup.mem_sup_of_normal_left] at hn
      obtain ⟨a, ha, b, hb, rfl⟩ := hn
      rw [show u * (a * b) * u⁻¹ = (u * a * u⁻¹) * (u * b * u⁻¹) by group]
      exact mul_mem (Subgroup.mem_sup_left (hH.conj_mem a ha u))
        (Subgroup.mem_sup_right (hConjU u hu b hb))
    intro n
    refine ⟨key u hu n, fun hn => ?_⟩
    have := key u⁻¹ (inv_mem hu) _ hn
    rwa [show u⁻¹ * (u * n * u⁻¹) * u⁻¹⁻¹ = n by group] at this

/-- `N ⊴ W` の characteristic 部分群 `L : Subgroup ↥N` は, `↥N` から `W` へ押し出すと `W` で正規。
共役自己同型 `MulAut.conjNormal w : MulAut ↥N` (`N ⊴ W` ゆえ各 `w ∈ W` の共役が `↥N` の自己同型に
制限) が `L` を固定する (`characteristic_iff_map_eq`)。 -/
theorem normal_map_subtype_of_characteristic {W : Type*} [Group W] {N : Subgroup W} [N.Normal]
    {L : Subgroup ↥N} (hL : L.Characteristic) : (L.map N.subtype).Normal := by
  refine ⟨fun a ha w => ?_⟩
  obtain ⟨⟨a', ha'N⟩, ha'L, rfl⟩ := ha
  have hmap : L.map (MulAut.conjNormal w).toMonoidHom = L :=
    (Subgroup.characteristic_iff_map_eq.mp hL) (MulAut.conjNormal w)
  have hmem : (MulAut.conjNormal w) ⟨a', ha'N⟩ ∈ L := by
    rw [← hmap]; exact Subgroup.mem_map_of_mem _ ha'L
  exact ⟨(MulAut.conjNormal w) ⟨a', ha'N⟩, hmem, MulAut.conjNormal_apply w ⟨a', ha'N⟩⟩

end OddOrder.GroupTheory


