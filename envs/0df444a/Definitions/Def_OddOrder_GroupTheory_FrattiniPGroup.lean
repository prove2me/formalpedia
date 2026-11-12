-- Prove2me | Definitions.Def_OddOrder_GroupTheory_FrattiniPGroup
-- name    : OddOrder_GroupTheory_FrattiniPGroup
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:46:07.227204+00:00
-- url     : https://prove2.me/theorems/f2ce5c50-ac35-44e6-802d-9ac0d5ef59f3
-- title:
--   Frattini subgroup of a finite $p$-group (Bender–Glauberman Lemma 1.7)
-- statement:
--   Formalizes parts (b), (c), (d) of Bender–Glauberman §1 Lemma 1.7 on the four basic properties of the Frattini subgroup $\Phi(R)$ of a finite $p$-group $R$ (part (a), the Frattini argument, is handled by Mathlib's `frattini_nongenerating`). Results include `IsPGroup.pow_mem_frattini` ($x^p\in\Phi(R)$), `IsPGroup.commutator_mem_frattini` ($[x,y]\in\Phi(R)$) and `IsPGroup.quotient_frattini_isElementaryAbelian` ($R/\Phi(R)$ is elementary abelian).
--
--   The one declaration is `quotient_subgroup_dichotomy` (coatom correspondence: if $M$ is a maximal normal subgroup, the subgroups of $R/M$ are exactly $\bot$ and $\top$).
--
--   The bundle also proves 8 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/FrattiniPGroup.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/FrattiniPGroup.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_ElementaryAbelian
import Mathlib.GroupTheory.Frattini
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Algebra.Group.Commutator
import Mathlib.Algebra.Group.Subgroup.Order

open scoped commutatorElement

open scoped IsMulCommutative

namespace OddOrder.GroupTheory

namespace IsPGroup

variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [Group R] [Finite R]

/-- For a finite p-group, every maximal subgroup is normal (from finite nilpotent TFAE). -/
lemma _root_.IsCoatom.normal_of_isPGroup
    (hR : IsPGroup p R) {M : Subgroup R} (hM : IsCoatom M) : M.Normal := by
  have : Group.IsNilpotent R := hR.isNilpotent
  exact Subgroup.NormalizerCondition.normal_of_coatom M Group.normalizerCondition_of_isNilpotent hM

set_option linter.unusedSectionVars false in
/-- Coatom correspondence: subgroups of `R ⧸ M` are exactly `⊥` and `⊤` when `M` is a coatom. -/
private lemma quotient_subgroup_dichotomy {M : Subgroup R} (hM : IsCoatom M) [M.Normal]
    (H' : Subgroup (R ⧸ M)) : H' = ⊥ ∨ H' = ⊤ := by
  set K : Subgroup R := H'.comap (QuotientGroup.mk' M) with hK_def
  have hMleK : M ≤ K := by
    intro x hx
    change (QuotientGroup.mk' M) x ∈ H'
    have hone : (QuotientGroup.mk' M) x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    rw [hone]; exact H'.one_mem
  rcases lt_or_eq_of_le hMleK with hMlt | hMeq
  · right
    have hKtop : K = ⊤ := hM.2 K hMlt
    have hsurj := QuotientGroup.mk'_surjective M
    have hH'_eq : H' = K.map (QuotientGroup.mk' M) :=
      (Subgroup.map_comap_eq_self_of_surjective hsurj H').symm
    rw [hH'_eq, hKtop, Subgroup.map_top_of_surjective _ hsurj]
  · left
    have hmap_eq : H' = K.map (QuotientGroup.mk' M) :=
      (Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective M) H').symm
    rw [hmap_eq, ← hMeq]
    ext g
    simp only [Subgroup.mem_map, Subgroup.mem_bot]
    refine ⟨?_, fun h => ⟨1, M.one_mem, by rw [h, map_one]⟩⟩
    rintro ⟨x, hxM, rfl⟩
    exact (QuotientGroup.eq_one_iff x).mpr hxM

/-- For a finite p-group `R` and a maximal subgroup `M`, `Nat.card (R ⧸ M) = p`. -/
lemma _root_.IsCoatom.card_quotient_of_isPGroup
    (hR : IsPGroup p R) {M : Subgroup R} (hM : IsCoatom M) :
    Nat.card (R ⧸ M) = p := by
  have hMnorm : M.Normal := hM.normal_of_isPGroup hR
  have hQpgroup : IsPGroup p (R ⧸ M) := hR.to_quotient M
  have hntriv : Nontrivial (R ⧸ M) := QuotientGroup.nontrivial_iff.mpr hM.1
  -- |R⧸M| = p^n for some n ≥ 1.
  obtain ⟨n, hn_card⟩ := IsPGroup.iff_card.mp hQpgroup
  have hn_pos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · -- n = 0 ⇒ |R⧸M| = 1, but R⧸M is nontrivial
      exfalso
      have h1 : (1 : ℕ) < Nat.card (R ⧸ M) := Finite.one_lt_card_iff_nontrivial.mpr hntriv
      rw [hn_card] at h1
      simp at h1
    · exact hpos
  -- Find element y ∈ R⧸M of prime order p (Cauchy).
  have hp_dvd : p ∣ Nat.card (R ⧸ M) := by
    rw [hn_card]; exact dvd_pow_self p hn_pos.ne'
  obtain ⟨y, hy_order⟩ := exists_prime_orderOf_dvd_card' (G := R ⧸ M) p hp_dvd
  -- ⟨y⟩ ≠ ⊥ (since y ≠ 1 of order p), so ⟨y⟩ = ⊤ by dichotomy.
  have hy_ne_one : y ≠ 1 := by
    intro hy_eq
    rw [hy_eq, orderOf_one] at hy_order
    exact hp.out.one_lt.ne' hy_order.symm
  have hzpowers_ne_bot : Subgroup.zpowers y ≠ ⊥ := by
    rw [Subgroup.zpowers_ne_bot]; exact hy_ne_one
  have hzpowers_top : Subgroup.zpowers y = ⊤ :=
    (quotient_subgroup_dichotomy hM (Subgroup.zpowers y)).resolve_left hzpowers_ne_bot
  -- Hence |R⧸M| = |⟨y⟩| = orderOf y = p.
  have hcard_eq : Nat.card (R ⧸ M) = Nat.card (Subgroup.zpowers y) := by
    rw [hzpowers_top]; exact (Subgroup.card_top).symm
  rw [hcard_eq, Nat.card_zpowers, hy_order]

/-- For a finite p-group `R`, every commutator `⁅x, y⁆` lies in `Φ(R)`. -/
theorem commutator_mem_frattini
    (hR : IsPGroup p R) (x y : R) : ⁅x, y⁆ ∈ frattini R := by
  rw [frattini, Order.radical, Subgroup.mem_iInf]
  intro M
  rw [Subgroup.mem_iInf]
  intro hM
  have hMnorm : M.Normal := hM.normal_of_isPGroup hR
  -- |R⧸M| = p prime ⇒ R/M cyclic ⇒ R/M abelian (use IsCyclic.commutative instance).
  have hcard : Nat.card (R ⧸ M) = p := hM.card_quotient_of_isPGroup hR
  have : IsCyclic (R ⧸ M) := isCyclic_of_prime_card hcard
  -- Sufficient to show `(mk' M) ⁅x, y⁆ = 1`.
  suffices h : (QuotientGroup.mk' M) ⁅x, y⁆ = 1 by
    exact (QuotientGroup.eq_one_iff _).mp h
  rw [map_commutatorElement]
  exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)

/-- For a finite p-group `R`, every `p`-th power lies in `Φ(R)`. -/
theorem pow_mem_frattini
    (hR : IsPGroup p R) (x : R) : x ^ p ∈ frattini R := by
  rw [frattini, Order.radical, Subgroup.mem_iInf]
  intro M
  rw [Subgroup.mem_iInf]
  intro hM
  have hMnorm : M.Normal := hM.normal_of_isPGroup hR
  -- |R⧸M| = p, so `(x̄)^p = 1` by Lagrange.
  have hcard : Nat.card (R ⧸ M) = p := hM.card_quotient_of_isPGroup hR
  suffices h : (QuotientGroup.mk' M) (x ^ p) = 1 by
    exact (QuotientGroup.eq_one_iff _).mp h
  rw [map_pow, ← hcard]
  exact pow_card_eq_one'

/-- **BG Lemma 1.7 (b)**: For a finite p-group `R`, `R ⧸ Φ(R)` is elementary abelian. -/
theorem quotient_frattini_isElementaryAbelian
    (hR : IsPGroup p R) :
    IsElementaryAbelian p (R ⧸ frattini R) := by
  refine ⟨?_, ?_⟩
  · -- Commutative
    intro a b
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (frattini R) a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (frattini R) b
    have hcomm_mem : ⁅x, y⁆ ∈ frattini R := commutator_mem_frattini hR x y
    -- (mk' Φ) ⁅x, y⁆ = 1 ⇒ ⁅(mk' Φ) x, (mk' Φ) y⁆ = 1 ⇒ commute.
    have h : (QuotientGroup.mk' (frattini R)) ⁅x, y⁆ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hcomm_mem
    rw [map_commutatorElement] at h
    exact commutatorElement_eq_one_iff_mul_comm.mp h
  · -- `∀ x, x ^ p = 1`
    intro a
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (frattini R) a
    have hpow_mem : x ^ p ∈ frattini R := pow_mem_frattini hR x
    have h : (QuotientGroup.mk' (frattini R)) (x ^ p) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hpow_mem
    rw [map_pow] at h
    exact h

/-- **BG Lemma 1.7 (c) (⇒)**: For a finite p-group `R` with `Φ(R) = ⊥`,
`R` is elementary abelian. -/
theorem isElementaryAbelian_of_frattini_eq_bot
    (hR : IsPGroup p R) (hFrat : frattini R = ⊥) :
    IsElementaryAbelian p R := by
  refine ⟨?_, ?_⟩
  · -- Commutative: `⁅x, y⁆ ∈ Φ(R) = ⊥` ⇒ `⁅x, y⁆ = 1` ⇒ `x * y = y * x`.
    intro x y
    have h : ⁅x, y⁆ ∈ frattini R := commutator_mem_frattini hR x y
    rw [hFrat] at h
    have h_eq_one : ⁅x, y⁆ = 1 := Subgroup.mem_bot.mp h
    exact commutatorElement_eq_one_iff_mul_comm.mp h_eq_one
  · -- `∀ x, x^p ∈ Φ(R) = ⊥` ⇒ `x^p = 1`.
    intro x
    have h : x ^ p ∈ frattini R := pow_mem_frattini hR x
    rw [hFrat] at h
    exact Subgroup.mem_bot.mp h

/-- **BG Lemma 1.7 (d) (⊇ direction)**: For a finite p-group `R`,
the subgroup generated by `[R, R]` and `{x^p | x ∈ R}` lies in `Φ(R)`.

逆向き (`Φ(R) ≤ ⟨[R, R], x^p⟩`) は (c)(⇐) 経由 — 有限 elementary abelian 群の
hyperplane (complement) 構造を必要とするため別補題で扱う. -/
theorem commutator_sup_pow_closure_le_frattini
    (hR : IsPGroup p R) :
    commutator R ⊔ Subgroup.closure (Set.range (fun x : R => x ^ p)) ≤ frattini R := by
  apply sup_le
  · -- `[R, R] ≤ Φ(R)`: commutator-generators are in Φ(R) by `commutator_mem_frattini`.
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    exact commutator_mem_frattini hR x y
  · -- `closure {x^p} ≤ Φ(R)`: each generator is in Φ(R) by `pow_mem_frattini`.
    rw [Subgroup.closure_le]
    rintro _ ⟨x, rfl⟩
    exact pow_mem_frattini hR x

/-- **Burnside basis theorem (cyclic case)**: a finite group whose Frattini quotient is cyclic is
itself cyclic.  If `R/Φ(R) = ⟨ḡ⟩` with `ḡ = ḡ` the image of `g`, then `⟨g⟩ ⊔ Φ(R)` maps onto
`R/Φ(R)` and contains `ker = Φ(R)`, so it is all of `R`; `frattini_nongenerating` then upgrades
`⟨g⟩ ⊔ Φ(R) = ⊤` to `⟨g⟩ = ⊤`.

Stated for any finite group (the `p`-group hypotheses of this namespace are unused); kept here as
the natural home of the Frattini-quotient API.  Used in `IsExtraspecial.of_card_eq_prime_cube`. -/
theorem _root_.OddOrder.GroupTheory.isCyclic_of_isCyclic_quotient_frattini {G : Type*} [Group G]
    [Finite G] (h : IsCyclic (G ⧸ frattini G)) : IsCyclic G := by
  have := h
  obtain ⟨gbar, hgbar⟩ := IsCyclic.exists_generator (α := G ⧸ frattini G)
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (frattini G) gbar
  have htop : Subgroup.zpowers g ⊔ frattini G = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hgbar (QuotientGroup.mk' (frattini G) x))
    -- `hn : (mk' g) ^ n = mk' x`, so `(gⁿ)⁻¹ x ∈ ker (mk') = Φ(G)`.
    have hφ : (g ^ n)⁻¹ * x ∈ frattini G := by
      rw [← QuotientGroup.ker_mk' (N := frattini G), MonoidHom.mem_ker, map_mul, map_inv, map_zpow,
        hn, inv_mul_cancel]
    have hx : x = g ^ n * ((g ^ n)⁻¹ * x) := by group
    rw [hx]
    exact Subgroup.mul_mem_sup (Subgroup.mem_zpowers_iff.mpr ⟨n, rfl⟩) hφ
  have hgtop : Subgroup.zpowers g = ⊤ := frattini_nongenerating htop
  exact ⟨g, fun x => hgtop.ge (Subgroup.mem_top x)⟩

end IsPGroup

end OddOrder.GroupTheory


