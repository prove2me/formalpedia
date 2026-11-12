-- Prove2me | Definitions.Def_OddOrder_BG_Ch1_Preliminary_S04b_Thm412
-- name    : OddOrder_BG_Ch1_Preliminary_S04b_Thm412
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:54:01.825934+00:00
-- url     : https://prove2.me/theorems/bb6e80c6-5eb3-45f8-bed1-4894960a9a4d
-- title:
--   BG §4: Theorem 4.12(a) (Huppert)
-- statement:
--   Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, §4, Theorem 4.12(a) (Huppert): suppose $p$ is an odd prime, $R$ is a metacyclic $p$-group and $A$ is a $p'$-group of operators on $R$. If $[R,A]=R$ then $R$ is abelian. The operator group acts through $\phi:A\to\mathrm{Aut}\,R$ with coprime orders.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 1 supporting lemma used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch1_Preliminary/S04b_Thm412.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch1_Preliminary/S04b_Thm412.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S04_PGroupsSmallRank
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_OperatorQuotientAction
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_OperatorMaschke
import Definitions.Def_OddOrder_GroupTheory_IsMetacyclic

namespace OddOrder.BG.Ch1.S04b

open OddOrder.GroupTheory

open OddOrder.Isaacs.Ch03 (IsAInvariant)

open OddOrder.Isaacs.Ch04

open OddOrder.BG.Ch1.OperatorQuotientAction

open OddOrder.BG.Ch1_Preliminary

open OddOrder.BG.Ch1.S04

/-- **BG Theorem 4.12(a)** (Huppert). Let `p` be an odd prime, `R` a metacyclic `p`-group, and
`φ : A →* MulAut R` a coprime operator action with `[R, A] = R` (`actionCommutator φ = ⊤`).
Then `R` is abelian.

mmd L1588-1614. Because `[R, A] = R` is assumed directly, no induction on `|R|` is needed. -/
theorem isMulCommutative_of_metacyclic_actionCommutator_eq_top
    {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime] (hp_odd : Odd p)
    (hR : IsPGroup p R) (hmeta : OddOrder.GroupTheory.IsMetacyclic R)
    {A : Type*} [Group A] [Finite A] {φ : A →* MulAut R}
    (hcop : Nat.Coprime (Nat.card A) (Nat.card R))
    (hRA : OddOrder.Isaacs.Ch04.actionCommutator φ = ⊤) :
    IsMulCommutative R := by
  classical
  -- If `R` is already abelian we are done; otherwise `commutator R ≠ ⊥`.
  by_cases hab : commutator R = ⊥
  · exact (commutator_eq_bot_iff R).mp hab
  -- `R` non-cyclic (a cyclic group is abelian, contradicting `commutator R ≠ ⊥`).
  have hRcyc : ¬ IsCyclic R := by
    intro hcyc
    let := hcyc.commGroup
    exact hab (commutator_eq_bot R)
  -- ## Step 1 — construct the maximal cyclic `A`-invariant `S ⊇ R'`.
  have hcyc : IsCyclic ↥(commutator R) := hmeta.isCyclic_commutator
  obtain ⟨S, hS_inv, hS_cyc, hRprime_le, hS_max⟩ :=
    exists_maximal_isCyclic_isAInvariant_commutator_le φ hcyc
  have : IsCyclic ↥S := hS_cyc
  have hS_norm : S.Normal := OddOrder.Isaacs.Ch06.normal_of_commutator_le hRprime_le
  have := hS_norm
  -- `S ≠ ⊥` since it contains the nontrivial `commutator R`.
  have hSne : S ≠ ⊥ := fun h => hab (le_bot_iff.mp (h ▸ hRprime_le))
  have hS_nt : Nontrivial ↥S := S.nontrivial_iff_ne_bot.mpr hSne
  -- `R` itself is nontrivial (it has the nontrivial subgroup `S`).
  have hR_nt : Nontrivial R := by
    obtain ⟨x, y, hxy⟩ := hS_nt
    exact ⟨x, y, fun h => hxy (Subtype.ext h)⟩
  -- ## Step 2 — `S ⊆ Z(R)` (output of the cyclic-centralizer lemma, not an input).
  have hSZ : S ≤ Subgroup.center R :=
    isCyclic_le_center_of_actionCommutator_eq_top hS_norm hS_inv hRA
  -- ## Step 3 — Maschke integration ⇒ `R/S` cyclic.
  -- (3a) `R/S` is abelian (since `R' ⊆ S`).
  have hQab : ∀ x y : R ⧸ S, x * y = y * x :=
    isMulCommutative_iff.mp
      ((Subgroup.Normal.quotient_commutative_iff_commutator_le (N := S)).mpr hRprime_le)
  -- (3b) `p ∣ |R|` (nontrivial `p`-group).
  have hpR : p ∣ Nat.card R := by
    rcases hR.card_eq_or_dvd with h1 | hd
    · exact absurd h1 (by simpa using (Finite.one_lt_card (α := R)).ne')
    · exact hd
  -- (3c) `Ω₁(R)` is `A`-invariant (characteristic).
  have hWinv : IsAInvariant φ (Omega R p 1) := IsAInvariant.of_characteristic φ
  -- (3d) the image of `Ω₁(R)` under `mk' S` lands in `Ω₁(R/S)`.
  have hWΩ : (Omega R p 1).map (QuotientGroup.mk' S) ≤ Omega (R ⧸ S) p 1 := by
    rw [Subgroup.map_le_iff_le_comap, Omega, Subgroup.closure_le]
    rintro g (hg : g ^ (p ^ 1) = 1)
    change g ∈ Subgroup.comap (QuotientGroup.mk' S) (Omega (R ⧸ S) p 1)
    rw [Subgroup.mem_comap]
    refine Omega.mem_of_pow_eq_one ?_
    rw [← map_pow, hg, map_one]
  -- (3e) Maschke complement `X` to `Ω₁(R)·S/S` inside `Ω₁(R/S)`.
  obtain ⟨X, hSX, hXinv, _hXΩ, hXinf, hXsup⟩ :=
    exists_aInvariant_complement_in_omega1_quotient hpR hcop hS_inv hQab hWinv hWΩ
  -- (3g) `Ω₁(R)` elementary abelian of order `p²` (Lemma 4.10, non-cyclic case).
  obtain ⟨hΩR_ea, hΩR_card⟩ := isElementaryAbelian_omega1_of_isMetacyclic hR hp_odd hmeta hRcyc
  -- every element of `Ω₁(R)` is `p`-torsion.
  have hΩR_pow : ∀ g : R, g ∈ Omega R p 1 → g ^ p = 1 := by
    intro g hg
    have := hΩR_ea.pow_eq_one ⟨g, hg⟩
    simpa using congrArg (Subtype.val) this
  -- `|Ω₁(S)| = p`, and its image under `S.subtype` (a subgroup of `R`) has order `p`.
  have hΩS_card : Nat.card (Omega ↥S p 1) = p :=
    card_omega1_eq_prime_of_isCyclic (hR.to_subgroup S)
  have hΩSmap_card : Nat.card ((Omega ↥S p 1).map S.subtype) = p := by
    rw [Subgroup.card_map_of_injective S.subtype_injective, hΩS_card]
  -- `(Ω₁ ↥S).map subtype = S ⊓ Ω₁(R)` (both directions via `p`-torsion in elementary abelian).
  have hΩSmap_le : (Omega ↥S p 1).map S.subtype ≤ S ⊓ Omega R p 1 := by
    rw [Subgroup.map_le_iff_le_comap, Omega, Subgroup.closure_le]
    rintro ⟨g, hgS⟩ (hg : (⟨g, hgS⟩ : ↥S) ^ (p ^ 1) = 1)
    change (⟨g, hgS⟩ : ↥S) ∈ Subgroup.comap S.subtype (S ⊓ Omega R p 1)
    rw [Subgroup.mem_comap]
    have hgp : g ^ p = 1 := by
      have := congrArg (Subgroup.subtype S) hg
      rwa [map_pow, pow_one, map_one] at this
    exact ⟨hgS, Omega.mem_of_pow_eq_one (by rw [pow_one]; exact hgp)⟩
  have hinter_le_map : S ⊓ Omega R p 1 ≤ (Omega ↥S p 1).map S.subtype := by
    rintro x ⟨hxS, hxΩ⟩
    rw [Subgroup.mem_map]
    refine ⟨⟨x, hxS⟩, ?_, rfl⟩
    refine Omega.mem_of_pow_eq_one ?_
    rw [pow_one]
    ext
    rw [SubmonoidClass.coe_pow, Subgroup.coe_mk, OneMemClass.coe_one]
    exact hΩR_pow x hxΩ
  have hinter_eq_map : S ⊓ Omega R p 1 = (Omega ↥S p 1).map S.subtype :=
    le_antisymm hinter_le_map hΩSmap_le
  have hinter_card : Nat.card ↥(S ⊓ Omega R p 1) = p := by
    rw [hinter_eq_map, hΩSmap_card]
  -- ### `X ⊓ Ω₁(R) ≤ S` from the trivial intersection of the `mk'`-images.
  have hXinter_le_S : X ⊓ Omega R p 1 ≤ S := by
    intro x ⟨hxX, hxΩ⟩
    -- `mk' x` lies in both `X.map mk'` and `Ω₁(R).map mk'`, hence in `⊥`.
    have hmem_X : (QuotientGroup.mk' S) x ∈ X.map (QuotientGroup.mk' S) :=
      Subgroup.mem_map_of_mem _ hxX
    have hmem_W : (QuotientGroup.mk' S) x ∈ (Omega R p 1).map (QuotientGroup.mk' S) :=
      Subgroup.mem_map_of_mem _ hxΩ
    have hbot : (QuotientGroup.mk' S) x ∈
        (X.map (QuotientGroup.mk' S) ⊓ (Omega R p 1).map (QuotientGroup.mk' S)) :=
      Subgroup.mem_inf.mpr ⟨hmem_X, hmem_W⟩
    rw [hXinf, Subgroup.mem_bot] at hbot
    -- `mk' x = 1` ⇒ `x ∈ ker (mk' S) = S`.
    rwa [← QuotientGroup.ker_mk' S, MonoidHom.mem_ker]
  -- ### `|Ω₁(X)| ≤ p`, so `X` is cyclic.
  have hΩXmap_le : (Omega ↥X p 1).map X.subtype ≤ S ⊓ Omega R p 1 := by
    rw [Subgroup.map_le_iff_le_comap, Omega, Subgroup.closure_le]
    rintro ⟨g, hgX⟩ (hg : (⟨g, hgX⟩ : ↥X) ^ (p ^ 1) = 1)
    change (⟨g, hgX⟩ : ↥X) ∈ Subgroup.comap X.subtype (S ⊓ Omega R p 1)
    rw [Subgroup.mem_comap]
    have hgp : g ^ p = 1 := by
      have := congrArg (Subgroup.subtype X) hg
      rwa [map_pow, pow_one, map_one] at this
    have hgΩ : g ∈ Omega R p 1 := Omega.mem_of_pow_eq_one (by rw [pow_one]; exact hgp)
    exact ⟨hXinter_le_S ⟨hgX, hgΩ⟩, hgΩ⟩
  have hΩX_card : Nat.card (Omega ↥X p 1) ≤ p := by
    calc Nat.card (Omega ↥X p 1)
        = Nat.card ((Omega ↥X p 1).map X.subtype) :=
          (Subgroup.card_map_of_injective X.subtype_injective).symm
      _ ≤ Nat.card ↥(S ⊓ Omega R p 1) := Subgroup.card_le_of_le hΩXmap_le
      _ = p := hinter_card
  have hX_cyc : IsCyclic ↥X := isCyclic_of_card_omega1_le_prime (hR.to_subgroup X) hp_odd hΩX_card
  -- ### maximality of `S` forces `X = S`.
  have hXS : S = X := hS_max X hXinv hX_cyc (le_trans hRprime_le hSX) hSX
  -- (3l) `Ω₁(R/S) = Ω₁(R)·S/S`.
  have hΩRS_eq : Omega (R ⧸ S) p 1 = (Omega R p 1).map (QuotientGroup.mk' S) := by
    have := hXsup
    rw [← hXS, QuotientGroup.map_mk'_self, bot_sup_eq] at this
    exact this.symm
  -- (3m) `|Ω₁(R/S)| = p` via the first isomorphism theorem for `mk' ∘ subtype`.
  have hΩRS_card : Nat.card (Omega (R ⧸ S) p 1) = p := by
    -- the hom `g : Ω₁(R) → R/S` whose range is `Ω₁(R).map mk'` and kernel `S ⊓ Ω₁(R)`.
    set g : ↥(Omega R p 1) →* R ⧸ S :=
      (QuotientGroup.mk' S).comp (Omega R p 1).subtype with hg_def
    -- range of `g` = image of `Ω₁(R)` under `mk' S`.
    have hrange : g.range = (Omega R p 1).map (QuotientGroup.mk' S) := by
      rw [hg_def, MonoidHom.range_comp, Subgroup.range_subtype]
    -- kernel of `g` = `S.subgroupOf (Ω₁(R))`, of cardinality `|S ⊓ Ω₁(R)| = p`.
    have hker : g.ker = S.subgroupOf (Omega R p 1) := by
      ext x
      simp only [hg_def, MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype,
        Subgroup.mem_subgroupOf]
      rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk' S]
    have hker_card : Nat.card g.ker = p := by
      rw [hker,
        ← Subgroup.card_map_of_injective (K := S.subgroupOf (Omega R p 1))
            (f := (Omega R p 1).subtype) (Omega R p 1).subtype_injective,
        Subgroup.subgroupOf_map_subtype]
      exact hinter_card
    -- first isomorphism theorem: `|Ω₁(R)| = |range g| · |ker g|`.
    have hcard_eq : Nat.card ↥(Omega R p 1) = Nat.card g.range * Nat.card g.ker := by
      have hiso : (↥(Omega R p 1) ⧸ g.ker) ≃* g.range := QuotientGroup.quotientKerEquivRange g
      have h1 : Nat.card ↥(Omega R p 1) =
          Nat.card (↥(Omega R p 1) ⧸ g.ker) * Nat.card g.ker :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup g.ker
      rw [h1, Nat.card_congr hiso.toEquiv]
    -- solve `|range g| · p = p²` for `|range g| = p`.
    have hkey : Nat.card g.range * p = p * p := by
      have : Nat.card g.range * p = Nat.card ↥(Omega R p 1) := by
        rw [hcard_eq, hker_card]
      rw [this, hΩR_card]; ring
    have hp_pos : 0 < p := (Fact.out : p.Prime).pos
    have hrng : Nat.card g.range = p := Nat.eq_of_mul_eq_mul_right hp_pos hkey
    rw [hΩRS_eq, ← hrange]; exact hrng
  have hΩRS_le : Nat.card (Omega (R ⧸ S) p 1) ≤ p := le_of_eq hΩRS_card
  -- (3n) `R/S` is cyclic.
  have hRS_cyc : IsCyclic (R ⧸ S) :=
    isCyclic_of_card_omega1_le_prime (hR.to_quotient S) hp_odd hΩRS_le
  -- ## Step 4 — `R/Z(R)` cyclic ⇒ `R` abelian (Lemma 4.1).
  -- `R/Z(R)` is a quotient of the cyclic `R/S` (since `S ≤ Z(R)`), hence cyclic.
  have : IsCyclic (R ⧸ S) := hRS_cyc
  have hSZ' : S ≤ (Subgroup.center R).comap (MonoidHom.id R) := by
    rw [Subgroup.comap_id]; exact hSZ
  -- the induced surjection `R/S →* R/Z(R)`.
  have hmap_surj : Function.Surjective
      (QuotientGroup.map S (Subgroup.center R) (MonoidHom.id R) hSZ') := by
    intro y
    obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨QuotientGroup.mk r, by rw [QuotientGroup.map_mk]; rfl⟩
  have hRZ_cyc : IsCyclic (R ⧸ Subgroup.center R) :=
    isCyclic_of_surjective _ hmap_surj
  let : IsCyclic (R ⧸ Subgroup.center R) := hRZ_cyc
  exact MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center
    (QuotientGroup.mk' (Subgroup.center R))
    (le_of_eq (QuotientGroup.ker_mk' (Subgroup.center R)))

end OddOrder.BG.Ch1.S04b


