-- Prove2me | Definitions.Def_OddOrder_GroupTheory_AInvariantComplement
-- name    : OddOrder_GroupTheory_AInvariantComplement
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:44:15.314193+00:00
-- url     : https://prove2.me/theorems/01a0efd2-18e2-4059-a33f-022c34d7d1e7
-- title:
--   Invariant Schur–Zassenhaus (complement form)
-- statement:
--   A normal Hall subgroup $N$ of a finite solvable group $G$, invariant under a coprime operator action $\varphi:A\to\mathrm{Aut}(G)$, admits a $\varphi$-invariant complement. This is the invariant-complement half of Schur–Zassenhaus; Mathlib supplies only the plain version.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 2 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/AInvariantComplement.lean

/-
Copyright (c) 2026 OddOrder contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/AInvariantComplement.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S01_Solvable

open OddOrder.Isaacs.Ch03

namespace OddOrder.GroupTheory

variable {G A : Type*} [Group G] [Finite G] [Group A] [Finite A]

/-- **Invariant Schur–Zassenhaus, complement form.**  A `φ`-invariant normal Hall subgroup `N` of a
finite solvable group has a `φ`-invariant complement `U`, provided the action is coprime to
`|G|`. -/
theorem exists_aInvariant_complement_of_normal_isHall [Group.IsSolvable G] {φ : A →* MulAut G}
    (hCop : Nat.Coprime (Nat.card A) (Nat.card G))
    {N : Subgroup G} [N.Normal] (_hN_inv : IsAInvariant φ N)
    (hN_hall : IsHallSubgroup (Nat.card ↥N).primeFactors N) :
    ∃ U : Subgroup G, Subgroup.IsComplement' N U ∧ IsAInvariant φ U := by
  classical
  set π : Set ℕ := ((Nat.card ↥N).primeFactors : Set ℕ) with hπ
  -- A `φ`-invariant Hall `π'`-subgroup `U`, from the trivial `π'`-subgroup `⊥ ≤ U`.
  obtain ⟨U, hU_hall, hU_inv, -⟩ :=
    OddOrder.BG.Ch1.S01.aInvariant_piSubgroup_le_aInvariant_hall (π := {p | p ∉ π}) hCop
      (Subgroup.IsPiGroup.bot {p | p ∉ π}) (IsAInvariant.bot φ)
  refine ⟨U, ?_, hU_inv⟩
  -- `|N|` (a `π`-number) and `|U|` (a `π'`-number) are coprime.
  have hcop_NU : Nat.Coprime (Nat.card ↥N) (Nat.card ↥U) := by
    apply Nat.coprime_of_dvd
    intro p hp hpN hpU
    exact hU_hall.1 p (Nat.mem_primeFactors.mpr ⟨hp, hpU, Nat.card_pos.ne'⟩)
      (hN_hall.1 p (Nat.mem_primeFactors.mpr ⟨hp, hpN, Nat.card_pos.ne'⟩))
  -- `[G : N]` (a `π'`-number) and `[G : U]` (a `π`-number) are coprime.
  have hcop_idx : Nat.Coprime N.index U.index := by
    apply Nat.coprime_of_dvd
    intro p hp hpN hpU
    have hpπ' : p ∉ π :=
      hN_hall.2 p (Nat.mem_primeFactors.mpr ⟨hp, hpN, Subgroup.index_ne_zero_of_finite⟩)
    have hpπ : p ∈ π := by
      by_contra hpπ
      exact hU_hall.2 p (Nat.mem_primeFactors.mpr ⟨hp, hpU, Subgroup.index_ne_zero_of_finite⟩) hpπ
    exact hpπ' hpπ
  -- `|U| = [G : N]`: both equal the `π'`-part of `|G|`.
  have hU_eq_index : Nat.card ↥U = N.index := by
    refine Nat.dvd_antisymm ?_ ?_
    · -- `|U| ∣ |N|·[G:N] = |G|`, coprime to `|N|`, so `|U| ∣ [G:N]`.
      refine (Nat.Coprime.dvd_of_dvd_mul_left hcop_NU.symm ?_)
      rw [Subgroup.card_mul_index]
      exact Subgroup.card_subgroup_dvd_card U
    · -- `[G:N] ∣ |U|·[G:U] = |G|`, coprime to `[G:U]`, so `[G:N] ∣ |U|`.
      refine (Nat.Coprime.dvd_of_dvd_mul_right hcop_idx ?_)
      rw [Subgroup.card_mul_index]
      exact Subgroup.index_dvd_card N
  -- Hence `|N|·|U| = |G|`, and with coprimality `U` is a complement of `N`.
  refine Subgroup.isComplement'_of_coprime ?_ hcop_NU
  rw [hU_eq_index, Subgroup.card_mul_index]

/-- **Ambient form of the invariant complement.**  Let `K` normalize both a subgroup `M'` (assumed
solvable) and a normal Hall subgroup `N ◁ M'`, with the action coprime (`gcd(|K|, |M'|) = 1`).  Then
`N` has a complement `U` *inside* `M'` (i.e. `N ⊔ U = M'`) that `K` normalizes.  This is the form
Peterfalvi (13.1.b) uses: `K` is the κ-Hall, `M' = S'` the derived subgroup, `N = M_F` the Fitting
kernel, and the conclusion is the semidirect factorisation `M' = M_F U` with `K ≤ N_G(U)`. -/
theorem exists_aInvariant_complement_within_normal {G : Type*} [Group G] [Finite G]
    {M' K N : Subgroup G} [Group.IsSolvable ↥M']
    (hN_le : N ≤ M') (hM'_norm_N : M' ≤ Subgroup.normalizer (N : Set G))
    (hK_norm_M' : K ≤ Subgroup.normalizer (M' : Set G))
    (hK_norm_N : K ≤ Subgroup.normalizer (N : Set G))
    (hN_hall : IsHallSubgroup (Nat.card ↥N).primeFactors (N.subgroupOf M'))
    (hCop : Nat.Coprime (Nat.card ↥K) (Nat.card ↥M')) :
    ∃ U : Subgroup G, U ≤ M' ∧ N ⊔ U = M' ∧ K ≤ Subgroup.normalizer (U : Set G) ∧
      N ⊓ U = ⊥ := by
  classical
  -- The conjugation action of `K` on `M'` (via the normalizer monoid hom).
  set φ : ↥K →* MulAut ↥M' :=
    (Subgroup.normalizerMonoidHom M').comp (Subgroup.inclusion hK_norm_M') with hφ
  -- `φ a` is conjugation by `↑a` on `↥M'`.
  have hφval : ∀ (a : ↥K) (x : ↥M'), ((φ a x : ↥M') : G) = (a : G) * (x : G) * (a : G)⁻¹ :=
    fun _ _ => rfl
  -- `N.subgroupOf M'` is normal in `↥M'` and `φ`-invariant (`K` normalizes `N`).
  have hN'_normal : (N.subgroupOf M').Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hN_le).mpr hM'_norm_N
  have hN'_inv : IsAInvariant φ (N.subgroupOf M') := by
    rw [isAInvariant_iff_smul_mem]
    intro a x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have hxN : (x : G) ∈ N := hx
    have ha : (a : G) ∈ Subgroup.normalizer (N : Set G) := hK_norm_N a.2
    rw [hφval a x]
    exact (Subgroup.mem_normalizer_iff.mp ha (x : G)).mp hxN
  -- `|N.subgroupOf M'| = |N|`, so the Hall hypothesis matches the general lemma's expectation.
  have hcardN' : Nat.card ↥(N.subgroupOf M') = Nat.card ↥N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN_le).toEquiv
  have hhall : IsHallSubgroup (Nat.card ↥(N.subgroupOf M')).primeFactors (N.subgroupOf M') := by
    rw [hcardN']; exact hN_hall
  -- Apply the invariant Schur–Zassenhaus complement.
  obtain ⟨U', hU'compl, hU'inv⟩ :=
    exists_aInvariant_complement_of_normal_isHall hCop hN'_inv hhall
  refine ⟨U'.map M'.subtype, Subgroup.map_subtype_le U', ?_, ?_, ?_⟩
  · -- `N ⊔ U'.map M'.subtype = M'`, by mapping the complement equality `N' ⊔ U' = ⊤` up to `M'`.
    have hsup : (N.subgroupOf M') ⊔ U' = ⊤ := hU'compl.sup_eq_top
    have := congrArg (Subgroup.map M'.subtype) hsup
    rwa [Subgroup.map_sup, ← MonoidHom.range_eq_map, Subgroup.range_subtype,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hN_le] at this
  · -- `K ≤ N_G(U'.map M'.subtype)`, from `φ`-invariance of `U'` and `φ a` = conjugation.
    intro k hk
    exact hU'inv.mem_normalizer_map_subtype_of_smul_val (hφval ⟨k, hk⟩)
  · -- `N ⊓ U'.map M'.subtype = ⊥`, mapping the complement disjointness `N' ⊓ U' = ⊥` up to `M'`.
    have hdisj : (N.subgroupOf M') ⊓ U' = ⊥ := disjoint_iff.mp hU'compl.disjoint
    have := congrArg (Subgroup.map M'.subtype) hdisj
    rwa [Subgroup.map_inf _ _ M'.subtype M'.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr hN_le, Subgroup.map_bot] at this

end OddOrder.GroupTheory


