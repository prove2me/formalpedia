-- Prove2me | Definitions.Def_OddOrder_BG_Ch1_Preliminary_S01_FrattiniBurnside
-- name    : OddOrder_BG_Ch1_Preliminary_S01_FrattiniBurnside
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:37:46.210974+00:00
-- url     : https://prove2.me/theorems/6104c47d-cc53-437a-b3fc-470cf60ff120
-- title:
--   Bender–Glauberman §1: Frattini and Burnside machinery for Hall subgroups
-- statement:
--   A part of the Bender–Glauberman §1 formalization (solvable groups, Frattini argument, Burnside), containing Hall-subgroup actions and invariant-subgroup transfer lemmas for quotients under an automorphic action.
--
--   Main definitions: `HallSubgroups` (the type of Hall subgroups), `hallSubgroupsMulAutAction` and `hallSubgroupsConjAction` (the actions of automorphisms and of $G$ by conjugation), and lemmas such as `isAInvariant_map_mk'`, `isAInvariant_comap_mk'` (invariance of images and preimages under quotient maps) and `quotient_hall_preimage_frame`.
--
--   The bundle also proves 30 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch1_Preliminary/S01_FrattiniBurnside.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch1_Preliminary/S01_FrattiniBurnside.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Isaacs_Ch01_Sylow_Main
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S01_SolvableBasics
import Definitions.Def_OddOrder_Isaacs_Ch03_SplitExtensions_Main
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_CommutatorBasics
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ThreeSubgroupsCoprime
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_BaerTrick
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ChainNilpotent
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_ForwardFromCh03
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ThreeSubgroups
import Definitions.Def_OddOrder_GroupTheory_ChiefFactor
import Definitions.Def_OddOrder_GroupTheory_FittingSelfCentralizing
import Definitions.Def_OddOrder_GroupTheory_FrattiniPGroup
import Definitions.Def_OddOrder_GroupTheory_CriticalSubgroup
import Definitions.Def_OddOrder_GroupTheory_SubgroupInAmbient
import Definitions.Def_OddOrder_GroupTheory_AInvariantPiSubgroups
import Mathlib.Order.Minimal
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.QuotientGroup.Basic

namespace OddOrder.BG.Ch1.S01

open OddOrder.Isaacs.Ch01

open Pointwise

section AInvariantHall

private abbrev HallSubgroups (π : Set ℕ) (G : Type*) [Group G] :=
  {H : Subgroup G // OddOrder.Isaacs.Ch03.IsHallSubgroup π H}

/-- The pointwise action of a `MulAut` on a subgroup is its image. -/
private theorem mulAut_smul_eq_map {G : Type*} [Group G] (φ : MulAut G) (H : Subgroup G) :
    φ • H = H.map (φ : G →* G) := by
  rw [Subgroup.pointwise_smul_def]
  rfl

/-- A Hall subgroup stays Hall under any automorphism. -/
private theorem isHallSubgroup_mulAut_smul {G : Type*} [Group G] [Finite G]
    {π : Set ℕ} {H : Subgroup G} (φ : MulAut G)
    (hH : OddOrder.Isaacs.Ch03.IsHallSubgroup π H) :
    OddOrder.Isaacs.Ch03.IsHallSubgroup π (φ • H) := by
  rw [mulAut_smul_eq_map]
  refine ⟨?_, ?_⟩
  · have hcard :
        Nat.card ↥(H.map (φ : G →* G)) = Nat.card ↥H :=
      (Nat.card_congr (Subgroup.equivMapOfInjective H _ φ.injective).toEquiv).symm
    rw [hcard]
    exact hH.1
  · have hidx : (H.map (φ : G →* G)).index = H.index :=
      Subgroup.index_map_equiv H φ
    rw [hidx]
    exact hH.2

private instance hallSubgroupsMulAutAction {G : Type*} [Group G] [Finite G] (π : Set ℕ) :
    MulAction (MulAut G) (HallSubgroups π G) where
  smul φ H := ⟨φ • H.1, isHallSubgroup_mulAut_smul φ H.2⟩
  one_smul H := by
    apply Subtype.ext
    change (1 : MulAut G) • H.1 = H.1
    simp
  mul_smul φ ψ H := by
    apply Subtype.ext
    change (φ * ψ) • H.1 = φ • (ψ • H.1)
    simp [mul_smul]

private instance hallSubgroupsConjAction {G : Type*} [Group G] [Finite G] (π : Set ℕ) :
    MulAction G (HallSubgroups π G) :=
  MulAction.compHom (HallSubgroups π G) (MulAut.conj : G →* MulAut G)

private theorem hallSubgroups_pretransitive {G : Type*} [Group G] [Finite G] [Group.IsSolvable G]
    (π : Set ℕ) :
    MulAction.IsPretransitive G (HallSubgroups π G) := by
  constructor
  intro H K
  obtain ⟨g, hg⟩ :=
    OddOrder.Isaacs.Ch03.hall_C (G := G) (π := π) H.2 K.2
  refine ⟨g, ?_⟩
  apply Subtype.ext
  change MulAut.conj g • H.1 = K.1
  rw [mulAut_smul_eq_map]
  exact hg

/-- **BG Prop 1.5(a)**: if a finite solvable group `G` is acted on by a finite operator
group `A` with coprime orders, then `A` fixes some Hall `π`-subgroup of `G`.

Proof: let `G` act by conjugation and `A` act through `φ` on the type of Hall `π`-subgroups.
Hall existence makes this type nonempty, Hall conjugacy makes the `G`-action transitive, and
Glauberman's fixed-point lemma gives an `A`-fixed Hall subgroup. -/
theorem exists_aInvariant_hall {G A : Type*} [Group G] [Finite G] [Group.IsSolvable G]
    [Group A] [Finite A] {φ : A →* MulAut G}
    (hCop : Nat.Coprime (Nat.card A) (Nat.card G)) (π : Set ℕ) :
    ∃ H : Subgroup G, OddOrder.Isaacs.Ch03.IsHallSubgroup π H ∧
      OddOrder.Isaacs.Ch03.IsAInvariant φ H := by
  let Ω := HallSubgroups π G
  let : MulAction A Ω := MulAction.compHom Ω φ
  have hΩ_nonempty : Nonempty Ω := by
    obtain ⟨H, hH⟩ := OddOrder.Isaacs.Ch03.hall_E_exists (G := G) π
    exact ⟨⟨H, hH⟩⟩
  have hcompat : OddOrder.Isaacs.Ch04.IsCompatibleMulAction φ Ω := by
    intro a g H
    apply Subtype.ext
    change (φ a) • (MulAut.conj g • H.1) =
      MulAut.conj ((φ a) g) • ((φ a) • H.1)
    rw [← mul_smul, ← mul_smul]
    congr 1
    ext x
    simp [MulAut.conj_apply, map_mul, map_inv]
  obtain ⟨H, hH_fix⟩ :=
    OddOrder.Isaacs.Ch04.glauberman_fixed_point_exists
      (G := G) (A := A) (φ := φ) hCop (Or.inr inferInstance)
      (Ω := Ω) hcompat (hallSubgroups_pretransitive π)
  refine ⟨H.1, H.2, ?_⟩
  intro a
  exact congrArg Subtype.val (hH_fix a)

/-- **BG Prop 1.5(c)**: two `A`-invariant Hall `π`-subgroups of a finite solvable group
under a coprime operator group are conjugate by an element fixed by every operator in `A`.

This is the Hall-subgroup specialization of Glauberman's conjugacy fixed-point lemma. -/
theorem aInvariant_hall_conj {G A : Type*} [Group G] [Finite G] [Group.IsSolvable G]
    [Group A] [Finite A] {φ : A →* MulAut G}
    (hCop : Nat.Coprime (Nat.card A) (Nat.card G)) {π : Set ℕ}
    {H K : Subgroup G}
    (hH_hall : OddOrder.Isaacs.Ch03.IsHallSubgroup π H)
    (hK_hall : OddOrder.Isaacs.Ch03.IsHallSubgroup π K)
    (hH_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ H)
    (hK_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ K) :
    ∃ c : G, (∀ a : A, (φ a) c = c) ∧ MulAut.conj c • H = K := by
  let Ω := HallSubgroups π G
  let : MulAction A Ω := MulAction.compHom Ω φ
  let HΩ : Ω := ⟨H, hH_hall⟩
  let KΩ : Ω := ⟨K, hK_hall⟩
  have hH_fix : ∀ a : A, a • HΩ = HΩ := by
    intro a
    apply Subtype.ext
    exact hH_inv a
  have hK_fix : ∀ a : A, a • KΩ = KΩ := by
    intro a
    apply Subtype.ext
    exact hK_inv a
  have hcompat : OddOrder.Isaacs.Ch04.IsCompatibleMulAction φ Ω := by
    intro a g L
    apply Subtype.ext
    change (φ a) • (MulAut.conj g • L.1) =
      MulAut.conj ((φ a) g) • ((φ a) • L.1)
    rw [← mul_smul, ← mul_smul]
    congr 1
    ext x
    simp [MulAut.conj_apply, map_mul, map_inv]
  obtain ⟨c, hc_fix, hc_smul⟩ :=
    OddOrder.Isaacs.Ch04.glauberman_fixed_points_conj
      (G := G) (A := A) (φ := φ) hCop (Or.inr inferInstance)
      (Ω := Ω) hcompat (hallSubgroups_pretransitive π)
      hH_fix hK_fix
  refine ⟨c, hc_fix, ?_⟩
  exact congrArg Subtype.val hc_smul

open OddOrder.Isaacs.Ch03.IsAInvariant
  (quotientMulAutHom quotientMulAutHom_apply_mk') in
/-- An `A`-invariant subgroup maps to an `A`-invariant subgroup in an `A`-invariant
quotient. This is the quotient-action transport used in BG Prop. 1.5(b). -/
private theorem isAInvariant_map_mk'
    {G A : Type*} [Group G] [Group A] {φ : A →* MulAut G}
    {N : Subgroup G} [N.Normal] (hN : OddOrder.Isaacs.Ch03.IsAInvariant φ N)
    {H : Subgroup G} (hH : OddOrder.Isaacs.Ch03.IsAInvariant φ H) :
    OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom hN)
      (H.map (QuotientGroup.mk' N)) := by
  rw [OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem]
  intro a q hq
  rw [Subgroup.mem_map] at hq ⊢
  obtain ⟨g, hg, rfl⟩ := hq
  exact ⟨(φ a) g, hH.smul_mem a hg, by rw [quotientMulAutHom_apply_mk']⟩

open OddOrder.Isaacs.Ch03.IsAInvariant
  (quotientMulAutHom quotientMulAutHom_apply_mk') in
/-- The preimage of an invariant subgroup of an `A`-invariant quotient is invariant in the
original group. -/
private theorem isAInvariant_comap_mk'
    {G A : Type*} [Group G] [Group A] {φ : A →* MulAut G}
    {N : Subgroup G} [N.Normal] (hN : OddOrder.Isaacs.Ch03.IsAInvariant φ N)
    {Y : Subgroup (G ⧸ N)}
    (hY : OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom hN) Y) :
    OddOrder.Isaacs.Ch03.IsAInvariant φ (Y.comap (QuotientGroup.mk' N)) := by
  rw [OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem]
  intro a g hg
  rw [Subgroup.mem_comap] at hg ⊢
  rw [← quotientMulAutHom_apply_mk']
  exact hY.smul_mem a hg

/-- Restrict an invariant subgroup into an invariant ambient subgroup. -/
private theorem isAInvariant_subgroupOf_restrict
    {G A : Type*} [Group G] [Group A] {φ : A →* MulAut G}
    {U H : Subgroup G} (hU : OddOrder.Isaacs.Ch03.IsAInvariant φ U)
    (hH : OddOrder.Isaacs.Ch03.IsAInvariant φ H) :
    OddOrder.Isaacs.Ch03.IsAInvariant hU.restrict (H.subgroupOf U) := by
  rw [OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem]
  intro a h hh
  rw [Subgroup.mem_subgroupOf] at hh ⊢
  rw [OddOrder.Isaacs.Ch03.IsAInvariant.restrict_apply_val]
  exact hH.smul_mem a hh

/-- Push an invariant subgroup of an invariant ambient subgroup back to the original group. -/
private theorem isAInvariant_map_subtype_of_restrict
    {G A : Type*} [Group G] [Group A] {φ : A →* MulAut G}
    {U : Subgroup G} (hU : OddOrder.Isaacs.Ch03.IsAInvariant φ U)
    {L : Subgroup U} (hL : OddOrder.Isaacs.Ch03.IsAInvariant hU.restrict L) :
    OddOrder.Isaacs.Ch03.IsAInvariant φ (L.map U.subtype) := by
  rw [OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem]
  intro a x hx
  rw [Subgroup.mem_map] at hx ⊢
  obtain ⟨l, hl, rfl⟩ := hx
  exact ⟨(hU.restrict a) l, hL.smul_mem a hl,
    OddOrder.Isaacs.Ch03.IsAInvariant.restrict_apply_val hU a l⟩

/-- A Hall subgroup of an invariant subgroup whose ambient index is a `π'`-number is a Hall
subgroup after pushing it back to the whole group. This is the Hall-index transfer needed in
the `H < G` branch of BG Prop. 1.5(b). -/
private theorem isHallSubgroup_map_subtype_of_index_no_pi
    {G : Type*} [Group G] [Finite G] {π : Set ℕ} {H : Subgroup G} {L : Subgroup H}
    (hL : OddOrder.Isaacs.Ch03.IsHallSubgroup π L)
    (hH_index : ∀ p ∈ H.index.primeFactors, p ∉ π) :
    OddOrder.Isaacs.Ch03.IsHallSubgroup π (L.map H.subtype) := by
  have hcard : Nat.card ↥(L.map H.subtype) = Nat.card ↥L :=
    (Nat.card_congr
      (Subgroup.equivMapOfInjective L H.subtype H.subtype_injective).toEquiv).symm
  have hindex : (L.map H.subtype).index = L.index * H.index := by
    have hpos : 0 < Nat.card ↥L := Nat.card_pos
    have hmul : Nat.card ↥L * (L.map H.subtype).index =
        Nat.card ↥L * (L.index * H.index) := by
      calc
        Nat.card ↥L * (L.map H.subtype).index
            = Nat.card ↥(L.map H.subtype) * (L.map H.subtype).index := by rw [hcard]
        _ = Nat.card G := Subgroup.card_mul_index (L.map H.subtype)
        _ = Nat.card H * H.index := (Subgroup.card_mul_index H).symm
        _ = (Nat.card ↥L * L.index) * H.index := by rw [Subgroup.card_mul_index L]
        _ = Nat.card ↥L * (L.index * H.index) := by ring
    exact Nat.mul_left_cancel hpos hmul
  refine ⟨?_, ?_⟩
  · intro p hp
    rw [hcard] at hp
    exact hL.1 p hp
  · intro p hp hp_pi
    rw [hindex] at hp
    rw [Nat.mem_primeFactors] at hp
    obtain ⟨hp_prime, hp_dvd, _⟩ := hp
    rcases hp_prime.dvd_mul.mp hp_dvd with hp_L | hp_H
    · exact hL.2 p
        (Nat.mem_primeFactors.mpr ⟨hp_prime, hp_L, Subgroup.index_ne_zero_of_finite⟩) hp_pi
    · exact hH_index p
        (Nat.mem_primeFactors.mpr ⟨hp_prime, hp_H, Subgroup.index_ne_zero_of_finite⟩) hp_pi

/-- A `π`-subgroup remains a `π`-subgroup after mapping to an invariant quotient. -/
private theorem isPiGroup_map_mk'
    {G : Type*} [Group G] [Finite G] {π : Set ℕ} {N K : Subgroup G} [N.Normal]
    (hK : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup π K) :
    OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup π (K.map (QuotientGroup.mk' N)) := by
  intro p hp
  apply hK
  rw [Nat.mem_primeFactors] at hp ⊢
  exact ⟨hp.1, hp.2.1.trans (Subgroup.card_map_dvd _ _), Nat.card_pos.ne'⟩

/-- Quotienting by a nontrivial normal subgroup strictly lowers finite group order. -/
private theorem card_quotient_lt_card_of_ne_bot
    {G : Type*} [Group G] [Finite G] {N : Subgroup G} [N.Normal] (hN_ne_bot : N ≠ ⊥) :
    Nat.card (G ⧸ N) < Nat.card G := by
  have : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).mpr hN_ne_bot
  have hN_one_lt : 1 < Nat.card N := Finite.one_lt_card
  have hQ_pos : 0 < Nat.card (G ⧸ N) := Nat.card_pos
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N]
  exact lt_mul_of_one_lt_right hQ_pos hN_one_lt

/-- Coprime operator order descends to a quotient of the acted-on group. -/
private theorem coprime_card_quotient_of_coprime
    {G A : Type*} [Group G] [Finite G] [Group A] [Finite A]
    {N : Subgroup G} [N.Normal] (hCop : Nat.Coprime (Nat.card A) (Nat.card G)) :
    Nat.Coprime (Nat.card A) (Nat.card (G ⧸ N)) :=
  hCop.coprime_dvd_right (Subgroup.card_quotient_dvd_card N)

open OddOrder.Isaacs.Ch03.IsAInvariant
  (quotientMulAutHom) in
/-- Pull back a quotient Hall subgroup containing the image of `K`.

This packages the quotient/comap step in BG Prop. 1.5(b): once induction in `G/M` gives an
`A`-invariant Hall subgroup containing the image of `K`, its preimage in `G` is
`A`-invariant, contains `K`, and has π-free index. -/
private theorem quotient_hall_preimage_frame
    {G A : Type*} [Group G] [Finite G] [Group A] {φ : A →* MulAut G}
    {π : Set ℕ} {K M : Subgroup G} [M.Normal]
    (hM_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ M)
    {Hbar : Subgroup (G ⧸ M)}
    (hHbar_hall : OddOrder.Isaacs.Ch03.IsHallSubgroup π Hbar)
    (hHbar_inv : OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom hM_inv) Hbar)
    (hK_image_le : K.map (QuotientGroup.mk' M) ≤ Hbar) :
    ∃ H : Subgroup G,
      OddOrder.Isaacs.Ch03.IsAInvariant φ H ∧ K ≤ H ∧
        (∀ p ∈ H.index.primeFactors, p ∉ π) ∧
        H = Hbar.comap (QuotientGroup.mk' M) := by
  let q : G →* G ⧸ M := QuotientGroup.mk' M
  let H : Subgroup G := Hbar.comap q
  refine ⟨H, ?_, ?_, ?_, rfl⟩
  · exact isAInvariant_comap_mk' hM_inv hHbar_inv
  · intro k hk
    change q k ∈ Hbar
    exact hK_image_le (by
      rw [Subgroup.mem_map]
      exact ⟨k, hk, rfl⟩)
  · have hindex : H.index = Hbar.index :=
      Hbar.index_comap_of_surjective (QuotientGroup.mk'_surjective (N := M))
    rw [hindex]
    exact hHbar_hall.2

/-- Coprime operator order descends to a subgroup of the acted-on group. -/
private theorem coprime_card_subgroup_of_coprime
    {G A : Type*} [Group G] [Finite G] [Group A] [Finite A]
    {H : Subgroup G} (hCop : Nat.Coprime (Nat.card A) (Nat.card G)) :
    Nat.Coprime (Nat.card A) (Nat.card H) :=
  hCop.coprime_dvd_right (Subgroup.card_subgroup_dvd_card H)

/-- Lift the recursive result from a proper invariant overgroup back to the ambient group.

In the `H < G` branch of BG Prop. 1.5(b), quotient induction first produces an invariant
overgroup `H` of `K` with π-free index.  Applying the main induction hypothesis inside `H`
gives an invariant Hall subgroup `L ≤ H` containing `K`; this helper pushes `L` back to `G`.
-/
private theorem lift_hall_from_invariant_overgroup
    {G A : Type*} [Group G] [Finite G] [Group A] {φ : A →* MulAut G}
    {π : Set ℕ} {K H : Subgroup G}
    (hH_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ H)
    (hH_index : ∀ p ∈ H.index.primeFactors, p ∉ π)
    (hK_le_H : K ≤ H) {L : Subgroup H}
    (hL_hall : OddOrder.Isaacs.Ch03.IsHallSubgroup π L)
    (hL_inv : OddOrder.Isaacs.Ch03.IsAInvariant hH_inv.restrict L)
    (hK_sub_le_L : K.subgroupOf H ≤ L) :
    ∃ Lg : Subgroup G,
      OddOrder.Isaacs.Ch03.IsHallSubgroup π Lg ∧
        OddOrder.Isaacs.Ch03.IsAInvariant φ Lg ∧ K ≤ Lg := by
  refine ⟨L.map H.subtype, ?_, ?_, ?_⟩
  · exact isHallSubgroup_map_subtype_of_index_no_pi hL_hall hH_index
  · exact isAInvariant_map_subtype_of_restrict hH_inv hL_inv
  · intro k hk
    rw [Subgroup.mem_map]
    refine ⟨⟨k, hK_le_H hk⟩, ?_, rfl⟩
    exact hK_sub_le_L (by
      rw [Subgroup.mem_subgroupOf]
      exact hk)

/-- Assemble the recursive proper-overgroup branch of BG Prop. 1.5(b).

This is the branch after quotient induction has produced an invariant overgroup `H` of `K`
with π-free index.  If the main induction hypothesis has already produced, inside `H`, an
invariant Hall subgroup containing `K.subgroupOf H`, then this packages the lift back to `G`.
-/
private theorem proper_overgroup_branch_frame
    {G A : Type*} [Group G] [Finite G] [Group A] {φ : A →* MulAut G}
    {π : Set ℕ} {K H : Subgroup G}
    (hH_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ H)
    (hH_index : ∀ p ∈ H.index.primeFactors, p ∉ π)
    (hK_pi : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup π K)
    (hK_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ K)
    (hK_le_H : K ≤ H)
    (hIH_H : ∀ {Ksub : Subgroup H},
      OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup π Ksub →
        OddOrder.Isaacs.Ch03.IsAInvariant hH_inv.restrict Ksub →
        ∃ L : Subgroup H,
          OddOrder.Isaacs.Ch03.IsHallSubgroup π L ∧
            OddOrder.Isaacs.Ch03.IsAInvariant hH_inv.restrict L ∧ Ksub ≤ L) :
    ∃ Lg : Subgroup G,
      OddOrder.Isaacs.Ch03.IsHallSubgroup π Lg ∧
        OddOrder.Isaacs.Ch03.IsAInvariant φ Lg ∧ K ≤ Lg := by
  let Ksub : Subgroup H := K.subgroupOf H
  have hKsub_pi : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup π Ksub :=
    OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup.subgroupOf hK_le_H hK_pi
  have hKsub_inv : OddOrder.Isaacs.Ch03.IsAInvariant hH_inv.restrict Ksub :=
    isAInvariant_subgroupOf_restrict hH_inv hK_inv
  obtain ⟨L, hL_hall, hL_inv, hKsub_le_L⟩ := hIH_H hKsub_pi hKsub_inv
  exact lift_hall_from_invariant_overgroup hH_inv hH_index hK_le_H
    hL_hall hL_inv hKsub_le_L

/-- A nontrivial finite group has a minimal nontrivial `A`-invariant normal subgroup. -/
private theorem exists_minimal_normal_aInvariant
    {G A : Type*} [Group G] [Finite G] [Nontrivial G]
    [Group A] {φ : A →* MulAut G} :
    ∃ M : Subgroup G, M.Normal ∧ OddOrder.Isaacs.Ch03.IsAInvariant φ M ∧ M ≠ ⊥ ∧
      ∀ N : Subgroup G, N.Normal → OddOrder.Isaacs.Ch03.IsAInvariant φ N →
        N ≤ M → N ≠ ⊥ → M ≤ N := by
  classical
  let S : Set (Subgroup G) :=
    {N | N.Normal ∧ OddOrder.Isaacs.Ch03.IsAInvariant φ N ∧ N ≠ ⊥}
  have hS_fin : S.Finite := Set.toFinite S
  have hS_nonempty : S.Nonempty :=
    ⟨⊤, inferInstance, OddOrder.Isaacs.Ch03.IsAInvariant.top φ, top_ne_bot⟩
  obtain ⟨M, hM_min⟩ := hS_fin.exists_minimal hS_nonempty
  obtain ⟨⟨hM_normal, hM_inv, hM_ne_bot⟩, hM_minimal⟩ := hM_min
  refine ⟨M, hM_normal, hM_inv, hM_ne_bot, ?_⟩
  intro N hN_normal hN_inv hN_le hN_ne_bot
  exact hM_minimal ⟨hN_normal, hN_inv, hN_ne_bot⟩ hN_le

/-- A minimal nontrivial `A`-invariant normal subgroup of a finite solvable group is
commutative.

This is the abelian-chief-factor step needed for the induction in BG Prop. 1.5(b): the
minimality is only among `A`-invariant normal subgroups below `M`, not among all normal
subgroups.  Solvability still forces `⁅M, M⁆ < M`; since `⁅M, M⁆` is again normal and
`A`-invariant, minimality makes the commutator trivial. -/
private theorem isMulCommutative_of_minimal_normal_aInvariant
    {G A : Type*} [Group G] [Finite G] [Group.IsSolvable G]
    [Group A] {φ : A →* MulAut G} {M : Subgroup G} [M.Normal]
    (hM_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ M)
    (hM_ne_bot : M ≠ ⊥)
    (hM_min : ∀ N : Subgroup G, N.Normal →
      OddOrder.Isaacs.Ch03.IsAInvariant φ N → N ≤ M → N ≠ ⊥ → M ≤ N) :
    IsMulCommutative M := by
  have hcomm_lt : ⁅M, M⁆ < M := Group.IsSolvable.commutator_lt_of_ne_bot hM_ne_bot
  have hcomm_bot : (⁅M, M⁆ : Subgroup G) = ⊥ := by
    by_contra hcomm_ne_bot
    have hM_le_comm : M ≤ ⁅M, M⁆ :=
      hM_min ⁅M, M⁆ (Subgroup.commutator_normal M M)
        (hM_inv.commutator hM_inv) hcomm_lt.le hcomm_ne_bot
    exact hcomm_lt.not_ge hM_le_comm
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hcomm_bot
  refine ⟨⟨fun x y => ?_⟩⟩
  have hx_cent : (x : G) ∈ Subgroup.centralizer M := hcomm_bot x.2
  rw [Subgroup.mem_centralizer_iff] at hx_cent
  exact Subtype.ext ((hx_cent y y.2).symm)

/-- A minimal nontrivial `A`-invariant normal subgroup of a finite solvable group is a
`p`-group for some prime `p`.

After the preceding commutativity lemma, a Sylow subgroup of `M` is characteristic in `M`;
its image in `G` is therefore again normal and `A`-invariant. Minimality forces that image to
be all of `M`. -/
private theorem exists_prime_isPGroup_of_minimal_normal_aInvariant
    {G A : Type*} [Group G] [Finite G] [Group.IsSolvable G]
    [Group A] {φ : A →* MulAut G} {M : Subgroup G} [M.Normal]
    (hM_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ M)
    (hM_ne_bot : M ≠ ⊥)
    (hM_min : ∀ N : Subgroup G, N.Normal →
      OddOrder.Isaacs.Ch03.IsAInvariant φ N → N ≤ M → N ≠ ⊥ → M ≤ N) :
    ∃ p : ℕ, p.Prime ∧ IsPGroup p M := by
  classical
  have hM_comm : IsMulCommutative M :=
    isMulCommutative_of_minimal_normal_aInvariant hM_inv hM_ne_bot hM_min
  have hM_card_ne_one : Nat.card M ≠ 1 := by
    intro hcard
    exact hM_ne_bot ((Subgroup.eq_bot_iff_card M).mpr hcard)
  obtain ⟨p, hp_prime, hp_dvd⟩ := Nat.exists_prime_and_dvd hM_card_ne_one
  have hpFact : Fact p.Prime := ⟨hp_prime⟩
  let P : Sylow p M := default
  have hP_normal : (P : Subgroup M).Normal := Subgroup.normal_of_isMulCommutative (P : Subgroup M)
  have hP_char : (P : Subgroup M).Characteristic :=
    Sylow.characteristic_of_normal P hP_normal
  let Pmap : Subgroup G := (P : Subgroup M).map M.subtype
  have hPmap_normal : Pmap.Normal := by
    dsimp [Pmap]
    infer_instance
  have hPmap_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ Pmap := by
    dsimp [Pmap]
    exact hM_inv.map_subtype_of_characteristic
  have hPmap_le_M : Pmap ≤ M := by
    dsimp [Pmap]
    exact Subgroup.map_subtype_le (P : Subgroup M)
  have hP_ne_bot : (P : Subgroup M) ≠ ⊥ := P.ne_bot_of_dvd_card hp_dvd
  have hPmap_ne_bot : Pmap ≠ ⊥ := by
    intro hbot
    apply hP_ne_bot
    have hmap_bot : (P : Subgroup M).map M.subtype = ⊥ := by
      simpa [Pmap] using hbot
    exact (Subgroup.map_eq_bot_iff_of_injective _ M.subtype_injective).mp hmap_bot
  have hM_le_Pmap : M ≤ Pmap :=
    hM_min Pmap hPmap_normal hPmap_inv hPmap_le_M hPmap_ne_bot
  have hPmap_eq_M : Pmap = M := le_antisymm hPmap_le_M hM_le_Pmap
  have hP_eq_top : (P : Subgroup M) = ⊤ := by
    apply (Subgroup.map_subtype_inj (H := M)).mp
    have htop_map : (⊤ : Subgroup M).map M.subtype = M := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    calc
      (P : Subgroup M).map M.subtype = M := by simpa [Pmap] using hPmap_eq_M
      _ = (⊤ : Subgroup M).map M.subtype := htop_map.symm
  obtain ⟨n, hnP⟩ := (IsPGroup.iff_card (p := p) (G := P)).mp P.2
  have hcardM : Nat.card M = p ^ n := by
    have hcardP : Nat.card P = Nat.card M := by
      rw [hP_eq_top, Subgroup.card_top]
    rwa [← hcardP]
  exact ⟨p, hp_prime, (IsPGroup.iff_card (p := p) (G := M)).mpr ⟨n, hcardM⟩⟩

/-- A proper subgroup of a finite group has strictly smaller cardinality. -/
private theorem subgroup_card_lt_card_of_ne_top
    {G : Type*} [Group G] [Finite G] {H : Subgroup G} (hH_ne_top : H ≠ ⊤) :
    Nat.card H < Nat.card G := by
  have hindex_ne_one : H.index ≠ 1 := fun hidx => hH_ne_top (Subgroup.index_eq_one.mp hidx)
  have hindex_gt_one : 1 < H.index :=
    Nat.one_lt_iff_ne_zero_and_ne_one.mpr
      ⟨Subgroup.index_ne_zero_of_finite, hindex_ne_one⟩
  calc
    Nat.card H < Nat.card H * H.index := lt_mul_of_one_lt_right Nat.card_pos hindex_gt_one
    _ = Nat.card G := Subgroup.card_mul_index H

/-- A `p`-group is a `π`-group once `p ∈ π`. -/
private theorem subgroup_isPiGroup_of_isPGroup_of_mem
    {G : Type*} [Group G] [Finite G] {π : Set ℕ} {H : Subgroup G}
    {p : ℕ} [Fact p.Prime] (hH : IsPGroup p H) (hpπ : p ∈ π) :
    OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup π H := by
  intro q hq
  have hsingle : q ∈ ({p} : Set ℕ) :=
    OddOrder.Isaacs.Ch04.isPiGroup_singleton_of_isPGroup hH q hq
  rw [Set.mem_singleton_iff] at hsingle
  rw [hsingle]
  exact hpπ

/-- A `π`-subgroup has trivial intersection with a `p`-group for `p ∉ π`. -/
private theorem inf_eq_bot_of_isPiGroup_of_isPGroup_not_mem
    {G : Type*} [Group G] [Finite G] {π : Set ℕ} {K M : Subgroup G}
    {p : ℕ} [Fact p.Prime]
    (hK_pi : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup π K)
    (hM_p : IsPGroup p M) (hp_not_pi : p ∉ π) :
    K ⊓ M = ⊥ := by
  apply Subgroup.eq_bot_of_card_eq
  have hM_pi' : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup {q | q ∉ π} M :=
    subgroup_isPiGroup_of_isPGroup_of_mem hM_p hp_not_pi
  have hdvdK : Nat.card ↥(K ⊓ M : Subgroup G) ∣ Nat.card K :=
    Subgroup.card_dvd_of_le inf_le_left
  have hdvdM : Nat.card ↥(K ⊓ M : Subgroup G) ∣ Nat.card M :=
    Subgroup.card_dvd_of_le inf_le_right
  have hcop : Nat.Coprime (Nat.card K) (Nat.card M) :=
    OddOrder.Isaacs.Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl
      Nat.card_pos.ne' Nat.card_pos.ne' hK_pi hM_pi'
  have hdvd_gcd : Nat.card ↥(K ⊓ M : Subgroup G) ∣ Nat.gcd (Nat.card K) (Nat.card M) :=
    Nat.dvd_gcd hdvdK hdvdM
  rw [hcop] at hdvd_gcd
  exact Nat.dvd_one.mp hdvd_gcd

/-- Package complementary subgroups inside a specified ambient subgroup. -/
private theorem isComplement_subgroupOf_of_disjoint_mul_eq_univ
    {G : Type*} [Group G] {U H M : Subgroup G}
    (hH_le_U : H ≤ U) (hM_le_U : M ≤ U) (hHM_bot : H ⊓ M = ⊥)
    (hmul : ∀ x ∈ U, ∃ m ∈ M, ∃ h ∈ H, m * h = x) :
    Subgroup.IsComplement' (M.subgroupOf U) (H.subgroupOf U) := by
  apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
  · rw [disjoint_iff]
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_bot,
      Subtype.ext_iff, OneMemClass.coe_one]
    refine ⟨?_, fun hx => by simp [hx]⟩
    rintro ⟨hxM, hxH⟩
    have hx : (x : G) ∈ H ⊓ M := ⟨hxH, hxM⟩
    rw [hHM_bot, Subgroup.mem_bot] at hx
    exact hx
  · rw [Set.eq_univ_iff_forall]
    intro x
    obtain ⟨m, hmM, h, hhH, hmh⟩ := hmul x x.2
    refine ⟨⟨m, hM_le_U hmM⟩, hmM, ⟨h, hH_le_U hhH⟩, hhH, ?_⟩
    ext
    exact hmh

/-- A complement to a `π'`-subgroup is a Hall `π`-subgroup of the ambient subgroup. -/
private theorem isHallSubgroup_subgroupOf_of_complement_pi_pi'
    {G : Type*} [Group G] [Finite G] {π : Set ℕ} {U H M : Subgroup G}
    (hH_le_U : H ≤ U) (hM_le_U : M ≤ U)
    (hH_pi : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup π H)
    (hM_pi' : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup {p | p ∉ π} M)
    (hComp : Subgroup.IsComplement' (M.subgroupOf U) (H.subgroupOf U)) :
    OddOrder.Isaacs.Ch03.IsHallSubgroup π (H.subgroupOf U) := by
  refine ⟨?_, ?_⟩
  · exact OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup.subgroupOf hH_le_U hH_pi
  · have hMsub_pi' :
        OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup {p | p ∉ π} (M.subgroupOf U) :=
      OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup.subgroupOf hM_le_U hM_pi'
    intro q hq hq_pi
    rw [hComp.index_eq_card] at hq
    exact hMsub_pi' q hq hq_pi

/-- Conjugating an invariant subgroup by an `A`-fixed element preserves invariance. -/
private theorem isAInvariant_mulAut_conj_smul_of_fixed
    {G A : Type*} [Group G] [Group A] {φ : A →* MulAut G}
    {H : Subgroup G} (hH : OddOrder.Isaacs.Ch03.IsAInvariant φ H)
    {c : G} (hc : ∀ a : A, (φ a) c = c) :
    OddOrder.Isaacs.Ch03.IsAInvariant φ (MulAut.conj c • H) := by
  rw [OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem]
  intro a x hx
  rw [mulAut_smul_eq_map] at hx ⊢
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨(φ a) y, hH.smul_mem a hy, ?_⟩
  simp [MulAut.conj_apply, map_mul, map_inv, hc a]

/-- Assemble the `H = G` branch of BG Prop. 1.5(b).

Here quotient induction has produced the whole preimage, so `G/M` is a `π`-group.
For a minimal normal `p`-subgroup `M`, the non-`π` assumption on `G` forces `p ∉ π`.
An invariant Hall subgroup `Q` complements `M`; inside `K ⊔ M`, the subgroups `K` and
`Q ∩ (K ⊔ M)` are invariant Hall `π`-subgroups, hence are conjugate by an `A`-fixed element
of `K ⊔ M`.  The conjugate of `Q` is the desired invariant Hall overgroup of `K`.
-/
private theorem top_preimage_branch_frame
    {G A : Type*} [Group G] [Finite G] [Group.IsSolvable G]
    [Group A] [Finite A] {φ : A →* MulAut G}
    (hCop : Nat.Coprime (Nat.card A) (Nat.card G))
    {π : Set ℕ} {K M : Subgroup G} [M.Normal]
    (hG_not_pi : ¬ ∀ q ∈ (Nat.card G).primeFactors, q ∈ π)
    (hM_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ M)
    {p : ℕ} [Fact p.Prime] (hM_p : IsPGroup p M)
    (hquot_pi : ∀ q ∈ (Nat.card (G ⧸ M)).primeFactors, q ∈ π)
    (hK_pi : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup π K)
    (hK_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ K) :
    ∃ L : Subgroup G,
      OddOrder.Isaacs.Ch03.IsHallSubgroup π L ∧
        OddOrder.Isaacs.Ch03.IsAInvariant φ L ∧ K ≤ L := by
  classical
  have hp_not_pi : p ∉ π := by
    intro hp_pi
    have hM_pi : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup π M :=
      subgroup_isPiGroup_of_isPGroup_of_mem hM_p hp_pi
    have hG_pi : OddOrder.Isaacs.Ch03.IsPiGroup π G :=
      OddOrder.Isaacs.Ch03.IsPiGroup.of_normal_quotient (N := M) hM_pi hquot_pi
    exact hG_not_pi hG_pi
  have hM_pi' : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup {q | q ∉ π} M :=
    subgroup_isPiGroup_of_isPGroup_of_mem hM_p hp_not_pi
  obtain ⟨Q, hQ_hall, hQ_inv⟩ := exists_aInvariant_hall hCop π
  have hQ_M_bot : Q ⊓ M = ⊥ :=
    inf_eq_bot_of_isPiGroup_of_isPGroup_not_mem hQ_hall.1 hM_p hp_not_pi
  have hQbar_top : Q.map (QuotientGroup.mk' M) = ⊤ := by
    have htop_pi :
        OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup π (⊤ : Subgroup (G ⧸ M)) := by
      intro q hq
      rw [Subgroup.card_top] at hq
      exact hquot_pi q hq
    have hQbar_hall :
        OddOrder.Isaacs.Ch03.IsHallSubgroup π (Q.map (QuotientGroup.mk' M)) :=
      hQ_hall.map_quotient
    exact eq_top_iff.mpr
      (OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup.normal_le_hall htop_pi hQbar_hall)
  have hQM_top : Q ⊔ M = ⊤ := by
    rw [eq_top_iff]
    intro g _
    have hgbar : (QuotientGroup.mk' M) g ∈ Q.map (QuotientGroup.mk' M) := by
      rw [hQbar_top]
      trivial
    rw [Subgroup.mem_map] at hgbar
    obtain ⟨q, hqQ, hqeq⟩ := hgbar
    have hm : q⁻¹ * g ∈ M := by
      apply (QuotientGroup.eq_one_iff (N := M) (q⁻¹ * g)).mp
      change (QuotientGroup.mk' M) (q⁻¹ * g) = 1
      rw [map_mul, map_inv, hqeq, inv_mul_cancel]
    have hg : g = q * (q⁻¹ * g) := by group
    rw [hg]
    exact Subgroup.mul_mem_sup hqQ hm
  let U : Subgroup G := K ⊔ M
  have hK_le_U : K ≤ U := le_sup_left
  have hM_le_U : M ≤ U := le_sup_right
  have hU_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ U :=
    OddOrder.Isaacs.Ch03.IsAInvariant.sup hK_inv hM_inv
  have hK_M_bot : K ⊓ M = ⊥ :=
    inf_eq_bot_of_isPiGroup_of_isPGroup_not_mem hK_pi hM_p hp_not_pi
  have hK_comp : Subgroup.IsComplement' (M.subgroupOf U) (K.subgroupOf U) := by
    refine isComplement_subgroupOf_of_disjoint_mul_eq_univ hK_le_U hM_le_U hK_M_bot ?_
    intro x hxU
    have hx : (x : G) ∈ M ⊔ K := by
      rw [sup_comm]
      exact hxU
    rw [Subgroup.mem_sup_of_normal_left] at hx
    obtain ⟨m, hmM, k, hkK, hmk⟩ := hx
    exact ⟨m, hmM, k, hkK, hmk⟩
  have hKsub_hall : OddOrder.Isaacs.Ch03.IsHallSubgroup π (K.subgroupOf U) :=
    isHallSubgroup_subgroupOf_of_complement_pi_pi' hK_le_U hM_le_U hK_pi hM_pi' hK_comp
  let QKU : Subgroup G := Q ⊓ U
  have hQKU_le_U : QKU ≤ U := inf_le_right
  have hQKU_pi : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup π QKU :=
    OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup.le inf_le_left hQ_hall.1
  have hQKU_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ QKU :=
    OddOrder.Isaacs.Ch03.IsAInvariant.inf hQ_inv hU_inv
  have hQKU_M_bot : QKU ⊓ M = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxQM : x ∈ Q ⊓ M := ⟨hx.1.1, hx.2⟩
    rw [hQ_M_bot] at hxQM
    exact hxQM
  have hQKU_comp : Subgroup.IsComplement' (M.subgroupOf U) (QKU.subgroupOf U) := by
    refine isComplement_subgroupOf_of_disjoint_mul_eq_univ hQKU_le_U hM_le_U hQKU_M_bot ?_
    intro x hxU
    have hxQM : (x : G) ∈ Q ⊔ M := by
      rw [hQM_top]
      trivial
    rw [Subgroup.mem_sup_of_normal_right] at hxQM
    obtain ⟨q, hqQ, m, hmM, hqm⟩ := hxQM
    have hqU : q ∈ U := by
      have hq_eq : q = (x : G) * m⁻¹ := by
        rw [← hqm]
        group
      rw [hq_eq]
      exact U.mul_mem hxU (U.inv_mem (hM_le_U hmM))
    have hm_conj : q * m * q⁻¹ ∈ M :=
      (inferInstance : M.Normal).conj_mem m hmM q
    refine ⟨q * m * q⁻¹, hm_conj, q, ⟨hqQ, hqU⟩, ?_⟩
    rw [← hqm]
    group
  have hQKUsub_hall : OddOrder.Isaacs.Ch03.IsHallSubgroup π (QKU.subgroupOf U) :=
    isHallSubgroup_subgroupOf_of_complement_pi_pi' hQKU_le_U hM_le_U hQKU_pi hM_pi'
      hQKU_comp
  have hKsub_inv : OddOrder.Isaacs.Ch03.IsAInvariant hU_inv.restrict (K.subgroupOf U) :=
    isAInvariant_subgroupOf_restrict hU_inv hK_inv
  have hQKUsub_inv : OddOrder.Isaacs.Ch03.IsAInvariant hU_inv.restrict (QKU.subgroupOf U) :=
    isAInvariant_subgroupOf_restrict hU_inv hQKU_inv
  have hCop_U : Nat.Coprime (Nat.card A) (Nat.card U) :=
    coprime_card_subgroup_of_coprime hCop
  obtain ⟨c, hc_fix, hc_conj⟩ :=
    aInvariant_hall_conj (G := U) (A := A) (φ := hU_inv.restrict) hCop_U
      hQKUsub_hall hKsub_hall hQKUsub_inv hKsub_inv
  let cG : G := c
  have hc_fix_G : ∀ a : A, (φ a) cG = cG := by
    intro a
    have h := congrArg Subtype.val (hc_fix a)
    simpa [cG, OddOrder.Isaacs.Ch03.IsAInvariant.restrict_apply_val] using h
  refine ⟨MulAut.conj cG • Q, ?_, ?_, ?_⟩
  · exact isHallSubgroup_mulAut_smul (MulAut.conj cG) hQ_hall
  · exact isAInvariant_mulAut_conj_smul_of_fixed hQ_inv hc_fix_G
  · intro k hkK
    rw [mulAut_smul_eq_map, Subgroup.mem_map]
    let kU : U := ⟨k, hK_le_U hkK⟩
    have hkU : kU ∈ K.subgroupOf U := by
      change (kU : G) ∈ K
      exact hkK
    have hkU_conj : kU ∈ MulAut.conj c • (QKU.subgroupOf U) := by
      rw [hc_conj]
      exact hkU
    rw [mulAut_smul_eq_map, Subgroup.mem_map] at hkU_conj
    obtain ⟨y, hyQKU, hy_eq⟩ := hkU_conj
    refine ⟨(y : G), ?_, ?_⟩
    · have hyQKU_G : (y : G) ∈ QKU := hyQKU
      exact hyQKU_G.1
    · change (MulAut.conj cG) (y : G) = k
      simpa [cG] using congrArg Subtype.val hy_eq

open OddOrder.Isaacs.Ch03.IsAInvariant
  (quotientMulAutHom) in
/-- Induction kernel for BG Prop. 1.5(b). -/
private theorem aInvariant_piSubgroup_le_aInvariant_hall_aux :
    ∀ n : ℕ,
      ∀ (G A : Type*) [Group G] [Finite G] [Group.IsSolvable G]
        [Group A] [Finite A],
        Nat.card G ≤ n → ∀ {φ : A →* MulAut G}
        (_hCop : Nat.Coprime (Nat.card A) (Nat.card G))
        {π : Set ℕ} {K : Subgroup G},
        OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup π K →
        OddOrder.Isaacs.Ch03.IsAInvariant φ K →
        ∃ H : Subgroup G,
          OddOrder.Isaacs.Ch03.IsHallSubgroup π H ∧
            OddOrder.Isaacs.Ch03.IsAInvariant φ H ∧ K ≤ H := by
  intro n
  induction n with
  | zero =>
      intro G A _ _ _ _ _ hcard φ _hCop π K hK_pi hK_inv
      have hpos : 0 < Nat.card G := Nat.card_pos
      omega
  | succ n ih =>
      intro G A _ _ _ _ _ hcard φ hCop π K hK_pi hK_inv
      by_cases hsmall : Nat.card G ≤ n
      · exact ih G A hsmall hCop hK_pi hK_inv
      by_cases hG_pi : ∀ p ∈ (Nat.card G).primeFactors, p ∈ π
      · refine ⟨⊤, ?_, OddOrder.Isaacs.Ch03.IsAInvariant.top φ, le_top⟩
        exact (OddOrder.Isaacs.Ch03.IsHallSubgroup.top_iff (G := G) π).mpr hG_pi
      have hG_card_ne_one : Nat.card G ≠ 1 := by
        intro hcard_one
        exact hG_pi (by
          intro p hp
          rw [hcard_one, Nat.primeFactors_one] at hp
          simp at hp)
      have hG_card_gt_one : 1 < Nat.card G :=
        Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨Nat.card_pos.ne', hG_card_ne_one⟩
      have : Nontrivial G := Finite.one_lt_card_iff_nontrivial.mp hG_card_gt_one
      obtain ⟨M, hM_normal, hM_inv, hM_ne_bot, hM_min⟩ :=
        exists_minimal_normal_aInvariant (G := G) (A := A) (φ := φ)
      have : M.Normal := hM_normal
      obtain ⟨p, hp_prime, hM_p⟩ :=
        exists_prime_isPGroup_of_minimal_normal_aInvariant hM_inv hM_ne_bot hM_min
      have : Fact p.Prime := ⟨hp_prime⟩
      have hquot_lt : Nat.card (G ⧸ M) < Nat.card G :=
        card_quotient_lt_card_of_ne_bot hM_ne_bot
      have hquot_le_n : Nat.card (G ⧸ M) ≤ n := by
        omega
      have hKbar_pi :
          OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup π (K.map (QuotientGroup.mk' M)) :=
        isPiGroup_map_mk' (N := M) hK_pi
      have hKbar_inv :
          OddOrder.Isaacs.Ch03.IsAInvariant
            (quotientMulAutHom hM_inv) (K.map (QuotientGroup.mk' M)) :=
        isAInvariant_map_mk' hM_inv hK_inv
      have hCop_quot : Nat.Coprime (Nat.card A) (Nat.card (G ⧸ M)) :=
        coprime_card_quotient_of_coprime (N := M) hCop
      obtain ⟨Hbar, hHbar_hall, hHbar_inv, hKbar_le⟩ :=
        ih (G ⧸ M) A hquot_le_n hCop_quot hKbar_pi hKbar_inv
      obtain ⟨H, hH_inv, hK_le_H, hH_index, hH_eq⟩ :=
        quotient_hall_preimage_frame hM_inv hHbar_hall hHbar_inv hKbar_le
      by_cases hH_top : H = ⊤
      · have hHbar_top : Hbar = ⊤ := by
          apply eq_top_iff.mpr
          intro y hy
          obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (N := M) y
          have hgH : g ∈ H := by
            rw [hH_top]
            trivial
          rw [hH_eq] at hgH
          exact hgH
        have hquot_pi : ∀ q ∈ (Nat.card (G ⧸ M)).primeFactors, q ∈ π := by
          have htop_hall :
              OddOrder.Isaacs.Ch03.IsHallSubgroup π (⊤ : Subgroup (G ⧸ M)) := by
            simpa [hHbar_top] using hHbar_hall
          exact (OddOrder.Isaacs.Ch03.IsHallSubgroup.top_iff (G := G ⧸ M) π).mp
            htop_hall
        exact top_preimage_branch_frame hCop hG_pi hM_inv hM_p hquot_pi hK_pi hK_inv
      · have hH_le_n : Nat.card H ≤ n := by
          have hH_lt : Nat.card H < Nat.card G :=
            subgroup_card_lt_card_of_ne_top hH_top
          omega
        have hCop_H : Nat.Coprime (Nat.card A) (Nat.card H) :=
          coprime_card_subgroup_of_coprime (H := H) hCop
        have hIH_H : ∀ {Ksub : Subgroup H},
            OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup π Ksub →
              OddOrder.Isaacs.Ch03.IsAInvariant hH_inv.restrict Ksub →
              ∃ L : Subgroup H,
                OddOrder.Isaacs.Ch03.IsHallSubgroup π L ∧
                  OddOrder.Isaacs.Ch03.IsAInvariant hH_inv.restrict L ∧ Ksub ≤ L := by
          intro Ksub hKsub_pi hKsub_inv
          exact ih H A hH_le_n hCop_H hKsub_pi hKsub_inv
        exact proper_overgroup_branch_frame hH_inv hH_index hK_pi hK_inv hK_le_H hIH_H

/-- **BG Prop 1.5(b)**: if a finite solvable group `G` is acted on by a finite operator
 group `A` with coprime order, every `A`-invariant `π`-subgroup is contained in an
`A`-invariant Hall `π`-subgroup. -/
theorem aInvariant_piSubgroup_le_aInvariant_hall
    {G A : Type*} [Group G] [Finite G] [Group.IsSolvable G]
    [Group A] [Finite A] {φ : A →* MulAut G}
    (hCop : Nat.Coprime (Nat.card A) (Nat.card G))
    {π : Set ℕ} {K : Subgroup G}
    (hK_pi : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup π K)
    (hK_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ K) :
    ∃ H : Subgroup G,
      OddOrder.Isaacs.Ch03.IsHallSubgroup π H ∧
        OddOrder.Isaacs.Ch03.IsAInvariant φ H ∧ K ≤ H :=
  aInvariant_piSubgroup_le_aInvariant_hall_aux (Nat.card G) G A le_rfl hCop hK_pi hK_inv

/-- Complementary Hall subgroups have coprime orders. -/
private theorem hall_compl_card_coprime {G : Type*} [Group G] [Finite G]
    {π : Set ℕ} {K H : Subgroup G}
    (hK : OddOrder.Isaacs.Ch03.IsHallSubgroup {p | p ∉ π} K)
    (hH : OddOrder.Isaacs.Ch03.IsHallSubgroup π H) :
    Nat.Coprime (Nat.card K) (Nat.card H) := by
  have hHK : Nat.Coprime (Nat.card H) (Nat.card K) :=
    OddOrder.Isaacs.Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl
      Nat.card_pos.ne' Nat.card_pos.ne'
      hH.1
      (fun p hp => by simpa using hK.1 p hp)
  exact hHK.symm

/-- The index of a `π'`-Hall subgroup and the index of a `π`-Hall subgroup are coprime. -/
private theorem hall_compl_index_coprime {G : Type*} [Group G] [Finite G]
    {π : Set ℕ} {K H : Subgroup G}
    (hK : OddOrder.Isaacs.Ch03.IsHallSubgroup {p | p ∉ π} K)
    (hH : OddOrder.Isaacs.Ch03.IsHallSubgroup π H) :
    Nat.Coprime K.index H.index := by
  refine OddOrder.Isaacs.Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl
    Subgroup.index_ne_zero_of_finite Subgroup.index_ne_zero_of_finite ?_ hH.2
  intro p hp
  by_contra hp_not
  exact hK.2 p hp hp_not

/-- If `K` is Hall `π'` and `H` is Hall `π`, then `|K| * |H| = |G|`. -/
private theorem hall_compl_card_mul {G : Type*} [Group G] [Finite G]
    {π : Set ℕ} {K H : Subgroup G}
    (hK : OddOrder.Isaacs.Ch03.IsHallSubgroup {p | p ∉ π} K)
    (hH : OddOrder.Isaacs.Ch03.IsHallSubgroup π H) :
    Nat.card K * Nat.card H = Nat.card G := by
  have h_card_cop : Nat.Coprime (Nat.card K) (Nat.card H) :=
    hall_compl_card_coprime hK hH
  have h_index_cop : Nat.Coprime H.index K.index :=
    (hall_compl_index_coprime hK hH).symm
  have hK_dvd_Hindex : Nat.card K ∣ H.index := by
    have hdiv : Nat.card K ∣ Nat.card H * H.index := by
      rw [Subgroup.card_mul_index H]
      exact Subgroup.card_subgroup_dvd_card K
    rw [mul_comm] at hdiv
    exact h_card_cop.dvd_of_dvd_mul_right hdiv
  have hHindex_dvd_K : H.index ∣ Nat.card K := by
    have hdivG : H.index ∣ Nat.card G :=
      ⟨Nat.card H, by rw [mul_comm, Subgroup.card_mul_index H]⟩
    have hdiv : H.index ∣ Nat.card K * K.index := by
      rwa [← Subgroup.card_mul_index K] at hdivG
    exact h_index_cop.dvd_of_dvd_mul_right hdiv
  have hK_card_eq : Nat.card K = H.index :=
    Nat.dvd_antisymm hK_dvd_Hindex hHindex_dvd_K
  calc
    Nat.card K * Nat.card H = H.index * Nat.card H := by rw [hK_card_eq]
    _ = Nat.card H * H.index := by rw [mul_comm]
    _ = Nat.card G := Subgroup.card_mul_index H

/-- Complementary Hall subgroups multiply bijectively. This is the Lean form of BG's
`G = K H` line in Prop. 1.5(e).

De-privatised (2026-06-20) for use in BG Theorem 15.2 (`S15_MF`), where the `K`-invariant
`{q}ᶜ`-Hall complement `D` of the normal Sylow `q`-subgroup `Q` of `M_σ` is built via
`exists_aInvariant_hall` and shown to complement `Q` by this lemma. -/
theorem hall_compl_isComplement {G : Type*} [Group G] [Finite G]
    {π : Set ℕ} {K H : Subgroup G}
    (hK : OddOrder.Isaacs.Ch03.IsHallSubgroup {p | p ∉ π} K)
    (hH : OddOrder.Isaacs.Ch03.IsHallSubgroup π H) :
    Subgroup.IsComplement' K H :=
  Subgroup.isComplement'_of_coprime (hall_compl_card_mul hK hH)
    (hall_compl_card_coprime hK hH)

/-- **BG Prop 1.6(d)**: if `G` is abelian, then
`G = C_G(A) × [G,A]`.

Lean packages the internal direct product as a complement: multiplication from
`C_G(A) × [G,A]` onto `G` is bijective. -/
theorem fixedPoints_isComplement_actionCommutator_of_abelian
    {G A : Type*} [CommGroup G] [Finite G] [Group.IsSolvable G]
    [Group A] [Finite A] {φ : A →* MulAut G}
    (hCop : Nat.Coprime (Nat.card A) (Nat.card G)) :
    Subgroup.IsComplement' (Subgroup.fixedPointsOfMulAut φ)
      (OddOrder.Isaacs.Ch04.actionCommutator φ) := by
  have hsup : Subgroup.fixedPointsOfMulAut φ ⊔
      OddOrder.Isaacs.Ch04.actionCommutator φ = ⊤ :=
    OddOrder.Isaacs.Ch04.fixedPoints_sup_actionCommutator_eq_top
      (φ := φ) hCop (Or.inr inferInstance)
  have hinf : Subgroup.fixedPointsOfMulAut φ ⊓
      OddOrder.Isaacs.Ch04.actionCommutator φ = ⊥ :=
    OddOrder.Isaacs.Ch04.fixedPoints_inf_actionCommutator_eq_bot_of_abelian φ hCop
  apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
  · rw [disjoint_iff]
    exact hinf
  · rw [Set.eq_univ_iff_forall]
    intro g
    have hg : g ∈ Subgroup.fixedPointsOfMulAut φ ⊔
        OddOrder.Isaacs.Ch04.actionCommutator φ := by
      rw [hsup]
      trivial
    rw [Subgroup.mem_sup_of_normal_right] at hg
    obtain ⟨c, hc, d, hd, hcd⟩ := hg
    exact ⟨c, hc, d, hd, hcd⟩

end AInvariantHall

end OddOrder.BG.Ch1.S01


