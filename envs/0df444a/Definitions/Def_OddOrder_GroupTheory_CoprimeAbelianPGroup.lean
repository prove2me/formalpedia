-- Prove2me | Definitions.Def_OddOrder_GroupTheory_CoprimeAbelianPGroup
-- name    : OddOrder_GroupTheory_CoprimeAbelianPGroup
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:26:01.638949+00:00
-- url     : https://prove2.me/theorems/2610a9d0-3099-4c3f-b006-e2668dd4da86
-- title:
--   Gorenstein Ch. 3 §2: $p'$-automorphisms of abelian $p$-groups
-- statement:
--   Coprime ($p'$-)automorphism action on a finite abelian $p$-group, following Gorenstein, *Finite Groups* (1968), Chapter 3 §2. This is precursor material for BG §4 Lemma 4.13 (Gorenstein Theorem 4.15(ii)): the structure of a minimal invariant subgroup on which a $p'$-automorphism acts nontrivially.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 1 supporting lemma used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/CoprimeAbelianPGroup.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/CoprimeAbelianPGroup.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_CommutatorBasics
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ThreeSubgroupsCoprime
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_BaerTrick
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ChainNilpotent
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_ForwardFromCh03
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ThreeSubgroups
import Definitions.Def_OddOrder_GroupTheory_OmegaSubgroup

namespace OddOrder.GroupTheory

open OddOrder.Isaacs.Ch04

variable {A G : Type*} [Group A]

/-- **Gorenstein "Finite Groups" Theorem 2.4** (Chapter 3 §2). Let `A` be a `p′`-group of
automorphisms of a finite abelian `p`-group `G` (`φ : A →* MulAut G`, `(|A|, |G|) = 1`). If
`A` acts trivially on `Ω₁(G)` (every element of order dividing `p` is fixed), then `A` acts
trivially on all of `G`, i.e. `[G, A] = ⊥`.

Proof (Gorenstein, via Theorem 2.3): `G = C_G(A) × [G, A]`, so `C_G(A) ⊓ [G, A] = ⊥`. If
`[G, A] ≠ ⊥` it is a nontrivial `p`-group, hence (Cauchy) contains an element `x` of order
`p`; then `x ∈ Ω₁(G) ⊆ C_G(A)`, so `x ∈ C_G(A) ⊓ [G, A] = ⊥`, contradicting `x ≠ 1`.

This is the abelian special case of Gorenstein Theorem 3.10 and the `Ω₁`-extension feeding
Theorem 3.7 (precursor 2 of BG Lemma 4.13). -/
theorem actionCommutator_eq_bot_of_omega1_le_fixedPoints
    [CommGroup G] [Finite A] [Finite G] {p : ℕ} [Fact p.Prime]
    (φ : A →* MulAut G) (hCop : Nat.Coprime (Nat.card A) (Nat.card G))
    (hG : IsPGroup p G)
    (htriv : Omega G p 1 ≤ Subgroup.fixedPointsOfMulAut φ) :
    actionCommutator φ = ⊥ := by
  classical
  have hinf : Subgroup.fixedPointsOfMulAut φ ⊓ actionCommutator φ = ⊥ :=
    fixedPoints_inf_actionCommutator_eq_bot_of_abelian φ hCop
  by_contra hH
  -- `H := [G, A]` is a nontrivial `p`-group; extract an order-`p` element (Cauchy).
  have hHne : Nontrivial (actionCommutator φ) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr hH
  have hHp : IsPGroup p (actionCommutator φ) := hG.to_subgroup _
  have : Fintype (actionCommutator φ) := Fintype.ofFinite _
  have hpH : p ∣ Nat.card (actionCommutator φ) := by
    rcases hHp.card_eq_or_dvd with h1 | hd
    · exact absurd h1 (by simpa using (Finite.one_lt_card (α := actionCommutator φ)).ne')
    · exact hd
  have hpH' : p ∣ Fintype.card (actionCommutator φ) := by rwa [Nat.card_eq_fintype_card] at hpH
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card (G := actionCommutator φ) p hpH'
  have hxp : (x : G) ^ p = 1 := by
    have hxp1 : x ^ p = 1 := hx ▸ pow_orderOf_eq_one x
    exact_mod_cast hxp1
  have hx_ne : (x : G) ≠ 1 := by
    rw [Ne, OneMemClass.coe_eq_one]
    intro h; rw [h, orderOf_one] at hx; exact (Fact.out : p.Prime).ne_one hx.symm
  have hx_omega : (x : G) ∈ Omega G p 1 :=
    Omega.mem_of_pow_eq_one (by rw [pow_one]; exact hxp)
  have hx_inf : (x : G) ∈ Subgroup.fixedPointsOfMulAut φ ⊓ actionCommutator φ :=
    Subgroup.mem_inf.mpr ⟨htriv hx_omega, x.2⟩
  rw [hinf, Subgroup.mem_bot] at hx_inf
  exact hx_ne hx_inf

end OddOrder.GroupTheory


