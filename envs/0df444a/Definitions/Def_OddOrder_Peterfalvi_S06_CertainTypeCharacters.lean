-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S06_CertainTypeCharacters
-- name    : OddOrder_Peterfalvi_S06_CertainTypeCharacters
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T06:01:11.653631+00:00
-- url     : https://prove2.me/theorems/172cb8fe-1712-40a0-ae3b-d200098ebeb3
-- title:
--   Peterfalvi §6 (4.3.b): the certain-type characters
-- statement:
--   Peterfalvi, *Character Theory for the Odd Order Theorem*, §6, pp. 21-24. Building on the §6 structural hypothesis and its TI/Dade infrastructure (the TI set $W-W_2$, the cyclic $W=W_1\sqcup W_2$ and the §4 Dade isometry package), this file produces the certain-type characters of (4.3.b).
--
--   Helper definitions include `cyclicGenerator`, `cyclicPowEnum` (the power enumeration $i\mapsto\gamma^i$ of a finite cyclic group) and `omegaColumnDiff` (the column difference $\omega_{ij}-\omega_{kj}$), with many supporting facts on the $W_1$-dual.
--
--   The bundle also proves 15 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S06_CertainTypeCharacters.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S06_CertainTypeCharacters.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S05_SigmaIsometry
import Definitions.Def_OddOrder_Peterfalvi_S06_DadeIsometryCertain
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_IsometryDifferencePair
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_InflationCharacter

namespace OddOrder.Peterfalvi.S06

open OddOrder.RepresentationTheory

open OddOrder.Peterfalvi.S05

variable {L : Type*} [Group L] [Fintype L]

/-- Within a fixed `W₂`-column, the linear character `ω_{ij} = omegaProdChar χ₁ χ₂`
evaluated on `W₂` is independent of the `W₁`-index `χ₁`: on `W₂` the `W₁`-projection
`wFst` is trivial, so `omegaProdChar χ₁ χ₂ = χ₂ ∘ wSnd` there. -/
theorem omegaProdChar_apply_of_mem_W2 (hyp : TICyclicHypothesis L)
    (χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ) (χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ)
    {w : hyp.W} (hw : w ∈ hyp.W2.subgroupOf hyp.W) :
    hyp.omegaProdChar χ₁ χ₂ w = χ₂ (hyp.wSnd w) := by
  have h1 : hyp.omegaProdChar χ₁ χ₂ w = χ₁ (hyp.wFst w) * χ₂ (hyp.wSnd w) := rfl
  rw [h1, hyp.wFst_eq_one_of_mem_W2 hw, map_one, one_mul]

/-- The column difference `ω_{ij} − ω_{kj}` (same `W₂`-index `χ₂`) vanishes on `W₂`:
both characters restrict to `χ₂ ∘ wSnd` there (`omegaProdChar_apply_of_mem_W2`).
This is what makes the difference supported on the TI set `W − W₂` of (4.3.a). -/
theorem omega_omegaProdChar_sub_eq_zero_of_mem_W2 (hyp : TICyclicHypothesis L)
    (χ₁ χ₁' : (hyp.W1.subgroupOf hyp.W) →* ℂˣ) (χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ)
    {w : hyp.W} (hw : w ∈ hyp.W2.subgroupOf hyp.W) :
    ((hyp.omega (hyp.omegaProdChar χ₁ χ₂) : ClassFunction hyp.W ℂ) w
      - (hyp.omega (hyp.omegaProdChar χ₁' χ₂) : ClassFunction hyp.W ℂ) w) = 0 := by
  rw [TICyclicHypothesis.omega_apply, TICyclicHypothesis.omega_apply,
    omegaProdChar_apply_of_mem_W2 hyp χ₁ χ₂ hw,
    omegaProdChar_apply_of_mem_W2 hyp χ₁' χ₂ hw, sub_self]

/-- Characters in different `W₂`-columns are distinct: `ω_{aj} ≠ ω_{bj'}` when `j ≠ j'`
(`omegaProdChar` is injective in the index pair, `omegaProdChar_inj`). -/
theorem omegaProdChar_ne_of_ne_right (hyp : TICyclicHypothesis L)
    {χ₂ χ₂' : (hyp.W2.subgroupOf hyp.W) →* ℂˣ} (hne : χ₂ ≠ χ₂')
    (χ₁ χ₁' : (hyp.W1.subgroupOf hyp.W) →* ℂˣ) :
    hyp.omegaProdChar χ₁ χ₂ ≠ hyp.omegaProdChar χ₁' χ₂' :=
  hyp.omegaProdChar_ne (fun h => hne h.2)

/-- **Cross-column orthogonality of `ω`-differences**: for `χ₂ ≠ χ₂'`, the difference
`ω_{aj} − ω_{a₀j}` is orthogonal to `ω_{bj'} − ω_{b₀j'}`.  All four `ω`-terms have
distinct index pairs (the `W₂`-components differ), so each cross inner product vanishes
(`omega_inner_ne`).  This is the source-side input feeding (4.1) for the cross-column
distinctness of the certain-type characters. -/
theorem omega_diff_cross_inner_eq_zero (hyp : TICyclicHypothesis L)
    [Fintype hyp.W] [Invertible (Nat.card hyp.W : ℂ)]
    {χ₂ χ₂' : (hyp.W2.subgroupOf hyp.W) →* ℂˣ} (hne : χ₂ ≠ χ₂')
    (a a₀ b b₀ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ) :
    ClassFunction.inner
      ((hyp.omega (hyp.omegaProdChar a χ₂) : ClassFunction hyp.W ℂ)
        - (hyp.omega (hyp.omegaProdChar a₀ χ₂) : ClassFunction hyp.W ℂ))
      ((hyp.omega (hyp.omegaProdChar b χ₂') : ClassFunction hyp.W ℂ)
        - (hyp.omega (hyp.omegaProdChar b₀ χ₂') : ClassFunction hyp.W ℂ)) = 0 := by
  rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
    ClassFunction.inner_sub_right,
    hyp.omega_inner_ne (omegaProdChar_ne_of_ne_right hyp hne a b),
    hyp.omega_inner_ne (omegaProdChar_ne_of_ne_right hyp hne a b₀),
    hyp.omega_inner_ne (omegaProdChar_ne_of_ne_right hyp hne a₀ b),
    hyp.omega_inner_ne (omegaProdChar_ne_of_ne_right hyp hne a₀ b₀)]
  ring

/-- Biorthogonality (diagonal) for the `CF(W, W − W₂)` basis: `⟨ω_{ij} − ω_{0j}, ω_{ij}⟩ = 1`
(for `χ₁ ≠ 1`).  Only the `ω_{ij}` term survives; `ω_{0j} ⊥ ω_{ij}` since `χ₁ ≠ 1`. -/
theorem omegaColumnDiff_inner_omega_self (hyp : TICyclicHypothesis L)
    [Fintype hyp.W] [Invertible (Nat.card hyp.W : ℂ)]
    {χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ} (hχ₁ : χ₁ ≠ 1)
    (χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ) :
    ClassFunction.inner
      ((hyp.omega (hyp.omegaProdChar χ₁ χ₂) : ClassFunction hyp.W ℂ)
        - (hyp.omega (hyp.omegaProdChar 1 χ₂) : ClassFunction hyp.W ℂ))
      (hyp.omega (hyp.omegaProdChar χ₁ χ₂) : ClassFunction hyp.W ℂ) = 1 := by
  rw [ClassFunction.inner_sub_left, hyp.omega_inner_self,
    hyp.omega_inner_ne (hyp.omegaProdChar_ne (fun h => hχ₁ h.1.symm))]
  ring

/-- Biorthogonality (off-diagonal) for the `CF(W, W − W₂)` basis: `⟨ω_{i'j'} − ω_{0j'}, ω_{ij}⟩ = 0`
for `(i', j') ≠ (i, j)` (`χ₁ ≠ 1`).  Both `ω`-terms are distinct from `ω_{ij}`. -/
theorem omegaColumnDiff_inner_omega_ne (hyp : TICyclicHypothesis L)
    [Fintype hyp.W] [Invertible (Nat.card hyp.W : ℂ)]
    {χ₁' χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ} (hχ₁ : χ₁ ≠ 1)
    {χ₂' χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ} (hne : ¬ (χ₁' = χ₁ ∧ χ₂' = χ₂)) :
    ClassFunction.inner
      ((hyp.omega (hyp.omegaProdChar χ₁' χ₂') : ClassFunction hyp.W ℂ)
        - (hyp.omega (hyp.omegaProdChar 1 χ₂') : ClassFunction hyp.W ℂ))
      (hyp.omega (hyp.omegaProdChar χ₁ χ₂) : ClassFunction hyp.W ℂ) = 0 := by
  rw [ClassFunction.inner_sub_left,
    hyp.omega_inner_ne (hyp.omegaProdChar_ne hne),
    hyp.omega_inner_ne (hyp.omegaProdChar_ne (fun h => hχ₁ h.1.symm))]
  ring

/-- A virtual character `ψ` of a finite group `H` that vanishes off the identity has degree
divisible by `|H|`: `ψ(1) = |H|·m` for some integer `m` (the multiplicity `⟨ψ, 1_H⟩` of the
trivial character).  The masking sum `|H|·⟨ψ, 1_H⟩ = ∑_x ψ(x)` collapses to the single
identity term. -/
theorem exists_apply_one_eq_card_mul_of_vanishing_off_one {H : Type*} [Group H] [Finite H]
    [Invertible (Nat.card H : ℂ)] {ψ : ClassFunction H ℂ} (hψ : ψ ∈ ZIrr H)
    (hvan : ∀ x : H, x ≠ 1 → ψ x = 0) :
    ∃ m : ℤ, ψ 1 = (Nat.card H : ℂ) * (m : ℂ) := by
  have : Fintype H := Fintype.ofFinite H
  obtain ⟨m, hm⟩ :=
    ClassFunction.inner_mem_ZIrr_int hψ (trivialClassFunction_isIrreducible (G := H)).mem_ZIrr
  refine ⟨m, ?_⟩
  have hsum : ClassFunction.innerSum ψ (trivialClassFunction H) = ψ 1 := by
    rw [ClassFunction.innerSum,
      Finset.sum_eq_single (1 : H) (fun b _ hb => by rw [hvan b hb, zero_mul])
        (fun hb => absurd (Finset.mem_univ (1 : H)) hb),
      trivialClassFunction_apply, star_one, mul_one]
  have hcard := ClassFunction.card_mul_inner ψ (trivialClassFunction H)
  rw [hsum, hm] at hcard
  exact hcard.symm

section CyclicPowEnum

variable (D : Type*) [Group D] [Finite D] [IsCyclic D]

open Subgroup in
/-- A generator of a finite cyclic group (a choice fixed once and for all). -/
noncomputable def cyclicGenerator : D :=
  (IsCyclic.exists_generator (α := D)).choose

open Subgroup in
omit [Finite D] in
theorem forall_mem_zpowers_cyclicGenerator : ∀ x : D, x ∈ zpowers (cyclicGenerator D) :=
  (IsCyclic.exists_generator (α := D)).choose_spec

omit [Finite D] in
theorem orderOf_cyclicGenerator : orderOf (cyclicGenerator D) = Nat.card D :=
  orderOf_eq_card_of_forall_mem_zpowers (forall_mem_zpowers_cyclicGenerator D)

variable {D} {n : ℕ}

/-- The power enumeration `i ↦ γ^i : Fin n ≃ D` of a finite cyclic group of order `n`. -/
noncomputable def cyclicPowEnum (hn : Nat.card D = n) : Fin n ≃ D :=
  Equiv.ofBijective (fun i => cyclicGenerator D ^ (i : ℕ)) (by
    classical
    have hord : orderOf (cyclicGenerator D) = n := (orderOf_cyclicGenerator D).trans hn
    constructor
    · intro i j hij
      exact Fin.ext (pow_injOn_Iio_orderOf
        (by rw [hord]; exact i.2) (by rw [hord]; exact j.2) hij)
    · intro x
      have hx := forall_mem_zpowers_cyclicGenerator D x
      rw [mem_zpowers_iff_mem_range_orderOf] at hx
      obtain ⟨k, hk, hkx⟩ := Finset.mem_image.mp hx
      exact ⟨⟨k, hord ▸ Finset.mem_range.mp hk⟩, hkx⟩)

@[simp] theorem cyclicPowEnum_apply (hn : Nat.card D = n) (i : Fin n) :
    cyclicPowEnum hn i = cyclicGenerator D ^ (i : ℕ) :=
  rfl

end CyclicPowEnum

namespace Hypothesis

variable (h : Hypothesis L)

/-- The column difference `ω_{ij} − ω_{kj}` (same `W₂`-index `χ₂`) packaged as an
element of `CF(W, W − W₂)`, the supported class-function space of the sdiff
TI-cyclic hypothesis (4.3.a).  Membership uses
`omega_omegaProdChar_sub_eq_zero_of_mem_W2`: the difference vanishes on `W₂`. -/
noncomputable def omegaColumnDiff
    (χ₁ χ₁' : (h.W1.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ)
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) :
    TICyclicHypothesis.SupportedOnV ℂ h.sdiffTICyclicHypothesis :=
  ⟨(h.sdiffTICyclicHypothesis.omega (h.sdiffTICyclicHypothesis.omegaProdChar χ₁ χ₂) :
        ClassFunction h.sdiffTICyclicHypothesis.W ℂ)
      - (h.sdiffTICyclicHypothesis.omega (h.sdiffTICyclicHypothesis.omegaProdChar χ₁' χ₂) :
        ClassFunction h.sdiffTICyclicHypothesis.W ℂ),
   by
    rw [ClassFunction.mem_supportedSubmodule]
    intro w hw
    rw [ClassFunction.mem_support] at hw
    rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]
    refine ⟨w.2, ?_⟩
    intro hW2
    refine hw ?_
    rw [ClassFunction.sub_apply]
    exact omega_omegaProdChar_sub_eq_zero_of_mem_W2 h.sdiffTICyclicHypothesis χ₁ χ₁' χ₂
      ((Subgroup.mem_subgroupOf).mpr hW2)⟩

omit [Fintype L] in
/-- `1 < w₁` (it is `≥ 3`), giving a nonzero index `⟨1, _⟩ : Fin w₁` for the (4.1)
witnesses in the cross-column distinctness argument. -/
theorem one_lt_card_W1 [Finite L] : 1 < Nat.card h.W1 := by
  have : Fintype L := Fintype.ofFinite L
  have h3 : 3 ≤ Nat.card h.W1 := h.sdiffTICyclicHypothesis.three_le_card_W1
  omega

omit [Fintype L] in
/-- The `W₁`-dual is cyclic (`isCyclic_charGroup_subgroupOf`), recorded for the power
enumeration below. -/
theorem isCyclic_w1CharGroup [Finite L] : IsCyclic ((h.W1.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) := by
  have : Fintype L := Fintype.ofFinite L
  exact h.sdiffTICyclicHypothesis.isCyclic_charGroup_subgroupOf h.sdiffTICyclicHypothesis.W1_le_W

/-- The reindexing `Fin w₁ ≃ Ŵ₁`, realized as the **power enumeration** `i ↦ γ^i` of a fixed
generator `γ` of the cyclic dual (`isCyclic_w1CharGroup`, Pontryagin self-duality
`card_charGroup_subgroupOf`: `|Ŵ₁| = |W₁| = w₁`).  This is Peterfalvi's own indexing of the
grid by character powers ((3.5)): `0 ↦ γ^0 = 1` keeps the distinguished base index of the
(1.4) machinery (`w1CharEquiv_zero`), and index negation is character inversion
(`w1CharEquiv_finNeg`) — the honest form of the (3.9.a) grid pairing (issue 3002; an
arbitrary enumeration falsifies the `finNeg` pairing). -/
noncomputable def w1CharEquiv [NeZero (Nat.card h.W1)] :
    Fin (Nat.card h.W1) ≃ ((h.W1.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) :=
  haveI := h.isCyclic_w1CharGroup
  cyclicPowEnum (h.sdiffTICyclicHypothesis.card_charGroup_subgroupOf
    h.sdiffTICyclicHypothesis.W1_le_W)

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem w1CharEquiv_zero [NeZero (Nat.card h.W1)] : h.w1CharEquiv 0 = 1 := by
  have := h.isCyclic_w1CharGroup
  rw [w1CharEquiv, cyclicPowEnum_apply]
  simp

theorem w1CharEquiv_injective [NeZero (Nat.card h.W1)] :
    Function.Injective h.w1CharEquiv :=
  h.w1CharEquiv.injective

@[simp] theorem omegaColumnDiff_coe
    (χ₁ χ₁' : (h.W1.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ)
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) :
    ((h.omegaColumnDiff χ₁ χ₁' χ₂ : TICyclicHypothesis.SupportedOnV ℂ h.sdiffTICyclicHypothesis) :
        ClassFunction h.sdiffTICyclicHypothesis.W ℂ)
      = (h.sdiffTICyclicHypothesis.omega (h.sdiffTICyclicHypothesis.omegaProdChar χ₁ χ₂) :
          ClassFunction h.sdiffTICyclicHypothesis.W ℂ)
        - (h.sdiffTICyclicHypothesis.omega (h.sdiffTICyclicHypothesis.omegaProdChar χ₁' χ₂) :
          ClassFunction h.sdiffTICyclicHypothesis.W ℂ) :=
  rfl

/-- **The `W₂`-column character family** `i ↦ ω_{e i, j}` of (4.3.b): with `χ₂ = j`
a fixed nontrivial `W₂`-dual and `e = w1CharEquiv` (`e 0 = 1`), the linear characters
`ω_{ij} = ω(omegaProdChar (e i) χ₂)` of `W = W₁ ⊔ W₂`, indexed by `Fin w₁` with
distinguished index `0 ↦ ω_{0j}`.  This is the source family of the (1.4) machinery. -/
noncomputable def chiColumn [NeZero (Nat.card h.W1)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1)) :
    IrreducibleCharacter h.sdiffTICyclicHypothesis.W :=
  h.sdiffTICyclicHypothesis.omega
    (h.sdiffTICyclicHypothesis.omegaProdChar (h.w1CharEquiv i) χ₂)

theorem chiColumn_zero [NeZero (Nat.card h.W1)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) :
    h.chiColumn χ₂ 0 =
      h.sdiffTICyclicHypothesis.omega (h.sdiffTICyclicHypothesis.omegaProdChar 1 χ₂) :=
  congrArg
    (fun c => h.sdiffTICyclicHypothesis.omega (h.sdiffTICyclicHypothesis.omegaProdChar c χ₂))
    h.w1CharEquiv_zero

/-- The column family is injective (`ω`, `omegaProdChar(·, χ₂)`, and `w1CharEquiv` are). -/
theorem chiColumn_injective [NeZero (Nat.card h.W1)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) :
    Function.Injective (h.chiColumn χ₂) := by
  intro i j hij
  exact h.w1CharEquiv_injective
    (h.sdiffTICyclicHypothesis.omegaProdChar_inj
      (h.sdiffTICyclicHypothesis.omega_injective hij)).1

/-- Every member of the column family has degree one (`ω` is linear). -/
@[simp] theorem chiColumn_apply_one [NeZero (Nat.card h.W1)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1)) :
    ((h.chiColumn χ₂ i : ClassFunction h.sdiffTICyclicHypothesis.W ℂ)) 1 = 1 :=
  h.sdiffTICyclicHypothesis.omega_apply_one _

set_option backward.isDefEq.respectTransparency false in
/-- Value of the `j = 0` column character: `ω_{i0}(w) = (w1CharEquiv i)(wFst w)` — the `W₂`-dual
`χ₂ = 1` is trivial on the `W₂`-component, so only the `W₁`-component survives. -/
theorem chiColumn_one_apply [NeZero (Nat.card h.W1)] (i : Fin (Nat.card h.W1))
    (w : ↥h.sdiffTICyclicHypothesis.W) :
    (h.chiColumn 1 i : ClassFunction h.sdiffTICyclicHypothesis.W ℂ) w
      = ((h.w1CharEquiv i) (h.sdiffTICyclicHypothesis.wFst w) : ℂ) := by
  rw [chiColumn, h.sdiffTICyclicHypothesis.omega_apply]
  congr 1
  change (h.w1CharEquiv i) (h.sdiffTICyclicHypothesis.wFst w)
      * (1 : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (h.sdiffTICyclicHypothesis.wSnd w)
      = (h.w1CharEquiv i) (h.sdiffTICyclicHypothesis.wFst w)
  rw [MonoidHom.one_apply, mul_one]

/-- The normal subgroup `K ⊴ L` of Hypothesis (4.2), as an instance (so quotients `L ⧸ K`
elaborate). -/
instance instKNormal : h.K.Normal := h.K_normal

omit [Fintype L] in
/-- `L/K` is cyclic: it is isomorphic to the cyclic complement `W₁`
(`Subgroup.IsComplement'.QuotientMulEquiv`). -/
theorem isCyclic_quotient_K : IsCyclic (L ⧸ h.K) := by
  have := h.W1_cyclic
  exact isCyclic_of_surjective
    (h.isComplement.symm.QuotientMulEquiv.symm : (↥h.W1) →* (L ⧸ h.K))
    (h.isComplement.symm.QuotientMulEquiv.symm).surjective

omit [Fintype L] in
/-- `L/K` is abelian (it is cyclic, `isCyclic_quotient_K`).  This is what makes an irreducible
character of `L` whose kernel contains `K` linear (degree one) — the engine of the forward
direction of (4.4). -/
theorem isMulCommutative_quotient_K : IsMulCommutative (L ⧸ h.K) := by
  have := h.isCyclic_quotient_K
  infer_instance

section Recipe

variable [Invertible (Nat.card L : ℂ)]
  [Fintype ↥(h.W1 ⊔ h.W2)]
  [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]

/-- Bridge instances: `Fintype`/`Invertible` for the order of `h.sdiffTICyclicHypothesis.W`,
definitionally `W₁ ⊔ W₂`.  Let `Ind_W^L`, `card_charGroup` and the §4 Dade package resolve
when the source group appears in its `sdiffTICyclicHypothesis.W` form. -/
instance instFintypeSdiffW : Fintype ↥h.sdiffTICyclicHypothesis.W :=
  ‹Fintype ↥(h.W1 ⊔ h.W2)›

instance instInvertibleCardSdiffW :
    Invertible (Nat.card ↥h.sdiffTICyclicHypothesis.W : ℂ) :=
  ‹Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)›

instance instFintypeToTICyclicW : Fintype ↥h.toTICyclicHypothesis.W :=
  ‹Fintype ↥(h.W1 ⊔ h.W2)›

instance instInvertibleCardToTICyclicW :
    Invertible (Nat.card ↥h.toTICyclicHypothesis.W : ℂ) :=
  ‹Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)›

/-- `Ind_W^L` as a `ℤ`-linear map `CF(W) →ₗ[ℤ] CF(L)`, the map fed to the (1.4)
orthonormal difference-pair machinery (`isometry_difference_pair_structure`). -/
noncomputable def induceZ :
    ClassFunction h.sdiffTICyclicHypothesis.W ℂ →ₗ[ℤ] ClassFunction L ℂ :=
  (h.sdiffTICyclicHypothesis.induceLinear).restrictScalars ℤ

omit [Invertible (Nat.card L : ℂ)] in
omit [Fintype ↥(h.W1 ⊔ h.W2)] in
/-- The (1.4) image `τ(χ_i − χ_0)` of the column family is the induced difference
`Ind_W^L(ω_{ij} − ω_{0j})` — definitionally, since `induceZ` is `Ind_W^L` and
`isometryDifferenceImage` is the image of the source difference. -/
theorem isometryDifferenceImage_induceZ [NeZero (Nat.card h.W1)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1)) :
    isometryDifferenceImage h.induceZ (h.chiColumn χ₂) i =
      ClassFunction.induce h.sdiffTICyclicHypothesis.W
        ((h.chiColumn χ₂ i : ClassFunction h.sdiffTICyclicHypothesis.W ℂ)
          - (h.chiColumn χ₂ 0 : ClassFunction h.sdiffTICyclicHypothesis.W ℂ)) :=
  rfl

/-- The `W₂`-column image of the (1.4) map is the Dade isometry of the column
difference: `Ind_W^L(ω_{ij} − ω_{0j}) = τ_{W−W₂}(ω_{ij} − ω_{0j})`, because on the
TI set `W − W₂` the Dade map *is* `Ind_W^L` (`tau_eq_induce`).  This is the bridge
that transfers the isometry property of the §4 Dade package to `Ind_W^L`. -/
theorem isometryDifferenceImage_eq_dade [NeZero (Nat.card h.W1)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1)) :
    isometryDifferenceImage h.induceZ (h.chiColumn χ₂) i =
      h.sdiffFullDadeIsometryData.toDadeMap
        (h.omegaColumnDiff (h.w1CharEquiv i) (h.w1CharEquiv 0) χ₂) := by
  rw [isometryDifferenceImage_induceZ]
  exact (h.sdiffTICyclicHypothesis.tau_eq_induce
    h.sdiffFullDadeIsometryData.toDadeIsometryData
    (h.omegaColumnDiff (h.w1CharEquiv i) (h.w1CharEquiv 0) χ₂)).symm

omit [Fintype ↥(h.W1 ⊔ h.W2)] in
/-- **Peterfalvi (4.3.b), per-column signed family** (mmd 04.6, the (4.5) consumer of
(1.4)).  For a fixed nontrivial `W₂`-dual `χ₂` (a "column" `j`), the (1.4) machinery
applied to `Ind_W^L` and the column family `ω_{ij}` yields a signed irreducible-difference
family `{μ_{ij}, δ_j}` of `L` with

  `Ind_W^L(ω_{ij} − ω_{0j}) = δ_j • (μ_{ij} − μ_{0j})`,  `δ_j = ±1`,  `μ_{·j}` injective.

The three (1.4) hypotheses are discharged from the §6 infrastructure: virtual-character
images by `induce_mem_ZIrr`, vanishing at `1` by `induce_apply_one` (the source
difference has degree `0`), and the isometry on the differences by the §4 Dade package
on the TI set `W − W₂` (`sdiffFullDadeIsometryData`, via `isometryDifferenceImage_eq_dade`
and `full_inner_eq`).  Distinctness within the column is the `injective` field. -/
theorem exists_columnSignedFamily [NeZero (Nat.card h.W1)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) :
    ∃ data : SignedIrreducibleDifferenceFamily L (Nat.card h.W1),
      ∀ i, isometryDifferenceImage h.induceZ (h.chiColumn χ₂) i = data.signedDifference i := by
  have : Fintype ↥(h.W1 ⊔ h.W2) := Fintype.ofFinite _
  classical
  have hn : 2 ≤ Nat.card h.W1 := by
    have h3 : 3 ≤ Nat.card h.W1 := h.sdiffTICyclicHypothesis.three_le_card_W1
    omega
  -- Same degree: every member of the column family has degree one.
  have hdeg : ∀ i, ((h.chiColumn χ₂ i : ClassFunction h.sdiffTICyclicHypothesis.W ℂ) :
      h.sdiffTICyclicHypothesis.W → ℂ) 1 =
      ((h.chiColumn χ₂ 0 : ClassFunction h.sdiffTICyclicHypothesis.W ℂ) :
      h.sdiffTICyclicHypothesis.W → ℂ) 1 := by
    intro i
    rw [h.chiColumn_apply_one χ₂ i, h.chiColumn_apply_one χ₂ 0]
  -- (1.4.virtual): each image lies in `ℤ[Irr L]` (`Ind` of a difference of irreducibles).
  have h_image_virtual :
      IsometryDifferenceImagesAreVirtual h.induceZ (h.chiColumn χ₂) := by
    intro i
    rw [isometryDifferenceImage_induceZ]
    exact ClassFunction.induce_mem_ZIrr _
      (Submodule.sub_mem _ (h.chiColumn χ₂ i).mem_ZIrr (h.chiColumn χ₂ 0).mem_ZIrr)
  -- (1.4.degree): each image vanishes at `1` (`Ind` of a degree-0 difference).
  have h_image_degree_zero :
      IsometryDifferenceImagesVanishAtOne h.induceZ (h.chiColumn χ₂) := by
    intro i
    rw [isometryDifferenceImage_induceZ, ClassFunction.induce_apply_one,
      ClassFunction.sub_apply, h.chiColumn_apply_one χ₂ i, h.chiColumn_apply_one χ₂ 0,
      sub_self, mul_zero]
  -- (1.4.isometry): inner products preserved on the differences (the §4 Dade isometry).
  have h_isom : ∀ i j,
      ClassFunction.inner (isometryDifferenceImage h.induceZ (h.chiColumn χ₂) i)
        (isometryDifferenceImage h.induceZ (h.chiColumn χ₂) j) =
      ClassFunction.inner (irreducibleCharacterDifference (h.chiColumn χ₂) i)
        (irreducibleCharacterDifference (h.chiColumn χ₂) j) := by
    intro i j
    rw [h.isometryDifferenceImage_eq_dade χ₂ i, h.isometryDifferenceImage_eq_dade χ₂ j]
    exact (TICyclicHypothesis.full_inner_eq
      (⟨h.sdiffFullDadeIsometryData⟩ : TICyclicHypothesis.FullDadeApplication
        h.sdiffTICyclicHypothesis)
      (h.omegaColumnDiff (h.w1CharEquiv i) (h.w1CharEquiv 0) χ₂)
      (h.omegaColumnDiff (h.w1CharEquiv j) (h.w1CharEquiv 0) χ₂))
  exact isometry_difference_pair_structure (G := L)
    (H := h.sdiffTICyclicHypothesis.W) hn (h.chiColumn χ₂) (h.chiColumn_injective χ₂)
    hdeg h.induceZ h_image_virtual h_image_degree_zero h_isom

/-- A choice of the (1.4) signed irreducible-difference family for the `W₂`-column `χ₂`
(`exists_columnSignedFamily`): the data `{μ_{ij}, δ_j}` of (4.3.b). -/
noncomputable def columnFamily [NeZero (Nat.card h.W1)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) :
    SignedIrreducibleDifferenceFamily L (Nat.card h.W1) :=
  (h.exists_columnSignedFamily χ₂).choose

omit [Fintype ↥(h.W1 ⊔ h.W2)] in
theorem columnFamily_spec [NeZero (Nat.card h.W1)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1)) :
    isometryDifferenceImage h.induceZ (h.chiColumn χ₂) i =
      (h.columnFamily χ₂).signedDifference i :=
  (h.exists_columnSignedFamily χ₂).choose_spec i

omit [Fintype ↥(h.W1 ⊔ h.W2)] in
set_option backward.isDefEq.respectTransparency false in
/-- **Cross-column orthogonality of the (1.4) images** (4.3.b proof step): for `χ₂ ≠ χ₂'`,
`(Ind_W^L(ω_{ij} − ω_{0j}), Ind_W^L(ω_{i'j'} − ω_{0j'})) = 0`.  The §4 Dade map on
`CF(W, W − W₂)` is an isometry, so this equals the source cross inner product
`omega_diff_cross_inner_eq_zero`, which vanishes because the two columns use distinct
`W₂`-duals. -/
theorem ind_cross_inner_eq_zero [NeZero (Nat.card h.W1)]
    {χ₂ χ₂' : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ} (hne : χ₂ ≠ χ₂')
    (i i' : Fin (Nat.card h.W1)) :
    ClassFunction.inner (isometryDifferenceImage h.induceZ (h.chiColumn χ₂) i)
      (isometryDifferenceImage h.induceZ (h.chiColumn χ₂') i') = 0 := by
  have : Fintype ↥(h.W1 ⊔ h.W2) := Fintype.ofFinite _
  rw [h.isometryDifferenceImage_eq_dade χ₂ i, h.isometryDifferenceImage_eq_dade χ₂' i',
    h.sdiffFullDadeIsometryData.inner_eq, omegaColumnDiff_coe, omegaColumnDiff_coe]
  exact omega_diff_cross_inner_eq_zero h.sdiffTICyclicHypothesis hne _ _ _ _

omit [Invertible (Nat.card L : ℂ)] [Fintype ↥(h.W1 ⊔ h.W2)] in
/-- The (1.4) image of the column family vanishes at `1` (the source difference
`ω_{ij} − ω_{0j}` has degree `0`, and `Ind` preserves that). -/
theorem image_apply_one_eq_zero [NeZero (Nat.card h.W1)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1)) :
    isometryDifferenceImage h.induceZ (h.chiColumn χ₂) i (1 : L) = 0 := by
  have : Fintype ↥(h.W1 ⊔ h.W2) := Fintype.ofFinite _
  rw [isometryDifferenceImage_induceZ, ClassFunction.induce_apply_one,
    ClassFunction.sub_apply, h.chiColumn_apply_one χ₂ i, h.chiColumn_apply_one χ₂ 0,
    sub_self, mul_zero]

omit [Fintype ↥(h.W1 ⊔ h.W2)] in
/-- The signed differences `μ_{ij} − μ_{0j}` of the column family vanish at `1`
(same degree within a column), since the (1.4) image does and `δ_j ≠ 0`. -/
theorem columnFamily_difference_apply_one [NeZero (Nat.card h.W1)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1)) :
    (h.columnFamily χ₂).difference i (1 : L) = 0 := by
  have : Fintype ↥(h.W1 ⊔ h.W2) := Fintype.ofFinite _
  have h0 : (h.columnFamily χ₂).signedDifference i (1 : L) = 0 := by
    rw [← h.columnFamily_spec χ₂ i]; exact h.image_apply_one_eq_zero χ₂ i
  rw [SignedIrreducibleDifferenceFamily.signedDifference_apply, ClassFunction.zsmul_apply,
    zsmul_eq_mul] at h0
  have hs : ((h.columnFamily χ₂).sign : ℂ) ≠ 0 := by
    rcases (h.columnFamily χ₂).sign_eq with he | he <;> rw [he] <;> norm_num
  exact (mul_eq_zero.mp h0).resolve_left hs

omit [Fintype ↥(h.W1 ⊔ h.W2)] in
/-- **Cross-column orthogonality of the `μ`-differences** (4.3.b proof step): for `χ₂ ≠ χ₂'`,
`(μ_{ij} − μ_{0j}, μ_{i'j'} − μ_{0j'}) = 0`.  From the (1.4)-image cross orthogonality
(`ind_cross_inner_eq_zero`) after removing both signs `δ_j, δ_{j'} = ±1`. -/
theorem columnFamily_difference_cross_inner_eq_zero [NeZero (Nat.card h.W1)]
    {χ₂ χ₂' : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ} (hne : χ₂ ≠ χ₂')
    (i i' : Fin (Nat.card h.W1)) :
    ClassFunction.inner ((h.columnFamily χ₂).difference i)
      ((h.columnFamily χ₂').difference i') = 0 := by
  have : Fintype ↥(h.W1 ⊔ h.W2) := Fintype.ofFinite _
  have h0 := h.ind_cross_inner_eq_zero hne i i'
  rw [h.columnFamily_spec χ₂ i, h.columnFamily_spec χ₂' i',
    SignedIrreducibleDifferenceFamily.signedDifference_apply,
    SignedIrreducibleDifferenceFamily.signedDifference_apply,
    ← Int.cast_smul_eq_zsmul ℂ (h.columnFamily χ₂).sign ((h.columnFamily χ₂).difference i),
    ← Int.cast_smul_eq_zsmul ℂ (h.columnFamily χ₂').sign ((h.columnFamily χ₂').difference i'),
    ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
    star_intCast] at h0
  have hs : ((h.columnFamily χ₂).sign : ℂ) ≠ 0 := by
    rcases (h.columnFamily χ₂).sign_eq with he | he <;> rw [he] <;> norm_num
  have hs' : ((h.columnFamily χ₂').sign : ℂ) ≠ 0 := by
    rcases (h.columnFamily χ₂').sign_eq with he | he <;> rw [he] <;> norm_num
  exact (mul_eq_zero.mp ((mul_eq_zero.mp h0).resolve_left hs)).resolve_left hs'

omit [Fintype ↥(h.W1 ⊔ h.W2)] in
/-- **The four cross inner products vanish** (4.3.b proof step, via (4.1)).  For `χ₂ ≠ χ₂'`
and nonzero `k, k'`, the signed differences `μ_{kj} − μ_{0j}` and `μ_{k'j'} − μ_{0j'}` are
orthogonal (`columnFamily_difference_cross_inner_eq_zero`) and vanish at `1`
(`columnFamily_difference_apply_one`), so Peterfalvi (4.1) forces all four cross inner
products `(μ_{kj}, μ_{k'j'})`, `(μ_{kj}, μ_{0j'})`, `(μ_{0j}, μ_{k'j'})`, `(μ_{0j}, μ_{0j'})`
to vanish. -/
theorem columnFamily_cross_products_zero [NeZero (Nat.card h.W1)]
    {χ₂ χ₂' : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ} (hne : χ₂ ≠ χ₂')
    {k k' : Fin (Nat.card h.W1)} (hk : k ≠ 0) (hk' : k' ≠ 0) :
    ClassFunction.inner ((h.columnFamily χ₂).mu k : ClassFunction L ℂ)
        ((h.columnFamily χ₂').mu k' : ClassFunction L ℂ) = 0 ∧
      ClassFunction.inner ((h.columnFamily χ₂).mu k : ClassFunction L ℂ)
        ((h.columnFamily χ₂').mu 0 : ClassFunction L ℂ) = 0 ∧
      ClassFunction.inner ((h.columnFamily χ₂).mu 0 : ClassFunction L ℂ)
        ((h.columnFamily χ₂').mu k' : ClassFunction L ℂ) = 0 ∧
      ClassFunction.inner ((h.columnFamily χ₂).mu 0 : ClassFunction L ℂ)
        ((h.columnFamily χ₂').mu 0 : ClassFunction L ℂ) = 0 := by
  have : Fintype ↥(h.W1 ⊔ h.W2) := Fintype.ofFinite _
  have hself : ∀ (d : SignedIrreducibleDifferenceFamily L (Nat.card h.W1)) (m : Fin (Nat.card
      h.W1)),
      ClassFunction.inner (d.mu m : ClassFunction L ℂ) (d.mu m : ClassFunction L ℂ) = 1 := by
    intro d m; rw [irreducibleCharacter_inner, if_pos rfl]
  have horth : ∀ (d : SignedIrreducibleDifferenceFamily L (Nat.card h.W1))
      {m n : Fin (Nat.card h.W1)}, m ≠ n →
      ClassFunction.inner (d.mu m : ClassFunction L ℂ) (d.mu n : ClassFunction L ℂ) = 0 := by
    intro d m n hmn
    rw [irreducibleCharacter_inner, if_neg (fun heq => hmn (d.injective heq))]
  refine pairwise_inner_eq_zero_of_orthogonal_signedDifference (Γ := L)
    (u := 1) (v := 1) one_ne_zero one_ne_zero
    ((h.columnFamily χ₂).mu k).mem_ZIrr (hself _ k)
    ((h.columnFamily χ₂).mu 0).mem_ZIrr (hself _ 0)
    ((h.columnFamily χ₂').mu k').mem_ZIrr (hself _ k')
    ((h.columnFamily χ₂').mu 0).mem_ZIrr (hself _ 0)
    (horth _ hk) (horth _ hk') ?_ ?_ ?_
  · -- (μ_{kj} − μ_{0j}, 1•μ_{k'j'} − 1•μ_{0j'}) = 0
    simp only [Complex.ofReal_one, one_smul]
    exact h.columnFamily_difference_cross_inner_eq_zero hne k k'
  · -- (μ_{kj} − μ_{0j})(1) = 0
    exact h.columnFamily_difference_apply_one χ₂ k
  · -- (1•μ_{k'j'} − 1•μ_{0j'})(1) = 0
    simp only [Complex.ofReal_one, one_smul]
    exact h.columnFamily_difference_apply_one χ₂' k'

omit [Fintype ↥(h.W1 ⊔ h.W2)] in
/-- **Peterfalvi (4.3.b), cross-column distinctness**: certain-type characters from
different `W₂`-columns are distinct — `μ_{ij} ≠ μ_{i'j'}` for `χ₂ ≠ χ₂'` and any `i, i'`.
By `columnFamily_cross_products_zero` (the four cross inner products vanish, via (4.1)),
`(μ_{ij}, μ_{i'j'}) = 0`; orthogonal irreducibles are distinct.  A case split on `i, i' = 0`
selects which of the four products to read (the (4.1) witnesses use the nonzero index `1`). -/
theorem columnFamily_mu_ne [NeZero (Nat.card h.W1)]
    {χ₂ χ₂' : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ} (hne : χ₂ ≠ χ₂')
    (i i' : Fin (Nat.card h.W1)) :
    (h.columnFamily χ₂).mu i ≠ (h.columnFamily χ₂').mu i' := by
  have : Fintype ↥(h.W1 ⊔ h.W2) := Fintype.ofFinite _
  have hz : (⟨1, h.one_lt_card_W1⟩ : Fin (Nat.card h.W1)) ≠ 0 := Fin.ne_of_val_ne (by simp)
  have hinner : ClassFunction.inner ((h.columnFamily χ₂).mu i : ClassFunction L ℂ)
      ((h.columnFamily χ₂').mu i' : ClassFunction L ℂ) = 0 := by
    rcases eq_or_ne i 0 with hi | hi <;> rcases eq_or_ne i' 0 with hi' | hi'
    · subst hi; subst hi'
      exact (h.columnFamily_cross_products_zero hne hz hz).2.2.2
    · subst hi
      exact (h.columnFamily_cross_products_zero hne hz hi').2.2.1
    · subst hi'
      exact (h.columnFamily_cross_products_zero hne hi hz).2.1
    · exact (h.columnFamily_cross_products_zero hne hi hi').1
  intro heq
  rw [heq, irreducibleCharacter_inner, if_pos rfl] at hinner
  exact one_ne_zero hinner

omit [Invertible (Nat.card L : ℂ)] [Fintype ↥(h.W1 ⊔ h.W2)] in
/-- **Linear independence of the `CF(W, W − W₂)` family** `ω_{ij} − ω_{0j}` (`i ≠ 0`, all `j`):
the biorthogonal system `⟨ω_{i'j'} − ω_{0j'}, ω_{ij}⟩ = δ`
(`omegaColumnDiff_inner_omega_self`/`_ne`)
witnesses linear independence.  With the matching count `(w₁−1)·w₂ = |W − W₂| = dim CF(W, W − W₂)`
this gives the basis of (4.3.b) (the `ω_{ij} − ω_{0j}` comprise a basis of `CF(W, W − W₂)`). -/
theorem omegaColumnDiff_linearIndependent :
    LinearIndependent ℂ
      (fun p : {χ₁ : (h.W1.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ // χ₁ ≠ 1} ×
          ((h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) =>
        h.omegaColumnDiff p.1.1 1 p.2) := by
  have : Fintype ↥(h.W1 ⊔ h.W2) := Fintype.ofFinite _
  refine LinearIndependent.of_pairwise_dual_eq_zero_one _
    (fun p => (innerDual (h.sdiffTICyclicHypothesis.omega
        (h.sdiffTICyclicHypothesis.omegaProdChar p.1.1 p.2))).comp (Submodule.subtype _))
    (fun p q hpq => ?_) (fun p => ?_)
  · simp only [LinearMap.comp_apply, Submodule.subtype_apply, innerDual_apply, omegaColumnDiff_coe]
    exact omegaColumnDiff_inner_omega_ne h.sdiffTICyclicHypothesis p.1.2
      (fun heq => hpq (Prod.ext (Subtype.ext heq.1.symm) heq.2.symm))
  · simp only [LinearMap.comp_apply, Submodule.subtype_apply, innerDual_apply, omegaColumnDiff_coe]
    exact omegaColumnDiff_inner_omega_self h.sdiffTICyclicHypothesis p.1.2 p.2

omit [Fintype ↥(h.W1 ⊔ h.W2)] in
/-- **Peterfalvi (4.3.b), all certain-type characters distinct**: the global family
`(χ₂, i) ↦ μ_{ij}` is injective.  Within a column by the (1.4) `injective` field;
across columns by `columnFamily_mu_ne`. -/
theorem columnFamily_mu_injective [NeZero (Nat.card h.W1)] :
    Function.Injective
      (fun p : ((h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) × Fin (Nat.card h.W1) =>
        (h.columnFamily p.1).mu p.2) := by
  have : Fintype ↥(h.W1 ⊔ h.W2) := Fintype.ofFinite _
  rintro ⟨χ₂, i⟩ ⟨χ₂', i'⟩ heq
  by_cases hχ : χ₂ = χ₂'
  · subst hχ
    obtain rfl : i = i' := (h.columnFamily χ₂).injective heq
    rfl
  · exact absurd heq (h.columnFamily_mu_ne hχ i i')

omit [Invertible (Nat.card L : ℂ)] in
omit [Fintype ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)] in
/-- The count `|W − W₂| = (w₁ − 1)·w₂`: the support set of the sdiff hypothesis is the
complement of `W₂` in `W`, so `|W| − |W₂| = w₁w₂ − w₂`. -/
theorem card_supportInSubgroup_sdiff :
    Nat.card ↥(OddOrder.Peterfalvi.S04.supportInSubgroup h.sdiffTICyclicHypothesis.V
        h.sdiffTICyclicHypothesis.W) = (Nat.card h.W1 - 1) * Nat.card h.W2 := by
  classical
  have : Finite L := Finite.of_fintype L
  have : Fintype ↥h.sdiffTICyclicHypothesis.W := Fintype.ofFinite _
  have : Fintype ↥(h.W2.subgroupOf h.sdiffTICyclicHypothesis.W) := Fintype.ofFinite _
  have hmemiff : ∀ x : ↥h.sdiffTICyclicHypothesis.W,
      x ∈ OddOrder.Peterfalvi.S04.supportInSubgroup h.sdiffTICyclicHypothesis.V
        h.sdiffTICyclicHypothesis.W ↔ x ∉ h.W2.subgroupOf h.sdiffTICyclicHypothesis.W := by
    intro x
    rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup, Subgroup.mem_subgroupOf]
    exact ⟨fun hxV => hxV.2, fun hxW2 => ⟨SetLike.coe_mem x, hxW2⟩⟩
  have hcompl := Nat.card_congr (Equiv.subtypeEquivRight hmemiff)
  have hW : Nat.card ↥h.sdiffTICyclicHypothesis.W = Nat.card h.W1 * Nat.card h.W2 :=
    h.card_sup_eq_mul
  have hW2 : Nat.card ↥(h.W2.subgroupOf h.sdiffTICyclicHypothesis.W) = Nat.card h.W2 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.sdiffTICyclicHypothesis.W2_le_W).toEquiv
  have hsub : Nat.card {x : ↥h.sdiffTICyclicHypothesis.W //
        x ∉ h.W2.subgroupOf h.sdiffTICyclicHypothesis.W}
      = Nat.card ↥h.sdiffTICyclicHypothesis.W
        - Nat.card ↥(h.W2.subgroupOf h.sdiffTICyclicHypothesis.W) := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      Fintype.card_subtype_compl]
  rw [hcompl, hsub, hW, hW2, Nat.sub_one_mul]

omit [Invertible (Nat.card L : ℂ)] [Fintype ↥(h.W1 ⊔ h.W2)] in
omit [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)] in
/-- `dim_ℂ CF(W, W − W₂) = (w₁ − 1)·w₂`, the dimension behind the `ω_{ij} − ω_{0j}` basis. -/
theorem finrank_sdiffSupported :
    Module.finrank ℂ (TICyclicHypothesis.SupportedOnV ℂ h.sdiffTICyclicHypothesis)
      = (Nat.card h.W1 - 1) * Nat.card h.W2 := by
  have : Finite L := Finite.of_fintype L
  have : Fintype ↥h.sdiffTICyclicHypothesis.W := Fintype.ofFinite _
  have : IsMulCommutative ↥h.sdiffTICyclicHypothesis.W :=
    h.sdiffTICyclicHypothesis.isMulCommutative_W
  change Module.finrank ℂ ↥(ClassFunction.supportedSubmodule
      (OddOrder.Peterfalvi.S04.supportInSubgroup h.sdiffTICyclicHypothesis.V
        h.sdiffTICyclicHypothesis.W)) = _
  rw [finrank_supportedSubmodule_eq_card, h.card_supportInSubgroup_sdiff]

/-- **Peterfalvi (4.3.b) basis**: the `ω_{ij} − ω_{0j}` (`i ≠ 0`, all `j`) form a basis of
`CF(W, W − W₂)` — linearly independent (`omegaColumnDiff_linearIndependent`) with the matching
count `(w₁−1)·w₂ = dim` (`finrank_sdiffSupported`). -/
noncomputable def omegaColumnDiffBasis :
    Module.Basis ({χ₁ : (h.W1.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ // χ₁ ≠ 1} ×
        ((h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ)) ℂ
      (TICyclicHypothesis.SupportedOnV ℂ h.sdiffTICyclicHypothesis) := by
  classical
  haveI : Finite L := Finite.of_fintype L
  haveI : Fintype ((h.W1.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) := Fintype.ofFinite _
  haveI : Fintype ((h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) := Fintype.ofFinite _
  haveI : Fintype {χ₁ : (h.W1.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ // χ₁ ≠ 1} := Fintype.ofFinite _
  haveI : Nonempty ((h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) := ⟨1⟩
  haveI : Nonempty {χ₁ : (h.W1.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ // χ₁ ≠ 1} :=
    h.sdiffTICyclicHypothesis.nonempty_charNeOne
      h.sdiffTICyclicHypothesis.W1_le_W h.sdiffTICyclicHypothesis.W1_nontrivial
  refine basisOfLinearIndependentOfCardEqFinrank h.omegaColumnDiff_linearIndependent ?_
  rw [h.finrank_sdiffSupported, Fintype.card_prod]
  have hc1 : Nat.card ((h.W1.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) = Nat.card h.W1 :=
    h.sdiffTICyclicHypothesis.card_charGroup_subgroupOf h.sdiffTICyclicHypothesis.W1_le_W
  have hc2 : Nat.card ((h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) = Nat.card h.W2 :=
    h.sdiffTICyclicHypothesis.card_charGroup_subgroupOf h.sdiffTICyclicHypothesis.W2_le_W
  have e1 : Fintype.card {χ₁ : (h.W1.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ // χ₁ ≠ 1}
      = Nat.card h.W1 - 1 := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, ← Nat.card_eq_fintype_card, hc1]
  have e2 : Fintype.card ((h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) = Nat.card h.W2 := by
    rw [← Nat.card_eq_fintype_card, hc2]
  rw [e1, e2]

omit [Invertible (Nat.card L : ℂ)] [Fintype ↥(h.W1 ⊔ h.W2)] in
/-- The `ω_{ij} − ω_{0j}` basis evaluated at an index pair `⟨k, l⟩` is the column difference
`ω_{kl} − ω_{0l}` (`coe_basisOfLinearIndependentOfCardEqFinrank` on the family of
`omegaColumnDiff_linearIndependent`). -/
theorem omegaColumnDiffBasis_apply
    (pq : {χ₁ : (h.W1.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ // χ₁ ≠ 1} ×
        ((h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ)) :
    h.omegaColumnDiffBasis pq = h.omegaColumnDiff pq.1.1 1 pq.2 := by
  classical
  have : Finite L := Finite.of_fintype L
  let : Fintype ((h.W1.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) := Fintype.ofFinite _
  let : Fintype ((h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) := Fintype.ofFinite _
  let : Fintype {χ₁ : (h.W1.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ // χ₁ ≠ 1} := Fintype.ofFinite _
  have : Nonempty ((h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) := ⟨1⟩
  have : Nonempty {χ₁ : (h.W1.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ // χ₁ ≠ 1} :=
    h.sdiffTICyclicHypothesis.nonempty_charNeOne
      h.sdiffTICyclicHypothesis.W1_le_W h.sdiffTICyclicHypothesis.W1_nontrivial
  have hcoe : ⇑h.omegaColumnDiffBasis = fun p => h.omegaColumnDiff p.1.1 1 p.2 := by
    unfold omegaColumnDiffBasis
    exact coe_basisOfLinearIndependentOfCardEqFinrank _ _
  exact congrFun hcoe pq

omit [Invertible (Nat.card L : ℂ)] in
omit [Fintype ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)] in
/-- `ω_{kl} = chiColumn l (e⁻¹ k)`: the basis index `k` (a `W₁`-dual) is `e (e⁻¹ k)` of
the column family. -/
theorem chiColumn_w1CharEquiv_symm [NeZero (Nat.card h.W1)]
    (l : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ)
    (k : (h.W1.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) :
    h.chiColumn l (h.w1CharEquiv.symm k)
      = h.sdiffTICyclicHypothesis.omega (h.sdiffTICyclicHypothesis.omegaProdChar k l) := by
  rw [chiColumn, Equiv.apply_symm_apply]

omit [Fintype ↥(h.W1 ⊔ h.W2)] in
/-- **The (1.4) image of a basis vector** `ω_{kl} − ω_{0l}` is the column-`l` signed
difference at index `e⁻¹ k`:
`Ind_W^L(ω_{kl} − ω_{0l}) = (columnFamily l).signedDifference (e⁻¹ k)`. -/
theorem induce_omegaColumnDiff_eq [NeZero (Nat.card h.W1)]
    (l : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ)
    (k : (h.W1.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) :
    ClassFunction.induce h.sdiffTICyclicHypothesis.W
        (h.omegaColumnDiff k 1 l : ClassFunction h.sdiffTICyclicHypothesis.W ℂ)
      = (h.columnFamily l).signedDifference (h.w1CharEquiv.symm k) := by
  have : Fintype ↥(h.W1 ⊔ h.W2) := Fintype.ofFinite _
  have hval : (h.omegaColumnDiff k 1 l : ClassFunction h.sdiffTICyclicHypothesis.W ℂ)
      = (h.chiColumn l (h.w1CharEquiv.symm k) : ClassFunction h.sdiffTICyclicHypothesis.W ℂ)
        - (h.chiColumn l 0 : ClassFunction h.sdiffTICyclicHypothesis.W ℂ) := by
    rw [h.chiColumn_w1CharEquiv_symm l k, h.chiColumn_zero l]
    exact h.omegaColumnDiff_coe k 1 l
  rw [hval, ← h.isometryDifferenceImage_induceZ l (h.w1CharEquiv.symm k),
    h.columnFamily_spec l (h.w1CharEquiv.symm k)]

/-- The "certain-type difference" `g = Res_W(δ_{χ₂}·μ_{ij}) − ω_{ij}` on `↥W`, whose
vanishing on `W − W₂` (the (1.3) value-match) gives the σ-identification. -/
noncomputable def certainTypeRestrictDiff [NeZero (Nat.card h.W1)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1)) :
    ClassFunction h.sdiffTICyclicHypothesis.W ℂ :=
  ClassFunction.restrict h.sdiffTICyclicHypothesis.W
      ((h.columnFamily χ₂).sign • ((h.columnFamily χ₂).mu i : ClassFunction L ℂ))
    - (h.chiColumn χ₂ i : ClassFunction h.sdiffTICyclicHypothesis.W ℂ)

set_option backward.isDefEq.respectTransparency false in
/-- **Step 4, `g ⊥ basis`.**  The certain-type difference `g = Res_W(δ_j·μ_{ij}) − ω_{ij}` is
orthogonal to every basis vector `ω_{kl} − ω_{0l}` of `CF(W, W − W₂)`.

Frobenius reciprocity (`inner_induce_eq_inner_restrict`) turns the `Res`-part into
`⟨Ind_W^L(ω_{kl} − ω_{0l}), δ_j μ_{ij}⟩`, and the (1.4) image
`Ind_W^L(ω_{kl} − ω_{0l}) = δ_l·(μ_{e⁻¹k,l} − μ_{0,l})` (`induce_omegaColumnDiff_eq`) reduces
both pairings to character orthonormality.  On the diagonal `l = χ₂` the within-column
orthonormality `(μ_{·l}, μ_{·χ₂})` matches the source pairing `(ω_{·l}, ω_{·χ₂})` once the
sign `δ_l² = 1` is removed (`k = e i ↔ e⁻¹k = i`, `1 = e i ↔ 0 = i`); off the diagonal both
sides vanish because distinct `W₂`-columns are orthogonal (`columnFamily_mu_ne` / the source
`ω`-orthogonality). -/
theorem certainTypeRestrictDiff_inner_basis [NeZero (Nat.card h.W1)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1))
    (l : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ)
    (k : (h.W1.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) :
    ClassFunction.inner
      ((h.omegaColumnDiff k 1 l : TICyclicHypothesis.SupportedOnV ℂ h.sdiffTICyclicHypothesis) :
          ClassFunction h.sdiffTICyclicHypothesis.W ℂ)
      (h.certainTypeRestrictDiff χ₂ i) = 0 := by
  classical
  rw [certainTypeRestrictDiff, ClassFunction.inner_sub_right, sub_eq_zero,
    ← ClassFunction.inner_induce_eq_inner_restrict, h.induce_omegaColumnDiff_eq l k,
    SignedIrreducibleDifferenceFamily.signedDifference_apply,
    ← Int.cast_smul_eq_zsmul ℂ (h.columnFamily l).sign
      ((h.columnFamily l).difference (h.w1CharEquiv.symm k)),
    ← Int.cast_smul_eq_zsmul ℂ (h.columnFamily χ₂).sign
      ((h.columnFamily χ₂).mu i : ClassFunction L ℂ),
    ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right, star_intCast,
    SignedIrreducibleDifferenceFamily.difference_apply,
    SignedIrreducibleDifferenceFamily.classFunction_apply,
    SignedIrreducibleDifferenceFamily.classFunction_apply,
    ClassFunction.inner_sub_left, omegaColumnDiff_coe, chiColumn, ClassFunction.inner_sub_left,
    irreducibleCharacter_inner, irreducibleCharacter_inner,
    irreducibleCharacter_inner, irreducibleCharacter_inner]
  -- LHS = δ_l·(δ_χ₂·([μ_{e⁻¹k,l}=μ_{iχ₂}] − [μ_{0,l}=μ_{iχ₂}]));
  -- RHS = [ω_{kl}=ω_{e i,χ₂}] − [ω_{0l}=ω_{e i,χ₂}].
  by_cases hl : l = χ₂
  · subst hl
    -- the within-column index equalities
    have hcol : ∀ (a : (h.W1.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ),
        (h.sdiffTICyclicHypothesis.omegaProdChar a l
          = h.sdiffTICyclicHypothesis.omegaProdChar (h.w1CharEquiv i) l) ↔ a = h.w1CharEquiv i :=
      fun a => ⟨fun he => (h.sdiffTICyclicHypothesis.omegaProdChar_inj he).1,
        fun he => by rw [he]⟩
    have hs1 : h.w1CharEquiv.symm 1 = 0 := by rw [Equiv.symm_apply_eq, h.w1CharEquiv_zero]
    simp only [(h.columnFamily l).injective.eq_iff,
      h.sdiffTICyclicHypothesis.omega_injective.eq_iff, hcol, ← Equiv.symm_apply_eq, hs1]
    have hsign2 : ((h.columnFamily l).sign : ℂ) * ((h.columnFamily l).sign : ℂ) = 1 := by
      rcases (h.columnFamily l).sign_eq with hs | hs <;> rw [hs] <;> norm_num
    rw [← mul_assoc, hsign2, one_mul]
  · -- distinct columns: all four pairings vanish
    rw [if_neg (h.columnFamily_mu_ne hl (h.w1CharEquiv.symm k) i),
      if_neg (h.columnFamily_mu_ne hl 0 i),
      if_neg (fun he => (h.sdiffTICyclicHypothesis.omegaProdChar_ne (fun hand => hl hand.2))
        (h.sdiffTICyclicHypothesis.omega_injective he)),
      if_neg (fun he => (h.sdiffTICyclicHypothesis.omegaProdChar_ne (fun hand => hl hand.2))
        (h.sdiffTICyclicHypothesis.omega_injective he))]
    ring

omit [Invertible (Nat.card L : ℂ)] in
/-- **The (1.3)(a) masking engine for `CF(W, W − W₂)`.**  Any class function `f` on `↥W`
orthogonal to every `ω_{kl} − ω_{0l}` basis vector vanishes on the TI set `W − W₂`.  The
`ω_{kl} − ω_{0l}` are a basis of `CF(W, W − W₂)` (`omegaColumnDiffBasis`), so the ℂ-linear
functional `⟨·, f⟩` is zero on all of `CF(W, W − W₂)`; the (1.3)(a) engine
(`eq_zero_of_mem_of_inner_supported_eq_zero`, with `W − W₂` conjugation-closed in the abelian
`W`) then forces `f` to vanish on `W − W₂`. -/
theorem apply_eq_zero_of_mem_V_of_inner_omegaColumnDiff
    {f : ClassFunction h.sdiffTICyclicHypothesis.W ℂ}
    (hf : ∀ (l : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ)
      (k : (h.W1.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ),
      ClassFunction.inner
        ((h.omegaColumnDiff k 1 l :
            TICyclicHypothesis.SupportedOnV ℂ h.sdiffTICyclicHypothesis) :
          ClassFunction h.sdiffTICyclicHypothesis.W ℂ) f = 0)
    {v : L} (hv : v ∈ h.sdiffTICyclicHypothesis.V) :
    f ⟨v, h.sdiffTICyclicHypothesis.V_subset_W hv⟩ = 0 := by
  classical
  have : IsMulCommutative ↥h.sdiffTICyclicHypothesis.W :=
    h.sdiffTICyclicHypothesis.isMulCommutative_W
  -- `⟨·, f⟩` is zero on `CF(W, W − W₂)`: zero on the `ω`-basis, so on the whole submodule
  have hL0 : (innerLeftFunctional f).comp
      (Submodule.subtype (ClassFunction.supportedSubmodule (G := ↥h.sdiffTICyclicHypothesis.W)
        (OddOrder.Peterfalvi.S04.supportInSubgroup h.sdiffTICyclicHypothesis.V
          h.sdiffTICyclicHypothesis.W))) = 0 := by
    refine Module.Basis.ext h.omegaColumnDiffBasis (fun pq => ?_)
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.zero_apply,
      innerLeftFunctional_apply, h.omegaColumnDiffBasis_apply]
    exact hf pq.2 pq.1.1
  refine eq_zero_of_mem_of_inner_supported_eq_zero
    (A := OddOrder.Peterfalvi.S04.supportInSubgroup h.sdiffTICyclicHypothesis.V
      h.sdiffTICyclicHypothesis.W) (fun x _ t => ?_) (fun φ hφ => ?_) ?_
  · -- `W − W₂` is conjugation-closed in the abelian `W`, so `t * x * t⁻¹ = x`
    have hxx : t * x * t⁻¹ = x := by rw [mul_comm' t x, mul_assoc, mul_inv_cancel, mul_one]
    rw [hxx]; assumption
  · -- orthogonal to every `φ ∈ CF(W, W − W₂)` via `hL0`
    have := DFunLike.congr_fun hL0 ⟨φ, (ClassFunction.mem_supportedSubmodule).mpr hφ⟩
    simpa using this
  · rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]; exact hv

omit [Fintype ↥(h.W1 ⊔ h.W2)] in
/-- **Step 4, the (1.3) masking.**  The certain-type difference `g = Res_W(δ_j·μ_{ij}) − ω_{ij}`
vanishes on the TI set `W − W₂` — `g ⊥` the `ω_{kl} − ω_{0l}` basis
(`certainTypeRestrictDiff_inner_basis`) feeds the masking engine. -/
theorem certainTypeRestrictDiff_apply_eq_zero_of_mem_V [NeZero (Nat.card h.W1)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1))
    {v : L} (hv : v ∈ h.sdiffTICyclicHypothesis.V) :
    h.certainTypeRestrictDiff χ₂ i ⟨v, h.sdiffTICyclicHypothesis.V_subset_W hv⟩ = 0 := by
  have : Fintype ↥(h.W1 ⊔ h.W2) := Fintype.ofFinite _
  exact h.apply_eq_zero_of_mem_V_of_inner_omegaColumnDiff
    (fun l k => h.certainTypeRestrictDiff_inner_basis χ₂ i l k) hv

/-- The canonical (3.1)-for-`L` Dade application of (4.3)(a): the §4 Dade package (2.6) on the
TI set `V = W − (W₁ ∪ W₂)`, whose local subgroups are all trivial (`H(a) = ⊥`), so
`HConjInvariant` holds for free.  This `app` drives the §5 σ-machinery on `(L, W)`. -/
noncomputable def toTICyclicFullDadeApplication :
    OddOrder.Peterfalvi.S05.TICyclicHypothesis.FullDadeApplication h.toTICyclicHypothesis :=
  ⟨h.toTICyclicHypothesis.toDadeHypothesis.fullDadeIsometryData⟩

/-- **Peterfalvi (4.3.b), the certain-type characters as σ-images.**  For each `W₂`-column `χ₂`
and `W₁`-index `i`, the (3.2) isometry `σ` of the `(L, W)` TI-cyclic setup sends the linear
character `ω_{ij}` of `W` to the signed certain-type character `δ_j·μ_{ij}` of `L`:

  `σ(ω_{ij}) = δ_j · μ_{ij}`.

The σ-machinery runs on `toTICyclicHypothesis` (`V = W − (W₁ ∪ W₂)`), while the `μ_{ij}` come
from the (1.4) difference family on the larger TI set `W − W₂` (`sdiffTICyclicHypothesis`); the
two share the same `W = W₁ ⊔ W₂`.  Applying `eq_sigma_of_apply_eq_on_V`: `δ_j·μ_{ij}` is a
norm-one virtual character (`δ_j² = 1`, `μ_{ij}` irreducible) whose values on `V` match `ω_{ij}`
— this is the (1.3) value-match `certainTypeRestrictDiff_apply_eq_zero_of_mem_V`, transported
from `W − W₂ ⊇ V`. -/
theorem sigma_chiColumn_eq_certainType [NeZero (Nat.card h.W1)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1)) :
    h.toTICyclicHypothesis.sigma rfl h.toTICyclicFullDadeApplication
        (h.chiColumn χ₂ i : ClassFunction h.sdiffTICyclicHypothesis.W ℂ)
      = (h.columnFamily χ₂).sign • ((h.columnFamily χ₂).mu i : ClassFunction L ℂ) := by
  symm
  refine h.toTICyclicHypothesis.eq_sigma_of_apply_eq_on_V rfl h.toTICyclicFullDadeApplication
    (h.chiColumn χ₂ i) ((ZIrr L).smul_mem _ ((h.columnFamily χ₂).mu i).mem_ZIrr) ?_ ?_
  · -- norm one: `⟨δ_j μ_{ij}, δ_j μ_{ij}⟩ = δ_j² = 1`
    rw [← Int.cast_smul_eq_zsmul ℂ (h.columnFamily χ₂).sign
        ((h.columnFamily χ₂).mu i : ClassFunction L ℂ),
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right, star_intCast,
      irreducibleCharacter_inner, if_pos rfl]
    rcases (h.columnFamily χ₂).sign_eq with hs | hs <;> rw [hs] <;> norm_num
  · -- value-match on `V ⊆ W − W₂` from the (1.3) masking
    intro v hv
    have hvs : v ∈ h.sdiffTICyclicHypothesis.V := ⟨hv.1, fun h2 => hv.2 (Or.inr h2)⟩
    have hg := h.certainTypeRestrictDiff_apply_eq_zero_of_mem_V χ₂ i hvs
    rw [certainTypeRestrictDiff, ClassFunction.sub_apply, sub_eq_zero,
      ClassFunction.restrict_apply] at hg
    exact hg

omit [Fintype ↥(h.W1 ⊔ h.W2)] in
/-- **Peterfalvi (4.3.c), first part** (the value identity).  For `x ∈ W − W₂`,
`μ_{ij}(x) = δ_j·ω_{ij}(x)`.  This is the (1.3) value-match
`certainTypeRestrictDiff_apply_eq_zero_of_mem_V` (`δ_j·μ_{ij}(x) = ω_{ij}(x)`) multiplied by
`δ_j` (using `δ_j² = 1`). -/
theorem certainType_apply_eq_of_mem_V [NeZero (Nat.card h.W1)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1))
    {v : L} (hv : v ∈ h.sdiffTICyclicHypothesis.V) :
    ((h.columnFamily χ₂).mu i : ClassFunction L ℂ) v
      = ((h.columnFamily χ₂).sign : ℂ)
        * (h.chiColumn χ₂ i : ClassFunction h.sdiffTICyclicHypothesis.W ℂ)
            ⟨v, h.sdiffTICyclicHypothesis.V_subset_W hv⟩ := by
  have : Fintype ↥(h.W1 ⊔ h.W2) := Fintype.ofFinite _
  have hg := h.certainTypeRestrictDiff_apply_eq_zero_of_mem_V χ₂ i hv
  rw [certainTypeRestrictDiff, ClassFunction.sub_apply, sub_eq_zero,
    ClassFunction.restrict_apply, ClassFunction.zsmul_apply, zsmul_eq_mul] at hg
  rw [← hg, ← mul_assoc]
  rcases (h.columnFamily χ₂).sign_eq with hs | hs <;> rw [hs] <;> push_cast <;> ring

omit [Fintype ↥(h.W1 ⊔ h.W2)] in
/-- **Peterfalvi (4.3.d)** (the degree congruence).  `μ_{ij}(1) ≡ δ_j (mod w₁)`: there is an
integer `a` with `μ_{ij}(1) = δ_j + a·w₁`.

The class function `ψ = Res_{W₁}(μ_{ij}) − δ_j·Res_{W₁}(ω_{ij})` on `W₁` (both restrictions
taken inside `W`, so the proof never leaves `↥W`) is a virtual character that vanishes on
`W₁^# ⊆ W − W₂` (the (4.3.c) value identity), hence `ψ(1) = w₁·m` for some integer `m`
(`exists_apply_one_eq_card_mul_of_vanishing_off_one`).  Evaluating `ψ(1) = μ_{ij}(1) − δ_j`
(both `ω_{ij}` and the restriction are degree-preserving at `1`) gives the congruence. -/
theorem certainType_degree_modEq [NeZero (Nat.card h.W1)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1)) :
    ∃ a : ℤ, ((h.columnFamily χ₂).mu i : ClassFunction L ℂ) 1
      = ((h.columnFamily χ₂).sign : ℂ) + (Nat.card h.W1 : ℂ) * (a : ℂ) := by
  have : Fintype ↥(h.W1 ⊔ h.W2) := Fintype.ofFinite _
  classical
  have : Finite L := Finite.of_fintype L
  have : Fintype ↥(h.W1.subgroupOf h.sdiffTICyclicHypothesis.W) := Fintype.ofFinite _
  have hcard : Nat.card ↥(h.W1.subgroupOf h.sdiffTICyclicHypothesis.W) = Nat.card h.W1 :=
    Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe h.sdiffTICyclicHypothesis.W1_le_W).toEquiv
  have : Invertible (Nat.card ↥(h.W1.subgroupOf h.sdiffTICyclicHypothesis.W) : ℂ) :=
    invertibleOfNonzero (by rw [Nat.cast_ne_zero]; exact Nat.card_pos.ne')
  -- `ψ = Res_{W₁⊆W}(Res_W μ_{ij}) − δ_j · Res_{W₁⊆W}(ω_{ij})`, a class function on `↥(W₁ ∩ W)`
  set ψ : ClassFunction ↥(h.W1.subgroupOf h.sdiffTICyclicHypothesis.W) ℂ :=
    ClassFunction.restrict (h.W1.subgroupOf h.sdiffTICyclicHypothesis.W)
        (ClassFunction.restrict h.sdiffTICyclicHypothesis.W
          ((h.columnFamily χ₂).mu i : ClassFunction L ℂ))
      - (h.columnFamily χ₂).sign •
        ClassFunction.restrict (h.W1.subgroupOf h.sdiffTICyclicHypothesis.W)
          (h.chiColumn χ₂ i : ClassFunction h.sdiffTICyclicHypothesis.W ℂ) with hψdef
  -- `ψ` is a virtual character
  have hψZ : ψ ∈ ZIrr ↥(h.W1.subgroupOf h.sdiffTICyclicHypothesis.W) :=
    Submodule.sub_mem _
      (ClassFunction.restrict_mem_ZIrr _
        (ClassFunction.restrict_mem_ZIrr _ ((h.columnFamily χ₂).mu i).mem_ZIrr))
      ((ZIrr _).smul_mem _
        (ClassFunction.restrict_mem_ZIrr _ (h.chiColumn χ₂ i).mem_ZIrr))
  -- `ψ` vanishes off the identity (`W₁^# ⊆ W − W₂`, the (4.3.c) value identity)
  have hvan : ∀ y : ↥(h.W1.subgroupOf h.sdiffTICyclicHypothesis.W), y ≠ 1 → ψ y = 0 := by
    intro y hy
    have hyW1 : ((y : ↥h.sdiffTICyclicHypothesis.W) : L) ∈ h.W1 :=
      Subgroup.mem_subgroupOf.mp (SetLike.coe_mem y)
    have hyne : ((y : ↥h.sdiffTICyclicHypothesis.W) : L) ≠ 1 := fun heq =>
      hy (Subtype.ext (Subtype.ext heq))
    have hmemV : ((y : ↥h.sdiffTICyclicHypothesis.W) : L) ∈ h.sdiffTICyclicHypothesis.V := by
      refine ⟨(le_sup_left : h.W1 ≤ h.W1 ⊔ h.W2) hyW1, fun hW2 => hyne ?_⟩
      have hmem : ((y : ↥h.sdiffTICyclicHypothesis.W) : L) ∈ h.W1 ⊓ h.W2 :=
        Subgroup.mem_inf.mpr ⟨hyW1, hW2⟩
      rwa [disjoint_iff.mp h.W_disjoint, Subgroup.mem_bot] at hmem
    rw [hψdef, ClassFunction.sub_apply, ClassFunction.restrict_apply, ClassFunction.zsmul_apply,
      ClassFunction.restrict_apply, ClassFunction.restrict_apply, zsmul_eq_mul,
      h.certainType_apply_eq_of_mem_V χ₂ i hmemV]
    rw [show (⟨((y : ↥h.sdiffTICyclicHypothesis.W) : L),
        h.sdiffTICyclicHypothesis.V_subset_W hmemV⟩ : ↥h.sdiffTICyclicHypothesis.W)
        = (y : ↥h.sdiffTICyclicHypothesis.W) from Subtype.ext rfl, sub_self]
  obtain ⟨m, hm⟩ := exists_apply_one_eq_card_mul_of_vanishing_off_one hψZ hvan
  rw [hcard] at hm
  -- `ψ(1) = μ_{ij}(1) − δ_j`
  have hψ1 : ψ 1 = ((h.columnFamily χ₂).mu i : ClassFunction L ℂ) 1
      - ((h.columnFamily χ₂).sign : ℂ) := by
    rw [hψdef, ClassFunction.sub_apply, ClassFunction.restrict_apply, ClassFunction.restrict_apply,
      ClassFunction.zsmul_apply, ClassFunction.restrict_apply, zsmul_eq_mul]
    simp [h.chiColumn_apply_one χ₂ i]
  rw [hψ1] at hm
  exact ⟨m, by linear_combination hm⟩

omit [Invertible (Nat.card L : ℂ)] in
omit [Fintype ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)] in
set_option backward.isDefEq.respectTransparency false in
/-- `ω_{00} = 1_W`: the index-`(0,0)` member of the column family (trivial `W₂`-dual, base
`W₁`-index) is the trivial character of `W` (`omegaProdChar 1 1 = 1`, `ω(1) = 1_W`). -/
theorem chiColumn_one_zero_eq_trivial [NeZero (Nat.card h.W1)] :
    (h.chiColumn 1 0 : ClassFunction h.sdiffTICyclicHypothesis.W ℂ)
      = trivialClassFunction h.sdiffTICyclicHypothesis.W := by
  apply ClassFunction.ext
  intro w
  rw [trivialClassFunction_apply, chiColumn, h.sdiffTICyclicHypothesis.omega_apply]
  -- the value `ω_{00}(w) = (w1CharEquiv 0)(wFst w) · 1(wSnd w) = 1`
  have hv : (h.sdiffTICyclicHypothesis.omegaProdChar (h.w1CharEquiv 0)
      (1 : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ)) w = 1 := by
    change (h.w1CharEquiv 0) (h.sdiffTICyclicHypothesis.wFst w)
        * (1 : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (h.sdiffTICyclicHypothesis.wSnd w) = 1
    rw [h.w1CharEquiv_zero, MonoidHom.one_apply, MonoidHom.one_apply, one_mul]
  rw [hv, Units.val_one]

omit [Fintype ↥(h.W1 ⊔ h.W2)] in
/-- **Peterfalvi (4.4), the `(0,0)` anchor**: `δ_0 = 1` and `μ_{00} = 1_L`.  The (4.3.b)
σ-identification sends the trivial character `ω_{00} = 1_W` to `δ_0·μ_{00}`, while `σ` fixes the
trivial character (`sigma_trivial`), so `δ_0·μ_{00} = 1_L`.  Pairing with `1_L` (irreducible)
forces the multiplicity `⟨μ_{00}, 1_L⟩ = 1`, i.e. `μ_{00} = 1_L`, and then `δ_0 = 1`. -/
theorem certainType_zero_column_anchor [NeZero (Nat.card h.W1)] :
    (h.columnFamily 1).sign = 1 ∧
      ((h.columnFamily 1).mu 0 : ClassFunction L ℂ) = trivialClassFunction L := by
  have : Fintype ↥(h.W1 ⊔ h.W2) := Fintype.ofFinite _
  classical
  set oneIrr : IrreducibleCharacter L :=
    ⟨trivialClassFunction L, trivialClassFunction_isIrreducible⟩ with honeIrr
  -- `δ_0 · μ_{00} = 1_L`, the σ-image of the trivial character
  have hkey : ((h.columnFamily 1).sign) • ((h.columnFamily 1).mu 0 : ClassFunction L ℂ)
      = trivialClassFunction L := by
    rw [← h.sigma_chiColumn_eq_certainType 1 0, h.chiColumn_one_zero_eq_trivial]
    exact h.toTICyclicHypothesis.sigma_trivial rfl h.toTICyclicFullDadeApplication
  -- pair with `1_L`: `δ_0 · ⟨μ_{00}, 1_L⟩ = ⟨1_L, 1_L⟩ = 1`
  have hinner : ((h.columnFamily 1).sign : ℂ)
      * (if (h.columnFamily 1).mu 0 = oneIrr then (1 : ℂ) else 0) = 1 := by
    have h2 := congrArg
      (fun f : ClassFunction L ℂ => ClassFunction.inner f (oneIrr : ClassFunction L ℂ)) hkey
    rw [(by rfl : (oneIrr : ClassFunction L ℂ) = trivialClassFunction L).symm,
      irreducibleCharacter_inner oneIrr oneIrr, if_pos rfl,
      ← Int.cast_smul_eq_zsmul ℂ, ClassFunction.inner_smul_left, irreducibleCharacter_inner] at h2
    exact h2
  rcases (h.columnFamily 1).sign_eq with hs | hs
  · -- `δ_0 = 1`
    rw [hs] at hinner
    have hP : (h.columnFamily 1).mu 0 = oneIrr := by
      by_contra hne
      rw [if_neg hne] at hinner; norm_num at hinner
    exact ⟨hs, by rw [hP]⟩
  · -- `δ_0 = -1` is impossible (a multiplicity is `0` or `1`)
    exfalso
    rw [hs] at hinner
    by_cases hP : (h.columnFamily 1).mu 0 = oneIrr
    · rw [if_pos hP] at hinner; norm_num at hinner
    · rw [if_neg hP] at hinner; norm_num at hinner

omit [Fintype ↥(h.W1 ⊔ h.W2)] in
/-- **Peterfalvi (4.4), forward direction.**  An irreducible character `χ` of `L` whose kernel
contains `K` is one of the `j = 0` certain-type characters `μ_{i0}`.

Since `L/K ≅ W₁` is abelian (`isMulCommutative_quotient_K`), `χ` is linear (degree one): it
inflates from `L/K` (`exists_inflate_eq_of_subset_characterKernel`) and irreducible characters of
abelian groups are degree one (`apply_one_eq_one_of_isMulCommutative`).  Writing the linear
character `χ̂ : L →* ℂˣ` and `χ₁ = χ̂|_{W₁}`, the value of `χ` on `V = W − (W₁ ∪ W₂)`
decomposes as `χ(x·y) = χ̂(x)·χ̂(y) = χ̂(x)` (since `y ∈ W₂ ⊆ K ⊆ ker χ`), which matches `ω_{i0}`
for `i = w1CharEquiv.symm χ₁`.  Theorem (3.9.a) (`eq_sigma_of_apply_eq_on_V`) then identifies `χ`
with `σ(ω_{i0}) = δ_0·μ_{i0} = μ_{i0}` (`δ_0 = 1` by the `(0,0)`-anchor). -/
theorem exists_certainType_zero_column_eq_of_subset_characterKernel [NeZero (Nat.card h.W1)]
    (χ : IrreducibleCharacter L)
    (hker : (h.K : Set L) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (χ : ClassFunction L ℂ)) :
    ∃ i, (h.columnFamily 1).mu i = χ := by
  have : Fintype ↥(h.W1 ⊔ h.W2) := Fintype.ofFinite _
  classical
  have := h.isMulCommutative_quotient_K
  -- (1) `χ` is linear: `χ(1) = 1`, since `χ` inflates from the abelian quotient `L/K`.
  obtain ⟨χbar, hχbar⟩ := exists_inflate_eq_of_subset_characterKernel (N := h.K) χ hker
  have h1 : (χ : ClassFunction L ℂ) 1 = 1 := by
    conv_lhs => rw [← hχbar]
    rw [inflate_apply_one]
    exact χbar.2.apply_one_eq_one_of_isMulCommutative
  -- (2) the linear character `χ̂ : L →* ℂˣ` with `(χ̂ g : ℂ) = χ g`
  obtain ⟨χhat, hχhat⟩ := χ.2.exists_linearIrreducibleCharacter_eq_of_apply_one_eq_one h1
  have hval : ∀ g, (χ : ClassFunction L ℂ) g = (χhat g : ℂ) := by
    intro g
    rw [← linearIrreducibleCharacter_apply χhat g, hχhat]
  -- (3) `χ̂` is trivial on `K` (`K ⊆ ker χ`, `χ(1) = 1`)
  have hKtriv : ∀ k : L, k ∈ h.K → χhat k = 1 := by
    intro k hk
    have hk1 : (χ : ClassFunction L ℂ) k = 1 := by
      have hmem := hker hk
      rwa [OddOrder.Peterfalvi.S03.mem_characterKernel,
        OddOrder.Peterfalvi.S03.characterDegree_def, h1] at hmem
    rw [hval k] at hk1
    exact Units.val_eq_one.mp hk1
  -- (4) the `W₁`-restriction `χ₁ : Ŵ₁` (over the ambient `W = W₁ ⊔ W₂`) and its index `i`
  let χ1 : (h.W1.subgroupOf h.sdiffTICyclicHypothesis.W) →* ℂˣ :=
    χhat.comp ((h.sdiffTICyclicHypothesis.W.subtype).comp
      (h.W1.subgroupOf h.sdiffTICyclicHypothesis.W).subtype)
  refine ⟨h.w1CharEquiv.symm χ1, ?_⟩
  set i := h.w1CharEquiv.symm χ1 with hidef
  have hwi : h.w1CharEquiv i = χ1 := h.w1CharEquiv.apply_symm_apply χ1
  -- the σ-identification `χ = σ(ω_{i0})`
  have heqsigma : (χ : ClassFunction L ℂ)
      = h.toTICyclicHypothesis.sigma rfl h.toTICyclicFullDadeApplication
          (h.chiColumn 1 i : ClassFunction h.sdiffTICyclicHypothesis.W ℂ) := by
    refine h.toTICyclicHypothesis.eq_sigma_of_apply_eq_on_V rfl h.toTICyclicFullDadeApplication
      (h.chiColumn 1 i) χ.mem_ZIrr ?_ ?_
    · rw [irreducibleCharacter_inner, if_pos rfl]
    · intro v hv
      have hvW : v ∈ h.sdiffTICyclicHypothesis.W := h.toTICyclicHypothesis.V_subset_W hv
      -- decompose `v = x₀ · y₀` in `L` (`x₀, y₀` the `W₁`/`W₂` components)
      have hvL : v = ((h.sdiffTICyclicHypothesis.wFst ⟨v, hvW⟩ :
            ↥h.sdiffTICyclicHypothesis.W) : L)
          * ((h.sdiffTICyclicHypothesis.wSnd ⟨v, hvW⟩ :
            ↥h.sdiffTICyclicHypothesis.W) : L) := by
        have h2 := congrArg (h.sdiffTICyclicHypothesis.W.subtype)
          (h.sdiffTICyclicHypothesis.eq_wFst_mul_wSnd ⟨v, hvW⟩)
        rw [map_mul] at h2
        simpa using h2
      have hy0 : ((h.sdiffTICyclicHypothesis.wSnd ⟨v, hvW⟩ :
          ↥h.sdiffTICyclicHypothesis.W) : L) ∈ h.K := by
        apply h.W2_le_K
        have hmem := (h.sdiffTICyclicHypothesis.wSnd ⟨v, hvW⟩).2
        rwa [Subgroup.mem_subgroupOf] at hmem
      -- both sides equal `χ̂(x₀)`: `χ(v) = χ̂(v) = χ̂(x₀·y₀) = χ̂(x₀) = χ₁(wFst v) = ω_{i0}(v)`
      have hmatch : χhat v = χ1 (h.sdiffTICyclicHypothesis.wFst ⟨v, hvW⟩) := by
        have hx : χ1 (h.sdiffTICyclicHypothesis.wFst ⟨v, hvW⟩)
            = χhat ((h.sdiffTICyclicHypothesis.wFst ⟨v, hvW⟩ :
                ↥h.sdiffTICyclicHypothesis.W) : L) := rfl
        rw [hx]
        conv_lhs => rw [hvL]
        rw [map_mul, hKtriv _ hy0, mul_one]
      change (χ : ClassFunction L ℂ) v
        = (h.chiColumn 1 i : ClassFunction h.sdiffTICyclicHypothesis.W ℂ) ⟨v, hvW⟩
      rw [h.chiColumn_one_apply, hwi, hval v]
      exact congrArg _ hmatch
  -- conclude: `χ = σ(ω_{i0}) = δ_0 · μ_{i0} = μ_{i0}`
  rw [h.sigma_chiColumn_eq_certainType 1 i, h.certainType_zero_column_anchor.1, one_zsmul]
    at heqsigma
  exact Subtype.ext heqsigma.symm

end Recipe

end Hypothesis

end OddOrder.Peterfalvi.S06


